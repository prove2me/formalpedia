-- Prove2me | solution 1 for PhilipponMultiplicity.exists_open_preserving_quasifinite_mixed_slices
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-10-07T16:49:35.720576+00:00
-- url     : https://prove2.me/submissions/7fdbad93-9e18-4c95-8bbd-f2f6ba01b692

import Theorems.Thm_PhilipponMultiplicity_exists_open_preserving_finite_model_mixed_slices
import Definitions.Def_PhilipponMultiplicity_Analytic
import Definitions.Def_PhilipponMultiplicity_GeometricSupport
import Definitions.Def_PhilipponMultiplicity_MixedFlagParameters
import Definitions.Def_PhilipponMultiplicity_UniversalMixedSlices
import Mathlib
import Mathlib.Analysis.Analytic.Polynomial
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.FDeriv.Analytic


section

set_option autoImplicit false
set_option maxHeartbeats 300000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false
noncomputable section

attribute [local instance] MvPolynomial.algebraMvPolynomial

namespace PhilipponMultiplicity.SpecializationFiber
open MvPolynomial

def specialize {K R δ : Type*} [CommRing K] [CommRing R] [Algebra K R]
    (c : δ → K) : MvPolynomial δ R →ₐ[K] R :=
  (MvPolynomial.aeval (fun i => algebraMap K R (c i))).restrictScalars K

@[simp] theorem specialize_C {K R δ : Type*} [CommRing K] [CommRing R] [Algebra K R]
    (c : δ → K) (r : R) : specialize c (C r) = r := by
  simp [specialize]

@[simp] theorem specialize_X {K R δ : Type*} [CommRing K] [CommRing R] [Algebra K R]
    (c : δ → K) (i : δ) : specialize (R := R) c (X i) = algebraMap K R (c i) := by
  simp [specialize]

theorem specialize_surjective {K R δ : Type*} [CommRing K] [CommRing R] [Algebra K R]
    (c : δ → K) : Function.Surjective (specialize (R := R) c) :=
  fun r => ⟨C r, specialize_C c r⟩

theorem specialize_comp {K R δ : Type*} [CommRing K] [CommRing R] [Algebra K R]
    (c : δ → K) :
    (specialize (R := R) c).toRingHom.comp
      (algebraMap (MvPolynomial δ K) (MvPolynomial δ R)) =
        (algebraMap K R).comp (MvPolynomial.eval c) := by
  apply MvPolynomial.ringHom_ext
  · intro k
    change specialize c (MvPolynomial.map (algebraMap K R) (C k)) =
      algebraMap K R (MvPolynomial.eval c (C k))
    rw [MvPolynomial.map_C, specialize_C, MvPolynomial.eval_C]
  · intro i
    change specialize c (MvPolynomial.map (algebraMap K R) (X i)) =
      algebraMap K R (MvPolynomial.eval c (X i))
    rw [MvPolynomial.map_X, specialize_X, MvPolynomial.eval_X]

/-- Specializing coefficient variables has exactly the extended evaluation
ideal as kernel, over an arbitrary coefficient algebra. -/
theorem ker_specialize {K R δ : Type*} [CommRing K] [CommRing R] [Algebra K R]
    (c : δ → K) :
    RingHom.ker (specialize (R := R) c) =
      (RingHom.ker (MvPolynomial.eval c)).map
        (algebraMap (MvPolynomial δ K) (MvPolynomial δ R)) := by
  let L := (RingHom.ker (MvPolynomial.eval c)).map
    (algebraMap (MvPolynomial δ K) (MvPolynomial δ R))
  have hrel (i : δ) : C (algebraMap K R (c i)) - X i ∈ L := by
    have h : C (c i) - X i ∈ RingHom.ker (MvPolynomial.eval c) := by
      simp [RingHom.mem_ker]
    have hm := Ideal.mem_map_of_mem
      (algebraMap (MvPolynomial δ K) (MvPolynomial δ R)) h
    change MvPolynomial.map (algebraMap K R) (C (c i) - X i) ∈ L at hm
    simpa only [map_sub, MvPolynomial.map_C, MvPolynomial.map_X] using hm
  have hdiff (P : MvPolynomial δ R) : C (specialize c P) - P ∈ L := by
    induction P using MvPolynomial.induction_on with
    | C r => simp
    | add P Q hP hQ =>
      simpa only [map_add, add_sub_add_comm] using L.add_mem hP hQ
    | mul_X P i hP =>
      simpa only [map_mul, specialize_X] using L.mul_sub_mul_mem hP (hrel i)
  apply le_antisymm
  · intro P hP
    have hz : specialize c P = 0 := hP
    simpa only [hz, map_zero, zero_sub, neg_mem_iff] using hdiff P
  · rw [Ideal.map_le_iff_le_comap]
    intro P hP
    change specialize c ((algebraMap (MvPolynomial δ K) (MvPolynomial δ R)) P) = 0
    have he := RingHom.congr_fun (specialize_comp (R := R) c) P
    change specialize c ((algebraMap (MvPolynomial δ K) (MvPolynomial δ R)) P) =
      algebraMap K R (MvPolynomial.eval c P) at he
    rw [he]
    rw [show MvPolynomial.eval c P = 0 from hP, map_zero]

/-- The fiber of a quotient under a surjective specialization is the quotient
by the specialized ideal, without replacing either ideal by its radical. -/
def quotientFiberEquiv {K P R : Type*} [CommRing K] [CommRing P] [CommRing R]
    [Algebra K P] [Algebra K R] (f : P →ₐ[K] R) (hf : Function.Surjective f)
    (J : Ideal P) :
    ((P ⧸ J) ⧸ (RingHom.ker f).map (Ideal.Quotient.mk J)) ≃ₐ[K]
      (R ⧸ J.map f) := by
  let g := (Ideal.Quotient.mkₐ K (J.map f)).comp f
  have hg : Function.Surjective g := Ideal.Quotient.mk_surjective.comp hf
  have hker : RingHom.ker g = J ⊔ RingHom.ker f := by
    change RingHom.ker ((Ideal.Quotient.mk (J.map f)).comp f.toRingHom) = _
    rw [← RingHom.comap_ker, Ideal.mk_ker]
    exact Ideal.comap_map_of_surjective f.toRingHom hf J
  exact (DoubleQuot.quotQuotEquivQuotSupₐ K J (RingHom.ker f)).trans
    ((Ideal.quotientEquivAlgOfEq K hker.symm).trans
      (Ideal.quotientKerAlgEquivOfSurjective hg))

/-- Finite fibers imply quasi-finiteness at every prime over that fiber.
Zariski's main theorem supplies the passage to Mathlib's local-algebra form. -/
theorem quasiFiniteAt_of_finite_fiber
    {K A B : Type*} [CommRing K] [CommRing A] [CommRing B]
    [Algebra K A] [Algebra A B] [Algebra K B] [IsScalarTower K A B]
    [Algebra.FiniteType A B] (p : Ideal A) (q : Ideal B) [q.IsPrime]
    (hqp : q.under A = p)
    (hfinite : Module.Finite K (B ⧸ p.map (algebraMap A B))) :
    Algebra.QuasiFiniteAt A q := by
  subst p
  letI := hfinite
  haveI : Module.Finite A (B ⧸ (q.under A).map (algebraMap A B)) :=
    Module.Finite.of_restrictScalars_finite K A _
  haveI : Algebra.WeaklyQuasiFiniteAt A q := inferInstance
  exact Algebra.QuasiFiniteAt.of_weaklyQuasiFiniteAt q

end PhilipponMultiplicity.SpecializationFiber
end

end


section

set_option autoImplicit false
set_option maxHeartbeats 350000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false
open scoped BigOperators
noncomputable section

attribute [local instance] MvPolynomial.algebraMvPolynomial

namespace PhilipponMultiplicity.MixedFamily
open MvPolynomial SpecializationFiber
variable {K : Type*} [Field K] (M : MultiProjectiveSpace K)

theorem specialize_fixed (l : List M.FactorIndex)
    (c : Fin l.length → M.Variable → K) :
    (specialize (R := SlicePolynomial M) (Function.uncurry c)).toRingHom.comp
      (fixed M l) = Polynomial.C := by
  apply RingHom.ext
  intro P
  change specialize (Function.uncurry c) (MvPolynomial.C (Polynomial.C P)) = Polynomial.C P
  exact specialize_C _ _

theorem specialize_row (l : List M.FactorIndex)
    (c : Fin l.length → M.Variable → K) (j : Fin l.length) :
    specialize (R := SlicePolynomial M) (Function.uncurry c) (row M l j) =
      Polynomial.C (MixedFlag.polynomial M l c j) := by
  classical
  simp [row, fixed, MixedFlag.polynomial, MixedFlag.rowForm, Algebra.smul_def,
    MvPolynomial.algebraMap_eq]

/-- Fixing the coefficient parameters recovers exactly the normalized mixed
equations and the inverse equation used in the original finite slice. -/
theorem specialize_ideal (W : Set M.Point) (l : List M.FactorIndex)
    (b : ∀ i : M.FactorIndex, Fin (M.ambientDimension i + 1))
    (H : M.CoordinateRing) (c : Fin l.length → M.Variable → K) :
    (ideal M W l b H).map (specialize (R := SlicePolynomial M) (Function.uncurry c)).toRingHom =
      (((MixedFlag.ideal M (M.vanishingIdeal W) l c l.length) ⊔
        Ideal.span (Set.range (fun i : M.FactorIndex =>
          (MvPolynomial.X (⟨i,b i⟩ : M.Variable) : M.CoordinateRing) - 1))).map
          Polynomial.C ⊔ Ideal.span {Polynomial.C H * Polynomial.X - 1}) := by
  have hf (I : Ideal M.CoordinateRing) :
      (I.map (fixed M l)).map
        (specialize (R := SlicePolynomial M) (Function.uncurry c)).toRingHom =
          I.map Polynomial.C := by
    rw [Ideal.map_map, specialize_fixed]
  simp only [ideal, Ideal.map_sup, hf]
  have hrow (j : Fin l.length) :
      (specialize (R := SlicePolynomial M) (Function.uncurry c)).toRingHom (row M l j) =
        Polynomial.C (MixedFlag.polynomial M l c j) := specialize_row M l c j
  have hconst (P : SlicePolynomial M) :
      (specialize (R := SlicePolynomial M) (Function.uncurry c)).toRingHom (C P) = P :=
    specialize_C _ _
  simp only [MixedFlag.ideal, Ideal.map_sup, Ideal.map_iSup, Ideal.map_span,
    Set.image_singleton, hrow, hconst]

theorem parameter_ideal_eq_kernel (l : List M.FactorIndex)
    (c : Fin l.length → M.Variable → K) :
    (MvPolynomial.vanishingIdeal K {Function.uncurry c}).map
      (algebraMap (ParameterRing M l) (TotalPolynomial M l)) =
        RingHom.ker (specialize (R := SlicePolynomial M) (Function.uncurry c)) := by
  rw [ker_specialize]
  congr 1
  ext P
  simp [RingHom.mem_ker]

/-- Finiteness of the explicit initial slice is finiteness of the actual
closed fiber of the universal coefficient algebra. -/
theorem finite_fiber (W : Set M.Point) (l : List M.FactorIndex)
    (b : ∀ i : M.FactorIndex, Fin (M.ambientDimension i + 1))
    (H : M.CoordinateRing) (c : Fin l.length → M.Variable → K)
    (hfinite : Module.Finite K ((Polynomial M.CoordinateRing) ⧸
      (((MixedFlag.ideal M (M.vanishingIdeal W) l c l.length) ⊔
        Ideal.span (Set.range (fun i : M.FactorIndex =>
          (MvPolynomial.X (⟨i,b i⟩ : M.Variable) : M.CoordinateRing) - 1))).map
          Polynomial.C ⊔ Ideal.span {Polynomial.C H * Polynomial.X - 1}))) :
    Module.Finite K ((CoordinateRing M W l b H) ⧸
      (MvPolynomial.vanishingIdeal K {Function.uncurry c}).map
        (algebraMap (ParameterRing M l) (CoordinateRing M W l b H))) := by
  let J := ideal M W l b H
  let f := specialize (R := SlicePolynomial M) (Function.uncurry c)
  haveI : Module.Finite K (SlicePolynomial M ⧸ J.map f) := by
    change Module.Finite K (SlicePolynomial M ⧸ (ideal M W l b H).map
      (specialize (R := SlicePolynomial M) (Function.uncurry c)).toRingHom)
    rw [specialize_ideal]
    exact hfinite
  have hparam : (MvPolynomial.vanishingIdeal K {Function.uncurry c}).map
      (algebraMap (ParameterRing M l) (CoordinateRing M W l b H)) =
        (RingHom.ker f).map (Ideal.Quotient.mk J) := by
    rw [← parameter_ideal_eq_kernel M l c, Ideal.map_map]
    rfl
  rw [hparam]
  exact Module.Finite.equiv
    (quotientFiberEquiv f (specialize_surjective _) J).symm.toLinearEquiv

/-- The universal mixed family is quasi-finite at every prime of a finite
initial slice. This uses the actual family, with all coefficient variables. -/
theorem quasiFiniteAt_fiber (W : Set M.Point) (l : List M.FactorIndex)
    (b : ∀ i : M.FactorIndex, Fin (M.ambientDimension i + 1))
    (H : M.CoordinateRing) (c : Fin l.length → M.Variable → K)
    (hfinite : Module.Finite K ((Polynomial M.CoordinateRing) ⧸
      (((MixedFlag.ideal M (M.vanishingIdeal W) l c l.length) ⊔
        Ideal.span (Set.range (fun i : M.FactorIndex =>
          (MvPolynomial.X (⟨i,b i⟩ : M.Variable) : M.CoordinateRing) - 1))).map
          Polynomial.C ⊔ Ideal.span {Polynomial.C H * Polynomial.X - 1})))
    (q : PrimeSpectrum (CoordinateRing M W l b H))
    (hq : q.asIdeal.under (ParameterRing M l) =
      MvPolynomial.vanishingIdeal K {Function.uncurry c}) :
    Algebra.QuasiFiniteAt (ParameterRing M l) q.asIdeal := by
  haveI : Algebra.FiniteType (ParameterRing M l) (CoordinateRing M W l b H) :=
    Algebra.FiniteType.of_restrictScalars_finiteType K _ _
  exact quasiFiniteAt_of_finite_fiber _ q.asIdeal hq (finite_fiber M W l b H c hfinite)

end PhilipponMultiplicity.MixedFamily
end

end


section

set_option autoImplicit false
open scoped Topology BigOperators ContDiff
open Filter
noncomputable section

namespace PhilipponMultiplicity
variable {K E : Type*} [NontriviallyNormedField K]
  [NormedAddCommGroup E] [NormedSpace K E]

/-- Multiplication preserves a vanishing finite jet. -/
theorem iteratedFDeriv_mul_eq_zero_of_vanishing_jet
    {f u : E → K} {x : E} {n : ℕ}
    (hf : ContDiffAt K n f x) (hu : ContDiffAt K n u x)
    (hz : ∀ i ≤ n, iteratedFDeriv K i f x = 0) :
    iteratedFDeriv K n (fun y => u y * f y) x = 0 := by
  obtain ⟨s, hs, hopen, hxs⟩ := eventually_nhds_iff.mp
    ((hf.eventually (by simp)).and (hu.eventually (by simp)))
  have hfs : ContDiffOn K n f s := fun y hy => (hs y hy).1.contDiffWithinAt
  have hus : ContDiffOn K n u s := fun y hy => (hs y hy).2.contDiffWithinAt
  have hbound := norm_iteratedFDerivWithin_mul_le hus hfs hopen.uniqueDiffOn hxs
    (le_refl (n : ℕ∞ω))
  simp only [iteratedFDerivWithin_of_isOpen _ hopen hxs] at hbound
  have hsum : (∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) *
      ‖iteratedFDeriv K i u x‖ * ‖iteratedFDeriv K (n - i) f x‖) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    simp [hz (n - i) (Nat.sub_le _ _)]
  rw [hsum] at hbound
  exact norm_eq_zero.mp (le_antisymm hbound (norm_nonneg _))

def jetOrder (f : E → K) (x : E) : WithTop ℕ :=
  sInf ((fun n : ℕ => (n : WithTop ℕ)) '' {n | iteratedFDeriv K n f x ≠ 0})

theorem natCast_le_jetOrder_iff {f : E → K} {x : E} {n : ℕ} :
    (n : WithTop ℕ) ≤ jetOrder f x ↔
      ∀ i < n, iteratedFDeriv K i f x = 0 := by
  constructor
  · intro h i hi
    by_contra hne
    have hle : jetOrder f x ≤ (i : WithTop ℕ) := sInf_le ⟨i, hne, rfl⟩
    have : n ≤ i := by exact_mod_cast h.trans hle
    omega
  · intro h
    apply le_sInf
    rintro _ ⟨i, hi, rfl⟩
    by_contra! hlt
    have hin : i < n := by exact_mod_cast hlt
    exact hi (h i hin)

theorem jetOrder_congr {f g : E → K} {x : E} (h : f =ᶠ[𝓝 x] g) :
    jetOrder f x = jetOrder g x := by
  unfold jetOrder
  congr 3
  ext n
  rw [(h.iteratedFDeriv K n).eq_of_nhds]

/-- An analytic unit does not change the order defined by iterated Fréchet derivatives. -/
theorem jetOrder_mul_unit [CompleteSpace K] {f u : E → K} {x : E}
    (hf : AnalyticAt K f x) (hu : AnalyticAt K u x) (hu0 : u x ≠ 0) :
    jetOrder (fun y => u y * f y) x = jetOrder f x := by
  apply WithTop.eq_of_forall_coe_le_iff
  intro n
  change ((n : WithTop ℕ) ≤ jetOrder (fun y => u y * f y) x) ↔
    (n : WithTop ℕ) ≤ jetOrder f x
  rw [natCast_le_jetOrder_iff, natCast_le_jetOrder_iff]
  have hunit : ∀ᶠ y in 𝓝 x, u y ≠ 0 := hu.continuousAt.eventually_ne hu0
  have hinv : (fun y => (u y)⁻¹ * (u y * f y)) =ᶠ[𝓝 x] f := by
    filter_upwards [hunit] with y hy
    simp [hy]
  constructor
  · intro h i hi
    have hz := iteratedFDeriv_mul_eq_zero_of_vanishing_jet
      (hu.mul hf).contDiffAt (hu.inv hu0).contDiffAt
      (fun j hj => h j (hj.trans_lt hi))
    change iteratedFDeriv K i (fun y => (u y)⁻¹ * (u y * f y)) x = 0 at hz
    rw [(hinv.iteratedFDeriv K i).eq_of_nhds] at hz
    exact hz
  · intro h i hi
    exact iteratedFDeriv_mul_eq_zero_of_vanishing_jet hf.contDiffAt hu.contDiffAt
      (fun j hj => h j (hj.trans_lt hi))

end PhilipponMultiplicity
end

end


section

set_option autoImplicit false
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators Topology
open Filter MvPolynomial
noncomputable section

namespace PhilipponMultiplicity

theorem MultiProjectiveSpace.eval_block_scale {K : Type*} [Field K]
    (M : MultiProjectiveSpace K) (P : M.CoordinateRing)
    (D : M.FactorIndex → ℕ) (hP : M.IsHomogeneous P D)
    (v : M.Variable → K) (a : M.FactorIndex → K) :
    MvPolynomial.eval (fun j => a j.1 * v j) P = (∏ i, a i ^ D i) * MvPolynomial.eval v P := by
  classical
  rw [eval_eq', eval_eq', Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d hd
  have hscale : (∏ j : M.Variable, a j.1 ^ d j) = ∏ i, a i ^ D i := by
    rw [Fintype.prod_sigma]
    apply Finset.prod_congr rfl
    intro i _
    change (∏ j : Fin (M.ambientDimension i + 1), a i ^ d ⟨i, j⟩) = a i ^ D i
    rw [Finset.prod_pow_eq_pow_sum, hP d hd i]
  simp only [mul_pow, Finset.prod_mul_distrib, hscale]
  ring

private theorem coordinate_ratio {K : Type*} [Field K] {ι : Type*}
    {f g : ι → K} {hf : f ≠ 0} {hg : g ≠ 0}
    (h : Projectivization.mk K f hf = Projectivization.mk K g hg)
    (j : ι) (hj : g j ≠ 0) :
    f j / g j ≠ 0 ∧ ∀ k, f k = (f j / g j) * g k := by
  obtain ⟨a, ha⟩ := (Projectivization.mk_eq_mk_iff K f g hf hg).mp h
  have hj' : f j = (a : K) * g j := by
    simpa only [Pi.smul_apply, Units.smul_def, smul_eq_mul] using (congrFun ha j).symm
  have hratio : f j / g j = (a : K) := by rw [hj']; exact mul_div_cancel_right₀ _ hj
  rw [hratio]
  refine ⟨a.ne_zero, ?_⟩
  intro k
  simpa only [Pi.smul_apply, Units.smul_def, smul_eq_mul] using (congrFun ha k).symm

/-- Locally equal projective lifts change a multihomogeneous pullback by an analytic unit. -/
theorem MultiProjectiveSpace.jetOrder_eq_of_projective_lifts
    {K E : Type*} [NontriviallyNormedField K] [CompleteSpace K]
    [NormedAddCommGroup E] [NormedSpace K E]
    (M : MultiProjectiveSpace K) (P : M.CoordinateRing)
    (D : M.FactorIndex → ℕ) (hP : M.IsHomogeneous P D)
    (f g : E → M.Variable → K) (x : E)
    (hf : ∀ v, AnalyticAt K (fun z => f z v) x)
    (hg : ∀ v, AnalyticAt K (fun z => g z v) x)
    (hrep : ∀ᶠ z in 𝓝 x, ∀ i : M.FactorIndex,
      ∃ hfi : (fun j => f z ⟨i, j⟩) ≠ 0,
      ∃ hgi : (fun j => g z ⟨i, j⟩) ≠ 0,
        Projectivization.mk K (fun j => f z ⟨i, j⟩) hfi =
          Projectivization.mk K (fun j => g z ⟨i, j⟩) hgi) :
    jetOrder (fun z => MvPolynomial.eval (f z) P) x = jetOrder (fun z => MvPolynomial.eval (g z) P) x := by
  classical
  have hpivot (i : M.FactorIndex) : ∃ j, g x ⟨i, j⟩ ≠ 0 := by
    obtain ⟨_, hgi, _⟩ := hrep.self_of_nhds i
    simpa only [ne_eq, funext_iff, Pi.zero_apply, not_forall] using hgi
  choose j hj using hpivot
  let a (z : E) (i : M.FactorIndex) := f z ⟨i, j i⟩ / g z ⟨i, j i⟩
  let u (z : E) := ∏ i, a z i ^ D i
  have ha (i : M.FactorIndex) : AnalyticAt K (fun z => a z i) x :=
    (hf _).div (hg _) (hj i)
  have hu : AnalyticAt K u x := by
    exact Finset.analyticAt_fun_prod _ (fun i _ => (ha i).pow (D i))
  have hax (i : M.FactorIndex) : a x i ≠ 0 := by
    obtain ⟨hfi, hgi, heq⟩ := hrep.self_of_nhds i
    exact (coordinate_ratio heq (j i) (hj i)).1
  have hux : u x ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun i _ => pow_ne_zero _ (hax i))
  have hjnear : ∀ᶠ z in 𝓝 x, ∀ i : M.FactorIndex, g z ⟨i, j i⟩ ≠ 0 := by
    rw [Filter.eventually_all]
    intro i
    exact (hg _).continuousAt.eventually_ne (hj i)
  have hfg : (fun z => MvPolynomial.eval (f z) P) =ᶠ[𝓝 x]
      (fun z => u z * MvPolynomial.eval (g z) P) := by
    filter_upwards [hrep, hjnear] with z hz hjz
    have hcoords : f z = fun v => a z v.1 * g z v := by
      funext v
      obtain ⟨hfi, hgi, heq⟩ := hz v.1
      exact (coordinate_ratio heq (j v.1) (hjz v.1)).2 v.2
    rw [hcoords, M.eval_block_scale P D hP]
  have hgP : AnalyticAt K (fun z => MvPolynomial.eval (g z) P) x := by
    change AnalyticAt K (fun z => aeval (g z) P) x
    exact AnalyticAt.aeval_mvPolynomial hg P
  exact (jetOrder_congr hfg).trans (jetOrder_mul_unit hgP hu hux)

private theorem completeSpace_of_isometric_ringEquiv
    {K F : Type*} [NontriviallyNormedField K] [NontriviallyNormedField F]
    [CompleteSpace F] (e : K ≃+* F) (he : Isometry e) : CompleteSpace K :=
  (he.isUniformInducing.completeSpace_congr e.surjective).mpr inferInstance

theorem IsPhilipponBaseField.completeSpace {K : Type*} [NontriviallyNormedField K]
    (hK : IsPhilipponBaseField K) : CompleteSpace K := by
  rcases hK with ⟨e, he⟩ | ⟨p, hp, h⟩
  · exact completeSpace_of_isometric_ringEquiv e he
  · letI : Fact p.Prime := ⟨hp⟩
    obtain ⟨e, he⟩ := h
    exact completeSpace_of_isometric_ringEquiv e he

/-- The independence assertion in Philippon's definition of contact order, p. 358. -/
theorem projective_lift_contact_invariance
    (K : Type*) [NontriviallyNormedField K] (hK : IsPhilipponBaseField K)
    (G : EmbeddedGroupProduct K) (A : AnalyticSubgroup G)
    (g : G.Point) (P : G.CoordinateRing) (D : G.FactorIndex → ℕ)
    (hP : IsMultihomogeneousOfDegree G P D)
    (f : A.ParameterSpace → G.ambient.Variable → K)
    (hf : ∀ v, AnalyticAt K (fun z => f z v) 0)
    (hrep : ∀ᶠ z in 𝓝 (0 : A.ParameterSpace), ∃ hz : z ∈ A.domain,
      ∀ i : G.FactorIndex, ∃ h : (fun j => f z ⟨i, j⟩) ≠ 0,
        Projectivization.mk K (fun j => f z ⟨i, j⟩) h =
          G.embedding (g + A.map ⟨z, hz⟩) i) :
    vanishingOrder A P g = sInf ((fun n : ℕ => (n : WithTop ℕ)) ''
      {n | iteratedFDeriv K n (fun z => MvPolynomial.eval (f z) P) 0 ≠ 0}) := by
  letI : CompleteSpace K := hK.completeSpace
  apply G.ambient.jetOrder_eq_of_projective_lifts P D hP
    (A.lift g) f 0 (A.lift_analytic g) hf
  filter_upwards [A.lift_represents g, hrep] with z hz hfz
  obtain ⟨hz, hAz⟩ := hz
  obtain ⟨hfz, hFz⟩ := hfz
  intro i
  obtain ⟨hA, heqA⟩ := hAz i
  obtain ⟨hF, heqF⟩ := hFz i
  exact ⟨hA, hF, heqA.trans heqF.symm⟩

end PhilipponMultiplicity
end

end


section

set_option autoImplicit false
set_option maxHeartbeats 300000
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators Topology
open Filter MvPolynomial
noncomputable section

namespace PhilipponMultiplicity

theorem MultiProjectiveSpace.eval_lift_eq_zero_of_mem_vanishingIdeal
    {K : Type*} [Field K] (M : MultiProjectiveSpace K)
    {V : Set M.Point} {p : M.Point} (hp : p ∈ V)
    (v : M.Variable → K)
    (hv : ∀ i, ∃ h : (fun j => v ⟨i, j⟩) ≠ 0,
      Projectivization.mk K (fun j => v ⟨i, j⟩) h = p i)
    {P : M.CoordinateRing} (hP : P ∈ M.vanishingIdeal V) :
    MvPolynomial.eval v P = 0 := by
  classical
  have ha (i : M.FactorIndex) : ∃ a : Kˣ,
      ∀ j, v ⟨i, j⟩ = (a : K) * (p i).rep j := by
    obtain ⟨h, he⟩ := hv i
    obtain ⟨a, ha⟩ := (Projectivization.mk_eq_mk_iff K _ _ h
      (Projectivization.rep_nonzero (p i))).mp
      (he.trans (Projectivization.mk_rep (p i)).symm)
    refine ⟨a, fun j => ?_⟩
    simpa only [Pi.smul_apply, Units.smul_def, smul_eq_mul] using (congrFun ha j).symm
  choose a ha using ha
  have hv' : v = fun j => (a j.1 : K) * M.coordinate p j := by
    funext j
    exact ha j.1 j.2
  have hideal : M.vanishingIdeal V ≤ RingHom.ker (MvPolynomial.eval v) := by
    apply Ideal.span_le.mpr
    rintro Q ⟨⟨D, hD⟩, hz⟩
    change MvPolynomial.eval v Q = 0
    rw [hv', M.eval_block_scale Q D hD (M.coordinate p) (fun i => (a i : K)),
      show MvPolynomial.eval (M.coordinate p) Q = 0
      from hz p hp, mul_zero]
  exact hideal hP

/-- Containment forces every defining equation to have zero first derivative along A. -/
theorem analyticCodimension_eq_zero_of_carrier_subset
    {K : Type*} [NontriviallyNormedField K]
    {G : EmbeddedGroupProduct K} (A : AnalyticSubgroup G) (H : AlgebraicSubgroup G)
    (hsub : A.carrier ⊆ H.carrier) : analyticCodimension A H.carrier = 0 := by
  have hker : A.tangentKernel H.carrier = ⊤ := by
    apply top_unique
    intro t _
    apply (Submodule.mem_iInf _).mpr
    intro P
    have hpull : A.pullback P.val 0 =ᶠ[𝓝 0] (fun _ => (0 : K)) := by
      filter_upwards [A.lift_represents 0] with z hz
      obtain ⟨hz, hlift⟩ := hz
      have hmem : A.map ⟨z, hz⟩ ∈ H.carrier :=
        hsub (AddSubgroup.subset_closure ⟨⟨z, hz⟩, rfl⟩)
      apply G.ambient.eval_lift_eq_zero_of_mem_vanishingIdeal
        (Set.mem_image_of_mem G.embedding hmem) (A.lift 0 z) _ P.property
      intro i
      obtain ⟨h, he⟩ := hlift i
      exact ⟨h, by simpa only [zero_add] using he⟩
    change fderiv K (A.pullback P.val 0) 0 t = 0
    rw [hpull.fderiv_eq]
    simp
  unfold analyticCodimension
  rw [hker, finrank_top]
  simp [AnalyticSubgroup.ParameterSpace]

end PhilipponMultiplicity
end

end


section

set_option autoImplicit false
set_option maxHeartbeats 900000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators
noncomputable section

namespace PhilipponMultiplicity.GenericChoice
variable {K σ : Type*} [Field K] [Infinite K]

theorem exists_eval_ne_zero (F : MvPolynomial σ K) (hF : F ≠ 0) :
    ∃ x : σ → K, MvPolynomial.eval x F ≠ 0 := by
  by_contra! h
  apply hF
  apply MvPolynomial.funext
  intro x
  simpa using h x

/-- A nonempty principal open in affine space meets the complement of any
finite union of proper linear subspaces. -/
theorem exists_eval_ne_zero_avoiding_subspaces [Fintype σ]
    (S : Finset (Submodule K (σ → K))) (hS : ∀ U ∈ S, U ≠ ⊤)
    (F : MvPolynomial σ K) (hF : F ≠ 0) :
    ∃ x : σ → K, MvPolynomial.eval x F ≠ 0 ∧ ∀ U ∈ S, x ∉ U := by
  classical
  induction S using Finset.induction_on generalizing F with
  | empty =>
    obtain ⟨x,hx⟩ := exists_eval_ne_zero F hF
    exact ⟨x,hx,by simp⟩
  | @insert U S hUS ih =>
    have hU : U ≠ ⊤ := hS U (Finset.mem_insert_self _ _)
    obtain ⟨v,hv⟩ : ∃ v : σ → K, v ∉ U := by
      by_contra! h
      exact hU (top_unique (fun x _ => h x))
    obtain ⟨f,hfv,hUf⟩ := Submodule.exists_le_ker_of_notMem hv
    let g : MvPolynomial σ K := ∑ i, MvPolynomial.C (f (Pi.single i 1)) * MvPolynomial.X i
    have heval (x : σ → K) : MvPolynomial.eval x g = f x := by
      calc
        MvPolynomial.eval x g = ∑ i, f (Pi.single i 1) * x i := by simp [g]
        _ = f (∑ i, x i • Pi.single i (1 : K)) := by
          simp [map_sum, map_smul, smul_eq_mul, mul_comm]
        _ = f x := by
          congr 1
          ext j
          simp [Pi.single_apply]
    have hg : g ≠ 0 := by
      intro hz
      have := heval v
      rw [hz, map_zero] at this
      exact hfv this.symm
    obtain ⟨x,hx,havoid⟩ := ih (fun V hV => hS V (Finset.mem_insert_of_mem hV))
      (F * g) (mul_ne_zero hF hg)
    rw [map_mul, mul_ne_zero_iff] at hx
    refine ⟨x,hx.1,?_⟩
    intro V hV
    rcases Finset.mem_insert.mp hV with rfl | hV
    · intro hxU
      apply hx.2
      rw [heval]
      exact hUf hxU
    · exact havoid V hV

/-- A finite sequence of choices can be made inside any principal open,
provided each next-row condition is dense and only depends on its prefix. -/
theorem exists_sequential_choice
    (n : ℕ) (Good : Fin n → (Fin n → σ → K) → Prop)
    (hprefix : ∀ i c d, (∀ j : Fin n, j.val ≤ i.val → c j = d j) →
      (Good i c ↔ Good i d))
    (hdense : ∀ (i : Fin n) (c : Fin n → σ → K) (F : MvPolynomial σ K),
      F ≠ 0 → ∃ a : σ → K, MvPolynomial.eval a F ≠ 0 ∧
        Good i (Function.update c i a))
    (F : MvPolynomial (Fin n × σ) K) (hF : F ≠ 0) :
    ∃ c : Fin n → σ → K, MvPolynomial.eval (Function.uncurry c) F ≠ 0 ∧
      ∀ i, Good i c := by
  classical
  have haux : ∀ k : ℕ, k ≤ n →
      ∃ c : Fin n → σ → K, MvPolynomial.eval (Function.uncurry c) F ≠ 0 ∧
        ∀ i : Fin n, i.val < k → Good i c := by
    intro k
    induction k with
    | zero =>
      intro _
      obtain ⟨x,hx⟩ := exists_eval_ne_zero F hF
      exact ⟨Function.curry x, by simpa using hx, by simp⟩
    | succ k ih =>
      intro hkn
      have hk : k < n := by omega
      let i : Fin n := ⟨k,hk⟩
      obtain ⟨c,hc,hgood⟩ := ih (by omega)
      let G : MvPolynomial σ K := MvPolynomial.bind₁
        (fun w : Fin n × σ => if w.1 = i then MvPolynomial.X w.2
          else MvPolynomial.C (c w.1 w.2)) F
      have heval (a : σ → K) :
          MvPolynomial.eval a G =
            MvPolynomial.eval (Function.uncurry (Function.update c i a)) F := by
        change MvPolynomial.eval₂Hom (RingHom.id K) a
          (MvPolynomial.bind₁ _ F) = _
        rw [MvPolynomial.eval₂Hom_bind₁]
        apply congrArg (fun y : Fin n × σ → K => MvPolynomial.eval y F)
        funext w
        by_cases hw : w.1 = i
        · simp [hw, Function.uncurry]
        · simp [hw, Function.uncurry, Function.update_of_ne hw]
      have hG : G ≠ 0 := by
        intro hz
        have hh := heval (c i)
        rw [hz, map_zero, Function.update_eq_self] at hh
        exact hc hh.symm
      obtain ⟨a,ha,hnew⟩ := hdense i c G hG
      refine ⟨Function.update c i a, (heval a).symm ▸ ha, ?_⟩
      intro j hj
      by_cases hji : j = i
      · simpa [hji] using hnew
      · have hjk : j.val < k := by
          have hne : j.val ≠ k := fun h => hji (Fin.ext h)
          omega
        apply (hprefix j c (Function.update c i a) ?_).mp (hgood j hjk)
        intro t ht
        have hti : t ≠ i := by
          intro hti
          have : t.val = k := congrArg Fin.val hti
          omega
        exact (Function.update_of_ne hti _ _).symm
  obtain ⟨c,hc,hgood⟩ := haux n le_rfl
  exact ⟨c,hc,fun i => hgood i i.isLt⟩

end PhilipponMultiplicity.GenericChoice

end

end


section

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators
noncomputable section

namespace PhilipponMultiplicity.MixedFlag
variable {K : Type*} [Field K] (M : MultiProjectiveSpace K)

theorem rowForm_single (i : M.FactorIndex) (j : Fin (M.ambientDimension i + 1)) :
    rowForm M i (Pi.single ⟨i,j⟩ 1) = MvPolynomial.X ⟨i,j⟩ := by
  classical
  simp [rowForm, Pi.single_apply]

theorem rowForm_homogeneous (b : M.FactorIndex) (a : M.Variable → K) :
    M.IsHomogeneous (rowForm M b a) (Pi.single b 1) := by
  classical
  intro m hm i
  change m ∈ (∑ t : Fin (M.ambientDimension b + 1),
    a ⟨b,t⟩ • (MvPolynomial.X ⟨b,t⟩ : M.CoordinateRing)).support at hm
  have hs := MvPolynomial.support_sum (s := Finset.univ)
    (f := fun t : Fin (M.ambientDimension b + 1) =>
      a ⟨b,t⟩ • (MvPolynomial.X ⟨b,t⟩ : M.CoordinateRing)) hm
  obtain ⟨t, _, ht⟩ := Finset.mem_biUnion.mp hs
  have hmX : m ∈ (MvPolynomial.X (⟨b,t⟩ : M.Variable) : M.CoordinateRing).support :=
    MvPolynomial.support_smul ht
  simp only [MvPolynomial.support_X, Finset.mem_singleton] at hmX
  subst m
  by_cases hi : i = b
  · subst i
    simp [Finsupp.single_apply, Sigma.mk.inj_iff, Pi.single_apply]
  · have hn (k : Fin (M.ambientDimension i + 1)) :
        (⟨b,t⟩ : M.Variable) ≠ ⟨i,k⟩ := by
      intro h
      exact hi (congrArg Sigma.fst h).symm
    simp [Finsupp.single_apply, Pi.single_apply, hi, hn]

theorem polynomial_homogeneous (l : List M.FactorIndex)
    (c : Fin l.length → M.Variable → K) (j : Fin l.length) :
    M.IsHomogeneous (polynomial M l c j) (Pi.single l[j] 1) :=
  rowForm_homogeneous M l[j] (c j)

theorem ideal_zero (I : Ideal M.CoordinateRing) (l : List M.FactorIndex)
    (c : Fin l.length → M.Variable → K) : ideal M I l c 0 = I := by
  simp [ideal]

theorem ideal_prefix (I : Ideal M.CoordinateRing) (l : List M.FactorIndex)
    (c d : Fin l.length → M.Variable → K) (k : ℕ)
    (h : ∀ j : Fin l.length, j.val < k → c j = d j) :
    ideal M I l c k = ideal M I l d k := by
  classical
  unfold ideal
  congr 1
  apply iSup_congr
  intro j
  apply iSup_congr
  intro hj
  simp [polynomial, h j hj]

theorem ideal_succ (I : Ideal M.CoordinateRing) (l : List M.FactorIndex)
    (c : Fin l.length → M.Variable → K) (k : ℕ) (hk : k < l.length) :
    ideal M I l c (k+1) = ideal M I l c k ⊔
      Ideal.span {polynomial M l c ⟨k,hk⟩} := by
  unfold ideal
  apply le_antisymm
  · refine sup_le (le_sup_of_le_left le_sup_left) ?_
    refine iSup_le fun j => iSup_le fun hj => ?_
    by_cases hjk : j.val < k
    · exact le_sup_of_le_left (le_sup_of_le_right
        (le_iSup_of_le j (le_iSup_of_le hjk le_rfl)))
    · have he : j = ⟨k,hk⟩ := Fin.ext (by change j.val = k; omega)
      subst j
      exact le_sup_right
  · refine sup_le (sup_le le_sup_left ?_) ?_
    · refine iSup_le fun j => iSup_le fun hj => ?_
      exact le_sup_of_le_right (le_iSup_of_le j (le_iSup_of_le (by omega : j.val < k+1) le_rfl))
    · exact le_sup_of_le_right (le_iSup_of_le ⟨k,hk⟩ (le_iSup_of_le (by simp) le_rfl))

/-- Associated-prime avoidance in any nonempty principal open of one block's
coefficient space. No geometric hypotheses on the initial ideal are needed. -/
theorem exists_row_avoiding_associatedPrimes [Infinite K]
    (I : Ideal M.CoordinateRing) (i : M.FactorIndex)
    (F : MvPolynomial M.Variable K) (hF : F ≠ 0) :
    ∃ a : M.Variable → K, MvPolynomial.eval a F ≠ 0 ∧
      ∀ q ∈ associatedPrimes (M.CoordinateRing ⧸ I) (M.CoordinateRing ⧸ I),
        (∀ b : M.FactorIndex, ∃ j : Fin (M.ambientDimension b + 1),
          Ideal.Quotient.mk I (MvPolynomial.X ⟨b,j⟩) ∉ q) →
        Ideal.Quotient.mk I (rowForm M i a) ∉ q := by
  classical
  let Q := M.CoordinateRing ⧸ I
  let φ : (M.Variable → K) →ₗ[K] Q :=
    (Ideal.Quotient.mkₐ K I).toLinearMap.comp (rowForm M i)
  let bad (q : Ideal Q) : Submodule K (M.Variable → K) :=
    (q.restrictScalars K).comap φ
  let S := (associatedPrimes.finite Q Q).toFinset.filter
    (fun q => ∀ b : M.FactorIndex, ∃ j : Fin (M.ambientDimension b + 1),
      Ideal.Quotient.mk I (MvPolynomial.X ⟨b,j⟩) ∉ q)
  have hproper : ∀ U ∈ S.image bad, U ≠ ⊤ := by
    intro U hU
    obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hU
    obtain ⟨j,hj⟩ := (Finset.mem_filter.mp hq).2 i
    intro he
    have hv : Pi.single (⟨i,j⟩ : M.Variable) (1 : K) ∈ bad q := by
      rw [he]
      trivial
    change Ideal.Quotient.mk I (rowForm M i (Pi.single ⟨i,j⟩ 1)) ∈ q at hv
    rw [rowForm_single] at hv
    exact hj hv
  obtain ⟨a,ha,havoid⟩ := GenericChoice.exists_eval_ne_zero_avoiding_subspaces
    (S.image bad) hproper F hF
  refine ⟨a,ha,?_⟩
  intro q hq hblocks
  exact havoid (bad q) (Finset.mem_image.mpr ⟨q,
    Finset.mem_filter.mpr ⟨by simpa using hq, hblocks⟩,rfl⟩)

/-- Filter-regular flags meet every nonempty principal open of coefficient matrices. -/
theorem exists_flag_avoiding_associatedPrimes [Infinite K]
    (I : Ideal M.CoordinateRing) (l : List M.FactorIndex)
    (F : MvPolynomial (Fin l.length × M.Variable) K) (hF : F ≠ 0) :
    ∃ c : Fin l.length → M.Variable → K,
      MvPolynomial.eval (Function.uncurry c) F ≠ 0 ∧
      ∀ j : Fin l.length,
        ∀ q ∈ associatedPrimes (M.CoordinateRing ⧸ ideal M I l c j.val)
          (M.CoordinateRing ⧸ ideal M I l c j.val),
          (∀ b : M.FactorIndex, ∃ t : Fin (M.ambientDimension b + 1),
            Ideal.Quotient.mk (ideal M I l c j.val) (MvPolynomial.X ⟨b,t⟩) ∉ q) →
          Ideal.Quotient.mk (ideal M I l c j.val) (polynomial M l c j) ∉ q := by
  classical
  let Good (j : Fin l.length) (c : Fin l.length → M.Variable → K) : Prop :=
    ∀ q ∈ associatedPrimes (M.CoordinateRing ⧸ ideal M I l c j.val)
      (M.CoordinateRing ⧸ ideal M I l c j.val),
      (∀ b : M.FactorIndex, ∃ t : Fin (M.ambientDimension b + 1),
        Ideal.Quotient.mk (ideal M I l c j.val) (MvPolynomial.X ⟨b,t⟩) ∉ q) →
      Ideal.Quotient.mk (ideal M I l c j.val) (polynomial M l c j) ∉ q
  apply GenericChoice.exists_sequential_choice l.length Good ?_ ?_ F hF
  · intro j c d hp
    have hI := ideal_prefix M I l c d j.val (fun t ht => hp t (by omega))
    have hP : polynomial M l c j = polynomial M l d j := by
      simp [polynomial, hp j le_rfl]
    dsimp [Good]
    rw [hI,hP]
  · intro j c G hG
    obtain ⟨a,ha,havoid⟩ := exists_row_avoiding_associatedPrimes M
      (ideal M I l c j.val) l[j] G hG
    refine ⟨a,ha,?_⟩
    have hI : ideal M I l (Function.update c j a) j.val = ideal M I l c j.val := by
      apply ideal_prefix
      intro t ht
      exact Function.update_of_ne (fun he => by subst t; omega) _ _
    dsimp [Good]
    rw [hI]
    simpa [polynomial] using havoid

end PhilipponMultiplicity.MixedFlag

end

end


section

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false
open scoped BigOperators
noncomputable section
attribute [local instance] MvPolynomial.algebraMvPolynomial

namespace PhilipponMultiplicity.MixedFamily
open MvPolynomial SpecializationFiber
variable {K : Type*} [Field K] (M : MultiProjectiveSpace K)

/-- Evaluate the affine coordinates, inverse variable, and coefficient array. -/
def rawEvaluation (l : List M.FactorIndex) (c : Fin l.length → M.Variable → K)
    (v : M.Variable → K) (a : K) : TotalPolynomial M l →ₐ[K] K :=
  (Polynomial.eval₂AlgHom (MvPolynomial.aeval v) a (fun _ => Commute.all _ _)).comp
    (specialize (R := SlicePolynomial M) (Function.uncurry c))

@[simp] theorem rawEvaluation_fixed (l : List M.FactorIndex)
    (c : Fin l.length → M.Variable → K) (v : M.Variable → K) (a : K)
    (P : M.CoordinateRing) :
    rawEvaluation M l c v a (fixed M l P) = MvPolynomial.eval v P := by
  simp [rawEvaluation, fixed, Polynomial.eval₂AlgHom]

@[simp] theorem rawEvaluation_parameter (l : List M.FactorIndex)
    (c : Fin l.length → M.Variable → K) (v : M.Variable → K) (a : K)
    (P : ParameterRing M l) :
    rawEvaluation M l c v a (algebraMap (ParameterRing M l) (TotalPolynomial M l) P) =
      MvPolynomial.eval (Function.uncurry c) P := by
  have he := RingHom.congr_fun (specialize_comp (R := SlicePolynomial M) (Function.uncurry c)) P
  change specialize (Function.uncurry c)
    (algebraMap (ParameterRing M l) (TotalPolynomial M l) P) =
      algebraMap K (SlicePolynomial M) (MvPolynomial.eval (Function.uncurry c) P) at he
  simp only [rawEvaluation, AlgHom.comp_apply, he, AlgHom.commutes, Algebra.algebraMap_self]
  rfl

@[simp] theorem rawEvaluation_row (l : List M.FactorIndex)
    (c : Fin l.length → M.Variable → K) (v : M.Variable → K) (a : K)
    (j : Fin l.length) : rawEvaluation M l c v a (row M l j) =
      MvPolynomial.eval v (MixedFlag.polynomial M l c j) := by
  simp only [rawEvaluation, AlgHom.comp_apply, specialize_row]
  exact Polynomial.eval₂_C _ _

@[simp] theorem rawEvaluation_inverse (l : List M.FactorIndex)
    (c : Fin l.length → M.Variable → K) (v : M.Variable → K) (a : K)
    (H : M.CoordinateRing) :
    rawEvaluation M l c v a (C (Polynomial.C H * Polynomial.X - 1)) =
      MvPolynomial.eval v H * a - 1 := by
  simp only [rawEvaluation, AlgHom.comp_apply, specialize_C, map_sub, map_mul, map_one]
  change Polynomial.eval₂ (MvPolynomial.eval v) a (Polynomial.C H) *
    Polynomial.eval₂ (MvPolynomial.eval v) a Polynomial.X - 1 = _
  rw [Polynomial.eval₂_C, Polynomial.eval₂_X]

theorem mixed_polynomial_eval_zero (l : List M.FactorIndex)
    (c : Fin l.length → M.Variable → K) (x : M.Point) (v : M.Variable → K)
    (hrep : ∀ i, ∃ h : (fun j => v ⟨i,j⟩) ≠ 0,
      Projectivization.mk K (fun j => v ⟨i,j⟩) h = x i)
    (hz : ∀ j : Fin l.length, M.eval (MixedFlag.polynomial M l c j) x = 0)
    (j : Fin l.length) : MvPolynomial.eval v (MixedFlag.polynomial M l c j) = 0 := by
  apply M.eval_lift_eq_zero_of_mem_vanishingIdeal (Set.mem_singleton x) v hrep
  apply Ideal.subset_span
  refine ⟨⟨Pi.single l[j] 1, MixedFlag.polynomial_homogeneous M l c j⟩, ?_⟩
  rintro y rfl
  exact hz j

/-- A normalized projective point of the initial mixed section kills the
actual universal equations, so evaluation descends without radicalization. -/
theorem ideal_le_ker_rawEvaluation (W : Set M.Point) (l : List M.FactorIndex)
    (c : Fin l.length → M.Variable → K) (x : M.Point) (hx : x ∈ W)
    (b : ∀ i : M.FactorIndex, Fin (M.ambientDimension i + 1))
    (v : M.Variable → K) (hb : ∀ i, v ⟨i,b i⟩ = 1)
    (hrep : ∀ i, ∃ h : (fun j => v ⟨i,j⟩) ≠ 0,
      Projectivization.mk K (fun j => v ⟨i,j⟩) h = x i)
    (hz : ∀ j : Fin l.length, M.eval (MixedFlag.polynomial M l c j) x = 0)
    (H : M.CoordinateRing) (a : K) (ha : MvPolynomial.eval v H * a = 1) :
    ideal M W l b H ≤ RingHom.ker (rawEvaluation M l c v a) := by
  rw [ideal, sup_le_iff, sup_le_iff, sup_le_iff]
  refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
  · rw [Ideal.map_le_iff_le_comap]
    intro P hP
    change rawEvaluation M l c v a (fixed M l P) = 0
    rw [rawEvaluation_fixed]
    exact M.eval_lift_eq_zero_of_mem_vanishingIdeal hx v hrep hP
  · refine iSup_le fun j => iSup_le fun _ => Ideal.span_le.mpr ?_
    rintro P rfl
    change rawEvaluation M l c v a (row M l j) = 0
    rw [rawEvaluation_row]
    exact mixed_polynomial_eval_zero M l c x v hrep hz j
  · rw [Ideal.map_le_iff_le_comap]
    apply Ideal.span_le.mpr
    rintro P ⟨i,rfl⟩
    exact (rawEvaluation_fixed M l c v a _).trans (by simp [hb])
  · apply Ideal.span_le.mpr
    rintro P rfl
    change rawEvaluation M l c v a (C (Polynomial.C H * Polynomial.X - 1)) = 0
    rw [rawEvaluation_inverse, ha, sub_self]

/-- The selected point gives a rational point of the universal coefficient
algebra, with the original coordinates and coefficient specialization. -/
theorem exists_evaluation (W : Set M.Point) (l : List M.FactorIndex)
    (c : Fin l.length → M.Variable → K) (x : M.Point) (hx : x ∈ W)
    (b : ∀ i : M.FactorIndex, Fin (M.ambientDimension i + 1))
    (v : M.Variable → K) (hb : ∀ i, v ⟨i,b i⟩ = 1)
    (hrep : ∀ i, ∃ h : (fun j => v ⟨i,j⟩) ≠ 0,
      Projectivization.mk K (fun j => v ⟨i,j⟩) h = x i)
    (hz : ∀ j : Fin l.length, M.eval (MixedFlag.polynomial M l c j) x = 0)
    (H : M.CoordinateRing) (a : K) (ha : MvPolynomial.eval v H * a = 1) :
    ∃ e : CoordinateRing M W l b H →ₐ[K] K,
      (∀ P : M.CoordinateRing,
        e (Ideal.Quotient.mk (ideal M W l b H) (fixed M l P)) = MvPolynomial.eval v P) ∧
      ∀ P : ParameterRing M l,
        e (algebraMap (ParameterRing M l) (CoordinateRing M W l b H) P) =
          MvPolynomial.eval (Function.uncurry c) P := by
  let e := Ideal.Quotient.liftₐ (ideal M W l b H) (rawEvaluation M l c v a)
    (ideal_le_ker_rawEvaluation M W l c x hx b v hb hrep hz H a ha)
  refine ⟨e, ?_, ?_⟩
  · intro P
    exact rawEvaluation_fixed M l c v a P
  · intro P
    exact rawEvaluation_parameter M l c v a P

end PhilipponMultiplicity.MixedFamily
end

end


section

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false
noncomputable section
attribute [local instance] MvPolynomial.algebraMvPolynomial

namespace PhilipponMultiplicity.FiniteMixedModel

/-- Zariski's main theorem gives a finite coefficient subalgebra whose
localization agrees with the original algebra around a rational point. -/
theorem exists_finite_model_at_evaluation
    {K A B : Type*} [Field K] [CommRing A] [CommRing B]
    [Algebra K A] [Algebra A B] [Algebra K B] [IsScalarTower K A B]
    [Algebra.FiniteType A B] (e : B →ₐ[K] K) (q : PrimeSpectrum B)
    (heq : q.asIdeal = RingHom.ker e.toRingHom)
    (hq : Algebra.QuasiFiniteAt A q.asIdeal) :
    ∃ D : Subalgebra A B, Module.Finite A D ∧ ∃ r : D,
      e r.val ≠ 0 ∧ Function.Bijective (Localization.awayMap D.val.toRingHom r) := by
  letI := hq
  obtain ⟨D,hD,r,hr,hbij⟩ :=
    Algebra.QuasiFiniteAt.exists_fg_and_exists_notMem_and_awayMap_bijective
      (R := A) q.asIdeal
  refine ⟨D, ⟨(Submodule.fg_top _).mpr hD⟩, r, ?_, hbij⟩
  intro hz
  apply hr
  rw [heq]
  exact hz

open MixedFamily
variable {K : Type*} [Field K] (M : MultiProjectiveSpace K)

/-- Compatibility with coefficient evaluation identifies the contraction of
the point's kernel with the initial coefficient maximal ideal. -/
theorem evaluation_kernel_under (W : Set M.Point) (l : List M.FactorIndex)
    (c : Fin l.length → M.Variable → K)
    (b : ∀ i : M.FactorIndex, Fin (M.ambientDimension i + 1)) (H : M.CoordinateRing)
    (e : CoordinateRing M W l b H →ₐ[K] K)
    (he : ∀ P : ParameterRing M l,
      e (algebraMap (ParameterRing M l) (CoordinateRing M W l b H) P) =
        MvPolynomial.eval (Function.uncurry c) P) :
    (RingHom.ker e.toRingHom).under (ParameterRing M l) =
      MvPolynomial.vanishingIdeal K {Function.uncurry c} := by
  ext P
  change e (algebraMap (ParameterRing M l) (CoordinateRing M W l b H) P) = 0 ↔ _
  rw [he, MvPolynomial.mem_vanishingIdeal_singleton_iff]
  rfl

/-- The whole-fiber quasi-finiteness hypothesis supplies a finite model at
each selected rational point of the actual normalized universal family. -/
theorem exists_model (W : Set M.Point) (l : List M.FactorIndex)
    (c : Fin l.length → M.Variable → K)
    (b : ∀ i : M.FactorIndex, Fin (M.ambientDimension i + 1)) (H : M.CoordinateRing)
    (e : CoordinateRing M W l b H →ₐ[K] K)
    (he : ∀ P : ParameterRing M l,
      e (algebraMap (ParameterRing M l) (CoordinateRing M W l b H) P) =
        MvPolynomial.eval (Function.uncurry c) P)
    (hquasi : ∀ q : PrimeSpectrum (CoordinateRing M W l b H),
      q.asIdeal.under (ParameterRing M l) =
        MvPolynomial.vanishingIdeal K {Function.uncurry c} →
      Algebra.QuasiFiniteAt (ParameterRing M l) q.asIdeal) :
    ∃ D : Subalgebra (ParameterRing M l) (CoordinateRing M W l b H),
      Module.Finite (ParameterRing M l) D ∧ ∃ r : D,
        e r.val ≠ 0 ∧ Function.Bijective (Localization.awayMap D.val.toRingHom r) := by
  haveI : Algebra.FiniteType (ParameterRing M l) (CoordinateRing M W l b H) :=
    Algebra.FiniteType.of_restrictScalars_finiteType K _ _
  let q : PrimeSpectrum (CoordinateRing M W l b H) :=
    ⟨RingHom.ker e.toRingHom, RingHom.ker_isPrime e.toRingHom⟩
  exact exists_finite_model_at_evaluation e q rfl
    (hquasi q (evaluation_kernel_under M W l c b H e he))

end PhilipponMultiplicity.FiniteMixedModel
end

end


section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators Topology
noncomputable section

attribute [local instance] MvPolynomial.algebraMvPolynomial

namespace PhilipponMultiplicity
open SectionThree SectionThreeSupport

theorem quasifinite_persistence_of_finite_models
    (K : Type*) [NontriviallyNormedField K] (hK : IsPhilipponBaseField K)
    (hgeometry : ∀ (M : MultiProjectiveSpace K) (W : Set M.Point),
      @IsClosed _ M.zariskiTopology W → @IsIrreducible _ M.zariskiTopology W →
      ∀ (α : M.FactorIndex → ℕ), (∀ i, α i ≤ M.ambientDimension i) →
      (∑ i, α i = locusDimension M W) →
      ∀ l : List M.FactorIndex, (∀ i, l.count i = α i) →
      ∀ c₀ : Fin l.length → M.Variable → K,
      ∀ S : Set M.Point, S.Finite →
      S ⊆ {x : M.Point | x ∈ W ∧
        ∀ j : Fin l.length, M.eval (MixedFlag.polynomial M l c₀ j) x = 0} →
      (∀ x ∈ S,
        ∃ b : ∀ i : M.FactorIndex, Fin (M.ambientDimension i + 1),
        ∃ v : M.Variable → K, (∀ i, v ⟨i,b i⟩ = 1) ∧
          (∀ i : M.FactorIndex, ∃ h : (fun j => v ⟨i,j⟩) ≠ 0,
            Projectivization.mk K (fun j => v ⟨i,j⟩) h = x i) ∧
          ∃ H : M.CoordinateRing, ∃ a : K, MvPolynomial.eval v H * a = 1 ∧
            ∃ e : MixedFamily.CoordinateRing M W l b H →ₐ[K] K,
              (∀ P : M.CoordinateRing,
                e (Ideal.Quotient.mk (MixedFamily.ideal M W l b H) (MixedFamily.fixed M l P)) =
                  MvPolynomial.eval v P) ∧
              (∀ P : MixedFamily.ParameterRing M l,
                e (algebraMap (MixedFamily.ParameterRing M l) (MixedFamily.CoordinateRing M W l b H) P) =
                  MvPolynomial.eval (Function.uncurry c₀) P) ∧
              ∃ D : Subalgebra (MixedFamily.ParameterRing M l) (MixedFamily.CoordinateRing M W l b H),
                Module.Finite (MixedFamily.ParameterRing M l) D ∧ ∃ r : D,
                  e r.val ≠ 0 ∧ Function.Bijective (Localization.awayMap D.val.toRingHom r)) →
        ∃ U : Set (PrimeSpectrum (MvPolynomial (Fin l.length × M.Variable) K)),
          IsOpen U ∧
          (⟨MvPolynomial.vanishingIdeal K {Function.uncurry c₀}, inferInstance⟩ :
            PrimeSpectrum (MvPolynomial (Fin l.length × M.Variable) K)) ∈ U ∧
          ∀ c : Fin l.length → M.Variable → K,
            (⟨MvPolynomial.vanishingIdeal K {Function.uncurry c}, inferInstance⟩ :
              PrimeSpectrum (MvPolynomial (Fin l.length × M.Variable) K)) ∈ U →
            Nonempty (S ↪ {x : M.Point | x ∈ W ∧
              ∀ j : Fin l.length, M.eval (MixedFlag.polynomial M l c j) x = 0})) :
    ∀ (M : MultiProjectiveSpace K) (W : Set M.Point),
      @IsClosed _ M.zariskiTopology W → @IsIrreducible _ M.zariskiTopology W →
      ∀ (α : M.FactorIndex → ℕ), (∀ i, α i ≤ M.ambientDimension i) →
      (∑ i, α i = locusDimension M W) →
      ∀ l : List M.FactorIndex, (∀ i, l.count i = α i) →
      ∀ c₀ : Fin l.length → M.Variable → K,
      ∀ S : Set M.Point, S.Finite →
      S ⊆ {x : M.Point | x ∈ W ∧
        ∀ j : Fin l.length, M.eval (MixedFlag.polynomial M l c₀ j) x = 0} →
      (∀ x ∈ S,
        ∃ b : ∀ i : M.FactorIndex, Fin (M.ambientDimension i + 1),
        ∃ v : M.Variable → K, (∀ i, v ⟨i,b i⟩ = 1) ∧
          (∀ i : M.FactorIndex, ∃ h : (fun j => v ⟨i,j⟩) ≠ 0,
            Projectivization.mk K (fun j => v ⟨i,j⟩) h = x i) ∧
          ∃ H : M.CoordinateRing, ∃ a : K, MvPolynomial.eval v H * a = 1 ∧
            ∀ q : PrimeSpectrum (MixedFamily.CoordinateRing M W l b H),
              q.asIdeal.under (MixedFamily.ParameterRing M l) =
                MvPolynomial.vanishingIdeal K {Function.uncurry c₀} →
              Algebra.QuasiFiniteAt (MixedFamily.ParameterRing M l) q.asIdeal) →
        ∃ U : Set (PrimeSpectrum (MvPolynomial (Fin l.length × M.Variable) K)),
          IsOpen U ∧
          (⟨MvPolynomial.vanishingIdeal K {Function.uncurry c₀}, inferInstance⟩ :
            PrimeSpectrum (MvPolynomial (Fin l.length × M.Variable) K)) ∈ U ∧
          ∀ c : Fin l.length → M.Variable → K,
            (⟨MvPolynomial.vanishingIdeal K {Function.uncurry c}, inferInstance⟩ :
              PrimeSpectrum (MvPolynomial (Fin l.length × M.Variable) K)) ∈ U →
            Nonempty (S ↪ {x : M.Point | x ∈ W ∧
              ∀ j : Fin l.length, M.eval (MixedFlag.polynomial M l c j) x = 0}) := by
  intro M W hW hirr α hα hdim l hl c₀ S hS hSZ hfinite
  apply hgeometry M W hW hirr α hα hdim l hl c₀ S hS hSZ
  intro x hx
  obtain ⟨b,v,hb,hrep,H,a,ha,hquasi⟩ := hfinite x hx
  obtain ⟨e,hev,hec⟩ := MixedFamily.exists_evaluation M W l c₀ x (hSZ hx).1
    b v hb hrep (hSZ hx).2 H a ha
  obtain ⟨D,hD,r,hr,hbij⟩ := FiniteMixedModel.exists_model M W l c₀ b H e hec hquasi
  exact ⟨b,v,hb,hrep,H,a,ha,e,hev,hec,D,hD,r,hr,hbij⟩

end PhilipponMultiplicity
end

end

set_option autoImplicit false
open PhilipponMultiplicity PhilipponMultiplicity.SectionThree PhilipponMultiplicity.SectionThreeSupport
open scoped BigOperators Topology
attribute [local instance] MvPolynomial.algebraMvPolynomial

theorem solution
    (K : Type*) [NontriviallyNormedField K] (hK : IsPhilipponBaseField K) :
    ∀ (M : MultiProjectiveSpace K) (W : Set M.Point),
      @IsClosed _ M.zariskiTopology W → @IsIrreducible _ M.zariskiTopology W →
      ∀ (α : M.FactorIndex → ℕ), (∀ i, α i ≤ M.ambientDimension i) →
      (∑ i, α i = locusDimension M W) →
      ∀ l : List M.FactorIndex, (∀ i, l.count i = α i) →
      ∀ c₀ : Fin l.length → M.Variable → K,
      ∀ S : Set M.Point, S.Finite →
      S ⊆ {x : M.Point | x ∈ W ∧
        ∀ j : Fin l.length, M.eval (MixedFlag.polynomial M l c₀ j) x = 0} →
      (∀ x ∈ S,
        ∃ b : ∀ i : M.FactorIndex, Fin (M.ambientDimension i + 1),
        ∃ v : M.Variable → K, (∀ i, v ⟨i,b i⟩ = 1) ∧
          (∀ i : M.FactorIndex, ∃ h : (fun j => v ⟨i,j⟩) ≠ 0,
            Projectivization.mk K (fun j => v ⟨i,j⟩) h = x i) ∧
          ∃ H : M.CoordinateRing, ∃ a : K, MvPolynomial.eval v H * a = 1 ∧
            ∀ q : PrimeSpectrum (MixedFamily.CoordinateRing M W l b H),
              q.asIdeal.under (MixedFamily.ParameterRing M l) =
                MvPolynomial.vanishingIdeal K {Function.uncurry c₀} →
              Algebra.QuasiFiniteAt (MixedFamily.ParameterRing M l) q.asIdeal) →
        ∃ U : Set (PrimeSpectrum (MvPolynomial (Fin l.length × M.Variable) K)),
          IsOpen U ∧
          (⟨MvPolynomial.vanishingIdeal K {Function.uncurry c₀}, inferInstance⟩ :
            PrimeSpectrum (MvPolynomial (Fin l.length × M.Variable) K)) ∈ U ∧
          ∀ c : Fin l.length → M.Variable → K,
            (⟨MvPolynomial.vanishingIdeal K {Function.uncurry c}, inferInstance⟩ :
              PrimeSpectrum (MvPolynomial (Fin l.length × M.Variable) K)) ∈ U →
            Nonempty (S ↪ {x : M.Point | x ∈ W ∧
              ∀ j : Fin l.length, M.eval (MixedFlag.polynomial M l c j) x = 0}) := by
  exact quasifinite_persistence_of_finite_models K hK
    (exists_open_preserving_finite_model_mixed_slices K hK)
