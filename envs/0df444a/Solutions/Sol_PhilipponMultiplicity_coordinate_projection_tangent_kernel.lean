-- Prove2me | solution 1 for PhilipponMultiplicity.coordinate_projection_tangent_kernel
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-10-01T10:59:52.540987+00:00
-- url     : https://prove2.me/submissions/fc73464c-68e0-4b02-bac9-b1c789b39234

import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Definitions.Def_PhilipponMultiplicity_Analytic
import Mathlib.Analysis.Analytic.Polynomial
import Definitions.Def_PhilipponMultiplicity_Geometry
import Definitions.Def_PhilipponMultiplicity_FactorProjection
import Definitions.Def_PhilipponMultiplicity_ProjectedAnalytic


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


set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
noncomputable section

namespace PhilipponMultiplicity
universe u
namespace MultiProjectiveSpace

variable {K : Type*} [Field K] (M : MultiProjectiveSpace K)

theorem IsHomogeneous.mul {P Q : M.CoordinateRing} {D E : M.FactorIndex → ℕ}
    (hP : M.IsHomogeneous P D) (hQ : M.IsHomogeneous Q E) :
    M.IsHomogeneous (P * Q) (D + E) := by
  classical
  intro d hd i
  obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_add.mp (MvPolynomial.support_mul P Q hd)
  simpa only [Finsupp.add_apply, Finset.sum_add_distrib, Pi.add_apply, hP a ha i,
    hQ b hb i]

theorem isHomogeneous_one : M.IsHomogeneous 1 0 := by
  classical
  intro d hd i
  have hd0 : d = 0 := by simpa using hd
  simp [hd0]

theorem isOpen_basic (P : M.CoordinateRing) (D : M.FactorIndex → ℕ)
    (hP : M.IsHomogeneous P D) :
    @IsOpen _ M.zariskiTopology {x | M.eval P x ≠ 0} := by
  exact TopologicalSpace.isOpen_generateFrom_of_mem ⟨P, D, hP, rfl⟩

theorem isClosed_zero (P : M.CoordinateRing) (D : M.FactorIndex → ℕ)
    (hP : M.IsHomogeneous P D) :
    @IsClosed _ M.zariskiTopology {x | M.eval P x = 0} := by
  letI := M.zariskiTopology
  simpa only [Set.compl_setOf, not_not] using (M.isOpen_basic P D hP).isClosed_compl

theorem isTopologicalBasis_basic :
    @TopologicalSpace.IsTopologicalBasis _ M.zariskiTopology
      {U | ∃ P : M.CoordinateRing, ∃ D, M.IsHomogeneous P D ∧
        U = {x | M.eval P x ≠ 0}} := by
  classical
  letI := M.zariskiTopology
  have h := TopologicalSpace.isTopologicalBasis_of_subbasis_of_inter
    (show M.zariskiTopology = TopologicalSpace.generateFrom _ from rfl) (by
      rintro U ⟨P, D, hP, rfl⟩ V ⟨Q, E, hQ, rfl⟩
      refine ⟨P * Q, D + E, hP.mul M hQ, ?_⟩
      ext x
      simp [eval, mul_ne_zero_iff])
  have huniv : Set.univ ∈ {U | ∃ P : M.CoordinateRing, ∃ D,
      M.IsHomogeneous P D ∧ U = {x | M.eval P x ≠ 0}} := by
    refine ⟨1, 0, M.isHomogeneous_one, ?_⟩
    ext x
    simp [eval]
  simpa only [Set.insert_eq_of_mem huniv] using h

theorem eval_eq_zero_of_mem_vanishingIdeal {S : Set M.Point}
    {P : M.CoordinateRing} (hP : P ∈ M.vanishingIdeal S)
    {x : M.Point} (hx : x ∈ S) : M.eval P x = 0 := by
  have hle : M.vanishingIdeal S ≤ RingHom.ker (MvPolynomial.eval (M.coordinate x)) := by
    apply Ideal.span_le.mpr
    rintro Q ⟨_, hQ⟩
    exact hQ x hx
  exact hle hP

theorem vanishingIdeal_antitone {S T : Set M.Point} (h : S ⊆ T) :
    M.vanishingIdeal T ≤ M.vanishingIdeal S := by
  apply Ideal.span_mono
  rintro P ⟨hP, hz⟩
  exact ⟨hP, fun x hx => hz x (h hx)⟩

end MultiProjectiveSpace
end PhilipponMultiplicity
end


set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace PhilipponMultiplicity.MultiProjectiveSpace
variable {K : Type*} [Field K] (M : MultiProjectiveSpace K)

theorem isHomogeneous_X (v : M.Variable) :
    M.IsHomogeneous (MvPolynomial.X v) (fun i => if i = v.1 then 1 else 0) := by
  classical
  intro a ha i
  simp only [MvPolynomial.support_X, Finset.mem_singleton] at ha
  subst a
  rcases v with ⟨b, j⟩
  by_cases hi : i = b
  · subst i
    simp [Finsupp.single_apply, Sigma.mk.inj_iff]
  · have hn (k : Fin (M.ambientDimension i + 1)) :
        (⟨b, j⟩ : M.Variable) ≠ ⟨i, k⟩ := by
      intro h
      exact hi (congrArg Sigma.fst h).symm
    simp [Finsupp.single_apply, hi, hn]

theorem isHomogeneous_C (c : K) : M.IsHomogeneous (MvPolynomial.C c) 0 := by
  classical
  intro a ha i
  have ha0 : a = 0 := Finset.mem_singleton.mp (MvPolynomial.support_monomial_subset ha)
  simp [ha0]

theorem IsHomogeneous.add {P Q : M.CoordinateRing} {D : M.FactorIndex → ℕ}
    (hP : M.IsHomogeneous P D) (hQ : M.IsHomogeneous Q D) :
    M.IsHomogeneous (P + Q) D := by
  classical
  intro a ha i
  rcases Finset.mem_union.mp (MvPolynomial.support_add ha) with h | h
  · exact hP a h i
  · exact hQ a h i

theorem IsHomogeneous.neg {P : M.CoordinateRing} {D : M.FactorIndex → ℕ}
    (hP : M.IsHomogeneous P D) : M.IsHomogeneous (-P) D := by
  intro a ha i
  exact hP a (by simpa only [MvPolynomial.support_neg] using ha) i

theorem IsHomogeneous.sub {P Q : M.CoordinateRing} {D : M.FactorIndex → ℕ}
    (hP : M.IsHomogeneous P D) (hQ : M.IsHomogeneous Q D) :
    M.IsHomogeneous (P - Q) D := by
  simpa only [sub_eq_add_neg] using hP.add M (hQ.neg M)

theorem IsHomogeneous.C_mul {P : M.CoordinateRing} {D : M.FactorIndex → ℕ}
    (hP : M.IsHomogeneous P D) (c : K) : M.IsHomogeneous (MvPolynomial.C c * P) D := by
  simpa only [zero_add] using (M.isHomogeneous_C c).mul M hP

theorem IsHomogeneous.nat_mul {P : M.CoordinateRing} {D : M.FactorIndex → ℕ}
    (hP : M.IsHomogeneous P D) (c : ℕ) : M.IsHomogeneous (c * P) D := by
  simpa only [map_natCast] using hP.C_mul M (c : K)

theorem IsHomogeneous.pow {P : M.CoordinateRing} {D : M.FactorIndex → ℕ}
    (hP : M.IsHomogeneous P D) (n : ℕ) :
    M.IsHomogeneous (P ^ n) (fun i => n * D i) := by
  induction n with
  | zero =>
    convert M.isHomogeneous_one using 1
    · simp
    · funext i; simp
  | succ n ih =>
    convert ih.mul M hP using 1
    · exact pow_succ P n
    · funext i; simp [Nat.succ_mul]

end PhilipponMultiplicity.MultiProjectiveSpace
end


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


set_option autoImplicit false
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators Topology
open MvPolynomial
noncomputable section

namespace PhilipponMultiplicity

theorem MultiProjectiveSpace.eval_eq_zero_iff_of_lift
    {K : Type*} [Field K] (M : MultiProjectiveSpace K) (p : M.Point)
    (v : M.Variable → K)
    (hv : ∀ i, ∃ h : (fun j => v ⟨i, j⟩) ≠ 0,
      Projectivization.mk K (fun j => v ⟨i, j⟩) h = p i)
    (P : M.CoordinateRing) (D : M.FactorIndex → ℕ) (hP : M.IsHomogeneous P D) :
    MvPolynomial.eval v P = 0 ↔ M.eval P p = 0 := by
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
  have hne : (∏ i, (a i : K) ^ D i) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun i _ => pow_ne_zero _ (a i).ne_zero)
  rw [hv', M.eval_block_scale P D hP (M.coordinate p) (fun i => (a i : K))]
  exact mul_eq_zero.trans (or_iff_right hne)

end PhilipponMultiplicity
end


set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
noncomputable section
open MvPolynomial Set
open scoped BigOperators Topology

namespace PhilipponMultiplicity.MultiProjectiveSpace
universe u
variable {K : Type u} [Field K]

theorem isHomogeneous_zero (M : MultiProjectiveSpace K) (D : M.FactorIndex → ℕ) :
    M.IsHomogeneous 0 D := by simp [IsHomogeneous]

theorem isHomogeneous_sum (M : MultiProjectiveSpace K) {ι : Type*}
    (s : Finset ι) (P : ι → M.CoordinateRing) (D : M.FactorIndex → ℕ)
    (hP : ∀ i ∈ s, M.IsHomogeneous (P i) D) :
    M.IsHomogeneous (∑ i ∈ s, P i) D := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using M.isHomogeneous_zero D
  | @insert i s hi ih =>
    simp only [Finset.sum_insert, hi, not_false_eq_true]
    exact (hP i (by simp)).add M (ih (fun j hj => hP j (by simp [hj])))

theorem isHomogeneous_prod (M : MultiProjectiveSpace K) {ι : Type*}
    (s : Finset ι) (P : ι → M.CoordinateRing) (D : ι → M.FactorIndex → ℕ)
    (hP : ∀ i ∈ s, M.IsHomogeneous (P i) (D i)) :
    M.IsHomogeneous (∏ i ∈ s, P i) (∑ i ∈ s, D i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using M.isHomogeneous_one
  | @insert i s hi ih =>
    simp only [Finset.prod_insert, Finset.sum_insert, hi, not_false_eq_true]
    exact (hP i (by simp)).mul M (ih (fun j hj => hP j (by simp [hj])))

/-- Substituting tuples homogeneous in each source block preserves
multihomogeneity, with the expected linear transformation of degrees. -/
theorem IsHomogeneous.eval₂_blocks (M N : MultiProjectiveSpace K)
    {Q : N.CoordinateRing} {D : N.FactorIndex → ℕ} (hQ : N.IsHomogeneous Q D)
    (P : N.Variable → M.CoordinateRing) (E : N.FactorIndex → M.FactorIndex → ℕ)
    (hP : ∀ j, M.IsHomogeneous (P j) (E j.1)) :
    M.IsHomogeneous (eval₂ C P Q) (fun i => ∑ b, D b * E b i) := by
  classical
  rw [eval₂_eq']
  apply M.isHomogeneous_sum
  intro d hd
  have hh := M.isHomogeneous_prod Finset.univ (fun j => P j ^ d j)
    (fun j i => d j * E j.1 i) (fun j _ => (hP j).pow M (d j))
  have he : (∑ j : N.Variable, fun i => d j * E j.1 i) =
      (fun i => ∑ b, D b * E b i) := by
    funext i
    simp only [Finset.sum_apply]
    rw [Fintype.sum_sigma]
    apply Finset.sum_congr rfl
    intro b _
    change (∑ y, d ⟨b, y⟩ * E b i) = D b * E b i
    rw [← Finset.sum_mul, hQ d hd b]
  rw [he] at hh
  exact hh.C_mul M _

/-- Two projective lifts represent the same point precisely when all their
two-by-two cross products vanish. -/
theorem projectivization_mk_eq_iff_cross {ι : Type*}
    (v w : ι → K) (hv : v ≠ 0) (hw : w ≠ 0) :
    Projectivization.mk K v hv = Projectivization.mk K w hw ↔
      ∀ j k, v j * w k = v k * w j := by
  classical
  constructor
  · intro heq
    obtain ⟨a, ha⟩ := (Projectivization.mk_eq_mk_iff' K v w hv hw).mp heq
    intro j k
    rw [← ha]
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  · intro h
    obtain ⟨k, hk⟩ := Function.ne_iff.mp hw
    change w k ≠ 0 at hk
    apply (Projectivization.mk_eq_mk_iff' K v w hv hw).mpr
    refine ⟨v k / w k, ?_⟩
    funext j
    simp only [Pi.smul_apply, smul_eq_mul, div_mul_eq_mul_div]
    apply (div_eq_iff hk).mpr
    exact h k j

/-- Regular maps into a multiprojective space have a closed equalizer, even
though the Zariski topology on the target is not Hausdorff. -/
theorem IsRegularAlong.isClosed_equalizer
    {X : Type u} (M N : MultiProjectiveSpace K)
    {e : X → M.Point} {f g : X → N.Point}
    (hf : M.IsRegularAlong N e f) (hg : M.IsRegularAlong N e g) :
    @IsClosed X (TopologicalSpace.induced e M.zariskiTopology) {x | f x = g x} := by
  classical
  let := M.zariskiTopology
  let := TopologicalSpace.induced e M.zariskiTopology
  apply isOpen_compl_iff.mp
  apply isOpen_iff_mem_nhds.mpr
  intro x hx
  obtain ⟨b, hb⟩ := Function.ne_iff.mp hx
  obtain ⟨U, hU, hxU, D, P, hP, hflift⟩ := hf x b
  obtain ⟨V, hV, hxV, E, Q, hQ, hglift⟩ := hg x b
  obtain ⟨hp, hpx⟩ := hflift x hxU
  obtain ⟨hq, hqx⟩ := hglift x hxV
  have hcross : ∃ j k, M.eval (P j * Q k - P k * Q j) (e x) ≠ 0 := by
    by_contra! hn
    apply hb
    rw [← hpx, ← hqx, projectivization_mk_eq_iff_cross]
    intro j k
    simpa only [eval, map_sub, map_mul, sub_eq_zero] using hn j k
  obtain ⟨j, k, hjk⟩ := hcross
  have hhom := ((hP j).mul M (hQ k)).sub M ((hP k).mul M (hQ j))
  let W := U ∩ V ∩ {p | M.eval (P j * Q k - P k * Q j) p ≠ 0}
  have hopen : IsOpen (e ⁻¹' W) :=
    ((hU.inter hV).inter (M.isOpen_basic _ _ hhom)).preimage continuous_induced_dom
  refine Filter.mem_of_superset (hopen.mem_nhds ⟨⟨hxU, hxV⟩, hjk⟩) ?_
  intro y hy heq
  obtain ⟨hpy, hpy'⟩ := hflift y hy.1.1
  obtain ⟨hqy, hqy'⟩ := hglift y hy.1.2
  have hmk := hpy'.trans ((congrFun heq b).trans hqy'.symm)
  have hz := (projectivization_mk_eq_iff_cross _ _ hpy hqy).mp hmk j k
  exact hy.2 (by simpa only [eval, map_sub, map_mul, sub_eq_zero] using hz)

theorem IsRegularAlong.eq_of_dense
    {X : Type u} (M N : MultiProjectiveSpace K)
    {e : X → M.Point} {f g : X → N.Point}
    (hf : M.IsRegularAlong N e f) (hg : M.IsRegularAlong N e g)
    (A : Set X) (hA : @Dense X (TopologicalSpace.induced e M.zariskiTopology) A)
    (hfg : Set.EqOn f g A) : f = g := by
  let := M.zariskiTopology
  let := TopologicalSpace.induced e M.zariskiTopology
  have hh : closure A ⊆ {x | f x = g x} :=
    closure_minimal hfg (hf.isClosed_equalizer M N hg)
  funext x
  exact hh (hA x)

/-- Regular maps are continuous for the actual polynomial Zariski topologies. -/
theorem IsRegularAlong.continuous
    {X : Type u} (M N : MultiProjectiveSpace K)
    {e : X → M.Point} {f : X → N.Point} (hf : M.IsRegularAlong N e f) :
    @Continuous X N.Point (TopologicalSpace.induced e M.zariskiTopology)
      N.zariskiTopology f := by
  classical
  let := M.zariskiTopology
  let := TopologicalSpace.induced e M.zariskiTopology
  apply continuous_generateFrom_iff.mpr
  rintro _ ⟨R, D, hR, rfl⟩
  apply isOpen_iff_mem_nhds.mpr
  intro x hx
  choose U hU hxU E P hP hlift using hf x
  let pull := eval₂ C (fun j : N.Variable => P j.1 j.2) R
  have hpull : M.IsHomogeneous pull (fun i => ∑ b, D b * E b i) :=
    hR.eval₂_blocks M N _ E (fun j => hP j.1 j.2)
  have heval (y : X) : M.eval pull (e y) =
      MvPolynomial.eval (fun j : N.Variable => M.eval (P j.1 j.2) (e y)) R := by
    dsimp only [eval, pull]
    rw [← eval_assoc]
    rfl
  have hiff (y : X) (hy : ∀ b, e y ∈ U b) :
      M.eval pull (e y) = 0 ↔ N.eval R (f y) = 0 := by
    rw [heval]
    exact N.eval_eq_zero_iff_of_lift (f y) _ (fun b => hlift b y (hy b)) R D hR
  let W : Set M.Point := (⋂ b, U b) ∩ {p | M.eval pull p ≠ 0}
  have hW : IsOpen (e ⁻¹' W) :=
    ((isOpen_iInter_of_finite hU).inter (M.isOpen_basic _ _ hpull)).preimage
      continuous_induced_dom
  have hxW : x ∈ e ⁻¹' W := ⟨Set.mem_iInter.mpr hxU, (hiff x hxU).not.mpr hx⟩
  refine Filter.mem_of_superset (hW.mem_nhds hxW) ?_
  intro y hy
  exact (hiff y (Set.mem_iInter.mp hy.1)).not.mp hy.2

theorem IsRegularAlong.comp_domain
    {X Y : Type u} {M N : MultiProjectiveSpace K}
    {e : X → M.Point} {f : X → N.Point} (hf : M.IsRegularAlong N e f) (g : Y → X) :
    M.IsRegularAlong N (e ∘ g) (f ∘ g) := by
  intro y b
  obtain ⟨U, hU, hy, D, P, hP, hl⟩ := hf (g y) b
  exact ⟨U, hU, hy, D, P, hP, fun z hz => hl (g z) hz⟩

end PhilipponMultiplicity.MultiProjectiveSpace
end


set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators Topology
open Set MvPolynomial Filter
noncomputable section

namespace PhilipponMultiplicity.GroupFactorSelection
universe u
variable {K : Type u} [Field K] {G : EmbeddedGroupProduct K}
variable (s : GroupFactorSelection G)

theorem index_injective : Function.Injective s.index :=
  Subtype.val_injective.comp s.indexEquiv.injective

theorem index_mem (i : s.group.FactorIndex) : s.index i ∈ s.val := (s.indexEquiv i).property

theorem range_index : Set.range s.index = s.val := by
  ext i
  constructor
  · rintro ⟨j,rfl⟩
    exact s.index_mem j
  · intro hi
    exact ⟨s.indexEquiv.symm ⟨i,hi⟩,congrArg Subtype.val (s.indexEquiv.apply_symm_apply _)⟩

theorem coordinateIndex_injective : Function.Injective s.coordinateIndex := by
  rintro ⟨i,j⟩ ⟨b,k⟩ h
  have hi : i = b := s.index_injective (congrArg Sigma.fst h)
  subst b
  have hj : j = k := (Sigma.mk.inj_iff.mp h).2.eq
  subst k
  rfl

theorem project_surjective : Function.Surjective s.project := by
  intro y
  let y' : ∀ i : s.val, (G.factor i.val).Point :=
    Equiv.piCongrLeft (fun i : s.val => (G.factor i.val).Point) s.indexEquiv y
  let x : G.Point := fun i => if hi : i ∈ s.val then y' ⟨i,hi⟩ else 0
  refine ⟨x,?_⟩
  funext i
  change (if hi : s.index i ∈ s.val then y' ⟨s.index i,hi⟩ else 0) = y i
  rw [dif_pos (s.index_mem i)]
  change (Equiv.piCongrLeft (fun i : s.val => (G.factor i.val).Point) s.indexEquiv y)
    (s.indexEquiv i) = y i
  simp

theorem dimension_le : s.group.dimension ≤ G.dimension := by
  classical
  unfold EmbeddedGroupProduct.dimension
  calc
    _ = ∑ i ∈ Finset.univ.image s.index, (G.factor i).dimension := by
      rw [Finset.sum_image (fun i _ j _ h => s.index_injective h)]
      rfl
    _ ≤ ∑ i, (G.factor i).dimension :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        (fun i _ _ => Nat.zero_le _)

theorem extendExponent_index (r : s.group.FactorIndex → ℕ) (i : s.group.FactorIndex) :
    s.extendExponent r (s.index i) = r i := by
  simp only [extendExponent,dif_pos (s.index_mem i)]
  change r (s.indexEquiv.symm (s.indexEquiv i)) = r i
  rw [s.indexEquiv.symm_apply_apply]

theorem extendExponent_bounded (r : s.group.FactorIndex → ℕ)
    (hr : ∀ i, r i ≤ (s.group.factor i).dimension) :
    ∀ i, s.extendExponent r i ≤ (G.factor i).dimension := by
  intro i
  by_cases hi : i ∈ s.val
  · obtain ⟨j,rfl⟩ := s.range_index.symm.subset hi
    rw [s.extendExponent_index]
    exact hr j
  · simp [extendExponent,hi]

theorem degreeMonomial (D : G.FactorIndex → ℕ) (r : s.group.FactorIndex → ℕ) :
    (∏ i, (D i : ℝ) ^ s.extendExponent r i) = ∏ i, (D (s.index i) : ℝ) ^ r i := by
  classical
  symm
  apply Finset.prod_bij_ne_one (fun i _ _ => s.index i)
  · simp
  · intro i _ _ j _ _ hij
    exact s.index_injective hij
  · intro i _ hi
    have his : i ∈ s.val := by
      by_contra hn
      exact hi (by simp [extendExponent,hn])
    obtain ⟨j,rfl⟩ := s.range_index.symm.subset his
    refine ⟨j,Finset.mem_univ _,?_,rfl⟩
    simpa [s.extendExponent_index] using hi
  · intro i _ _
    rw [s.extendExponent_index]

theorem eval_rename (Q : s.group.CoordinateRing) (x : G.Point) :
    G.ambient.eval (rename s.coordinateIndex Q) (G.embedding x) =
      s.group.ambient.eval Q (s.group.embedding (s.project x)) := by
  simp only [MultiProjectiveSpace.eval,MvPolynomial.eval_rename]
  rfl

theorem variables_of_supported_degree (D : G.FactorIndex → ℕ)
    (hD : ∀ i, i ∉ s.val → D i = 0)
    (P : G.CoordinateRing) (hP : IsMultihomogeneousOfDegree G P D) :
    (P.vars : Set G.ambient.Variable) ⊆ Set.range s.coordinateIndex := by
  classical
  intro v hv
  obtain ⟨m,hm,hv⟩ := (mem_vars_iff_mem_support v).mp hv
  have hi : v.1 ∈ s.val := by
    by_contra hi
    have hz := (hP m hm v.1).trans (hD v.1 hi)
    have hle : m v ≤ ∑ j : Fin (G.ambient.ambientDimension v.1+1), m ⟨v.1,j⟩ :=
      Finset.single_le_sum (f := fun j : Fin (G.ambient.ambientDimension v.1+1) => m ⟨v.1,j⟩)
        (fun j _ => Nat.zero_le _) (Finset.mem_univ v.2)
    have hm0 : m v = 0 := Nat.eq_zero_of_le_zero (hle.trans_eq hz)
    exact Finsupp.mem_support_iff.mp hv hm0
  obtain ⟨j,hj⟩ := s.range_index.symm.subset hi
  rcases v with ⟨b,k⟩
  dsimp at hj
  subst b
  exact ⟨⟨j,k⟩,rfl⟩

theorem exists_polynomial (D : G.FactorIndex → ℕ)
    (hD : ∀ i, i ∉ s.val → D i = 0)
    (P : G.CoordinateRing) (hP : IsMultihomogeneousOfDegree G P D) :
    ∃ Q : s.group.CoordinateRing, rename s.coordinateIndex Q = P :=
  exists_rename_eq_of_vars_subset_range P s.coordinateIndex s.coordinateIndex_injective
    (s.variables_of_supported_degree D hD P hP)

theorem homogeneous_of_rename (Q : s.group.CoordinateRing) (D : G.FactorIndex → ℕ)
    (hQ : IsMultihomogeneousOfDegree G (rename s.coordinateIndex Q) D) :
    IsMultihomogeneousOfDegree s.group Q (fun i => D (s.index i)) := by
  classical
  intro m hm i
  have hm' : Finsupp.mapDomain s.coordinateIndex m ∈ (rename s.coordinateIndex Q).support := by
    rw [support_rename_of_injective s.coordinateIndex_injective]
    exact Finset.mem_image.mpr ⟨m,hm,rfl⟩
  have hh := hQ _ hm' (s.index i)
  change (∑ j, Finsupp.mapDomain s.coordinateIndex m (s.coordinateIndex ⟨i,j⟩)) = _ at hh
  simpa only [Finsupp.mapDomain_apply s.coordinateIndex_injective] using hh

theorem translate_lift (A : Set G.Point) (B : Set s.group.Point)
    (hB : B = s.project '' A) (Q : s.group.CoordinateRing)
    (g : s.group.Point) (hg : PhilipponMultiplicity.translate g B ⊆ zeroLocusOnGroup s.group Q) :
    ∃ g' : G.Point, PhilipponMultiplicity.translate g' A ⊆
      zeroLocusOnGroup G (rename s.coordinateIndex Q) := by
  obtain ⟨g',rfl⟩ := s.project_surjective g
  refine ⟨g',?_⟩
  rintro x ⟨a,ha,rfl⟩
  change G.ambient.eval (rename s.coordinateIndex Q) (G.embedding (g'+a)) = 0
  rw [s.eval_rename,map_add]
  apply hg
  exact ⟨s.project a,by rw [hB]; exact ⟨a,ha,rfl⟩,rfl⟩

end PhilipponMultiplicity.GroupFactorSelection

namespace PhilipponMultiplicity.GroupFactorSelection
universe u
variable {K : Type u} [NontriviallyNormedField K] {G : EmbeddedGroupProduct K}
variable (s : GroupFactorSelection G)

theorem grid_lift {l : ℕ} (γ : Fin l → G.Point) {R S : ℝ} (hRS : R ≤ S)
    {y : s.group.Point} (hy : y ∈ samplingGrid (fun i => s.project (γ i)) R) :
    ∃ x ∈ samplingGrid γ S, s.project x = y := by
  obtain ⟨a,ha,rfl⟩ := hy
  refine ⟨∑ i, a i • γ i,⟨a,fun i => (ha i).trans hRS,rfl⟩,?_⟩
  simp only [map_sum,map_nsmul]

end PhilipponMultiplicity.GroupFactorSelection

namespace PhilipponMultiplicity.CorollaryProjectionProof
universe u
variable {K : Type u} [NontriviallyNormedField K] {G : EmbeddedGroupProduct K}

theorem positive_support_of_contact (A : AnalyticSubgroup G)
    (P : G.CoordinateRing) (D : G.FactorIndex → ℕ)
    (hP : P ≠ 0) (hhom : IsMultihomogeneousOfDegree G P D)
    (hcontact : (1 : WithTop ℕ) ≤ vanishingOrder A P 0) : ∃ i, 0 < D i := by
  classical
  by_contra hn
  have hD : ∀ i, D i = 0 := by intro i; have := not_exists.mp hn i; omega
  have hvars : P.vars = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro v hv
    obtain ⟨m,hm,hv⟩ := (mem_vars_iff_mem_support v).mp hv
    have hz := (hhom m hm v.1).trans (hD v.1)
    have hle : m v ≤ ∑ j : Fin (G.ambient.ambientDimension v.1+1), m ⟨v.1,j⟩ :=
      Finset.single_le_sum (f := fun j : Fin (G.ambient.ambientDimension v.1+1) => m ⟨v.1,j⟩)
        (fun j _ => Nat.zero_le _) (Finset.mem_univ v.2)
    exact Finsupp.mem_support_iff.mp hv (Nat.eq_zero_of_le_zero (hle.trans_eq hz))
  have heq : P = C (P.coeff 0) := vars_eq_empty_iff_eq_C.mp hvars
  have hpull : A.pullback P 0 = fun _ => P.coeff 0 := by
    funext z
    change MvPolynomial.eval (A.lift 0 z) P = P.coeff 0
    conv_lhs => rw [heq]
    rw [eval_C]
  have hz := (natCast_le_jetOrder_iff (n := 1) (f := A.pullback P 0) (x := 0)).mp hcontact 0 (by decide)
  rw [hpull] at hz
  have hc : P.coeff 0 = 0 := by
    have hh := congrArg (fun f => f (fun _ => (0 : A.ParameterSpace))) hz
    simpa only [iteratedFDeriv_zero_apply,
      ContinuousMultilinearMap.zero_apply] using hh
  exact hP (heq.trans (by rw [hc,map_zero]))

end PhilipponMultiplicity.CorollaryProjectionProof
end


set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators Topology
open Set Filter MvPolynomial
noncomputable section

namespace PhilipponMultiplicity.GroupFactorSelection
universe u
variable {K : Type u} [NontriviallyNormedField K] {G : EmbeddedGroupProduct K}
variable (s : GroupFactorSelection G)

theorem exists_coordinateIndex (v : G.ambient.Variable) (hv : v.1 ∈ s.val) :
    ∃ w, s.coordinateIndex w = v := by
  obtain ⟨j,hj⟩ := s.range_index.symm.subset hv
  rcases v with ⟨i,k⟩
  dsimp at hj
  subst i
  exact ⟨⟨j,k⟩,rfl⟩

/-- Substitute constants for omitted blocks and retain selected variables. -/
def specializeCoordinate (a : G.ambient.Variable → K) (v : G.ambient.Variable) :
    s.group.CoordinateRing :=
  if h : ∃ w, s.coordinateIndex w = v then X h.choose else C (a v)

theorem specializeCoordinate_selected (a : G.ambient.Variable → K)
    (w : s.group.ambient.Variable) :
    s.specializeCoordinate a (s.coordinateIndex w) = X w := by
  have h : ∃ w', s.coordinateIndex w' = s.coordinateIndex w := ⟨w,rfl⟩
  rw [specializeCoordinate,dif_pos h]
  exact congrArg X (s.coordinateIndex_injective h.choose_spec)

theorem specializeCoordinate_omitted (a : G.ambient.Variable → K)
    (v : G.ambient.Variable) (hv : v.1 ∉ s.val) :
    s.specializeCoordinate a v = C (a v) := by
  have hn : ¬ ∃ w, s.coordinateIndex w = v := by
    rintro ⟨w,hw⟩
    exact hv ((congrArg Sigma.fst hw) ▸ s.index_mem w.1)
  exact dif_neg hn

def specialize (a : G.ambient.Variable → K) (P : G.CoordinateRing) :
    s.group.CoordinateRing := eval₂ C (s.specializeCoordinate a) P

theorem specialize_homogeneous (a : G.ambient.Variable → K)
    (P : G.CoordinateRing) (D : G.FactorIndex → ℕ) (hP : G.ambient.IsHomogeneous P D) :
    ∃ E, s.group.ambient.IsHomogeneous (s.specialize a P) E := by
  classical
  let E (i : G.FactorIndex) (j : s.group.FactorIndex) := if s.index j = i then 1 else 0
  refine ⟨fun j => ∑ i, D i * E i j,?_⟩
  apply hP.eval₂_blocks s.group.ambient G.ambient (s.specializeCoordinate a) E
  intro v
  by_cases hv : v.1 ∈ s.val
  · obtain ⟨w,rfl⟩ := s.exists_coordinateIndex v hv
    rw [s.specializeCoordinate_selected]
    have he : E (s.coordinateIndex w).1 = (fun j => if j = w.1 then 1 else 0) := by
      funext j
      simp only [E,coordinateIndex,s.index_injective.eq_iff]
    rw [he]
    exact s.group.ambient.isHomogeneous_X w
  · rw [s.specializeCoordinate_omitted a v hv]
    have he : E v.1 = 0 := by
      funext j
      have hn : s.index j ≠ v.1 := by
        intro h
        exact hv (h ▸ s.index_mem j)
      simp only [E,if_neg hn,Pi.zero_apply]
    rw [he]
    exact s.group.ambient.isHomogeneous_C _

theorem eval_specialize (a f : G.ambient.Variable → K) (P : G.CoordinateRing) :
    MvPolynomial.eval (fun w => f (s.coordinateIndex w)) (s.specialize a P) =
      MvPolynomial.eval (fun v => if v.1 ∈ s.val then f v else a v) P := by
  classical
  unfold specialize
  rw [← eval_assoc]
  congr 2
  funext v
  simp only [Function.comp_apply]
  by_cases hv : v.1 ∈ s.val
  · obtain ⟨w,rfl⟩ := s.exists_coordinateIndex v hv
    rw [s.specializeCoordinate_selected,eval_X,if_pos hv]
  · rw [s.specializeCoordinate_omitted a v hv,eval_C,if_neg hv]

theorem sectionPoint_omitted (y : s.group.Point) (i : G.FactorIndex) (hi : i ∉ s.val) :
    s.sectionPoint y i = 0 := by simp only [sectionPoint,dif_neg hi]

/-- Freezing omitted blocks at an identity lift sends a homogeneous equation
of the subgroup preimage to an actual equation of the selected subgroup. -/
theorem specialize_mem_vanishingIdeal (A : AnalyticSubgroup G)
    (H : AlgebraicSubgroup s.group) (P : G.CoordinateRing) (D : G.FactorIndex → ℕ)
    (hP : G.ambient.IsHomogeneous P D)
    (hPH : ∀ x ∈ s.project ⁻¹' H.carrier, G.ambient.eval P (G.embedding x) = 0) :
    s.specialize (A.lift 0 0) P ∈ s.group.vanishingIdeal H.carrier := by
  classical
  apply Ideal.subset_span
  refine ⟨s.specialize_homogeneous _ P D hP,?_⟩
  rintro _ ⟨y,hy,rfl⟩
  let x := s.sectionPoint y
  have hx : x ∈ s.project ⁻¹' H.carrier := by
    change s.project (s.sectionPoint y) ∈ H.carrier
    rwa [s.project_sectionPoint]
  have hc : (fun w => G.ambient.coordinate (G.embedding x) (s.coordinateIndex w)) =
      s.group.ambient.coordinate (s.group.embedding y) := by
    funext w
    have he := congrFun (s.project_sectionPoint y) w.1
    exact congrArg (fun t => t.val.rep w.2) he
  change MvPolynomial.eval (s.group.ambient.coordinate (s.group.embedding y)) _ = 0
  rw [← hc,s.eval_specialize]
  apply (G.ambient.eval_eq_zero_iff_of_lift (G.embedding x)
    (fun v => if v.1 ∈ s.val then G.ambient.coordinate (G.embedding x) v else A.lift 0 0 v)
    ?_ P D hP).mpr (hPH x hx)
  intro i
  by_cases hi : i ∈ s.val
  · simp only [hi,if_true,MultiProjectiveSpace.coordinate]
    exact ⟨Projectivization.rep_nonzero (G.embedding x i),
      Projectivization.mk_rep (G.embedding x i)⟩
  · simp only [hi,if_false]
    have h := A.base_represents ⟨0,A.zero_mem⟩ i
    simpa only [A.map_zero,EmbeddedGroupProduct.embedding,x,s.sectionPoint_omitted y i hi,
      Pi.zero_apply] using h

end PhilipponMultiplicity.GroupFactorSelection

namespace PhilipponMultiplicity.ProjectionTangentProof
universe u
variable {K : Type u} [NontriviallyNormedField K] [CompleteSpace K]

/-- The differential on the diagonal is the sum of the two partial differentials. -/
theorem diagonal_fderiv {E : Type*} [NormedAddCommGroup E] [NormedSpace K E]
    (F : E × E → K) (hF : DifferentiableAt K F (0,0)) (v : E) :
    fderiv K (fun z => F (z,z)) 0 v =
      fderiv K (fun z => F (z,0)) 0 v + fderiv K (fun z => F (0,z)) 0 v := by
  have hd := hF.hasFDerivAt.comp (f := fun z : E => (z,z)) 0
    ((hasFDerivAt_id (0 : E)).prodMk (hasFDerivAt_id 0))
  have hl := hF.hasFDerivAt.comp (f := fun z : E => (z,0)) 0
    ((hasFDerivAt_id (0 : E)).prodMk (hasFDerivAt_const (0 : E) 0))
  have hr := hF.hasFDerivAt.comp (f := fun z : E => (0,z)) 0
    ((hasFDerivAt_const (0 : E) (0 : E)).prodMk (hasFDerivAt_id 0))
  dsimp only [Function.comp_def] at hd hl hr
  rw [hd.fderiv,hl.fderiv,hr.fderiv]
  simp only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.prod_apply,
    ContinuousLinearMap.id_apply,ContinuousLinearMap.zero_apply]
  rw [← map_add]
  simp

end PhilipponMultiplicity.ProjectionTangentProof
end


set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators Topology
open Set Filter MvPolynomial
noncomputable section

namespace PhilipponMultiplicity.ProjectionTangentProof
universe u
variable {K : Type u} [NontriviallyNormedField K] [CompleteSpace K]
variable {G : EmbeddedGroupProduct K}

/-- The product rule extends the differential test from the homogeneous
generators to every polynomial in the actual vanishing ideal. -/
theorem homogeneous_equations_suffice (A : AnalyticSubgroup G)
    (V : Set G.Point) (hV : (0 : G.Point) ∈ V) (v : A.ParameterSpace)
    (h : ∀ P : G.CoordinateRing, (∃ D, G.ambient.IsHomogeneous P D) →
      (∀ y ∈ V, G.ambient.eval P (G.embedding y) = 0) →
      fderiv K (A.pullback P 0) 0 v = 0)
    (P : G.CoordinateRing) (hP : P ∈ G.vanishingIdeal V) :
    fderiv K (A.pullback P 0) 0 v = 0 := by
  have ha (Q : G.CoordinateRing) : AnalyticAt K (A.pullback Q 0) 0 :=
    AnalyticAt.aeval_mvPolynomial (fun i => A.lift_analytic 0 i) Q
  have hrep : ∀ i, ∃ hn : (fun j => A.lift 0 0 ⟨i,j⟩) ≠ 0,
      Projectivization.mk K (fun j => A.lift 0 0 ⟨i,j⟩) hn = G.embedding 0 i := by
    intro i
    simpa only [A.map_zero] using A.base_represents ⟨0,A.zero_mem⟩ i
  have hzero (Q : G.CoordinateRing) (hQ : Q ∈ G.vanishingIdeal V) :
      A.pullback Q 0 0 = 0 := G.ambient.eval_lift_eq_zero_of_mem_vanishingIdeal
        (Set.mem_image_of_mem G.embedding hV) _ hrep hQ
  induction hP using Submodule.span_induction with
  | mem Q hQ =>
    exact h Q hQ.1 (fun y hy => hQ.2 _ ⟨y,hy,rfl⟩)
  | zero =>
    change fderiv K (fun z : A.ParameterSpace => MvPolynomial.eval (A.lift 0 z) 0) 0 v = 0
    simp only [_root_.map_zero,fderiv_const_apply,ContinuousLinearMap.zero_apply]
  | add Q R hQ hR ihQ ihR =>
    have heq : A.pullback (Q+R) 0 = fun z => A.pullback Q 0 z + A.pullback R 0 z := by
      funext z
      exact _root_.map_add _ _ _
    rw [heq,fderiv_fun_add (ha Q).differentiableAt (ha R).differentiableAt]
    simp only [ContinuousLinearMap.add_apply,ihQ,ihR,add_zero]
  | smul a Q hQ ih =>
    have heq : A.pullback (a • Q) 0 = fun z => A.pullback a 0 z * A.pullback Q 0 z := by
      funext z
      exact map_mul _ _ _
    rw [heq,fderiv_fun_mul (ha a).differentiableAt (ha Q).differentiableAt]
    simp only [ContinuousLinearMap.add_apply,ContinuousLinearMap.smul_apply,
      ih,hzero Q hQ,smul_zero,zero_smul,add_zero]

/-- The curve that moves only omitted coordinates lies in the subgroup preimage. -/
theorem omitted_zero_germ (s : GroupFactorSelection G) (A : AnalyticSubgroup G)
    (H : AlgebraicSubgroup s.group) (P : G.CoordinateRing) (D : G.FactorIndex → ℕ)
    (hP : G.ambient.IsHomogeneous P D)
    (hPH : ∀ x ∈ s.project ⁻¹' H.carrier, G.ambient.eval P (G.embedding x) = 0) :
    (fun z : A.ParameterSpace => MvPolynomial.eval
      (fun v => if v.1 ∈ s.val then A.lift 0 0 v else A.lift 0 z v) P) =ᶠ[𝓝 0] 0 := by
  classical
  filter_upwards [A.domain_open.mem_nhds A.zero_mem] with z hz
  let x : G.Point := fun i => if i ∈ s.val then 0 else A.map ⟨z,hz⟩ i
  have hx : x ∈ s.project ⁻¹' H.carrier := by
    have hp : s.project x = 0 := by
      funext i
      simp only [GroupFactorSelection.project,AddMonoidHom.coe_mk,ZeroHom.coe_mk,
        x,s.index_mem i,if_true,Pi.zero_apply]
    change s.project x ∈ H.carrier
    rw [hp]
    exact H.toAddSubgroup.zero_mem
  apply (G.ambient.eval_eq_zero_iff_of_lift (G.embedding x)
    (fun v => if v.1 ∈ s.val then A.lift 0 0 v else A.lift 0 z v)
    ?_ P D hP).mpr (hPH x hx)
  intro i
  by_cases hi : i ∈ s.val
  · simp only [hi,if_true,EmbeddedGroupProduct.embedding,x]
    have h := A.base_represents ⟨0,A.zero_mem⟩ i
    simpa only [A.map_zero,EmbeddedGroupProduct.embedding,Pi.zero_apply] using h
  · simp only [hi,if_false,EmbeddedGroupProduct.embedding,x]
    exact A.base_represents ⟨z,hz⟩ i

/-- Split the differential into a selected-block equation and an omitted-block
curve on which the original equation vanishes identically. -/
theorem homogeneous_direction (s : GroupFactorSelection G) (A : AnalyticSubgroup G)
    (H : AlgebraicSubgroup s.group) (v : A.ParameterSpace)
    (hv : v ∈ (s.projectedAnalytic A).tangentKernel H.carrier)
    (P : G.CoordinateRing) (D : G.FactorIndex → ℕ) (hP : G.ambient.IsHomogeneous P D)
    (hPH : ∀ x ∈ s.project ⁻¹' H.carrier, G.ambient.eval P (G.embedding x) = 0) :
    fderiv K (A.pullback P 0) 0 v = 0 := by
  classical
  let F (zw : A.ParameterSpace × A.ParameterSpace) := MvPolynomial.eval
    (fun q => if q.1 ∈ s.val then A.lift 0 zw.1 q else A.lift 0 zw.2 q) P
  have hF : DifferentiableAt K F (0,0) := by
    apply AnalyticAt.differentiableAt
    apply AnalyticAt.aeval_mvPolynomial
    intro q
    by_cases hq : q.1 ∈ s.val
    · simp only [hq,if_true]
      exact (A.lift_analytic 0 q).comp
        (f := fun zw : A.ParameterSpace × A.ParameterSpace => zw.1)
        (x := (0,0)) analyticAt_fst
    · simp only [hq,if_false]
      exact (A.lift_analytic 0 q).comp
        (f := fun zw : A.ParameterSpace × A.ParameterSpace => zw.2)
        (x := (0,0)) analyticAt_snd
  have hpull : A.pullback P 0 = fun z => F (z,z) := by
    funext z
    simp only [F,ite_self,AnalyticSubgroup.pullback]
  let Q := s.specialize (A.lift 0 0) P
  have hQ : Q ∈ s.group.vanishingIdeal H.carrier :=
    s.specialize_mem_vanishingIdeal A H P D hP hPH
  have hleft : (fun z : A.ParameterSpace => (s.projectedAnalytic A).pullback Q 0 z) =
      fun z => F (z,0) := by
    funext z
    change MvPolynomial.eval
      (fun w => A.lift (s.sectionPoint 0) z (s.coordinateIndex w)) Q = _
    rw [s.sectionPoint_zero]
    exact s.eval_specialize (A.lift 0 0) (A.lift 0 z) P
  have hdQ := (Submodule.mem_iInf _).mp hv ⟨Q,hQ⟩
  change fderiv K ((s.projectedAnalytic A).pullback Q 0) 0 v = 0 at hdQ
  have hdleft : fderiv K (fun z : A.ParameterSpace =>
      (s.projectedAnalytic A).pullback Q 0 z) 0 v = 0 := hdQ
  rw [hleft] at hdleft
  have hright : (fun z => F (0,z)) =ᶠ[𝓝 0] 0 :=
    omitted_zero_germ s A H P D hP hPH
  rw [hpull,diagonal_fderiv F hF v,hdleft,hright.fderiv_eq]
  simp

theorem kernel_inclusion (s : GroupFactorSelection G) (A : AnalyticSubgroup G)
    (H : AlgebraicSubgroup s.group) :
    (s.projectedAnalytic A).tangentKernel H.carrier ≤
      A.tangentKernel (s.project ⁻¹' H.carrier) := by
  intro v hv
  apply (Submodule.mem_iInf _).mpr
  intro P
  change fderiv K (A.pullback P.val 0) 0 v = 0
  have hzero : (0 : G.Point) ∈ s.project ⁻¹' H.carrier := by
    change s.project 0 ∈ H.carrier
    rw [map_zero]
    exact H.toAddSubgroup.zero_mem
  apply homogeneous_equations_suffice A _ hzero v _ P.val P.property
  rintro Q ⟨D,hD⟩ hQ
  exact homogeneous_direction s A H v hv Q D hD hQ

end PhilipponMultiplicity.ProjectionTangentProof

end

open PhilipponMultiplicity

theorem solution
    (K : Type*) [NontriviallyNormedField K] (hK : IsPhilipponBaseField K)
    (G : EmbeddedGroupProduct K) (s : GroupFactorSelection G)
    (A : AnalyticSubgroup G) (H : AlgebraicSubgroup s.group) :
    (s.projectedAnalytic A).tangentKernel H.carrier ≤
      A.tangentKernel (s.project ⁻¹' H.carrier) := by
  let : CompleteSpace K := hK.completeSpace
  exact ProjectionTangentProof.kernel_inclusion s A H
