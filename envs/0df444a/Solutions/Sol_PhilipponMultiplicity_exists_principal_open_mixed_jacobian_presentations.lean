-- Prove2me | solution 1 for PhilipponMultiplicity.exists_principal_open_mixed_jacobian_presentations
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-10-06T01:37:16.001789+00:00
-- url     : https://prove2.me/submissions/c231cf46-f88f-436b-a2c5-eab621936f60

import Theorems.Thm_PhilipponMultiplicity_exists_principal_open_regular_point_mixed_zero_locus
import Definitions.Def_PhilipponMultiplicity_GeometricSupport
import Definitions.Def_PhilipponMultiplicity_MixedFlagParameters
import Mathlib
import Theorems.Thm_RegularLocalConormal_inf_maximalIdeal_sq_eq_mul

set_option autoImplicit false

section

set_option autoImplicit false
set_option maxHeartbeats 1600000
open scoped BigOperators

namespace AffineJacobian
namespace FirstOrder

open MvPolynomial
variable {K σ : Type*} [Field K] [Fintype σ]

noncomputable def remainder (a : σ → K) (P : MvPolynomial σ K) : MvPolynomial σ K :=
  P - C (eval a P) - ∑ j, C (eval a (pderiv j P)) * (X j - C (a j))

lemma remainder_C (a : σ → K) (c : K) : remainder a (C c) = 0 := by
  simp [remainder]

lemma remainder_add (a : σ → K) (P Q : MvPolynomial σ K) :
    remainder a (P + Q) = remainder a P + remainder a Q := by
  simp only [remainder, map_add, add_mul, Finset.sum_add_distrib]
  ring

lemma remainder_mul_X (a : σ → K) (P : MvPolynomial σ K) (j : σ) :
    remainder a (P * X j) =
      (P - C (eval a P)) * (X j - C (a j)) + C (a j) * remainder a P := by
  classical
  have ht (i : σ) : C (eval a (pderiv i (P * X j))) * (X i - C (a i)) =
      C (a j) * (C (eval a (pderiv i P)) * (X i - C (a i))) +
      if i = j then C (eval a P) * (X j - C (a j)) else 0 := by
    by_cases h : i = j
    · subst i
      simp only [pderiv_mul, pderiv_X_self, map_add, map_mul, eval_X,
        map_one, mul_one, ite_true]
      ring
    · simp only [pderiv_mul, pderiv_X_of_ne (Ne.symm h), map_add, map_mul,
        eval_X, map_zero, mul_zero, add_zero, if_neg h]
      ring
  have hs := Finset.sum_congr (s₁ := Finset.univ) rfl (fun i _ => ht i)
  simp only [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ,
    if_true, ← Finset.mul_sum] at hs
  simp only [remainder, hs, map_mul, eval_X]
  ring

lemma remainder_mem_square (a : σ → K) (P : MvPolynomial σ K) :
    remainder a P ∈ (RingHom.ker (eval a)) ^ 2 := by
  induction P using MvPolynomial.induction_on with
  | C c => simp [remainder_C]
  | add P Q hP hQ => exact remainder_add a P Q ▸ Ideal.add_mem _ hP hQ
  | mul_X P j hP =>
    rw [remainder_mul_X]
    refine Ideal.add_mem _ ?_ (Ideal.mul_mem_left _ _ hP)
    rw [pow_two]
    apply Ideal.mul_mem_mul
    · change eval a (P - C (eval a P)) = 0
      simp
    · change eval a (X j - C (a j)) = 0
      simp

theorem mem_square_of_value_gradient_zero (a : σ → K) (P : MvPolynomial σ K)
    (hP : eval a P = 0) (hdP : ∀ j, eval a (pderiv j P) = 0) :
    P ∈ (RingHom.ker (eval a)) ^ 2 := by
  simpa [remainder, hP, hdP] using remainder_mem_square a P

end FirstOrder
end AffineJacobian


end


section

set_option autoImplicit false
set_option maxHeartbeats 1600000
open scoped BigOperators
noncomputable section

namespace AffineJacobian
namespace Gradient
open MvPolynomial
variable {K σ : Type*} [Field K] [Fintype σ]

def gradient (a : σ → K) : MvPolynomial σ K →ₗ[K] (σ → K) where
  toFun P j := eval a (pderiv j P)
  map_add' P Q := by ext j; simp
  map_smul' c P := by ext j; simp

theorem basis_equations (I : Ideal (MvPolynomial σ K)) (a : σ → K) :
    ∃ (r : ℕ) (P : Fin r → MvPolynomial σ K),
      (∀ i, P i ∈ I) ∧
      Function.Surjective (fun v : σ → K => fun i : Fin r =>
        ∑ j, eval a (pderiv j (P i)) * v j) ∧
      ∀ Q ∈ I, ∃ c : Fin r → K,
        ∀ j, eval a (pderiv j Q) = ∑ i, c i * eval a (pderiv j (P i)) := by
  classical
  let g := (gradient a).comp (I.restrictScalars K).subtype
  let W := LinearMap.range g
  let b := Module.finBasis K W
  have hb (i : Fin (Module.finrank K W)) : ∃ P : I, g P = (b i : σ → K) :=
    (b i).property
  choose P hP using hb
  refine ⟨Module.finrank K W, fun i => P i, fun i => (P i).property, ?_, ?_⟩
  · intro y
    let ψ : Module.Dual K W := b.constr K y
    let φ : Module.Dual K (σ → K) := Subspace.dualLift W ψ
    refine ⟨fun j => φ (Pi.single j 1), ?_⟩
    funext i
    change (∑ j, g (P i) j * φ (Pi.single j 1)) = y i
    rw [hP]
    calc
      _ = φ (∑ j, (b i : σ → K) j • Pi.single j (1 : K)) := by simp
      _ = φ (b i : σ → K) := by congr 1; ext j; simp [Pi.single_apply]
      _ = ψ (b i) := Subspace.dualLift_of_subtype _
      _ = y i := b.constr_basis K y i
  · intro Q hQ
    let w : W := ⟨g ⟨Q, hQ⟩, LinearMap.mem_range_self _ _⟩
    refine ⟨fun i => b.repr w i, fun j => ?_⟩
    change (w : σ → K) j = ∑ i, b.repr w i * g (P i) j
    have h := congrArg (fun z : W => (z : σ → K) j) (b.sum_repr w)
    simpa only [Submodule.coe_sum, Finset.sum_apply, Submodule.coe_smul,
      Pi.smul_apply, smul_eq_mul, ← hP] using h.symm

end Gradient
end AffineJacobian

end

end


section

set_option autoImplicit false
set_option maxHeartbeats 1600000
open scoped BigOperators

namespace AffineJacobian
namespace LocalEquations
open MvPolynomial
variable {K σ : Type*} [Field K] [Fintype σ]

theorem local_span_of_conormal (I : Ideal (MvPolynomial σ K)) (a : σ → K)
    (m : MaximalSpectrum (MvPolynomial σ K))
    (hm : m.asIdeal = RingHom.ker (eval a)) (hIm : I ≤ m.asIdeal)
    {r : ℕ} (P : Fin r → MvPolynomial σ K) (hP : ∀ i, P i ∈ I)
    (hgrad : ∀ Q ∈ I, ∃ c : Fin r → K,
      ∀ j, eval a (pderiv j Q) = ∑ i, c i * eval a (pderiv j (P i)))
    (hconormal : I.map (algebraMap _ (Localization.AtPrime m.asIdeal)) ⊓
        (IsLocalRing.maximalIdeal (Localization.AtPrime m.asIdeal)) ^ 2 ≤
      IsLocalRing.maximalIdeal (Localization.AtPrime m.asIdeal) *
        I.map (algebraMap _ (Localization.AtPrime m.asIdeal))) :
    I.map (algebraMap _ (Localization.AtPrime m.asIdeal)) =
      (Ideal.span (Set.range P)).map (algebraMap _ (Localization.AtPrime m.asIdeal)) := by
  classical
  let A := MvPolynomial σ K
  let R := Localization.AtPrime m.asIdeal
  let f := algebraMap A R
  let J : Ideal A := Ideal.span (Set.range P)
  let L := I.map f
  let N := J.map f
  let n := IsLocalRing.maximalIdeal R
  have hJI : J ≤ I := Ideal.span_le.mpr (by rintro _ ⟨i, rfl⟩; exact hP i)
  have hred : L ≤ N ⊔ n * L := by
    apply Ideal.map_le_iff_le_comap.mpr
    intro Q hQ
    obtain ⟨c, hc⟩ := hgrad Q hQ
    let F := ∑ i, C (c i) * P i
    have hFJ : F ∈ J :=
      Ideal.sum_mem _ (fun i _ => J.mul_mem_left _ (Ideal.subset_span ⟨i, rfl⟩))
    have hFI : F ∈ I := hJI hFJ
    have hDI : Q - F ∈ I := I.sub_mem hQ hFI
    have hDval : eval a (Q - F) = 0 := by
      have h := hIm hDI
      rwa [hm, RingHom.mem_ker] at h
    have hDgrad (j : σ) : eval a (pderiv j (Q - F)) = 0 := by
      simp only [map_sub, F, map_sum, pderiv_C_mul, map_mul, eval_C, hc j, sub_self]
    have hDsq : Q - F ∈ m.asIdeal ^ 2 := by
      rw [hm]
      exact FirstOrder.mem_square_of_value_gradient_zero a (Q - F) hDval hDgrad
    have hlocsq : f (Q - F) ∈ n ^ 2 := by
      have h := Ideal.mem_map_of_mem f hDsq
      rwa [Ideal.map_pow, Localization.AtPrime.map_eq_maximalIdeal] at h
    have hlocD : f (Q - F) ∈ n * L :=
      hconormal ⟨Ideal.mem_map_of_mem f hDI, hlocsq⟩
    change f Q ∈ N ⊔ n * L
    apply Submodule.mem_sup.mpr
    refine ⟨f F, Ideal.mem_map_of_mem f hFJ, f (Q - F), hlocD, ?_⟩
    rw [map_sub]
    ring
  have hLN : L ≤ N := by
    apply Submodule.le_of_le_smul_of_le_jacobson_bot L.fg_of_isNoetherianRing
      (I := n)
    · exact (IsLocalRing.jacobson_eq_maximalIdeal (⊥ : Ideal R) bot_ne_top).ge
    · simpa only [Ideal.smul_eq_mul] using hred
  exact hLN.antisymm (Ideal.map_mono hJI)
end LocalEquations
end AffineJacobian

end


section

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators
noncomputable section

namespace AffineJacobian.LocalPresentation

/-- A surjective rectangular matrix admits a square nonsingular minor obtained
by selecting distinct columns. The statement includes the empty matrix. -/
theorem exists_nonsingular_minor
    {K σ : Type*} [Field K] [Fintype σ]
    (r : ℕ) (A : Matrix (Fin r) σ K) (hA : Function.Surjective A.mulVec) :
    ∃ e : Fin r ↪ σ, (Matrix.of (fun i j : Fin r => A j (e i))).det ≠ 0 := by
  classical
  have hspan : Submodule.span K (Set.range A.col) = ⊤ := by
    rw [← Matrix.range_mulVecLin]
    exact LinearMap.range_eq_top.mpr hA
  obtain ⟨κ,a,ha,hsp,hli⟩ := exists_linearIndependent' K A.col
  letI : Finite κ := Finite.of_injective a ha
  letI : Fintype κ := Fintype.ofFinite κ
  let b : Module.Basis κ K (Fin r → K) := Module.Basis.mk hli (by rw [hsp,hspan])
  have hcard : Fintype.card κ = r := by
    simpa using (Module.finrank_eq_card_basis b).symm
  let u : Fin r ≃ κ := (Fintype.equivFinOfCardEq hcard).symm
  let e : Fin r ↪ σ := ⟨a ∘ u,ha.comp u.injective⟩
  refine ⟨e,?_⟩
  have hrows : LinearIndependent K (Matrix.of (fun i j : Fin r => A j (e i))).row :=
    hli.comp u u.injective
  exact ((Matrix.isUnit_iff_isUnit_det _).mp
    (Matrix.linearIndependent_rows_iff_isUnit.mp hrows)).ne_zero

end AffineJacobian.LocalPresentation
end

end


section

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators
noncomputable section

namespace AffineJacobian.LocalPresentation
open MvPolynomial

/-- A regular point-local polynomial quotient has local generators with a
nonvanishing coordinate Jacobian minor. No global radicality is required. -/
theorem of_regular_quotient
    {K σ : Type*} [Field K] [Fintype σ]
    (I : Ideal (MvPolynomial σ K)) (a : σ → K)
    (ha : ∀ P ∈ I, eval a P = 0)
    (hreg : IsRegularLocalRing
      ((Localization.AtPrime (vanishingIdeal K {a})) ⧸
        I.map (algebraMap (MvPolynomial σ K)
          (Localization.AtPrime (vanishingIdeal K {a}))))) :
    ∃ (r : ℕ) (Q : Fin r → MvPolynomial σ K) (e : Fin r ↪ σ),
      (∀ i, eval a (Q i) = 0) ∧
      (Ideal.span (Set.range Q)).map
          (algebraMap (MvPolynomial σ K) (Localization.AtPrime (vanishingIdeal K {a}))) =
        I.map (algebraMap (MvPolynomial σ K) (Localization.AtPrime (vanishingIdeal K {a}))) ∧
      eval a (Matrix.of (fun i j : Fin r => pderiv (e i) (Q j))).det ≠ 0 := by
  classical
  let m : MaximalSpectrum (MvPolynomial σ K) := ⟨vanishingIdeal K {a},inferInstance⟩
  have hm : m.asIdeal = RingHom.ker (eval a) := by
    ext P
    simp [m,vanishingIdeal,RingHom.mem_ker]
  have hIm : I ≤ m.asIdeal := by
    intro P hP
    simpa [m,vanishingIdeal] using ha P hP
  letI : IsRegularLocalRing (Localization.AtPrime m.asIdeal) :=
    IsRegularRing.isRegularLocalRing_localization m.asIdeal
  letI : IsRegularLocalRing ((Localization.AtPrime m.asIdeal) ⧸
      I.map (algebraMap (MvPolynomial σ K) (Localization.AtPrime m.asIdeal))) := hreg
  have hconormal := RegularLocalConormal.inf_maximalIdeal_sq_eq_mul
    (Localization.AtPrime m.asIdeal)
    (I.map (algebraMap (MvPolynomial σ K) (Localization.AtPrime m.asIdeal)))
  obtain ⟨r,Q,hQ,hsurj,hgrad⟩ := Gradient.basis_equations I a
  have hgen := LocalEquations.local_span_of_conormal I a m hm hIm Q hQ hgrad hconormal.le
  obtain ⟨e,hdet⟩ := exists_nonsingular_minor r
    (Matrix.of (fun i j => eval a (pderiv j (Q i)))) hsurj
  refine ⟨r,Q,e,(fun i => ha (Q i) (hQ i)),hgen.symm,?_⟩
  rw [(eval a).map_det]
  exact hdet

end AffineJacobian.LocalPresentation
end

end


section

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators Topology
noncomputable section

namespace PhilipponMultiplicity
open SectionThree SectionThreeSupport

theorem mixed_jacobian_presentations_of_regular_points
    (K : Type*) [NontriviallyNormedField K] (hK : IsPhilipponBaseField K)
    (hgeometry : ∀ (M : MultiProjectiveSpace K) (W : Set M.Point),
      @IsClosed _ M.zariskiTopology W → @IsIrreducible _ M.zariskiTopology W →
      ∀ (α : M.FactorIndex → ℕ), (∀ i, α i ≤ M.ambientDimension i) →
      (∑ i, α i = locusDimension M W) →
      ∀ B : Set M.Point, @IsClosed _ M.zariskiTopology B → B ⊆ W →
      (W \ B).Nonempty →
      ∀ l : List M.FactorIndex, (∀ i, l.count i = α i) →
        ∃ F : MvPolynomial (Fin l.length × M.Variable) K, F ≠ 0 ∧
          ∀ c : Fin l.length → M.Variable → K,
            MvPolynomial.eval (Function.uncurry c) F ≠ 0 →
            ({x : M.Point | x ∈ W ∧
              ∀ j : Fin l.length, M.eval (MixedFlag.polynomial M l c j) x = 0}).Finite ∧
            Disjoint {x : M.Point | x ∈ W ∧
              ∀ j : Fin l.length, M.eval (MixedFlag.polynomial M l c j) x = 0} B ∧
            (∀ v : M.Variable → K,
                (∀ i : M.FactorIndex,
                  (fun j : Fin (M.ambientDimension i + 1) => v ⟨i,j⟩) ≠ 0) →
                (∀ P ∈ MixedFlag.ideal M (M.vanishingIdeal W) l c l.length,
                  MvPolynomial.eval v P = 0) →
                IsRegularLocalRing
                  ((Localization.AtPrime (MvPolynomial.vanishingIdeal K {v})) ⧸
                    (MixedFlag.ideal M (M.vanishingIdeal W) l c l.length).map
                      (algebraMap M.CoordinateRing
                        (Localization.AtPrime (MvPolynomial.vanishingIdeal K {v})))))) :
    ∀ (M : MultiProjectiveSpace K) (W : Set M.Point),
      @IsClosed _ M.zariskiTopology W → @IsIrreducible _ M.zariskiTopology W →
      ∀ (α : M.FactorIndex → ℕ), (∀ i, α i ≤ M.ambientDimension i) →
      (∑ i, α i = locusDimension M W) →
      ∀ B : Set M.Point, @IsClosed _ M.zariskiTopology B → B ⊆ W →
      (W \ B).Nonempty →
      ∀ l : List M.FactorIndex, (∀ i, l.count i = α i) →
        ∃ F : MvPolynomial (Fin l.length × M.Variable) K, F ≠ 0 ∧
          ∀ c : Fin l.length → M.Variable → K,
            MvPolynomial.eval (Function.uncurry c) F ≠ 0 →
            ({x : M.Point | x ∈ W ∧
              ∀ j : Fin l.length, M.eval (MixedFlag.polynomial M l c j) x = 0}).Finite ∧
            Disjoint {x : M.Point | x ∈ W ∧
              ∀ j : Fin l.length, M.eval (MixedFlag.polynomial M l c j) x = 0} B ∧
            (∀ v : M.Variable → K,
                (∀ i : M.FactorIndex,
                  (fun j : Fin (M.ambientDimension i + 1) => v ⟨i,j⟩) ≠ 0) →
                (∀ P ∈ MixedFlag.ideal M (M.vanishingIdeal W) l c l.length,
                  MvPolynomial.eval v P = 0) →
                ∃ (r : ℕ) (Q : Fin r → M.CoordinateRing) (e : Fin r ↪ M.Variable),
                  (∀ i, MvPolynomial.eval v (Q i) = 0) ∧
                  (Ideal.span (Set.range Q)).map
                      (algebraMap M.CoordinateRing
                        (Localization.AtPrime (MvPolynomial.vanishingIdeal K {v}))) =
                    (MixedFlag.ideal M (M.vanishingIdeal W) l c l.length).map
                      (algebraMap M.CoordinateRing
                        (Localization.AtPrime (MvPolynomial.vanishingIdeal K {v}))) ∧
                  MvPolynomial.eval v
                    (Matrix.of (fun i j : Fin r => MvPolynomial.pderiv (e i) (Q j))).det ≠ 0) := by
  classical
  intro M W hW hWirr α hα hdim B hB hBW hne l hl
  obtain ⟨F,hF,hs⟩ := hgeometry M W hW hWirr α hα hdim B hB hBW hne l hl
  refine ⟨F,hF,?_⟩
  intro c hc
  obtain ⟨hfinite,hdisj,hlocal⟩ := hs c hc
  refine ⟨hfinite,hdisj,?_⟩
  intro v hv hJ
  exact AffineJacobian.LocalPresentation.of_regular_quotient
    (MixedFlag.ideal M (M.vanishingIdeal W) l c l.length) v hJ (hlocal v hv hJ)

end PhilipponMultiplicity
end

end

set_option maxHeartbeats 2400000
open PhilipponMultiplicity PhilipponMultiplicity.SectionThree PhilipponMultiplicity.SectionThreeSupport
open scoped BigOperators Topology

theorem solution
    (K : Type*) [NontriviallyNormedField K] (hK : IsPhilipponBaseField K) :
    ∀ (M : MultiProjectiveSpace K) (W : Set M.Point),
      @IsClosed _ M.zariskiTopology W → @IsIrreducible _ M.zariskiTopology W →
      ∀ (α : M.FactorIndex → ℕ), (∀ i, α i ≤ M.ambientDimension i) →
      (∑ i, α i = locusDimension M W) →
      ∀ B : Set M.Point, @IsClosed _ M.zariskiTopology B → B ⊆ W →
      (W \ B).Nonempty →
      ∀ l : List M.FactorIndex, (∀ i, l.count i = α i) →
        ∃ F : MvPolynomial (Fin l.length × M.Variable) K, F ≠ 0 ∧
          ∀ c : Fin l.length → M.Variable → K,
            MvPolynomial.eval (Function.uncurry c) F ≠ 0 →
            ({x : M.Point | x ∈ W ∧
              ∀ j : Fin l.length, M.eval (MixedFlag.polynomial M l c j) x = 0}).Finite ∧
            Disjoint {x : M.Point | x ∈ W ∧
              ∀ j : Fin l.length, M.eval (MixedFlag.polynomial M l c j) x = 0} B ∧
            (∀ v : M.Variable → K,
                (∀ i : M.FactorIndex,
                  (fun j : Fin (M.ambientDimension i + 1) => v ⟨i,j⟩) ≠ 0) →
                (∀ P ∈ MixedFlag.ideal M (M.vanishingIdeal W) l c l.length,
                  MvPolynomial.eval v P = 0) →
                ∃ (r : ℕ) (Q : Fin r → M.CoordinateRing) (e : Fin r ↪ M.Variable),
                  (∀ i, MvPolynomial.eval v (Q i) = 0) ∧
                  (Ideal.span (Set.range Q)).map
                      (algebraMap M.CoordinateRing
                        (Localization.AtPrime (MvPolynomial.vanishingIdeal K {v}))) =
                    (MixedFlag.ideal M (M.vanishingIdeal W) l c l.length).map
                      (algebraMap M.CoordinateRing
                        (Localization.AtPrime (MvPolynomial.vanishingIdeal K {v}))) ∧
                  MvPolynomial.eval v
                    (Matrix.of (fun i j : Fin r => MvPolynomial.pderiv (e i) (Q j))).det ≠ 0) := by
  exact mixed_jacobian_presentations_of_regular_points K hK
    (exists_principal_open_regular_point_mixed_zero_locus K hK)
