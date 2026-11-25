-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.algebraicIndependent_scaledForms
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T13:29:41.5078+00:00
-- url     : https://prove2.me/submissions/5485927c-d8fe-44ec-8a79-95f7e1004fea

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_AevalElimEqRenameLinearSubstitution
import Definitions.Def_ReciprocityTheory_SemistableReduction_ExistsDualDerivations
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_SaturatedChains_AlgStep
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_AlgebraicIndependentScaledForms
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_DerivationAlgebraicIndependence_algebraicIndependent_of_derivations
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_DerivationAlgebraicIndependence_coeffDer_C
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_DerivationAlgebraicIndependence_coeffDer_X


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0
open MvPolynomial ReciprocityTheory.MultiplicativeHeights.DerivationAlgebraicIndependence
open MvPolynomial ReciprocityTheory.MultiplicativeHeights.DerivationAlgebraicIndependence
namespace ReciprocityTheory.ChartRestriction.G.T0
theorem _root_.solution {K Ω : Type} [Field K] [CharZero K] [Field Ω] [Algebra K Ω] {D N : ℕ}
    (y : Fin (N + 1) → Ω) (jc : Fin (N + 1)) (hy : y jc = 1)
    (J : Fin D → Fin N) (δ : Fin D → Derivation K Ω Ω)
    (hδ : ∀ a b, δ a (y (jc.succAbove (J b))) = if a = b then 1 else 0)
    (ρ : Option (Fin D) → Fin (D + 2)) (hρ : Function.Injective ρ) :
    AlgebraicIndependent K (Sum.elim
      (fun p : Fin (D + 2) × Fin (N + 1) =>
        (X (some p) : MvPolynomial (Option (Fin (D + 2) × Fin (N + 1))) Ω))
      (fun o : Option (Fin D) => X none * ∑ j, X (some (ρ o, j)) * C (y j))) := by
  classical
  refine algebraicIndependent_of_derivations _ (Sum.elim
    (fun o => (pderiv o :
      Derivation Ω (MvPolynomial (Option (Fin (D + 2) × Fin (N + 1))) Ω)
        (MvPolynomial (Option (Fin (D + 2) × Fin (N + 1))) Ω)).restrictScalars K)
    (fun a => coeffDer (σ := Option (Fin (D + 2) × Fin (N + 1))) (δ a))) ?_
  intro c H
  have hZ : ∀ o, pderiv (none : Option (Fin (D + 2) × Fin (N + 1)))
      (∑ j, X (some (ρ o, j)) * C (y j) : MvPolynomial (Option (Fin (D + 2) × Fin (N + 1))) Ω) = 0 := by
    intro o; simp [pderiv_X]
  have hpn : ∀ o, pderiv (none : Option (Fin (D + 2) × Fin (N + 1)))
      (X none * ∑ j, X (some (ρ o, j)) * C (y j) : MvPolynomial (Option (Fin (D + 2) × Fin (N + 1))) Ω) =
        ∑ j, X (some (ρ o, j)) * C (y j) := by
    intro o; rw [Derivation.leibniz, hZ, smul_zero, zero_add, pderiv_X]; simp
  have hcd : ∀ a o, coeffDer (σ := Option (Fin (D + 2) × Fin (N + 1))) (δ a)
      (X none * ∑ j, X (some (ρ o, j)) * C (y j)) =
        X none * ∑ j, X (some (ρ o, j)) * C (δ a (y j)) := by
    intro a o
    simp [Derivation.leibniz, coeffDer_X, coeffDer_C, map_sum]
  let M : Matrix (Option (Fin D)) (Option (Fin D))
      (MvPolynomial (Option (Fin (D + 2) × Fin (N + 1))) Ω) := fun r o =>
    match r with
    | none => ∑ j, X (some (ρ o, j)) * C (y j)
    | some a => X none * ∑ j, X (some (ρ o, j)) * C (δ a (y j))
  have e1 : ∑ o, c (Sum.inr o) * ∑ j, (X (some (ρ o, j)) * C (y j) :
      MvPolynomial (Option (Fin (D + 2) × Fin (N + 1))) Ω) = 0 := by
    have := H (Sum.inl none)
    rw [Fintype.sum_sum_type] at this
    simp only [Sum.elim_inl, Sum.elim_inr, Derivation.coe_restrictScalars, hpn] at this
    rwa [Finset.sum_eq_zero (fun p _ => by simp [pderiv_X]), zero_add] at this
  have e2 : ∀ a, ∑ o, c (Sum.inr o) * (X none * ∑ j, (X (some (ρ o, j)) * C (δ a (y j)) :
      MvPolynomial (Option (Fin (D + 2) × Fin (N + 1))) Ω)) = 0 := by
    intro a
    have := H (Sum.inr a)
    rw [Fintype.sum_sum_type] at this
    simp only [Sum.elim_inl, Sum.elim_inr, hcd] at this
    rwa [Finset.sum_eq_zero (fun p _ => by simp [coeffDer_X]), zero_add] at this
  have hv : M.mulVec (fun o => c (Sum.inr o)) = 0 := by
    funext r
    cases r with
    | none =>
      simp only [Matrix.mulVec, dotProduct, Pi.zero_apply]
      rw [← e1]
      exact Finset.sum_congr rfl fun o _ => mul_comm _ _
    | some a =>
      simp only [Matrix.mulVec, dotProduct, Pi.zero_apply]
      rw [← e2 a]
      exact Finset.sum_congr rfl fun o _ => mul_comm _ _
  let pt : Option (Fin (D + 2) × Fin (N + 1)) → Ω := fun v =>
    match v with
    | none => 1
    | some q => ∑ o : Option (Fin D), if ρ o = q.1 then
        (match o with
          | none => if q.2 = jc then 1 else 0
          | some b => (if q.2 = jc then -y (jc.succAbove (J b)) else 0) +
              (if q.2 = jc.succAbove (J b) then 1 else 0))
        else 0
  have hpt0 : ∀ j, pt (some (ρ none, j)) = if j = jc then 1 else 0 := by
    intro j
    show (∑ o : Option (Fin D), _) = _
    rw [Finset.sum_eq_single none]
    · simp
    · intro o _ ho; rw [if_neg]; exact fun h => ho (hρ h)
    · simp
  have hpt1 : ∀ b j, pt (some (ρ (some b), j)) = (if j = jc then -y (jc.succAbove (J b)) else 0) +
      (if j = jc.succAbove (J b) then 1 else 0) := by
    intro b j
    show (∑ o : Option (Fin D), _) = _
    rw [Finset.sum_eq_single (some b)]
    · simp
    · intro o _ ho; rw [if_neg]; exact fun h => ho (hρ h)
    · simp
  have hptn : pt none = 1 := rfl
  have hne : ∀ b, jc.succAbove (J b) ≠ jc := fun b => Fin.succAbove_ne jc (J b)
  have hev : (MvPolynomial.eval pt).mapMatrix M = 1 := by
    ext r o
    rw [RingHom.mapMatrix_apply, Matrix.map_apply]
    cases r with
    | none =>
      cases o with
      | none => simp [M, hpt0, hy]
      | some b =>
        simp [M, hpt1, add_mul, Finset.sum_add_distrib, hy, Matrix.one_apply]
    | some a =>
      cases o with
      | none =>
        simp [M, hpt0, hy, hptn, Matrix.one_apply]
      | some b =>
        simp [M, hpt1, add_mul, Finset.sum_add_distrib, hy, hδ, Matrix.one_apply, hptn]
  have hdet : M.det ≠ 0 := by
    intro h0
    have := RingHom.map_det (MvPolynomial.eval pt) M
    rw [h0, map_zero, hev, Matrix.det_one] at this
    exact zero_ne_one this
  have hc2 : ∀ o, c (Sum.inr o) = 0 := fun o =>
    congrFun (Matrix.eq_zero_of_mulVec_eq_zero hdet hv) o
  intro i
  rcases i with p | o
  · have := H (Sum.inl (some p))
    simpa [Fintype.sum_sum_type, hc2, pderiv_X, Pi.single_apply] using this
  · exact hc2 o
end ReciprocityTheory.ChartRestriction.G.T0
