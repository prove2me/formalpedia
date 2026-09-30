-- Prove2me | solution 1 for PhilipponMultiplicity.proposition_3_3
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-27T10:51:00.580168+00:00
-- url     : https://prove2.me/submissions/f46468fd-a490-4fc9-b83a-d45585f1b191

import Theorems.Thm_PhilipponMultiplicity_proposition_3_3_radical
import Theorems.Thm_PhilipponMultiplicity_proposition_3_3_cohenMacaulay
set_option autoImplicit false
open PhilipponMultiplicity

theorem solution
    (K : Type*) [NontriviallyNormedField K] (hK : IsPhilipponBaseField K)
    (M : MultiProjectiveSpace K)
    (I₀ : Ideal M.CoordinateRing) (hI₀ : IsMultihomogeneousIdeal M I₀)
    (m : ℕ) (P : Fin m → M.CoordinateRing) (D : M.FactorIndex → ℕ)
    (hP : ∀ j, IsMultihomogeneousOfDegreeAtMost M (P j) D) :
    let I := I₀ ⊔ Ideal.span (Set.range P)
    (componentHilbertSum M I.radical (⊤ : MaximalOpenLocus M) D ≤
      componentHilbertSum M I₀.radical (⊤ : MaximalOpenLocus M) D) ∧
    (∀ U : MaximalOpenLocus M, IsLocallyCohenMacaulayOn M I₀ U →
      componentHilbertSum M I U D ≤ componentHilbertSum M I₀ U D)  := by
  exact ⟨proposition_3_3_radical M I₀ hI₀ m P D hP ⊤,
    fun U hCM => proposition_3_3_cohenMacaulay K hK M I₀ hI₀ m P D hP U hCM⟩
