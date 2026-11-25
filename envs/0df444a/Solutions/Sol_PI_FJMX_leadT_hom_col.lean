-- Prove2me | solution 1 for PI.FJMX.leadT_hom_col
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T09:38:50.786205+00:00
-- url     : https://prove2.me/submissions/1642ac8f-be77-4096-bb14-b1758cbf31c4

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_JointMultOfSteps
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_ExistGen
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_ExistWt
import Theorems.Thm_PI_FJMX_minorPolynomial_isWeightedHomogeneous


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial FockH1Action PI.FJM
noncomputable section
open PI PI.FJMX
variable {p q r s m k : ℕ}
namespace PI.FJMX
theorem _root_.solution (ρ : Fin m → Ix p q) (κ : Fin k → Ix r s) (w : Ln p q r s → ℕ) (j₀ : Fin k)
    (hw : ∀ i j, w (ρ i, κ j) = if j = j₀ then 1 else 0) (t : ℕ) :
    IsWeightedHomogeneous w (leadT (varMat ρ κ) t) (if j₀.val < t then 1 else 0) := by
  classical
  unfold leadT
  split_ifs with hh hlt
  · have := minorPolynomial_isWeightedHomogeneous (R := ℂ) (fun i j : Fin t => (ρ (Fin.castLE hh.1 i), κ (Fin.castLE hh.2 j))) w
      (fun _ => 0) (fun j => if Fin.castLE hh.2 j = j₀ then 1 else 0) (fun i j => by simp [hw])
    have hs : ∑ _i : Fin t, 0 + ∑ j : Fin t, (if Fin.castLE hh.2 j = j₀ then 1 else 0) = 1 := by
      simp only [Finset.sum_const_zero, zero_add]
      rw [Finset.sum_eq_single ⟨j₀.val, hlt⟩]
      · simp [Fin.ext_iff]
      · intro j _ hj
        rw [if_neg]
        intro e
        apply hj
        ext
        simp [← e]
      · simp
    rw [hs] at this
    exact this
  · have := minorPolynomial_isWeightedHomogeneous (R := ℂ) (fun i j : Fin t => (ρ (Fin.castLE hh.1 i), κ (Fin.castLE hh.2 j))) w
      (fun _ => 0) (fun j => if Fin.castLE hh.2 j = j₀ then 1 else 0) (fun i j => by simp [hw])
    have hs : ∑ _i : Fin t, 0 + ∑ j : Fin t, (if Fin.castLE hh.2 j = j₀ then 1 else 0) = 0 := by
      simp only [Finset.sum_const_zero, zero_add]
      apply Finset.sum_eq_zero
      intro j _
      rw [if_neg]
      intro e
      apply hlt
      rw [← e]
      simp
    rw [hs] at this
    exact this
  · exact isWeightedHomogeneous_zero _ _ _
  · exact isWeightedHomogeneous_zero _ _ _
end PI.FJMX
