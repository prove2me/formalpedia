-- Prove2me | solution 1 for PI.FJMX.leadT_hom_row
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T09:38:53.87142+00:00
-- url     : https://prove2.me/submissions/9da7798f-d893-48c1-af2b-62afb2af35cf

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
theorem _root_.solution (ρ : Fin m → Ix p q) (κ : Fin k → Ix r s) (w : Ln p q r s → ℕ) (i₀ : Fin m)
    (hw : ∀ i j, w (ρ i, κ j) = if i = i₀ then 1 else 0) (t : ℕ) :
    IsWeightedHomogeneous w (leadT (varMat ρ κ) t) (if i₀.val < t then 1 else 0) := by
  classical
  unfold leadT
  split_ifs with hh hlt
  · have := minorPolynomial_isWeightedHomogeneous (R := ℂ) (fun i j : Fin t => (ρ (Fin.castLE hh.1 i), κ (Fin.castLE hh.2 j))) w
      (fun i => if Fin.castLE hh.1 i = i₀ then 1 else 0) (fun _ => 0) (fun i j => by simp [hw])
    have hs : ∑ i : Fin t, (if Fin.castLE hh.1 i = i₀ then 1 else 0) + ∑ _j : Fin t, 0 = 1 := by
      simp only [Finset.sum_const_zero, add_zero]
      rw [Finset.sum_eq_single ⟨i₀.val, hlt⟩]
      · simp [Fin.ext_iff]
      · intro i _ hi
        rw [if_neg]
        intro e
        apply hi
        ext
        simp [← e]
      · simp
    rw [hs] at this
    exact this
  · have := minorPolynomial_isWeightedHomogeneous (R := ℂ) (fun i j : Fin t => (ρ (Fin.castLE hh.1 i), κ (Fin.castLE hh.2 j))) w
      (fun i => if Fin.castLE hh.1 i = i₀ then 1 else 0) (fun _ => 0) (fun i j => by simp [hw])
    have hs : ∑ i : Fin t, (if Fin.castLE hh.1 i = i₀ then 1 else 0) + ∑ _j : Fin t, 0 = 0 := by
      simp only [Finset.sum_const_zero, add_zero]
      apply Finset.sum_eq_zero
      intro i _
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
