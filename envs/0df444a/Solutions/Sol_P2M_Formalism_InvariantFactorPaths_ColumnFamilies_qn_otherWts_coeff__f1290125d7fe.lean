-- Prove2me | solution 1 for P2M_Formalism_InvariantFactorPaths_ColumnFamilies_qn_otherWts_coeff__f1290125d7fe
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:45:23.847976+00:00
-- url     : https://prove2.me/submissions/75c00b1c-aea7-4d47-bd3a-38a5819c3957

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_TransposeVariables
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_FockQHW
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_CoeffTransposeVariables
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qn_otherWts_coeff
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qn_swap_apply
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_coeff_transposeVariables
import Theorems.Thm_Formalism_GradedWeylDivisibility_lhwline_mnu_apply
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_transposeVariables_involutive
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply



set_option autoImplicit false
open MvPolynomial
noncomputable section
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.ColumnFamilies
open Formalism.GradedWeylDivisibility
namespace Formalism.InvariantFactorPaths.ColumnFamilies
theorem _root_.solution (n : ℕ) (ν : Fin n → ℕ) (z : MvPolynomial (Fin n × Fin n) ℚ)
    (hz : z ∈ otherWts (glOps ℚ n (rowLetters n) Set.univ) (fun a => (ν a : ℤ))) :
    coeff (lhwline_mnu (le_refl n) ν) (transposeVariables ℚ n z) = 0 := by
  classical
  have h := coeff_transposeVariables n (transposeVariables ℚ n z) (lhwline_mnu (le_refl n) ν)
  rw [transposeVariables_involutive] at h
  rw [← h]
  refine qn_otherWts_coeff n _ z hz _ ?_
  funext a
  simp only [qn_wt, qn_swap_apply, lhwline_mnu_apply]
  rw [Finset.sum_eq_single a]
  · simp
  · intro b _ hb
    have : a.val ≠ b.val := fun h => hb (Fin.ext h).symm
    simp [this]
  · simp
end Formalism.InvariantFactorPaths.ColumnFamilies
