-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_LowerBoundFree_Jint_line_8a43ca352fca
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T05:25:20.006826+00:00
-- url     : https://prove2.me/submissions/edaf7170-f66d-4d4d-ad01-87e5569d9c6b

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HodgeLowerBound_FrameDefinitions_PermFinTwoUniv
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LowerBoundFree_sum_unit_perm_2a06cd6a3a93
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LowerBoundFree_rhoMono_line_bec6bd5baceb
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LowerBoundFree_dimN_line_500fcd94b89b
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LowerBoundFree_muPoly_line_d486cf876662
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LowerBoundFree_vandBlocks_line_0cdaf03e7255

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open MvPolynomial
namespace GroundTheory.Heights₂.Heights.LowerBoundFree
theorem _root_.solution (cf : ℚ) : Jint Unit 2 1 cf = -cf := by
  unfold Jint flagInt antisym
  rw [dimN_line, pow_one, muPoly_line, fib, vandBlocks_line, mul_one, sum_unit_perm, rhoMono_line]
  simp only [weylSign, Finset.univ_unique, Finset.prod_singleton, Equiv.Perm.sign_one,
    Equiv.Perm.sign_swap (show (0 : Fin 2) ≠ 1 by decide), map_mul, rename_X, rename_C, coeff_add,
    coeff_smul, smul_eq_mul, weylAct]
  rw [coeff_X_mul', coeff_X_mul']
  simp [coeff_C, Finsupp.single_apply, Equiv.swap_apply_of_ne_of_ne]
end GroundTheory.Heights₂.Heights.LowerBoundFree
