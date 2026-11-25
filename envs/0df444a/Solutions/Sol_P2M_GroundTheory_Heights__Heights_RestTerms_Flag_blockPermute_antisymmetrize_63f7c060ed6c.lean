-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_Flag_blockPermute_antisymmetrize_63f7c060ed6c
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T05:29:33.24875+00:00
-- url     : https://prove2.me/submissions/4ba5dabf-5dde-4f92-9e6e-ec05665083c8

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_FlagBasic
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Flag_blockPermute_blockPermute_98b261a82348
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Flag_blockSign_mul_51072d07ff72
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Flag_blockSign_mul_self_a12250e20b18

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open GroundTheory.Heights₂.Heights.RestTerms
open GroundTheory.Heights₂.Heights.RestTerms.Flag
open MvPolynomial Finset
noncomputable section
namespace GroundTheory.Heights₂.Heights.RestTerms.Flag
theorem _root_.solution (f N : ℕ) (v : Fin f → Equiv.Perm (Fin N)) (H : RootRing f N) :
    blockPermute f N v (antisymmetrize f N H) = blockSign f N v • antisymmetrize f N H := by
  simp only [antisymmetrize, map_sum, map_smul, blockPermute_blockPermute, Finset.smul_sum, smul_smul]
  refine Fintype.sum_equiv (Equiv.mulLeft v) _ _ (fun w => ?_)
  simp only [Equiv.coe_mulLeft]
  congr 1
  rw [blockSign_mul, ← mul_assoc, blockSign_mul_self, one_mul]
end GroundTheory.Heights₂.Heights.RestTerms.Flag
