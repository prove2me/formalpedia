-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_Flag_sumPderiv_X_8d74257f5c74
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:40:20.80061+00:00
-- url     : https://prove2.me/submissions/f8f72379-7f3b-4a04-8280-60c22b81a34a

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_FlagBasic
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Flag_sumPderiv_apply_de6d8a815ba9

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
variable {σ ι : Type*}
namespace GroundTheory.Heights₂.Heights.RestTerms.Flag
theorem _root_.solution [DecidableEq σ] (s : Finset ι) (g : ι → σ) (v : σ) :
    sumPderiv s g (X v) = C (((s.filter fun l => g l = v).card : ℕ) : ℚ) := by
  rw [sumPderiv_apply, map_natCast]
  simp only [pderiv_X, Pi.single_apply]
  rw [Finset.sum_boole]
  simp only [eq_comm]
end GroundTheory.Heights₂.Heights.RestTerms.Flag
