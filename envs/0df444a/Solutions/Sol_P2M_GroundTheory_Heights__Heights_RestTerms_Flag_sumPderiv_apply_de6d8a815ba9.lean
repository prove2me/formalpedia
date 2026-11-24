-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_Flag_sumPderiv_apply_de6d8a815ba9
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:36:26.487866+00:00
-- url     : https://prove2.me/submissions/e60b9a7f-8a4a-4216-9663-cea44fafe728

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_FlagBasic

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
theorem _root_.solution (s : Finset ι) (g : ι → σ) (P : MvPolynomial σ ℚ) :
    sumPderiv s g P = ∑ l ∈ s, pderiv (g l) P := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [sumPderiv]
  | insert b s hb ih =>
    rw [Finset.sum_insert hb, ← ih]
    simp [sumPderiv, Finset.sum_insert hb]
end GroundTheory.Heights₂.Heights.RestTerms.Flag
