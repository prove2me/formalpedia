-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_inh_van_eq_517663f47d01
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T05:13:21.452041+00:00
-- url     : https://prove2.me/submissions/bde0dc16-158e-4a15-a6d8-1222f078fe4a

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Inhabitants

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
open MvPolynomial
noncomputable section
open MvPolynomial
namespace GroundTheory.Heights₂.Heights.RestTerms
theorem _root_.solution : blockVandermonde 1 (1+1) = flagTwoFirstRoot - flagTwoSecondRoot := by
  have hIoi0 : Finset.Ioi (0 : Fin (1+1)) = {1} := by decide
  have hIoi1 : Finset.Ioi (1 : Fin (1+1)) = ∅ := by decide
  simp [blockVandermonde, vandermondeOf, Fin.prod_univ_two, hIoi0, hIoi1]
end GroundTheory.Heights₂.Heights.RestTerms
