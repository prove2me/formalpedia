-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_Top_blockPermute_blockEmb_50bfbd9b99dc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T04:54:01.411785+00:00
-- url     : https://prove2.me/submissions/b734edd7-542f-40a3-ad99-1615c9319dc8

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Expand

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
open GroundTheory.Heights₂.Heights.RestTerms.Top
open MvPolynomial Finset
noncomputable section
namespace GroundTheory.Heights₂.Heights.RestTerms.Top
theorem _root_.solution (f N : ℕ) (w : Fin f → Equiv.Perm (Fin N)) (σ : Fin f)
    (P : RootRing 1 N) :
    blockPermute f N w (blockEmb f N σ P) =
      blockEmb f N σ (blockPermute 1 N (fun _ => w σ) P) := by
  simp only [blockPermute, blockEmb, rename_rename]
  rfl
end GroundTheory.Heights₂.Heights.RestTerms.Top
