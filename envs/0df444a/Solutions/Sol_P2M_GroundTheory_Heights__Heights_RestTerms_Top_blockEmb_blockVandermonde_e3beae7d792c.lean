-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_Top_blockEmb_blockVandermonde_e3beae7d792c
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T04:53:03.827558+00:00
-- url     : https://prove2.me/submissions/2e70e5a2-72dc-45fa-b1a3-349d134d5480

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
theorem _root_.solution (f N : ℕ) (σ : Fin f) :
    blockEmb f N σ (blockVandermonde 1 N) =
      vandermondeOf (fun i : Fin N => (X (σ, i) : RootRing f N)) := by
  simp [blockVandermonde, vandermondeOf, blockEmb, map_prod, map_sub, rename_X]
end GroundTheory.Heights₂.Heights.RestTerms.Top
