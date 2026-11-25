-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_FinGradedSub_cellCone_of_subset_d748224c1d3f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T08:56:11.461462+00:00
-- url     : https://prove2.me/submissions/2c0e7bbe-48d4-4932-8a9b-2e5492bcff3b

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsTildeTail
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PTildeTailLoc
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PTildeTail

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman
open MvPolynomial
noncomputable section
universe u w
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω} (M : FinGradedSub (S := S) (x := x) Ω)
namespace GroundTheory.Heights₂.Heights.Kleiman
namespace FinGradedSub
theorem _root_.solution {I : StdCell N} (h : I.1 ⊆ support x) :
    M.cellCone I = locCone M I.1 h := dif_pos h
end FinGradedSub
end GroundTheory.Heights₂.Heights.Kleiman
