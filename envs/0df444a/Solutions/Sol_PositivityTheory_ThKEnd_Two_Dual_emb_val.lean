-- Prove2me | solution 1 for PositivityTheory.ThKEnd.Two.Dual.emb_val
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:00:20.627079+00:00
-- url     : https://prove2.me/submissions/3402e081-eac6-426c-a9a1-dfcf48396bd9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
import Definitions.Def_Development_WeilBound_ThetaLifts_EigenvalueEndgame_SignatureSplitting_EmbMMul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
set_option linter.unusedSectionVars false
open PositivityTheory PositivityTheory.ThKEnd PositivityTheory.ThKEnd.Two
open Matrix GlobalTheory.WeilM
variable {S R d k : Type} [CommRing S] [CommRing R] [Algebra S R] [Fintype d] [DecidableEq d] [Fintype k] [DecidableEq k]
variable {c : R →ₐ[S] R} {J : Matrix d d R} {X Y : Matrix d k R}
namespace PositivityTheory.ThKEnd.Two
namespace Dual
theorem _root_.solution (h : Dual c J X Y) (g : GL k R) : (h.emb g).1.1 = embM c J X Y g.1 ((g⁻¹).1.map c)ᵀ := rfl
end Dual
end PositivityTheory.ThKEnd.Two
