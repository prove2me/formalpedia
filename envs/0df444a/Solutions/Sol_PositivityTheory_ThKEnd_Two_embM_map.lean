-- Prove2me | solution 1 for PositivityTheory.ThKEnd.Two.embM_map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T05:22:45.285578+00:00
-- url     : https://prove2.me/submissions/9f24c746-a1d6-4882-b761-733523701f97

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
theorem _root_.solution {S' R' : Type} [CommRing S'] [CommRing R'] [Algebra S' R'] {c' : R' →ₐ[S'] R'} (f : R →+* R')
    (hf : ∀ a, f (c a) = c' (f a)) (g g' : Matrix k k R) :
    (embM c J X Y g g').map f = embM c' (J.map f) (X.map f) (Y.map f) (g.map f) (g'.map f) := by
  have hfc : (f : R → R') ∘ c = c' ∘ f := funext hf
  simp only [embM, Matrix.map_sub f (map_sub f), Matrix.map_add f (map_add f), Matrix.map_mul,
    Matrix.map_one f (map_zero f) (map_one f), Matrix.transpose_map, Matrix.map_map, hfc]
end PositivityTheory.ThKEnd.Two
