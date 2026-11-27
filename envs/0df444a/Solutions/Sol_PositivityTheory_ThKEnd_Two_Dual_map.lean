-- Prove2me | solution 1 for PositivityTheory.ThKEnd.Two.Dual.map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T05:22:23.7978+00:00
-- url     : https://prove2.me/submissions/84588149-b515-47fa-a1af-ea6ec91e646c

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
theorem _root_.solution (h : Dual c J X Y) {S' R' : Type} [CommRing S'] [CommRing R'] [Algebra S' R'] {c' : R' →ₐ[S'] R'} (f : R →+* R')
    (hf : ∀ a, f (c a) = c' (f a)) (hc : ∀ a, c' (c' a) = a) : Dual c' (J.map f) (X.map f) (Y.map f) := by
  have hfc : (f : R → R') ∘ c = c' ∘ f := funext hf
  refine ⟨hc, ?_, ?_, ?_, ?_⟩
  · have e := congrArg (fun M => Matrix.map M f) h.skew
    simp only [Matrix.transpose_map, Matrix.map_map, hfc, Matrix.map_neg f (map_neg f)] at e
    simpa only [Matrix.transpose_map, Matrix.map_map] using e
  · have e := congrArg (fun M => Matrix.map M f) h.xx
    simp only [Matrix.map_mul, Matrix.transpose_map, Matrix.map_map, hfc, Matrix.map_zero f (map_zero f)] at e
    simpa only [Matrix.transpose_map, Matrix.map_map] using e
  · have e := congrArg (fun M => Matrix.map M f) h.yy
    simp only [Matrix.map_mul, Matrix.transpose_map, Matrix.map_map, hfc, Matrix.map_zero f (map_zero f)] at e
    simpa only [Matrix.transpose_map, Matrix.map_map] using e
  · have e := congrArg (fun M => Matrix.map M f) h.xy
    simp only [Matrix.map_mul, Matrix.transpose_map, Matrix.map_map, hfc, Matrix.map_one f (map_zero f) (map_one f)] at e
    simpa only [Matrix.transpose_map, Matrix.map_map] using e
end Dual
end PositivityTheory.ThKEnd.Two
