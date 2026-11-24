-- Prove2me | solution 1 for PositivityTheory.Mix.PlaneOK.ext
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T11:47:35.654964+00:00
-- url     : https://prove2.me/submissions/0277bd89-8ca0-48dc-89e3-80dd6487dc6c

import Mathlib
import Definitions.Def_Development_WeilBound_ThetaLifts_LeviDeterminants_MixedModels_PlaneGen

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PositivityTheory PositivityTheory.Mix
open Matrix
variable {R : Type} [CommRing R] {n k : ℕ}
variable {c : R →+* R} {J : Matrix (Fin n) (Fin n) R}
open PositivityTheory.Mix.PlaneOK
variable {ε : R} {x y : Fin n → R} {ι : Matrix (Fin n) (Fin k) R} (h : PlaneOK c J ε x y ι)
include h
namespace PositivityTheory.Mix.PlaneOK
theorem _root_.solution {A B : Matrix (Fin n) (Fin n) R} (hx : A *ᵥ x = B *ᵥ x) (hy : A *ᵥ y = B *ᵥ y)
    (hi : ∀ z, A *ᵥ (ι *ᵥ z) = B *ᵥ (ι *ᵥ z)) : A = B := by
  have hv : ∀ v, A *ᵥ v = B *ᵥ v := by
    intro v
    obtain ⟨s, t, z, rfl⟩ := h.span v
    simp only [mulVec_add, mulVec_smul, hx, hy, hi]
  ext i j
  have e := congrFun (hv (Pi.single j 1)) i
  simpa [mulVec_single_one] using e
end PositivityTheory.Mix.PlaneOK
