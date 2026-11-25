-- Prove2me | solution 1 for PositivityTheory.RgUd.TP.Desc.Piece.PSect.fl_step
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T11:55:20.255464+00:00
-- url     : https://prove2.me/submissions/baf33f00-922b-4819-9b91-5ec5b136010d

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_UnitaryDualProof_TwistedPieces_FiniteDimensionalDescent_ClosedOrbitPieces_FrobeniusSections_CompIterateFrobenius

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PositivityTheory PositivityTheory.RgUd PositivityTheory.RgUd.TP PositivityTheory.RgUd.TP.Desc PositivityTheory.RgUd.TP.Desc.Piece PositivityTheory.RgUd.TP.Desc.Piece.PSect
open Module Polynomial IntermediateField
namespace PositivityTheory.RgUd.TP.Desc.Piece.PSect
theorem _root_.solution {F E : Type*} [Field F] [Field E] [Algebra F E] (p : ℕ) [hp : Fact p.Prime]
    [CharP E p] (h : ∀ x : E, x ^ p ∈ Set.range (algebraMap F E))
    (L : IntermediateField F E) {x : E} (hx : x ∉ L) :
    finrank L (adjoin L {x}) = p := by
  obtain ⟨a, ha⟩ := h x
  have hxp : x ^ p ∈ L := ha ▸ L.algebraMap_mem a
  set b : L := ⟨x ^ p, hxp⟩ with hb
  have hirr : Irreducible (X ^ p - C b) := by
    apply X_pow_sub_C_irreducible_of_prime hp.out
    intro y hy
    apply hx
    have h1 : (y : E) ^ p = x ^ p := by
      have := congrArg (fun z : L => (z : E)) hy
      simpa [hb] using this
    have h2 : (y : E) = x := frobenius_inj E p (by simpa [frobenius_def] using h1)
    exact h2 ▸ y.2
  have haev : aeval x (X ^ p - C b) = 0 := by
    simp [hb]
  have hmon : (X ^ p - C b).Monic := monic_X_pow_sub_C _ hp.out.ne_zero
  have hmin : X ^ p - C b = minpoly L x := minpoly.eq_of_irreducible_of_monic hirr haev hmon
  have hint : IsIntegral L x := ⟨X ^ p - C b, hmon, by simpa [aeval_def] using haev⟩
  rw [adjoin.finrank hint, ← hmin, natDegree_X_pow_sub_C]
end PositivityTheory.RgUd.TP.Desc.Piece.PSect
