-- Prove2me | solution 1 for PositivityTheory.ThKEnd.Two.Dual.emb_cont
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T05:21:33.973034+00:00
-- url     : https://prove2.me/submissions/002e5e53-62bd-42e9-8233-a34c2f51fee7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
import Definitions.Def_Development_WeilBound_ThetaLifts_EigenvalueEndgame_SignatureSplitting_EmbMMul
import Theorems.Thm_PositivityTheory_ThKEnd_Two_Dual_emb_val

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
theorem _root_.solution [TopologicalSpace R] [IsTopologicalRing R] (h : Dual c J X Y) (hc : Continuous c) : Continuous h.emb := by
  have hE : ∀ {a b : GL k R → Matrix k k R}, Continuous a → Continuous b →
      Continuous fun g => embM c J X Y (a g) (b g) := by
    intro a b ha hb
    simp only [embM]
    fun_prop
  have hv : Continuous fun g : GL k R => (g : Matrix k k R) := Units.continuous_val
  have hi : Continuous fun g : GL k R => ((g⁻¹ : GL k R) : Matrix k k R) := Units.continuous_coe_inv
  have hii : Continuous fun g : GL k R => ((g⁻¹⁻¹ : GL k R) : Matrix k k R) := by
    simpa only [inv_inv] using hv
  rw [continuous_induced_rng]
  refine Units.continuous_iff.mpr ⟨?_, ?_⟩
  · exact (hE hv ((hi.matrix_map hc).matrix_transpose)).congr fun g => (h.emb_val g).symm
  · exact (hE hi ((hii.matrix_map hc).matrix_transpose)).congr fun g => rfl
end Dual
end PositivityTheory.ThKEnd.Two
