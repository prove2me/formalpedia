-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AI.exists_basis_zero_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:28:07.050482+00:00
-- url     : https://prove2.me/submissions/97a3e131-a6ac-40f1-abbd-e9946b832ebe

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_LintegralIoiOfRealMul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_KappaB

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AI
open MeasureTheory
namespace ReciprocityTheory.ChartRestriction.G.AI
theorem _root_.solution {u : E3} (hu : ‖u‖ = 1) :
    ∃ b : OrthonormalBasis (Fin 3) ℝ E3, b 0 = u := by
  have hv : Orthonormal ℝ (({0} : Set (Fin 3)).restrict fun _ : Fin 3 => u) := by
    refine ⟨fun _ => hu, fun i j hij => (hij (Subsingleton.elim i j)).elim⟩
  obtain ⟨b, hb⟩ := Orthonormal.exists_orthonormalBasis_extension_of_card_eq (by simp) hv
  exact ⟨b, hb 0 rfl⟩
end ReciprocityTheory.ChartRestriction.G.AI
