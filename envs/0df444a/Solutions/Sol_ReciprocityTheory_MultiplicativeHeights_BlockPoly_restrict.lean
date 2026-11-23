-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.BlockPoly.restrict
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:14:06.910582+00:00
-- url     : https://prove2.me/submissions/6ebe0934-1a79-470f-9be7-6b834c665feb

import Definitions.Def_ReciprocityTheory_SemistableReduction_IntCoresA
import Definitions.Def_ReciprocityTheory_SemistableReduction_IntCoresB

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights
open MeasureTheory Metric
namespace ReciprocityTheory.MultiplicativeHeights
namespace BlockPoly
theorem _root_.solution {k n : ℕ} {a : Fin (k + 1) → ℕ} {F : (Fin (k + 1) → Fin n → ℂ) → ℂ}
    (hF : BlockPoly (k + 1) n a F) (v : Fin n → ℂ) :
    BlockPoly k n (fun j => a j.succ) (fun p => F (Fin.cons v p)) := by
  refine ⟨hF.1.comp (continuous_const.finCons continuous_id), fun b p => ?_⟩
  obtain ⟨g, hg, hgF⟩ := hF.2 b.succ (Fin.cons v p)
  refine ⟨g, hg, fun w => ?_⟩
  simp only
  rw [Fin.cons_update]
  exact hgF w
end BlockPoly
end ReciprocityTheory.MultiplicativeHeights
