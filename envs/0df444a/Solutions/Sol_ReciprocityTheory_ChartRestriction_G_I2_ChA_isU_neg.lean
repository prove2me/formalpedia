-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.ChA.isU_neg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T13:07:36.82379+00:00
-- url     : https://prove2.me/submissions/b178b4fb-83f5-44a3-a446-6ca4139d2732

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_SplitSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GaussianTailBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_HfRsmulRight

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.I2
open NumberField Complex
noncomputable section
variable {E : Type} [Field E] [NumberField E]
open ReciprocityTheory.ChartRestriction.G.I2.ChA
namespace ReciprocityTheory.ChartRestriction.G.I2.ChA
theorem _root_.solution {dim : (E →+* ℂ) → ℕ} {I : Submodule ℤ (Vsp dim)} {x u : Vsp dim}
    (hu : IsU I x u) : IsU I (-x) (-u) :=
    ⟨neg_mem hu.1, fun a ha => by
      have hn : Hf (-x) a = -Hf x a := by simp [Hf, Finset.sum_neg_distrib]
      rw [inner_neg_left, hu.2 a ha, hn, Complex.neg_im]⟩
end ReciprocityTheory.ChartRestriction.G.I2.ChA
