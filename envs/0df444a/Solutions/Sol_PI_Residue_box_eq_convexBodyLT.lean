-- Prove2me | solution 1 for PI.Residue.box_eq_convexBodyLT
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:13:16.295174+00:00
-- url     : https://prove2.me/submissions/e0af13fd-5e8e-426c-809a-0637a6a1d795

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ResidueLatticeCount_UnitPreserving
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ResidueLatticeCount_BoxEqConvexBodyLT

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField NumberField.mixedEmbedding NumberField.InfinitePlace MeasureTheory
open scoped ENNReal Classical
noncomputable section
open PI PI.Residue
namespace PI.Residue
theorem _root_.solution (K : Type) [Field K] [NumberField K] (r : InfinitePlace K → ℝ)
    (hr : ∀ w, 0 < r w) : box K r = convexBodyLT K (fun w => (r w).toNNReal) := by
  ext y
  simp only [box, Set.mem_ofPred_eq, Set.mem_prod, Set.mem_pi, Set.mem_univ, forall_true_left,
    mem_ball_zero_iff, Subtype.forall, Real.coe_toNNReal _ (hr _).le]
  constructor
  · intro h
    refine ⟨fun w hw => ?_, fun w hw => ?_⟩
    · simpa [normAtPlace_apply_of_isReal hw] using h w
    · simpa [normAtPlace_apply_of_isComplex hw] using h w
  · rintro ⟨h1, h2⟩ w
    rcases isReal_or_isComplex w with hw | hw
    · rw [normAtPlace_apply_of_isReal hw]; exact h1 w hw
    · rw [normAtPlace_apply_of_isComplex hw]; exact h2 w hw
end PI.Residue
