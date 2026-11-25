-- Prove2me | solution 1 for PI.ExistsGaugeMeasureForEachRank.W.lieOf_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:08:26.013838+00:00
-- url     : https://prove2.me/submissions/04a6ee61-8de5-4cfb-9bc2-1c5bf81e4d3a

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_ExistsGaugeMeasureForEachRank
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CircleGaugeAction_DglApplyOff
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CircleGaugeAction_OfRealCoordsSmulCenterCoord
import Theorems.Thm_PI_ExistsGaugeMeasureForEachRank_W_exp_dz
import Theorems.Thm_PI_ExistsGaugeMeasureForEachRank_W_dz_mem_lie
import Theorems.Thm_PI_ExistsGaugeMeasureForEachRank_W_eq_dz_of_lie
import Theorems.Thm_PI_ExistsGaugeMeasureForEachRank_W_conj_mul_iff
import Theorems.Thm_PI_ExistsGaugeMeasureForEachRank_W_dgl_norm


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Filter Topology
open PI PI.ExistsGaugeMeasureForEachRank PI.ExistsGaugeMeasureForEachRank.W
variable {r : ℕ}
namespace PI.ExistsGaugeMeasureForEachRank.W
theorem _root_.solution (X : Mat 0 r) :
    X ∈ lieOf (UWb 0 r) ↔ ∃ s : ℝ, X = dz r ((s : ℂ) * Complex.I) := by
  constructor
  · intro hX
    have hX' := eq_dz_of_lie hX
    set x := X (cI r) (cI r)
    have h1 := hX 1
    rw [hX', Complex.ofReal_one, one_smul, exp_dz] at h1
    have hn := (conj_mul_iff _).1 (dgl_norm h1)
    rw [Complex.norm_exp, Real.exp_eq_one_iff] at hn
    refine ⟨x.im, hX'.trans ?_⟩
    congr 1
    apply Complex.ext <;> simp [hn]
  · rintro ⟨s, rfl⟩
    exact dz_mem_lie s
end PI.ExistsGaugeMeasureForEachRank.W
