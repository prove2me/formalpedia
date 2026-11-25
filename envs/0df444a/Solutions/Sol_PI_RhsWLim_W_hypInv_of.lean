-- Prove2me | solution 1 for PI.RhsWLim.W.hypInv_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:56:02.288118+00:00
-- url     : https://prove2.me/submissions/5d70a09a-4103-42d2-897a-7211ad4735aa

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_RhsWLim
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_VolumeLieE
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_MBaseMem
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_RhsTest
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_OrbitPushCut
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_OrbitPushI
import Theorems.Thm_PI_RhsWLim_W_blkAct_mul
import Theorems.Thm_PI_RhsWLim_W_blkAct_one
import Theorems.Thm_PI_RhsWLim_W_blkAct_smul
import Theorems.Thm_PI_RhsWLim_W_continuous_blkAct
import Theorems.Thm_PI_RhsWLim_W_hb_inv_mul
import Theorems.Thm_PI_RhsWLim_W_qf_blkAct
import Theorems.Thm_PI_RhsWLim_W_hypS_iff
import Theorems.Thm_PI_RhsWLim_W_opAct_uwb

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option linter.unusedVariables false
noncomputable section
open MeasureTheory Filter Topology Matrix
open scoped ENNReal
open PI PI.RhsWLim PI.RhsWLim.W
open PI.RhsWLim PI.RhsWLim.W.MB
variable {k r : ℕ}
namespace PI.RhsWLim.W
theorem _root_.solution (hL : LebInvB) (hC : ConeForm) : HypInv := by
  intro k r T' hk hT' s hs
  obtain ⟨μ, hμ, hse⟩ := opAct_uwb hs
  rw [hse]
  set ν := Hb k * μᴴ * Hb k with hν
  have hνμ : ν * μ = 1 := hb_inv_mul hμ
  have hμν : μ * ν = 1 := mul_eq_one_comm.1 hνμ
  let e : ((Fin k → ℂ) × ℂ) ≃ᵐ ((Fin k → ℂ) × ℂ) :=
    { toFun := blkAct k μ
      invFun := blkAct k ν
      left_inv := fun p => by simp only [blkAct_mul, hνμ, blkAct_one]
      right_inv := fun p => by simp only [blkAct_mul, hμν, blkAct_one]
      measurable_toFun := (continuous_blkAct μ).measurable
      measurable_invFun := (continuous_blkAct ν).measurable }
  obtain ⟨κ, -, -, hκ⟩ := hC k T' hT'
  have hset : ∀ E, coneSh k T' (blkAct k μ ⁻¹' E) = blkAct k μ ⁻¹' coneSh k T' E := by
    intro E
    ext x
    constructor
    · rintro ⟨⟨v, t⟩, ⟨⟨hvE, hvS⟩, ht⟩, rfl⟩
      refine ⟨(blkAct k μ v, t), ⟨⟨hvE, ?_⟩, ht⟩, ?_⟩
      · rw [hypS_iff, qf_blkAct hμ]; exact hvS
      · exact (blkAct_smul μ t v).symm
    · rintro ⟨⟨w, t⟩, ⟨⟨hwE, hwS⟩, ht⟩, hx⟩
      have hw : blkAct k μ (blkAct k ν w) = w := by rw [blkAct_mul, hμν, blkAct_one]
      refine ⟨(blkAct k ν w, t), ⟨⟨?_, ?_⟩, ht⟩, ?_⟩
      · show blkAct k μ (blkAct k ν w) ∈ E
        rw [hw]; exact hwE
      · rw [hypS_iff, ← qf_blkAct hμ, hw]; exact hwS
      · have h1 : blkAct k μ (t • blkAct k ν w) = blkAct k μ x := by
          rw [blkAct_smul, hw]; exact hx
        have h2 := congrArg (blkAct k ν) h1
        simp only [blkAct_mul, hνμ, blkAct_one] at h2
        exact h2
  ext E hE
  rw [Measure.map_apply (continuous_blkAct μ).measurable hE,
    hκ _ ((continuous_blkAct μ).measurable hE), hκ _ hE, hset]
  congr 1
  have := MeasurableEquiv.map_apply e (μ := (volume : Measure ((Fin k → ℂ) × ℂ))) (coneSh k T' E)
  have hmap : (volume : Measure ((Fin k → ℂ) × ℂ)).map e = volume := hL k μ hμ
  rw [hmap] at this
  exact this.symm
end PI.RhsWLim.W
