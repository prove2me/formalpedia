-- Prove2me | solution 1 for PositivityTheory.ThK.LinAct.eventually_fix
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T11:57:39.236312+00:00
-- url     : https://prove2.me/submissions/b43bf3fa-343b-4c77-9d3a-9f90718a08f4

import Definitions.Def_Development_WeilBound_CoreStatements_LocalThetaKernels_EvlLoc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsLocallyConstantAddChar
import Definitions.Def_Development_WeilBound_CoreStatements_CompactAveragingSplitting_EigenvectorLifting_LinearActInt
import Theorems.Thm_GlobalTheory_WeilM_isLocallyConstant_addChar
import Theorems.Thm_GlobalTheory_WeilM_nonarch_field


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix GlobalTheory.WeilM MeasureTheory ValuativeRel Topology Filter PositivityTheory.ThKH.Evl
open PositivityTheory PositivityTheory.ThK PositivityTheory.ThK.LinAct
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [Invertible (2 : k)]
  {κ ι : Type} [Fintype κ] [Fintype ι] {ψ : AddChar k ℂ}
namespace PositivityTheory.ThK.LinAct
theorem _root_.solution (hc : Continuous ψ) {φ : (κ → k) → ℂ} (hφ : φ ∈ SB (κ → k)) :
    ∀ᶠ w in 𝓝 (0 : (κ → k) × (κ → k)), schr ψ w φ = φ := by
  have := nonarch_field k
  have hlc := isLocallyConstant_addChar ψ hc
  have h1 : IsLocallyConstant fun z : ((κ → k) × (κ → k)) × (κ → k) => schr ψ z.1 φ z.2 - φ z.2 := by
    refine IsLocallyConstant.sub (IsLocallyConstant.mul ?_ ?_) (hφ.1.comp_continuous continuous_snd)
    · exact hlc.comp_continuous ((continuous_snd.dotProduct continuous_fst.snd).add
        (continuous_const.mul (continuous_fst.fst.dotProduct continuous_fst.snd)))
    · exact hφ.1.comp_continuous (continuous_snd.add continuous_fst.fst)
  have h2 : IsLocallyConstant fun z : ((κ → k) × (κ → k)) × (κ → k) => φ (z.2 - z.1.1) - φ z.2 :=
    (hφ.1.comp_continuous (continuous_snd.sub continuous_fst.fst)).sub (hφ.1.comp_continuous continuous_snd)
  have hK : IsCompact (tsupport φ) := hφ.2
  have e1 := hK.eventually_forall_of_forall_eventually (x₀ := (0 : (κ → k) × (κ → k)))
    (P := fun w x => schr ψ w φ x - φ x = 0) fun y _ => by
      simpa [schr] using h1.eventually_eq (0, y)
  have e2 := hK.eventually_forall_of_forall_eventually (x₀ := (0 : (κ → k) × (κ → k)))
    (P := fun w x => φ (x - w.1) - φ x = 0) fun y _ => by
      simpa using h2.eventually_eq (0, y)
  filter_upwards [e1, e2] with w a1 a2
  funext x
  by_cases hx : x ∈ tsupport φ
  · exact sub_eq_zero.1 (a1 x hx)
  have h0 : φ x = 0 := image_eq_zero_of_notMem_tsupport hx
  have h3 : φ (x + w.1) = 0 := by
    by_cases hy : x + w.1 ∈ tsupport φ
    · have := a2 _ hy
      rw [add_sub_cancel_right, h0, zero_sub, neg_eq_zero] at this
      exact this
    · exact image_eq_zero_of_notMem_tsupport hy
  rw [schr, h3, h0, mul_zero]
end PositivityTheory.ThK.LinAct
