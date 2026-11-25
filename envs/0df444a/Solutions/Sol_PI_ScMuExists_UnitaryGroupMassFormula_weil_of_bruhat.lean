-- Prove2me | solution 1 for PI.ScMuExists.UnitaryGroupMassFormula.weil_of_bruhat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:35:20.216686+00:00
-- url     : https://prove2.me/submissions/d4dd2583-3149-4ea2-a03a-168542c913d7

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MeasureDecomposition_InstDecomp
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MeasureDecomposition_GenericWeilRepresentation
import Theorems.Thm_PI_ScMuExists_UnitaryGroupMassFormula_exists_bruhat_left
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
open MeasureTheory
open scoped ENNReal Pointwise
noncomputable section
open PI PI.ScMuExists PI.ScMuExists.UnitaryGroupMassFormula
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [T2Space G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
namespace PI.ScMuExists.UnitaryGroupMassFormula
theorem _root_.solution (μG μS : Measure G) [SFinite μG] [μG.IsMulLeftInvariant] [SFinite μS]
    (S : Set G) (_hS : MeasurableSet S) (hSc : μS Sᶜ = 0)
    (hinv : ∀ t ∈ S, μS.map (fun x => t * x) = μS)
    (hpos : ∀ U : Set G, IsOpen U → (1 : G) ∈ U → 0 < μS U)
    (hfin : ∀ K : Set G, IsCompact K → μS K < ⊤) :
    ∃ ν : Measure G, ∀ f : G → ℝ≥0∞, Measurable f →
      ∫⁻ x, f x ∂μG = ∫⁻ x, (∫⁻ s, f (s * x) ∂μS) ∂ν := by
  obtain ⟨β, hβm, hβ⟩ := exists_bruhat_left μS S hSc hinv hpos hfin
  refine ⟨μG.withDensity β, fun f hf => ?_⟩
  have hF : Measurable (fun x : G => ∫⁻ s, f (s * x) ∂μS) :=
    (hf.comp (measurable_snd.mul measurable_fst)).lintegral_prod_right'
  rw [lintegral_withDensity_eq_lintegral_mul _ hβm hF]
  calc ∫⁻ x, f x ∂μG = ∫⁻ x, (∫⁻ s, β (s⁻¹ * x) ∂μS) * f x ∂μG := by
        simp only [hβ, one_mul]
    _ = ∫⁻ x, ∫⁻ s, β (s⁻¹ * x) * f x ∂μS ∂μG := by
        refine lintegral_congr fun x => ?_
        exact (lintegral_mul_const _ (hβm.comp (measurable_inv.mul_const x))).symm
    _ = ∫⁻ s, ∫⁻ x, β (s⁻¹ * x) * f x ∂μG ∂μS :=
        lintegral_lintegral_swap ((hβm.comp (measurable_snd.inv.mul measurable_fst)).mul
          (hf.comp measurable_fst)).aemeasurable
    _ = ∫⁻ s, ∫⁻ x, β x * f (s * x) ∂μG ∂μS := by
        refine lintegral_congr fun s => ?_
        simpa only [inv_mul_cancel_left] using
          (lintegral_mul_left_eq_self (fun x => β (s⁻¹ * x) * f x) s).symm
    _ = ∫⁻ x, ∫⁻ s, β x * f (s * x) ∂μS ∂μG :=
        lintegral_lintegral_swap ((hβm.comp measurable_snd).mul
          (hf.comp (measurable_fst.mul measurable_snd))).aemeasurable
    _ = ∫⁻ x, (β * fun x => ∫⁻ s, f (s * x) ∂μS) x ∂μG := by
        refine lintegral_congr fun x => ?_
        exact lintegral_const_mul _ (hf.comp (measurable_id.mul_const x))
end PI.ScMuExists.UnitaryGroupMassFormula
