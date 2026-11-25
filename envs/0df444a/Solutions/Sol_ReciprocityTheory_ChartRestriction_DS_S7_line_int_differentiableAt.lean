-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.S7.line_int_differentiableAt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:45:42.639955+00:00
-- url     : https://prove2.me/submissions/e685873a-2b75-4063-bb91-18d794dee394

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_IsClosedKset
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_PhiCasA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_KFacts
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_IdThmA
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_IdA_continuous_toMK
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_IdA_continuous_toMK_inv
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_IdA_continuous_P
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_IdA_continuous_cline
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_IdA_hasDerivAt_cline
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_IdA_hasDerivAt_intK
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_IdA_contDiffAt_dPhi2
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_IdA_continuousOn_dPhi2
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_IdA_continuousOn_fderiv_dPhi2
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_compactSpace_KG


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset MeasureTheory Matrix
open scoped ComplexOrder ContDiff ENNReal
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7
open ReciprocityTheory.ChartRestriction.DS
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ} {ε : Fin n → Bool} {Λ : Fin n → ℝ}
namespace ReciprocityTheory.ChartRestriction.DS.S7
theorem _root_.solution (T : KType ε Λ) (μ : Fin n → ℤ) {U : Set (Matrix (Fin n) (Fin n) ℂ)}
    (hUo : IsOpen U) (hU : ∀ z ∈ U, ∀ k : KG ε, toMK k⁻¹ * z * toMK k ∈ OmegaSet n)
    (a₀ a₁ b₀ b₁ : Matrix (Fin n) (Fin n) ℂ) {s₀ : ℂ} (hs₀ : a₀ + s₀ • a₁ ∈ U) :
    DifferentiableAt ℂ (fun s : ℂ => ∫ k, IdA.dPhi2 μ (toMK k⁻¹ * (a₀ + s • a₁) * toMK k,
      toMK k⁻¹ * (b₀ + s • b₁) * toMK k) • (T.op k * projW T * T.op k⁻¹) ∂(muK ε)) s₀ := by
  have := compactSpace_KG ε
  have hS : IsOpen ((fun s : ℂ => a₀ + s • a₁) ⁻¹' U) :=
    hUo.preimage (continuous_const.add (continuous_id.smul continuous_const))
  have hγ : Continuous fun p : ℂ × KG ε =>
      (toMK p.2⁻¹ * (a₀ + p.1 • a₁) * toMK p.2, toMK p.2⁻¹ * (b₀ + p.1 • b₁) * toMK p.2) :=
    (IdA.continuous_cline a₀ a₁).prodMk (IdA.continuous_cline b₀ b₁)
  have hmaps : Set.MapsTo (fun p : ℂ × KG ε =>
      (toMK p.2⁻¹ * (a₀ + p.1 • a₁) * toMK p.2, toMK p.2⁻¹ * (b₀ + p.1 • b₁) * toMK p.2))
      (((fun s : ℂ => a₀ + s • a₁) ⁻¹' U) ×ˢ Set.univ) (OmegaSet n ×ˢ Set.univ) :=
    fun p hp => ⟨hU _ hp.1 p.2, trivial⟩
  have hP : ContinuousOn (fun p : ℂ × KG ε => T.op p.2 * projW T * T.op p.2⁻¹)
      (((fun s : ℂ => a₀ + s • a₁) ⁻¹' U) ×ˢ Set.univ) :=
    ((IdA.continuous_P T).comp continuous_snd).continuousOn
  have hd1 : Continuous fun p : ℂ × KG ε => (toMK p.2⁻¹ * a₁ * toMK p.2, toMK p.2⁻¹ * b₁ * toMK p.2) :=
    (((IdA.continuous_toMK_inv.comp continuous_snd).matrix_mul continuous_const).matrix_mul
      (IdA.continuous_toMK.comp continuous_snd)).prodMk
    (((IdA.continuous_toMK_inv.comp continuous_snd).matrix_mul continuous_const).matrix_mul
      (IdA.continuous_toMK.comp continuous_snd))
  have hF : ContinuousOn (fun p : ℂ × KG ε => IdA.dPhi2 μ (toMK p.2⁻¹ * (a₀ + p.1 • a₁) * toMK p.2,
      toMK p.2⁻¹ * (b₀ + p.1 • b₁) * toMK p.2) • (T.op p.2 * projW T * T.op p.2⁻¹))
      (((fun s : ℂ => a₀ + s • a₁) ⁻¹' U) ×ˢ Set.univ) :=
    ((IdA.continuousOn_dPhi2 μ).comp hγ.continuousOn hmaps).smul hP
  have hF' : ContinuousOn (fun p : ℂ × KG ε => fderiv ℂ (IdA.dPhi2 μ)
      (toMK p.2⁻¹ * (a₀ + p.1 • a₁) * toMK p.2, toMK p.2⁻¹ * (b₀ + p.1 • b₁) * toMK p.2)
      (toMK p.2⁻¹ * a₁ * toMK p.2, toMK p.2⁻¹ * b₁ * toMK p.2) • (T.op p.2 * projW T * T.op p.2⁻¹))
      (((fun s : ℂ => a₀ + s • a₁) ⁻¹' U) ×ˢ Set.univ) :=
    (((IdA.continuousOn_fderiv_dPhi2 μ).comp hγ.continuousOn hmaps).clm_apply hd1.continuousOn).smul hP
  have hd : ∀ s ∈ (fun s : ℂ => a₀ + s • a₁) ⁻¹' U, ∀ k : KG ε, HasDerivAt
      (fun s => IdA.dPhi2 μ (toMK k⁻¹ * (a₀ + s • a₁) * toMK k, toMK k⁻¹ * (b₀ + s • b₁) * toMK k) •
        (T.op k * projW T * T.op k⁻¹))
      (fderiv ℂ (IdA.dPhi2 μ) (toMK k⁻¹ * (a₀ + s • a₁) * toMK k, toMK k⁻¹ * (b₀ + s • b₁) * toMK k)
        (toMK k⁻¹ * a₁ * toMK k, toMK k⁻¹ * b₁ * toMK k) • (T.op k * projW T * T.op k⁻¹)) s := by
    intro s hs k
    have hq := (IdA.hasDerivAt_cline k a₀ a₁ s).prodMk (IdA.hasDerivAt_cline k b₀ b₁ s)
    have hD := ((IdA.contDiffAt_dPhi2 μ (p := (toMK k⁻¹ * (a₀ + s • a₁) * toMK k,
      toMK k⁻¹ * (b₀ + s • b₁) * toMK k)) (hU _ hs k)).differentiableAt one_ne_zero).hasFDerivAt
    exact (hD.comp_hasDerivAt s hq).smul_const (T.op k * projW T * T.op k⁻¹)
  exact (IdA.hasDerivAt_intK T _ _ hS hF hF' hd hs₀).differentiableAt
end ReciprocityTheory.ChartRestriction.DS.S7
