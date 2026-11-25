-- Prove2me | solution 1 for PositivityTheory.RgUd.T2.HaarDistr.eq_const_mul_integral_char
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:18:53.34199+00:00
-- url     : https://prove2.me/submissions/3773ff2d-4bf3-4121-b847-d0e386bac6f6

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_BernsteinUnitaryProducts_BernsteinTheoremA_FrobeniusReciprocity_SupportedInIffOfFrob
import Definitions.Def_GroundTheory_AutomorphicForms_LocallyConstantCompact
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_UnitaryDualProof_FrobeniusReciprocity_PowNear
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_UnitaryDualProof_FrobeniusReciprocity_HaarDistr
import Theorems.Thm_PositivityTheory_RgUd_T2_HaarDistr_isLocallyConstant_char
import Theorems.Thm_PositivityTheory_RgUd_T2_HaarDistr_mulLC_apply
import Theorems.Thm_PositivityTheory_RgUd_T2_HaarDistr_exists_eq_const_mul
import Theorems.Thm_PositivityTheory_RgUd_T2_HaarDistr_intLC_apply
import Theorems.Thm_PositivityTheory_RgUd_T2_HaarDistr_intLC_transl
import Theorems.Thm_PositivityTheory_RgUd_T2_HaarDistr_intLC_ind_ne_zero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] PositivityTheory.RgUd.T2.HaarDistr.mulLC_apply

set_option autoImplicit false
noncomputable section
open MeasureTheory MeasureTheory.Measure GlobalTheory.SplitWeil PositivityTheory.PfBern.Frob GroundTheory.Automorphic
open scoped Pointwise
open PositivityTheory PositivityTheory.RgUd PositivityTheory.RgUd.T2 PositivityTheory.RgUd.T2.HaarDistr
namespace PositivityTheory.RgUd.T2.HaarDistr
theorem _root_.solution :
    ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
      [LocallyCompactSpace G] [TotallyDisconnectedSpace G] [SecondCountableTopology G]
      [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure] (χ : G →* ℂˣ),
      Continuous (fun g => (χ g : ℂ)) → ∀ L : SB G →ₗ[ℂ] ℂ,
      (∀ (g : G) (α : SB G), L (transl g α) = (χ g : ℂ) * L α) →
      ∃ c : ℂ, ∀ α : SB G, L α = c * ∫ x, (α : G → ℂ) x * (χ x : ℂ) ∂μ := by
  intro G _ _ _ _ _ _ _ _ _ μ _ χ hχ L hL
  have hc : IsLocallyConstant (fun g => (χ g : ℂ)) := isLocallyConstant_char χ hχ
  have hci : IsLocallyConstant (fun g => ((χ g)⁻¹ : ℂˣ).val) := by
    have hχ' : Continuous (fun g => ((χ⁻¹ g : ℂˣ) : ℂ)) := by
      have : (fun g => ((χ⁻¹ g : ℂˣ) : ℂ)) = fun g => (χ g : ℂ)⁻¹ := by
        funext g; simp
      rw [this]
      exact hχ.inv₀ fun g => (χ g).ne_zero
    exact isLocallyConstant_char χ⁻¹ hχ'
  have hinv : ∀ x, ((χ x)⁻¹ : ℂˣ).val * (χ x : ℂ) = 1 := fun x => by simp
  let T := mulLC _ hci
  let S := mulLC _ hc
  have hTS : ∀ β : SB G, T (S β) = β := fun β => by
    apply Subtype.ext; funext x
    show ((χ x)⁻¹ : ℂˣ).val * ((χ x : ℂ) * (β : G → ℂ) x) = (β : G → ℂ) x
    rw [← mul_assoc, hinv, one_mul]
  have hM : ∀ (g : G) (α : SB G), (L ∘ₗ T) (transl g α) = (L ∘ₗ T) α := by
    intro g α
    have e : T (transl g α) = ((χ g)⁻¹ : ℂˣ).val • transl g (T α) := by
      apply Subtype.ext; funext x
      show ((χ x)⁻¹ : ℂˣ).val * (α : G → ℂ) (g⁻¹ • x) =
        ((χ g)⁻¹ : ℂˣ).val * (((χ (g⁻¹ • x))⁻¹ : ℂˣ).val * (α : G → ℂ) (g⁻¹ • x))
      have e2 : (χ x)⁻¹ = (χ g)⁻¹ * (χ (g⁻¹ • x))⁻¹ := by
        rw [smul_eq_mul, map_mul, map_inv, mul_inv, inv_inv, inv_mul_cancel_left]
      rw [e2, Units.val_mul, mul_assoc]
    simp only [LinearMap.comp_apply]
    rw [e, map_smul, hL, smul_eq_mul, ← mul_assoc, hinv g, one_mul]
  obtain ⟨c, hcM⟩ := exists_eq_const_mul (L ∘ₗ T) (intLC μ) hM (intLC_transl μ)
    (intLC_ind_ne_zero μ)
  refine ⟨c, fun α => ?_⟩
  have h1 := hcM (S α)
  rw [LinearMap.comp_apply, hTS, intLC_apply] at h1
  rw [h1]
  congr 1
  exact integral_congr_ae (Filter.Eventually.of_forall fun x => mul_comm _ _)
end PositivityTheory.RgUd.T2.HaarDistr
