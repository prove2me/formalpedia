-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_PtsIntegralProjIndep_proof_944cefc4c00d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T05:14:21.605112+00:00
-- url     : https://prove2.me/submissions/ab01b5d8-c32a-4bf1-863b-12b5132f78e8

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterFib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterSheet
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StPtsIntegralProjIndep
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StPtsPosPartProjIndep
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StPtsPosDensIntegrable
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PPtsIntegralProjIndep
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_sheetDensity_neg_9667c0f480de
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_sheetDensity_congr_5e999200a44f
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_fibreFinite
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_isOpen_blockNonzero


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MeasureTheory Filter
open ReciprocityTheory.ChartRestriction.G.Geo (MRing HermLine IsSmoothHerm IsArithVar IsGoodProj IsSheet ptsIntegralAt sheetDensity
  fibre pot mcPts fibreFinite isOpen_blockNonzero)
namespace GroundTheory.Heights₂.Heights
namespace PtsIntegralProjIndep
theorem _root_.solution (hInt : PtsPosDensIntegrable.Statement)
    (hPos : PtsPosPartProjIndep.Statement) : PtsIntegralProjIndep.Statement := by
  intro K _ ι _ P e Ψ Ψ' L g hP hΨ hΨ' hL hg
  classical
  set S : Set ((Σ k, ι k) → ℂ) := {z | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} with hSdef
  set g₀ : ((Σ k, ι k) → ℂ) → ℝ := S.piecewise g 0 with hg₀def
  have hg₀m : Measurable g₀ :=
    hg.1.continuousOn.measurable_piecewise continuousOn_const isOpen_blockNonzero.measurableSet
  have hg₀inv : ∀ (c : K → ℂ) (z : (Σ k, ι k) → ℂ), (∀ k, c k ≠ 0) →
      g₀ (fun p => c p.1 * z p) = g₀ z := by
    intro c z hc
    have hmem : (fun p : Σ k, ι k => c p.1 * z p) ∈ S ↔ z ∈ S := by
      simp only [hSdef, Set.mem_ofPred_eq, ne_eq, mul_eq_zero, hc, false_or]
    by_cases hz : z ∈ S
    · rw [hg₀def, Set.piecewise_eq_of_mem _ _ _ hz, Set.piecewise_eq_of_mem _ _ _ (hmem.2 hz), hg.2 c z hc]
    · rw [hg₀def, Set.piecewise_eq_of_notMem _ _ _ hz, Set.piecewise_eq_of_notMem _ _ _ (mt hmem.1 hz)]
      rfl
  have hag : ∀ z ∈ mcPts P, g z = g₀ z := fun z hz =>
    (Set.piecewise_eq_of_mem S _ _ (show z ∈ S from hz.1)).symm
  have hagn : ∀ z ∈ mcPts P, -g z = -g₀ z := fun z hz => by rw [hag z hz]
  have hneg : IsDegZeroSmooth (fun z => -g z) :=
    ⟨hg.1.neg, fun c z hc => by simp only [hg.2 c z hc]⟩
  have hnn : ∀ (Ψ₀ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) (u : ((Σ k, ι k) → ℂ) → ℝ) y,
      0 ≤ ptsPosDens P Ψ₀ (pot L) u y := fun Ψ₀ u y =>
    finsum_nonneg fun w => finsum_nonneg fun _ => le_max_right _ _

  have key : ∀ Ψ₀ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ), IsGoodProj P Ψ₀ →
      ptsIntegralAt P Ψ₀ (pot L) g =
        (∫⁻ y, ENNReal.ofReal (ptsPosDens P Ψ₀ (pot L) g₀ y)).toReal -
          (∫⁻ y, ENNReal.ofReal (ptsPosDens P Ψ₀ (pot L) (fun z => -g₀ z) y)).toReal := by
    intro Ψ₀ h₀
    have hp := hInt K ι P e Ψ₀ L g hP h₀ hL hg
    have hn := hInt K ι P e Ψ₀ L (fun z => -g z) hP h₀ hL hneg
    have e₁ : ptsPosDens P Ψ₀ (pot L) g₀ = ptsPosDens P Ψ₀ (pot L) g := by
      funext y
      simp only [ptsPosDens, sheetDensity_congr (Ψ := Ψ₀) (φ := pot L) hag]
    have e₂ : ptsPosDens P Ψ₀ (pot L) (fun z => -g₀ z) = ptsPosDens P Ψ₀ (pot L) (fun z => -g z) := by
      funext y
      simp only [ptsPosDens, sheetDensity_congr (Ψ := Ψ₀) (φ := pot L) hagn]
    have hsplit : ∀ y, (∑ᶠ w ∈ fibre P Ψ₀ y, sheetDensity P Ψ₀ (pot L) g y w) =
        ptsPosDens P Ψ₀ (pot L) g y - ptsPosDens P Ψ₀ (pot L) (fun z => -g z) y := by
      intro y
      have hF := fibreFinite K ι P e Ψ₀ hP h₀ y
      simp only [ptsPosDens, finsum_mem_eq_finite_toFinset_sum _ hF, sheetDensity_neg,
        ← Finset.sum_sub_distrib, max_zero_sub_max_neg_zero_eq_self]
    unfold ptsIntegralAt
    simp only [hsplit]
    rw [integral_sub hp hn, integral_eq_lintegral_of_nonneg_ae (ae_of_all _ (hnn Ψ₀ g)) hp.1,
      integral_eq_lintegral_of_nonneg_ae (ae_of_all _ (hnn Ψ₀ _)) hn.1, e₁, e₂]
  rw [key Ψ hΨ, key Ψ' hΨ', hPos K ι P e Ψ Ψ' L g₀ hP hΨ hΨ' hL hg₀m hg₀inv,
    hPos K ι P e Ψ Ψ' L (fun z => -g₀ z) hP hΨ hΨ' hL hg₀m.neg fun c z hc => by simp only [hg₀inv c z hc]]
end PtsIntegralProjIndep
end GroundTheory.Heights₂.Heights
