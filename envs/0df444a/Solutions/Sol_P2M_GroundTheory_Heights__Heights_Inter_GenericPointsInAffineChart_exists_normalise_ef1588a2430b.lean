-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_GenericPointsInAffineChart_exists_normalise_ef1588a2430b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T14:58:36.244804+00:00
-- url     : https://prove2.me/submissions/23ce6e07-5c38-4fa4-b38a-5cae10471b54

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterBridgeB
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PtsOverChart
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ImportsMoreRest
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ImportsMoreSide
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsOrbitCompNonvanish
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_NormSegreSameOrbit
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ExistsNormalise
import Theorems.Thm_ReciprocityTheory_AnForm_M_ima_apply
import Theorems.Thm_ReciprocityTheory_AnForm_M_rea_apply
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_mcPts_smul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.AnForm.M.ima_apply
attribute [local simp] ReciprocityTheory.AnForm.M.rea_apply



set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4
open GroundTheory.Heights₂.Heights.Inter.GenericPointsInAffineChart
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {K' : Type} [Fintype K'] {ι' : K' → Type} [∀ k, Fintype (ι' k)]
omit [∀ k, Fintype (ι k)]
open Classical
namespace GroundTheory.Heights₂.Heights.Inter.GenericPointsInAffineChart
theorem _root_.solution {κ : K → K'} {v : (Σ k, ι k) → (Σ k', ι' k')} (hv : IsBlockMap κ v)
    {P' : Ideal (MRing ι')} (hP' : IsMultiHomogIdeal P') {j : ∀ k : FibreBlock κ, ι' k.1}
    {z : (Σ k, ι k) → ℂ} {c : K → ℂ} (hc : ∀ k, c k ≠ 0) {z' : (Σ k', ι' k') → ℂ} (hz' : z' ∈ mcPts P')
    (hzz : SameOrbit (fun p => z' (v p)) z) (hj : ∀ k : FibreBlock κ, z' ⟨k.1, j k⟩ ≠ 0) :
    ∃ d : K' → ℂ, (∀ k, d k ≠ 0) ∧ (fun q => d q.1 * z' q) ∈ mcPts P' ∧
      (∀ p, d (v p).1 * z' (v p) = c p.1 * z p) ∧ ∀ k : FibreBlock κ, d k.1 * z' ⟨k.1, j k⟩ = 1 := by
  obtain ⟨s, hs, hzs⟩ := hzz
  let d : K' → ℂ := fun k' =>
    if h : k' ∈ Set.range κ then c h.choose / s h.choose else (z' ⟨k', j ⟨k', h⟩⟩)⁻¹
  have hdk : ∀ k, d (κ k) = c k / s k := by
    intro k
    have h : κ k ∈ Set.range κ := ⟨k, rfl⟩
    have hk : h.choose = k := hv.1 h.choose_spec
    simp only [d, dif_pos h, hk]
  have hd : ∀ k, d k ≠ 0 := by
    intro k'
    by_cases h : k' ∈ Set.range κ
    · obtain ⟨k, rfl⟩ := h
      rw [hdk]
      exact div_ne_zero (hc k) (hs k)
    · simp only [d, dif_neg h]
      exact inv_ne_zero (hj ⟨k', h⟩)
  refine ⟨d, hd, mcPts_smul hP' d hd hz', fun p => ?_, fun k => ?_⟩
  · have h1 : z' (v p) = s p.1 * z p := congrFun hzs p
    rw [hv.2.2.1 p, hdk, h1]
    field_simp [hs p.1]
  · have h : k.1 ∉ Set.range κ := k.2
    simp only [d, dif_neg h]
    exact inv_mul_cancel₀ (hj k)
end GroundTheory.Heights₂.Heights.Inter.GenericPointsInAffineChart
