-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ptsPosDens_split_ba2d8287ae82
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T14:18:32.715811+00:00
-- url     : https://prove2.me/submissions/903bb17e-2684-4065-b882-93f33e21b580

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterFib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StPtsSheetOnlyNull
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StPtsPosPartLocal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StPtsPosDensMeasurable
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PPtsPosPartProjIndep
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_fibreFinite


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
open MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G.Geo (MRing HermLine IsSmoothHerm IsArithVar IsGoodProj mcPts segre fibre IsSheet sheetDensity
  pot fibreFinite)
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)] {e : ℕ}
    {P : Ideal (MRing ι)} {Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)}
    (φ : Fin e → ((Σ k, ι k) → ℂ) → ℝ) (g : ((Σ k, ι k) → ℂ) → ℝ) (E : ℕ → Set ((Σ k, ι k) → ℂ))
    (y : Fin e → ℂ) (hfin : (fibre P Ψ y).Finite) (hE : Pairwise (Function.onFun Disjoint E))
    (hcov : ∀ w ∈ fibre P Ψ y, (∃ γ, IsSheet P Ψ y w γ) → ∀ z ∈ mcPts P, segre z = w → ∃ k, z ∈ E k) :
    ENNReal.ofReal (ptsPosDens P Ψ φ g y) =
      ∑' k, ENNReal.ofReal (ptsPosDens P Ψ φ ((E k).indicator g) y) := by
  classical
  unfold ptsPosDens
  simp only [finsum_mem_eq_finite_toFinset_sum _ hfin]
  have hT0 : ∀ (g' : ((Σ k, ι k) → ℂ) → ℝ) w, 0 ≤ max (sheetDensity P Ψ φ g' y w) 0 :=
    fun _ _ => le_max_right _ _
  have hpt : ∀ w ∈ hfin.toFinset, ENNReal.ofReal (max (sheetDensity P Ψ φ g y w) 0) =
      ∑' k, ENNReal.ofReal (max (sheetDensity P Ψ φ ((E k).indicator g) y w) 0) := by
    intro w hw
    have hw' : w ∈ fibre P Ψ y := hfin.mem_toFinset.mp hw
    by_cases hs : ∃ γ, IsSheet P Ψ y w γ
    · have hz : hs.choose y ∈ mcPts P := hs.choose_spec.2.self_of_nhds.2.1
      obtain ⟨k₀, hk₀⟩ := hcov w hw' hs _ hz hs.choose_spec.1
      rw [tsum_eq_single k₀]
      · simp only [sheetDensity, dif_pos hs, Set.indicator_of_mem hk₀]
      · intro k hk
        have hxk : hs.choose y ∉ E k := fun hxk => Set.disjoint_left.mp (hE hk) hxk hk₀
        simp [sheetDensity, dif_pos hs, Set.indicator_of_notMem hxk]
    · simp [sheetDensity, dif_neg hs]
  rw [ENNReal.ofReal_sum_of_nonneg (fun w _ => hT0 g w), Finset.sum_congr rfl hpt,
    ← Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
  exact tsum_congr fun k => (ENNReal.ofReal_sum_of_nonneg (fun w _ => hT0 _ w)).symm
end GroundTheory.Heights₂.Heights
