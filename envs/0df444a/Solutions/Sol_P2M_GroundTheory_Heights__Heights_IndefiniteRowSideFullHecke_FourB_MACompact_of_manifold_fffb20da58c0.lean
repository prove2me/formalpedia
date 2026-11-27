-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_FourB_MACompact_of_manifold_fffb20da58c0
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T05:14:37.231524+00:00
-- url     : https://prove2.me/submissions/4b40a8d9-6afb-4160-bc14-b8769901fc28

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_LocDens
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LocalDensities_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LocalDensities_LeviFormGbPotOne
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LocalDensities_OneChartAtlasIndexEq
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_FourB_MACompact_topDens_congr_a0b8135a3cf1
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_FourB_MACompact_topDens_continuousOn_f7eedd4e6ecd
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_FourB_MACompact_inclChart_symm_08c35d356223
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_FourB_MACompact_oneChartAtlas_smooth_671d5e416723
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_FourB_MACompact_oneChartAtlas_mInt_0ce76d64badf
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_FourB_MACompact_oneChartAtlas_locDens_29848ca1e7ad
import Theorems.Thm_ReciprocityTheory_AnForm_M_ima_apply
import Theorems.Thm_ReciprocityTheory_AnForm_M_isPotential_ofFun
import Theorems.Thm_ReciprocityTheory_AnForm_M_rea_apply
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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.FourB
open MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.ChartRestriction.G.Geo
open scoped ContDiff
open MACompact
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.FourB
namespace MACompact
theorem _root_.solution
    (hA : GroundTheory.Heights₂.Heights.FourB.MongeAmpereCompactChange.Statement) :
    MACompact.Statement := by
  rintro D Ω φ v ⟨hΩ, hφ, hv, hvc, hvΩ⟩
  rcases Ω.eq_empty_or_nonempty with rfl | hne
  · simp
  have : Nonempty Ω := hne.to_subtype
  set T := tsupport v with hT
  let P : LocPot Ω := LocPot.ofFun fun x => φ x / 2
  let w : Ω → ℝ := fun x => v x / 2
  let K : Set Ω := Subtype.val ⁻¹' T
  have hKc : IsCompact K := by
    rw [Subtype.isCompact_iff, Subtype.image_preimage_coe, Set.inter_eq_right.2 hvΩ]
    exact hvc
  have hwK : tsupport w ⊆ K := by
    refine closure_minimal ?_ ((isClosed_tsupport v).preimage continuous_subtype_val)
    intro x hx
    exact subset_tsupport v fun h0 => hx (by simp [w, h0])
  have hmain := hA (oneChartAtlas hΩ) P w K
    ⟨isPotential_ofFun _ _ (oneChartAtlas_smooth hΩ (hφ.div_const 2)),
      oneChartAtlas_smooth hΩ (hv.div_const 2),
      hKc.of_isClosed_subset (isClosed_tsupport w) hwK, hKc, hwK⟩
  rw [oneChartAtlas_mInt, oneChartAtlas_mInt] at hmain
  have hind : ∀ y ∈ Ω, K.indicator (1 : Ω → ℝ) ((inclChart hΩ).symm y) =
      T.indicator (1 : (Fin D → ℂ) → ℝ) y := by
    intro y hy
    have hm : (inclChart hΩ).symm y ∈ K ↔ y ∈ T := by
      show (((inclChart hΩ).symm y : Ω) : Fin D → ℂ) ∈ T ↔ y ∈ T
      rw [inclChart_symm hΩ y hy]
    by_cases h : y ∈ T
    · rw [Set.indicator_of_mem (hm.2 h), Set.indicator_of_mem h]; rfl
    · rw [Set.indicator_of_notMem (mt hm.1 h), Set.indicator_of_notMem h]
  have hL1 : Set.EqOn (fun y => K.indicator 1 ((inclChart hΩ).symm y) *
      locDens (oneChartAtlas hΩ) (fun _ => P + LocPot.ofFun w) (j0 hΩ) y)
      (T.indicator (topDens (φ + v))) Ω := by
    intro y hy
    simp only
    rw [hind y hy, oneChartAtlas_locDens hΩ _ (φ + v) (fun x x' => by
      show φ x' / 2 + v x' / 2 = (φ + v) x' / 2
      rw [Pi.add_apply, add_div]) y hy]
    by_cases h : y ∈ T <;> simp [h]
  have hL2 : Set.EqOn (fun y => K.indicator 1 ((inclChart hΩ).symm y) *
      locDens (oneChartAtlas hΩ) (fun _ => P) (j0 hΩ) y) (T.indicator (topDens φ)) Ω := by
    intro y hy
    simp only
    rw [hind y hy, oneChartAtlas_locDens hΩ _ φ (fun x x' => rfl) y hy]
    by_cases h : y ∈ T <;> simp [h]
  rw [setIntegral_congr_fun hΩ.measurableSet hL1, setIntegral_congr_fun hΩ.measurableSet hL2]
    at hmain
  have hint : ∀ ψ : (Fin D → ℂ) → ℝ, ContDiffOn ℝ ∞ ψ Ω →
      IntegrableOn (T.indicator (topDens ψ)) Ω := fun ψ hψ =>
    (((topDens_continuousOn hΩ hψ).mono hvΩ).integrableOn_compact hvc).integrable_indicator
      (isClosed_tsupport v).measurableSet |>.integrableOn
  have heq : Set.EqOn (fun z => topDens (φ + v) z - topDens φ z)
      (fun z => T.indicator (topDens (φ + v)) z - T.indicator (topDens φ) z) Ω := by
    intro z _
    by_cases hz : z ∈ T
    · simp [Set.indicator_of_mem hz]
    · simp only [Set.indicator_of_notMem hz, sub_zero, sub_eq_zero]
      exact topDens_congr ((notMem_tsupport_iff_eventuallyEq.1 hz).mono fun y hy => by
        simp only [Pi.add_apply, hy, Pi.zero_apply, add_zero])
  rw [setIntegral_congr_fun hΩ.measurableSet heq, integral_sub (hint (φ + v) (hφ.add hv)) (hint φ hφ),
    hmain, sub_self]
end MACompact
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.FourB
