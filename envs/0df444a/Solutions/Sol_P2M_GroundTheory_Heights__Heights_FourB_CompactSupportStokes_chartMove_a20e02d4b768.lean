-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FourB_CompactSupportStokes_chartMove_a20e02d4b768
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T13:02:56.879805+00:00
-- url     : https://prove2.me/submissions/b29223cf-599b-419a-b127-8e37cc6d9ef2

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_Stokes
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LocalDensities_CompactSupportStokes
import Theorems.Thm_ReciprocityTheory_AnForm_A_det_jacC
import Theorems.Thm_ReciprocityTheory_AnForm_A_integral_image_eq_integral_normSq_det_smul
import Theorems.Thm_ReciprocityTheory_AnForm_M_locDensChart


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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FourB GroundTheory.Heights₂.Heights.FourB.CompactSupportStokes
open MeasureTheory Filter Topology Set ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M FinHolAtlas
open scoped ContDiff Manifold
variable {e : ℕ} {X : Type} [TopologicalSpace X]
namespace GroundTheory.Heights₂.Heights.FourB.CompactSupportStokes
theorem _root_.solution (A : FinHolAtlas e X) (χ : ChartPartition A) (Φ : Fin e → LocPot X)
    (hΦ : ∀ i, IsPotential A (Φ i)) (j k : Fin A.n) (g : X → ℝ)
    (hs : ∀ y ∈ (A.chart k).target, (A.chart k).symm y ∉ (A.chart j).source →
      g ((A.chart k).symm y) * locDens A Φ k y = 0) :
    ∫ y in (A.chart k).target,
        χ.χ k ((A.chart k).symm y) * g ((A.chart k).symm y) * locDens A Φ k y =
      ∫ y in (A.chart j).target,
        χ.χ k ((A.chart j).symm y) * g ((A.chart j).symm y) * locDens A Φ j y := by
  have hU : IsOpen ((A.chart k).target ∩ (A.chart k).symm ⁻¹' (A.chart j).source) :=
    (A.chart k).continuousOn_symm.isOpen_inter_preimage (A.chart k).open_target
      (A.chart j).open_source
  have hτ : AnalyticOnNhd ℂ (A.chart j ∘ (A.chart k).symm)
      ((A.chart k).target ∩ (A.chart k).symm ⁻¹' (A.chart j).source) := A.holo k j
  have hinj : Set.InjOn (A.chart j ∘ (A.chart k).symm)
      ((A.chart k).target ∩ (A.chart k).symm ⁻¹' (A.chart j).source) := by
    intro a ha b hb hab
    exact (A.chart k).symm.injOn ha.1 hb.1 ((A.chart j).injOn ha.2 hb.2 hab)
  have himg : (A.chart j ∘ (A.chart k).symm) ''
      ((A.chart k).target ∩ (A.chart k).symm ⁻¹' (A.chart j).source) ⊆ (A.chart j).target := by
    rintro _ ⟨z, hz, rfl⟩; exact (A.chart j).map_source hz.2
  have hin : ∀ w ∈ (A.chart j).target, (A.chart j).symm w ∈ (A.chart k).source →
      w ∈ (A.chart j ∘ (A.chart k).symm) ''
        ((A.chart k).target ∩ (A.chart k).symm ⁻¹' (A.chart j).source) := by
    intro w hw h2
    refine ⟨A.chart k ((A.chart j).symm w), ⟨(A.chart k).map_source h2, ?_⟩, ?_⟩
    · show (A.chart k).symm (A.chart k ((A.chart j).symm w)) ∈ (A.chart j).source
      rw [(A.chart k).left_inv h2]; exact (A.chart j).map_target hw
    · show A.chart j ((A.chart k).symm (A.chart k ((A.chart j).symm w))) = w
      rw [(A.chart k).left_inv h2, (A.chart j).right_inv hw]
  rw [setIntegral_eq_of_subset_of_forall_sdiff_eq_zero (A.chart k).open_target.measurableSet
      Set.inter_subset_left ?z1,
    setIntegral_eq_of_subset_of_forall_sdiff_eq_zero (A.chart j).open_target.measurableSet
      himg ?z2,
    ReciprocityTheory.AnForm.A.integral_image_eq_integral_normSq_det_smul _ _ hU hτ hinj]
  · refine setIntegral_congr_fun hU.measurableSet (fun z hz => ?_)
    have hz2 : (A.chart k).symm z ∈ (A.chart j).source := hz.2
    simp only [Function.comp_apply, smul_eq_mul, (A.chart j).left_inv hz2]
    rw [ReciprocityTheory.AnForm.A.det_jacC, Complex.normSq_eq_norm_sq,
      locDensChart A Φ hΦ k j z hz.1 hz2]
    ring
  case z1 =>
    rintro y ⟨hy, hyU⟩
    have h1 : (A.chart k).symm y ∉ (A.chart j).source := fun h => hyU ⟨hy, h⟩
    rw [mul_assoc, hs y hy h1, mul_zero]
  case z2 =>
    rintro w ⟨hw, hwU⟩
    have h1 : (A.chart j).symm w ∉ (A.chart k).source := fun h => hwU (hin w hw h)
    have h2 : (A.chart j).symm w ∉ tsupport (χ.χ k) := fun h => h1 (χ.tsupport_subset k h)
    simp only [image_eq_zero_of_notMem_tsupport h2, zero_mul]
end GroundTheory.Heights₂.Heights.FourB.CompactSupportStokes
