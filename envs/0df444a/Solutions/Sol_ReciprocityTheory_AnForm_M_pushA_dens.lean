-- Prove2me | solution 1 for ReciprocityTheory.AnForm.M.pushA_dens
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T13:09:01.452649+00:00
-- url     : https://prove2.me/submissions/4379331f-74e0-47ef-962f-f870d2381a89

import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_IsPotentialPullbackStatement
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_AnalyticSubsetChartLocal
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_LocDens
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_Partition
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_LintegralImageEqLintegralNormSqDetMul
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_PushAFinsumInter
import Theorems.Thm_ReciprocityTheory_AnForm_M_pushA_analytic
import Theorems.Thm_ReciprocityTheory_AnForm_M_pushA_det_comp
import Theorems.Thm_ReciprocityTheory_AnForm_M_locDensChart


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open MeasureTheory FinHolAtlas Filter Topology
noncomputable section
variable {e : ℕ} {X : Type} [TopologicalSpace X]
namespace ReciprocityTheory.AnForm.M
theorem _root_.solution (A : FinHolAtlas e X) (Φ : Fin e → LocPot X) (hΦ : ∀ i, IsPotential A (Φ i))
    {Q : Set X} {q : X → Fin e → ℂ} (hq : ∀ i, A.HoloOn Q (fun x => q x i))
    (j : Fin A.n) {z : Fin e → ℂ} (hz : z ∈ (A.chart j).target) (hzQ : (A.chart j).symm z ∈ Q)
    (hdet : LinearMap.det (fderiv ℂ (q ∘ (A.chart (chartIdx A ((A.chart j).symm z))).symm)
        (A.chart (chartIdx A ((A.chart j).symm z)) ((A.chart j).symm z)) :
        (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ)) ≠ 0) :
    Complex.normSq (LinearMap.det (fderiv ℂ (q ∘ (A.chart j).symm) z :
        (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ))) * pushDens A Φ q ((A.chart j).symm z) =
      locDens A Φ j z := by
  have hxc : (A.chart j).symm z ∈ (A.chart (chartIdx A ((A.chart j).symm z))).source :=
    Classical.choose_spec (A.cover ((A.chart j).symm z))
  have hch := locDensChart A Φ hΦ j (chartIdx A ((A.chart j).symm z)) z hz hxc
  have hτ : AnalyticAt ℂ (A.chart (chartIdx A ((A.chart j).symm z)) ∘ (A.chart j).symm) z :=
    A.holo j _ z ⟨hz, hxc⟩
  have hqc : AnalyticAt ℂ (q ∘ (A.chart (chartIdx A ((A.chart j).symm z))).symm)
      ((A.chart (chartIdx A ((A.chart j).symm z)) ∘ (A.chart j).symm) z) := by
    apply pushA_analytic A hq
    · exact (A.chart _).map_source hxc
    · simpa [(A.chart _).left_inv hxc] using hzQ
  have heq : q ∘ (A.chart j).symm =ᶠ[𝓝 z] (q ∘ (A.chart (chartIdx A ((A.chart j).symm z))).symm) ∘
      (A.chart (chartIdx A ((A.chart j).symm z)) ∘ (A.chart j).symm) := by
    have hmem : (A.chart j).target ∩ (A.chart j).symm ⁻¹'
        (A.chart (chartIdx A ((A.chart j).symm z))).source ∈ 𝓝 z :=
      ((A.chart j).isOpen_inter_preimage_symm (A.chart _).open_source).mem_nhds ⟨hz, hxc⟩
    filter_upwards [hmem] with w hw
    simp [(A.chart _).left_inv hw.2]
  have hfd := heq.fderiv_eq (𝕜 := ℂ)
  rw [fderiv_comp z hqc.differentiableAt hτ.differentiableAt] at hfd
  rw [hfd, hch, pushDens, pushA_det_comp, map_mul,
    Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq]
  have ha := norm_ne_zero_iff.2 hdet
  simp only [Function.comp_apply] at ha ⊢
  field_simp
end ReciprocityTheory.AnForm.M
