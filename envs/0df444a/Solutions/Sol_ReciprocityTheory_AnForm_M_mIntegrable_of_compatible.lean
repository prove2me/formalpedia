-- Prove2me | solution 1 for ReciprocityTheory.AnForm.M.mIntegrable_of_compatible
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T13:08:49.635496+00:00
-- url     : https://prove2.me/submissions/e6174a4d-609c-46b0-a327-63c1e140d90a

import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_IsPotentialPullbackStatement
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_LocDens
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_IntegrableOnTargetOfTsupport
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_Partition
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_AtlasIndep
import Theorems.Thm_ReciprocityTheory_AnForm_M_isPotential_of_compatible
import Theorems.Thm_ReciprocityTheory_AnForm_M_locDens_unionAtlas_castAdd
import Theorems.Thm_ReciprocityTheory_AnForm_M_locDens_unionAtlas_natAdd
import Theorems.Thm_ReciprocityTheory_AnForm_A_det_jacC
import Theorems.Thm_ReciprocityTheory_AnForm_A_integrableOn_image_iff_analytic
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
open scoped ContDiff
noncomputable section
variable {e : ℕ} {X : Type} [TopologicalSpace X]
namespace ReciprocityTheory.AnForm.M
theorem _root_.solution {A B : FinHolAtlas e X} (h : A.Compatible B)
    (Φ : Fin e → LocPot X) (hΦ : ∀ i, IsPotential A (Φ i)) {g : X → ℝ}
    (hg : MIntegrable A Φ g) : MIntegrable B Φ g := by
  have hΦU : ∀ i, IsPotential (unionAtlas A B h) (Φ i) := fun i =>
    isPotential_of_compatible (compatible_unionAtlas_left A B h) (hΦ i)
  intro k K hK hKc
  refine LocallyIntegrableOn.integrableOn_isCompact (fun y hyK => ?_) hKc
  have hy : y ∈ (B.chart k).target := hK hyK
  obtain ⟨j, hj⟩ := A.cover ((B.chart k).symm y)

  have hVo : IsOpen ((B.chart k).target ∩ (B.chart k).symm ⁻¹' (A.chart j).source) :=
    (B.chart k).isOpen_inter_preimage_symm (A.chart j).open_source
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 hVo y ⟨hy, hj⟩
  have hsub : Metric.closedBall y (r / 2) ⊆
      (B.chart k).target ∩ (B.chart k).symm ⁻¹' (A.chart j).source :=
    (Metric.closedBall_subset_ball (half_lt_self hr)).trans hball
  have hbV : Metric.ball y (r / 2) ⊆
      (B.chart k).target ∩ (B.chart k).symm ⁻¹' (A.chart j).source :=
    Metric.ball_subset_closedBall.trans hsub

  have hτa : AnalyticOnNhd ℂ (A.chart j ∘ (B.chart k).symm)
      ((B.chart k).target ∩ (B.chart k).symm ⁻¹' (A.chart j).source) := h.2 k j
  have hinj : Set.InjOn (A.chart j ∘ (B.chart k).symm)
      ((B.chart k).target ∩ (B.chart k).symm ⁻¹' (A.chart j).source) := by
    intro a ha b hb hab
    have h1 : (B.chart k).symm a = (B.chart k).symm b := (A.chart j).injOn ha.2 hb.2 hab
    exact (B.chart k).symm.injOn (by simpa using ha.1) (by simpa using hb.1) h1
  have hmaps : ∀ z ∈ (B.chart k).target ∩ (B.chart k).symm ⁻¹' (A.chart j).source,
      (A.chart j ∘ (B.chart k).symm) z ∈ (A.chart j).target := fun z hz =>
    (A.chart j).map_source hz.2

  have hcpt : IsCompact ((A.chart j ∘ (B.chart k).symm) '' Metric.closedBall y (r / 2)) :=
    (isCompact_closedBall y (r / 2)).image_of_continuousOn (hτa.continuousOn.mono hsub)
  have hA : IntegrableOn (fun w => g ((A.chart j).symm w) * locDens A Φ j w)
      ((A.chart j ∘ (B.chart k).symm) '' Metric.ball y (r / 2)) :=
    (hg j _ (by rintro _ ⟨z, hz, rfl⟩; exact hmaps z (hsub hz)) hcpt).mono_set
      (Set.image_mono Metric.ball_subset_closedBall)
  have hB := (ReciprocityTheory.AnForm.A.integrableOn_image_iff_analytic (A.chart j ∘ (B.chart k).symm)
    (Metric.ball y (r / 2)) Metric.isOpen_ball (hτa.mono hbV) (hinj.mono hbV)
    (fun w => g ((A.chart j).symm w) * locDens A Φ j w)).1 hA
  refine ⟨Metric.ball y (r / 2), mem_nhdsWithin_of_mem_nhds (Metric.ball_mem_nhds y (half_pos hr)),
    hB.congr_fun (fun z hz => ?_) Metric.isOpen_ball.measurableSet⟩
  have hzV := hbV hz
  have key := locDensChart (unionAtlas A B h) Φ hΦU (Fin.natAdd A.n k) (Fin.castAdd B.n j) z
    (by simpa using hzV.1) (by simpa using hzV.2)
  simp only [unionAtlas_chart_natAdd, unionAtlas_chart_castAdd, locDens_unionAtlas_natAdd,
    locDens_unionAtlas_castAdd] at key
  have hleft : (A.chart j).symm (A.chart j ((B.chart k).symm z)) = (B.chart k).symm z :=
    (A.chart j).left_inv hzV.2
  simp only [smul_eq_mul, ReciprocityTheory.AnForm.A.det_jacC, Complex.normSq_eq_norm_sq, key,
    Function.comp_apply, hleft]
  ring
end ReciprocityTheory.AnForm.M
