-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_AnalyticLimit_levi_abs_le_local_acdff8994b08
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T13:45:27.721547+00:00
-- url     : https://prove2.me/submissions/9679f2b2-02e6-497f-b859-4324a26a7ab7

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_PshShiftA
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_AnalyticLimit_KaehlerBound
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_AnalyticLimit_PKaehlerBound
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_AnalyticLimit_two_le_smooth_kb_fd6647adc872
import Theorems.Thm_ReciprocityTheory_AnForm_A_PshMean_isOpen_inter_preimage
import Theorems.Thm_ReciprocityTheory_AnForm_M_ima_apply
import Theorems.Thm_ReciprocityTheory_AnForm_M_rea_apply
import Theorems.Thm_ReciprocityTheory_AnForm_continuousOn_levi
import Theorems.Thm_ReciprocityTheory_AnForm_levi_add_smul
import Theorems.Thm_ReciprocityTheory_AnForm_levi_comp
import Theorems.Thm_ReciprocityTheory_AnForm_levi_congr
import Theorems.Thm_ReciprocityTheory_AnForm_levi_re_analytic
import Theorems.Thm_ReciprocityTheory_AnForm_levi_smul_dir
import Theorems.Thm_ReciprocityTheory_AnForm_levi_zero
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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.AnalyticLimit
open Filter Topology
open scoped ContDiff
open ReciprocityTheory.AnForm (levi levi_congr levi_comp levi_zero levi_smul_dir levi_add_smul
  levi_re_analytic continuousOn_levi)
open ReciprocityTheory.AnForm.M (FinHolAtlas LocPot IsPotential IsPosPot chartIdx)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular (RegChartData)
noncomputable section
variable {D : ℕ} {X : Type} [TopologicalSpace X]
namespace GroundTheory.Heights₂.Heights.AnalyticLimit
theorem _root_.solution (A : FinHolAtlas D X) (θ om : LocPot X) (hθ : IsPotential A θ)
    (hom : IsPotential A om) (hpos : IsPosPot A om) (p : X) (j : Fin A.n)
    (hp : p ∈ (A.chart j).source) :
    ∃ r > 0, ∃ M : ℝ, Metric.closedBall (A.chart j p) r ⊆
        (A.chart j).target ∩ (A.chart j).symm ⁻¹' (θ.U p ∩ om.U p) ∧
      ∀ y ∈ Metric.closedBall (A.chart j p) r, ∀ u : Fin D → ℂ,
        |levi (θ.φ p ∘ (A.chart j).symm) y u| ≤ M * levi (om.φ p ∘ (A.chart j).symm) y u := by
  set c := A.chart j with hc
  set O := c.target ∩ c.symm ⁻¹' (θ.U p ∩ om.U p) with hO
  have hOo : IsOpen O := c.continuousOn_symm.isOpen_inter_preimage c.open_target
    ((θ.isOpen_U p).inter (om.isOpen_U p))
  have hpO : c p ∈ O := ⟨c.map_source hp, by
    simp only [Set.mem_preimage, c.left_inv hp]; exact ⟨θ.mem_U p, om.mem_U p⟩⟩
  obtain ⟨r, hr, hrO⟩ := Metric.isOpen_iff.1 hOo _ hpO
  have hcb : Metric.closedBall (c p) (r / 2) ⊆ O :=
    (Metric.closedBall_subset_ball (by linarith)).trans hrO
  have homs : ContDiffOn ℝ 2 (om.φ p ∘ c.symm) O :=
    ((hom.1 p j).mono fun y hy => ⟨hy.1, hy.2.2⟩).of_le two_le_smooth_kb
  have hθs : ContDiffOn ℝ 2 (θ.φ p ∘ c.symm) O :=
    ((hθ.1 p j).mono fun y hy => ⟨hy.1, hy.2.1⟩).of_le two_le_smooth_kb
  set K := Metric.closedBall (c p) (r / 2) ×ˢ Metric.sphere (0 : Fin D → ℂ) 1 with hK
  have hKc : IsCompact K := (isCompact_closedBall _ _).prod (isCompact_sphere _ _)
  have hKO : K ⊆ O ×ˢ Set.univ := Set.prod_mono hcb (Set.subset_univ _)
  have hpos' : ∀ q ∈ K, 0 < levi (om.φ p ∘ c.symm) q.1 q.2 := by
    rintro ⟨y, u⟩ ⟨hy, hu⟩
    refine hpos p j y ⟨(hcb hy).1, (hcb hy).2.2⟩ u ?_
    rintro rfl
    simp at hu
  have hcont : ContinuousOn (fun q : (Fin D → ℂ) × (Fin D → ℂ) =>
      |levi (θ.φ p ∘ c.symm) q.1 q.2| / levi (om.φ p ∘ c.symm) q.1 q.2) K :=
    (((continuousOn_levi hOo hθs).mono hKO).abs).div ((continuousOn_levi hOo homs).mono hKO)
      (fun q hq => (hpos' q hq).ne')
  obtain ⟨M, hM⟩ := hKc.bddAbove_image hcont
  refine ⟨r / 2, by linarith, M, hcb, fun y hy u => ?_⟩
  rcases eq_or_ne u 0 with rfl | hu
  · simp [levi_zero]
  · have hn : 0 < ‖u‖ := norm_pos_iff.2 hu
    obtain ⟨v, hv'⟩ : ∃ v : Fin D → ℂ, v = ‖u‖⁻¹ • u := ⟨_, rfl⟩
    have hv : v ∈ Metric.sphere (0 : Fin D → ℂ) 1 := by
      rw [mem_sphere_zero_iff_norm, hv', norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hn.ne']
    have hq : (y, v) ∈ K := ⟨hy, hv⟩
    have h1 : |levi (θ.φ p ∘ c.symm) y v| / levi (om.φ p ∘ c.symm) y v ≤ M :=
      hM ⟨(y, v), hq, rfl⟩
    have h2 := hpos' _ hq
    have h3 : |levi (θ.φ p ∘ c.symm) y v| ≤ M * levi (om.φ p ∘ c.symm) y v := by
      rwa [div_le_iff₀ h2] at h1
    obtain ⟨s, hs⟩ : ∃ s : ℝ, s = ‖u‖ := ⟨_, rfl⟩
    have huv : u = s • v := by
      rw [hs, hv', smul_smul, mul_inv_cancel₀ hn.ne', one_smul]
    rw [huv, levi_smul_dir, levi_smul_dir, abs_mul, abs_of_nonneg (sq_nonneg s)]
    have : 0 ≤ s ^ 2 := sq_nonneg s
    nlinarith
end GroundTheory.Heights₂.Heights.AnalyticLimit
