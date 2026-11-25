-- Prove2me | solution 1 for ReciprocityTheory.AnForm.M.pshShift_local
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:22:14.713027+00:00
-- url     : https://prove2.me/submissions/05aa417d-26d0-4c4d-bb41-b6c9910ae64d

import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_IsPotentialPullbackStatement
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_PshShiftA
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_PshShiftB
import Theorems.Thm_ReciprocityTheory_AnForm_M_two_le_infty
import Theorems.Thm_ReciprocityTheory_AnForm_continuousOn_levi
import Theorems.Thm_ReciprocityTheory_AnForm_levi_smul_dir
import Theorems.Thm_ReciprocityTheory_AnForm_levi_zero


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open Filter Topology FinHolAtlas
open scoped ContDiff
noncomputable section
variable {e : ℕ} {X : Type} [TopologicalSpace X]
namespace ReciprocityTheory.AnForm.M
theorem _root_.solution (A : FinHolAtlas e X) (Ω : LocPot X) (hΩ : IsPotential A Ω)
    (hpos : IsPosPot A Ω) (w : X → ℝ) (hw : A.Smooth w) (p : X) (j : Fin A.n)
    (hp : p ∈ (A.chart j).source) :
    ∃ r > 0, ∃ m : ℝ, Metric.closedBall (A.chart j p) r ⊆
        (A.chart j).target ∩ (A.chart j).symm ⁻¹' Ω.U p ∧
      ∀ y ∈ Metric.closedBall (A.chart j p) r, ∀ u : Fin e → ℂ,
        m * levi (Ω.φ p ∘ (A.chart j).symm) y u ≤ levi (w ∘ (A.chart j).symm) y u := by
  classical
  set φ : (Fin e → ℂ) → ℝ := Ω.φ p ∘ (A.chart j).symm with hφdef
  set ψ : (Fin e → ℂ) → ℝ := w ∘ (A.chart j).symm with hψdef
  set S : Set (Fin e → ℂ) := (A.chart j).target ∩ (A.chart j).symm ⁻¹' Ω.U p with hSdef
  have hSo : IsOpen S := (A.chart j).isOpen_inter_preimage_symm (Ω.isOpen_U p)
  have hz0 : A.chart j p ∈ S := by
    refine ⟨(A.chart j).map_source hp, ?_⟩
    show (A.chart j).symm (A.chart j p) ∈ Ω.U p
    rw [(A.chart j).left_inv hp]
    exact Ω.mem_U p
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hSo _ hz0
  have hsub : Metric.closedBall (A.chart j p) (ε / 2) ⊆ S :=
    (Metric.closedBall_subset_ball (by linarith)).trans hball
  have hφc : ContDiffOn ℝ 2 φ S := (hΩ.1 p j).of_le two_le_infty
  have hψc : ContDiffOn ℝ 2 ψ S :=
    ((hw j).of_le two_le_infty).mono (fun y hy => ⟨hy.1, Set.mem_univ _⟩)
  have hLφ := continuousOn_levi hSo hφc
  have hLψ := continuousOn_levi hSo hψc
  set K : Set ((Fin e → ℂ) × (Fin e → ℂ)) :=
    Metric.closedBall (A.chart j p) (ε / 2) ×ˢ Metric.sphere 0 1 with hKdef
  have hK : IsCompact K := (isCompact_closedBall _ _).prod (isCompact_sphere _ _)
  have hKS : K ⊆ S ×ˢ Set.univ := Set.prod_mono hsub (Set.subset_univ _)
  have hposK : ∀ q ∈ K, 0 < levi φ q.1 q.2 := by
    intro q hq
    refine hpos p j q.1 (hsub hq.1) q.2 ?_
    intro h0
    have h1 := hq.2
    rw [h0] at h1
    simp at h1
  have hg : ContinuousOn
      (fun q : (Fin e → ℂ) × (Fin e → ℂ) => levi ψ q.1 q.2 / levi φ q.1 q.2) K :=
    (hLψ.mono hKS).div (hLφ.mono hKS) (fun q hq => (hposK q hq).ne')
  obtain ⟨M, hM⟩ := hK.bddBelow_image hg
  refine ⟨ε / 2, by positivity, M, hsub, ?_⟩
  intro y hy u
  by_cases hu : u = 0
  · subst hu
    simp [levi_zero]
  · have ht : 0 < ‖u‖ := norm_pos_iff.2 hu
    obtain ⟨s, v, hv, rfl⟩ : ∃ s : ℝ, ∃ v ∈ Metric.sphere (0 : Fin e → ℂ) 1, u = s • v := by
      refine ⟨‖u‖, ‖u‖⁻¹ • u, ?_, ?_⟩
      · simp [norm_smul, hu, ht.ne']
      · simp [smul_smul, hu, ht.ne']
    have hq : ((y, v) : (Fin e → ℂ) × (Fin e → ℂ)) ∈ K := ⟨hy, hv⟩
    have h1 := hM ⟨(y, v), hq, rfl⟩
    have h2 := hposK _ hq
    simp only at h1 h2
    have h3 : M * levi φ y v ≤ levi ψ y v := by
      rwa [le_div_iff₀ h2] at h1
    rw [levi_smul_dir, levi_smul_dir]
    nlinarith [mul_le_mul_of_nonneg_left h3 (sq_nonneg s)]
end ReciprocityTheory.AnForm.M
