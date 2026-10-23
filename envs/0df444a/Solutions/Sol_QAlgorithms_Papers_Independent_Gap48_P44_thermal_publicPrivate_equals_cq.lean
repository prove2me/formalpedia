-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Gap48.P44.thermal_publicPrivate_equals_cq
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T06:29:49.586595+00:00
-- url     : https://prove2.me/submissions/746d21a1-7b50-4ce9-b191-9e1b7bea1b3c

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P44
noncomputable section

open QAlgorithms.Papers.Independent.Gap48.P44
open Filter

open scoped ENNReal Topology

open QAlgorithms.Papers.Independent.Claimed50.P39 (g)

open QAlgorithms.Papers.Independent.Information100.P54 (thermalEntropy)

theorem g78b_g_mono : MonotoneOn g (Set.Ici 0) := by
  have hc : ContinuousOn g (Set.Ici 0) := by
    have h1 : ContinuousOn (fun v : ℝ => (v + 1) * Real.log (v + 1)) (Set.Ici 0) := by
      apply ContinuousOn.mul (continuousOn_id.add continuousOn_const)
      apply ContinuousOn.log (continuousOn_id.add continuousOn_const)
      intro x hx; have : (0:ℝ) ≤ x := hx; exact ne_of_gt (by simp; linarith)
    exact h1.sub Real.continuous_mul_log.continuousOn
  have hd : ∀ v : ℝ, 0 < v → HasDerivAt g (Real.log (v + 1) - Real.log v) v := by
    intro v hv
    have h1 : HasDerivAt (fun v : ℝ => v + 1) 1 v := (hasDerivAt_id v).add_const 1
    have h2 := h1.mul (h1.log (by linarith))
    have h3 := (hasDerivAt_id v).mul (Real.hasDerivAt_log hv.ne')
    have := h2.sub h3
    refine this.congr_deriv ?_
    simp only [id, one_mul]
    field_simp
    ring
  apply monotoneOn_of_deriv_nonneg (convex_Ici 0) hc
  · rw [interior_Ici]; intro x hx; exact (hd x hx).differentiableAt.differentiableWithinAt
  · rw [interior_Ici]; intro x hx
    have hx' : (0:ℝ) < x := hx
    rw [(hd x hx').deriv]
    have := Real.log_le_log hx' (by linarith : x ≤ x + 1)
    linarith

theorem g78b_te_mono {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) : thermalEntropy x ≤ thermalEntropy y := by
  have := g78b_g_mono hx (le_trans hx hxy : (0:ℝ) ≤ y) hxy
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  show g x / Real.log 2 ≤ g y / Real.log 2
  exact div_le_div_of_nonneg_right this hl2.le

theorem g78b_te_nonneg {x : ℝ} (hx : 0 ≤ x) : 0 ≤ thermalEntropy x := by
  have := g78b_te_mono le_rfl hx
  simpa [thermalEntropy] using this

/-- PDF p.15, Section IV B: the displayed coherent-ensemble public/private
family at S=0 equals the displayed CQ family, after relabeling (R,P)=(C,Q).
Only the explicit inner families are compared, with both modes of the true
complement in (80); this is not equality of operational channel capacities. -/
theorem solution (eta budget noise : ℝ)
    (heta0 : 0 ≤ eta) (heta1 : eta ≤ 1) (hbudget : 0 ≤ budget) (hnoise : 0 ≤ noise) :
    let output := thermalEntropy (eta * budget + (1 - eta) * noise)
    let conditional := fun share => thermalEntropy (eta * share * budget + (1 - eta) * noise)
    let environment := fun share => thermalEnvironment eta share budget noise
    {r ∈ cqFamily output conditional environment |
      r.1 + r.2 ≤ output - thermalEntropy ((1 - eta) * noise)} =
      cqFamily output conditional environment := by
  intro output conditional environment
  ext r
  simp only [Set.mem_sep_iff]
  refine ⟨fun h => h.1, fun h => ⟨h, ?_⟩⟩
  obtain ⟨_, _, share, ⟨hs0, hs1⟩, _, h2⟩ := h
  have key : thermalEntropy ((1 - eta) * noise) ≤ environment share := by
    simp only [environment, thermalEnvironment]
    have ha : 0 ≤ share * (1 - eta) * budget := by
      have : 0 ≤ 1 - eta := by linarith
      positivity
    have hb : 0 ≤ (1 - eta) * noise := mul_nonneg (by linarith) hnoise
    have hD : share * (1 - eta) * budget + (1 - eta) * noise + 1 ≤
        thermalD eta share budget noise := by
      unfold thermalD
      apply Real.le_sqrt_of_sq_le
      have : 0 ≤ 4 * eta * (share * budget) * ((1 - eta) * noise) := by positivity
      nlinarith
    have t1 := g78b_te_nonneg (x := (thermalD eta share budget noise +
        share * (1 - eta) * budget - (1 - eta) * noise - 1) / 2) (by linarith)
    have t2 := g78b_te_mono (x := (1 - eta) * noise) (y := (thermalD eta share budget noise -
        share * (1 - eta) * budget + (1 - eta) * noise - 1) / 2) hb (by linarith)
    linarith
  linarith


end
