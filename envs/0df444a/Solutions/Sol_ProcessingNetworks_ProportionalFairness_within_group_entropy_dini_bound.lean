-- Prove2me | solution 1 for ProcessingNetworks.ProportionalFairness.within_group_entropy_dini_bound
-- status  : ACCEPTED   (disprove)
-- author  : @mrfancypants
-- created : 2026-10-03T18:21:19.248127+00:00
-- url     : https://prove2.me/submissions/72a15b9a-82d0-4e7f-8277-e51d1c314db9

import Mathlib
import Definitions.Def_ProcessingNetworks_ProportionalFairness_WithinGroupEntropy

open Filter Topology

namespace ProcessingNetworks.ProportionalFairness.WGEDiniCE

open ProcessingNetworks.ProportionalFairness

noncomputable def Z (s : ℝ) : Fin 1 → ℝ := fun _ => max (2 - |s - 1|) 0

theorem agg (x : Fin 1 → ℝ) : groupAggregate id x = x := by
  funext l; fin_cases l
  unfold groupAggregate
  rw [Finset.sum_eq_single 0]
  · rfl
  · intro b _ hb; exact absurd (Subsingleton.elim b 0) hb
  · intro h; simp at h

theorem small : ∀ᶠ h : ℝ in 𝓝[>] 0, 0 < h ∧ h < 1 := by
  filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (gt_mem_nhds (zero_lt_one' ℝ))]
    with h h1 h2
  exact ⟨h1, h2⟩

theorem Z_right (h : ℝ) (hh : 0 < h ∧ h < 1) : Z (1 + h) 0 = 2 - h := by
  simp only [Z]
  rw [show 1 + h - 1 = h by ring, abs_of_pos hh.1, max_eq_left (by linarith)]

theorem Z_left (h : ℝ) (hh : 0 < h ∧ h < 1) : Z (1 - h) 0 = 2 - h := by
  simp only [Z]
  rw [show 1 - h - 1 = -h by ring, abs_neg, abs_of_pos hh.1, max_eq_left (by linarith)]

theorem Z_one : Z 1 0 = 2 := by simp [Z]

theorem dini_const (g : ℝ → ℝ) (c : ℝ) (hg : ∀ᶠ h in 𝓝[>] (0 : ℝ), g h = c) :
    Filter.limsup (fun h => ((g h : ℝ) : EReal)) (𝓝[>] (0 : ℝ)) = (c : EReal) := by
  rw [limsup_congr (hg.mono fun h hh => by rw [hh])]
  exact limsup_const _

theorem W_zero (s : ℝ) : withinGroupEntropy id Z s = 0 := by
  unfold withinGroupEntropy
  rw [agg]
  simp only [Fin.sum_univ_one, id]
  split_ifs with h
  · rfl
  · rw [div_self h, Real.log_one, mul_zero]

end ProcessingNetworks.ProportionalFairness.WGEDiniCE

open ProcessingNetworks.ProportionalFairness in
theorem solution : ¬ (∀ {I L : ℕ} (grp : Fin I → Fin L) (Zh : ℝ → Fin I → ℝ)
    (hZnn : ∀ t, 0 ≤ t → ∀ i, 0 ≤ Zh t i)
    (hZlip : ∃ Kc : ℝ, ∀ i (s t : ℝ), 0 ≤ s → s ≤ t → |Zh t i - Zh s i| ≤ Kc * (t - s))
    (t : ℝ) (ht : 0 < t),
    diniUpperRight (withinGroupEntropy grp Zh) t ≤
      ∑ i, if Zh t i = 0 then (0 : EReal) else
        diniUpperLeft (fun s => Zh s i) t *
            ((Real.log (Zh t i / groupAggregate grp (Zh t) (grp i)) : ℝ) : EReal) +
          diniUpperRight (fun s => Zh s i) t -
            diniUpperLeft (fun s => groupAggregate grp (Zh s) (grp i)) t *
              ((Zh t i / groupAggregate grp (Zh t) (grp i) : ℝ) : EReal)) := by
  open WGEDiniCE in
  intro h
  have hlip : ∃ Kc : ℝ, ∀ i (s t : ℝ), 0 ≤ s → s ≤ t → |Z t i - Z s i| ≤ Kc * (t - s) := by
    refine ⟨1, fun i s t _ hst => ?_⟩
    simp only [Z, one_mul]
    refine (abs_max_sub_max_le_abs _ _ _).trans ?_
    rw [show 2 - |t - 1| - (2 - |s - 1|) = |s - 1| - |t - 1| by ring]
    refine (abs_abs_sub_abs_le_abs_sub _ _).trans ?_
    rw [show s - 1 - (t - 1) = s - t by ring, abs_sub_comm, abs_of_nonneg (by linarith)]
  have H := h id Z (fun _ _ _ => le_max_right _ _) hlip 1 one_pos
  have hW : diniUpperRight (withinGroupEntropy id Z) 1 = ((0 : ℝ) : EReal) := by
    unfold diniUpperRight
    refine dini_const _ 0 (Eventually.of_forall fun h => ?_)
    simp [W_zero]
  have hR : diniUpperRight (fun s => Z s 0) 1 = ((-1 : ℝ) : EReal) := by
    unfold diniUpperRight
    refine dini_const _ (-1) (small.mono fun h hh => ?_)
    show (Z (1 + h) 0 - Z 1 0) / h = -1
    rw [Z_right h hh, Z_one]
    field_simp [hh.1.ne']
    ring
  have hL : diniUpperLeft (fun s => Z s 0) 1 = ((1 : ℝ) : EReal) := by
    unfold diniUpperLeft
    refine dini_const _ 1 (small.mono fun h hh => ?_)
    show (Z 1 0 - Z (1 - h) 0) / h = 1
    rw [Z_left h hh, Z_one]
    field_simp [hh.1.ne']
    ring
  have hLY : diniUpperLeft (fun s => groupAggregate id (Z s) (id 0)) 1 = ((1 : ℝ) : EReal) := by
    simp only [agg, id]; exact hL
  rw [hW, Fin.sum_univ_one] at H
  rw [if_neg (by rw [Z_one]; norm_num)] at H
  rw [hL, hR, hLY] at H
  simp only [agg, id, Z_one] at H
  rw [← EReal.coe_mul, ← EReal.coe_mul, ← EReal.coe_add, ← EReal.coe_sub,
    EReal.coe_le_coe_iff] at H
  norm_num at H


