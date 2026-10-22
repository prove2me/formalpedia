-- Prove2me | solution 1 for OceanicGames.Interior.eq_4_3
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-21T23:54:04.394693+00:00
-- url     : https://prove2.me/submissions/b7e85c91-5432-4425-ba18-4495dde6660a

import Mathlib
import Definitions.Def_OceanicGames_Interior_Basic
open MeasureTheory Filter Topology


namespace OceanicGames.Interior

lemma og_hyper_null {m : ℕ} (L : (Fin m → ℝ) →ₗ[ℝ] ℝ) (hL : L ≠ 0) (a : ℝ) :
    volume {x : Fin m → ℝ | L x = a} = 0 := by
  by_cases hne : ∃ p, L p = a
  · obtain ⟨p, hp⟩ := hne
    have hker : (LinearMap.ker L) ≠ ⊤ := by
      intro h; exact hL (LinearMap.ker_eq_top.mp h)
    have h0 := Measure.addHaar_submodule (volume : Measure (Fin m → ℝ)) (LinearMap.ker L) hker
    have hset : {x : Fin m → ℝ | L x = a} = (fun x => x + (-p)) ⁻¹' (LinearMap.ker L : Set _) := by
      ext x; simp [sub_eq_zero, hp, ← sub_eq_add_neg]
    rw [hset, measure_preimage_add_right]; exact h0
  · push_neg at hne
    have : {x : Fin m → ℝ | L x = a} = ∅ := by ext x; simp [hne x]
    rw [this]; simp

lemma og_diag_null {m : ℕ} (i j : Fin m) (hij : i ≠ j) :
    volume {x : Fin m → ℝ | x i = x j} = 0 := by
  let L : (Fin m → ℝ) →ₗ[ℝ] ℝ := LinearMap.proj (R := ℝ) (φ := fun _ : Fin m => ℝ) i - LinearMap.proj (R := ℝ) (φ := fun _ : Fin m => ℝ) j
  have hL : L ≠ 0 := by
    intro h
    have := LinearMap.congr_fun h (Pi.single i 1)
    simp [L, Pi.single_apply, hij.symm] at this
  have := og_hyper_null L hL 0
  have hset : {x : Fin m → ℝ | x i = x j} = {x | L x = 0} := by
    ext x; simp [L, sub_eq_zero]
  rw [hset]; exact this

lemma og_wsum_mono {m : ℕ} (w : Fin m → ℝ) (hw : ∀ j, 0 ≤ w j) {S T : Finset (Fin m)}
    (h : S ⊆ T) : wsum w S ≤ wsum w T :=
  Finset.sum_le_sum_of_subset_of_nonneg h (fun j _ _ => hw j)

lemma og_not_lt {m : ℕ} (c α : ℝ) (w : Fin m → ℝ) (hα : 0 < α)
    (hw : ∀ j, 0 ≤ w j) (i j : Fin m) (x : Fin m → ℝ)
    (hi : x ∈ pivotSet c α w i) (hj : x ∈ pivotSet c α w j) (hlt : x i < x j) : False := by
  obtain ⟨_, _, hi2⟩ := hi
  obtain ⟨_, hj1, _⟩ := hj
  have hsub : insert i (pred x (x i)) ⊆ pred x (x j) := by
    intro k hk
    simp only [pred, Finset.mem_insert, Finset.mem_filter, Finset.mem_univ, true_and] at hk ⊢
    rcases hk with rfl | hk
    · exact hlt
    · exact hk.trans hlt
  have hnot : i ∉ pred x (x i) := by simp [pred]
  have h1 := og_wsum_mono w hw hsub
  have h2 : wsum w (insert i (pred x (x i))) = w i + wsum w (pred x (x i)) := by
    unfold wsum; rw [Finset.sum_insert hnot]
  nlinarith

theorem pivotSet_ae_disjoint_core {m : ℕ} (c α : ℝ) (w : Fin m → ℝ) (hα : 0 < α)
    (hw : ∀ j, 0 ≤ w j) (i j : Fin m) (hij : i ≠ j) :
    volume (pivotSet c α w i ∩ pivotSet c α w j) = 0 := by
  apply measure_mono_null _ (og_diag_null i j hij)
  intro x ⟨hi, hj⟩
  simp only [Set.mem_setOf_eq]
  rcases lt_trichotomy (x i) (x j) with h | h | h
  · exact (og_not_lt c α w hα hw i j x hi hj h).elim
  · exact h
  · exact (og_not_lt c α w hα hw j i x hj hi h).elim

lemma og_pred_mono {m : ℕ} (x : Fin m → ℝ) {s t : ℝ} (h : s ≤ t) : pred x s ⊆ pred x t := by
  intro k hk
  simp only [pred, Finset.mem_filter, Finset.mem_univ, true_and] at hk ⊢
  exact lt_of_lt_of_le hk h

lemma og_g_mono {m : ℕ} (α : ℝ) (w : Fin m → ℝ) (hw : ∀ j, 0 ≤ w j) (hα : 0 < α)
    (x : Fin m → ℝ) {s t : ℝ} (h : s ≤ t) :
    wsum w (pred x s) + α * s ≤ wsum w (pred x t) + α * t := by
  have := og_wsum_mono w hw (og_pred_mono x h)
  nlinarith

lemma og_g_strict {m : ℕ} (α : ℝ) (w : Fin m → ℝ) (hw : ∀ j, 0 ≤ w j) (hα : 0 < α)
    (x : Fin m → ℝ) {s t : ℝ} (h : s < t) :
    wsum w (pred x s) + α * s < wsum w (pred x t) + α * t := by
  have := og_wsum_mono w hw (og_pred_mono x h.le)
  nlinarith

lemma og_pred_big {m : ℕ} (x : Fin m → ℝ) (hx : x ∈ cube m) {t : ℝ} (ht : 1 < t) :
    pred x t = Finset.univ := by
  ext j; simp only [pred, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
  exact lt_of_le_of_lt (hx.2 j) ht

lemma og_pred_zero {m : ℕ} (x : Fin m → ℝ) (hx : x ∈ cube m) : pred x 0 = ∅ := by
  ext j; simp only [pred, Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty,
    iff_false, not_lt]
  exact hx.1 j

lemma og_S_nonempty {m : ℕ} (α : ℝ) (w : Fin m → ℝ) (hα : 0 < α) (x : Fin m → ℝ)
    (hx : x ∈ cube m) (y : ℝ) (hyW : y ≤ wsum w Finset.univ + α) :
    (2:ℝ) ∈ {t : ℝ | 0 ≤ t ∧ y ≤ wsum w (pred x t) + α * t} := by
  refine ⟨by norm_num, ?_⟩
  rw [og_pred_big x hx (by norm_num : (1:ℝ) < 2)]
  nlinarith

lemma og_S_bdd {m : ℕ} (α : ℝ) (w : Fin m → ℝ) (x : Fin m → ℝ) (y : ℝ) :
    BddBelow {t : ℝ | 0 ≤ t ∧ y ≤ wsum w (pred x t) + α * t} := ⟨0, fun t ht => ht.1⟩

/-- direction 1 -/
lemma og_piv_to_loc {m : ℕ} (α : ℝ) (w : Fin m → ℝ) (hα : 0 < α) (hw : ∀ j, 0 ≤ w j)
    (y : ℝ) (hyW : y ≤ wsum w Finset.univ + α) (i : Fin m) (x : Fin m → ℝ)
    (hx : x ∈ pivotSet y α w i) : pivotLoc α w x y = x i := by
  obtain ⟨hc, h1, h2⟩ := hx
  have hne : ({t : ℝ | 0 ≤ t ∧ y ≤ wsum w (pred x t) + α * t}).Nonempty :=
    ⟨2, og_S_nonempty α w hα x hc y hyW⟩
  apply le_antisymm
  · apply le_of_forall_gt_imp_ge_of_dense
    intro t ht
    apply csInf_le (og_S_bdd α w x y)
    refine ⟨le_trans (hc.1 i) ht.le, ?_⟩
    have hsub : insert i (pred x (x i)) ⊆ pred x t := by
      intro k hk
      simp only [pred, Finset.mem_insert, Finset.mem_filter, Finset.mem_univ, true_and] at hk ⊢
      rcases hk with rfl | hk
      · exact ht
      · exact hk.trans ht
    have hnot : i ∉ pred x (x i) := by simp [pred]
    have e1 := og_wsum_mono w hw hsub
    have e2 : wsum w (insert i (pred x (x i))) = w i + wsum w (pred x (x i)) := by
      unfold wsum; rw [Finset.sum_insert hnot]
    nlinarith
  · apply le_csInf hne
    intro t ⟨_, ht⟩
    by_contra hlt
    push_neg at hlt
    have := og_g_strict α w hw hα x hlt
    linarith

/-- direction 2 -/
lemma og_loc_to_piv {m : ℕ} (α : ℝ) (w : Fin m → ℝ) (hα : 0 < α) (hw : ∀ j, 0 ≤ w j)
    (y : ℝ) (hy0 : 0 ≤ y) (hyW : y ≤ wsum w Finset.univ + α) (i : Fin m) (x : Fin m → ℝ)
    (hc : x ∈ cube m) (hnt : ∀ j, j ≠ i → x j ≠ x i)
    (hF : pivotLoc α w x y = x i) : x ∈ pivotSet y α w i := by
  have hne : ({t : ℝ | 0 ≤ t ∧ y ≤ wsum w (pred x t) + α * t}).Nonempty :=
    ⟨2, og_S_nonempty α w hα x hc y hyW⟩
  unfold pivotLoc at hF
  refine ⟨hc, ?_, ?_⟩
  · by_contra hlt
    push_neg at hlt
    rcases (hc.1 i).eq_or_lt with h0 | hpos
    · have h0' : x i = 0 := h0.symm
      rw [h0', og_pred_zero x hc] at hlt
      simp [wsum] at hlt; linarith
    · have hpos' : 0 < x i := hpos
      have ev1 : ∀ᶠ t in 𝓝[<] (x i), ∀ j, x j < x i → x j < t := by
        rw [Filter.eventually_all]
        intro j
        by_cases hj : x j < x i
        · filter_upwards [nhdsWithin_le_nhds (Ioi_mem_nhds hj)] with t ht _ using ht
        · exact Filter.Eventually.of_forall (fun t h => (hj h).elim)
      have ev2 : ∀ᶠ t in 𝓝[<] (x i), x i - (wsum w (pred x (x i)) + α * x i - y) / α < t ∧ 0 < t := by
        have hd : 0 < (wsum w (pred x (x i)) + α * x i - y) / α := div_pos (by linarith) hα
        apply nhdsWithin_le_nhds
        exact Filter.inter_mem (Ioi_mem_nhds (by linarith : x i - _ < x i)) (Ioi_mem_nhds hpos')
      have ev3 : ∀ᶠ t in 𝓝[<] (x i), t < x i := self_mem_nhdsWithin
      obtain ⟨t, ht1, ⟨ht2, ht0⟩, ht3⟩ := (ev1.and (ev2.and ev3)).exists
      have hpe : pred x t = pred x (x i) := by
        ext j; simp only [pred, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨fun h => h.trans ht3, ht1 j⟩
      have hmem : t ∈ {t : ℝ | 0 ≤ t ∧ y ≤ wsum w (pred x t) + α * t} := by
        refine ⟨ht0.le, ?_⟩
        rw [hpe]
        have : (wsum w (pred x (x i)) + α * x i - y) / α * α = wsum w (pred x (x i)) + α * x i - y :=
          div_mul_cancel₀ _ hα.ne'
        nlinarith
      have := csInf_le (og_S_bdd α w x y) hmem
      linarith
  · by_contra hlt
    push_neg at hlt
    have ev1 : ∀ᶠ t in 𝓝[>] (x i), ∀ j, x i < x j → t < x j := by
      rw [Filter.eventually_all]
      intro j
      by_cases hj : x i < x j
      · filter_upwards [nhdsWithin_le_nhds (Iio_mem_nhds hj)] with t ht _ using ht
      · exact Filter.Eventually.of_forall (fun t h => (hj h).elim)
    have ev2 : ∀ᶠ t in 𝓝[>] (x i), t < x i + (y - (wsum w (pred x (x i)) + w i + α * x i)) / α := by
      have hd : 0 < (y - (wsum w (pred x (x i)) + w i + α * x i)) / α := div_pos (by linarith) hα
      apply nhdsWithin_le_nhds
      exact Iio_mem_nhds (by linarith)
    have ev3 : ∀ᶠ t in 𝓝[>] (x i), x i < t := self_mem_nhdsWithin
    obtain ⟨t, ht1, ht2, ht3⟩ := (ev1.and (ev2.and ev3)).exists
    have hsub : pred x t ⊆ insert i (pred x (x i)) := by
      intro k hk
      simp only [pred, Finset.mem_insert, Finset.mem_filter, Finset.mem_univ, true_and] at hk ⊢
      by_contra hcon
      push_neg at hcon
      rcases lt_trichotomy (x i) (x k) with h | h | h
      · exact absurd (ht1 k h) (not_lt.mpr hk.le)
      · exact hnt k hcon.1 h.symm
      · exact absurd h (not_lt.mpr hcon.2)
    have hnot : i ∉ pred x (x i) := by simp [pred]
    have e1 := og_wsum_mono w hw hsub
    have e2 : wsum w (insert i (pred x (x i))) = w i + wsum w (pred x (x i)) := by
      unfold wsum; rw [Finset.sum_insert hnot]
    have hgt : wsum w (pred x t) + α * t < y := by
      have : (y - (wsum w (pred x (x i)) + w i + α * x i)) / α * α
          = y - (wsum w (pred x (x i)) + w i + α * x i) := div_mul_cancel₀ _ hα.ne'
      nlinarith
    have hlb : t ≤ sInf {t : ℝ | 0 ≤ t ∧ y ≤ wsum w (pred x t) + α * t} := by
      apply le_csInf hne
      intro s ⟨_, hs⟩
      by_contra hst
      push_neg at hst
      have := og_g_mono α w hw hα x hst.le
      linarith
    linarith

lemma og_ties_null {m : ℕ} (i : Fin m) :
    volume {x : Fin m → ℝ | ∃ j, j ≠ i ∧ x j = x i} = 0 := by
  have : {x : Fin m → ℝ | ∃ j, j ≠ i ∧ x j = x i} = ⋃ j, ⋃ (_ : j ≠ i),
      {x : Fin m → ℝ | x j = x i} := by
    ext x; simp
  rw [this]
  exact measure_iUnion_null fun j => measure_iUnion_null fun hj => og_diag_null j i hj

theorem eq_4_3_core {m : ℕ} (α : ℝ) (w : Fin m → ℝ) (hα : 0 < α) (hw : ∀ j, 0 ≤ w j)
    (y : ℝ) (hy0 : 0 ≤ y) (hyW : y ≤ wsum w Finset.univ + α) (i : Fin m) :
    value y α w i = (volume {x | x ∈ cube m ∧ pivotLoc α w x y = x i}).toReal := by
  unfold value
  congr 1
  apply measure_congr
  rw [Filter.eventuallyEq_set]
  filter_upwards [measure_eq_zero_iff_ae_notMem.mp (og_ties_null i)] with x hx
  simp only [Set.mem_ofPred_eq, not_exists, not_and] at hx
  constructor
  · intro h
    exact ⟨h.1, og_piv_to_loc α w hα hw y hyW i x h⟩
  · rintro ⟨hc, hF⟩
    exact og_loc_to_piv α w hα hw y hy0 hyW i x hc hx hF

end OceanicGames.Interior

open OceanicGames.Interior


theorem solution {m : ℕ} (α : ℝ) (w : Fin m → ℝ) (hα : 0 < α) (hw : ∀ j, 0 ≤ w j)
    (y : ℝ) (hy0 : 0 ≤ y) (hyW : y ≤ wsum w Finset.univ + α) (i : Fin m) :
    value y α w i = (volume {x | x ∈ cube m ∧ pivotLoc α w x y = x i}).toReal := by
  exact eq_4_3_core α w hα hw y hy0 hyW i
