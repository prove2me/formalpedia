-- Prove2me | solution 1 for OceanicGames.Interior.theorem_2
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-22T00:03:22.767992+00:00
-- url     : https://prove2.me/submissions/bb6c7290-4a2a-4673-afe6-93933aa4f22a

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

lemma og_loc_inv {m : ℕ} (α : ℝ) (w : Fin m → ℝ) (hα : 0 < α) (hw : ∀ j, 0 ≤ w j)
    (x : Fin m → ℝ) {t : ℝ} (ht : 0 ≤ t) :
    pivotLoc α w x (wsum w (pred x t) + α * t) = t := by
  unfold pivotLoc
  apply IsLeast.csInf_eq
  refine ⟨⟨ht, le_rfl⟩, ?_⟩
  intro s ⟨_, hs⟩
  by_contra hlt
  push_neg at hlt
  have := og_g_strict α w hw hα x hlt
  linarith

lemma og_pred_loc_const {m : ℕ} (x : Fin m → ℝ) (t0 : ℝ) (h : ∀ j, x j ≠ t0) :
    ∀ᶠ t in 𝓝 t0, pred x t = pred x t0 := by
  have : ∀ᶠ t in 𝓝 t0, ∀ j, (x j < t ↔ x j < t0) := by
    rw [Filter.eventually_all]
    intro j
    rcases lt_or_gt_of_ne (h j) with hj | hj
    · filter_upwards [Ioi_mem_nhds hj] with t ht
      exact ⟨fun _ => hj, fun _ => ht⟩
    · filter_upwards [Iio_mem_nhds hj] with t ht
      exact ⟨fun h' => absurd (h'.trans ht) (lt_irrefl _), fun h' => absurd (h'.trans hj) (lt_irrefl _)⟩
  filter_upwards [this] with t ht
  ext j; simp only [pred, Finset.mem_filter, Finset.mem_univ, true_and]; exact ht j

/-- case A: x pivotal at i strictly -/
lemma og_caseA {m : ℕ} (α : ℝ) (w : Fin m → ℝ) (hα : 0 < α) (hw : ∀ j, 0 ≤ w j)
    (y : ℝ) (hyW : y < wsum w Finset.univ + α) (i : Fin m) (x : Fin m → ℝ)
    (hc : x ∈ cube m) (h1 : wsum w (pred x (x i)) + α * x i < y)
    (h2 : y < wsum w (pred x (x i)) + w i + α * x i) :
    HasDerivAt (fun z => pivotLoc α w x z) 0 y := by
  apply (hasDerivAt_const y (x i)).congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds h1, Iio_mem_nhds h2, Iio_mem_nhds hyW] with z hz1 hz2 hz3
  exact og_piv_to_loc α w hα hw z (le_of_lt hz3) i x ⟨hc, le_of_lt hz1, le_of_lt hz2⟩

/-- case B: x not pivotal anywhere, no ties -/
lemma og_caseB {m : ℕ} (α : ℝ) (w : Fin m → ℝ) (hα : 0 < α) (hw : ∀ j, 0 ≤ w j)
    (y : ℝ) (hy0 : 0 < y) (hyW : y ≤ wsum w Finset.univ + α) (x : Fin m → ℝ)
    (hc : x ∈ cube m) (hnt : ∀ i j, i ≠ j → x i ≠ x j)
    (hnp : ∀ i, x ∉ pivotSet y α w i) :
    HasDerivAt (fun z => pivotLoc α w x z) (1 / α) y := by
  set S := {t : ℝ | 0 ≤ t ∧ y ≤ wsum w (pred x t) + α * t} with hS
  have hne : S.Nonempty := ⟨2, og_S_nonempty α w hα x hc y hyW⟩
  set t0 := pivotLoc α w x y with ht0def
  have ht0S : t0 = sInf S := rfl
  have ht0nn : 0 ≤ t0 := le_csInf hne (fun t ht => ht.1)
  have hneq : ∀ j, x j ≠ t0 := by
    intro j hj
    exact hnp j (og_loc_to_piv α w hα hw y hy0.le hyW j x hc
      (fun k hk => hnt k j hk) hj.symm)
  set P0 := pred x t0 with hP0
  have hloc := og_pred_loc_const x t0 hneq
  -- y ≤ G t0
  have hle1 : y ≤ wsum w P0 + α * t0 := by
    by_contra hlt
    push_neg at hlt
    have hd : 0 < (y - (wsum w P0 + α * t0)) / α := div_pos (by linarith) hα
    have ev : ∀ᶠ t in 𝓝 t0, pred x t = P0 ∧ t < t0 + (y - (wsum w P0 + α * t0)) / α :=
      hloc.and (Iio_mem_nhds (by linarith))
    obtain ⟨ε, hε, hεP⟩ := Metric.eventually_nhds_iff.mp ev
    obtain ⟨s, hsS, hslt⟩ := exists_lt_of_csInf_lt hne (show sInf S < t0 + ε by rw [← ht0S]; linarith)
    have hsge : t0 ≤ s := by rw [ht0S]; exact csInf_le (og_S_bdd α w x y) hsS
    have hd' : dist s t0 < ε := by rw [Real.dist_eq, abs_of_nonneg (by linarith)]; linarith
    obtain ⟨hp, hs2⟩ := hεP hd'
    have := hsS.2
    rw [hp] at this
    have : (y - (wsum w P0 + α * t0)) / α * α = y - (wsum w P0 + α * t0) := div_mul_cancel₀ _ hα.ne'
    nlinarith
  have ht0pos : 0 < t0 := by
    rcases ht0nn.eq_or_lt with h0 | h0
    · exfalso
      have : P0 = ∅ := by rw [hP0, ← h0]; exact og_pred_zero x hc
      rw [this, ← h0] at hle1
      simp [wsum] at hle1; linarith
    · exact h0
  have hle2 : wsum w P0 + α * t0 ≤ y := by
    by_contra hlt
    push_neg at hlt
    have hd : 0 < (wsum w P0 + α * t0 - y) / α := div_pos (by linarith) hα
    have ev : ∀ᶠ t in 𝓝[<] t0, (pred x t = P0 ∧ t0 - (wsum w P0 + α * t0 - y) / α < t ∧ 0 < t) ∧ t < t0 :=
      Filter.Eventually.and (nhdsWithin_le_nhds (hloc.and
        (show ∀ᶠ t in 𝓝 t0, t0 - (wsum w P0 + α * t0 - y) / α < t ∧ 0 < t from
          Filter.inter_mem (Ioi_mem_nhds (by linarith)) (Ioi_mem_nhds ht0pos)))) self_mem_nhdsWithin
    obtain ⟨t, ⟨hp, ht1, ht2⟩, ht3⟩ := ev.exists
    have hmem : t ∈ S := by
      refine ⟨ht2.le, ?_⟩
      rw [hp]
      have : (wsum w P0 + α * t0 - y) / α * α = wsum w P0 + α * t0 - y := div_mul_cancel₀ _ hα.ne'
      nlinarith
    have := csInf_le (og_S_bdd α w x y) hmem
    rw [← ht0S] at this
    linarith
  have hG : wsum w P0 + α * t0 = y := le_antisymm hle2 hle1
  -- local formula
  have hcont : Filter.Tendsto (fun z : ℝ => t0 + (z - y) / α) (𝓝 y) (𝓝 t0) := by
    have : Continuous (fun z : ℝ => t0 + (z - y) / α) := by fun_prop
    have h := this.tendsto y
    simpa using h
  have hder : HasDerivAt (fun z : ℝ => t0 + (z - y) / α) (1 / α) y := by
    have := (((hasDerivAt_id y).sub_const y).div_const α).const_add t0
    simpa using this
  apply hder.congr_of_eventuallyEq
  filter_upwards [hcont.eventually hloc, hcont.eventually (Ioi_mem_nhds ht0pos)] with z hz1 hz2
  have hgz : wsum w (pred x (t0 + (z - y) / α)) + α * (t0 + (z - y) / α) = z := by
    rw [hz1]
    have : α * ((z - y) / α) = z - y := mul_div_cancel₀ _ hα.ne'
    linarith
  have := og_loc_inv α w hα hw x (t := t0 + (z - y) / α) hz2.le
  rw [hgz] at this
  exact this

lemma og_hyp_null {m : ℕ} (α : ℝ) (hα : 0 < α) (w : Fin m → ℝ) (y : ℝ) :
    volume {x : Fin m → ℝ | ∃ i, ∃ S : Finset (Fin m), wsum w S + α * x i = y} = 0 := by
  have : {x : Fin m → ℝ | ∃ i, ∃ S : Finset (Fin m), wsum w S + α * x i = y} =
      ⋃ i, ⋃ S : Finset (Fin m), {x : Fin m → ℝ |
        (α • LinearMap.proj (R := ℝ) (φ := fun _ : Fin m => ℝ) i) x = y - wsum w S} := by
    ext x; simp only [Set.mem_ofPred_eq, Set.mem_iUnion, LinearMap.smul_apply, LinearMap.coe_proj,
      Function.eval, smul_eq_mul]
    constructor
    · rintro ⟨i, S, h⟩; exact ⟨i, S, by linarith⟩
    · rintro ⟨i, S, h⟩; exact ⟨i, S, by linarith⟩
  rw [this]
  refine measure_iUnion_null fun i => measure_iUnion_null fun S => og_hyper_null _ ?_ _
  intro h
  have := LinearMap.congr_fun h (Pi.single i 1)
  simp at this
  exact hα.ne' this

lemma og_allties_null {m : ℕ} :
    volume {x : Fin m → ℝ | ∃ i j, i ≠ j ∧ x i = x j} = 0 := by
  have : {x : Fin m → ℝ | ∃ i j, i ≠ j ∧ x i = x j} = ⋃ i, ⋃ j, ⋃ (_ : i ≠ j),
      {x : Fin m → ℝ | x i = x j} := by
    ext x; simp
  rw [this]
  exact measure_iUnion_null fun i => measure_iUnion_null fun j =>
    measure_iUnion_null fun hij => og_diag_null i j hij

lemma og_pivotSet_meas {m : ℕ} (c α : ℝ) (w : Fin m → ℝ) (i : Fin m) :
    MeasurableSet (pivotSet c α w i) := by
  have hm : Measurable (fun x : Fin m → ℝ => wsum w (pred x (x i))) := by
    have : (fun x : Fin m → ℝ => wsum w (pred x (x i))) =
        fun x => ∑ j, if x j < x i then w j else 0 := by
      funext x; simp [wsum, pred, Finset.sum_filter]
    rw [this]
    apply Finset.measurable_sum
    intro j _
    exact Measurable.ite (measurableSet_lt (measurable_pi_apply j) (measurable_pi_apply i))
      measurable_const measurable_const
  have hxi : Measurable (fun x : Fin m → ℝ => x i) := measurable_pi_apply i
  exact measurableSet_Icc.inter ((measurableSet_le (hm.add (hxi.const_mul α)) measurable_const).inter
    (measurableSet_le measurable_const ((hm.add_const (w i)).add (hxi.const_mul α))))

lemma og_cube_vol (m : ℕ) : volume (cube m) = 1 := by
  unfold cube
  rw [Real.volume_Icc_pi]; simp

theorem eq_4_4_4_5_core {m : ℕ} (α : ℝ) (w : Fin m → ℝ) (hα : 0 < α) (hw : ∀ j, 0 ≤ w j)
    (y : ℝ) (hy0 : 0 < y) (hyW : y < wsum w Finset.univ + α) :
    volume {x | x ∈ cube m ∧ ¬ DifferentiableAt ℝ (fun z => pivotLoc α w x z) y} = 0 ∧
    ∑ i, value y α w i =
      (volume {x | x ∈ cube m ∧ HasDerivAt (fun z => pivotLoc α w x z) 0 y}).toReal ∧
    oceanValue y α w =
      (volume {x | x ∈ cube m ∧ HasDerivAt (fun z => pivotLoc α w x z) (1 / α) y}).toReal := by
  set B := {x : Fin m → ℝ | ∃ i j, i ≠ j ∧ x i = x j} ∪
    {x : Fin m → ℝ | ∃ i, ∃ S : Finset (Fin m), wsum w S + α * x i = y} with hB
  have hBnull : volume B = 0 := measure_union_null og_allties_null (og_hyp_null α hα w y)
  have hgood : ∀ x, x ∉ B → (∀ i j, i ≠ j → x i ≠ x j) ∧
      (∀ i (S : Finset (Fin m)), wsum w S + α * x i ≠ y) := by
    intro x hx
    simp only [hB, Set.mem_union, Set.mem_ofPred_eq, not_or, not_exists, not_and] at hx
    exact ⟨fun i j hij h => hx.1 i j hij h, fun i S h => hx.2 i S h⟩
  -- case A strictness
  have hA : ∀ x, x ∉ B → ∀ i, x ∈ pivotSet y α w i →
      HasDerivAt (fun z => pivotLoc α w x z) 0 y := by
    intro x hx i hpi
    obtain ⟨_, hS⟩ := hgood x hx
    obtain ⟨hc, h1, h2⟩ := hpi
    have hnot : i ∉ pred x (x i) := by simp [pred]
    have e2 : wsum w (insert i (pred x (x i))) = w i + wsum w (pred x (x i)) := by
      unfold wsum; rw [Finset.sum_insert hnot]
    have n1 := hS i (pred x (x i))
    have n2 := hS i (insert i (pred x (x i)))
    apply og_caseA α w hα hw y hyW i x hc (lt_of_le_of_ne h1 n1)
    refine lt_of_le_of_ne h2 ?_
    intro h; apply n2; linarith
  have hBc : ∀ x, x ∉ B → x ∈ cube m → (∀ i, x ∉ pivotSet y α w i) →
      HasDerivAt (fun z => pivotLoc α w x z) (1 / α) y := by
    intro x hx hc hnp
    exact og_caseB α w hα hw y hy0 hyW.le x hc (hgood x hx).1 hnp
  have hdiff : (0:ℝ) ≠ 1 / α := by
    have : 0 < 1 / α := by positivity
    exact this.ne
  have hae : ∀ᵐ x ∂(volume : Measure (Fin m → ℝ)), x ∉ B := measure_eq_zero_iff_ae_notMem.mp hBnull
  set U := ⋃ i, pivotSet y α w i with hU
  have hUsub : U ⊆ cube m := Set.iUnion_subset fun i => fun x hx => hx.1
  have hUmeas : MeasurableSet U := MeasurableSet.iUnion fun i => og_pivotSet_meas y α w i
  have hUfin : volume U ≠ ⊤ := by
    have := measure_mono (μ := volume) hUsub
    rw [og_cube_vol] at this
    exact ne_top_of_le_ne_top ENNReal.one_ne_top this
  have hfin : ∀ i, volume (pivotSet y α w i) ≠ ⊤ := by
    intro i
    have := measure_mono (μ := volume) (Set.subset_iUnion (fun i => pivotSet y α w i) i)
    exact ne_top_of_le_ne_top hUfin this
  have hsum : ∑ i, value y α w i = (volume U).toReal := by
    unfold value
    rw [← ENNReal.toReal_sum (fun i _ => hfin i), hU, measure_iUnion₀, tsum_fintype]
    · intro i j hij
      exact pivotSet_ae_disjoint_core y α w hα hw i j hij
    · intro i; exact (og_pivotSet_meas y α w i).nullMeasurableSet
  have hE0 : volume {x | x ∈ cube m ∧ HasDerivAt (fun z => pivotLoc α w x z) 0 y} = volume U := by
    apply measure_congr
    rw [Filter.eventuallyEq_set]
    filter_upwards [hae] with x hx
    constructor
    · rintro ⟨hc, hd⟩
      by_contra hnu
      simp only [hU, Set.mem_iUnion, not_exists] at hnu
      exact hdiff (hd.unique (hBc x hx hc hnu))
    · intro hu
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hu
      exact ⟨hi.1, hA x hx i hi⟩
  have hE1 : volume {x | x ∈ cube m ∧ HasDerivAt (fun z => pivotLoc α w x z) (1 / α) y} =
      volume (cube m \ U) := by
    apply measure_congr
    rw [Filter.eventuallyEq_set]
    filter_upwards [hae] with x hx
    constructor
    · rintro ⟨hc, hd⟩
      refine ⟨hc, fun hu => ?_⟩
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hu
      exact hdiff ((hA x hx i hi).unique hd)
    · rintro ⟨hc, hnu⟩
      simp only [hU, Set.mem_iUnion, not_exists] at hnu
      exact ⟨hc, hBc x hx hc hnu⟩
  refine ⟨?_, ?_, ?_⟩
  · apply measure_mono_null _ hBnull
    intro x ⟨hc, hnd⟩
    by_contra hx
    apply hnd
    by_cases hu : ∃ i, x ∈ pivotSet y α w i
    · obtain ⟨i, hi⟩ := hu
      exact (hA x hx i hi).differentiableAt
    · push_neg at hu
      exact (hBc x hx hc hu).differentiableAt
  · rw [hsum, hE0]
  · unfold oceanValue
    rw [hsum, hE1, measure_sdiff hUsub hUmeas.nullMeasurableSet hUfin, og_cube_vol,
      ENNReal.toReal_sub_of_le _ ENNReal.one_ne_top]
    · simp
    · have := measure_mono (μ := volume) hUsub
      rwa [og_cube_vol] at this

lemma og_g_le_top {m : ℕ} (α : ℝ) (w : Fin m → ℝ) (hw : ∀ j, 0 ≤ w j) (hα : 0 < α)
    (x : Fin m → ℝ) (hc : x ∈ cube m) (i : Fin m) :
    wsum w (pred x (x i)) + w i + α * x i ≤ wsum w Finset.univ + α := by
  have hnot : i ∉ pred x (x i) := by simp [pred]
  have e1 := og_wsum_mono w hw (Finset.subset_univ (insert i (pred x (x i))))
  have e2 : wsum w (insert i (pred x (x i))) = w i + wsum w (pred x (x i)) := by
    unfold wsum; rw [Finset.sum_insert hnot]
  have h1 : x i ≤ 1 := hc.2 i
  nlinarith

lemma og_caseA' {m : ℕ} (α : ℝ) (w : Fin m → ℝ) (hα : 0 < α) (hw : ∀ j, 0 ≤ w j)
    (y : ℝ) (i : Fin m) (x : Fin m → ℝ)
    (hc : x ∈ cube m) (h1 : wsum w (pred x (x i)) + α * x i < y)
    (h2 : y < wsum w (pred x (x i)) + w i + α * x i) :
    HasDerivAt (fun z => pivotLoc α w x z) 0 y := by
  have htop := og_g_le_top α w hw hα x hc i
  apply (hasDerivAt_const y (x i)).congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds h1, Iio_mem_nhds h2] with z hz1 hz2
  have hz2' : z < wsum w (pred x (x i)) + w i + α * x i := hz2
  exact og_piv_to_loc α w hα hw z (by linarith) i x ⟨hc, le_of_lt hz1, le_of_lt hz2⟩

lemma og_S_nonempty_all {m : ℕ} (α : ℝ) (w : Fin m → ℝ) (hα : 0 < α) (hw : ∀ j, 0 ≤ w j)
    (x : Fin m → ℝ) (z : ℝ) : ({t : ℝ | 0 ≤ t ∧ z ≤ wsum w (pred x t) + α * t}).Nonempty := by
  have h3 : 0 ≤ |z| / α := by positivity
  have h5 : 0 ≤ ∑ j, |x j| := Finset.sum_nonneg (fun j _ => abs_nonneg _)
  refine ⟨|z| / α + ∑ j, |x j| + 1, by positivity, ?_⟩
  have hp : pred x (|z| / α + ∑ j, |x j| + 1) = Finset.univ := by
    ext j; simp only [pred, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
    have h1 : x j ≤ |x j| := le_abs_self _
    have h2 : |x j| ≤ ∑ k, |x k| :=
      Finset.single_le_sum (f := fun k => |x k|) (fun k _ => abs_nonneg _) (Finset.mem_univ j)
    linarith
  rw [hp]
  have hW : 0 ≤ wsum w Finset.univ := Finset.sum_nonneg (fun j _ => hw j)
  have h4 : α * (|z| / α) = |z| := mul_div_cancel₀ _ hα.ne'
  have h6 : z ≤ |z| := le_abs_self z
  nlinarith

lemma og_loc_mono {m : ℕ} (α : ℝ) (w : Fin m → ℝ) (hα : 0 < α) (hw : ∀ j, 0 ≤ w j)
    (x : Fin m → ℝ) {z1 z2 : ℝ} (h : z1 ≤ z2) : pivotLoc α w x z1 ≤ pivotLoc α w x z2 := by
  unfold pivotLoc
  apply csInf_le_csInf (og_S_bdd α w x z1) (og_S_nonempty_all α w hα hw x z2)
  intro t ⟨ht0, ht⟩; exact ⟨ht0, le_trans h ht⟩

lemma og_loc_lip_up {m : ℕ} (α : ℝ) (w : Fin m → ℝ) (hα : 0 < α) (hw : ∀ j, 0 ≤ w j)
    (x : Fin m → ℝ) {z1 z2 : ℝ} (h : z1 ≤ z2) :
    pivotLoc α w x z2 ≤ pivotLoc α w x z1 + (z2 - z1) / α := by
  unfold pivotLoc
  have hd : 0 ≤ (z2 - z1) / α := div_nonneg (by linarith) hα.le
  have key : sInf {t : ℝ | 0 ≤ t ∧ z2 ≤ wsum w (pred x t) + α * t} - (z2 - z1) / α ≤
      sInf {t : ℝ | 0 ≤ t ∧ z1 ≤ wsum w (pred x t) + α * t} := by
    apply le_csInf (og_S_nonempty_all α w hα hw x z1)
    intro t ⟨ht0, ht⟩
    have hmem : t + (z2 - z1) / α ∈ {t : ℝ | 0 ≤ t ∧ z2 ≤ wsum w (pred x t) + α * t} := by
      refine ⟨by linarith, ?_⟩
      have e := og_wsum_mono w hw (og_pred_mono x (le_add_of_nonneg_right hd : t ≤ t + (z2 - z1) / α))
      have h4 : α * ((z2 - z1) / α) = z2 - z1 := mul_div_cancel₀ _ hα.ne'
      have h5 : α * (t + (z2 - z1) / α) = α * t + (z2 - z1) := by rw [mul_add, h4]
      linarith
    have := csInf_le (og_S_bdd α w x z2) hmem
    linarith
  linarith

/-- the extended pivot location -/
noncomputable def ogFt {m : ℕ} (α : ℝ) (w : Fin m → ℝ) (x : Fin m → ℝ) (z : ℝ) : ℝ :=
  pivotLoc α w x z + min z 0 / α

lemma og_ft_lip {m : ℕ} (α : ℝ) (w : Fin m → ℝ) (hα : 0 < α) (hw : ∀ j, 0 ≤ w j)
    (x : Fin m → ℝ) : LipschitzWith (Real.nnabs (2 / α)) (fun z => ogFt α w x z) := by
  rw [Real.nnabs_of_nonneg (by positivity)]
  apply LipschitzWith.of_le_add_mul'
  intro z1 z2
  rw [Real.dist_eq]
  unfold ogFt
  rcases le_total z1 z2 with h | h
  · have := og_loc_mono α w hα hw x h
    have hm : min z1 0 ≤ min z2 0 := min_le_min_right 0 h
    have : min z1 0 / α ≤ min z2 0 / α := div_le_div_of_nonneg_right hm hα.le
    have : 0 ≤ 2 / α * |z1 - z2| := by positivity
    linarith
  · have h1 := og_loc_lip_up α w hα hw x h
    have hm : min z1 0 ≤ min z2 0 + (z1 - z2) := by
      rcases le_total z2 0 with b | b
      · rw [min_eq_left b]; linarith [min_le_left z1 (0:ℝ)]
      · rw [min_eq_right b]; linarith [min_le_right z1 (0:ℝ)]
    have : min z1 0 / α ≤ (min z2 0 + (z1 - z2)) / α := div_le_div_of_nonneg_right hm hα.le
    rw [abs_of_nonneg (by linarith : 0 ≤ z1 - z2)]
    have e : (min z2 0 + (z1 - z2)) / α = min z2 0 / α + (z1 - z2) / α := add_div _ _ _
    have e2 : 2 / α * (z1 - z2) = (z1 - z2) / α + (z1 - z2) / α := by ring
    linarith

lemma og_wsum_pred_meas {m : ℕ} (w : Fin m → ℝ) (t : ℝ) :
    Measurable (fun x : Fin m → ℝ => wsum w (pred x t)) := by
  have : (fun x : Fin m → ℝ => wsum w (pred x t)) =
      fun x => ∑ j, if x j < t then w j else 0 := by
    funext x; simp [wsum, pred, Finset.sum_filter]
  rw [this]
  apply Finset.measurable_sum
  intro j _
  exact Measurable.ite (measurableSet_lt (measurable_pi_apply j) measurable_const)
    measurable_const measurable_const

lemma og_loc_meas {m : ℕ} (α : ℝ) (w : Fin m → ℝ) (hα : 0 < α) (hw : ∀ j, 0 ≤ w j) (z : ℝ) :
    Measurable (fun x : Fin m → ℝ => pivotLoc α w x z) := by
  apply measurable_of_Iio
  intro s
  have : (fun x => pivotLoc α w x z) ⁻¹' Set.Iio s = ⋃ q : ℚ,
      {x : Fin m → ℝ | ((q:ℝ) < s ∧ 0 ≤ (q:ℝ)) ∧ z ≤ wsum w (pred x q) + α * q} := by
    ext x
    simp only [Set.mem_preimage, Set.mem_Iio, Set.mem_iUnion, Set.mem_ofPred_eq]
    constructor
    · intro h
      unfold pivotLoc at h
      obtain ⟨t, ⟨ht0, ht⟩, hts⟩ := exists_lt_of_csInf_lt (og_S_nonempty_all α w hα hw x z) h
      obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn hts
      refine ⟨q, ⟨hq2, by linarith⟩, ?_⟩
      have := og_g_mono α w hw hα x hq1.le
      linarith
    · rintro ⟨q, ⟨hq1, hq0⟩, hq⟩
      unfold pivotLoc
      exact lt_of_le_of_lt (csInf_le (og_S_bdd α w x z) ⟨hq0, hq⟩) hq1
  rw [this]
  exact MeasurableSet.iUnion fun q => (MeasurableSet.const _).inter
    (measurableSet_le measurable_const ((og_wsum_pred_meas w q).add_const _))

lemma og_ocean_eq {m : ℕ} (c α : ℝ) (w : Fin m → ℝ) (hα : 0 < α) (hw : ∀ j, 0 ≤ w j) :
    oceanValue c α w = (volume (cube m \ ⋃ i, pivotSet c α w i)).toReal := by
  set U := ⋃ i, pivotSet c α w i with hU
  have hUsub : U ⊆ cube m := Set.iUnion_subset fun i => fun x hx => hx.1
  have hUmeas : MeasurableSet U := MeasurableSet.iUnion fun i => og_pivotSet_meas c α w i
  have hUfin : volume U ≠ ⊤ := by
    have := measure_mono (μ := volume) hUsub
    rw [og_cube_vol] at this
    exact ne_top_of_le_ne_top ENNReal.one_ne_top this
  have hfin : ∀ i, volume (pivotSet c α w i) ≠ ⊤ := by
    intro i
    have := measure_mono (μ := volume) (Set.subset_iUnion (fun i => pivotSet c α w i) i)
    exact ne_top_of_le_ne_top hUfin this
  have hsum : ∑ i, value c α w i = (volume U).toReal := by
    unfold value
    rw [← ENNReal.toReal_sum (fun i _ => hfin i), hU, measure_iUnion₀, tsum_fintype]
    · intro i j hij
      exact pivotSet_ae_disjoint_core c α w hα hw i j hij
    · intro i; exact (og_pivotSet_meas c α w i).nullMeasurableSet
  unfold oceanValue
  rw [hsum, measure_sdiff hUsub hUmeas.nullMeasurableSet hUfin, og_cube_vol,
    ENNReal.toReal_sub_of_le _ ENNReal.one_ne_top]
  · simp
  · have := measure_mono (μ := volume) hUsub
    rwa [og_cube_vol] at this

lemma og_ae_deriv {m : ℕ} (α : ℝ) (w : Fin m → ℝ) (hα : 0 < α) (hw : ∀ j, 0 ≤ w j)
    (y : ℝ) (hy0 : 0 ≤ y) (hyW : y ≤ wsum w Finset.univ + α) :
    ∀ᵐ x ∂(volume.restrict (cube m)), HasDerivAt (fun z => ogFt α w x z)
      ((⋃ i, pivotSet y α w i)ᶜ.indicator (fun _ => 1 / α) x) y := by
  set B := {x : Fin m → ℝ | ∃ i j, i ≠ j ∧ x i = x j} ∪
    {x : Fin m → ℝ | ∃ i, ∃ S : Finset (Fin m), wsum w S + α * x i = y} with hB
  have hBnull : volume B = 0 := measure_union_null og_allties_null (og_hyp_null α hα w y)
  have hgood : ∀ x, x ∉ B → (∀ i j, i ≠ j → x i ≠ x j) ∧
      (∀ i (S : Finset (Fin m)), wsum w S + α * x i ≠ y) := by
    intro x hx
    simp only [hB, Set.mem_union, Set.mem_ofPred_eq, not_or, not_exists, not_and] at hx
    exact ⟨fun i j hij h => hx.1 i j hij h, fun i S h => hx.2 i S h⟩
  have hae : ∀ᵐ x ∂(volume.restrict (cube m)), x ∉ B :=
    ae_restrict_of_ae (measure_eq_zero_iff_ae_notMem.mp hBnull)
  filter_upwards [hae, ae_restrict_mem (measurableSet_Icc : MeasurableSet (cube m))] with x hx hc
  rcases hy0.eq_or_lt with h0 | hpos
  · have hnU : x ∉ ⋃ i, pivotSet y α w i := by
      intro hu
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hu
      obtain ⟨_, h1, _⟩ := hi
      have hW0 : 0 ≤ wsum w (pred x (x i)) := Finset.sum_nonneg (fun j _ => hw j)
      have hxi : 0 ≤ x i := hc.1 i
      have hne := (hgood x hx).2 i ∅
      apply hne
      have : α * x i ≥ 0 := mul_nonneg hα.le hxi
      simp only [wsum, Finset.sum_empty, zero_add]
      linarith
    rw [Set.indicator_of_mem (Set.mem_compl hnU)]
    have hpos_all : ∀ j, 0 < x j := by
      intro j
      have h1 : (0:ℝ) ≤ x j := hc.1 j
      rcases h1.eq_or_lt with h | h
      · exfalso
        apply (hgood x hx).2 j ∅
        rw [← h, ← h0]; simp [wsum]
      · exact h
    have ev : ∀ᶠ z in 𝓝 y, ogFt α w x z = z / α := by
      have : ∀ᶠ z in 𝓝 y, ∀ j, z < α * x j := by
        rw [Filter.eventually_all]; intro j
        exact Iio_mem_nhds (by rw [← h0]; exact mul_pos hα (hpos_all j))
      filter_upwards [this] with z hz
      unfold ogFt
      rcases le_or_gt z 0 with hz0 | hz0
      · have : pivotLoc α w x z = 0 := by
          unfold pivotLoc; apply IsLeast.csInf_eq
          refine ⟨⟨le_rfl, ?_⟩, fun t ht => ht.1⟩
          have : 0 ≤ wsum w (pred x 0) := Finset.sum_nonneg (fun j _ => hw j)
          linarith
        rw [this, min_eq_left hz0]; ring
      · have hp : pred x (z / α) = ∅ := by
          ext j
          simp only [pred, Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty,
            iff_false, not_lt]
          rw [div_le_iff₀ hα]; linarith [hz j]
        have := og_loc_inv α w hα hw x (t := z / α) (by positivity)
        have e : wsum w ∅ + α * (z / α) = z := by
          simp only [wsum, Finset.sum_empty, zero_add]; exact mul_div_cancel₀ _ hα.ne'
        rw [hp, e] at this
        rw [this, min_eq_right hz0.le]; simp
    exact ((hasDerivAt_id' y).div_const α).congr_of_eventuallyEq ev
  · have hmin : HasDerivAt (fun z : ℝ => min z 0 / α) 0 y := by
      apply (hasDerivAt_const y (0:ℝ)).congr_of_eventuallyEq
      filter_upwards [Ioi_mem_nhds hpos] with z hz
      have hz' : (0:ℝ) < z := hz
      simp [min_eq_right hz'.le]
    by_cases hu : x ∈ ⋃ i, pivotSet y α w i
    · rw [Set.indicator_of_notMem (by simpa using hu)]
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hu
      obtain ⟨_, hS⟩ := hgood x hx
      obtain ⟨_, h1, h2⟩ := hi
      have hnot : i ∉ pred x (x i) := by simp [pred]
      have e2 : wsum w (insert i (pred x (x i))) = w i + wsum w (pred x (x i)) := by
        unfold wsum; rw [Finset.sum_insert hnot]
      have n1 := hS i (pred x (x i))
      have n2 := hS i (insert i (pred x (x i)))
      have hA := og_caseA' α w hα hw y i x hc (lt_of_le_of_ne h1 n1)
        (lt_of_le_of_ne h2 (by intro h; apply n2; linarith))
      have := hA.add hmin
      rw [add_zero] at this
      exact this
    · rw [Set.indicator_of_mem (Set.mem_compl hu)]
      have h2 := og_caseB α w hα hw y hpos hyW x hc (hgood x hx).1 (by simpa using hu)
      have := h2.add hmin
      rw [add_zero] at this
      exact this

lemma og_ft_bound {m : ℕ} (α : ℝ) (w : Fin m → ℝ) (hα : 0 < α) (hw : ∀ j, 0 ≤ w j)
    (x : Fin m → ℝ) (hc : x ∈ cube m) (y : ℝ) : |ogFt α w x y| ≤ 2 * (|y| / α) + 2 := by
  have h0 : 0 ≤ pivotLoc α w x y := le_csInf (og_S_nonempty_all α w hα hw x y) (fun t ht => ht.1)
  have h1 : pivotLoc α w x y ≤ |y| / α + 2 := by
    apply csInf_le (og_S_bdd α w x y)
    have h3 : 0 ≤ |y| / α := by positivity
    refine ⟨by positivity, ?_⟩
    rw [og_pred_big x hc (by linarith : (1:ℝ) < |y| / α + 2)]
    have hW : 0 ≤ wsum w Finset.univ := Finset.sum_nonneg (fun j _ => hw j)
    have h4 : α * (|y| / α) = |y| := mul_div_cancel₀ _ hα.ne'
    have h6 : y ≤ |y| := le_abs_self y
    nlinarith
  have hm1 : -|y| ≤ min y 0 := le_min (neg_abs_le y) (neg_nonpos.mpr (abs_nonneg y))
  have hm2 : min y 0 ≤ 0 := min_le_right _ _
  have a1 : -(|y| / α) ≤ min y 0 / α := by rw [← neg_div]; exact div_le_div_of_nonneg_right hm1 hα.le
  have a2 : min y 0 / α ≤ 0 := div_nonpos_of_nonpos_of_nonneg hm2 hα.le
  have a3 : 0 ≤ |y| / α := by positivity
  unfold ogFt
  rw [abs_le]; constructor <;> linarith

theorem theorem_2_core {m : ℕ} (α : ℝ) (w : Fin m → ℝ) (hα : 0 < α) (hw : ∀ j, 0 ≤ w j)
    (y : ℝ) (hy : y ∈ Set.Icc 0 (wsum w Finset.univ + α)) :
    HasDerivWithinAt (expPivotLoc α w) (oceanValue y α w / α)
      (Set.Icc 0 (wsum w Finset.univ + α)) y := by
  have : IsFiniteMeasure (volume.restrict (cube m)) :=
    ⟨by rw [Measure.restrict_apply_univ, og_cube_vol]; exact ENNReal.one_lt_top⟩
  set U := ⋃ i, pivotSet y α w i with hU
  have hUm : MeasurableSet Uᶜ := (MeasurableSet.iUnion fun i => og_pivotSet_meas y α w i).compl
  have hmeasF : ∀ z, Measurable (fun x => ogFt α w x z) :=
    fun z => (og_loc_meas α w hα hw z).add_const _
  have hint : Integrable (fun x => ogFt α w x y) (volume.restrict (cube m)) :=
    Integrable.of_bound (hmeasF y).aestronglyMeasurable (2 * (|y| / α) + 2)
      ((ae_restrict_mem (measurableSet_Icc : MeasurableSet (cube m))).mono fun x hx => by
        rw [Real.norm_eq_abs]; exact og_ft_bound α w hα hw x hx y)
  have key := hasDerivAt_integral_of_dominated_loc_of_lip (μ := volume.restrict (cube m))
    (F := fun z x => ogFt α w x z) (F' := Uᶜ.indicator (fun _ => 1 / α))
    (bound := fun _ => 2 / α) (x₀ := y) Filter.univ_mem
    (Filter.Eventually.of_forall fun z => (hmeasF z).aestronglyMeasurable) hint
    ((measurable_const.indicator hUm).aestronglyMeasurable)
    (Filter.Eventually.of_forall fun x => (og_ft_lip α w hα hw x).lipschitzOnWith)
    (integrable_const _)
    (og_ae_deriv α w hα hw y hy.1 hy.2)
  have hval : ∫ x, Uᶜ.indicator (fun _ => 1 / α) x ∂(volume.restrict (cube m)) =
      oceanValue y α w / α := by
    rw [integral_indicator_const _ hUm, measureReal_def, Measure.restrict_apply hUm,
      og_ocean_eq y α w hα hw, smul_eq_mul, Set.diff_eq, Set.inter_comm]
    ring
  rw [hval] at key
  apply key.2.hasDerivWithinAt.congr_of_mem _ hy
  intro z hz
  unfold expPivotLoc ogFt
  congr 1
  funext x
  rw [min_eq_right hz.1]; simp

end OceanicGames.Interior

open OceanicGames.Interior


theorem solution {m : ℕ} (α : ℝ) (w : Fin m → ℝ) (hα : 0 < α) (hw : ∀ j, 0 ≤ w j)
    (y : ℝ) (hy : y ∈ Set.Icc 0 (wsum w Finset.univ + α)) :
    HasDerivWithinAt (expPivotLoc α w) (oceanValue y α w / α)
      (Set.Icc 0 (wsum w Finset.univ + α)) y := by
  exact theorem_2_core α w hα hw y hy
