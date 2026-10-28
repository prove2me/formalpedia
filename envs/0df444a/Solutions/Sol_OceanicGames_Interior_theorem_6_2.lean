-- Prove2me | solution 2 for OceanicGames.Interior.theorem_6
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-27T14:24:25.070707+00:00
-- url     : https://prove2.me/submissions/f4ca57c7-5a4a-4ea6-aeff-4271ba111baa

import Mathlib
import Definitions.Def_OceanicGames_Interior_Basic
import Theorems.Thm_OceanicGames_Interior_theorem_2

-- carved verbatim out of submission 7d1028b0-fa4f-472a-8078-e3d322cec56e, lines 1339-1346

section
open MeasureTheory Filter Topology
open OceanicGames
open OceanicGames.Interior

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

lemma og_S_bdd {m : ℕ} (α : ℝ) (w : Fin m → ℝ) (x : Fin m → ℝ) (y : ℝ) :
    BddBelow {t : ℝ | 0 ≤ t ∧ y ≤ wsum w (pred x t) + α * t} := ⟨0, fun t ht => ht.1⟩

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

lemma og_loc_bounds {m : ℕ} (α : ℝ) (w : Fin m → ℝ) (hα : 0 < α) (hw : ∀ j, 0 ≤ w j)
    (x : Fin m → ℝ) (hc : x ∈ cube m) (y : ℝ) :
    0 ≤ pivotLoc α w x y ∧ pivotLoc α w x y ≤ |y| / α + 2 := by
  refine ⟨le_csInf (og_S_nonempty_all α w hα hw x y) (fun t ht => ht.1), ?_⟩
  apply csInf_le (og_S_bdd α w x y)
  have h3 : 0 ≤ |y| / α := by positivity
  refine ⟨by positivity, ?_⟩
  rw [og_pred_big x hc (by linarith : (1:ℝ) < |y| / α + 2)]
  have hW : 0 ≤ wsum w Finset.univ := Finset.sum_nonneg (fun j _ => hw j)
  have h4 : α * (|y| / α) = |y| := mul_div_cancel₀ _ hα.ne'
  have h6 : y ≤ |y| := le_abs_self y
  nlinarith

lemma og_loc_integrable {m : ℕ} (α : ℝ) (w : Fin m → ℝ) (hα : 0 < α) (hw : ∀ j, 0 ≤ w j)
    (y : ℝ) : Integrable (fun x => pivotLoc α w x y) (volume.restrict (cube m)) := by
  have : IsFiniteMeasure (volume.restrict (cube m)) :=
    ⟨by rw [Measure.restrict_apply_univ, og_cube_vol]; exact ENNReal.one_lt_top⟩
  refine Integrable.of_bound (og_loc_meas α w hα hw y).aestronglyMeasurable (|y| / α + 2)
    ((ae_restrict_mem (measurableSet_Icc : MeasurableSet (cube m))).mono fun x hx => ?_)
  obtain ⟨h0, h1⟩ := og_loc_bounds α w hα hw x hx y
  rw [Real.norm_eq_abs, abs_of_nonneg h0]; exact h1

lemma og_below_loc {m : ℕ} (α : ℝ) (w : Fin m → ℝ) (x : Fin m → ℝ) (t s : ℝ) (hs0 : 0 ≤ s)
    (hs : s < pivotLoc α w x t) : wsum w (pred x s) + α * s < t := by
  by_contra h
  push_neg at h
  have := csInf_le (og_S_bdd α w x t) ⟨hs0, h⟩
  unfold pivotLoc at hs
  linarith

lemma og_above_loc {m : ℕ} (α : ℝ) (w : Fin m → ℝ) (hα : 0 < α) (hw : ∀ j, 0 ≤ w j)
    (x : Fin m → ℝ) (t s : ℝ)
    (hs : pivotLoc α w x t < s) : t < wsum w (pred x s) + α * s := by
  unfold pivotLoc at hs
  obtain ⟨u, ⟨_, hu⟩, hus⟩ := exists_lt_of_csInf_lt (og_S_nonempty_all α w hα hw x t) hs
  have := og_g_strict α w hw hα x hus
  linarith

lemma og_loc_nonpos {m : ℕ} (α : ℝ) (w : Fin m → ℝ) (hw : ∀ j, 0 ≤ w j)
    (x : Fin m → ℝ) (hc : x ∈ cube m) (t : ℝ) (ht : t ≤ 0) : pivotLoc α w x t = 0 := by
  unfold pivotLoc; apply IsLeast.csInf_eq
  refine ⟨⟨le_rfl, ?_⟩, fun s hs => hs.1⟩
  have : 0 ≤ wsum w (pred x 0) := Finset.sum_nonneg (fun j _ => hw j)
  linarith

lemma og_loc_top {m : ℕ} (α : ℝ) (w : Fin m → ℝ) (hα : 0 < α) (hw : ∀ j, 0 ≤ w j)
    (x : Fin m → ℝ) (h1 : ∀ j, x j < 1) :
    pivotLoc α w x (wsum w Finset.univ + α) = 1 := by
  unfold pivotLoc; apply IsLeast.csInf_eq
  have hp : pred x 1 = Finset.univ := by
    ext j; simp only [pred, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]; exact h1 j
  refine ⟨⟨by norm_num, by rw [hp]; linarith⟩, fun s ⟨_, hs⟩ => ?_⟩
  by_contra hlt
  push_neg at hlt
  have := og_wsum_mono w hw (Finset.subset_univ (pred x s))
  nlinarith

lemma og_slice_vol {m : ℕ} (α w' : ℝ) (w : Fin m → ℝ) (hα : 0 < α) (hw : ∀ j, 0 ≤ w j)
    (hw' : 0 ≤ w') (z : ℝ) (hz0 : 0 ≤ z) (hzW : z ≤ wsum w Finset.univ + w' + α)
    (x : Fin m → ℝ) (hc : x ∈ cube m) (h1 : ∀ j, x j < 1) :
    volume {s : ℝ | (0 ≤ s ∧ s ≤ 1) ∧ wsum w (pred x s) + α * s ≤ z ∧
        z ≤ wsum w (pred x s) + w' + α * s} =
      ENNReal.ofReal (pivotLoc α w x (min z (wsum w Finset.univ + α)) -
        pivotLoc α w x (max (z - w') 0)) := by
  set B0 := wsum w Finset.univ + α with hB0
  set a := max (z - w') 0 with ha
  set b := min z B0 with hb
  have hFB := og_loc_top α w hα hw x h1
  rw [← hB0] at hFB
  have hFa0 : 0 ≤ pivotLoc α w x a := (og_loc_bounds α w hα hw x hc a).1
  have hFb1 : pivotLoc α w x b ≤ 1 := by
    rw [← hFB]; exact og_loc_mono α w hα hw x (min_le_right _ _)
  have hsub1 : Set.Ioo (pivotLoc α w x a) (pivotLoc α w x b) ⊆ {s : ℝ | (0 ≤ s ∧ s ≤ 1) ∧
      wsum w (pred x s) + α * s ≤ z ∧ z ≤ wsum w (pred x s) + w' + α * s} := by
    intro s ⟨hs1, hs2⟩
    have hs0 : 0 ≤ s := by linarith
    refine ⟨⟨hs0, by linarith⟩, ?_, ?_⟩
    · have := og_below_loc α w x b s hs0 hs2
      have : b ≤ z := min_le_left _ _
      linarith
    · have := og_above_loc α w hα hw x a s hs1
      have : z - w' ≤ a := le_max_left _ _
      linarith
  have hsub2 : {s : ℝ | (0 ≤ s ∧ s ≤ 1) ∧ wsum w (pred x s) + α * s ≤ z ∧
      z ≤ wsum w (pred x s) + w' + α * s} ⊆ Set.Icc (pivotLoc α w x a) (pivotLoc α w x b) := by
    rintro s ⟨⟨hs0, hs1⟩, hg1, hg2⟩
    constructor
    · by_contra hlt
      push_neg at hlt
      rcases le_or_gt (z - w') 0 with hzw | hzw
      · have : a = 0 := max_eq_right hzw
        rw [this, og_loc_nonpos α w hw x hc 0 le_rfl] at hlt
        linarith
      · have : a = z - w' := max_eq_left hzw.le
        rw [this] at hlt
        have := og_below_loc α w x (z - w') s hs0 hlt
        linarith
    · by_contra hlt
      push_neg at hlt
      rcases le_or_gt z B0 with hzB | hzB
      · have : b = z := min_eq_left hzB
        rw [this] at hlt
        have := og_above_loc α w hα hw x z s hlt
        linarith
      · have : b = B0 := min_eq_right hzB.le
        rw [this, hFB] at hlt
        linarith
  apply le_antisymm
  · calc _ ≤ volume (Set.Icc (pivotLoc α w x a) (pivotLoc α w x b)) := measure_mono hsub2
      _ = _ := Real.volume_Icc
  · calc _ = volume (Set.Ioo (pivotLoc α w x a) (pivotLoc α w x b)) := Real.volume_Ioo.symm
      _ ≤ _ := measure_mono hsub1

lemma og_ocean_bounds {m : ℕ} (α : ℝ) (w : Fin m → ℝ) (hα : 0 < α) (hw : ∀ j, 0 ≤ w j) (y : ℝ) :
    0 ≤ oceanValue y α w ∧ oceanValue y α w ≤ 1 := by
  rw [og_ocean_eq y α w hα hw]
  refine ⟨ENNReal.toReal_nonneg, ?_⟩
  have : volume (cube m \ ⋃ i, pivotSet y α w i) ≤ 1 := by
    rw [← og_cube_vol m]; exact measure_mono Set.diff_subset
  have := ENNReal.toReal_mono ENNReal.one_ne_top this
  simpa using this

lemma og_ftc {m : ℕ} (α : ℝ) (w : Fin m → ℝ) (hα : 0 < α) (hw : ∀ j, 0 ≤ w j)
    (a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ wsum w Finset.univ + α) :
    1 / α * ∫ y in a..b, oceanValue y α w = expPivotLoc α w b - expPivotLoc α w a := by
  set B0 := wsum w Finset.univ + α with hB0
  have hd : ∀ y ∈ Set.Icc 0 B0, HasDerivWithinAt (expPivotLoc α w) (oceanValue y α w / α)
      (Set.Icc 0 B0) y := fun y hy => OceanicGames.Interior.theorem_2 α w hα hw y hy
  have hcont : ContinuousOn (expPivotLoc α w) (Set.Icc a b) :=
    fun y hy => ((hd y ⟨ha.trans hy.1, hy.2.trans hb⟩).continuousWithinAt).mono
      (Set.Icc_subset_Icc ha hb)
  have hint_d : ∀ y ∈ Set.Ioo 0 B0, HasDerivAt (expPivotLoc α w) (oceanValue y α w / α) y :=
    fun y hy => (hd y (Set.Ioo_subset_Icc_self hy)).hasDerivAt (Icc_mem_nhds hy.1 hy.2)
  set D := deriv (expPivotLoc α w) with hDdef
  have hD : ∀ y ∈ Set.Ioo 0 B0, D y = oceanValue y α w / α := fun y hy => (hint_d y hy).deriv
  have hsub : Set.Ioo a b ⊆ Set.Ioo 0 B0 := Set.Ioo_subset_Ioo ha hb
  have hDint : IntervalIntegrable D volume a b := by
    rw [intervalIntegrable_iff_integrableOn_Ioo_of_le hab]
    refine IntegrableOn.of_bound (by rw [Real.volume_Ioo]; exact ENNReal.ofReal_lt_top)
      (measurable_deriv _).aestronglyMeasurable (1 / α) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with y hy
    rw [hD y (hsub hy), Real.norm_eq_abs]
    obtain ⟨h0, h1⟩ := og_ocean_bounds α w hα hw y
    rw [abs_of_nonneg (div_nonneg h0 hα.le)]
    exact div_le_div_of_nonneg_right h1 hα.le
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab hcont
    (fun y hy => by rw [hD y (hsub hy)]; exact hint_d y (hsub hy)) hDint
  have hcongr : ∫ y in a..b, oceanValue y α w = ∫ y in a..b, α * D y := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [measure_eq_zero_iff_ae_notMem.mp
      (Real.volume_singleton : volume ({b} : Set ℝ) = 0)] with y hy hyI
    rw [Set.uIoc_of_le hab] at hyI
    have hy' : y ∈ Set.Ioo a b := ⟨hyI.1, lt_of_le_of_ne hyI.2 (by simpa using hy)⟩
    rw [hD y (hsub hy'), mul_div_cancel₀ _ hα.ne']
  rw [hcongr, intervalIntegral.integral_const_mul, hftc, ← mul_assoc, one_div,
    inv_mul_cancel₀ hα.ne', one_mul]

lemma og_ins_mem {m : ℕ} (z α : ℝ) (v : Fin (m + 1) → ℝ) (i : Fin (m + 1)) (x : Fin m → ℝ) (s : ℝ) :
    (Fin.insertNth (α := fun _ => ℝ) i s x : Fin (m + 1) → ℝ) ∈ pivotSet z α v i ↔
      ((0 ≤ s ∧ s ≤ 1) ∧ wsum (fun j => v (i.succAbove j)) (pred x s) + α * s ≤ z ∧
        z ≤ wsum (fun j => v (i.succAbove j)) (pred x s) + v i + α * s) ∧ x ∈ cube m := by
  have hws : wsum v (pred (Fin.insertNth (α := fun _ => ℝ) i s x : Fin (m + 1) → ℝ) s) =
      wsum (fun j => v (i.succAbove j)) (pred x s) := by
    simp only [wsum, pred, Finset.sum_filter]
    rw [Fin.sum_univ_succAbove _ i]
    simp
  have hcube : (Fin.insertNth (α := fun _ => ℝ) i s x : Fin (m + 1) → ℝ) ∈ cube (m + 1) ↔
      (0 ≤ s ∧ s ≤ 1) ∧ x ∈ cube m := by
    simp only [cube, Set.mem_Icc, Pi.le_def, Fin.forall_iff_succAbove i, Fin.insertNth_apply_same,
      Fin.insertNth_apply_succAbove, Pi.zero_apply, Pi.one_apply]
    tauto
  unfold pivotSet
  simp only [Set.mem_ofPred_eq, Fin.insertNth_apply_same, hws, hcube]
  tauto

lemma og_value_gen {m : ℕ} (α : ℝ) (v : Fin (m + 1) → ℝ) (hα : 0 < α) (hv : ∀ j, 0 ≤ v j)
    (i : Fin (m + 1)) (z : ℝ) (hz0 : 0 ≤ z)
    (hzW : z ≤ wsum (fun j => v (i.succAbove j)) Finset.univ + v i + α) :
    value z α v i =
      expPivotLoc α (fun j => v (i.succAbove j))
          (min z (wsum (fun j => v (i.succAbove j)) Finset.univ + α)) -
        expPivotLoc α (fun j => v (i.succAbove j)) (max (z - v i) 0) := by
  set w : Fin m → ℝ := fun j => v (i.succAbove j) with hwdef
  have hw : ∀ j, 0 ≤ w j := fun j => hv _
  have hw' : 0 ≤ v i := hv i
  set A := pivotSet z α v i with hA
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => ℝ) i
  have hmp : MeasurePreserving e volume ((volume : Measure ℝ).prod (volume : Measure (Fin m → ℝ))) :=
    volume_preserving_piFinSuccAbove (fun _ : Fin (m + 1) => ℝ) i
  have hAm : MeasurableSet A := og_pivotSet_meas _ _ _ _
  have h1 : volume A = ((volume : Measure ℝ).prod (volume : Measure (Fin m → ℝ))) (e.symm ⁻¹' A) := by
    rw [← hmp.measure_preimage_equiv]
    congr 1
    ext x; simp
  have hslice : ∀ x : Fin m → ℝ, (fun s : ℝ => (s, x)) ⁻¹' (e.symm ⁻¹' A) =
      {s : ℝ | ((0 ≤ s ∧ s ≤ 1) ∧ wsum w (pred x s) + α * s ≤ z ∧
        z ≤ wsum w (pred x s) + v i + α * s) ∧ x ∈ cube m} := by
    intro x
    ext s
    simp only [Set.mem_preimage, Set.mem_ofPred_eq]
    have : e.symm (s, x) = (Fin.insertNth (α := fun _ => ℝ) i s x : Fin (m + 1) → ℝ) := by
      simp [e, MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv]
    rw [this, hA, og_ins_mem]
  rw [Measure.prod_apply_symm (e.symm.measurable hAm)] at h1
  simp_rw [hslice] at h1
  have hN : volume {x : Fin m → ℝ | ∃ j, x j = 1} = 0 := by
    have : {x : Fin m → ℝ | ∃ j, x j = 1} = ⋃ j, {x : Fin m → ℝ |
        (LinearMap.proj (R := ℝ) (φ := fun _ : Fin m => ℝ) j) x = 1} := by
      ext x; simp
    rw [this]
    refine measure_iUnion_null fun j => og_hyper_null _ ?_ _
    intro h
    have := LinearMap.congr_fun h (Pi.single j 1)
    simp at this
  set f : (Fin m → ℝ) → ℝ := fun x => pivotLoc α w x (min z (wsum w Finset.univ + α)) -
    pivotLoc α w x (max (z - v i) 0) with hf
  have h2 : ∫⁻ x, volume {s : ℝ | ((0 ≤ s ∧ s ≤ 1) ∧ wsum w (pred x s) + α * s ≤ z ∧
        z ≤ wsum w (pred x s) + v i + α * s) ∧ x ∈ cube m} =
      ∫⁻ x, (cube m).indicator (fun x => ENNReal.ofReal (f x)) x := by
    apply lintegral_congr_ae
    filter_upwards [measure_eq_zero_iff_ae_notMem.mp hN] with x hx
    simp only [Set.mem_ofPred_eq, not_exists] at hx
    by_cases hc : x ∈ cube m
    · rw [Set.indicator_of_mem hc]
      have h1' : ∀ j, x j < 1 := fun j => lt_of_le_of_ne (hc.2 j) (hx j)
      have := og_slice_vol α (v i) w hα hw hw' z hz0 hzW x hc h1'
      simp only [hc, and_true]
      exact this
    · rw [Set.indicator_of_notMem hc]
      simp [hc]
  rw [h2, lintegral_indicator (show MeasurableSet (cube m) from measurableSet_Icc)] at h1
  have hfint : Integrable f (volume.restrict (cube m)) :=
    (og_loc_integrable α w hα hw _).sub (og_loc_integrable α w hα hw _)
  have hfnn : 0 ≤ᵐ[volume.restrict (cube m)] f := by
    filter_upwards with x
    simp only [hf, Pi.zero_apply, sub_nonneg]
    apply og_loc_mono α w hα hw x
    apply le_min
    · exact max_le (by linarith) hz0
    · apply max_le (by linarith)
      have : 0 ≤ wsum w Finset.univ := Finset.sum_nonneg (fun j _ => hw j)
      linarith
  rw [← ofReal_integral_eq_lintegral_ofReal hfint hfnn] at h1
  unfold value
  rw [← hA, h1, ENNReal.toReal_ofReal (integral_nonneg_of_ae hfnn)]
  unfold expPivotLoc
  rw [hf, integral_sub (og_loc_integrable α w hα hw _) (og_loc_integrable α w hα hw _)]

lemma og_wsum_succAbove {m : ℕ} (v : Fin (m + 1) → ℝ) (i : Fin (m + 1)) :
    wsum v Finset.univ = wsum (fun j => v (i.succAbove j)) Finset.univ + v i := by
  unfold wsum; rw [Fin.sum_univ_succAbove _ i]; ring

lemma og_EF_contOn {m : ℕ} (α : ℝ) (w : Fin m → ℝ) (hα : 0 < α) (hw : ∀ j, 0 ≤ w j) :
    ContinuousOn (expPivotLoc α w) (Set.Icc 0 (wsum w Finset.univ + α)) :=
  fun y hy => (OceanicGames.Interior.theorem_2 α w hα hw y hy).continuousWithinAt

lemma og_EF_derivGE {m : ℕ} (α : ℝ) (w : Fin m → ℝ) (hα : 0 < α) (hw : ∀ j, 0 ≤ w j)
    (x : ℝ) (hx0 : 0 ≤ x) (hxB : x < wsum w Finset.univ + α) :
    HasDerivWithinAt (expPivotLoc α w) (oceanValue x α w / α) (Set.Ici x) x := by
  apply (OceanicGames.Interior.theorem_2 α w hα hw x ⟨hx0, hxB.le⟩).mono_of_mem_nhdsWithin
  exact Filter.mem_of_superset (Icc_mem_nhdsGE hxB) (Set.Icc_subset_Icc hx0 le_rfl)

theorem og_ocean_const : ∀ (m : ℕ) (w : Fin m → ℝ) (α : ℝ), 0 < α → (∀ j, 0 ≤ w j) →
    ∀ y1 y2, y1 ∈ Set.Icc (wsum w Finset.univ) α → y2 ∈ Set.Icc (wsum w Finset.univ) α →
    oceanValue y1 α w = oceanValue y2 α w := by
  intro m
  induction m with
  | zero => intro w α _ _ y1 y2 _ _; simp [oceanValue]
  | succ m ih =>
    intro v α hα hv y1 y2 hy1 hy2
    unfold oceanValue
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    set u : Fin m → ℝ := fun j => v (i.succAbove j) with hu
    have hu0 : ∀ j, 0 ≤ u j := fun j => hv _
    have hWu : 0 ≤ wsum u Finset.univ := Finset.sum_nonneg (fun j _ => hu0 j)
    have hWv := og_wsum_succAbove v i
    rw [← hu] at hWv
    have hvi := hv i
    set H : ℝ → ℝ := fun y => expPivotLoc α u y - expPivotLoc α u (y - v i) with hH
    have hval : ∀ y ∈ Set.Icc (wsum v Finset.univ) α, value y α v i = H y := by
      intro y hy
      have := og_value_gen α v hα hv i y (by linarith [hy.1]) (by rw [← hu]; linarith [hy.2])
      rw [this, ← hu, min_eq_left (by linarith [hy.2]), max_eq_left (by linarith [hy.1])]
    have hcont : ContinuousOn H (Set.Icc (wsum v Finset.univ) α) := by
      have hc := og_EF_contOn α u hα hu0
      apply ContinuousOn.sub
      · exact hc.mono (Set.Icc_subset_Icc (by linarith) (by linarith))
      · refine hc.comp (continuousOn_id.sub continuousOn_const) ?_
        intro y hy
        simp only [id]
        exact ⟨by linarith [hy.1], by linarith [hy.2]⟩
    have hderiv : ∀ x ∈ Set.Ico (wsum v Finset.univ) α, HasDerivWithinAt H 0 (Set.Ici x) x := by
      intro x hx
      have d1 := og_EF_derivGE α u hα hu0 x (by linarith [hx.1]) (by linarith [hx.2])
      have d2 := og_EF_derivGE α u hα hu0 (x - v i) (by linarith [hx.1]) (by linarith [hx.2])
      have d3 : HasDerivWithinAt (fun y : ℝ => y - v i) 1 (Set.Ici x) x :=
        ((hasDerivAt_id' x).sub_const (v i)).hasDerivWithinAt
      have d4 := d2.comp x d3 (fun y hy => by simp only [Set.mem_Ici] at hy ⊢; linarith)
      have hd := d1.sub d4
      have heq : oceanValue x α u = oceanValue (x - v i) α u :=
        ih u α hα hu0 x (x - v i) ⟨by linarith [hx.1], by linarith [hx.2]⟩
          ⟨by linarith [hx.1], by linarith [hx.2]⟩
      rw [heq, mul_one, sub_self] at hd
      exact hd
    have hconst := constant_of_has_deriv_right_zero hcont hderiv
    rw [hval y1 hy1, hval y2 hy2, hconst y1 hy1, hconst y2 hy2]

lemma og_value_interior {m : ℕ} (c α : ℝ) (v : Fin (m + 1) → ℝ) (hα : 0 < α)
    (hv : ∀ j, 0 ≤ v j) (hint : IsInterior c α v) (i : Fin (m + 1)) :
    value c α v i = v i / α * oceanValue c α (fun j => v (i.succAbove j)) := by
  set u : Fin m → ℝ := fun j => v (i.succAbove j) with hu
  have hu0 : ∀ j, 0 ≤ u j := fun j => hv _
  have hWu : 0 ≤ wsum u Finset.univ := Finset.sum_nonneg (fun j _ => hu0 j)
  have hWv := og_wsum_succAbove v i
  rw [← hu] at hWv
  have hvi := hv i
  obtain ⟨hc1, hc2⟩ := hint
  have h1 := og_value_gen α v hα hv i c (by linarith) (by rw [← hu]; linarith)
  rw [← hu, min_eq_left (by linarith), max_eq_left (by linarith)] at h1
  have h2 := og_ftc α u hα hu0 (c - v i) c (by linarith) (by linarith) (by linarith)
  rw [h1, ← h2]
  have hcongr : ∫ y in (c - v i)..c, oceanValue y α u = ∫ _ in (c - v i)..c, oceanValue c α u := by
    apply intervalIntegral.integral_congr
    intro y hy
    rw [Set.uIcc_of_le (by linarith)] at hy
    exact og_ocean_const m u α hα hu0 y c ⟨by linarith [hy.1], by linarith [hy.2]⟩
      ⟨by linarith, hc2⟩
  rw [hcongr, intervalIntegral.integral_const, smul_eq_mul]
  ring

lemma og_reindex {m : ℕ} (α : ℝ) (v : Fin (m + 1) → ℝ) (i : Fin (m + 1)) :
    ∑ S ∈ (Finset.univ : Finset (Fin m)).powerset,
        (coeff S.card : ℝ) * piProd α (fun j => v (i.succAbove j)) S =
      ∑ S ∈ (Finset.univ.erase i).powerset, (coeff S.card : ℝ) * piProdErase α v i S := by
  simp only [piProd, piProdErase]
  have hU : (Finset.univ : Finset (Fin (m + 1))).erase i = Finset.univ.image i.succAbove := by
    rw [Fin.image_succAbove_univ]; ext k; simp
  have hinj : Function.Injective i.succAbove := Fin.succAbove_right_injective
  rw [hU, Finset.powerset_image, Finset.sum_image
    (fun S _ T _ h => Finset.image_injective hinj h)]
  apply Finset.sum_congr rfl
  intro S _
  rw [Finset.card_image_of_injective _ hinj, ← Finset.image_sdiff _ _ hinj,
    Finset.prod_image (fun a _ b _ h => hinj h), Finset.prod_image (fun a _ b _ h => hinj h)]

lemma og_alg {n : ℕ} (α : ℝ) (hα : α ≠ 0) (v : Fin n → ℝ) :
    1 - ∑ i, v i / α * ∑ S ∈ (Finset.univ.erase i).powerset,
        (coeff S.card : ℝ) * piProdErase α v i S =
      ∑ T ∈ (Finset.univ : Finset (Fin n)).powerset, (coeff T.card : ℝ) * piProd α v T := by
  have hone : ∑ T ∈ (Finset.univ : Finset (Fin n)).powerset, piProd α v T = 1 := by
    unfold piProd
    rw [← Finset.prod_add]
    apply Finset.prod_eq_one
    intro j _
    field_simp
    ring
  have hstep : ∀ i, v i / α * ∑ S ∈ (Finset.univ.erase i).powerset,
      (coeff S.card : ℝ) * piProdErase α v i S =
      ∑ T ∈ (Finset.univ : Finset (Fin n)).powerset,
        if i ∈ T then (coeff (T.card - 1) : ℝ) * piProd α v T else 0 := by
    intro i
    rw [Finset.mul_sum]
    have hnot : i ∉ (Finset.univ : Finset (Fin n)).erase i := Finset.notMem_erase i _
    rw [show (Finset.univ : Finset (Fin n)).powerset = (insert i (Finset.univ.erase i)).powerset by
      rw [Finset.insert_erase (Finset.mem_univ i)], Finset.sum_powerset_insert hnot]
    rw [Finset.sum_eq_zero (fun T hT => if_neg (fun h => hnot (Finset.mem_powerset.mp hT h))),
      zero_add]
    apply Finset.sum_congr rfl
    intro S hS
    rw [if_pos (Finset.mem_insert_self i S)]
    have hiS : i ∉ S := fun h => hnot (Finset.mem_powerset.mp hS h)
    rw [Finset.card_insert_of_notMem hiS, Nat.add_sub_cancel]
    unfold piProd piProdErase
    rw [Finset.prod_insert hiS]
    have : Finset.univ \ insert i S = (Finset.univ.erase i) \ S := by
      ext k; simp only [Finset.mem_sdiff, Finset.mem_univ, Finset.mem_insert, Finset.mem_erase,
        true_and]; tauto
    rw [this]; ring
  rw [Finset.sum_congr rfl (fun i _ => hstep i), Finset.sum_comm]
  simp_rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul]
  rw [← hone, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro T _
  cases hk : T.card with
  | zero => simp [coeff]
  | succ k =>
    simp only [coeff, Nat.add_sub_cancel]
    push_cast
    ring

theorem og_ocean_formula : ∀ (m : ℕ) (c α : ℝ) (w : Fin m → ℝ), 0 < α → (∀ j, 0 ≤ w j) →
    IsInterior c α w →
    oceanValue c α w =
      ∑ S ∈ (Finset.univ : Finset (Fin m)).powerset, (coeff S.card : ℝ) * piProd α w S := by
  intro m
  induction m with
  | zero => intro c α w _ _ _; simp [oceanValue, coeff, piProd]
  | succ m ih =>
    intro c α v hα hv hint
    have hW := fun i => og_wsum_succAbove v i
    have hval : ∀ i, value c α v i = v i / α * ∑ S ∈ (Finset.univ.erase i).powerset,
        (coeff S.card : ℝ) * piProdErase α v i S := by
      intro i
      rw [og_value_interior c α v hα hv hint i, ← og_reindex α v i,
        ih c α _ hα (fun j => hv _) ⟨by linarith [hW i, hv i, hint.1], hint.2⟩]
    rw [← og_alg α hα.ne' v]
    unfold oceanValue
    rw [Finset.sum_congr rfl (fun i _ => hval i)]

theorem theorem_6_core {m : ℕ} (c α : ℝ) (w : Fin m → ℝ) (hα : 0 < α) (hw : ∀ j, 0 ≤ w j)
    (hint : IsInterior c α w) :
    (∀ i, value c α w i =
      w i / α * ∑ S ∈ (Finset.univ.erase i).powerset, (coeff S.card : ℝ) * piProdErase α w i S) ∧
    oceanValue c α w =
      ∑ S ∈ (Finset.univ : Finset (Fin m)).powerset, (coeff S.card : ℝ) * piProd α w S := by
  refine ⟨?_, og_ocean_formula m c α w hα hw hint⟩
  intro i
  cases m with
  | zero => exact i.elim0
  | succ k =>
    have hW := og_wsum_succAbove w i
    rw [og_value_interior c α w hα hw hint i, ← og_reindex α w i,
      og_ocean_formula k c α _ hα (fun j => hw _) ⟨by linarith [hw i, hint.1], hint.2⟩]

end

section
open MeasureTheory Filter Topology
open OceanicGames.Interior

theorem solution {m : ℕ} (c α : ℝ) (w : Fin m → ℝ) (hα : 0 < α) (hw : ∀ j, 0 ≤ w j)
    (hint : IsInterior c α w) :
    (∀ i, value c α w i =
      w i / α * ∑ S ∈ (Finset.univ.erase i).powerset, (coeff S.card : ℝ) * piProdErase α w i S) ∧
    oceanValue c α w =
      ∑ S ∈ (Finset.univ : Finset (Fin m)).powerset, (coeff S.card : ℝ) * piProd α w S := by
  exact theorem_6_core c α w hα hw hint

end
