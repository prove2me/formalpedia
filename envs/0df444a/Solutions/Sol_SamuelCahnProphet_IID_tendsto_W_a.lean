-- Prove2me | solution 1 for SamuelCahnProphet.IID.tendsto_W_a
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-06T14:17:18.615653+00:00
-- url     : https://prove2.me/submissions/fcd86abe-b76e-4b39-b465-3c2e41955bdc

import Mathlib
import Definitions.Def_SamuelCahnProphet_IID_Setting

open MeasureTheory Filter Topology
open SamuelCahnProphet.IID

lemma scp2_prod_range (q A : ENNReal) (i : ℕ) : ∀ N : ℕ, i < N →
    ∏ m ∈ Finset.range N, (if m < i then q else if m = i then A else 1) = q ^ i * A := by
  intro N
  induction N with
  | zero => intro h; omega
  | succ N ih =>
    intro h
    rw [Finset.prod_range_succ]
    rcases Nat.lt_or_ge i N with hi | hi
    · rw [ih hi]
      have h1 : ¬ N < i := by omega
      have h2 : N ≠ i := by omega
      simp [h1, h2]
    · have hiN : i = N := by omega
      subst hiN
      have : ∀ m ∈ Finset.range i, (if m < i then q else if m = i then A else 1) = q := by
        intro m hm; simp [Finset.mem_range.1 hm]
      rw [Finset.prod_congr rfl this]
      simp

lemma scp2_pi_prod {N : ℕ} (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (g : Fin N → ℝ → ENNReal) (hg : ∀ j, Measurable (g j)) :
    ∫⁻ x, ∏ j, g j (x j) ∂(Measure.pi fun _ : Fin N => μ) = ∏ j, ∫⁻ y, g j y ∂μ := by
  have hind : ProbabilityTheory.iIndepFun (fun j (x : Fin N → ℝ) => g j (x j))
      (Measure.pi fun _ : Fin N => μ) :=
    ProbabilityTheory.iIndepFun_pi (μ := fun _ : Fin N => μ) (X := fun j y => g j y)
      (fun j => (hg j).aemeasurable)
  rw [ProbabilityTheory.lintegral_prod_eq_prod_lintegral_of_indepFun Finset.univ _ hind
    (fun j => (hg j).comp (measurable_pi_apply j))]
  congr 1; funext j
  exact (measurePreserving_eval (fun _ : Fin N => μ) j).lintegral_comp (hg j)

/-- General formula for a one-sided threshold-type stopping rule on i.i.d. coordinates. -/
lemma scp2_stop_formula {N : ℕ} [NeZero N] (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (S : Set ℝ) (hS : MeasurableSet S) (τ : (Fin N → ℝ) → Fin N)
    (hτ : ∀ x i, τ x = i ↔ (∀ j, j < i → x j ∉ S) ∧ (x i ∈ S ∨ i = ⊤)) :
    ∫⁻ x, ENNReal.ofReal (x (τ x)) ∂(Measure.pi fun _ : Fin N => μ) =
      (∑ i ∈ Finset.range (N - 1), μ Sᶜ ^ i) * ∫⁻ y, S.indicator (fun y => ENNReal.ofReal y) y ∂μ
        + μ Sᶜ ^ (N - 1) * ∫⁻ y, ENNReal.ofReal y ∂μ := by
  classical
  set g : Fin N → Fin N → ℝ → ENNReal := fun i j y =>
    if j < i then Sᶜ.indicator 1 y else if j = i then
      (if i = ⊤ then ENNReal.ofReal y else S.indicator (fun y => ENNReal.ofReal y) y) else 1
    with hgdef
  have hgm : ∀ i j, Measurable (g i j) := by
    intro i j
    simp only [hgdef]
    split_ifs
    · exact measurable_one.indicator hS.compl
    · exact ENNReal.measurable_ofReal
    · exact ENNReal.measurable_ofReal.indicator hS
    · exact measurable_const
  have hpt : ∀ x : Fin N → ℝ, ENNReal.ofReal (x (τ x)) = ∑ i, ∏ j, g i j (x j) := by
    intro x
    rw [Finset.sum_eq_single (τ x)]
    · rw [Finset.prod_eq_single (τ x)]
      · simp only [hgdef, lt_irrefl, if_false, if_true]
        split_ifs with h
        · rfl
        · have := ((hτ x (τ x)).1 rfl).2
          rcases this with h' | h'
          · simp [Set.indicator_of_mem h']
          · exact absurd h' h
      · intro j _ hj
        have hτx := ((hτ x (τ x)).1 rfl).1
        simp only [hgdef, hj, if_false]
        split_ifs with hlt
        · simp [Set.indicator_of_mem (show x j ∈ Sᶜ from hτx j hlt)]
        · rfl
      · simp
    · intro i _ hi
      have hnot : ¬ ((∀ j, j < i → x j ∉ S) ∧ (x i ∈ S ∨ i = ⊤)) := fun h =>
        hi ((hτ x i).2 h).symm
      rw [not_and_or] at hnot
      rcases hnot with h | h
      · push Not at h
        obtain ⟨j, hj, hjS⟩ := h
        apply Finset.prod_eq_zero (Finset.mem_univ j)
        simp [hgdef, hj, Set.indicator_of_notMem (show x j ∉ Sᶜ from fun h => h hjS)]
      · push Not at h
        apply Finset.prod_eq_zero (Finset.mem_univ i)
        simp [hgdef, h.2, Set.indicator_of_notMem h.1]
    · simp
  simp_rw [hpt]
  rw [lintegral_finsetSum]
  swap
  · intro i _
    exact Finset.measurable_prod _ (fun j _ =>
      ((hgm i j).comp (measurable_pi_apply j) : Measurable (fun x : Fin N → ℝ => g i j (x j))))
  simp_rw [scp2_pi_prod μ _ (hgm _)]
  -- compute each product
  set A := ∫⁻ y, S.indicator (fun y => ENNReal.ofReal y) y ∂μ
  set B := ∫⁻ y, ENNReal.ofReal y ∂μ
  set q := μ Sᶜ
  have hint : ∀ i j : Fin N, ∫⁻ y, g i j y ∂μ =
      if j < i then q else if j = i then (if i = ⊤ then B else A) else 1 := by
    intro i j
    simp only [hgdef]
    split_ifs
    · rw [lintegral_indicator hS.compl]; simp [q]
    · rfl
    · rfl
    · simp
  simp_rw [hint]
  have hprod : ∀ i : Fin N, (∏ j : Fin N, (if j < i then q else if j = i then
      (if i = ⊤ then B else A) else 1)) = q ^ (i : ℕ) * (if i = ⊤ then B else A) := by
    intro i
    have := Fin.prod_univ_eq_prod_range (fun m => if m < (i : ℕ) then q else if m = (i : ℕ) then
      (if i = ⊤ then B else A) else 1) N
    rw [← scp2_prod_range q _ i N i.isLt, ← this]
    apply Finset.prod_congr rfl
    intro j _
    simp only [Fin.lt_def, Fin.ext_iff]
  simp_rw [hprod]
  have hN : N = N - 1 + 1 := (Nat.succ_pred_eq_of_pos (Nat.pos_of_ne_zero (NeZero.ne N))).symm
  have := Fin.sum_univ_eq_sum_range (fun m => q ^ m * (if m = N - 1 then B else A)) N
  have hcongr : ∀ i : Fin N, q ^ (i : ℕ) * (if i = ⊤ then B else A) =
      q ^ (i : ℕ) * (if (i : ℕ) = N - 1 then B else A) := by
    intro i; congr 2; simp [Fin.ext_iff, Fin.val_top]
  simp_rw [hcongr]
  rw [this]
  rw [show Finset.range N = Finset.range (N - 1 + 1) by rw [← hN]]
  rw [Finset.sum_range_succ, Finset.sum_mul]
  rw [if_pos rfl]
  congr 1
  apply Finset.sum_congr rfl
  intro m hm
  have : m ≠ N - 1 := by have := Finset.mem_range.1 hm; omega
  simp [this]

lemma scp2_min'_iff {N : ℕ} [NeZero N] (p : Fin N → Prop) [DecidablePred p] (i : Fin N)
    (h : (Finset.univ.filter (fun j : Fin N => p j ∨ j = ⊤)).Nonempty) :
    (Finset.univ.filter (fun j : Fin N => p j ∨ j = ⊤)).min' h = i ↔
      (∀ j, j < i → ¬ p j) ∧ (p i ∨ i = ⊤) := by
  constructor
  · rintro rfl
    refine ⟨fun j hj hpj => ?_, ?_⟩
    · have := Finset.min'_le (Finset.univ.filter (fun j : Fin N => p j ∨ j = ⊤)) j (by rw [Finset.mem_filter]; exact ⟨Finset.mem_univ _, Or.inl hpj⟩)
      exact absurd hj (not_lt.2 this)
    · have := Finset.min'_mem _ h
      rw [Finset.mem_filter] at this
      exact this.2
  · rintro ⟨h1, h2⟩
    apply le_antisymm
    · exact Finset.min'_le (Finset.univ.filter (fun j : Fin N => p j ∨ j = ⊤)) i (by rw [Finset.mem_filter]; exact ⟨Finset.mem_univ _, h2⟩)
    · apply Finset.le_min'
      intro j hj
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
      by_contra hlt
      push Not at hlt
      rcases hj with hj | hj
      · exact h1 j hlt hj
      · subst hj; exact absurd hlt (not_lt.2 le_top)

lemma scp2_tIdx_iff {N : ℕ} [NeZero N] (x : Fin N → ℝ) (c : ℝ) (i : Fin N) :
    tIdx x c = i ↔ (∀ j, j < i → x j ∉ Set.Ici c) ∧ (x i ∈ Set.Ici c ∨ i = ⊤) := by
  unfold tIdx
  have := scp2_min'_iff (fun j => c ≤ x j) i ⟨⊤, by simp⟩
  simp only [Set.mem_Ici]
  exact this

lemma scp2_sIdx_iff {N : ℕ} [NeZero N] (x : Fin N → ℝ) (c : ℝ) (i : Fin N) :
    sIdx x c = i ↔ (∀ j, j < i → x j ∉ Set.Ioi c) ∧ (x i ∈ Set.Ioi c ∨ i = ⊤) := by
  unfold sIdx
  have := scp2_min'_iff (fun j => c < x j) i ⟨⊤, by simp⟩
  simp only [Set.mem_Ioi]
  exact this

lemma scp2_EstopT_formula {N : ℕ} [NeZero N] (μ : Measure ℝ) [IsProbabilityMeasure μ] (c : ℝ) :
    EstopT μ N c =
      (∑ i ∈ Finset.range (N - 1), μ (Set.Ici c)ᶜ ^ i) *
          ∫⁻ y, (Set.Ici c).indicator (fun y => ENNReal.ofReal y) y ∂μ
        + μ (Set.Ici c)ᶜ ^ (N - 1) * ∫⁻ y, ENNReal.ofReal y ∂μ :=
  scp2_stop_formula μ _ measurableSet_Ici (fun x => tIdx x c) (fun x i => scp2_tIdx_iff x c i)

lemma scp2_EstopS_formula {N : ℕ} [NeZero N] (μ : Measure ℝ) [IsProbabilityMeasure μ] (c : ℝ) :
    EstopS μ N c =
      (∑ i ∈ Finset.range (N - 1), μ (Set.Ioi c)ᶜ ^ i) *
          ∫⁻ y, (Set.Ioi c).indicator (fun y => ENNReal.ofReal y) y ∂μ
        + μ (Set.Ioi c)ᶜ ^ (N - 1) * ∫⁻ y, ENNReal.ofReal y ∂μ :=
  scp2_stop_formula μ _ measurableSet_Ioi (fun x => sIdx x c) (fun x i => scp2_sIdx_iff x c i)

lemma scp2_lintegral_threePoint (n a b c : ℝ) (f : ℝ → ENNReal) :
    ∫⁻ y, f y ∂(threePoint n a b c) = ENNReal.ofReal (1 - (b + c) / n) * f 0 +
      ENNReal.ofReal (c / n) * f a + ENNReal.ofReal (b / n) * f 1 := by
  simp [threePoint, lintegral_add_measure, lintegral_smul_measure, lintegral_dirac]

lemma scp2_threePoint_apply (n a b c : ℝ) (s : Set ℝ) (hs : MeasurableSet s) :
    threePoint n a b c s = ENNReal.ofReal (1 - (b + c) / n) * s.indicator 1 0 +
      ENNReal.ofReal (c / n) * s.indicator 1 a + ENNReal.ofReal (b / n) * s.indicator 1 1 := by
  simp only [threePoint, Measure.add_apply, Measure.smul_apply, smul_eq_mul,
    Measure.dirac_apply' _ hs]

lemma scp2_threePoint_prob (n a b c : ℝ) (hn : 0 < n) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hbc : b + c ≤ n) : IsProbabilityMeasure (threePoint n a b c) := by
  constructor
  simp only [threePoint, Measure.add_apply, Measure.smul_apply, measure_univ, smul_eq_mul, mul_one]
  have h1 : 0 ≤ 1 - (b + c) / n := by
    rw [sub_nonneg, div_le_one hn]; exact hbc
  rw [← ENNReal.ofReal_add h1 (by positivity), ← ENNReal.ofReal_add (by positivity) (by positivity)]
  rw [show 1 - (b + c) / n + c / n + b / n = 1 by field_simp; ring]
  simp

lemma scp2_pow_tendsto (s : ℝ) :
    Tendsto (fun k : ℕ => (1 - s / ((k + 1 : ℕ) : ℝ)) ^ k) atTop (𝓝 (Real.exp (-s))) := by
  have h0 : Tendsto (fun k : ℕ => s / ((k + 1 : ℕ) : ℝ)) atTop (𝓝 0) :=
    (tendsto_const_div_atTop_nhds_zero_nat s).comp (tendsto_add_atTop_nat 1)
  have h1 : Tendsto (fun k : ℕ => (1 + (-s) / ((k + 1 : ℕ) : ℝ)) ^ (k + 1)) atTop
      (𝓝 (Real.exp (-s))) :=
    (Real.tendsto_one_add_div_pow_exp (-s)).comp (tendsto_add_atTop_nat 1)
  have h2 : Tendsto (fun k : ℕ => 1 - s / ((k + 1 : ℕ) : ℝ)) atTop (𝓝 1) := by
    simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub h0
  have h3 := h1.div h2 one_ne_zero
  rw [div_one] at h3
  refine h3.congr' ?_
  have hev : ∀ᶠ k : ℕ in atTop, 1 - s / ((k + 1 : ℕ) : ℝ) ≠ 0 :=
    h2.eventually (isOpen_ne.mem_nhds one_ne_zero)
  filter_upwards [hev] with k hk
  simp only [Pi.div_apply]
  rw [neg_div, ← sub_eq_add_neg, pow_succ, mul_div_cancel_right₀ _ hk]

lemma scp2_toReal_formula (r A B : ℝ) (hr : 0 ≤ r) (hA : 0 ≤ A) (hB : 0 ≤ B) (k : ℕ) :
    ((∑ x ∈ Finset.range k, ENNReal.ofReal r ^ x) * ENNReal.ofReal A +
      ENNReal.ofReal r ^ k * ENNReal.ofReal B).toReal =
      (∑ x ∈ Finset.range k, r ^ x) * A + r ^ k * B := by
  have hs : (∑ x ∈ Finset.range k, ENNReal.ofReal r ^ x) =
      ENNReal.ofReal (∑ x ∈ Finset.range k, r ^ x) := by
    rw [ENNReal.ofReal_sum_of_nonneg (fun i _ => pow_nonneg hr i)]
    simp [ENNReal.ofReal_pow hr]
  rw [hs, ← ENNReal.ofReal_pow hr, ← ENNReal.ofReal_mul (Finset.sum_nonneg fun i _ => pow_nonneg hr i),
    ← ENNReal.ofReal_mul (pow_nonneg hr k), ← ENNReal.ofReal_add (by positivity) (by positivity),
    ENNReal.toReal_ofReal (by positivity)]

lemma scp2_div_tendsto (s : ℝ) :
    Tendsto (fun k : ℕ => s / ((k + 1 : ℕ) : ℝ)) atTop (𝓝 0) :=
  (tendsto_const_div_atTop_nhds_zero_nat s).comp (tendsto_add_atTop_nat 1)

theorem solution (a b c : ℝ) (ha : 0 < a) (ha1 : a < 1) (hb : 0 < b) (hc : 0 < c) :
    Tendsto (fun k : ℕ => (EstopT (threePoint ((k + 1 : ℕ) : ℝ) a b c) (k + 1) a).toReal) atTop
      (𝓝 ((1 - Real.exp (-b - c)) * (b + a * c) / (b + c))) := by
  have hbc0 : 0 < b + c := by linarith
  have hlim : Tendsto (fun k : ℕ => (1 - (1 - (b + c) / ((k + 1 : ℕ) : ℝ)) ^ k) * ((a * c + b) / (b + c)) +
      (1 - (b + c) / ((k + 1 : ℕ) : ℝ)) ^ k * ((a * c + b) / ((k + 1 : ℕ) : ℝ))) atTop
      (𝓝 ((1 - Real.exp (-b - c)) * (b + a * c) / (b + c))) := by
    have := (((tendsto_const_nhds (x := (1 : ℝ))).sub (scp2_pow_tendsto (b + c))).mul
      (tendsto_const_nhds (x := (a * c + b) / (b + c)))).add
      ((scp2_pow_tendsto (b + c)).mul (scp2_div_tendsto (a * c + b)))
    convert this using 2
    rw [show -b - c = -(b + c) by ring]
    ring
  refine hlim.congr' ?_
  have hev : ∀ᶠ k : ℕ in atTop, b + c < ((k + 1 : ℕ) : ℝ) := by
    obtain ⟨N, hN⟩ := exists_nat_gt (b + c)
    filter_upwards [eventually_ge_atTop N] with k hk
    have : (N : ℝ) ≤ k := by exact_mod_cast hk
    push_cast; linarith
  filter_upwards [hev] with k hk
  set n : ℝ := ((k + 1 : ℕ) : ℝ) with hn
  have hnpos : 0 < n := by positivity
  have := scp2_threePoint_prob n a b c hnpos hb.le hc.le hk.le
  rw [scp2_EstopT_formula, Nat.add_sub_cancel]
  rw [scp2_threePoint_apply _ _ _ _ _ measurableSet_Ici.compl, scp2_lintegral_threePoint,
    scp2_lintegral_threePoint]
  have h1 : ¬ a ≤ 0 := not_le.2 ha
  have h3 : ¬ 1 < a := not_lt.2 ha1.le
  simp [Set.indicator, h1, ha1.le, ha, h3]
  have hr0 : 0 ≤ 1 - (b + c) / n := by rw [sub_nonneg, div_le_one hnpos]; linarith
  have hB : ENNReal.ofReal (c / n) * ENNReal.ofReal a + ENNReal.ofReal (b / n) =
      ENNReal.ofReal ((a * c + b) / n) := by
    rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_add (by positivity) (by positivity)]
    congr 1; ring
  rw [hB, scp2_toReal_formula _ _ _ hr0 (by positivity) (by positivity)]
  have hne : 1 - (b + c) / n ≠ 1 := by
    intro h; have : (b + c) / n = 0 := by linarith
    rw [div_eq_zero_iff] at this; rcases this with h | h <;> linarith
  rw [geom_sum_eq hne, show 1 - (b + c) / n - 1 = -((b + c) / n) by ring]
  have hn0 : n ≠ 0 := hnpos.ne'
  have hbc' : b + c ≠ 0 := hbc0.ne'
  generalize (1 - (b + c) / n) ^ k = P
  field_simp
  ring
