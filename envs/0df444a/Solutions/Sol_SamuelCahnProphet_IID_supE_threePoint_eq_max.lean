-- Prove2me | solution 1 for SamuelCahnProphet.IID.supE_threePoint_eq_max
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-06T14:18:59.439117+00:00
-- url     : https://prove2.me/submissions/dc3203ad-726a-4c08-b083-78cdbcb4580f

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

lemma scp2_F_le (N : ℕ) [NeZero N] (q A B : ENNReal) (hAB : A ≤ B) :
    (∑ i ∈ Finset.range (N - 1), q ^ i) * A + q ^ (N - 1) * B ≤ (∑ i ∈ Finset.range N, q ^ i) * B := by
  have hN : N = N - 1 + 1 := (Nat.succ_pred_eq_of_pos (Nat.pos_of_ne_zero (NeZero.ne N))).symm
  conv_rhs => rw [hN, Finset.sum_range_succ, add_mul]
  gcongr

lemma scp2_B_le_sum (N : ℕ) [NeZero N] (q B : ENNReal) :
    B ≤ (∑ i ∈ Finset.range N, q ^ i) * B := by
  have h1 : (1 : ENNReal) ≤ ∑ i ∈ Finset.range N, q ^ i := by
    have := Finset.single_le_sum (f := fun i => q ^ i) (fun i _ => zero_le)
      (Finset.mem_range.2 (Nat.pos_of_ne_zero (NeZero.ne N)))
    simpa using this
  calc B = 1 * B := (one_mul B).symm
    _ ≤ _ := by gcongr

theorem solution (a b c : ℝ) (ha : 0 < a) (ha1 : a < 1) (hb : 0 < b)
    (hc : 0 < c) (n : ℕ) [NeZero n] (hn : b + c < n) :
    supE (threePoint n a b c) n =
      max (EstopT (threePoint n a b c) n a) (EstopT (threePoint n a b c) n 1) := by
  set μ := threePoint n a b c with hμ
  have hnpos : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
  have hprob : IsProbabilityMeasure μ := scp2_threePoint_prob _ _ _ _ hnpos hb.le hc.le hn.le
  set B := ∫⁻ y, ENNReal.ofReal y ∂μ with hBdef
  have hAleB : ∀ S : Set ℝ, ∫⁻ y, S.indicator (fun y => ENNReal.ofReal y) y ∂μ ≤ B :=
    fun S => lintegral_mono fun y => Set.indicator_le_self _ _ y
  -- the value of t(a)
  have hAa : ∫⁻ y, (Set.Ici a).indicator (fun y => ENNReal.ofReal y) y ∂μ = B := by
    rw [hBdef, hμ, scp2_lintegral_threePoint, scp2_lintegral_threePoint]
    simp [Set.indicator, ha.not_ge, ha1.le]
  have hTa : EstopT μ n a = (∑ i ∈ Finset.range n, μ (Set.Ici a)ᶜ ^ i) * B := by
    rw [scp2_EstopT_formula, hAa]
    have hN : n = n - 1 + 1 := (Nat.succ_pred_eq_of_pos (Nat.pos_of_ne_zero (NeZero.ne n))).symm
    conv_rhs => rw [hN, Finset.sum_range_succ, add_mul]
  have hBle : B ≤ EstopT μ n a := by rw [hTa]; exact scp2_B_le_sum n _ B
  -- rules whose continuation probability is at most that of t(a)
  have hsmall : ∀ S : Set ℝ, μ Sᶜ ≤ μ (Set.Ici a)ᶜ →
      (∑ i ∈ Finset.range (n - 1), μ Sᶜ ^ i) *
          ∫⁻ y, S.indicator (fun y => ENNReal.ofReal y) y ∂μ + μ Sᶜ ^ (n - 1) * B ≤
        EstopT μ n a := by
    intro S hS
    refine (scp2_F_le n _ _ _ (hAleB S)).trans ?_
    rw [hTa]
    gcongr
  -- rules that never stop early (zero early payoff)
  have hzero : ∀ S : Set ℝ, ∫⁻ y, S.indicator (fun y => ENNReal.ofReal y) y ∂μ = 0 →
      (∑ i ∈ Finset.range (n - 1), μ Sᶜ ^ i) *
          ∫⁻ y, S.indicator (fun y => ENNReal.ofReal y) y ∂μ + μ Sᶜ ^ (n - 1) * B ≤
        EstopT μ n a := by
    intro S hS
    rw [hS, mul_zero, zero_add]
    refine le_trans ?_ hBle
    calc μ Sᶜ ^ (n - 1) * B ≤ 1 * B := by
          gcongr; exact pow_le_one₀ zero_le prob_le_one
      _ = B := one_mul B
  apply le_antisymm
  · apply iSup₂_le
    intro c' hc'
    apply max_le
    · rcases le_or_gt c' a with h1 | h1
      · rw [scp2_EstopT_formula]
        refine le_trans (hsmall _ ?_) (le_max_left _ _)
        exact measure_mono fun y (hy : ¬ c' ≤ y) => (show ¬ a ≤ y from fun h => hy (h1.trans h))
      have hp : 0 < c' := ha.trans h1
      rcases le_or_gt c' 1 with h2 | h2
      · have hq : μ (Set.Ici c')ᶜ = μ (Set.Ici 1)ᶜ := by
          rw [hμ, scp2_threePoint_apply _ _ _ _ _ measurableSet_Ici.compl,
            scp2_threePoint_apply _ _ _ _ _ measurableSet_Ici.compl]
          simp [Set.indicator, hp, h1, h2.not_gt, ha1, hp.not_ge, h1.not_ge, h2, ha1.not_ge]
        have hA : ∫⁻ y, (Set.Ici c').indicator (fun y => ENNReal.ofReal y) y ∂μ =
            ∫⁻ y, (Set.Ici 1).indicator (fun y => ENNReal.ofReal y) y ∂μ := by
          rw [hμ, scp2_lintegral_threePoint, scp2_lintegral_threePoint]
          simp [Set.indicator, hp, h1, h2.not_gt, ha1, hp.not_ge, h1.not_ge, h2, ha1.not_ge]
        refine le_of_eq_of_le ?_ (le_max_right _ _)
        rw [scp2_EstopT_formula, scp2_EstopT_formula, hq, hA]
      · rw [scp2_EstopT_formula]
        refine le_trans (hzero _ ?_) (le_max_left _ _)
        rw [hμ, scp2_lintegral_threePoint]
        simp [Set.indicator, hp.not_ge, h1.not_ge, (ha1.trans h2).not_ge, h2.not_ge]
    · rcases lt_or_ge c' a with h1 | h1
      · rw [scp2_EstopS_formula]
        refine le_trans (hsmall _ ?_) (le_max_left _ _)
        exact measure_mono fun y (hy : ¬ c' < y) => (show ¬ a ≤ y from fun h => hy (h1.trans_le h))
      rcases lt_or_ge c' 1 with h2 | h2
      · have hq : μ (Set.Ioi c')ᶜ = μ (Set.Ici 1)ᶜ := by
          rw [hμ, scp2_threePoint_apply _ _ _ _ _ measurableSet_Ioi.compl,
            scp2_threePoint_apply _ _ _ _ _ measurableSet_Ici.compl]
          simp [Set.indicator, hc', h1, h2, ha1.not_ge, ha1, (ha.trans_le h1), hc'.not_gt, h1.not_gt, h2.le, h2.not_ge]
        have hA : ∫⁻ y, (Set.Ioi c').indicator (fun y => ENNReal.ofReal y) y ∂μ =
            ∫⁻ y, (Set.Ici 1).indicator (fun y => ENNReal.ofReal y) y ∂μ := by
          rw [hμ, scp2_lintegral_threePoint, scp2_lintegral_threePoint]
          simp [Set.indicator, hc', h1, h2, ha1.not_ge, ha1, (ha.trans_le h1), hc'.not_gt, h1.not_gt, h2.le, h2.not_ge]
        refine le_of_eq_of_le ?_ (le_max_right _ _)
        rw [scp2_EstopS_formula, scp2_EstopT_formula, hq, hA]
      · rw [scp2_EstopS_formula]
        refine le_trans (hzero _ ?_) (le_max_left _ _)
        rw [hμ, scp2_lintegral_threePoint]
        simp [Set.indicator, hc', h2, (ha1.trans_le h2).le, h2.not_gt, (ha1.trans_le h2).not_gt]
  · exact max_le
      (le_iSup₂_of_le (f := fun (c : ℝ) (_ : 0 ≤ c) => max (EstopT μ n c) (EstopS μ n c))
        a ha.le (le_max_left _ _))
      (le_iSup₂_of_le (f := fun (c : ℝ) (_ : 0 ≤ c) => max (EstopT μ n c) (EstopS μ n c))
        1 zero_le_one (le_max_left _ _))
