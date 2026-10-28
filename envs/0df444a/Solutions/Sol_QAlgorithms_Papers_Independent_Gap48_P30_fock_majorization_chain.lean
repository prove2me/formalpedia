-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Gap48.P30.fock_majorization_chain
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T10:53:09.954022+00:00
-- url     : https://prove2.me/submissions/f9ad7850-91a0-40df-8b3e-2f4f2e6c7b67

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P30
noncomputable section

namespace QAlgorithms.Papers.Independent.Gap48.P30

open Filter MeasureTheory
open scoped BigOperators ENNReal Topology

attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

/-- A top-j subset exists. -/
lemma S170F_top (F : Finset ℕ) (p : ℕ → ℝ) (j : ℕ) (hj : j ≤ F.card) :
    ∃ s ⊆ F, s.card = j ∧ ∀ a ∈ s, ∀ b ∈ F, b ∉ s → p b ≤ p a := by
  have hne : (F.powersetCard j).Nonempty := Finset.powersetCard_nonempty.2 hj
  obtain ⟨s, hs, hmax⟩ := Finset.exists_max_image (F.powersetCard j) (fun s => ∑ x ∈ s, p x) hne
  rw [Finset.mem_powersetCard] at hs
  refine ⟨s, hs.1, hs.2, fun a ha b hb hbs => ?_⟩
  by_contra hlt
  push_neg at hlt
  have hmem : insert b (s.erase a) ∈ F.powersetCard j := by
    rw [Finset.mem_powersetCard]
    refine ⟨Finset.insert_subset hb ((Finset.erase_subset _ _).trans hs.1), ?_⟩
    rw [Finset.card_insert_of_notMem (fun h => hbs (Finset.mem_of_mem_erase h)), Finset.card_erase_of_mem ha, hs.2]
    have : 0 < s.card := Finset.card_pos.2 ⟨a, ha⟩
    omega
  have := hmax _ hmem
  rw [Finset.sum_insert (fun h => hbs (Finset.mem_of_mem_erase h))] at this
  have h2 := Finset.add_sum_erase s p ha
  linarith

/-- Finite weighted sums are dominated by a top-j sum. -/
lemma S170F_fin (F : Finset ℕ) (p c : ℕ → ℝ) (j : ℕ) (hp : ∀ m, 0 ≤ p m)
    (hc0 : ∀ m, 0 ≤ c m) (hc1 : ∀ m, c m ≤ 1) (hcj : ∑ m ∈ F, c m ≤ j) :
    ∃ s ⊆ F, s.card ≤ j ∧ ∑ m ∈ F, c m * p m ≤ ∑ m ∈ s, p m := by
  rcases le_or_gt F.card j with hF | hF
  · refine ⟨F, subset_rfl, hF, Finset.sum_le_sum fun m _ => ?_⟩
    exact mul_le_of_le_one_left (hp m) (hc1 m)
  rcases Nat.eq_zero_or_pos j with rfl | hj0
  · refine ⟨∅, Finset.empty_subset _, le_rfl, ?_⟩
    have hz : ∀ m ∈ F, c m = 0 := by
      have := (Finset.sum_eq_zero_iff_of_nonneg fun m _ => hc0 m).1
        (le_antisymm (by simpa using hcj) (Finset.sum_nonneg fun m _ => hc0 m))
      exact this
    simp only [Finset.sum_empty]
    rw [Finset.sum_eq_zero fun m hm => by rw [hz m hm, zero_mul]]
  obtain ⟨s, hsF, hcard, htop⟩ := S170F_top F p j hF.le
  have hsne : s.Nonempty := Finset.card_pos.1 (by omega)
  obtain ⟨a0, ha0, hmin⟩ := Finset.exists_min_image s p hsne
  set t := p a0
  have ht0 : 0 ≤ t := hp a0
  have hsplit : ∀ g : ℕ → ℝ, ∑ m ∈ F, g m = ∑ m ∈ s, g m + ∑ m ∈ F \ s, g m := fun g => by
    rw [← Finset.sum_sdiff hsF, add_comm]
  have e1 : ∑ m ∈ F, c m * p m = ∑ m ∈ F, c m * (p m - t) + t * ∑ m ∈ F, c m := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]; congr 1; funext m; ring
  have e2 : ∑ m ∈ F \ s, c m * (p m - t) ≤ 0 := by
    refine Finset.sum_nonpos fun m hm => ?_
    rw [Finset.mem_sdiff] at hm
    exact mul_nonpos_of_nonneg_of_nonpos (hc0 m) (by linarith [htop a0 ha0 m hm.1 hm.2])
  have e3 : ∑ m ∈ s, c m * (p m - t) ≤ ∑ m ∈ s, (p m - t) := by
    refine Finset.sum_le_sum fun m hm => ?_
    exact mul_le_of_le_one_left (by linarith [hmin m hm]) (hc1 m)
  have e4 : t * ∑ m ∈ F, c m ≤ t * s.card := by
    rw [hcard]; exact mul_le_mul_of_nonneg_left hcj ht0
  refine ⟨s, hsF, hcard.le, ?_⟩
  rw [e1, hsplit (fun m => c m * (p m - t))]
  have e5 : ∑ m ∈ s, (p m - t) = ∑ m ∈ s, p m - t * s.card := by
    rw [Finset.sum_sub_distrib]; simp [mul_comm]
  linarith

lemma S170F_maj (p q : ℕ → ℝ) (D : ℕ → ℕ → ℝ) (hp : ∀ m, 0 ≤ p m)
    (hD : CountableSubunitalStochastic D) (hq : ∀ n, HasSum (fun m => D n m * p m) (q n)) (j : ℕ) :
    largestMass q j ≤ largestMass p j := by
  obtain ⟨hD0, hDcol, hDrow⟩ := hD
  have hq0 : ∀ n, 0 ≤ q n := fun n => (hq n).nonneg fun m => mul_nonneg (hD0 n m) (hp m)
  unfold largestMass
  refine iSup_le fun ⟨s, hs⟩ => ?_
  simp only
  set c : ℕ → ℝ := fun m => ∑ n ∈ s, D n m with hc
  have hsum : HasSum (fun m => c m * p m) (∑ n ∈ s, q n) := by
    have := hasSum_sum (s := s) fun n _ => hq n
    convert this using 1
    funext m; simp only [hc, Finset.sum_mul]
  have hc0 : ∀ m, 0 ≤ c m := fun m => Finset.sum_nonneg fun n _ => hD0 n m
  have hc1 : ∀ m, c m ≤ 1 := fun m => by
    have := sum_le_hasSum s (fun n _ => hD0 n m) (hDcol m)
    exact this
  have hcF : ∀ F : Finset ℕ, ∑ m ∈ F, c m ≤ j := fun F => by
    simp only [hc]
    rw [Finset.sum_comm]
    calc ∑ n ∈ s, ∑ m ∈ F, D n m ≤ ∑ n ∈ s, (1 : ℝ) := Finset.sum_le_sum fun n _ =>
          (Summable.sum_le_tsum F (fun m _ => hD0 n m) (hDrow n).1).trans (hDrow n).2
      _ = s.card := by simp
      _ ≤ j := by exact_mod_cast hs
  rw [← ENNReal.ofReal_sum_of_nonneg fun n _ => hq0 n]
  have ht := (ENNReal.tendsto_ofReal hsum.tendsto_sum_nat)
  refine le_of_tendsto' ht fun N => ?_
  obtain ⟨s', _, hcard, hle⟩ := S170F_fin (Finset.range N) p c j hp hc0 hc1 (hcF _)
  calc ENNReal.ofReal (∑ m ∈ Finset.range N, c m * p m) ≤ ENNReal.ofReal (∑ m ∈ s', p m) :=
        ENNReal.ofReal_le_ofReal hle
    _ = ∑ m ∈ s', ENNReal.ofReal (p m) := ENNReal.ofReal_sum_of_nonneg fun m _ => hp m
    _ ≤ ⨆ s : {s : Finset ℕ // s.card ≤ j}, ∑ n ∈ s.val, ENNReal.ofReal (p n) :=
        le_iSup (fun s : {s : Finset ℕ // s.card ≤ j} => ∑ n ∈ s.val, ENNReal.ofReal (p n)) ⟨s', hcard⟩

lemma S170F_law (k : ℕ) (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x < 1) : ProbabilityLaw (fockSchmidtWeight k x) := by
  have hx2 : x ^ 2 < 1 := by nlinarith
  refine ⟨fun n => ?_, ?_⟩
  · unfold fockSchmidtWeight
    have : 0 ≤ 1 - x ^ 2 := by linarith
    positivity
  · have h := hasSum_choose_mul_geometric_of_norm_lt_one (𝕜 := ℝ) k (r := x ^ 2)
      (by rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]; exact hx2)
    have h2 := h.mul_left ((1 - x ^ 2) ^ (k + 1))
    have hne : (1 - x ^ 2) ^ (k + 1) ≠ 0 := pow_ne_zero _ (by linarith)
    rw [mul_one_div_cancel hne] at h2
    have e : fockSchmidtWeight k x = fun i => (1 - x ^ 2) ^ (k + 1) * (((i + k).choose k : ℕ) * (x ^ 2) ^ i) := by
      funext n
      unfold fockSchmidtWeight
      rw [pow_mul, Nat.choose_symm_add]
      ring
    rw [e]; exact h2

/-- Column sums of a shifted negative-binomial column. -/
lemma S170F_col (K m : ℕ) (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1) :
    HasSum (fun n => if m ≤ n then ((n + K).choose (n - m) : ℝ) * q ^ (n - m) * (1 - q) ^ (m + K + 1) else 0) 1 := by
  have h := hasSum_choose_mul_geometric_of_norm_lt_one (𝕜 := ℝ) (m + K) (r := q)
    (by rw [Real.norm_eq_abs, abs_of_nonneg hq0]; exact hq1)
  have h2 := h.mul_right ((1 - q) ^ (m + K + 1))
  have hne : (1 - q) ^ (m + K + 1) ≠ 0 := pow_ne_zero _ (by linarith)
  rw [one_div, inv_mul_cancel₀ hne] at h2
  rw [← hasSum_nat_add_iff' m]
  have hz : ∑ i ∈ Finset.range m, (if m ≤ i then ((i + K).choose (i - m) : ℝ) * q ^ (i - m) *
      (1 - q) ^ (m + K + 1) else 0) = 0 :=
    Finset.sum_eq_zero fun i hi => by rw [Finset.mem_range] at hi; rw [if_neg (by omega)]
  rw [hz, sub_zero]
  have e : (fun j => if m ≤ j + m then ((j + m + K).choose (j + m - m) : ℝ) * q ^ (j + m - m) *
      (1 - q) ^ (m + K + 1) else 0) = fun i => ((i + (m + K)).choose (m + K) : ℕ) * q ^ i * (1 - q) ^ (m + K + 1) := by
    funext j
    rw [if_pos (by omega), show j + m - m = j by omega, show j + m + K = j + (m + K) by ring,
      Nat.choose_symm_add]
  rw [e]; exact h2

lemma S170F_row (K n : ℕ) (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    ∑ m ∈ Finset.range (n + 1), ((n + K).choose (n - m) : ℝ) * q ^ (n - m) * (1 - q) ^ (m + K + 1) ≤ 1 := by
  have h1q : 0 ≤ 1 - q := by linarith
  calc ∑ m ∈ Finset.range (n + 1), ((n + K).choose (n - m) : ℝ) * q ^ (n - m) * (1 - q) ^ (m + K + 1)
      ≤ ∑ m ∈ Finset.range (n + 1), q ^ (n - m) * (1 - q) ^ (n + K - (n - m)) * ((n + K).choose (n - m) : ℝ) := by
        refine Finset.sum_le_sum fun m hm => ?_
        rw [Finset.mem_range] at hm
        rw [show n + K - (n - m) = m + K by omega, mul_comm _ ((n + K).choose (n - m) : ℝ), mul_assoc]
        refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ (by positivity)) (by positivity)
        exact pow_le_pow_of_le_one h1q (by linarith) (by omega)
    _ = ∑ i ∈ Finset.range (n + 1), q ^ i * (1 - q) ^ (n + K - i) * ((n + K).choose i : ℝ) := by
        rw [← Finset.sum_range_reflect]
        refine Finset.sum_congr rfl fun m hm => ?_
        rw [Finset.mem_range] at hm
        rw [show n + 1 - 1 - m = n - m by omega, show n - (n - m) = m by omega]
    _ ≤ ∑ i ∈ Finset.range (n + K + 1), q ^ i * (1 - q) ^ (n + K - i) * ((n + K).choose i : ℝ) := by
        refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.2 (by omega)) fun i _ _ => ?_
        have : 0 ≤ 1 - q := h1q
        positivity
    _ = 1 := by rw [← add_pow]; simp

lemma S170F_choose (n k m : ℕ) (h : m ≤ n) :
    (n + k).choose (n - m) * (m + k).choose m = (n + k).choose n * n.choose m := by
  rw [Nat.choose_symm_of_eq_add (show n + k = (n - m) + (m + k) by omega), Nat.choose_symm_add,
    Nat.choose_symm_add, Nat.choose_mul (by omega)]
  congr 2 <;> omega

lemma S170F_ident (k n : ℕ) (q a : ℝ) :
    ∑ m ∈ Finset.range (n + 1), ((n + k).choose (n - m) : ℝ) * q ^ (n - m) * (1 - q) ^ (m + k + 1) *
      ((1 - a) ^ (k + 1) * a ^ m * ((m + k).choose m : ℝ)) =
    ((1 - q) * (1 - a)) ^ (k + 1) * (q + (1 - q) * a) ^ n * ((n + k).choose n : ℝ) := by
  rw [add_comm q, add_pow, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun m hm => ?_
  rw [Finset.mem_range] at hm
  have hc : ((n + k).choose (n - m) : ℝ) * ((m + k).choose m : ℝ) = ((n + k).choose n : ℝ) * (n.choose m : ℝ) := by
    exact_mod_cast S170F_choose n k m (by omega)
  have : ((n + k).choose (n - m) : ℝ) * q ^ (n - m) * (1 - q) ^ (m + k + 1) *
      ((1 - a) ^ (k + 1) * a ^ m * ((m + k).choose m : ℝ)) =
      (((n + k).choose (n - m) : ℝ) * ((m + k).choose m : ℝ)) * q ^ (n - m) * (1 - q) ^ (m + k + 1) *
      ((1 - a) ^ (k + 1) * a ^ m) := by ring
  rw [this, hc]
  simp only [mul_pow]
  ring

lemma S170G_vdm (e k n : ℕ) :
    ∑ m ∈ Finset.range (n + 1), (n - m + e).choose e * (m + k).choose k = ((e + k + 1) + n).choose (e + k + 1) := by
  suffices H : ∑ m ∈ Finset.range (n + 1), ((n - m + e).choose e : ℤ) * ((m + k).choose k : ℤ) =
      (((e + k + 1) + n).choose (e + k + 1) : ℤ) by exact_mod_cast H
  have h0 : (PowerSeries.invOneSubPow ℤ ((e + k + 1) + 1)).val =
      (PowerSeries.invOneSubPow ℤ (e + 1)).val * (PowerSeries.invOneSubPow ℤ (k + 1)).val := by
    rw [← Units.val_mul, ← PowerSeries.invOneSubPow_add, show e + 1 + (k + 1) = e + k + 1 + 1 by ring]
  have h := congrArg (PowerSeries.coeff n) h0
  rw [PowerSeries.invOneSubPow_val_succ_eq_mk_add_choose,
    PowerSeries.invOneSubPow_val_succ_eq_mk_add_choose,
    PowerSeries.invOneSubPow_val_succ_eq_mk_add_choose, PowerSeries.coeff_mk, PowerSeries.coeff_mul] at h
  rw [h, Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => (PowerSeries.coeff i (PowerSeries.mk fun n => ((e + n).choose e : ℤ))) *
    (PowerSeries.coeff j (PowerSeries.mk fun n => ((k + n).choose k : ℤ))))]
  rw [← Finset.sum_range_reflect]
  refine Finset.sum_congr rfl fun m hm => ?_
  rw [Finset.mem_range] at hm
  simp only [PowerSeries.coeff_mk]
  rw [show n + 1 - 1 - m = n - m by omega, show n - (n - m) = m by omega, add_comm e, add_comm k]

lemma S170G_series (e : ℕ) (b : ℝ) (hb0 : 0 ≤ b) (hb1 : b < 1) :
    HasSum (fun j => (1 - b) ^ (e + 1) * ((j + e).choose e : ℝ) * b ^ j) 1 := by
  have h := hasSum_choose_mul_geometric_of_norm_lt_one (𝕜 := ℝ) e (r := b)
    (by rw [Real.norm_eq_abs, abs_of_nonneg hb0]; exact hb1)
  have h2 := h.mul_left ((1 - b) ^ (e + 1))
  rw [mul_one_div_cancel (pow_ne_zero _ (by linarith))] at h2
  have e1 : (fun j => (1 - b) ^ (e + 1) * ((j + e).choose e : ℝ) * b ^ j) =
      fun i => (1 - b) ^ (e + 1) * (((i + e).choose e : ℕ) * b ^ i) := by funext j; ring
  rw [e1]; exact h2

lemma S170G_col (e m : ℕ) (b : ℝ) (hb0 : 0 ≤ b) (hb1 : b < 1) :
    HasSum (fun n => if m ≤ n then (1 - b) ^ (e + 1) * ((n - m + e).choose e : ℝ) * b ^ (n - m) else 0) 1 := by
  rw [← hasSum_nat_add_iff' m]
  have hz : ∑ i ∈ Finset.range m, (if m ≤ i then (1 - b) ^ (e + 1) * ((i - m + e).choose e : ℝ) *
      b ^ (i - m) else 0) = 0 :=
    Finset.sum_eq_zero fun i hi => by rw [Finset.mem_range] at hi; rw [if_neg (by omega)]
  rw [hz, sub_zero]
  have e1 : (fun j => if m ≤ j + m then (1 - b) ^ (e + 1) * ((j + m - m + e).choose e : ℝ) * b ^ (j + m - m)
      else 0) = fun j => (1 - b) ^ (e + 1) * ((j + e).choose e : ℝ) * b ^ j := by
    funext j; rw [if_pos (by omega), show j + m - m = j by omega]
  rw [e1]; exact S170G_series e b hb0 hb1

end QAlgorithms.Papers.Independent.Gap48.P30

open QAlgorithms.Papers.Independent.Gap48.P30

theorem solution (lambda : ℝ) (hl : 0 ≤ lambda) (hlu : lambda < 1) :
    (∀ n m : ℕ, fockKernel 1 lambda n m =
      if m ≤ n then (1 - lambda ^ 2) * lambda ^ (2 * (n - m)) else 0) ∧
    (∀ d : ℕ, CountableSubunitalStochastic (fockKernel d lambda) ∧
      ∀ k : ℕ, ProbabilityMajorizes (fockSchmidtWeight k lambda) (fockSchmidtWeight (k + d) lambda) ∧
        ∀ n : ℕ, HasSum (fun m => fockKernel d lambda n m * fockSchmidtWeight k lambda m)
          (fockSchmidtWeight (k + d) lambda n)) ∧
    (∀ k : ℕ, ProbabilityMajorizes (fockSchmidtWeight 0 lambda) (fockSchmidtWeight k lambda)) := by
  set b := lambda ^ 2 with hb
  have hb0 : 0 ≤ b := by positivity
  have hb1 : b < 1 := by rw [hb]; nlinarith
  have hw : ∀ k n, fockSchmidtWeight k lambda n = (1 - b) ^ (k + 1) * b ^ n * ((n + k).choose n : ℝ) := by
    intro k n; unfold fockSchmidtWeight; rw [pow_mul, ← hb]
  have hlaw : ∀ k, ProbabilityLaw (fockSchmidtWeight k lambda) := fun k => S170F_law k lambda hl hlu
  have main : ∀ d, CountableSubunitalStochastic (fockKernel d lambda) ∧
      ∀ k n, HasSum (fun m => fockKernel d lambda n m * fockSchmidtWeight k lambda m)
        (fockSchmidtWeight (k + d) lambda n) := by
    intro d
    rcases d with _ | e
    · have hK : ∀ n m, fockKernel 0 lambda n m = if n = m then 1 else 0 := by
        intro n m; simp [fockKernel]
      refine ⟨⟨fun n m => by rw [hK]; split_ifs <;> norm_num, fun m => ?_, fun n => ?_⟩, fun k n => ?_⟩
      · simp only [hK]; exact hasSum_ite_eq m 1
      · have h : HasSum (fun m => fockKernel 0 lambda n m) 1 := by
          simp only [hK]
          have := hasSum_ite_eq n (1 : ℝ)
          convert this using 2 with m
          simp only [eq_comm]
        exact ⟨h.summable, h.tsum_eq.le⟩
      · have := hasSum_ite_eq n (fockSchmidtWeight k lambda n)
        rw [add_zero]
        convert this using 2 with m
        rw [hK]
        by_cases h : m = n
        · subst h; simp
        · rw [if_neg (Ne.symm h), if_neg h, zero_mul]
    · have hK : ∀ n m, fockKernel (e + 1) lambda n m =
          if m ≤ n then (1 - b) ^ (e + 1) * ((n - m + e).choose e : ℝ) * b ^ (n - m) else 0 := by
        intro n m
        simp only [fockKernel, Nat.add_one_ne_zero, if_false, Nat.add_sub_cancel]
        split_ifs
        · rw [pow_mul, ← hb, show n - m + (e + 1) - 1 = n - m + e by omega]
        · rfl
      have hK0 : ∀ n m, 0 ≤ fockKernel (e + 1) lambda n m := by
        intro n m; rw [hK]; split_ifs
        · have : 0 ≤ 1 - b := by linarith
          positivity
        · exact le_rfl
      have hfin : ∀ n, ∀ m ∉ Finset.range (n + 1), fockKernel (e + 1) lambda n m = 0 := by
        intro n m hm; rw [Finset.mem_range] at hm; rw [hK, if_neg (by omega)]
      refine ⟨⟨hK0, fun m => ?_, fun n => ⟨summable_of_ne_finset_zero (hfin n), ?_⟩⟩, fun k n => ?_⟩
      · simp only [hK]; exact S170G_col e m b hb0 hb1
      · rw [tsum_eq_sum (hfin n)]
        calc ∑ m ∈ Finset.range (n + 1), fockKernel (e + 1) lambda n m
            = ∑ j ∈ Finset.range (n + 1), (1 - b) ^ (e + 1) * ((j + e).choose e : ℝ) * b ^ j := by
              rw [← Finset.sum_range_reflect]
              refine Finset.sum_congr rfl fun m hm => ?_
              rw [Finset.mem_range] at hm
              rw [hK, if_pos (by omega), show n + 1 - 1 - m = n - m by omega, show n - (n - m) = m by omega]
          _ ≤ 1 := sum_le_hasSum _ (fun j _ => by
                have : 0 ≤ 1 - b := by linarith
                positivity) (S170G_series e b hb0 hb1)
      · have hfin2 : ∀ m ∉ Finset.range (n + 1), fockKernel (e + 1) lambda n m * fockSchmidtWeight k lambda m = 0 :=
          fun m hm => by rw [hfin n m hm, zero_mul]
        have key : ∑ m ∈ Finset.range (n + 1), fockKernel (e + 1) lambda n m * fockSchmidtWeight k lambda m =
            fockSchmidtWeight (k + (e + 1)) lambda n := by
          calc ∑ m ∈ Finset.range (n + 1), fockKernel (e + 1) lambda n m * fockSchmidtWeight k lambda m
              = ∑ m ∈ Finset.range (n + 1), (1 - b) ^ (k + e + 2) * b ^ n *
                  (((n - m + e).choose e * (m + k).choose k : ℕ) : ℝ) := by
                refine Finset.sum_congr rfl fun m hm => ?_
                rw [Finset.mem_range] at hm
                rw [hK, if_pos (by omega), hw, Nat.choose_symm_add]
                have hp : b ^ n = b ^ (n - m) * b ^ m := by rw [← pow_add]; congr 1; omega
                rw [hp]; push_cast; ring
            _ = (1 - b) ^ (k + e + 2) * b ^ n * ((((e + k + 1) + n).choose (e + k + 1) : ℕ) : ℝ) := by
                rw [← Finset.mul_sum, ← Nat.cast_sum, S170G_vdm]
            _ = fockSchmidtWeight (k + (e + 1)) lambda n := by
                rw [hw, Nat.choose_symm_add, show n + (k + (e + 1)) = e + k + 1 + n by ring,
                  show k + (e + 1) + 1 = k + e + 2 by ring]
        rw [← key]; exact hasSum_sum_of_ne_finset_zero hfin2
  have hmaj : ∀ d k, ProbabilityMajorizes (fockSchmidtWeight k lambda) (fockSchmidtWeight (k + d) lambda) :=
    fun d k => ⟨hlaw k, hlaw (k + d), fun j =>
      S170F_maj _ _ (fockKernel d lambda) (hlaw k).1 (main d).1 (fun n => (main d).2 k n) j⟩
  refine ⟨fun n m => ?_, fun d => ⟨(main d).1, fun k => ⟨hmaj d k, (main d).2 k⟩⟩, fun k => ?_⟩
  · simp only [fockKernel, one_ne_zero, if_false]
    split_ifs
    · simp only [pow_one, Nat.sub_self, Nat.choose_zero_right, Nat.cast_one, mul_one, hb]
    · rfl
  · have := hmaj k 0
    rwa [zero_add] at this
