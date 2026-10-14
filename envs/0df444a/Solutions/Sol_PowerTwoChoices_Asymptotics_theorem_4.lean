-- Prove2me | solution 1 for PowerTwoChoices.Asymptotics.theorem_4
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T00:38:12.239146+00:00
-- url     : https://prove2.me/submissions/e59f841c-4105-42e9-9625-dac989fb3cfd

import Mathlib
import Definitions.Def_PowerTwoChoices_Asymptotics_ExpectedTime

set_option autoImplicit false

open Filter Topology PowerTwoChoices.Asymptotics

def p2c_e (d i : ℕ) : ℕ := ∑ k ∈ Finset.Ico 1 i, d ^ k

def p2c_f (d : ℕ) (lam : ℝ) (i : ℕ) : ℝ := if 1 ≤ i then lam ^ (p2c_e d i) else 0

lemma p2c_Td_eq (d : ℕ) (lam : ℝ) : Td d lam = ∑' i, p2c_f d lam i := rfl

lemma p2c_e_succ (d n : ℕ) (hn : 1 ≤ n) : p2c_e d (n + 1) = p2c_e d n + d ^ n := by
  unfold p2c_e
  exact Finset.sum_Ico_succ_top hn _

lemma p2c_e_le (d : ℕ) (hd : 2 ≤ d) (n : ℕ) : p2c_e d n ≤ d ^ n := by
  induction n with
  | zero => simp [p2c_e]
  | succ n ih =>
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [p2c_e]
    · rw [p2c_e_succ d n hn, pow_succ]
      nlinarith [ih, hd, Nat.zero_le (d ^ n)]

lemma p2c_e_mono (d : ℕ) {m n : ℕ} (h : m ≤ n) : p2c_e d m ≤ p2c_e d n :=
  Finset.sum_le_sum_of_subset (Finset.Ico_subset_Ico_right h)

lemma p2c_e_ge_pred (d : ℕ) (m : ℕ) (hm : 2 ≤ m) : d ^ (m - 1) ≤ p2c_e d m := by
  unfold p2c_e
  exact Finset.single_le_sum (f := fun k => d ^ k) (fun _ _ => Nat.zero_le _)
    (by simp only [Finset.mem_Ico]; omega)

lemma p2c_e_ge_card (d : ℕ) (hd : 1 ≤ d) (n : ℕ) : n ≤ p2c_e d (n + 1) := by
  unfold p2c_e
  calc n = ∑ k ∈ Finset.Ico 1 (n + 1), 1 := by simp
    _ ≤ _ := Finset.sum_le_sum (fun k _ => Nat.one_le_pow _ _ hd)

lemma p2c_f_succ (d : ℕ) (lam : ℝ) (i : ℕ) : p2c_f d lam (i + 1) = lam ^ p2c_e d (i + 1) := by
  simp [p2c_f]

lemma p2c_f_nonneg (d : ℕ) (lam : ℝ) (h0 : 0 ≤ lam) (i : ℕ) : 0 ≤ p2c_f d lam i := by
  unfold p2c_f
  split_ifs <;> positivity

lemma p2c_f_le_one (d : ℕ) (lam : ℝ) (h0 : 0 ≤ lam) (h1 : lam ≤ 1) (i : ℕ) :
    p2c_f d lam i ≤ 1 := by
  unfold p2c_f
  split_ifs
  · exact pow_le_one₀ h0 h1
  · exact zero_le_one

lemma p2c_summable (d : ℕ) (hd : 2 ≤ d) (lam : ℝ) (h0 : 0 ≤ lam) (h1 : lam < 1) :
    Summable (p2c_f d lam) := by
  rw [← summable_nat_add_iff 1]
  refine Summable.of_nonneg_of_le (fun i => p2c_f_nonneg d lam h0 _) (fun i => ?_)
    (summable_geometric_of_lt_one h0 h1)
  rw [p2c_f_succ]
  exact pow_le_pow_of_le_one h0 h1.le (p2c_e_ge_card d (by omega) i)

lemma p2c_lower (d : ℕ) (hd : 2 ≤ d) (lam : ℝ) (h0 : 0 < lam) (h1 : lam < 1) (N : ℕ) :
    (N : ℝ) * (1 - ((1 - lam) * (d : ℝ) ^ N)) ≤ Td d lam := by
  have hs := p2c_summable d hd lam h0.le h1
  have h1' : ∑ i ∈ Finset.range (N + 1), p2c_f d lam i ≤ Td d lam := by
    rw [p2c_Td_eq]
    exact hs.sum_le_tsum _ (fun i _ => p2c_f_nonneg d lam h0.le i)
  have h2 : ∑ i ∈ Finset.range (N + 1), p2c_f d lam i
      = ∑ i ∈ Finset.range N, p2c_f d lam (i + 1) := by
    rw [Finset.sum_range_succ']
    simp [p2c_f]
  have h3 : ∀ i ∈ Finset.range N, lam ^ p2c_e d N ≤ p2c_f d lam (i + 1) := by
    intro i hi
    rw [p2c_f_succ]
    exact pow_le_pow_of_le_one h0.le h1.le (p2c_e_mono d (by simp at hi; omega))
  have h4 : (N : ℝ) * lam ^ p2c_e d N ≤ ∑ i ∈ Finset.range N, p2c_f d lam (i + 1) := by
    have := Finset.card_nsmul_le_sum (Finset.range N) (fun i => p2c_f d lam (i + 1))
      (lam ^ p2c_e d N) h3
    simpa using this
  have hb : 1 + (p2c_e d N : ℝ) * (lam - 1) ≤ lam ^ p2c_e d N := by
    have := one_add_mul_le_pow (show (-2 : ℝ) ≤ lam - 1 by linarith) (p2c_e d N)
    simpa using this
  have he : (p2c_e d N : ℝ) ≤ (d : ℝ) ^ N := by exact_mod_cast p2c_e_le d hd N
  have hc : 1 - (1 - lam) * (d : ℝ) ^ N ≤ lam ^ p2c_e d N := by nlinarith
  have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  calc (N : ℝ) * (1 - (1 - lam) * (d : ℝ) ^ N) ≤ (N : ℝ) * lam ^ p2c_e d N :=
        mul_le_mul_of_nonneg_left hc hN
    _ ≤ _ := by linarith

lemma p2c_upper (d : ℕ) (hd : 2 ≤ d) (lam : ℝ) (h0 : 0 < lam) (h1 : lam < 1) (N : ℕ)
    (hN : 1 ≤ (1 - lam) * (d : ℝ) ^ N) : Td d lam ≤ N + 2 := by
  have hs := p2c_summable d hd lam h0.le h1
  have hN1 : 1 ≤ N := by
    rcases Nat.eq_zero_or_pos N with rfl | h
    · simp at hN; linarith
    · exact h
  set y : ℝ := lam ^ (d ^ N) with hy
  have hy0 : 0 ≤ y := by positivity
  have hyhalf : y ≤ 1 / 2 := by
    have h5 : lam ≤ Real.exp (lam - 1) := by
      have := Real.add_one_le_exp (lam - 1)
      linarith
    have h6 : y ≤ Real.exp (lam - 1) ^ (d ^ N) := pow_le_pow_left₀ h0.le h5 _
    have h7 : Real.exp (lam - 1) ^ (d ^ N) = Real.exp ((d ^ N : ℕ) * (lam - 1)) :=
      (Real.exp_nat_mul _ _).symm
    have h8 : ((d ^ N : ℕ) : ℝ) * (lam - 1) ≤ -1 := by
      push_cast
      nlinarith
    have h9 : Real.exp (-1) ≤ 1 / 2 := by
      rw [Real.exp_neg]
      have := Real.exp_one_gt_d9
      rw [inv_le_comm₀ (Real.exp_pos 1) (by norm_num)]
      linarith
    calc y ≤ Real.exp ((d ^ N : ℕ) * (lam - 1)) := h7 ▸ h6
      _ ≤ Real.exp (-1) := Real.exp_le_exp.2 h8
      _ ≤ 1 / 2 := h9
  have hsum := hs.sum_add_tsum_nat_add (N + 1)
  have hA : ∑ i ∈ Finset.range (N + 1), p2c_f d lam i ≤ ((N + 1 : ℕ) : ℝ) := by
    have := Finset.sum_le_card_nsmul (Finset.range (N + 1)) (p2c_f d lam) 1
      (fun i _ => p2c_f_le_one d lam h0.le h1.le i)
    simpa using this
  have hterm : ∀ j : ℕ, p2c_f d lam (j + (N + 1)) ≤ y * y ^ j := by
    intro j
    have hidx : 1 ≤ j + (N + 1) := by omega
    have : p2c_f d lam (j + (N + 1)) = lam ^ p2c_e d (j + (N + 1)) := by
      simp [p2c_f, hidx]
    rw [this, ← pow_succ']
    rw [hy, ← pow_mul]
    refine pow_le_pow_of_le_one h0.le h1.le ?_
    have hge := p2c_e_ge_pred d (j + (N + 1)) (by omega)
    have hj : j + 1 ≤ d ^ j := Nat.lt_pow_self (by omega)
    have : j + (N + 1) - 1 = N + j := by omega
    rw [this] at hge
    calc d ^ N * (j + 1) ≤ d ^ N * d ^ j := Nat.mul_le_mul_left _ hj
      _ = d ^ (N + j) := (pow_add d N j).symm
      _ ≤ _ := hge
  have hy1 : y < 1 := by linarith
  have hgeo : Summable (fun j : ℕ => y * y ^ j) :=
    (summable_geometric_of_lt_one hy0 hy1).mul_left y
  have hB : ∑' j : ℕ, p2c_f d lam (j + (N + 1)) ≤ 1 := by
    calc ∑' j : ℕ, p2c_f d lam (j + (N + 1)) ≤ ∑' j : ℕ, y * y ^ j :=
          ((summable_nat_add_iff (N + 1)).2 hs).tsum_le_tsum hterm hgeo
      _ = y * (1 - y)⁻¹ := by rw [tsum_mul_left, tsum_geometric_of_lt_one hy0 hy1]
      _ ≤ 1 := by
        rw [← div_eq_mul_inv, div_le_one (by linarith)]
        linarith
  rw [p2c_Td_eq, ← hsum]
  push_cast at hA ⊢
  linarith

lemma p2c_dpow (d : ℕ) (hd : 2 ≤ d) (N : ℕ) :
    (d : ℝ) ^ N = Real.exp (N * Real.log d) := by
  rw [mul_comm, Real.exp_mul, Real.exp_log (by positivity)]
  simp

lemma p2c_L_eq (lam : ℝ) (_h1 : lam < 1) : Real.log (T1 lam) = - Real.log (1 - lam) := by
  unfold T1
  rw [one_div, Real.log_inv]

lemma p2c_L_tendsto :
    Tendsto (fun lam : ℝ => Real.log (T1 lam)) (𝓝[<] (1 : ℝ)) atTop := by
  have h1 : Tendsto (fun lam : ℝ => 1 - lam) (𝓝[<] (1 : ℝ)) (𝓝[>] (0 : ℝ)) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · have : Tendsto (fun lam : ℝ => 1 - lam) (𝓝 (1 : ℝ)) (𝓝 (1 - 1)) :=
        (continuous_const.sub continuous_id).tendsto 1
      simp only [sub_self] at this
      exact this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with lam hlam
      simp only [Set.mem_Iio] at hlam
      simp only [Set.mem_Ioi]
      linarith
  have h2 := Filter.tendsto_neg_atBot_atTop.comp (Real.tendsto_log_nhdsGT_zero.comp h1)
  refine h2.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with lam hlam
  simp only [Set.mem_Iio] at hlam
  simp [p2c_L_eq lam hlam]

open Filter Topology PowerTwoChoices.Asymptotics in
theorem solution (d : ℕ) (hd : 2 ≤ d) :
    Tendsto (fun lam : ℝ => Td d lam / Real.log (T1 lam)) (𝓝[<] (1 : ℝ))
      (𝓝 (1 / Real.log (d : ℝ))) := by
  have hdR : (1 : ℝ) < d := by exact_mod_cast hd
  have hl : 0 < Real.log (d : ℝ) := Real.log_pos hdR
  have hL := p2c_L_tendsto
  have hmem : Set.Ioo (0 : ℝ) 1 ∈ 𝓝[<] (1 : ℝ) := Ioo_mem_nhdsLT (by norm_num)
  have hLpos : ∀ᶠ lam : ℝ in 𝓝[<] (1 : ℝ), 0 < Real.log (T1 lam) :=
    hL.eventually_gt_atTop 0
  refine tendsto_order.2 ⟨fun a ha => ?_, fun b hb => ?_⟩
  · -- lower bound
    have haℓ : a * Real.log d < 1 := by
      rwa [lt_div_iff₀ hl] at ha
    set ε : ℝ := min (1 / 2) ((1 - a * Real.log d) / 2) with hε
    have hε0 : 0 < ε := lt_min (by norm_num) (by linarith)
    have hε1 : ε ≤ 1 / 2 := min_le_left _ _
    have hε2 : ε ≤ (1 - a * Real.log d) / 2 := min_le_right _ _
    have hag : a < (1 - ε) / Real.log d := by
      rw [lt_div_iff₀ hl]; nlinarith
    have hg : Tendsto (fun lam : ℝ => ((1 - ε) / Real.log d - 1 / Real.log (T1 lam)) *
        (1 - Real.exp (-(ε * Real.log (T1 lam))))) (𝓝[<] (1 : ℝ))
        (𝓝 (((1 - ε) / Real.log d - 0) * (1 - 0))) := by
      refine Tendsto.mul (tendsto_const_nhds.sub ?_) (tendsto_const_nhds.sub ?_)
      · exact tendsto_const_nhds.div_atTop hL
      · exact Real.tendsto_exp_neg_atTop_nhds_zero.comp (hL.const_mul_atTop hε0)
    have hg' : ∀ᶠ lam : ℝ in 𝓝[<] (1 : ℝ), a < ((1 - ε) / Real.log d - 1 / Real.log (T1 lam)) *
        (1 - Real.exp (-(ε * Real.log (T1 lam)))) := by
      refine hg.eventually_const_lt ?_
      simpa using hag
    filter_upwards [hg', hmem, hLpos] with lam hlam hm hLp
    refine lt_of_lt_of_le hlam ?_
    obtain ⟨hm0, hm1⟩ := hm
    set L := Real.log (T1 lam) with hLdef
    have hLu : L = - Real.log (1 - lam) := p2c_L_eq lam hm1
    have hu : 0 < 1 - lam := by linarith
    have hexpL : Real.exp (-L) = 1 - lam := by
      rw [hLu, neg_neg, Real.exp_log hu]
    set N : ℕ := ⌊(1 - ε) * L / Real.log d⌋₊ with hN
    have hx0 : 0 ≤ (1 - ε) * L / Real.log d := by
      have : 0 ≤ 1 - ε := by linarith
      positivity
    have hN1 : (N : ℝ) ≤ (1 - ε) * L / Real.log d := Nat.floor_le hx0
    have hN2 : (1 - ε) * L / Real.log d < N + 1 := Nat.lt_floor_add_one _
    have hNl : (N : ℝ) * Real.log d ≤ (1 - ε) * L := by
      rwa [le_div_iff₀ hl] at hN1
    have hdN : (1 - lam) * (d : ℝ) ^ N ≤ Real.exp (-(ε * L)) := by
      rw [p2c_dpow d hd N, ← hexpL, ← Real.exp_add]
      apply Real.exp_le_exp.2
      linarith
    have hlow := p2c_lower d hd lam hm0 hm1 N
    have he1 : Real.exp (-(ε * L)) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      have : 0 ≤ ε * L := by positivity
      linarith
    have hNge : (1 - ε) * L / Real.log d - 1 ≤ N := by linarith
    have h5 : ((1 - ε) * L / Real.log d - 1) * (1 - Real.exp (-(ε * L))) ≤ Td d lam := by
      calc ((1 - ε) * L / Real.log d - 1) * (1 - Real.exp (-(ε * L)))
          ≤ (N : ℝ) * (1 - Real.exp (-(ε * L))) :=
            mul_le_mul_of_nonneg_right hNge (by linarith)
        _ ≤ (N : ℝ) * (1 - (1 - lam) * (d : ℝ) ^ N) :=
            mul_le_mul_of_nonneg_left (by linarith) (Nat.cast_nonneg N)
        _ ≤ _ := hlow
    rw [le_div_iff₀ hLp]
    have : ((1 - ε) / Real.log d - 1 / L) * (1 - Real.exp (-(ε * L))) * L
        = ((1 - ε) * L / Real.log d - 1) * (1 - Real.exp (-(ε * L))) := by
      field_simp
    rw [this]
    exact h5
  · -- upper bound
    have hb' : 1 / Real.log d + 0 < b := by simpa using hb
    have hg : Tendsto (fun lam : ℝ => 1 / Real.log d + 3 / Real.log (T1 lam)) (𝓝[<] (1 : ℝ))
        (𝓝 (1 / Real.log d + 0)) := by
      refine tendsto_const_nhds.add ?_
      exact tendsto_const_nhds.div_atTop hL
    have hg' := hg.eventually_lt_const hb'
    filter_upwards [hg', hmem, hLpos] with lam hlam hm hLp
    refine lt_of_le_of_lt ?_ hlam
    obtain ⟨hm0, hm1⟩ := hm
    set L := Real.log (T1 lam) with hLdef
    have hLu : L = - Real.log (1 - lam) := p2c_L_eq lam hm1
    have hu : 0 < 1 - lam := by linarith
    have hexpL : Real.exp L = (1 - lam)⁻¹ := by
      rw [hLu, Real.exp_neg, Real.exp_log hu]
    set N : ℕ := ⌈L / Real.log d⌉₊ with hN
    have hN1 : L / Real.log d ≤ N := Nat.le_ceil _
    have hN2 : (N : ℝ) < L / Real.log d + 1 := Nat.ceil_lt_add_one (by positivity)
    have hNl : L ≤ (N : ℝ) * Real.log d := by
      rwa [div_le_iff₀ hl] at hN1
    have hdN : 1 ≤ (1 - lam) * (d : ℝ) ^ N := by
      rw [p2c_dpow d hd N]
      have : (1 - lam)⁻¹ ≤ Real.exp (N * Real.log d) := by
        rw [← hexpL]; exact Real.exp_le_exp.2 hNl
      calc (1 : ℝ) = (1 - lam) * (1 - lam)⁻¹ := (mul_inv_cancel₀ hu.ne').symm
        _ ≤ _ := mul_le_mul_of_nonneg_left this hu.le
    have hup := p2c_upper d hd lam hm0 hm1 N hdN
    rw [div_le_iff₀ hLp]
    have : (1 / Real.log d + 3 / L) * L = L / Real.log d + 3 := by
      field_simp
    rw [this]
    linarith
