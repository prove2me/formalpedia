-- Prove2me | solution 1 for StrictCompatLB.MeanField.meanfield_limit_and_steady_state
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-18T09:13:36.871294+00:00
-- url     : https://prove2.me/submissions/298cb83a-60bb-452f-b714-5a63e5397cfa

import Mathlib
import Definitions.Def_StrictCompatLB_MeanField_Model
import Theorems.Thm_StrictCompatLB_MeanField_theorem_4_3
import Theorems.Thm_StrictCompatLB_MeanField_lemma_4_2
import Theorems.Thm_StrictCompatLB_MeanField_theorem_4_8_i
import Theorems.Thm_StrictCompatLB_MeanField_theorem_4_8_ii
import Theorems.Thm_StrictCompatLB_MeanField_jsqd_subset_sampling_process_limit
import Theorems.Thm_StrictCompatLB_MeanField_jsqd_stationary_concentration_of_process_limit
import Theorems.Thm_StrictCompatLB_MeanField_supermarket_ode_exists_in_Y
import Theorems.Thm_StrictCompatLB_MeanField_supermarket_ode_uniform_exp_decay
import Theorems.Thm_StrictCompatLB_MeanField_lb_process_exists

set_option autoImplicit false

open Filter Topology MeasureTheory
open scoped ENNReal

namespace SC77

open StrictCompatLB.MeanField

/-! Bridge lemmas for 77ae612d (Thm 3.4): the JSQ(d) assignment function (E.1) is an
assignment function, and a supermarket-ODE trajectory in Y is a (4.2)-trajectory of it. -/

lemma tele_partial (a : ℕ → ℝ) (i n : ℕ) :
    ∑ j ∈ Finset.range n, (if i ≤ j then a j - a (j + 1) else 0)
      = if n ≤ i then 0 else a i - a n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    by_cases h1 : n + 1 ≤ i
    · have h2 : n ≤ i := by omega
      have h3 : ¬ i ≤ n := by omega
      simp [h1, h2, h3]
    · by_cases h2 : n ≤ i
      · have h4 : i = n := by omega
        subst h4
        simp
      · have h3 : i ≤ n := by omega
        simp only [h1, h2, h3, if_true, if_false]
        ring

lemma tele_hasSum (a : ℕ → ℝ) (ha : Antitone a) (h0 : Tendsto a atTop (𝓝 0)) (i : ℕ) :
    HasSum (fun j => if i ≤ j then a j - a (j + 1) else 0) (a i) := by
  have hnn : ∀ j, 0 ≤ (if i ≤ j then a j - a (j + 1) else 0) := by
    intro j
    split_ifs
    · linarith [ha (Nat.le_succ j)]
    · exact le_refl 0
  rw [hasSum_iff_tendsto_nat_of_nonneg hnn]
  simp_rw [tele_partial]
  have h1 : Tendsto (fun n => a i - a n) atTop (𝓝 (a i - 0)) := tendsto_const_nhds.sub h0
  rw [sub_zero] at h1
  refine h1.congr' ?_
  filter_upwards [eventually_gt_atTop i] with n hn
  simp [show ¬ n ≤ i by omega]

lemma tail_eq (s : ℕ → ℝ) (hs : InY s) (i : ℕ) :
    tailOf (fun j => s j - s (j + 1)) i = s i := by
  have hanti : Antitone s := hs.1.2.2
  have h0 : Tendsto s atTop (𝓝 0) :=
    (tendsto_add_atTop_iff_nat 1).mp hs.2.tendsto_atTop_zero
  unfold tailOf
  exact (tele_hasSum s hanti h0 i).tsum_eq

/-- A `𝒴`-valued trajectory of the supermarket system (Mitzenmacher (1)) is a solution of (4.2)
for the JSQ(d) assignment function (E.1). -/
theorem traj_to_pi (lam : ℝ) (d : ℕ) (s : ℝ → ℕ → ℝ)
    (hs : PowerTwoChoices.Limit.IsTrajectory lam d s) (hY : ∀ t : ℝ, 0 ≤ t → InY (s t)) :
    IsPiTrajectory lam (jsqdAssign d) s := by
  refine ⟨hs.1, fun i hi t ht => ?_⟩
  have h := hs.2 i hi t ht
  have e : lam * jsqdAssign d (fun j => s t j - s t (j + 1)) (i - 1) - (s t i - s t (i + 1))
      = PowerTwoChoices.Limit.drift lam d (s t) i := by
    unfold jsqdAssign PowerTwoChoices.Limit.drift
    rw [tail_eq _ (hY t ht), tail_eq _ (hY t ht), Nat.sub_add_cancel hi]
  rw [e]
  exact h

lemma tailOf_hasSum (x : ℕ → ℝ) (hx : InX x) (i : ℕ) :
    HasSum (fun j => if i ≤ j then x j else 0) (tailOf x i) := by
  have hs : Summable (fun j => if i ≤ j then x j else 0) :=
    Summable.of_nonneg_of_le (fun j => by split_ifs <;> simp [hx.1 j])
      (fun j => by split_ifs <;> simp [hx.1 j]) hx.2.summable
  exact hs.hasSum

lemma tailOf_succ (x : ℕ → ℝ) (hx : InX x) (i : ℕ) :
    tailOf x i = x i + tailOf x (i + 1) := by
  have h1 := hasSum_ite_eq i (x i)
  have h2 := (h1.add (tailOf_hasSum x hx (i + 1)))
  have hfun : (fun j => (if j = i then x i else 0) + (if i + 1 ≤ j then x j else 0))
      = (fun j => if i ≤ j then x j else 0) := by
    funext j
    by_cases hj : j = i
    · subst hj; simp
    · by_cases hij : i ≤ j
      · have : i + 1 ≤ j := by omega
        simp [hj, hij, this]
      · have : ¬ i + 1 ≤ j := by omega
        simp [hj, hij, this]
  rw [hfun] at h2
  exact (tailOf_hasSum x hx i).unique h2

lemma tailOf_zero (x : ℕ → ℝ) (hx : InX x) : tailOf x 0 = 1 := by
  have h := tailOf_hasSum x hx 0
  simp only [zero_le, if_true] at h
  exact h.unique hx.2

lemma tailOf_eq (x : ℕ → ℝ) (hx : InX x) (i : ℕ) :
    tailOf x i = 1 - ∑ j ∈ Finset.range i, x j := by
  induction i with
  | zero => simp [tailOf_zero x hx]
  | succ i ih =>
    rw [Finset.sum_range_succ]
    have := tailOf_succ x hx i
    linarith

lemma tailOf_nonneg (x : ℕ → ℝ) (hx : InX x) (i : ℕ) : 0 ≤ tailOf x i :=
  tsum_nonneg (fun j => by split_ifs <;> simp [hx.1 j])

lemma tailOf_antitone (x : ℕ → ℝ) (hx : InX x) : Antitone (tailOf x) := by
  refine antitone_nat_of_succ_le (fun i => ?_)
  have := tailOf_succ x hx i
  linarith [hx.1 i]

lemma tailOf_tendsto (x : ℕ → ℝ) (hx : InX x) : Tendsto (tailOf x) atTop (𝓝 0) := by
  have h := hx.2.tendsto_sum_nat
  have h2 : Tendsto (fun i => 1 - ∑ j ∈ Finset.range i, x j) atTop (𝓝 (1 - 1)) :=
    tendsto_const_nhds.sub h
  rw [sub_self] at h2
  exact h2.congr (fun i => (tailOf_eq x hx i).symm)

/-- The JSQ(d) assignment function (E.1) is an assignment probability function. -/
theorem jsqdAssign_isAssignmentFn (d : ℕ) (hd : 1 ≤ d) : IsAssignmentFn (jsqdAssign d) := by
  intro x hx
  have hanti : Antitone (fun i => tailOf x i ^ d) := fun i j hij =>
    pow_le_pow_left₀ (tailOf_nonneg x hx j) (tailOf_antitone x hx hij) d
  refine ⟨fun i => ?_, ?_, fun i hi => ?_⟩
  · unfold jsqdAssign
    linarith [hanti (Nat.le_succ i)]
  · have h0 : Tendsto (fun i => tailOf x i ^ d) atTop (𝓝 0) := by
      have := (tailOf_tendsto x hx).pow d
      rwa [zero_pow (by omega)] at this
    have h := tele_hasSum (fun i => tailOf x i ^ d) hanti h0 0
    simp only [zero_le, if_true, tailOf_zero x hx, one_pow] at h
    exact h
  · unfold jsqdAssign
    rw [tailOf_succ x hx i, hi, zero_add, sub_self]

end SC77

namespace SC77K3A

open StrictCompatLB.MeanField

/-! K3a: total variation between JSQ(d) without replacement (`jsqdRoute`) and the generic policy
with the JSQ(d) assignment function (`piRoute (jsqdAssign d)`, i.e. d draws with replacement):
`∑_v |jsqdRoute - piRoute| ≤ 2 d^3 / |𝒩_w|`. -/

/-! ### Numeric part -/

noncomputable def Fq (n k a : ℕ) : ℝ := (a.choose k : ℝ) / (n.choose k : ℝ)
noncomputable def Gq (n d a : ℕ) : ℝ := ((a : ℝ) / n) ^ d

lemma pow_sub_pow_le_c (e : ℕ) (x y c : ℝ) (hy : 0 ≤ y) (hyx : y ≤ x) (hxc : x ≤ c) :
    x ^ e - y ^ e ≤ e * c ^ (e - 1) * (x - y) := by
  induction e with
  | zero => simp
  | succ e ih =>
    have hx : 0 ≤ x := hy.trans hyx
    have hc : 0 ≤ c := hx.trans hxc
    have h1 : x ^ (e+1) - y ^ (e+1) = x * (x ^ e - y ^ e) + y ^ e * (x - y) := by ring
    have h2 : x * (x ^ e - y ^ e) ≤ c * (e * c ^ (e - 1) * (x - y)) :=
      mul_le_mul hxc ih (sub_nonneg.mpr (pow_le_pow_left₀ hy hyx e)) hc
    have h3 : y ^ e * (x - y) ≤ c ^ e * (x - y) :=
      mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hy (hyx.trans hxc) e) (sub_nonneg.mpr hyx)
    have h4 : c * (e * c ^ (e - 1)) = e * c ^ e := by
      rcases Nat.eq_zero_or_pos e with he | he
      · subst he; simp
      · rw [mul_left_comm, mul_pow_sub_one (Nat.pos_iff_ne_zero.mp he)]
    have h5 : c * (e * c ^ (e - 1) * (x - y)) = e * c ^ e * (x - y) := by
      rw [← h4]; ring
    simp only [Nat.add_sub_cancel]
    push_cast
    nlinarith [h1, h2, h3, h5]

lemma abs_eq_two_pos (δ : ℝ) : |δ| = δ + 2 * max (-δ) 0 := by
  rcases le_total 0 δ with h | h
  · rw [abs_of_nonneg h, max_eq_right (by linarith)]; ring
  · rw [abs_of_nonpos h, max_eq_left (by linarith)]; ring

lemma dF_nonneg (n k a : ℕ) : 0 ≤ Fq n k (a+1) - Fq n k a := by
  unfold Fq; rw [← sub_div]
  apply div_nonneg _ (Nat.cast_nonneg _)
  rw [sub_nonneg]; exact_mod_cast Nat.choose_le_choose k (Nat.le_succ a)

lemma dG_nonneg (n d a : ℕ) : 0 ≤ Gq n d (a+1) - Gq n d a := by
  unfold Gq; rw [sub_nonneg]
  apply pow_le_pow_left₀ (by positivity)
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  push_cast; linarith

lemma sumF (n k : ℕ) (hk : 1 ≤ k) (hkn : k ≤ n) :
    ∑ a ∈ Finset.range n, (Fq n k (a+1) - Fq n k a) = 1 := by
  rw [Finset.sum_range_sub]
  unfold Fq
  have hpos : (0 : ℝ) < (n.choose k : ℝ) := Nat.cast_pos.mpr (Nat.choose_pos hkn)
  rw [div_self hpos.ne', Nat.choose_eq_zero_of_lt (by omega : 0 < k)]
  simp

lemma sumG (n d : ℕ) (hn : 1 ≤ n) (hd : 1 ≤ d) :
    ∑ a ∈ Finset.range n, (Gq n d (a+1) - Gq n d a) = 1 := by
  rw [Finset.sum_range_sub]
  unfold Gq
  have hnR : (n : ℝ) ≠ 0 := by have : (1 : ℝ) ≤ n := by exact_mod_cast hn
                               linarith
  rw [div_self hnR]
  simp [zero_pow (by omega : d ≠ 0)]

theorem tv_num (n d : ℕ) (hn : 1 ≤ n) (hd : 1 ≤ d) :
    ∑ a ∈ Finset.range n,
      |(Fq n (min d n) (a+1) - Gq n d (a+1)) - (Fq n (min d n) a - Gq n d a)|
        ≤ 2 * (d : ℝ) ^ 3 / n := by
  set k := min d n with hk
  have hk1 : 1 ≤ k := le_min hd hn
  have hkn : k ≤ n := min_le_right _ _
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have e1 : ∀ a, (Fq n k (a+1) - Gq n d (a+1)) - (Fq n k a - Gq n d a)
      = (Fq n k (a+1) - Fq n k a) - (Gq n d (a+1) - Gq n d a) := fun a => by ring
  simp_rw [e1, abs_eq_two_pos]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, sumF n k hk1 hkn, sumG n d hn hd,
    ← Finset.mul_sum]
  by_cases hdn : d ≤ n
  · have hkd : k = d := min_eq_left hdn
    obtain ⟨e, rfl⟩ : ∃ e, d = e + 1 := ⟨d - 1, by omega⟩
    set β : ℝ := (e + 1) * ((e : ℝ) ^ 2 * (n : ℝ) ^ (e - 1)) / (n : ℝ) ^ (e + 1) with hβ
    have hterm : ∀ a ∈ Finset.range n,
        max (-((Fq n k (a+1) - Fq n k a) - (Gq n (e+1) (a+1) - Gq n (e+1) a))) 0 ≤ β := by
      intro a ha
      have ha' : a + 1 ≤ n := Finset.mem_range.mp ha
      apply max_le _ (by positivity)
      rw [hkd]
      set y : ℝ := ((a + 1 - e : ℕ) : ℝ) with hy
      have hF : (e + 1 : ℝ) * y ^ e / (n : ℝ) ^ (e + 1)
          ≤ Fq n (e+1) (a+1) - Fq n (e+1) a := by
        unfold Fq
        rw [← sub_div, Nat.choose_succ_succ', Nat.cast_add, add_sub_cancel_right]
        have h3 : (0 : ℝ) < (n.choose (e+1) : ℝ) := Nat.cast_pos.mpr (Nat.choose_pos hdn)
        have hf : (0 : ℝ) < (e.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos e
        have h1 : y ^ e ≤ (a.choose e : ℝ) * (e.factorial : ℝ) := by
          have := Nat.pow_le_choose (α := ℝ) e a
          rw [div_le_iff₀ hf] at this
          simpa [hy] using this
        have h2 : (n.choose (e+1) : ℝ) * ((e + 1 : ℝ) * (e.factorial : ℝ)) ≤ (n : ℝ) ^ (e+1) := by
          have := Nat.choose_le_pow_div (α := ℝ) (e+1) n
          rw [Nat.factorial_succ] at this
          push_cast at this
          rw [le_div_iff₀ (by positivity)] at this
          linarith
        rw [div_le_div_iff₀ (by positivity) h3]
        have hy0 : 0 ≤ y := by positivity
        calc (e + 1 : ℝ) * y ^ e * (n.choose (e+1) : ℝ)
            ≤ (e + 1 : ℝ) * ((a.choose e : ℝ) * (e.factorial : ℝ)) * (n.choose (e+1) : ℝ) := by
              gcongr
          _ = (a.choose e : ℝ) * ((n.choose (e+1) : ℝ) * ((e + 1 : ℝ) * (e.factorial : ℝ))) := by
              ring
          _ ≤ (a.choose e : ℝ) * (n : ℝ) ^ (e+1) := by gcongr
      have hG : Gq n (e+1) (a+1) - Gq n (e+1) a ≤ (e + 1 : ℝ) * ((a : ℝ) + 1) ^ e / (n : ℝ) ^ (e + 1) := by
        unfold Gq
        rw [div_pow, div_pow, ← sub_div]
        apply div_le_div_of_nonneg_right _ (by positivity)
        have := pow_sub_pow_le_c (e+1) ((a : ℝ) + 1) a ((a : ℝ) + 1) (Nat.cast_nonneg a)
          (by linarith) le_rfl
        push_cast
        simpa using this
      have hP : ((a : ℝ) + 1) ^ e - y ^ e ≤ (e : ℝ) ^ 2 * (n : ℝ) ^ (e - 1) := by
        have hy0 : 0 ≤ y := by positivity
        have hya : y ≤ (a : ℝ) + 1 := by
          rw [hy]; exact_mod_cast Nat.sub_le (a + 1) e
        have han : (a : ℝ) + 1 ≤ n := by exact_mod_cast ha'
        have hdiff : (a : ℝ) + 1 - y ≤ e := by
          have : a + 1 ≤ (a + 1 - e) + e := by omega
          have : ((a : ℝ) + 1) ≤ y + e := by rw [hy]; exact_mod_cast this
          linarith
        have := pow_sub_pow_le_c e ((a : ℝ) + 1) y n hy0 hya han
        have hc : 0 ≤ (e : ℝ) * (n : ℝ) ^ (e - 1) := by positivity
        calc ((a : ℝ) + 1) ^ e - y ^ e ≤ (e : ℝ) * (n : ℝ) ^ (e - 1) * ((a : ℝ) + 1 - y) := this
          _ ≤ (e : ℝ) * (n : ℝ) ^ (e - 1) * e := mul_le_mul_of_nonneg_left hdiff hc
          _ = (e : ℝ) ^ 2 * (n : ℝ) ^ (e - 1) := by ring
      have hfin : (e + 1 : ℝ) * ((a : ℝ) + 1) ^ e / (n : ℝ) ^ (e + 1)
          - (e + 1 : ℝ) * y ^ e / (n : ℝ) ^ (e + 1) ≤ β := by
        rw [← sub_div, ← mul_sub, hβ]
        apply div_le_div_of_nonneg_right _ (by positivity)
        exact mul_le_mul_of_nonneg_left hP (by positivity)
      push_cast
      linarith
    have hs := Finset.sum_le_sum hterm
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hs
    have hnb : (n : ℝ) * β = (e + 1) * (e : ℝ) ^ 2 / n := by
      rw [hβ]
      cases e with
      | zero => simp
      | succ f =>
        simp only [Nat.add_sub_cancel]
        field_simp
        ring
    have hlast : (e + 1 : ℝ) * (e : ℝ) ^ 2 / n ≤ ((e + 1 : ℕ) : ℝ) ^ 3 / n := by
      apply div_le_div_of_nonneg_right _ hnR.le
      push_cast
      have he : (0 : ℝ) ≤ e := Nat.cast_nonneg e
      nlinarith [sq_nonneg (e : ℝ)]
    have : (1 : ℝ) - 1 + 2 * ∑ a ∈ Finset.range n,
        max (-((Fq n k (a+1) - Fq n k a) - (Gq n (e+1) (a+1) - Gq n (e+1) a))) 0
          ≤ 2 * ((e + 1 : ℕ) : ℝ) ^ 3 / n := by
      rw [mul_div_assoc]
      nlinarith [hs, hnb, hlast]
    exact this
  · rw [not_le] at hdn
    have hterm : ∀ a ∈ Finset.range n,
        max (-((Fq n k (a+1) - Fq n k a) - (Gq n d (a+1) - Gq n d a))) 0
          ≤ Gq n d (a+1) - Gq n d a := by
      intro a _
      exact max_le (by linarith [dF_nonneg n k a]) (dG_nonneg n d a)
    have hs := Finset.sum_le_sum hterm
    rw [sumG n d hn hd] at hs
    have h2 : (2 : ℝ) ≤ 2 * (d : ℝ) ^ 3 / n := by
      rw [le_div_iff₀ hnR]
      have h1 : (n : ℝ) ≤ d := by exact_mod_cast hdn.le
      have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
      nlinarith [mul_le_mul hd1 hd1 zero_le_one (by linarith : (0:ℝ) ≤ d)]
    linarith

/-! ### Chain (telescoping along the level counts) -/

lemma tele_Ico (H : ℕ → ℝ) (m n : ℕ) (h : m ≤ n) :
    |H n - H m| ≤ ∑ a ∈ Finset.Ico m n, |H (a+1) - H a| := by
  rw [Finset.sum_Ico_eq_sum_range]
  have hs : ∑ k ∈ Finset.range (n - m), (H (m + k + 1) - H (m + k)) = H n - H m := by
    have := Finset.sum_range_sub (fun k => H (m + k)) (n - m)
    simp only [add_zero] at this
    rw [Nat.add_sub_cancel' h] at this
    exact this
  rw [← hs]
  exact Finset.abs_sum_le_sum_abs _ _

lemma chain (H : ℕ → ℝ) (A : ℕ → ℕ) (hA : Antitone A) (B : ℕ) :
    ∑ i ∈ Finset.range B, |H (A i) - H (A (i+1))|
      ≤ ∑ a ∈ Finset.Ico (A B) (A 0), |H (a+1) - H a| := by
  induction B with
  | zero => simp
  | succ B ih =>
    rw [Finset.sum_range_succ]
    have hle : A (B+1) ≤ A B := hA (Nat.le_succ B)
    have hle0 : A B ≤ A 0 := hA (Nat.zero_le B)
    have h1 := tele_Ico H (A (B+1)) (A B) hle
    rw [← Finset.sum_Ico_consecutive _ hle hle0]
    linarith

/-! ### Graph part -/

def Acnt (M : ℕ → ℕ) (G : (N : ℕ) → Finset (Fin N × Fin (M N))) (N : ℕ) (z : Fin N → ℕ)
    (w : Fin (M N)) (i : ℕ) : ℕ :=
  ((nbrW M G N w).filter (fun v => i ≤ z v)).card

lemma tail_leqd (M : ℕ → ℕ) (G : (N : ℕ) → Finset (Fin N × Fin (M N))) (N : ℕ)
    (z : Fin N → ℕ) (w : Fin (M N)) (i : ℕ) :
    tailOf (leqd M G N z w) i = (Acnt M G N z w i : ℝ) / ((nbrW M G N w).card : ℝ) := by
  set B : ℕ := ∑ v, z v + 1 with hB
  have hzB : ∀ v, z v < B := fun v => by
    have := Finset.single_le_sum (f := z) (fun _ _ => Nat.zero_le _) (Finset.mem_univ v)
    omega
  unfold tailOf
  rw [tsum_eq_sum (s := Finset.range B)]
  · unfold leqd Acnt
    have hcount : ((nbrW M G N w).filter (fun v => i ≤ z v)).card
        = ∑ j ∈ Finset.range B,
            (if i ≤ j then ((nbrW M G N w).filter (fun v => z v = j)).card else 0) := by
      rw [Finset.card_eq_sum_card_fiberwise (f := z) (t := Finset.range B)]
      · apply Finset.sum_congr rfl
        intro j _
        split_ifs with hij
        · congr 1; ext v; simp only [Finset.mem_filter]
          constructor
          · rintro ⟨⟨h1, _⟩, h3⟩; exact ⟨h1, h3⟩
          · rintro ⟨h1, h3⟩; exact ⟨⟨h1, h3 ▸ hij⟩, h3⟩
        · rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
          intro v hv; simp only [Finset.mem_filter] at hv; omega
      · intro v _; exact Finset.mem_range.mpr (hzB v)
    rw [hcount]; push_cast
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro j _; split_ifs <;> simp
  · intro j hj
    have hj' : B ≤ j := by simpa using hj
    split_ifs
    · unfold leqd
      rw [show ((nbrW M G N w).filter (fun v => z v = j)) = ∅ by
        rw [Finset.filter_eq_empty_iff]; intro v _ h; have := hzB v; omega]
      simp
    · rfl

lemma Acnt_le (M : ℕ → ℕ) (G : (N : ℕ) → Finset (Fin N × Fin (M N))) (N : ℕ)
    (z : Fin N → ℕ) (w : Fin (M N)) (i : ℕ) : Acnt M G N z w i ≤ (nbrW M G N w).card :=
  Finset.card_filter_le _ _

lemma Acnt_anti (M : ℕ → ℕ) (G : (N : ℕ) → Finset (Fin N × Fin (M N))) (N : ℕ)
    (z : Fin N → ℕ) (w : Fin (M N)) : Antitone (fun i => Acnt M G N z w i) := by
  intro i j hij
  apply Finset.card_le_card
  intro v hv
  simp only [Finset.mem_filter] at hv ⊢
  exact ⟨hv.1, le_trans hij hv.2⟩

lemma argmin_map {N : ℕ} (σ : Equiv.Perm (Fin N)) (z : Fin N → ℕ) (hz : ∀ u, z (σ u) = z u)
    (U : Finset (Fin N)) :
    argminSet (U.map σ.toEmbedding) z = (argminSet U z).map σ.toEmbedding := by
  ext x
  constructor
  · intro hx
    rw [argminSet, Finset.mem_filter, Finset.mem_map] at hx
    obtain ⟨⟨a, ha, rfl⟩, hmin⟩ := hx
    rw [Finset.mem_map]
    refine ⟨a, ?_, rfl⟩
    rw [argminSet, Finset.mem_filter]
    refine ⟨ha, fun b hb => ?_⟩
    have := hmin (σ.toEmbedding b) (Finset.mem_map_of_mem _ hb)
    simpa [hz] using this
  · intro hx
    rw [Finset.mem_map] at hx
    obtain ⟨a, ha, rfl⟩ := hx
    rw [argminSet, Finset.mem_filter] at ha ⊢
    refine ⟨Finset.mem_map_of_mem _ ha.1, fun u' hu' => ?_⟩
    rw [Finset.mem_map] at hu'
    obtain ⟨b, hb, rfl⟩ := hu'
    simpa [hz] using ha.2 b hb

lemma jr_out (M : ℕ → ℕ) (G : (N : ℕ) → Finset (Fin N × Fin (M N))) (N d : ℕ)
    (w : Fin (M N)) (z : Fin N → ℕ) (v : Fin N) (hv : v ∉ nbrW M G N w) :
    jsqdRoute M G N d w z v = 0 := by
  unfold jsqdRoute
  rw [Finset.sum_eq_zero, mul_zero]
  intro U hU
  rw [Finset.mem_powersetCard] at hU
  rw [if_neg]
  intro h
  exact hv (hU.1 (Finset.filter_subset _ _ h))

lemma jr_perm (M : ℕ → ℕ) (G : (N : ℕ) → Finset (Fin N × Fin (M N))) (N d : ℕ)
    (w : Fin (M N)) (z : Fin N → ℕ) (σ : Equiv.Perm (Fin N)) (hz : ∀ u, z (σ u) = z u)
    (hN : ∀ u, σ u ∈ nbrW M G N w ↔ u ∈ nbrW M G N w) (v : Fin N) :
    jsqdRoute M G N d w z (σ v) = jsqdRoute M G N d w z v := by
  unfold jsqdRoute
  congr 1
  have hz' : ∀ u, z (σ.symm u) = z u := fun u => by simpa using (hz (σ.symm u)).symm
  have hmap : ∀ (τ : Equiv.Perm (Fin N)), (∀ u, τ u ∈ nbrW M G N w ↔ u ∈ nbrW M G N w) →
      ∀ U ∈ (nbrW M G N w).powersetCard (min d (nbrW M G N w).card),
        U.map τ.toEmbedding ∈ (nbrW M G N w).powersetCard (min d (nbrW M G N w).card) := by
    intro τ hτ U hU
    rw [Finset.mem_powersetCard] at hU ⊢
    refine ⟨fun x hx => ?_, by rw [Finset.card_map]; exact hU.2⟩
    rw [Finset.mem_map] at hx
    obtain ⟨b, hb, rfl⟩ := hx
    exact (hτ b).mpr (hU.1 hb)
  have hNs : ∀ u, σ.symm u ∈ nbrW M G N w ↔ u ∈ nbrW M G N w := fun u => by
    simpa using (hN (σ.symm u)).symm
  apply Finset.sum_nbij' (fun U => U.map σ.symm.toEmbedding) (fun U => U.map σ.toEmbedding)
  · exact hmap σ.symm hNs
  · exact hmap σ hN
  · intro U _; ext x; simp [Finset.mem_map_equiv]
  · intro U _; ext x; simp [Finset.mem_map_equiv]
  · intro U _
    rw [argmin_map σ.symm z hz' U, Finset.card_map]
    by_cases h : σ v ∈ argminSet U z
    · rw [if_pos h, if_pos (Finset.mem_map_equiv.mpr (by simpa using h))]
    · rw [if_neg h, if_neg (fun h' => h (by simpa using Finset.mem_map_equiv.mp h'))]

lemma jr_const (M : ℕ → ℕ) (G : (N : ℕ) → Finset (Fin N × Fin (M N))) (N d : ℕ)
    (w : Fin (M N)) (z : Fin N → ℕ) (v v' : Fin N) (hv : v ∈ nbrW M G N w)
    (hv' : v' ∈ nbrW M G N w) (hzz : z v = z v') :
    jsqdRoute M G N d w z v' = jsqdRoute M G N d w z v := by
  have hz : ∀ u, z (Equiv.swap v v' u) = z u := by
    intro u
    rw [Equiv.swap_apply_def]
    split_ifs with h1 h2
    · rw [h1, hzz]
    · rw [h2, hzz]
    · rfl
  have hN : ∀ u, Equiv.swap v v' u ∈ nbrW M G N w ↔ u ∈ nbrW M G N w := by
    intro u
    rw [Equiv.swap_apply_def]
    split_ifs with h1 h2
    · rw [h1]; exact ⟨fun _ => hv, fun _ => hv'⟩
    · rw [h2]; exact ⟨fun _ => hv', fun _ => hv⟩
    · exact Iff.rfl
  have := jr_perm M G N d w z (Equiv.swap v v') hz hN v
  rwa [Equiv.swap_apply_left] at this

noncomputable def Hq (n k d a : ℕ) : ℝ := Fq n k a - Gq n d a

lemma jr_level (M : ℕ → ℕ) (G : (N : ℕ) → Finset (Fin N × Fin (M N))) (N d : ℕ)
    (w : Fin (M N)) (z : Fin N → ℕ) (hd : 1 ≤ d) (hn : 1 ≤ (nbrW M G N w).card) (i : ℕ) :
    ∑ v ∈ (nbrW M G N w).filter (fun u => z u = i), jsqdRoute M G N d w z v
      = Fq (nbrW M G N w).card (min d (nbrW M G N w).card) (Acnt M G N z w i)
        - Fq (nbrW M G N w).card (min d (nbrW M G N w).card) (Acnt M G N z w (i+1)) := by
  unfold jsqdRoute
  rw [← Finset.mul_sum, Finset.sum_comm]
  have hk1 : 1 ≤ min d (nbrW M G N w).card := le_min hd hn
  have hU : ∀ U ∈ (nbrW M G N w).powersetCard (min d (nbrW M G N w).card),
      ∑ v ∈ (nbrW M G N w).filter (fun u => z u = i),
          (if v ∈ argminSet U z then ((argminSet U z).card : ℝ)⁻¹ else 0)
        = if (∀ u ∈ U, i ≤ z u) ∧ ¬ (∀ u ∈ U, i + 1 ≤ z u) then 1 else 0 := by
    intro U hUP
    rw [Finset.mem_powersetCard] at hUP
    have hne : U.Nonempty := Finset.card_pos.mp (by omega)
    obtain ⟨u0, hu0, hmin⟩ := Finset.exists_min_image U z hne
    have hu0A : u0 ∈ argminSet U z := Finset.mem_filter.mpr ⟨hu0, hmin⟩
    have hAz : ∀ x ∈ argminSet U z, z x = z u0 := fun x hx =>
      le_antisymm ((Finset.mem_filter.mp hx).2 u0 hu0) (hmin x (Finset.mem_filter.mp hx).1)
    by_cases hc : z u0 = i
    · rw [if_pos ⟨fun u hu => hc ▸ hmin u hu, fun h => by have := h u0 hu0; omega⟩]
      rw [← Finset.sum_filter]
      have hsub : ((nbrW M G N w).filter (fun u => z u = i)).filter (fun v => v ∈ argminSet U z)
          = argminSet U z := by
        ext x
        constructor
        · intro hx; exact (Finset.mem_filter.mp hx).2
        · intro hx
          refine Finset.mem_filter.mpr ⟨?_, hx⟩
          exact Finset.mem_filter.mpr ⟨hUP.1 (Finset.filter_subset _ _ hx), (hAz x hx).trans hc⟩
      rw [hsub, Finset.sum_const, nsmul_eq_mul]
      have hpos : (0 : ℝ) < ((argminSet U z).card : ℝ) :=
        Nat.cast_pos.mpr (Finset.card_pos.mpr ⟨u0, hu0A⟩)
      exact mul_inv_cancel₀ hpos.ne'
    · rw [if_neg (fun ⟨h1, h2⟩ => h2 (fun u hu => by
        have := h1 u0 hu0; have := hmin u hu; omega))]
      apply Finset.sum_eq_zero
      intro v hv
      rw [if_neg]
      intro hvA
      exact hc ((hAz v hvA).symm.trans (Finset.mem_filter.mp hv).2)
  rw [Finset.sum_congr rfl hU, Finset.sum_boole]
  have hcard : ∀ j, (((nbrW M G N w).powersetCard (min d (nbrW M G N w).card)).filter
      (fun U => ∀ u ∈ U, j ≤ z u)).card = (Acnt M G N z w j).choose (min d (nbrW M G N w).card) := by
    intro j
    rw [Acnt, ← Finset.card_powersetCard]
    congr 1
    ext U
    simp only [Finset.mem_filter, Finset.mem_powersetCard, Finset.subset_iff]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨fun x hx => ⟨h1 hx, h3 x hx⟩, h2⟩
    · rintro ⟨h1, h2⟩; exact ⟨⟨fun x hx => (h1 hx).1, h2⟩, fun x hx => (h1 hx).2⟩
  have hsplit : ((nbrW M G N w).powersetCard (min d (nbrW M G N w).card)).filter
        (fun U => ∀ u ∈ U, i ≤ z u)
      = ((nbrW M G N w).powersetCard (min d (nbrW M G N w).card)).filter
          (fun U => (∀ u ∈ U, i ≤ z u) ∧ ¬ (∀ u ∈ U, i + 1 ≤ z u))
        ∪ ((nbrW M G N w).powersetCard (min d (nbrW M G N w).card)).filter
          (fun U => ∀ u ∈ U, i + 1 ≤ z u) := by
    ext U
    simp only [Finset.mem_union, Finset.mem_filter]
    constructor
    · rintro ⟨hP, h⟩
      by_cases h' : ∀ u ∈ U, i + 1 ≤ z u
      · exact Or.inr ⟨hP, h'⟩
      · exact Or.inl ⟨hP, h, h'⟩
    · rintro (⟨hP, h, _⟩ | ⟨hP, h'⟩)
      · exact ⟨hP, h⟩
      · exact ⟨hP, fun u hu => by have := h' u hu; omega⟩
  have hdisj : Disjoint (((nbrW M G N w).powersetCard (min d (nbrW M G N w).card)).filter
          (fun U => (∀ u ∈ U, i ≤ z u) ∧ ¬ (∀ u ∈ U, i + 1 ≤ z u)))
        (((nbrW M G N w).powersetCard (min d (nbrW M G N w).card)).filter
          (fun U => ∀ u ∈ U, i + 1 ≤ z u)) :=
    Finset.disjoint_filter.mpr (fun U _ h1 h2 => h1.2 h2)
  have hc := congrArg Finset.card hsplit
  first
    | rw [Finset.card_union_of_disjoint hdisj] at hc
    | rw [Finset.card_union_eq_card_add_card.mpr hdisj] at hc
  rw [hcard, hcard] at hc
  have hR := congrArg (Nat.cast (R := ℝ)) hc
  push_cast at hR
  unfold Fq
  rw [← sub_div, div_eq_inv_mul]
  congr 1
  linarith

lemma pr_level (M : ℕ → ℕ) (G : (N : ℕ) → Finset (Fin N × Fin (M N))) (N d : ℕ)
    (w : Fin (M N)) (z : Fin N → ℕ) (v : Fin N) (hv : v ∈ nbrW M G N w) :
    piRoute M G N (jsqdAssign d) w z v
      = (Gq (nbrW M G N w).card d (Acnt M G N z w (z v))
          - Gq (nbrW M G N w).card d (Acnt M G N z w (z v + 1)))
        / (((nbrW M G N w).filter (fun u => z u = z v)).card : ℝ) := by
  unfold piRoute jsqdAssign Gq
  rw [if_pos hv, tail_leqd, tail_leqd]

/-- K3a. -/
theorem tv_jsqd (M : ℕ → ℕ) (G : (N : ℕ) → Finset (Fin N × Fin (M N))) (N d : ℕ)
    (hd : 1 ≤ d) (w : Fin (M N)) (z : Fin N → ℕ) :
    ∑ v : Fin N, |jsqdRoute M G N d w z v - piRoute M G N (jsqdAssign d) w z v|
      ≤ 2 * (d : ℝ) ^ 3 / (nbrW M G N w).card := by
  have hout : ∀ v ∈ (Finset.univ : Finset (Fin N)), v ∉ nbrW M G N w →
      |jsqdRoute M G N d w z v - piRoute M G N (jsqdAssign d) w z v| = 0 := by
    intro v _ hv
    rw [jr_out M G N d w z v hv]
    unfold piRoute
    rw [if_neg hv]; simp
  rw [← Finset.sum_subset (Finset.subset_univ (nbrW M G N w)) hout]
  rcases Nat.eq_zero_or_pos (nbrW M G N w).card with h0 | hn
  · rw [Finset.card_eq_zero.mp h0]; simp
  have hzB : ∀ v, z v < ∑ u, z u + 1 := fun v => by
    have := Finset.single_le_sum (f := z) (fun _ _ => Nat.zero_le _) (Finset.mem_univ v)
    omega
  rw [← Finset.sum_fiberwise_of_maps_to (g := z) (t := Finset.range (∑ u, z u + 1))
    (fun v _ => Finset.mem_range.mpr (hzB v))]
  have hlev : ∀ i ∈ Finset.range (∑ u, z u + 1),
      ∑ v ∈ (nbrW M G N w).filter (fun v => z v = i),
          |jsqdRoute M G N d w z v - piRoute M G N (jsqdAssign d) w z v|
        ≤ |Hq (nbrW M G N w).card (min d (nbrW M G N w).card) d (Acnt M G N z w i)
            - Hq (nbrW M G N w).card (min d (nbrW M G N w).card) d (Acnt M G N z w (i+1))| := by
    intro i _
    rcases ((nbrW M G N w).filter (fun v => z v = i)).eq_empty_or_nonempty with hE | ⟨v0, hv0⟩
    · rw [hE, Finset.sum_empty]; exact abs_nonneg _
    have hv0' := Finset.mem_filter.mp hv0
    have hconst : ∀ v ∈ (nbrW M G N w).filter (fun v => z v = i),
        jsqdRoute M G N d w z v - piRoute M G N (jsqdAssign d) w z v
          = jsqdRoute M G N d w z v0 - piRoute M G N (jsqdAssign d) w z v0 := by
      intro v hv
      have hv' := Finset.mem_filter.mp hv
      rw [jr_const M G N d w z v0 v hv0'.1 hv'.1 (hv0'.2.trans hv'.2.symm),
        pr_level M G N d w z v hv'.1, pr_level M G N d w z v0 hv0'.1, hv'.2, hv0'.2]
    have hsumabs : ∑ v ∈ (nbrW M G N w).filter (fun v => z v = i),
          |jsqdRoute M G N d w z v - piRoute M G N (jsqdAssign d) w z v|
        = |∑ v ∈ (nbrW M G N w).filter (fun v => z v = i),
          (jsqdRoute M G N d w z v - piRoute M G N (jsqdAssign d) w z v)| := by
      rw [Finset.sum_congr rfl (fun v hv => congrArg abs (hconst v hv)),
        Finset.sum_congr rfl hconst, Finset.sum_const, Finset.sum_const, nsmul_eq_mul,
        nsmul_eq_mul, abs_mul, Nat.abs_cast]
    have hpr : ∑ v ∈ (nbrW M G N w).filter (fun v => z v = i),
          piRoute M G N (jsqdAssign d) w z v
        = Gq (nbrW M G N w).card d (Acnt M G N z w i)
          - Gq (nbrW M G N w).card d (Acnt M G N z w (i + 1)) := by
      rw [Finset.sum_congr rfl (fun v hv => by
        rw [pr_level M G N d w z v (Finset.mem_filter.mp hv).1, (Finset.mem_filter.mp hv).2])]
      rw [Finset.sum_const, nsmul_eq_mul]
      have hpos : (0 : ℝ) < (((nbrW M G N w).filter (fun u => z u = i)).card : ℝ) :=
        Nat.cast_pos.mpr (Finset.card_pos.mpr ⟨v0, hv0⟩)
      field_simp
    rw [hsumabs, Finset.sum_sub_distrib, jr_level M G N d w z hd hn i, hpr]
    apply le_of_eq
    unfold Hq
    congr 1
    ring
  have hA0 := Acnt_le M G N z w 0
  calc ∑ i ∈ Finset.range (∑ u, z u + 1), ∑ v ∈ (nbrW M G N w).filter (fun v => z v = i),
          |jsqdRoute M G N d w z v - piRoute M G N (jsqdAssign d) w z v|
        ≤ ∑ i ∈ Finset.range (∑ u, z u + 1),
          |Hq (nbrW M G N w).card (min d (nbrW M G N w).card) d (Acnt M G N z w i)
            - Hq (nbrW M G N w).card (min d (nbrW M G N w).card) d (Acnt M G N z w (i+1))| :=
          Finset.sum_le_sum hlev
    _ ≤ ∑ a ∈ Finset.Ico (Acnt M G N z w (∑ u, z u + 1)) (Acnt M G N z w 0),
          |Hq (nbrW M G N w).card (min d (nbrW M G N w).card) d (a+1)
            - Hq (nbrW M G N w).card (min d (nbrW M G N w).card) d a| :=
          chain _ (fun i => Acnt M G N z w i) (Acnt_anti M G N z w) _
    _ ≤ ∑ a ∈ Finset.range (nbrW M G N w).card,
          |Hq (nbrW M G N w).card (min d (nbrW M G N w).card) d (a+1)
            - Hq (nbrW M G N w).card (min d (nbrW M G N w).card) d a| := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro a ha
            rw [Finset.mem_Ico] at ha
            rw [Finset.mem_range]
            omega
          · intro _ _ _; exact abs_nonneg _
    _ ≤ 2 * (d : ℝ) ^ 3 / (nbrW M G N w).card := tv_num _ d hn hd

/-! ### Row sums (session 9): both routing laws are probability vectors on a nonempty `𝒩_w`. -/

lemma Acnt_zero (M : ℕ → ℕ) (G : (N : ℕ) → Finset (Fin N × Fin (M N))) (N : ℕ)
    (z : Fin N → ℕ) (w : Fin (M N)) : Acnt M G N z w 0 = (nbrW M G N w).card := by
  unfold Acnt
  congr 1
  exact Finset.filter_true_of_mem (fun v _ => Nat.zero_le _)

lemma Acnt_big (M : ℕ → ℕ) (G : (N : ℕ) → Finset (Fin N × Fin (M N))) (N : ℕ)
    (z : Fin N → ℕ) (w : Fin (M N)) : Acnt M G N z w (∑ u, z u + 1) = 0 := by
  unfold Acnt
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro v _ h
  have := Finset.single_le_sum (f := z) (fun _ _ => Nat.zero_le _) (Finset.mem_univ v)
  omega

lemma Acnt_split (M : ℕ → ℕ) (G : (N : ℕ) → Finset (Fin N × Fin (M N))) (N : ℕ)
    (z : Fin N → ℕ) (w : Fin (M N)) (i : ℕ) :
    Acnt M G N z w i = Acnt M G N z w (i+1) + ((nbrW M G N w).filter (fun u => z u = i)).card := by
  unfold Acnt
  have hdisj : Disjoint ((nbrW M G N w).filter (fun v => i + 1 ≤ z v))
      ((nbrW M G N w).filter (fun u => z u = i)) :=
    Finset.disjoint_filter.mpr (fun v _ h1 h2 => by omega)
  have hU : (nbrW M G N w).filter (fun v => i ≤ z v)
      = (nbrW M G N w).filter (fun v => i + 1 ≤ z v) ∪ (nbrW M G N w).filter (fun u => z u = i) := by
    ext v
    simp only [Finset.mem_union, Finset.mem_filter]
    constructor
    · rintro ⟨hv, h⟩
      by_cases h' : z v = i
      · exact Or.inr ⟨hv, h'⟩
      · exact Or.inl ⟨hv, by omega⟩
    · rintro (⟨hv, h⟩ | ⟨hv, h⟩)
      · exact ⟨hv, by omega⟩
      · exact ⟨hv, by omega⟩
  rw [hU]
  first
    | exact Finset.card_union_of_disjoint hdisj
    | exact Finset.card_union_eq_card_add_card.mpr hdisj

lemma level_sum (M : ℕ → ℕ) (G : (N : ℕ) → Finset (Fin N × Fin (M N))) (N : ℕ)
    (w : Fin (M N)) (z : Fin N → ℕ) (f : Fin N → ℝ) (H : ℕ → ℝ)
    (hout : ∀ v, v ∉ nbrW M G N w → f v = 0)
    (hlev : ∀ i, ∑ v ∈ (nbrW M G N w).filter (fun u => z u = i), f v
      = H (Acnt M G N z w i) - H (Acnt M G N z w (i+1))) :
    ∑ v, f v = H (nbrW M G N w).card - H 0 := by
  rw [← Finset.sum_subset (Finset.subset_univ (nbrW M G N w)) (fun v _ hv => hout v hv)]
  have hzB : ∀ v, z v < ∑ u, z u + 1 := fun v => by
    have := Finset.single_le_sum (f := z) (fun _ _ => Nat.zero_le _) (Finset.mem_univ v)
    omega
  rw [← Finset.sum_fiberwise_of_maps_to (g := z) (t := Finset.range (∑ u, z u + 1))
    (fun v _ => Finset.mem_range.mpr (hzB v))]
  rw [Finset.sum_congr rfl (fun i _ => hlev i)]
  have := Finset.sum_range_sub' (fun i => H (Acnt M G N z w i)) (∑ u, z u + 1)
  simp only [Acnt_zero, Acnt_big] at this
  exact this

theorem sum_jr (M : ℕ → ℕ) (G : (N : ℕ) → Finset (Fin N × Fin (M N))) (N d : ℕ)
    (hd : 1 ≤ d) (w : Fin (M N)) (z : Fin N → ℕ) (hn : 1 ≤ (nbrW M G N w).card) :
    ∑ v, jsqdRoute M G N d w z v = 1 := by
  rw [level_sum M G N w z _ (Fq (nbrW M G N w).card (min d (nbrW M G N w).card))
    (jr_out M G N d w z) (jr_level M G N d w z hd hn)]
  have hk : min d (nbrW M G N w).card ≤ (nbrW M G N w).card := min_le_right _ _
  have hk1 : 1 ≤ min d (nbrW M G N w).card := le_min hd hn
  unfold Fq
  have hC : ((nbrW M G N w).card.choose (min d (nbrW M G N w).card) : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.choose_pos hk).ne'
  rw [div_self hC, Nat.choose_eq_zero_of_lt (by omega : 0 < min d (nbrW M G N w).card)]
  simp

theorem sum_pr (M : ℕ → ℕ) (G : (N : ℕ) → Finset (Fin N × Fin (M N))) (N d : ℕ)
    (hd : 1 ≤ d) (w : Fin (M N)) (z : Fin N → ℕ) (hn : 1 ≤ (nbrW M G N w).card) :
    ∑ v, piRoute M G N (jsqdAssign d) w z v = 1 := by
  have hout : ∀ v, v ∉ nbrW M G N w → piRoute M G N (jsqdAssign d) w z v = 0 := by
    intro v hv; unfold piRoute; rw [if_neg hv]
  have hlev : ∀ i, ∑ v ∈ (nbrW M G N w).filter (fun u => z u = i),
      piRoute M G N (jsqdAssign d) w z v
        = Gq (nbrW M G N w).card d (Acnt M G N z w i)
          - Gq (nbrW M G N w).card d (Acnt M G N z w (i + 1)) := by
    intro i
    rcases ((nbrW M G N w).filter (fun v => z v = i)).eq_empty_or_nonempty with hE | ⟨v0, hv0⟩
    · rw [hE, Finset.sum_empty, Acnt_split M G N z w i, hE, Finset.card_empty, add_zero, sub_self]
    rw [Finset.sum_congr rfl (fun v hv => by
      rw [pr_level M G N d w z v (Finset.mem_filter.mp hv).1, (Finset.mem_filter.mp hv).2])]
    rw [Finset.sum_const, nsmul_eq_mul]
    have hpos : (0 : ℝ) < (((nbrW M G N w).filter (fun u => z u = i)).card : ℝ) :=
      Nat.cast_pos.mpr (Finset.card_pos.mpr ⟨v0, hv0⟩)
    field_simp
  rw [level_sum M G N w z _ (Gq (nbrW M G N w).card d) hout hlev]
  unfold Gq
  have hn' : ((nbrW M G N w).card : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  rw [div_self hn', Nat.cast_zero, zero_div, zero_pow (by omega : d ≠ 0)]
  simp

end SC77K3A

namespace SC77R

open StrictCompatLB.MeanField

lemma lb_hasSum (lam : ℝ) (hlam : 0 < lam) (M : ℕ → ℕ) (N : ℕ) (hN : 1 ≤ N) (hM : 0 < M N)
    (route : Fin (M N) → (Fin N → ℕ) → Fin N → ℝ) (z : Fin N → ℕ)
    (hsum : ∀ w, ∑ v, route w z v = 1) : HasSum (lbKernel lam M N route z) 1 := by
  have h1 : HasSum (fun z' : Fin N → ℕ => ∑ w : Fin (M N), ∑ v : Fin N,
      route w z v * (if z' = arrive z v then (1 : ℝ) else 0))
      (∑ w : Fin (M N), ∑ v : Fin N, route w z v * 1) :=
    hasSum_sum (fun w _ => hasSum_sum (fun v _ =>
      (hasSum_ite_eq (arrive z v) (1 : ℝ)).mul_left (route w z v)))
  have h2 : HasSum (fun z' : Fin N → ℕ => ∑ v : Fin N, (if z' = depart z v then (1 : ℝ) else 0))
      (∑ v : Fin N, (1 : ℝ)) :=
    hasSum_sum (fun v _ => hasSum_ite_eq (depart z v) (1 : ℝ))
  have h := (h1.mul_left (lam / (lam + 1) * (1 / (M N : ℝ)))).add
    (h2.mul_left (1 / (lam + 1) * (1 / (N : ℝ))))
  have hval : lam / (lam + 1) * (1 / (M N : ℝ)) * (∑ w : Fin (M N), ∑ v : Fin N, route w z v * 1) +
      1 / (lam + 1) * (1 / (N : ℝ)) * (∑ v : Fin N, (1 : ℝ)) = 1 := by
    simp only [mul_one, hsum, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have hMr : (0 : ℝ) < M N := by exact_mod_cast hM
    have hNr : (0 : ℝ) < N := by exact_mod_cast hN
    have hl : (0 : ℝ) < lam + 1 := by linarith
    field_simp
  rw [hval] at h
  unfold lbKernel
  convert h using 1

lemma nbr_pos (M : ℕ → ℕ) (G : (N : ℕ) → Finset (Fin N × Fin (M N)))
    (hconn : IsConnectedSeq M G) (N : ℕ) (hN : 1 ≤ N) (w : Fin (M N)) :
    1 ≤ (nbrW M G N w).card := by
  have hc := hconn N hN
  obtain ⟨p⟩ := hc.preconnected (Sum.inr w) (Sum.inl (⟨0, by omega⟩ : Fin N))
  rcases p with _ | ⟨h, _⟩
  rw [compatGraph, SimpleGraph.fromRel_adj] at h
  obtain ⟨_, h | h⟩ := h
  · obtain ⟨v, w', h1, _⟩ := h
    cases h1
  · obtain ⟨v, w', rfl, h2, h3⟩ := h
    cases h2
    exact Finset.card_pos.mpr ⟨v, by simp [nbrW, h3]⟩

lemma hst (lam : ℝ) (hlam : 0 < lam) (d : ℕ) (hd : 1 ≤ d) (M : ℕ → ℕ) (hM : ∀ N, 0 < M N)
    (G : (N : ℕ) → Finset (Fin N × Fin (M N))) (hconn : IsConnectedSeq M G) :
    ∀ N, 1 ≤ N → IsStochasticKernel (jsqdKernel lam d M G N) := by
  intro N hN
  have hl : (0 : ℝ) ≤ lam + 1 := by linarith
  have hr : ∀ w z v, 0 ≤ jsqdRoute M G N d w z v := fun w z v => by
    unfold jsqdRoute
    apply mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))
    apply Finset.sum_nonneg
    intro U _
    split_ifs
    · exact inv_nonneg.mpr (Nat.cast_nonneg _)
    · exact le_refl 0
  refine ⟨fun z z' => ?_, fun z => ?_⟩
  · unfold jsqdKernel lbKernel
    apply add_nonneg
    · apply mul_nonneg (mul_nonneg (div_nonneg hlam.le hl) (by positivity))
      apply Finset.sum_nonneg; intro w _; apply Finset.sum_nonneg; intro v _
      apply mul_nonneg (hr w z v); split_ifs <;> norm_num
    · apply mul_nonneg (mul_nonneg (div_nonneg zero_le_one hl) (by positivity))
      apply Finset.sum_nonneg; intro v _; split_ifs <;> norm_num
  · exact lb_hasSum lam hlam M N hN (hM N) _ z
      (fun w => SC77K3A.sum_jr M G N d hd w z (nbr_pos M G hconn N hN w))

end SC77R

open StrictCompatLB.MeanField in
theorem solution (lam : ℝ) (hlam0 : 0 < lam) (hlam1 : lam < 1)
    (d : ℕ) (hd : 2 ≤ d)
    (M : ℕ → ℕ) (hM : ∀ N, 0 < M N) (G : (N : ℕ) → Finset (Fin N × Fin (M N)))
    (hconn : IsConnectedSeq M G) (hsparse : IsPropSparse M G) :
    (∀ (z₀ : (N : ℕ) → Fin N → ℕ) (q₀ : ℕ → ℝ), InY q₀ →
      Tendsto (fun N => PowerOfDUniversality.Fluid.l1dist (occ (z₀ N)) q₀) atTop (𝓝 0) →
      ∀ s : ℝ → ℕ → ℝ, PowerTwoChoices.Limit.IsTrajectory lam d s →
        (∀ t : ℝ, 0 ≤ t → InY (s t)) → s 0 = q₀ →
        ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω)
          (Y : (N : ℕ) → ℕ → Ω → (Fin N → ℕ)) (τ : ℕ → ℕ → Ω → ℝ),
          (∀ N, 1 ≤ N → IsLBProcess P lam M N (jsqdRoute M G N d) (z₀ N) (Y N) (τ N)) →
          ∀ T : ℝ, 0 ≤ T → ∀ ε : ℝ, 0 < ε →
            Tendsto (fun N => P {ω | ENNReal.ofReal ε ≤
                PowerOfDUniversality.Fluid.supDistL1 (occPath (Y N) (τ N) ω) s T})
              atTop (𝓝 0)) ∧
    (IsSubcritical d M G →
      ∃ N₀ : ℕ, (∀ N ≥ N₀, ∃! π : (Fin N → ℕ) → ℝ, IsStationary (jsqdKernel lam d M G N) π) ∧
        ∀ π : (N : ℕ) → (Fin N → ℕ) → ℝ,
          (∀ N ≥ N₀, IsStationary (jsqdKernel lam d M G N) (π N)) →
          ∀ ε : ℝ, 0 < ε →
            Tendsto (fun N => probOf (π N) {z | ENNReal.ofReal ε ≤
                PowerOfDUniversality.Fluid.l1dist (occ z) (PowerTwoChoices.Limit.fixedPoint lam d)})
              atTop (𝓝 0)) := by
  have hd1 : 1 ≤ d := by omega
  have hKpos : (0 : ℝ) < 2 * (d.factorial : ℝ) * (d : ℝ) ^ 2 := by
    have : (0 : ℝ) < d := by exact_mod_cast hd1
    positivity
  have conj1 : ∀ (z₀ : (N : ℕ) → Fin N → ℕ) (q₀ : ℕ → ℝ), InY q₀ →
      Tendsto (fun N => PowerOfDUniversality.Fluid.l1dist (occ (z₀ N)) q₀) atTop (𝓝 0) →
      ∀ s : ℝ → ℕ → ℝ, PowerTwoChoices.Limit.IsTrajectory lam d s →
        (∀ t : ℝ, 0 ≤ t → InY (s t)) → s 0 = q₀ →
        ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω)
          (Y : (N : ℕ) → ℕ → Ω → (Fin N → ℕ)) (τ : ℕ → ℕ → Ω → ℝ),
          (∀ N, 1 ≤ N → IsLBProcess P lam M N (jsqdRoute M G N d) (z₀ N) (Y N) (τ N)) →
          ∀ T : ℝ, 0 ≤ T → ∀ ε : ℝ, 0 < ε →
            Tendsto (fun N => P {ω | ENNReal.ofReal ε ≤
                PowerOfDUniversality.Fluid.supDistL1 (occPath (Y N) (τ N) ω) s T})
              atTop (𝓝 0) := by
    intro z₀ q₀ hq₀ hinit s hs hsY hs0 Ω _ P Y τ hproc T hT ε hε
    exact jsqd_subset_sampling_process_limit lam hlam0 hlam1 d hd M hM G hconn hsparse z₀ s T hT
      (fun Ω' _ P' Y' τ' hproc' ε' hε' =>
        theorem_4_3 lam hlam0 hlam1 M hM G hconn hsparse (jsqdAssign d)
          (SC77.jsqdAssign_isAssignmentFn d hd1) ⟨_, hKpos, lemma_4_2 d hd1⟩ z₀ q₀ hq₀ hinit s
          (SC77.traj_to_pi lam d s hs hsY) hsY hs0 Ω' P' Y' τ' hproc' T hT ε' hε')
      Ω P Y τ hproc ε hε
  refine ⟨conj1, fun hsub => ?_⟩
  obtain ⟨N₁, _, huniq⟩ := theorem_4_8_i lam hlam0 hlam1 d hd1 M hM G hconn hsub
  obtain ⟨ω, hω, r, hr1, hr2, h417, δ, hδ, hdec⟩ :=
    supermarket_ode_uniform_exp_decay lam hlam0 hlam1 d hd
  obtain ⟨N₂, hN₂, hex, htight⟩ :=
    theorem_4_8_ii lam hlam0 hlam1 d hd1 M hM G hconn hsub r hr1 hr2 ω hω (i0Index lam d) h417
  refine ⟨max N₁ N₂, fun N hN => huniq N (le_of_max_le_left hN), ?_⟩
  intro π hπ ε hε
  classical
  let π' : (N : ℕ) → (Fin N → ℕ) → ℝ := fun N =>
    if max N₁ N₂ ≤ N then π N else
      if h2 : N₂ ≤ N then Classical.choose (hex N h2) else π N
  have hπ' : ∀ N ≥ N₂, IsStationary (jsqdKernel lam d M G N) (π' N) := by
    intro N hN
    by_cases h : max N₁ N₂ ≤ N
    · simp only [π', if_pos h]
      exact hπ N h
    · simp only [π', if_neg h, dif_pos hN]
      exact Classical.choose_spec (hex N hN)
  have key := jsqd_stationary_concentration_of_process_limit lam hlam0 hlam1 d hd M hM G
    (SC77R.hst lam hlam0 d hd1 M hM G hconn) lb_process_exists conj1
    (supermarket_ode_exists_in_Y lam hlam0 hlam1 d hd) ω hω r hr1 hr2 (i0Index lam d) h417
    δ hδ hdec N₂ hN₂ π' hπ' (htight π' hπ') ε hε
  refine key.congr' ?_
  filter_upwards [eventually_ge_atTop (max N₁ N₂)] with N hN
  simp only [π', if_pos hN]
