-- Prove2me | solution 1 for SubsetShrink.BIC.eq_55
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-23T00:58:27.184735+00:00
-- url     : https://prove2.me/submissions/e6094c7d-23e9-49ef-b853-f50ec33c3f84

import Mathlib
import Definitions.Def_SubsetShrink_BIC_Model
import Theorems.Thm_SubsetShrink_Events_eq_28
import Theorems.Thm_SubsetShrink_BIC_union_bound

open MeasureTheory ProbabilityTheory

namespace BICCore

open SubsetShrink.Events SubsetShrink.BIC

/-- `g(m) = m log(ep/m)`. -/
noncomputable def gfun (p m : ℕ) : ℝ := (m : ℝ) * Real.log (Real.exp 1 * p / m)

lemma muB_mul {p : ℕ} (b : ℝ) (β : Fin p → ℝ) :
    muB b β * (l0 β : ℝ) = b * gfun p (l0 β) := by
  unfold muB gfun; ring

lemma lamB_eq {p : ℕ} (a : ℝ) (β : Fin p → ℝ) :
    lamB a β = a * Real.sqrt (gfun p (l0 β)) := rfl

lemma one_le_log_ep {p m : ℕ} (hm : 1 ≤ m) (hmp : m ≤ p) :
    1 ≤ Real.log (Real.exp 1 * p / m) := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hmp' : (m : ℝ) ≤ p := by exact_mod_cast hmp
  have hp' : (0 : ℝ) < p := lt_of_lt_of_le hm' hmp'
  rw [Real.le_log_iff_exp_le (by positivity)]
  rw [le_div_iff₀ hm']
  exact mul_le_mul_of_nonneg_left hmp' (Real.exp_pos 1).le

lemma gfun_nonneg {p m : ℕ} (hmp : m ≤ p) : 0 ≤ gfun p m := by
  unfold gfun
  rcases Nat.eq_zero_or_pos m with h | h
  · subst h; simp
  · have := one_le_log_ep (p := p) h hmp
    have : (0 : ℝ) ≤ m := by positivity
    nlinarith

lemma gfun_ge {p m : ℕ} (hm : 1 ≤ m) (hmp : m ≤ p) : (m : ℝ) ≤ gfun p m := by
  unfold gfun
  have := one_le_log_ep (p := p) hm hmp
  have : (0 : ℝ) ≤ m := by positivity
  nlinarith

lemma gfun_mono {p x y : ℕ} (hx : 1 ≤ x) (hxy : x ≤ y) (hyp : y ≤ p) :
    gfun p x ≤ gfun p y := by
  unfold gfun
  have hx' : (0 : ℝ) < x := by exact_mod_cast hx
  have hxy' : (x : ℝ) ≤ y := by exact_mod_cast hxy
  have hy' : (0 : ℝ) < y := lt_of_lt_of_le hx' hxy'
  have hyp' : (y : ℝ) ≤ p := by exact_mod_cast hyp
  have hp' : (0 : ℝ) < p := lt_of_lt_of_le hy' hyp'
  have e1 : ∀ t : ℝ, 0 < t → Real.log (Real.exp 1 * p / t) = 1 + Real.log p - Real.log t := by
    intro t ht
    rw [Real.log_div (by positivity) ht.ne', Real.log_mul (Real.exp_pos 1).ne' hp'.ne',
      Real.log_exp]
  rw [e1 x hx', e1 y hy']
  have h1 : Real.log y ≤ Real.log p := Real.log_le_log hy' hyp'
  have h2 : Real.log (y / x) ≤ y / x - 1 := Real.log_le_sub_one_of_pos (by positivity)
  rw [Real.log_div hy'.ne' hx'.ne'] at h2
  have h3 : x * (Real.log y - Real.log x) ≤ y - x := by
    have := mul_le_mul_of_nonneg_left h2 hx'.le
    have e : (x : ℝ) * (y / x - 1) = y - x := by field_simp
    linarith
  nlinarith

lemma gfun_subadd {p m k1 k2 : ℕ} (hm : m ≤ k1 + k2) (hmp : m ≤ p) (h1 : k1 ≤ p) (h2 : k2 ≤ p) :
    gfun p m ≤ gfun p k1 + gfun p k2 := by
  have g1 := gfun_nonneg h1
  have g2 := gfun_nonneg h2
  rcases Nat.eq_zero_or_pos m with h0 | hpos
  · subst h0
    have : gfun p 0 = 0 := by simp [gfun]
    linarith
  by_cases c1 : m ≤ k1
  · linarith [gfun_mono hpos c1 h1]
  by_cases c2 : m ≤ k2
  · linarith [gfun_mono hpos c2 h2]
  push Not at c1 c2
  have hm' : (0 : ℝ) < m := by exact_mod_cast hpos
  have hp' : (0 : ℝ) < p := by
    have : (0 : ℝ) < p := by exact_mod_cast (lt_of_lt_of_le hpos hmp)
    exact this
  have hL : 1 ≤ Real.log (Real.exp 1 * p / m) := one_le_log_ep hpos hmp
  have key : ∀ k : ℕ, k < m → (k : ℝ) * Real.log (Real.exp 1 * p / m) ≤ gfun p k := by
    intro k hk
    rcases Nat.eq_zero_or_pos k with hk0 | hk0
    · subst hk0; simp [gfun]
    · unfold gfun
      have hk' : (0 : ℝ) < k := by exact_mod_cast hk0
      have hkm : (k : ℝ) ≤ m := by exact_mod_cast hk.le
      have : Real.log (Real.exp 1 * p / m) ≤ Real.log (Real.exp 1 * p / k) :=
        Real.log_le_log (by positivity) (div_le_div_of_nonneg_left (by positivity) hk' hkm)
      exact mul_le_mul_of_nonneg_left this hk'.le
  have a1 := key k1 c1
  have a2 := key k2 c2
  have hmk : (m : ℝ) ≤ k1 + k2 := by exact_mod_cast hm
  have hmul : (m : ℝ) * Real.log (Real.exp 1 * p / m) ≤
      ((k1 : ℝ) + k2) * Real.log (Real.exp 1 * p / m) :=
    mul_le_mul_of_nonneg_right hmk (by linarith)
  have : gfun p m = (m : ℝ) * Real.log (Real.exp 1 * p / m) := rfl
  linarith

lemma l0_le {p : ℕ} (u : Fin p → ℝ) : l0 u ≤ p := by
  unfold l0
  calc (Finset.univ.filter (fun i => u i ≠ 0)).card ≤ Finset.univ.card := Finset.card_filter_le _ _
    _ = p := by simp

lemma l0_sub_le {p : ℕ} (u v : Fin p → ℝ) : l0 (u - v) ≤ l0 u + l0 v := by
  unfold l0
  calc (Finset.univ.filter (fun i => (u - v) i ≠ 0)).card
      ≤ (Finset.univ.filter (fun i => u i ≠ 0) ∪ Finset.univ.filter (fun i => v i ≠ 0)).card := by
        apply Finset.card_le_card
        intro i hi
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Pi.sub_apply] at hi
        simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
        by_contra h
        push Not at h
        apply hi; rw [h.1, h.2]; ring
    _ ≤ _ := Finset.card_union_le _ _

lemma eq_zero_of_l0 {p : ℕ} (u : Fin p → ℝ) (h : l0 u = 0) : u = 0 := by
  unfold l0 at h
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff] at h
  funext i
  by_contra hi
  exact h (Finset.mem_univ i) hi

/-- The basic inequality from optimality, for an arbitrary penalty. -/
lemma basic_ineq {n p : ℕ} (X : Matrix (Fin n) (Fin p) ℝ) (f ε : Fin n → ℝ)
    (βh β : Fin p → ℝ) (Ph P : ℝ)
    (h : ∑ i, ((f + ε) i - X.mulVec βh i) ^ 2 + Ph ≤ ∑ i, ((f + ε) i - X.mulVec β i) ^ 2 + P) :
    ∑ i, (f i - X.mulVec βh i) ^ 2 + Ph ≤
      ∑ i, (f i - X.mulVec β i) ^ 2 + 2 * dot ε (X.mulVec (βh - β)) + P := by
  have e : ∑ i, ((f + ε) i - X.mulVec βh i) ^ 2 - ∑ i, ((f + ε) i - X.mulVec β i) ^ 2 =
      ∑ i, (f i - X.mulVec βh i) ^ 2 - ∑ i, (f i - X.mulVec β i) ^ 2
        - 2 * dot ε (X.mulVec (βh - β)) := by
    unfold dot
    rw [Matrix.mulVec_sub, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib,
      ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    simp only [Pi.add_apply, Pi.sub_apply]
    ring
  linarith

/-- Minkowski: `‖a - b‖ ≤ ‖a‖ + ‖b‖` for the Euclidean norm written with sums. -/
lemma sqrt_sum_sub_le {n : ℕ} (a b : Fin n → ℝ) :
    Real.sqrt (∑ i, (a i - b i) ^ 2) ≤ Real.sqrt (∑ i, a i ^ 2) + Real.sqrt (∑ i, b i ^ 2) := by
  have hA : 0 ≤ ∑ i, a i ^ 2 := Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have hB : 0 ≤ ∑ i, b i ^ 2 := Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have cs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ a b
  have hab : -(∑ i, a i * b i) ≤ Real.sqrt (∑ i, a i ^ 2) * Real.sqrt (∑ i, b i ^ 2) := by
    rw [← Real.sqrt_mul hA]
    have : |∑ i, a i * b i| ≤ Real.sqrt ((∑ i, a i ^ 2) * ∑ i, b i ^ 2) := by
      rw [← Real.sqrt_sq_eq_abs]; exact Real.sqrt_le_sqrt cs
    linarith [neg_abs_le (∑ i, a i * b i), le_abs_self (-(∑ i, a i * b i)), abs_neg (∑ i, a i * b i)]
  rw [Real.sqrt_le_left (by positivity)]
  have e : ∑ i, (a i - b i) ^ 2 = ∑ i, a i ^ 2 - 2 * ∑ i, a i * b i + ∑ i, b i ^ 2 := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro i _; ring
  rw [e]
  have := Real.sq_sqrt hA
  have := Real.sq_sqrt hB
  nlinarith

lemma l2_X_sub_le {n p : ℕ} (X : Matrix (Fin n) (Fin p) ℝ) (f : Fin n → ℝ) (βh β : Fin p → ℝ) :
    l2 (X.mulVec (βh - β)) ≤
      Real.sqrt (∑ i, (f i - X.mulVec βh i) ^ 2) + Real.sqrt (∑ i, (f i - X.mulVec β i) ^ 2) := by
  have := sqrt_sum_sub_le (fun i => f i - X.mulVec β i) (fun i => f i - X.mulVec βh i)
  unfold l2
  rw [add_comm]
  convert this using 3
  rw [Matrix.mulVec_sub]
  simp only [Pi.sub_apply]
  ring

/-- `2 t (A + B) ≤ 3 t² + A²/2 + B²`. -/
lemma amgm (t A B : ℝ) : 2 * t * (A + B) ≤ 3 * t ^ 2 + A ^ 2 / 2 + B ^ 2 := by
  nlinarith [sq_nonneg (A - 2 * t), sq_nonneg (B - t)]

lemma dot_zero_right {n : ℕ} (ε : Fin n → ℝ) : dot ε 0 = 0 := by
  simp [dot]

/-! ### sorted sums -/

lemma sortedSum_sub_le {p : ℕ} (u v : Fin p → ℝ) :
    sortedSum (u - v) ≤ sortedSum u + sortedSum v := by
  unfold sortedSum
  apply Finset.sup'_le
  intro π _
  have hu := Finset.le_sup' (fun π : Equiv.Perm (Fin p) =>
    ∑ j : Fin p, |u (π j)| * Real.sqrt (Real.log (2 * (p : ℝ) / ((j.val : ℝ) + 1))))
    (Finset.mem_univ π)
  have hv := Finset.le_sup' (fun π : Equiv.Perm (Fin p) =>
    ∑ j : Fin p, |v (π j)| * Real.sqrt (Real.log (2 * (p : ℝ) / ((j.val : ℝ) + 1))))
    (Finset.mem_univ π)
  refine le_trans ?_ (add_le_add hu hv)
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro j _
  rw [← add_mul]
  apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg _)
  simp only [Pi.sub_apply]
  exact abs_sub _ _

lemma sortedSum_zero {p : ℕ} : sortedSum (0 : Fin p → ℝ) = 0 := by
  unfold sortedSum
  simp

lemma sortedSum_le_l1 {p : ℕ} (hp : 1 ≤ p) (u : Fin p → ℝ) :
    sortedSum u ≤ Real.sqrt (Real.log (2 * p)) * l1 u := by
  unfold sortedSum l1
  apply Finset.sup'_le
  intro π _
  have hp' : (0 : ℝ) < p := by exact_mod_cast hp
  calc ∑ j : Fin p, |u (π j)| * Real.sqrt (Real.log (2 * (p : ℝ) / ((j.val : ℝ) + 1)))
      ≤ ∑ j : Fin p, |u (π j)| * Real.sqrt (Real.log (2 * p)) := by
        apply Finset.sum_le_sum
        intro j _
        apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
        apply Real.sqrt_le_sqrt
        apply Real.log_le_log (by positivity)
        apply div_le_self (by positivity)
        have : (0 : ℝ) ≤ j.val := by positivity
        linarith
    _ = Real.sqrt (Real.log (2 * p)) * ∑ i, |u i| := by
        rw [Finset.mul_sum]
        rw [← Equiv.sum_comp π (fun i => Real.sqrt (Real.log (2 * p)) * |u i|)]
        apply Finset.sum_congr rfl; intro j _; ring

lemma log_two_le_one : Real.log 2 ≤ 1 := by
  have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
  linarith

/-- `sortedSum v ≤ √2 √(g(‖v‖₀)) ‖v‖`. -/
lemma sortedSum_le_g {p : ℕ} (hp : 1 ≤ p) (v : Fin p → ℝ) :
    sortedSum v ≤ Real.sqrt 2 * Real.sqrt (gfun p (l0 v)) * l2 v := by
  rcases Nat.eq_zero_or_pos (l0 v) with h0 | hpos
  · have := eq_zero_of_l0 v h0
    subst this
    rw [sortedSum_zero]
    have : l2 (0 : Fin p → ℝ) = 0 := by simp [l2]
    rw [this]; simp
  · have h28 := (SubsetShrink.Events.eq_28 hpos (l0_le v) v le_rfl)
    have hk : (0 : ℝ) < (l0 v : ℝ) := by exact_mod_cast hpos
    have hL := one_le_log_ep (p := p) hpos (l0_le v)
    have hp' : (0 : ℝ) < p := by exact_mod_cast hp
    have hlog : Real.log (2 * Real.exp 1 * p / (l0 v : ℝ)) ≤
        2 * Real.log (Real.exp 1 * p / (l0 v : ℝ)) := by
      have : 2 * Real.exp 1 * p / (l0 v : ℝ) = 2 * (Real.exp 1 * p / (l0 v : ℝ)) := by ring
      rw [this, Real.log_mul (by norm_num) (by positivity)]
      linarith [log_two_le_one]
    have hsq : Real.sqrt ((l0 v : ℝ) * Real.log (2 * Real.exp 1 * p / (l0 v : ℝ))) ≤
        Real.sqrt 2 * Real.sqrt (gfun p (l0 v)) := by
      rw [← Real.sqrt_mul (by norm_num)]
      apply Real.sqrt_le_sqrt
      unfold gfun
      nlinarith
    have hl2 : 0 ≤ l2 v := Real.sqrt_nonneg _
    calc sortedSum v ≤ Real.sqrt ((l0 v : ℝ) * Real.log (2 * Real.exp 1 * p / (l0 v : ℝ))) * l2 v :=
          le_trans h28.1 h28.2
      _ ≤ Real.sqrt 2 * Real.sqrt (gfun p (l0 v)) * l2 v := mul_le_mul_of_nonneg_right hsq hl2

lemma sqrt_two_le : Real.sqrt 2 ≤ 3 / 2 := by
  rw [Real.sqrt_le_left (by norm_num)]; norm_num

lemma c_sq_le : (4 + Real.sqrt 2) ^ 2 ≤ 30 := by
  have h2 := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  have := sqrt_two_le
  have := Real.sqrt_nonneg 2
  nlinarith

lemma log_one_div_nonneg {x : ℝ} (h0 : 0 < x) (h1 : x ≤ 1) : 0 ≤ Real.log (1 / x) := by
  apply Real.log_nonneg
  rw [le_div_iff₀ h0]; linarith

/-- On the event `G = ⋂_s G'_s` (with `δ_s = (s/[ep])^s ϵ0`), the cross term is controlled. -/
lemma onG_bound {n p : ℕ} (X : Matrix (Fin n) (Fin p) ℝ) (σ ϵ0 : ℝ) (hσ : 0 < σ)
    (hϵ0 : 0 < ϵ0) (hϵ1 : ϵ0 < 1) (f ε : Fin n → ℝ) (βh β : Fin p → ℝ)
    (hG : ε ∈ ⋂ s ∈ Finset.Icc 1 p, Gc X σ (((s : ℝ) / (Real.exp 1 * p)) ^ s * ϵ0) s) :
    2 * dot ε (X.mulVec (βh - β)) ≤
      24 * σ ^ 2 * (gfun p (l0 βh) + gfun p (l0 β)) + 9 * (σ ^ 2 * Real.log (1 / ϵ0)) +
        (∑ i, (f i - X.mulVec βh i) ^ 2) / 2 + ∑ i, (f i - X.mulVec β i) ^ 2 := by
  have hL := log_one_div_nonneg hϵ0 hϵ1.le
  have gh := gfun_nonneg (l0_le βh)
  have g0 := gfun_nonneg (l0_le β)
  have hSh : 0 ≤ ∑ i, (f i - X.mulVec βh i) ^ 2 := Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have hS : 0 ≤ ∑ i, (f i - X.mulVec β i) ^ 2 := Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have hσ2 : 0 ≤ σ ^ 2 := sq_nonneg σ
  have p1 : 0 ≤ σ ^ 2 * (gfun p (l0 βh) + gfun p (l0 β)) := mul_nonneg hσ2 (by linarith)
  have p2 : 0 ≤ σ ^ 2 * Real.log (1 / ϵ0) := mul_nonneg hσ2 hL
  set u := βh - β with hu
  rcases Nat.eq_zero_or_pos (l0 u) with h0 | hpos
  · have : u = 0 := eq_zero_of_l0 u h0
    rw [this, Matrix.mulVec_zero, dot_zero_right]
    linarith
  · set s := l0 u with hs
    have hsp : s ≤ p := l0_le u
    have hmem := Set.mem_iInter₂.mp hG s (Finset.mem_Icc.mpr ⟨hpos, hsp⟩)
    have hb := hmem u le_rfl
    have hs' : (0 : ℝ) < s := by exact_mod_cast hpos
    have hp' : (0 : ℝ) < p := lt_of_lt_of_le hs' (by exact_mod_cast hsp)
    -- the radicand
    have hlogd : Real.log (1 / (((s : ℝ) / (Real.exp 1 * p)) ^ s * ϵ0)) =
        gfun p s + Real.log (1 / ϵ0) := by
      unfold gfun
      rw [one_div, Real.log_inv, Real.log_mul (by positivity) hϵ0.ne', Real.log_pow, one_div,
        Real.log_inv]
      have : Real.exp 1 * p / s = ((s : ℝ) / (Real.exp 1 * p))⁻¹ := by rw [inv_div]
      rw [this, Real.log_inv]
      ring
    rw [hlogd] at hb
    have hsub : gfun p s ≤ gfun p (l0 βh) + gfun p (l0 β) :=
      gfun_subadd (l0_sub_le βh β) hsp (l0_le βh) (l0_le β)
    have hR : 5 * (s : ℝ) * Real.log (Real.exp 1 * p / s) + 3 * (gfun p s + Real.log (1 / ϵ0)) ≤
        8 * (gfun p (l0 βh) + gfun p (l0 β)) + 3 * Real.log (1 / ϵ0) := by
      have : (s : ℝ) * Real.log (Real.exp 1 * p / s) = gfun p s := rfl
      nlinarith
    set R := 8 * (gfun p (l0 βh) + gfun p (l0 β)) + 3 * Real.log (1 / ϵ0) with hRdef
    have hR0 : 0 ≤ R := by rw [hRdef]; linarith
    have hl2 : 0 ≤ l2 (X.mulVec u) := Real.sqrt_nonneg _
    have hAB := l2_X_sub_le X f βh β
    rw [← hu] at hAB
    set A := Real.sqrt (∑ i, (f i - X.mulVec βh i) ^ 2)
    set B := Real.sqrt (∑ i, (f i - X.mulVec β i) ^ 2)
    have hA2 : A ^ 2 = ∑ i, (f i - X.mulVec βh i) ^ 2 := Real.sq_sqrt hSh
    have hB2 : B ^ 2 = ∑ i, (f i - X.mulVec β i) ^ 2 := Real.sq_sqrt hS
    set t := σ * Real.sqrt R
    have ht0 : 0 ≤ t := mul_nonneg hσ.le (Real.sqrt_nonneg _)
    have ht2 : t ^ 2 = σ ^ 2 * R := by
      simp only [t]; rw [mul_pow, Real.sq_sqrt hR0]
    have h1 : dot ε (X.mulVec u) ≤ t * (A + B) := by
      calc dot ε (X.mulVec u) ≤ σ * Real.sqrt (5 * (s : ℝ) * Real.log (Real.exp 1 * p / s) +
            3 * (gfun p s + Real.log (1 / ϵ0))) * l2 (X.mulVec u) := hb
        _ ≤ σ * Real.sqrt R * l2 (X.mulVec u) := by
            apply mul_le_mul_of_nonneg_right _ hl2
            exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hR) hσ.le
        _ ≤ t * (A + B) := mul_le_mul_of_nonneg_left hAB ht0
    have h2 := amgm t A B
    have : σ ^ 2 * R = 8 * (σ ^ 2 * (gfun p (l0 βh) + gfun p (l0 β))) +
        3 * (σ ^ 2 * Real.log (1 / ϵ0)) := by rw [hRdef]; ring
    nlinarith

/-- On the event `F` (at level `δ0`), either the cross term is controlled by sorted sums, or by
`σ² log(1/δ0)` plus halves of the squared errors. -/
lemma onF_bound {n p : ℕ} (X : Matrix (Fin n) (Fin p) ℝ) (σ δ0 : ℝ) (hσ : 0 < σ)
    (hδ0 : 0 < δ0) (hδ1 : δ0 < 1) (f ε : Fin n → ℝ) (βh β : Fin p → ℝ)
    (hF : ε ∈ F X σ δ0) :
    dot ε (X.mulVec (βh - β)) ≤ (4 + Real.sqrt 2) * σ * (sortedSum βh + sortedSum β) ∨
    2 * dot ε (X.mulVec (βh - β)) ≤
      90 * (σ ^ 2 * Real.log (1 / δ0)) +
        (∑ i, (f i - X.mulVec βh i) ^ 2) / 2 + ∑ i, (f i - X.mulVec β i) ^ 2 := by
  have hL := log_one_div_nonneg hδ0 hδ1.le
  have hb := hF (βh - β)
  have hc0 : 0 ≤ (4 + Real.sqrt 2) * σ := mul_nonneg (by positivity) hσ.le
  rcases max_choice (sortedSum (βh - β))
      (Real.sqrt (Real.log (1 / δ0)) * l2 (X.mulVec (βh - β))) with hm | hm
  · left
    rw [hm] at hb
    exact le_trans hb (mul_le_mul_of_nonneg_left (sortedSum_sub_le βh β) hc0)
  · right
    rw [hm] at hb
    have hSh : 0 ≤ ∑ i, (f i - X.mulVec βh i) ^ 2 := Finset.sum_nonneg (fun i _ => sq_nonneg _)
    have hS : 0 ≤ ∑ i, (f i - X.mulVec β i) ^ 2 := Finset.sum_nonneg (fun i _ => sq_nonneg _)
    have hAB := l2_X_sub_le X f βh β
    set A := Real.sqrt (∑ i, (f i - X.mulVec βh i) ^ 2)
    set B := Real.sqrt (∑ i, (f i - X.mulVec β i) ^ 2)
    have hA2 : A ^ 2 = ∑ i, (f i - X.mulVec βh i) ^ 2 := Real.sq_sqrt hSh
    have hB2 : B ^ 2 = ∑ i, (f i - X.mulVec β i) ^ 2 := Real.sq_sqrt hS
    set t := (4 + Real.sqrt 2) * σ * Real.sqrt (Real.log (1 / δ0))
    have ht0 : 0 ≤ t := mul_nonneg hc0 (Real.sqrt_nonneg _)
    have ht2 : t ^ 2 = (4 + Real.sqrt 2) ^ 2 * (σ ^ 2 * Real.log (1 / δ0)) := by
      simp only [t]; rw [mul_pow, mul_pow, Real.sq_sqrt hL]; ring
    have h1 : dot ε (X.mulVec (βh - β)) ≤ t * (A + B) := by
      calc dot ε (X.mulVec (βh - β)) ≤ (4 + Real.sqrt 2) * σ *
            (Real.sqrt (Real.log (1 / δ0)) * l2 (X.mulVec (βh - β))) := hb
        _ = t * l2 (X.mulVec (βh - β)) := by simp only [t]; ring
        _ ≤ t * (A + B) := mul_le_mul_of_nonneg_left hAB ht0
    have h2 := amgm t A B
    have hc := c_sq_le
    have p2 : 0 ≤ σ ^ 2 * Real.log (1 / δ0) := mul_nonneg (sq_nonneg σ) hL
    have : t ^ 2 ≤ 30 * (σ ^ 2 * Real.log (1 / δ0)) := by
      rw [ht2]; exact mul_le_mul_of_nonneg_right hc p2
    nlinarith

lemma two_le_exp_one : (2 : ℝ) ≤ Real.exp 1 := by
  have := Real.add_one_le_exp (1 : ℝ); linarith

lemma sqrt_log_two_p_le {p : ℕ} (hp : 1 ≤ p) :
    Real.sqrt (Real.log (2 * p)) ≤ Real.sqrt (Real.log (Real.exp 1 * p)) := by
  have hp' : (0 : ℝ) < p := by exact_mod_cast hp
  apply Real.sqrt_le_sqrt
  apply Real.log_le_log (by positivity)
  exact mul_le_mul_of_nonneg_right two_le_exp_one hp'.le

lemma lam_term_nonneg {p : ℕ} {a : ℝ} (ha : 0 ≤ a) (β : Fin p → ℝ) : 0 ≤ lamB a β * l2 β := by
  rw [lamB_eq]
  exact mul_nonneg (mul_nonneg ha (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _)

lemma mu_term_nonneg {p : ℕ} {b : ℝ} (hb : 0 ≤ b) (β : Fin p → ℝ) :
    0 ≤ muB b β * (l0 β : ℝ) := by
  rw [muB_mul]; exact mul_nonneg hb (gfun_nonneg (l0_le β))

lemma l1_nonneg {p : ℕ} (β : Fin p → ℝ) : 0 ≤ l1 β :=
  Finset.sum_nonneg (fun i _ => abs_nonneg _)

/-- `β̂^B_2`, case `a ≥ a0 σ`, on the event `F`. -/
lemma bic2_F {n p : ℕ} (X : Matrix (Fin n) (Fin p) ℝ) (hp : 1 ≤ p) (σ a b δ0 : ℝ) (hσ : 0 < σ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hA : 2 * Real.sqrt 2 * (4 + Real.sqrt 2) * σ ≤ a)
    (hδ0 : 0 < δ0) (hδ1 : δ0 < 1) (f ε : Fin n → ℝ) (hF : ε ∈ F X σ δ0)
    (βh : Fin p → ℝ) (hβh : IsBIC2 X (f + ε) a b βh) (β : Fin p → ℝ) :
    ∑ i, (f i - X.mulVec βh i) ^ 2 + muB b βh * (l0 βh : ℝ) ≤
      180 * (∑ i, (f i - X.mulVec β i) ^ 2 + lamB a β * l2 β +
        muB b β * (l0 β : ℝ) + σ ^ 2 * Real.log (1 / δ0)) := by
  have hbasic := basic_ineq X f ε βh β (lamB a βh * l2 βh + muB b βh * (l0 βh : ℝ))
    (lamB a β * l2 β + muB b β * (l0 β : ℝ)) (by have := hβh β; unfold obj2 at this; linarith)
  have l1h := lam_term_nonneg ha βh
  have l1b := lam_term_nonneg ha β
  have m1h := mu_term_nonneg hb βh
  have m1b := mu_term_nonneg hb β
  have hS : 0 ≤ ∑ i, (f i - X.mulVec β i) ^ 2 := Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have hSh : 0 ≤ ∑ i, (f i - X.mulVec βh i) ^ 2 := Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have p2 : 0 ≤ σ ^ 2 * Real.log (1 / δ0) :=
    mul_nonneg (sq_nonneg σ) (log_one_div_nonneg hδ0 hδ1.le)
  rcases onF_bound X σ δ0 hσ hδ0 hδ1 f ε βh β hF with h1 | h2
  · have hc0 : 0 ≤ (4 + Real.sqrt 2) * σ := mul_nonneg (by positivity) hσ.le
    have s1 := sortedSum_le_g hp βh
    have s2 := sortedSum_le_g hp β
    have hQ1 : 0 ≤ Real.sqrt (gfun p (l0 βh)) * l2 βh :=
      mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    have hQ2 : 0 ≤ Real.sqrt (gfun p (l0 β)) * l2 β :=
      mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    have k1 := mul_le_mul_of_nonneg_left (add_le_add s1 s2) hc0
    have k2 : 2 * ((4 + Real.sqrt 2) * σ * (Real.sqrt 2 * Real.sqrt (gfun p (l0 βh)) * l2 βh +
        Real.sqrt 2 * Real.sqrt (gfun p (l0 β)) * l2 β)) =
        (2 * Real.sqrt 2 * (4 + Real.sqrt 2) * σ) *
          (Real.sqrt (gfun p (l0 βh)) * l2 βh + Real.sqrt (gfun p (l0 β)) * l2 β) := by ring
    have k3 := mul_le_mul_of_nonneg_right hA (add_nonneg hQ1 hQ2)
    have k4 : a * (Real.sqrt (gfun p (l0 βh)) * l2 βh + Real.sqrt (gfun p (l0 β)) * l2 β) =
        lamB a βh * l2 βh + lamB a β * l2 β := by rw [lamB_eq, lamB_eq]; ring
    linarith
  · linarith

/-- `β̂^B_2`, case `b ≥ 48 σ²`, on the event `G`. -/
lemma bic2_G {n p : ℕ} (X : Matrix (Fin n) (Fin p) ℝ) (σ a b ϵ0 : ℝ) (hσ : 0 < σ)
    (ha : 0 ≤ a) (hB : 48 * σ ^ 2 ≤ b)
    (hϵ0 : 0 < ϵ0) (hϵ1 : ϵ0 < 1) (f ε : Fin n → ℝ)
    (hG : ε ∈ ⋂ s ∈ Finset.Icc 1 p, Gc X σ (((s : ℝ) / (Real.exp 1 * p)) ^ s * ϵ0) s)
    (βh : Fin p → ℝ) (hβh : IsBIC2 X (f + ε) a b βh) (β : Fin p → ℝ) :
    ∑ i, (f i - X.mulVec βh i) ^ 2 + muB b βh * (l0 βh : ℝ) ≤
      18 * (∑ i, (f i - X.mulVec β i) ^ 2 + lamB a β * l2 β +
        muB b β * (l0 β : ℝ) + σ ^ 2 * Real.log (1 / ϵ0)) := by
  have hb : 0 ≤ b := le_trans (by positivity) hB
  have hbasic := basic_ineq X f ε βh β (lamB a βh * l2 βh + muB b βh * (l0 βh : ℝ))
    (lamB a β * l2 β + muB b β * (l0 β : ℝ)) (by have := hβh β; unfold obj2 at this; linarith)
  have l1h := lam_term_nonneg ha βh
  have l1b := lam_term_nonneg ha β
  have hS : 0 ≤ ∑ i, (f i - X.mulVec β i) ^ 2 := Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have p2 : 0 ≤ σ ^ 2 * Real.log (1 / ϵ0) :=
    mul_nonneg (sq_nonneg σ) (log_one_div_nonneg hϵ0 hϵ1.le)
  have hd := onG_bound X σ ϵ0 hσ hϵ0 hϵ1 f ε βh β hG
  have gh := gfun_nonneg (l0_le βh)
  have g0 := gfun_nonneg (l0_le β)
  have q1 := mul_nonneg (sub_nonneg.mpr hB) gh
  have q2 := mul_nonneg (sub_nonneg.mpr hB) g0
  rw [muB_mul, muB_mul] at hbasic ⊢
  nlinarith

/-- `β̂^B_1`, case `λ ≥ 2(4+√2) σ √log(ep)`, on the event `F`. -/
lemma bic1_F {n p : ℕ} (X : Matrix (Fin n) (Fin p) ℝ) (hp : 1 ≤ p) (σ lam b δ0 : ℝ) (hσ : 0 < σ)
    (hlam : 0 ≤ lam) (hb : 0 ≤ b)
    (hA : 2 * (4 + Real.sqrt 2) * σ * Real.sqrt (Real.log (Real.exp 1 * p)) ≤ lam)
    (hδ0 : 0 < δ0) (hδ1 : δ0 < 1) (f ε : Fin n → ℝ) (hF : ε ∈ F X σ δ0)
    (βh : Fin p → ℝ) (hβh : IsBIC1 X (f + ε) lam b βh) (β : Fin p → ℝ) :
    ∑ i, (f i - X.mulVec βh i) ^ 2 + muB b βh * (l0 βh : ℝ) ≤
      180 * (∑ i, (f i - X.mulVec β i) ^ 2 + lam * l1 β +
        muB b β * (l0 β : ℝ) + σ ^ 2 * Real.log (1 / δ0)) := by
  have hbasic := basic_ineq X f ε βh β (lam * l1 βh + muB b βh * (l0 βh : ℝ))
    (lam * l1 β + muB b β * (l0 β : ℝ)) (by have := hβh β; unfold obj1 at this; linarith)
  have l1h := mul_nonneg hlam (l1_nonneg βh)
  have l1b := mul_nonneg hlam (l1_nonneg β)
  have m1h := mu_term_nonneg hb βh
  have m1b := mu_term_nonneg hb β
  have hS : 0 ≤ ∑ i, (f i - X.mulVec β i) ^ 2 := Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have hSh : 0 ≤ ∑ i, (f i - X.mulVec βh i) ^ 2 := Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have p2 : 0 ≤ σ ^ 2 * Real.log (1 / δ0) :=
    mul_nonneg (sq_nonneg σ) (log_one_div_nonneg hδ0 hδ1.le)
  rcases onF_bound X σ δ0 hσ hδ0 hδ1 f ε βh β hF with h1 | h2
  · have hc0 : 0 ≤ (4 + Real.sqrt 2) * σ := mul_nonneg (by positivity) hσ.le
    have s1 := sortedSum_le_l1 hp βh
    have s2 := sortedSum_le_l1 hp β
    have hl := sqrt_log_two_p_le hp
    have hsum : 0 ≤ l1 βh + l1 β := add_nonneg (l1_nonneg βh) (l1_nonneg β)
    have k1 := mul_le_mul_of_nonneg_left (add_le_add s1 s2) hc0
    have k2 : (4 + Real.sqrt 2) * σ * (Real.sqrt (Real.log (2 * p)) * l1 βh +
        Real.sqrt (Real.log (2 * p)) * l1 β) =
        ((4 + Real.sqrt 2) * σ) * Real.sqrt (Real.log (2 * p)) * (l1 βh + l1 β) := by ring
    have k3 : ((4 + Real.sqrt 2) * σ) * Real.sqrt (Real.log (2 * p)) * (l1 βh + l1 β) ≤
        ((4 + Real.sqrt 2) * σ) * Real.sqrt (Real.log (Real.exp 1 * p)) * (l1 βh + l1 β) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hl hc0) hsum
    have k4 := mul_le_mul_of_nonneg_right hA hsum
    linarith
  · linarith

/-- `β̂^B_1`, case `b ≥ 48 σ²`, on the event `G`. -/
lemma bic1_G {n p : ℕ} (X : Matrix (Fin n) (Fin p) ℝ) (σ lam b ϵ0 : ℝ) (hσ : 0 < σ)
    (hlam : 0 ≤ lam) (hB : 48 * σ ^ 2 ≤ b)
    (hϵ0 : 0 < ϵ0) (hϵ1 : ϵ0 < 1) (f ε : Fin n → ℝ)
    (hG : ε ∈ ⋂ s ∈ Finset.Icc 1 p, Gc X σ (((s : ℝ) / (Real.exp 1 * p)) ^ s * ϵ0) s)
    (βh : Fin p → ℝ) (hβh : IsBIC1 X (f + ε) lam b βh) (β : Fin p → ℝ) :
    ∑ i, (f i - X.mulVec βh i) ^ 2 + muB b βh * (l0 βh : ℝ) ≤
      18 * (∑ i, (f i - X.mulVec β i) ^ 2 + lam * l1 β +
        muB b β * (l0 β : ℝ) + σ ^ 2 * Real.log (1 / ϵ0)) := by
  have hbasic := basic_ineq X f ε βh β (lam * l1 βh + muB b βh * (l0 βh : ℝ))
    (lam * l1 β + muB b β * (l0 β : ℝ)) (by have := hβh β; unfold obj1 at this; linarith)
  have l1h := mul_nonneg hlam (l1_nonneg βh)
  have l1b := mul_nonneg hlam (l1_nonneg β)
  have hS : 0 ≤ ∑ i, (f i - X.mulVec β i) ^ 2 := Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have p2 : 0 ≤ σ ^ 2 * Real.log (1 / ϵ0) :=
    mul_nonneg (sq_nonneg σ) (log_one_div_nonneg hϵ0 hϵ1.le)
  have hd := onG_bound X σ ϵ0 hσ hϵ0 hϵ1 f ε βh β hG
  have gh := gfun_nonneg (l0_le βh)
  have g0 := gfun_nonneg (l0_le β)
  have q1 := mul_nonneg (sub_nonneg.mpr hB) gh
  have q2 := mul_nonneg (sub_nonneg.mpr hB) g0
  rw [muB_mul, muB_mul] at hbasic ⊢
  nlinarith

end BICCore

open BICCore SubsetShrink.BIC SubsetShrink.Events in
theorem solution :
    ∃ b0 C : ℝ, 0 < C ∧
      ∀ {n p : ℕ} (X : Matrix (Fin n) (Fin p) ℝ) (fstar : Fin n → ℝ) (σ a b ϵ0 : ℝ)
        (β : Fin p → ℝ),
        SubsetShrink.Events.UnitCols X → 1 ≤ p → 0 < σ → 0 ≤ a → 0 ≤ b → b0 * σ ^ 2 ≤ b → 0 < ϵ0 → ϵ0 < 1 →
        ∃ A : Set (Fin n → ℝ), MeasurableSet A ∧ 1 - ϵ0 ≤ (SubsetShrink.Events.noiseLaw n σ A).toReal ∧
          ∀ ε ∈ A, ∀ βhat : Fin p → ℝ, IsBIC2 X (fstar + ε) a b βhat →
            ∑ i, (fstar i - X.mulVec βhat i) ^ 2 + muB b βhat * (SubsetShrink.Events.l0 βhat : ℝ) ≤
              C * (∑ i, (fstar i - X.mulVec β i) ^ 2 + σ ^ 2 * Real.log (1 / ϵ0) +
                lamB a β * SubsetShrink.Events.l2 β + muB b β * (SubsetShrink.Events.l0 β : ℝ)) := by
  refine ⟨48, 18, by norm_num, ?_⟩
  intro n p X fstar σ a b ϵ0 β hX hp hσ ha hb hB hϵ0 hϵ1
  obtain ⟨hm, -, -, -, -, hP⟩ := SubsetShrink.BIC.union_bound X σ ϵ0 hX hp hσ hϵ0 hϵ1
  refine ⟨_, hm, hP, ?_⟩
  intro ε hε βh hβh
  have := bic2_G X σ a b ϵ0 hσ ha hB hϵ0 hϵ1 fstar ε hε βh hβh β
  linarith
