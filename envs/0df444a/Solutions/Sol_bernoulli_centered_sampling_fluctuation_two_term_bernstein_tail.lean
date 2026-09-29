-- Prove2me | solution 1 for bernoulli_centered_sampling_fluctuation_two_term_bernstein_tail
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-06-30T00:21:10.317164+00:00
-- url     : https://prove2.me/submissions/bd7ebbaf-eaca-40a6-9430-119a374d25e6

import Mathlib
import Definitions.Def_matrix_completion_neumann
import Theorems.Thm_bernstein_exp_le
open MatrixCompletion
open scoped Classical BigOperators
open Finset

-- prod_add core: sum over all subsets of a product-of-ite equals product of sums
lemma sum_prod_ite {σ : Type*} [Fintype σ] [DecidableEq σ] (a b : σ → ℝ) :
    (∑ Ω : Finset σ, ∏ w, (if w ∈ Ω then a w else b w)) = ∏ w, (a w + b w) := by
  rw [Finset.prod_add]
  rw [Finset.powerset_univ]
  apply Finset.sum_congr rfl
  intro Ω _
  rw [Finset.prod_ite]
  congr 1
  · -- ∏ over univ.filter (·∈Ω) of a = ∏ over Ω of a
    apply Finset.prod_congr ?_ (fun _ _ => rfl)
    ext w; simp [Finset.mem_filter]
  · -- ∏ over univ.filter (·∉Ω) of b = ∏ over univ\Ω of b
    apply Finset.prod_congr ?_ (fun _ _ => rfl)
    ext w; simp [Finset.mem_filter, Finset.mem_sdiff]

-- MGF factorization for the centered statistic Z(Ω) = ∑_w X_w (1[w∈Ω] - p)
lemma mgf_fluct {n₁ n₂ : ℕ} (p s : ℝ) (X : Fin n₁ × Fin n₂ → ℝ) :
    (∑ Ω : Finset (Fin n₁ × Fin n₂),
        (p ^ Ω.card * (1 - p) ^ (Fintype.card (Fin n₁ × Fin n₂) - Ω.card))
          * Real.exp (s * ∑ w : Fin n₁ × Fin n₂, X w * ((if w ∈ Ω then (1 : ℝ) else 0) - p)))
      = ∏ w : Fin n₁ × Fin n₂,
          Real.exp (-(s * p * X w)) * (1 - p + p * Real.exp (s * X w)) := by
  -- rewrite each summand as ∏_w (if w∈Ω then p e^{sX} else 1-p) times the constant ∏ e^{-spX}
  have hconst : ∀ Ω : Finset (Fin n₁ × Fin n₂),
      (p ^ Ω.card * (1 - p) ^ (Fintype.card (Fin n₁ × Fin n₂) - Ω.card))
          * Real.exp (s * ∑ w, X w * ((if w ∈ Ω then (1 : ℝ) else 0) - p))
        = (∏ w : Fin n₁ × Fin n₂, Real.exp (-(s * p * X w)))
            * ∏ w : Fin n₁ × Fin n₂,
                (if w ∈ Ω then p * Real.exp (s * X w) else (1 - p)) := by
    intro Ω
    -- weight as product of ite
    have hc1 : (univ.filter (fun w : Fin n₁ × Fin n₂ => w ∈ Ω)).card = Ω.card := by
      rw [show univ.filter (fun w : Fin n₁ × Fin n₂ => w ∈ Ω) = Ω from by ext w; simp]
    have hc2 : (univ.filter (fun w : Fin n₁ × Fin n₂ => w ∉ Ω)).card
        = Fintype.card (Fin n₁ × Fin n₂) - Ω.card := by
      rw [show univ.filter (fun w : Fin n₁ × Fin n₂ => w ∉ Ω) = Ωᶜ from by ext w; simp,
        Finset.card_compl]
    have hweight : p ^ Ω.card * (1 - p) ^ (Fintype.card (Fin n₁ × Fin n₂) - Ω.card)
        = ∏ w : Fin n₁ × Fin n₂, (if w ∈ Ω then p else (1 - p)) := by
      rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const, hc1, hc2]
    -- exp of sum = product
    have hexp : Real.exp (s * ∑ w, X w * ((if w ∈ Ω then (1 : ℝ) else 0) - p))
        = ∏ w : Fin n₁ × Fin n₂,
            (Real.exp (-(s * p * X w)) * (if w ∈ Ω then Real.exp (s * X w) else 1)) := by
      rw [Finset.mul_sum, Real.exp_sum]
      apply Finset.prod_congr rfl
      intro w _
      by_cases h : w ∈ Ω
      · simp only [if_pos h]
        rw [show s * (X w * ((1:ℝ) - p)) = -(s * p * X w) + s * X w from by ring, Real.exp_add]
      · simp only [if_neg h]
        rw [show s * (X w * ((0:ℝ) - p)) = -(s * p * X w) from by ring, mul_one]
    rw [hweight, hexp, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro w _
    by_cases h : w ∈ Ω <;> simp [h] <;> ring
  rw [Finset.sum_congr rfl (fun Ω _ => hconst Ω), ← Finset.mul_sum, sum_prod_ite]
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro w _
  ring

-- Bennett MGF bound: MGF ≤ exp(∑ p (e^{sX}-1-sX))
lemma mgf_fluct_le {n₁ n₂ : ℕ} (p s : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (X : Fin n₁ × Fin n₂ → ℝ) :
    (∑ Ω : Finset (Fin n₁ × Fin n₂),
        (p ^ Ω.card * (1 - p) ^ (Fintype.card (Fin n₁ × Fin n₂) - Ω.card))
          * Real.exp (s * ∑ w : Fin n₁ × Fin n₂, X w * ((if w ∈ Ω then (1 : ℝ) else 0) - p)))
      ≤ Real.exp (∑ w : Fin n₁ × Fin n₂, p * (Real.exp (s * X w) - 1 - s * X w)) := by
  rw [mgf_fluct, Real.exp_sum]
  apply Finset.prod_le_prod
  · intro w _
    have h := Real.exp_pos (s * X w)
    apply mul_nonneg (Real.exp_pos _).le
    nlinarith [h, hp0, hp1]
  · intro w _
    have hE := Real.exp_pos (s * X w)
    have h1 : (1 - p + p * Real.exp (s * X w)) ≤ Real.exp (p * (Real.exp (s * X w) - 1)) := by
      have := Real.add_one_le_exp (p * (Real.exp (s * X w) - 1))
      nlinarith [this]
    calc Real.exp (-(s * p * X w)) * (1 - p + p * Real.exp (s * X w))
        ≤ Real.exp (-(s * p * X w)) * Real.exp (p * (Real.exp (s * X w) - 1)) :=
          mul_le_mul_of_nonneg_left h1 (Real.exp_pos _).le
      _ = Real.exp (p * (Real.exp (s * X w) - 1 - s * X w)) := by
          rw [← Real.exp_add]; congr 1; ring

-- One-sided Chernoff tail for Z(Ω) = ∑_w X_w (1[w∈Ω] - p)
lemma fluct_chernoff {n₁ n₂ : ℕ} (p s t : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hs : 0 ≤ s)
    (X : Fin n₁ × Fin n₂ → ℝ) :
    (∑ Ω : Finset (Fin n₁ × Fin n₂),
        if t < (∑ w : Fin n₁ × Fin n₂, X w * ((if w ∈ Ω then (1 : ℝ) else 0) - p))
        then p ^ Ω.card * (1 - p) ^ (Fintype.card (Fin n₁ × Fin n₂) - Ω.card) else 0)
      ≤ Real.exp (-(s * t) + ∑ w : Fin n₁ × Fin n₂, p * (Real.exp (s * X w) - 1 - s * X w)) := by
  have hmarkov : (∑ Ω : Finset (Fin n₁ × Fin n₂),
        if t < (∑ w, X w * ((if w ∈ Ω then (1 : ℝ) else 0) - p))
        then p ^ Ω.card * (1 - p) ^ (Fintype.card (Fin n₁ × Fin n₂) - Ω.card) else 0)
      ≤ ∑ Ω : Finset (Fin n₁ × Fin n₂),
          Real.exp (-(s * t)) *
            ((p ^ Ω.card * (1 - p) ^ (Fintype.card (Fin n₁ × Fin n₂) - Ω.card))
              * Real.exp (s * ∑ w, X w * ((if w ∈ Ω then (1 : ℝ) else 0) - p))) := by
    apply Finset.sum_le_sum
    intro Ω _
    set Z := (∑ w, X w * ((if w ∈ Ω then (1 : ℝ) else 0) - p)) with hZ
    set W := p ^ Ω.card * (1 - p) ^ (Fintype.card (Fin n₁ × Fin n₂) - Ω.card) with hW
    have hWnn : 0 ≤ W := mul_nonneg (pow_nonneg hp0 _) (pow_nonneg (by linarith) _)
    by_cases h : t < Z
    · rw [if_pos h]
      have h1 : (1 : ℝ) ≤ Real.exp (-(s * t)) * Real.exp (s * Z) := by
        rw [← Real.exp_add, Real.one_le_exp_iff]; nlinarith [hs, h]
      calc W = 1 * W := (one_mul _).symm
        _ ≤ (Real.exp (-(s * t)) * Real.exp (s * Z)) * W := mul_le_mul_of_nonneg_right h1 hWnn
        _ = Real.exp (-(s * t)) * (W * Real.exp (s * Z)) := by ring
    · rw [if_neg h]
      exact mul_nonneg (Real.exp_pos _).le (mul_nonneg hWnn (Real.exp_pos _).le)
  refine le_trans hmarkov ?_
  rw [← Finset.mul_sum, Real.exp_add]
  exact mul_le_mul_of_nonneg_left (mgf_fluct_le p s hp0 hp1 X) (Real.exp_pos _).le

lemma exp_sub_one_sub_le_half_sq_of_nonpos (y : ℝ) (hy : y ≤ 0) :
    Real.exp y - 1 - y ≤ y ^ 2 / 2 := by
  set f : ℝ → ℝ := fun t => t ^ 2 / 2 - Real.exp t + 1 + t with hf
  have hderiv : ∀ x : ℝ, HasDerivAt f (x - Real.exp x + 1) x := by
    intro x
    have h1 : HasDerivAt (fun t : ℝ => t ^ 2 / 2) x x := by
      simpa using (hasDerivAt_pow 2 x).div_const 2
    have h := ((h1.fun_sub (Real.hasDerivAt_exp x)).fun_add (hasDerivAt_const x (1:ℝ))).fun_add
      (hasDerivAt_id x)
    exact h.congr_deriv (by ring)
  have hcont : Continuous f := by rw [hf]; fun_prop
  have hanti : AntitoneOn f (Set.Iic 0) := by
    apply antitoneOn_of_deriv_nonpos (convex_Iic 0) hcont.continuousOn
      (fun x _ => ((hderiv x).differentiableAt).differentiableWithinAt)
    intro x _; rw [(hderiv x).deriv]; have hx := Real.add_one_le_exp x; linarith
  have h0 : f 0 = 0 := by rw [hf]; simp
  have hmono := hanti (Set.mem_Iic.mpr hy) (Set.mem_Iic.mpr le_rfl) hy
  rw [h0] at hmono; rw [hf] at hmono; simp only at hmono; linarith

lemma subgamma_per_term
    (hbern : ∀ y : ℝ, 0 ≤ y → y < 3 → Real.exp y - 1 - y ≤ y ^ 2 / (2 * (1 - y / 3)))
    (R y : ℝ) (hR0 : 0 ≤ R) (hR3 : R < 3) (hy : |y| ≤ R) :
    Real.exp y - 1 - y ≤ y ^ 2 / (2 * (1 - R / 3)) := by
  have hD : 0 < 2 * (1 - R / 3) := by linarith
  by_cases hy0 : 0 ≤ y
  · have hyR : y ≤ R := le_trans (le_abs_self y) hy
    have hy3 : y < 3 := lt_of_le_of_lt hyR hR3
    have h1 := hbern y hy0 hy3
    have hmono : y ^ 2 / (2 * (1 - y / 3)) ≤ y ^ 2 / (2 * (1 - R / 3)) := by
      rw [div_le_div_iff₀ (by linarith) hD]
      nlinarith [mul_nonneg (sq_nonneg y) (show (0:ℝ) ≤ R - y by linarith)]
    linarith
  · push_neg at hy0
    have h1 := exp_sub_one_sub_le_half_sq_of_nonpos y (le_of_lt hy0)
    have hmono : y ^ 2 / 2 ≤ y ^ 2 / (2 * (1 - R / 3)) := by
      rw [div_le_div_iff₀ (by norm_num) hD]
      nlinarith [mul_nonneg (sq_nonneg y) hR0]
    linarith

lemma subgamma_sum {ι : Type*} [Fintype ι]
    (hbern : ∀ y : ℝ, 0 ≤ y → y < 3 → Real.exp y - 1 - y ≤ y ^ 2 / (2 * (1 - y / 3)))
    (p s R : ℝ) (c : ι → ℝ) (hp0 : 0 ≤ p) (hs0 : 0 ≤ s) (hR0 : 0 ≤ R) (hsR3 : s * R < 3)
    (hc : ∀ i, |c i| ≤ R) :
    (∑ i, p * (Real.exp (s * c i) - 1 - s * c i))
      ≤ s ^ 2 * p * (∑ i, (c i) ^ 2) / (2 * (1 - s * R / 3)) := by
  have hbound : ∀ i, p * (Real.exp (s * c i) - 1 - s * c i)
      ≤ p * ((s * c i) ^ 2 / (2 * (1 - s * R / 3))) := by
    intro i
    apply mul_le_mul_of_nonneg_left _ hp0
    have hyabs : |s * c i| ≤ s * R := by
      rw [abs_mul, abs_of_nonneg hs0]; exact mul_le_mul_of_nonneg_left (hc i) hs0
    exact subgamma_per_term hbern (s * R) (s * c i) (mul_nonneg hs0 hR0) hsR3 hyabs
  calc (∑ i, p * (Real.exp (s * c i) - 1 - s * c i))
      ≤ ∑ i, p * ((s * c i) ^ 2 / (2 * (1 - s * R / 3))) := Finset.sum_le_sum (fun i _ => hbound i)
    _ = (∑ i, p * (s * c i) ^ 2) / (2 * (1 - s * R / 3)) := by
        rw [Finset.sum_div]; exact Finset.sum_congr rfl (fun i _ => by ring)
    _ = s ^ 2 * p * (∑ i, (c i) ^ 2) / (2 * (1 - s * R / 3)) := by
        congr 1; rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun i _ => by ring)

-- sub-gamma (Bernstein) one-sided tail, optimizing s = t/(v + R t/3)
lemma fluct_subgamma_tail {n₁ n₂ : ℕ}
    (hbern : ∀ y : ℝ, 0 ≤ y → y < 3 → Real.exp y - 1 - y ≤ y ^ 2 / (2 * (1 - y / 3)))
    (p t R : ℝ) (X : Fin n₁ × Fin n₂ → ℝ)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (ht0 : 0 ≤ t) (hR0 : 0 ≤ R)
    (hc : ∀ w, |X w| ≤ R) (v : ℝ) (hv : v = p * ∑ w, (X w) ^ 2) (hvpos : 0 < v) :
    (∑ Ω : Finset (Fin n₁ × Fin n₂),
        if t < (∑ w : Fin n₁ × Fin n₂, X w * ((if w ∈ Ω then (1 : ℝ) else 0) - p))
        then p ^ Ω.card * (1 - p) ^ (Fintype.card (Fin n₁ × Fin n₂) - Ω.card) else 0)
      ≤ Real.exp (-(t ^ 2 / (2 * (v + R * t / 3)))) := by
  have hD : 0 < v + R * t / 3 := by positivity
  set s := t / (v + R * t / 3) with hs
  have hs0 : 0 ≤ s := by rw [hs]; positivity
  have hsR3 : s * R < 3 := by
    rw [hs, div_mul_eq_mul_div, div_lt_iff₀ hD]; nlinarith [hvpos, mul_nonneg hR0 ht0]
  have h1mR : 1 - s * R / 3 = v / (v + R * t / 3) := by
    rw [hs]; field_simp; ring
  have hexp_eq : -(s * t) + s ^ 2 * v / (2 * (1 - s * R / 3))
      = -(t ^ 2 / (2 * (v + R * t / 3))) := by
    rw [h1mR, hs]; field_simp; ring
  refine le_trans (fluct_chernoff p s t hp0 hp1 hs0 X) ?_
  apply Real.exp_le_exp.mpr
  have hsg := subgamma_sum hbern p s R X hp0 hs0 hR0 hsR3 hc
  have hv2 : s ^ 2 * p * (∑ w, (X w) ^ 2) = s ^ 2 * v := by rw [hv]; ring
  rw [hv2] at hsg
  linarith [hsg, hexp_eq.le, hexp_eq.ge]

-- two-sided Bernstein tail
lemma fluct_subgamma_two_sided {n₁ n₂ : ℕ}
    (hbern : ∀ y : ℝ, 0 ≤ y → y < 3 → Real.exp y - 1 - y ≤ y ^ 2 / (2 * (1 - y / 3)))
    (p τ R : ℝ) (X : Fin n₁ × Fin n₂ → ℝ)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hτ0 : 0 ≤ τ) (hR0 : 0 ≤ R)
    (hc : ∀ w, |X w| ≤ R) (v : ℝ) (hv : v = p * ∑ w, (X w) ^ 2) (hvpos : 0 < v) :
    (∑ Ω : Finset (Fin n₁ × Fin n₂),
        if τ < |(∑ w : Fin n₁ × Fin n₂, X w * ((if w ∈ Ω then (1 : ℝ) else 0) - p))|
        then p ^ Ω.card * (1 - p) ^ (Fintype.card (Fin n₁ × Fin n₂) - Ω.card) else 0)
      ≤ 2 * Real.exp (-(τ ^ 2 / (2 * (v + R * τ / 3)))) := by
  have h1 := fluct_subgamma_tail hbern p τ R X hp0 hp1 hτ0 hR0 hc v hv hvpos
  have h2 := fluct_subgamma_tail hbern p τ R (fun w => -X w) hp0 hp1 hτ0 hR0
      (fun w => by rw [abs_neg]; exact hc w) v (by rw [hv]; apply congrArg; apply Finset.sum_congr rfl; intro w _; ring) hvpos
  have hterm : (∑ Ω : Finset (Fin n₁ × Fin n₂),
        if τ < |(∑ w, X w * ((if w ∈ Ω then (1:ℝ) else 0) - p))|
        then p ^ Ω.card * (1 - p) ^ (Fintype.card (Fin n₁ × Fin n₂) - Ω.card) else 0)
      ≤ (∑ Ω : Finset (Fin n₁ × Fin n₂),
          if τ < (∑ w, X w * ((if w ∈ Ω then (1:ℝ) else 0) - p))
          then p ^ Ω.card * (1 - p) ^ (Fintype.card (Fin n₁ × Fin n₂) - Ω.card) else 0)
        + (∑ Ω : Finset (Fin n₁ × Fin n₂),
          if τ < (∑ w, (-X w) * ((if w ∈ Ω then (1:ℝ) else 0) - p))
          then p ^ Ω.card * (1 - p) ^ (Fintype.card (Fin n₁ × Fin n₂) - Ω.card) else 0) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro Ω _
    have hWnn : 0 ≤ p ^ Ω.card * (1 - p) ^ (Fintype.card (Fin n₁ × Fin n₂) - Ω.card) :=
      mul_nonneg (pow_nonneg hp0 _) (pow_nonneg (by linarith) _)
    have hneg : (∑ w, (-X w) * ((if w ∈ Ω then (1:ℝ) else 0) - p))
        = -(∑ w, X w * ((if w ∈ Ω then (1:ℝ) else 0) - p)) := by
      rw [eq_neg_iff_add_eq_zero, ← Finset.sum_add_distrib]
      exact Finset.sum_eq_zero (fun w _ => by ring)
    rw [hneg]
    by_cases h : τ < |(∑ w, X w * ((if w ∈ Ω then (1:ℝ) else 0) - p))|
    · rw [if_pos h]
      rcases lt_abs.mp h with hpos | hneg2
      · have : τ < (∑ w, X w * ((if w ∈ Ω then (1:ℝ) else 0) - p)) := hpos
        rw [if_pos this]
        have : 0 ≤ (if τ < -(∑ w, X w * ((if w ∈ Ω then (1:ℝ) else 0) - p))
            then p ^ Ω.card * (1 - p) ^ (Fintype.card (Fin n₁ × Fin n₂) - Ω.card) else 0) := by
          split_ifs <;> [exact hWnn; exact le_rfl]
        linarith
      · have : τ < -(∑ w, X w * ((if w ∈ Ω then (1:ℝ) else 0) - p)) := hneg2
        rw [if_pos this]
        have : 0 ≤ (if τ < (∑ w, X w * ((if w ∈ Ω then (1:ℝ) else 0) - p))
            then p ^ Ω.card * (1 - p) ^ (Fintype.card (Fin n₁ × Fin n₂) - Ω.card) else 0) := by
          split_ifs <;> [exact hWnn; exact le_rfl]
        linarith
    · rw [if_neg h]
      have ha : 0 ≤ (if τ < (∑ w, X w * ((if w ∈ Ω then (1:ℝ) else 0) - p))
          then p ^ Ω.card * (1 - p) ^ (Fintype.card (Fin n₁ × Fin n₂) - Ω.card) else 0) := by
        split_ifs <;> [exact hWnn; exact le_rfl]
      have hb : 0 ≤ (if τ < -(∑ w, X w * ((if w ∈ Ω then (1:ℝ) else 0) - p))
          then p ^ Ω.card * (1 - p) ^ (Fintype.card (Fin n₁ × Fin n₂) - Ω.card) else 0) := by
        split_ifs <;> [exact hWnn; exact le_rfl]
      linarith
  have := add_le_add h1 h2
  linarith [hterm, this]

-- Bernstein two-term: the threshold √(2vu)+(2/3)Ru achieves tail ≤ exp(-u)
lemma bernstein_two_term (v R u : ℝ) (hv : 0 < v) (hR : 0 ≤ R) (hu : 0 ≤ u) :
    u ≤ (Real.sqrt (2 * v * u) + (2 / 3) * R * u) ^ 2
        / (2 * (v + R * (Real.sqrt (2 * v * u) + (2 / 3) * R * u) / 3)) := by
  set a := Real.sqrt (2 * v * u) with ha
  have ha2 : a ^ 2 = 2 * v * u := Real.sq_sqrt (by positivity)
  have ha0 : 0 ≤ a := Real.sqrt_nonneg _
  set τ := a + (2 / 3) * R * u with hτ
  have hden : 0 < 2 * (v + R * τ / 3) := by rw [hτ]; positivity
  rw [le_div_iff₀ hden]
  rw [hτ]
  nlinarith [ha2, mul_nonneg (mul_nonneg hR ha0) hu, sq_nonneg a, mul_nonneg hR hu, ha0, hv, hu, hR]

-- combined two-term tail: P(|Z| > √(2vu)+(2/3)Ru) ≤ 2 exp(-u)
lemma fluct_two_term_tail {n₁ n₂ : ℕ}
    (hbern : ∀ y : ℝ, 0 ≤ y → y < 3 → Real.exp y - 1 - y ≤ y ^ 2 / (2 * (1 - y / 3)))
    (p R u : ℝ) (X : Fin n₁ × Fin n₂ → ℝ)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hR0 : 0 ≤ R)
    (hc : ∀ w, |X w| ≤ R) (v : ℝ) (hv : v = p * ∑ w, (X w) ^ 2) (hvpos : 0 < v) (hu : 0 ≤ u) :
    (∑ Ω : Finset (Fin n₁ × Fin n₂),
        if (Real.sqrt (2 * v * u) + (2 / 3) * R * u)
            < |(∑ w : Fin n₁ × Fin n₂, X w * ((if w ∈ Ω then (1 : ℝ) else 0) - p))|
        then p ^ Ω.card * (1 - p) ^ (Fintype.card (Fin n₁ × Fin n₂) - Ω.card) else 0)
      ≤ 2 * Real.exp (-u) := by
  have hτ0 : 0 ≤ Real.sqrt (2 * v * u) + (2 / 3) * R * u := by positivity
  have h2s := fluct_subgamma_two_sided hbern p (Real.sqrt (2 * v * u) + (2 / 3) * R * u) R X
      hp0 hp1 hτ0 hR0 hc v hv hvpos
  have hbtt := bernstein_two_term v R u hvpos hR0 hu
  have hmono : Real.exp (-((Real.sqrt (2 * v * u) + (2 / 3) * R * u) ^ 2
        / (2 * (v + R * (Real.sqrt (2 * v * u) + (2 / 3) * R * u) / 3))))
      ≤ Real.exp (-u) := Real.exp_le_exp.mpr (by linarith)
  linarith [h2s, hmono]

-- ecosystem-native two-term Bernstein tail for the centered sampling fluctuation
private theorem two_term_native {n₁ n₂ : ℕ}
    (hbern : ∀ y : ℝ, 0 ≤ y → y < 3 → Real.exp y - 1 - y ≤ y ^ 2 / (2 * (1 - y / 3)))
    (p u : ℝ) (X : Matrix (Fin n₁) (Fin n₂) ℝ)
    (hp0 : 0 < p) (hp1 : p ≤ 1) (hu : 0 ≤ u) (hfro : 0 < frobeniusNormSq X) :
    bernoulliEventProb p (fun Ω =>
        Real.sqrt (2 * (frobeniusNormSq X / p) * u) + (2 / 3) * (entrySupNorm X / p) * u
          < |matrixEntrySum (centeredSamplingFluctuation Ω p X)|)
      ≤ 2 * Real.exp (-u) := by
  have hp0' : 0 ≤ p := le_of_lt hp0
  have hentry : ∀ w : Fin n₁ × Fin n₂, |X w.1 w.2| ≤ entrySupNorm X := by
    intro w
    have hbdd : BddAbove (Set.range (fun j => |X w.1 j|)) := Set.Finite.bddAbove (Set.finite_range _)
    have hbdd2 : BddAbove (Set.range (fun i => ⨆ j, |X i j|)) := Set.Finite.bddAbove (Set.finite_range _)
    calc |X w.1 w.2| ≤ ⨆ j, |X w.1 j| := le_ciSup hbdd w.2
      _ ≤ ⨆ i, ⨆ j, |X i j| := le_ciSup hbdd2 w.1
  have hRbound : ∀ w : Fin n₁ × Fin n₂, |p⁻¹ * X w.1 w.2| ≤ entrySupNorm X / p := by
    intro w
    rw [abs_mul, abs_of_pos (inv_pos.mpr hp0), div_eq_inv_mul]
    exact mul_le_mul_of_nonneg_left (hentry w) (le_of_lt (inv_pos.mpr hp0))
  have h1 : (∑ w : Fin n₁ × Fin n₂, (X w.1 w.2) ^ 2) = frobeniusNormSq X := by
    unfold frobeniusNormSq; rw [Fintype.sum_prod_type]
  have hentrynn : 0 ≤ entrySupNorm X :=
    Real.iSup_nonneg (fun i => Real.iSup_nonneg (fun j => abs_nonneg _))
  have hveq : frobeniusNormSq X / p = p * ∑ w : Fin n₁ × Fin n₂, (p⁻¹ * X w.1 w.2) ^ 2 := by
    rw [← h1, Finset.mul_sum, Finset.sum_div]
    apply Finset.sum_congr rfl; intro w _; field_simp
  have hvpos : 0 < frobeniusNormSq X / p := by positivity
  have hcoef : ∀ Ω : Finset (Fin n₁ × Fin n₂),
      matrixEntrySum (centeredSamplingFluctuation Ω p X)
        = ∑ w : Fin n₁ × Fin n₂, (p⁻¹ * X w.1 w.2) * ((if w ∈ Ω then (1 : ℝ) else 0) - p) := by
    intro Ω
    unfold matrixEntrySum centeredSamplingFluctuation
    apply Finset.sum_congr rfl; intro w _
    rw [Matrix.smul_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, smul_eq_mul]
    unfold samplingProjection
    by_cases h : w ∈ Ω <;> simp [h] <;> ring
  unfold bernoulliEventProb bernoulliObservationWeight
  rw [show (fun Ω => Real.sqrt (2 * (frobeniusNormSq X / p) * u) + (2 / 3) * (entrySupNorm X / p) * u
            < |matrixEntrySum (centeredSamplingFluctuation Ω p X)|)
        = (fun Ω => Real.sqrt (2 * (frobeniusNormSq X / p) * u) + (2 / 3) * (entrySupNorm X / p) * u
            < |∑ w : Fin n₁ × Fin n₂, (p⁻¹ * X w.1 w.2) * ((if w ∈ Ω then (1 : ℝ) else 0) - p)|)
      from by funext Ω; rw [hcoef]]
  exact fluct_two_term_tail hbern p (entrySupNorm X / p) u (fun w => p⁻¹ * X w.1 w.2)
    hp0' hp1 (div_nonneg hentrynn hp0') hRbound (frobeniusNormSq X / p) hveq hvpos hu

theorem solution {n₁ n₂ : ℕ}
    (p u : ℝ) (X : Matrix (Fin n₁) (Fin n₂) ℝ)
    (hp0 : 0 < p) (hp1 : p ≤ 1) (hu : 0 ≤ u) (hfro : 0 < frobeniusNormSq X) :
    bernoulliEventProb p (fun Ω =>
        Real.sqrt (2 * (frobeniusNormSq X / p) * u) + (2 / 3) * (entrySupNorm X / p) * u
          < |matrixEntrySum (centeredSamplingFluctuation Ω p X)|)
      ≤ 2 * Real.exp (-u) :=
  two_term_native (fun y h0 h3 => bernstein_exp_le y h0 h3) p u X hp0 hp1 hu hfro
