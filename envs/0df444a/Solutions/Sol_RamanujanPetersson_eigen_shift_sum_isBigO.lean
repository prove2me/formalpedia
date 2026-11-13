-- Prove2me | solution 1 for RamanujanPetersson.eigen_shift_sum_isBigO
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-13T01:46:28.260034+00:00
-- url     : https://prove2.me/submissions/611d49ff-8ca8-45a7-ba65-c514eb5eead4

import Mathlib

set_option autoImplicit false

open UpperHalfPlane Filter Asymptotics MatrixGroups ModularForm

namespace RPN6

/-- Prime-power step: `b(p^(a+1)) = α b(p^a) + β^(a+1)` when `α + β = b p`, `α β = c_p`. -/
lemma pow_step (b : ℕ → ℂ) (p : ℕ) (hp : 0 < p) (cp α β : ℂ) (h1 : b 1 = 1)
    (hsum : α + β = b p) (hprod : α * β = cp)
    (hrec : ∀ n : ℕ, b (p * n) = b p * b n - cp * (if p ∣ n then b (n / p) else 0)) :
    ∀ a : ℕ, b (p ^ (a + 1)) = α * b (p ^ a) + β ^ (a + 1) := by
  intro a
  induction a with
  | zero => simp [h1, hsum]
  | succ a ih =>
    have hdv : p ∣ p ^ (a + 1) := dvd_pow_self p (Nat.succ_ne_zero a)
    have hdiv : p ^ (a + 1) / p = p ^ a := by rw [pow_succ', Nat.mul_div_cancel_left _ hp]
    have e1 := hrec (p ^ (a + 1))
    rw [if_pos hdv, hdiv, ← pow_succ'] at e1
    rw [e1, ih, ← hsum, ← hprod]
    ring

/-- `‖b(p^a)‖ ≤ (a+1) R^a` from the step relation with `‖α‖, ‖β‖ ≤ R`. -/
lemma pow_bound (b : ℕ → ℂ) (p : ℕ) (α β : ℂ) (R : ℝ) (hα : ‖α‖ ≤ R) (hβ : ‖β‖ ≤ R)
    (h1 : b 1 = 1) (hstep : ∀ a : ℕ, b (p ^ (a + 1)) = α * b (p ^ a) + β ^ (a + 1)) :
    ∀ a : ℕ, ‖b (p ^ a)‖ ≤ ((a : ℝ) + 1) * R ^ a := by
  have hR : 0 ≤ R := (norm_nonneg _).trans hα
  intro a
  induction a with
  | zero => simp [h1]
  | succ a ih =>
    rw [hstep a]
    calc ‖α * b (p ^ a) + β ^ (a + 1)‖ ≤ ‖α‖ * ‖b (p ^ a)‖ + ‖β‖ ^ (a + 1) := by
          refine (norm_add_le _ _).trans ?_
          rw [norm_mul, norm_pow]
      _ ≤ R * (((a : ℝ) + 1) * R ^ a) + R ^ (a + 1) :=
          add_le_add (mul_le_mul hα ih (norm_nonneg _) hR) (pow_le_pow_left₀ (norm_nonneg _) hβ _)
      _ = (((a + 1 : ℕ) : ℝ) + 1) * R ^ (a + 1) := by push_cast; ring

/-- Multiplicativity across a prime power. -/
lemma mult_pp (b : ℕ → ℂ) (p : ℕ) (hp : 0 < p) (cp : ℂ) (h1 : b 1 = 1)
    (hrec : ∀ n : ℕ, b (p * n) = b p * b n - cp * (if p ∣ n then b (n / p) else 0))
    (m : ℕ) (hm : ¬ p ∣ m) : ∀ a : ℕ, b (p ^ a * m) = b (p ^ a) * b m := by
  intro a
  induction a using Nat.twoStepInduction with
  | zero => simp [h1]
  | one => rw [pow_one, hrec m, if_neg hm, mul_zero, sub_zero]
  | more a ih0 ih1 =>
    show b (p ^ (a + 1 + 1) * m) = b (p ^ (a + 1 + 1)) * b m
    have hdv : p ∣ p ^ (a + 1) * m :=
      Dvd.dvd.mul_right (dvd_pow_self p (Nat.succ_ne_zero a)) m
    have hdiv : p ^ (a + 1) * m / p = p ^ a * m := by
      rw [pow_succ', mul_assoc, Nat.mul_div_cancel_left _ hp]
    have hdv' : p ∣ p ^ (a + 1) := dvd_pow_self p (Nat.succ_ne_zero a)
    have hdiv' : p ^ (a + 1) / p = p ^ a := by rw [pow_succ', Nat.mul_div_cancel_left _ hp]
    have e1 := hrec (p ^ (a + 1) * m)
    rw [if_pos hdv, hdiv, ← mul_assoc, ← pow_succ'] at e1
    have e2 := hrec (p ^ (a + 1))
    rw [if_pos hdv', hdiv', ← pow_succ'] at e2
    rw [e1, e2, ih0, ih1]
    ring

/-- Coprime multiplicativity of a Hecke-recursive sequence. -/
lemma mult (b : ℕ → ℂ) (cp : ℕ → ℂ) (h1 : b 1 = 1)
    (hrec : ∀ p : ℕ, p.Prime → ∀ n : ℕ,
      b (p * n) = b p * b n - cp p * (if p ∣ n then b (n / p) else 0)) :
    ∀ x y : ℕ, Nat.Coprime x y → b (x * y) = b x * b y := by
  intro x
  induction x using Nat.recOnPrimeCoprime with
  | zero =>
    intro y hy
    rw [Nat.coprime_zero_left] at hy
    subst hy
    simp [h1]
  | prime_pow p a hp =>
    intro y hy
    rcases Nat.eq_zero_or_pos a with rfl | ha
    · simp [h1]
    · have hpy : ¬ p ∣ y := by
        have : Nat.Coprime p y := Nat.Coprime.coprime_dvd_left (dvd_pow_self p ha.ne') hy
        exact (Nat.Prime.coprime_iff_not_dvd hp).1 this
      exact mult_pp b p hp.pos (cp p) h1 (hrec p hp) y hpy a
  | coprime u v _ _ huv ihu ihv =>
    intro y hy
    have huy : Nat.Coprime u y := Nat.Coprime.coprime_dvd_left (dvd_mul_right u v) hy
    have hvy : Nat.Coprime v y := Nat.Coprime.coprime_dvd_left (dvd_mul_left v u) hy
    rw [mul_assoc, ihu (v * y) (Nat.Coprime.mul_right huv huy), ihv y hvy, ihu v huv]
    ring

/-- Both roots of `X^2 - s0 X + c` exist in `ℂ`. -/
lemma roots_exist (s0 c : ℂ) : ∃ α β : ℂ, α + β = s0 ∧ α * β = c ∧
    α ^ 2 - s0 * α + c = 0 ∧ β ^ 2 - s0 * β + c = 0 := by
  obtain ⟨s, hs⟩ := IsAlgClosed.exists_pow_nat_eq (s0 ^ 2 - 4 * c) (by norm_num : 0 < 2)
  refine ⟨(s0 + s) / 2, (s0 - s) / 2, by ring, ?_, ?_, ?_⟩
  · linear_combination (-1/4 : ℂ) * hs
  · linear_combination (1/4 : ℂ) * hs
  · linear_combination (1/4 : ℂ) * hs

/-- Prime-power product bound for `‖b n‖`. -/
lemma seq_pp_bound (b : ℕ → ℂ) (cp : ℕ → ℂ) (R : ℕ → ℝ) (h1 : b 1 = 1)
    (hrec : ∀ p : ℕ, p.Prime → ∀ n : ℕ,
      b (p * n) = b p * b n - cp p * (if p ∣ n then b (n / p) else 0))
    (hroots : ∀ p : ℕ, p.Prime → ∃ α β : ℂ, α + β = b p ∧ α * β = cp p ∧ ‖α‖ ≤ R p ∧ ‖β‖ ≤ R p) :
    ∀ n : ℕ, n ≠ 0 → ‖b n‖ ≤ n.factorization.prod (fun p a => ((a : ℝ) + 1) * R p ^ a) := by
  intro n hn
  have hm := mult b cp h1 hrec
  have hfac : b n = n.factorization.prod (fun p a => b (p ^ a)) :=
    Nat.multiplicative_factorization b hm h1 hn
  rw [hfac]
  simp only [Finsupp.prod]
  rw [norm_prod]
  apply Finset.prod_le_prod
  · intro p _; exact norm_nonneg _
  · intro p hp
    have hpp : p.Prime := by
      rw [Nat.support_factorization] at hp
      exact Nat.prime_of_mem_primeFactors hp
    obtain ⟨α, β, hs, hpr, hα, hβ⟩ := hroots p hpp
    exact pow_bound b p α β (R p) hα hβ h1
      (pow_step b p hpp.pos (cp p) α β h1 hs hpr (hrec p hpp)) _

/-- The local divisor-type inequality `(a+1) ≤ g(p) (p^ε)^a`. -/
lemma local_const (ε : ℝ) (hε : 0 < ε) : ∃ K : ℝ, 1 ≤ K ∧ ∃ P : ℕ, ∀ p : ℕ, p.Prime → ∀ a : ℕ,
    ((a : ℝ) + 1) ≤ (if p < P then K else 1) * ((p : ℝ) ^ ε) ^ a := by
  have hq1 : 1 < (2 : ℝ) ^ ε := Real.one_lt_rpow (by norm_num) hε
  have hq0 : 0 < (2 : ℝ) ^ ε - 1 := by linarith
  have hinv : 0 < 1 / ((2 : ℝ) ^ ε - 1) := div_pos one_pos hq0
  refine ⟨1 + 1 / ((2 : ℝ) ^ ε - 1), by linarith, ⌈(2 : ℝ) ^ (1 / ε)⌉₊, ?_⟩
  intro p hp a
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  split_ifs with hP
  · have h1 : (2 : ℝ) ^ ε ≤ (p : ℝ) ^ ε := Real.rpow_le_rpow (by norm_num) hp2 hε.le
    have h2 : ((2 : ℝ) ^ ε) ^ a ≤ ((p : ℝ) ^ ε) ^ a := pow_le_pow_left₀ (by linarith) h1 a
    have h3 : 1 + (a : ℝ) * ((2 : ℝ) ^ ε - 1) ≤ ((2 : ℝ) ^ ε) ^ a := by
      have h := one_add_mul_le_pow (by linarith : (-2 : ℝ) ≤ (2 : ℝ) ^ ε - 1) a
      have e : (1 : ℝ) + ((2 : ℝ) ^ ε - 1) = (2 : ℝ) ^ ε := by ring
      rw [e] at h
      exact h
    have h4 : ((a : ℝ) + 1) ≤
        (1 + 1 / ((2 : ℝ) ^ ε - 1)) * (1 + (a : ℝ) * ((2 : ℝ) ^ ε - 1)) := by
      have e : (1 + 1 / ((2 : ℝ) ^ ε - 1)) * (1 + (a : ℝ) * ((2 : ℝ) ^ ε - 1)) =
          ((a : ℝ) + 1) + (a : ℝ) * ((2 : ℝ) ^ ε - 1) + 1 / ((2 : ℝ) ^ ε - 1) := by
        field_simp
        ring
      rw [e]
      have : 0 ≤ (a : ℝ) * ((2 : ℝ) ^ ε - 1) := mul_nonneg (Nat.cast_nonneg a) hq0.le
      linarith
    calc ((a : ℝ) + 1) ≤ (1 + 1 / ((2 : ℝ) ^ ε - 1)) * (1 + (a : ℝ) * ((2 : ℝ) ^ ε - 1)) := h4
      _ ≤ (1 + 1 / ((2 : ℝ) ^ ε - 1)) * ((p : ℝ) ^ ε) ^ a := by
        apply mul_le_mul_of_nonneg_left (h3.trans h2)
        linarith
  · have hP2 : ⌈(2 : ℝ) ^ (1 / ε)⌉₊ ≤ p := not_lt.1 hP
    have hP' : (2 : ℝ) ^ (1 / ε) ≤ p := (Nat.le_ceil _).trans (by exact_mod_cast hP2)
    have h1 : (2 : ℝ) ≤ (p : ℝ) ^ ε := by
      have h := Real.rpow_le_rpow (by positivity) hP' hε.le
      rwa [← Real.rpow_mul (by norm_num), one_div_mul_cancel hε.ne', Real.rpow_one] at h
    have h2 : (2 : ℝ) ^ a ≤ ((p : ℝ) ^ ε) ^ a := pow_le_pow_left₀ (by norm_num) h1 a
    have h3 : 1 + (a : ℝ) * 1 ≤ (1 + 1) ^ a := one_add_mul_le_pow (by norm_num) a
    have e : (1 : ℝ) + 1 = 2 := by norm_num
    rw [e, mul_one] at h3
    rw [one_mul]
    linarith

lemma prod_g_le (S : Finset ℕ) (K : ℝ) (hK : 1 ≤ K) (P : ℕ) :
    ∏ p ∈ S, (if p < P then K else 1) ≤ K ^ P := by
  rw [← Finset.prod_filter, Finset.prod_const]
  apply pow_le_pow_right₀ hK
  calc (S.filter (· < P)).card ≤ (Finset.range P).card := by
        apply Finset.card_le_card
        intro x hx
        simp only [Finset.mem_filter] at hx
        exact Finset.mem_range.2 hx.2
    _ = P := Finset.card_range P

lemma rpow_split (p : ℕ) (hp : 0 < p) (θ ε : ℝ) (a : ℕ) :
    (((p ^ a : ℕ) : ℝ)) ^ (θ + ε) = ((p : ℝ) ^ θ) ^ a * ((p : ℝ) ^ ε) ^ a := by
  have hp0 : (0 : ℝ) ≤ p := Nat.cast_nonneg p
  have hpos : (0 : ℝ) < p := by exact_mod_cast hp
  rw [Nat.cast_pow, ← Real.rpow_natCast_mul hp0, mul_comm (a : ℝ) (θ + ε),
    Real.rpow_mul_natCast hp0, Real.rpow_add hpos, mul_pow]

lemma prod_bound (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) (e : ℕ → ℕ) (θ ε K : ℝ) (hK : 1 ≤ K)
    (P : ℕ)
    (hloc : ∀ p : ℕ, p.Prime → ∀ a : ℕ,
      ((a : ℝ) + 1) ≤ (if p < P then K else 1) * ((p : ℝ) ^ ε) ^ a) :
    ∏ p ∈ S, ((e p : ℝ) + 1) * ((p : ℝ) ^ θ) ^ e p ≤
      K ^ P * ∏ p ∈ S, (((p ^ e p : ℕ) : ℝ)) ^ (θ + ε) := by
  calc ∏ p ∈ S, ((e p : ℝ) + 1) * ((p : ℝ) ^ θ) ^ e p
      ≤ ∏ p ∈ S, ((if p < P then K else 1) * (((p ^ e p : ℕ) : ℝ)) ^ (θ + ε)) := by
        apply Finset.prod_le_prod
        · intro p _; positivity
        · intro p hp
          have hpp := hS p hp
          rw [rpow_split p hpp.pos θ ε (e p)]
          have hθa : 0 ≤ ((p : ℝ) ^ θ) ^ e p := by positivity
          calc ((e p : ℝ) + 1) * ((p : ℝ) ^ θ) ^ e p
              ≤ ((if p < P then K else 1) * ((p : ℝ) ^ ε) ^ e p) * ((p : ℝ) ^ θ) ^ e p :=
                mul_le_mul_of_nonneg_right (hloc p hpp (e p)) hθa
            _ = (if p < P then K else 1) * (((p : ℝ) ^ θ) ^ e p * ((p : ℝ) ^ ε) ^ e p) := by
                ring
    _ = (∏ p ∈ S, (if p < P then K else 1)) * ∏ p ∈ S, (((p ^ e p : ℕ) : ℝ)) ^ (θ + ε) :=
        Finset.prod_mul_distrib
    _ ≤ K ^ P * ∏ p ∈ S, (((p ^ e p : ℕ) : ℝ)) ^ (θ + ε) := by
        apply mul_le_mul_of_nonneg_right (prod_g_le S K hK P)
        apply Finset.prod_nonneg
        intro p _
        positivity

/-- Divisor-type bound: `∏ (a_p+1) p^(θ a_p) ≤ C n^(θ+ε)`. -/
lemma fac_bound (θ ε : ℝ) (hε : 0 < ε) : ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, n ≠ 0 →
    n.factorization.prod (fun p a => ((a : ℝ) + 1) * ((p : ℝ) ^ θ) ^ a) ≤
      C * (n : ℝ) ^ (θ + ε) := by
  obtain ⟨K, hK, P, hloc⟩ := local_const ε hε
  refine ⟨K ^ P, by positivity, ?_⟩
  intro n hn
  have hmulR : ∀ x y : ℕ, Nat.Coprime x y →
      ((x * y : ℕ) : ℝ) ^ (θ + ε) = ((x : ℕ) : ℝ) ^ (θ + ε) * ((y : ℕ) : ℝ) ^ (θ + ε) := by
    intro x y _
    rw [Nat.cast_mul, Real.mul_rpow (Nat.cast_nonneg _) (Nat.cast_nonneg _)]
  have hfacR : ((n : ℕ) : ℝ) ^ (θ + ε) =
      n.factorization.prod (fun p a => (((p ^ a : ℕ) : ℝ)) ^ (θ + ε)) :=
    Nat.multiplicative_factorization (fun m : ℕ => ((m : ℝ)) ^ (θ + ε)) hmulR (by simp) hn
  rw [hfacR]
  simp only [Finsupp.prod]
  refine prod_bound n.factorization.support (fun p hp => ?_) (fun p => n.factorization p)
    θ ε K hK P hloc
  rw [Nat.support_factorization] at hp
  exact Nat.prime_of_mem_primeFactors hp

/-- Per-sequence bound `‖b n‖ ≤ C n^((k-1)/2+ε)` for `n ≠ 0`. -/
lemma seq_bound (k : ℤ) (_hk : 1 ≤ k) (ε : ℝ) (hε : 0 < ε) (L : ℕ) (χ : DirichletCharacter ℂ L)
    (b : ℕ → ℂ) (h1 : b 1 = 1)
    (hrec : ∀ p n : ℕ, p.Prime →
      b (p * n) = b p * b n -
        (if p ∣ L then 0 else
          χ (p : ZMod L) * (p : ℂ) ^ (k - 1) * (if p ∣ n then b (n / p) else 0)))
    (hbad : ∀ p : ℕ, p.Prime → p ∣ L → ‖b p‖ ≤ (p : ℝ) ^ (((k : ℝ) - 1) / 2))
    (hroot : ∀ p : ℕ, p.Prime → ¬ p ∣ L → ∀ α : ℂ,
      α ^ 2 - b p * α + χ (p : ZMod L) * (p : ℂ) ^ (k - 1) = 0 →
        ‖α‖ ≤ (p : ℝ) ^ (((k : ℝ) - 1) / 2)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, n ≠ 0 → ‖b n‖ ≤ C * (n : ℝ) ^ (((k : ℝ) - 1) / 2 + ε) := by
  let cp : ℕ → ℂ := fun p => if p ∣ L then 0 else χ (p : ZMod L) * (p : ℂ) ^ (k - 1)
  have hrec' : ∀ p : ℕ, p.Prime → ∀ n : ℕ,
      b (p * n) = b p * b n - cp p * (if p ∣ n then b (n / p) else 0) := by
    intro p hp n
    rw [hrec p n hp]
    simp only [cp]
    split_ifs <;> ring
  have hroots : ∀ p : ℕ, p.Prime → ∃ α β : ℂ, α + β = b p ∧ α * β = cp p ∧
      ‖α‖ ≤ (p : ℝ) ^ (((k : ℝ) - 1) / 2) ∧ ‖β‖ ≤ (p : ℝ) ^ (((k : ℝ) - 1) / 2) := by
    intro p hp
    by_cases hpL : p ∣ L
    · refine ⟨b p, 0, by ring, ?_, hbad p hp hpL, ?_⟩
      · simp only [cp, if_pos hpL, mul_zero]
      · rw [norm_zero]; exact Real.rpow_nonneg (Nat.cast_nonneg p) _
    · obtain ⟨α, β, hs, hpr, hα, hβ⟩ :=
        roots_exist (b p) (χ (p : ZMod L) * (p : ℂ) ^ (k - 1))
      refine ⟨α, β, hs, ?_, hroot p hp hpL α hα, hroot p hp hpL β hβ⟩
      simp only [cp, if_neg hpL]
      exact hpr
  obtain ⟨C, hC0, hC⟩ := fac_bound (((k : ℝ) - 1) / 2) ε hε
  refine ⟨C, hC0, fun n hn => ?_⟩
  exact (seq_pp_bound b cp (fun p => (p : ℝ) ^ (((k : ℝ) - 1) / 2)) h1 hrec' hroots n hn).trans
    (hC n hn)

end RPN6

theorem solution (k : ℤ) (hk : 1 ≤ k) (ε : ℝ) (hε : 0 < ε) (r : ℕ)
    (c : Fin r → ℂ) (d L : Fin r → ℕ) (χ : (i : Fin r) → DirichletCharacter ℂ (L i))
    (b : Fin r → ℕ → ℂ) (hd : ∀ i, 0 < d i) (h1 : ∀ i, b i 1 = 1)
    (hrec : ∀ i, ∀ p n : ℕ, p.Prime →
      b i (p * n) = b i p * b i n -
        (if p ∣ L i then 0 else
          χ i (p : ZMod (L i)) * (p : ℂ) ^ (k - 1) * (if p ∣ n then b i (n / p) else 0)))
    (hbad : ∀ i, ∀ p : ℕ, p.Prime → p ∣ L i → ‖b i p‖ ≤ (p : ℝ) ^ (((k : ℝ) - 1) / 2))
    (hroot : ∀ i, ∀ p : ℕ, p.Prime → ¬ p ∣ L i → ∀ α : ℂ,
      α ^ 2 - b i p * α + χ i (p : ZMod (L i)) * (p : ℂ) ^ (k - 1) = 0 →
        ‖α‖ ≤ (p : ℝ) ^ (((k : ℝ) - 1) / 2)) :
    (fun n : ℕ => ∑ i, c i * (if d i ∣ n then b i (n / d i) else 0))
      =O[atTop] fun n : ℕ => (n : ℝ) ^ (((k : ℝ) - 1) / 2 + ε) := by
  have hσ : 0 ≤ ((k : ℝ) - 1) / 2 + ε := by
    have : (1 : ℝ) ≤ k := by exact_mod_cast hk
    have : 0 ≤ ((k : ℝ) - 1) / 2 := by linarith
    linarith
  apply Asymptotics.IsBigO.fun_sum
  intro i _
  obtain ⟨C, hC0, hC⟩ :=
    RPN6.seq_bound k hk ε hε (L i) (χ i) (b i) (h1 i) (hrec i) (hbad i) (hroot i)
  apply Asymptotics.IsBigO.of_bound (‖c i‖ * C)
  filter_upwards [Filter.eventually_ge_atTop 1] with n hn
  rw [norm_mul, Real.norm_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _), mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  split_ifs with hdn
  · have hq : n / d i ≠ 0 := (Nat.div_pos_iff.2 ⟨hd i, Nat.le_of_dvd hn hdn⟩).ne'
    calc ‖b i (n / d i)‖ ≤ C * ((n / d i : ℕ) : ℝ) ^ (((k : ℝ) - 1) / 2 + ε) := hC _ hq
      _ ≤ C * (n : ℝ) ^ (((k : ℝ) - 1) / 2 + ε) := by
        apply mul_le_mul_of_nonneg_left _ hC0
        apply Real.rpow_le_rpow (Nat.cast_nonneg _) _ hσ
        exact_mod_cast Nat.div_le_self n (d i)
  · rw [norm_zero]
    exact mul_nonneg hC0 (Real.rpow_nonneg (Nat.cast_nonneg n) _)
