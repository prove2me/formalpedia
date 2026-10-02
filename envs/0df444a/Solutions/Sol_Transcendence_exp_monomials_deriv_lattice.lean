-- Prove2me | solution 1 for Transcendence.exp_monomials_deriv_lattice
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-02T09:34:57.331654+00:00
-- url     : https://prove2.me/submissions/6e4a9e1b-f111-4c70-8949-4499b74e0017

import Mathlib
import Theorems.Thm_Transcendence_exp_monomial_derivs

/-!
# Derivatives of an integer combination of exponential monomials at lattice points

The algebraic half of the Liouville step (4.14) of Waldschmidt's §4.6. For each monomial
`φ_{τ,t}(z) = z_{k₀}^τ e^{⟨t₁x₁ + ⋯ + t_{d₁}x_{d₁}, z⟩}`, node 2 (`exp_monomial_derivs`), applied to
`w = Σ tᵢ ξᵢ ∈ K^ι` and `v = Σ s_j η_j`, writes the derivative at `q = Σ s_j y_j` as `φK γ₀ · e^{⟨w, q⟩}`,
and the exponential factor is `φK (∏ a_{ij}^{tᵢ s_j})`. Then `γ = Σ p_{τ,t} γ_{τ,t}`, whose house and
denominator are bounded termwise.
-/

open NumberField

namespace ExpMonomialsDerivLattice

/-- Monotonicity of finite products of non-negative reals (kept local: the Mathlib name differs between
versions). -/
lemma prod_le_prod_nn {α : Type*} (s : Finset α) {f g : α → ℝ} (h0 : ∀ i ∈ s, 0 ≤ f i)
    (h1 : ∀ i ∈ s, f i ≤ g i) : ∏ i ∈ s, f i ≤ ∏ i ∈ s, g i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    simp only [Finset.mem_insert, forall_eq_or_imp] at h0 h1
    rw [Finset.prod_insert ha, Finset.prod_insert ha]
    exact mul_le_mul h1.1 (ih h0.2 h1.2) (Finset.prod_nonneg h0.2) (h0.1.trans h1.1)

section house

variable {K : Type*} [Field K] [NumberField K]

lemma house_one_le : house (1 : K) ≤ 1 := by
  have := house_intCast (K := K) 1
  simp only [Int.cast_one] at this
  rw [this]; simp

lemma house_prod_le' {α : Type*} (s : Finset α) (f : α → K) :
    house (∏ i ∈ s, f i) ≤ ∏ i ∈ s, house (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using house_one_le
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha]
    exact (house_mul_le _ _).trans (mul_le_mul_of_nonneg_left ih (house_nonneg _))

lemma house_intCast_mul_le (c : ℤ) (α : K) : house ((c : K) * α) ≤ |(c : ℝ)| * house α := by
  have := house_mul_le (c : K) α
  rw [house_intCast] at this
  simpa using this

lemma house_natCast_mul_le (c : ℕ) (α : K) : house ((c : K) * α) ≤ c * house α :=
  (house_nat_mul α c).le

/-- `house (α ^ i) ≤ house α ^ i` (kept local, as `prod_le_prod_nn`). -/
lemma house_pow_le' (α : K) (i : ℕ) : house (α ^ i) ≤ house α ^ i := by
  induction i with
  | zero => simpa using house_one_le
  | succ i ih =>
    rw [pow_succ, pow_succ]
    exact (house_mul_le _ _).trans (mul_le_mul_of_nonneg_right ih (house_nonneg _))

omit [NumberField K] in
lemma isIntegral_pow_mul_of_le {δ : ℤ} {γ : K} {a b : ℕ} (hab : a ≤ b)
    (h : IsIntegral ℤ ((δ : K) ^ a * γ)) : IsIntegral ℤ ((δ : K) ^ b * γ) := by
  have e : (δ : K) ^ b * γ = (δ : K) ^ (b - a) * ((δ : K) ^ a * γ) := by
    rw [← mul_assoc, ← pow_add, Nat.sub_add_cancel hab]
  rw [e]
  exact ((isIntegral_intCast δ).pow _).mul h

end house

/-! ## Exponential monomials -/

lemma analyticAt_linear {ι : Type*} [Fintype ι] (c : ι → ℂ) (z : ι → ℂ) :
    AnalyticAt ℂ (fun z : ι → ℂ => ∑ ν, c ν * z ν) z := by
  have : (fun z : ι → ℂ => ∑ ν, c ν * z ν) = ∑ ν, fun z : ι → ℂ => c ν * z ν := by
    funext z; simp
  rw [this]
  exact Finset.analyticAt_sum _ fun ν _ =>
    analyticAt_const.mul ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : ι => ℂ) ν).analyticAt z)

lemma analytic_expMono {ι : Type*} [Fintype ι] (k₀ : ι) (τ : ℕ) (c : ι → ℂ) :
    AnalyticOnNhd ℂ (fun z : ι → ℂ => z k₀ ^ τ * Complex.exp (∑ ν, c ν * z ν)) Set.univ := by
  intro z _
  have h1 : AnalyticAt ℂ (fun z : ι → ℂ => z k₀) z :=
    (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : ι => ℂ) k₀).analyticAt z
  exact (h1.pow τ).mul (analyticAt_linear c z).cexp

/-- Derivatives of a finite linear combination of entire functions. -/
lemma iteratedFDeriv_lincomb_apply {ι Λ : Type*} [Fintype ι] [Fintype Λ] (a : Λ → ℂ)
    (φ : Λ → (ι → ℂ) → ℂ) (hφ : ∀ l, AnalyticOnNhd ℂ (φ l) Set.univ) (k : ℕ) (q : ι → ℂ)
    (v : Fin k → ι → ℂ) : iteratedFDeriv ℂ k (fun z => ∑ l, a l * φ l z) q v =
      ∑ l, a l * iteratedFDeriv ℂ k (φ l) q v := by
  rw [iteratedFDeriv_fun_sum_apply (u := Finset.univ) (fun l _ =>
    contDiffAt_const.mul ((hφ l).contDiff.contDiffAt)), sum_apply]
  refine Finset.sum_congr rfl fun l _ => ?_
  simpa only [smul_apply, smul_eq_mul] using congrArg (· v)
    (iteratedFDeriv_const_smul_apply' (a := a l) ((hφ l).contDiff.contDiffAt (n := k) (x := q)))

/-! ## One monomial at a lattice point -/

/-- `house (Σ tᵢ ξᵢ) ≤ (d₁ + 1) T H` when `tᵢ ≤ T` and `house ξᵢ ≤ H`. -/
lemma house_lincomb_le {K : Type*} [Field K] [NumberField K] {d₁ T : ℕ} (ξ : Fin d₁ → K) {H : ℝ}
    (hH : 1 ≤ H) (hξH : ∀ i, house (ξ i) ≤ H) (t : Fin d₁ → ℕ) (ht : ∀ i, t i ≤ T) :
    house (∑ i, (t i : K) * ξ i) ≤ ((d₁ : ℝ) + 1) * T * H := by
  calc house (∑ i, (t i : K) * ξ i) ≤ ∑ i, house ((t i : K) * ξ i) := house_sum_le_sum_house _ _
    _ ≤ ∑ i, (t i : ℝ) * house (ξ i) := Finset.sum_le_sum fun i _ => house_natCast_mul_le _ _
    _ ≤ ∑ _i : Fin d₁, (T : ℝ) * H := Finset.sum_le_sum fun i _ =>
        mul_le_mul (by exact_mod_cast ht i) (hξH i) (house_nonneg _) (by positivity)
    _ = d₁ * T * H := by simp; ring
    _ ≤ ((d₁ : ℝ) + 1) * T * H := by
        have : (0 : ℝ) ≤ T * H := by positivity
        nlinarith

lemma sum_ts_le {ι : Type*} [Fintype ι] {d₁ T S₁ : ℕ} (t : Fin d₁ → ℕ) (ht : ∀ i, t i ≤ T)
    (s : ι → ℕ) (hs : ∀ j, s j < S₁) : ∑ i, ∑ j, t i * s j ≤ d₁ * Fintype.card ι * T * S₁ := by
  calc ∑ i, ∑ j, t i * s j ≤ ∑ _i : Fin d₁, ∑ _j : ι, T * S₁ :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => Nat.mul_le_mul (ht i) (hs j).le
    _ = d₁ * Fintype.card ι * T * S₁ := by simp; ring

/-- The exponential factor at a lattice point: `e^{⟨Σ tᵢxᵢ, Σ s_j y_j⟩} = φK (∏ a_{ij}^{tᵢ s_j})`. -/
lemma exp_factor_eq {K : Type*} [Field K] (φK : K →+* ℂ) {ι : Type*} [Fintype ι] {d₁ : ℕ}
    (x : Fin d₁ → ι → ℂ) (y : ι → ι → ℂ) (a : Fin d₁ → ι → K)
    (ha : ∀ i j, φK (a i j) = Complex.exp (∑ ν, x i ν * y j ν)) (t : Fin d₁ → ℕ) (s : ι → ℕ) :
    Complex.exp (∑ ν, (∑ i, (t i : ℂ) * x i ν) * ∑ j, (s j : ℂ) * y j ν) =
      φK (∏ i, ∏ j, a i j ^ (t i * s j)) := by
  have e1 : ∑ ν, (∑ i, (t i : ℂ) * x i ν) * ∑ j, (s j : ℂ) * y j ν =
      ∑ i, ∑ j, ((t i * s j : ℕ) : ℂ) * (∑ ν, x i ν * y j ν) := by
    simp_rw [Finset.sum_mul_sum, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun ν _ => ?_
    push_cast; ring
  rw [e1, Complex.exp_sum, map_prod]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [Complex.exp_sum, map_prod]
  exact Finset.prod_congr rfl fun j _ => by rw [Complex.exp_nat_mul, map_pow, ha]

lemma house_exp_factor_le {K : Type*} [Field K] [NumberField K] {ι : Type*} [Fintype ι] {d₁ : ℕ}
    (a : Fin d₁ → ι → K) {H : ℝ} (hH : 1 ≤ H) (haH : ∀ i j, house (a i j) ≤ H) {T S₁ : ℕ}
    (t : Fin d₁ → ℕ) (ht : ∀ i, t i ≤ T) (s : ι → ℕ) (hs : ∀ j, s j < S₁) :
    house (∏ i, ∏ j, a i j ^ (t i * s j)) ≤ H ^ (d₁ * Fintype.card ι * T * S₁) := by
  calc house (∏ i, ∏ j, a i j ^ (t i * s j))
      ≤ ∏ i, house (∏ j, a i j ^ (t i * s j)) := house_prod_le' _ _
    _ ≤ ∏ i, ∏ j, house (a i j ^ (t i * s j)) :=
        prod_le_prod_nn _ (fun i _ => house_nonneg _) fun i _ => house_prod_le' _ _
    _ ≤ ∏ i, ∏ j, H ^ (t i * s j) :=
        prod_le_prod_nn _ (fun i _ => Finset.prod_nonneg fun j _ => house_nonneg _)
          fun i _ => prod_le_prod_nn _ (fun j _ => house_nonneg _) fun j _ =>
            (house_pow_le' _ _).trans (pow_le_pow_left₀ (house_nonneg _) (haH i j) _)
    _ = H ^ (∑ i, ∑ j, t i * s j) := by
        rw [← Finset.prod_pow_eq_pow_sum]
        exact Finset.prod_congr rfl fun i _ => Finset.prod_pow_eq_pow_sum _ _ _
    _ ≤ H ^ (d₁ * Fintype.card ι * T * S₁) := pow_le_pow_right₀ hH (sum_ts_le t ht s hs)

lemma isIntegral_exp_factor {K : Type*} [Field K] {ι : Type*} [Fintype ι] {d₁ : ℕ}
    (a : Fin d₁ → ι → K) {δ : ℤ} (hδa : ∀ i j, IsIntegral ℤ ((δ : K) * a i j))
    (t : Fin d₁ → ℕ) (s : ι → ℕ) :
    IsIntegral ℤ ((δ : K) ^ (∑ i, ∑ j, t i * s j) * ∏ i, ∏ j, a i j ^ (t i * s j)) := by
  have e : ∏ i, ∏ j, ((δ : K) * a i j) ^ (t i * s j) =
      (δ : K) ^ (∑ i, ∑ j, t i * s j) * ∏ i, ∏ j, a i j ^ (t i * s j) := by
    simp_rw [mul_pow, Finset.prod_mul_distrib]
    congr 1
    rw [← Finset.prod_pow_eq_pow_sum]
    exact Finset.prod_congr rfl fun i _ => Finset.prod_pow_eq_pow_sum _ _ _
  rw [← e]
  exact IsIntegral.prod _ fun i _ => IsIntegral.prod _ fun j _ => (hδa i j).pow _

end ExpMonomialsDerivLattice

open NumberField ExpMonomialsDerivLattice in
/-- **Derivatives of an integer combination of exponential monomials at lattice points** (DALAG §4.6,
the algebraic half of (4.14)). -/
theorem solution {K : Type*} [Field K] [NumberField K] (φK : K →+* ℂ)
    {ι : Type*} [Fintype ι] [DecidableEq ι] {d₁ : ℕ} (x : Fin d₁ → ι → ℂ) (y : ι → ι → ℂ)
    (k₀ : ι) (ξ : Fin d₁ → ι → K) (hξ : ∀ i ν, φK (ξ i ν) = x i ν) (η : ι → K)
    (a : Fin d₁ → ι → K) (ha : ∀ i j, φK (a i j) = Complex.exp (∑ ν, x i ν * y j ν))
    (δ : ℤ) (hδξ : ∀ i ν, IsIntegral ℤ ((δ : K) * ξ i ν))
    (hδη : ∀ j, IsIntegral ℤ ((δ : K) * η j)) (hδa : ∀ i j, IsIntegral ℤ ((δ : K) * a i j))
    {H : ℝ} (hH : 1 ≤ H) (hξH : ∀ i ν, house (ξ i ν) ≤ H) (hηH : ∀ j, house (η j) ≤ H)
    (haH : ∀ i j, house (a i j) ≤ H) {T₀ T₁ S₁ : ℕ} (hη : 0 < T₀ → ∀ j, φK (η j) = y j k₀)
    (hT₁ : 1 ≤ T₁) (p : Fin (T₀ + 1) × (Fin d₁ → Fin (T₁ + 1)) → ℤ) {X : ℝ}
    (hp : ∀ l, |(p l : ℝ)| ≤ X) (s : ι → Fin S₁) (k : ℕ) (L : Fin k → ι) :
    ∃ γ : K, iteratedFDeriv ℂ k (fun z : ι → ℂ => ∑ l, (p l : ℂ) * (z k₀ ^ (l.1 : ℕ) *
        Complex.exp (∑ ν, (∑ i, ((l.2 i : ℕ) : ℂ) * x i ν) * z ν))) (∑ j, ((s j : ℕ) : ℂ) • y j)
        (fun l => Pi.single (L l) 1) = φK γ ∧
      house γ ≤ ((T₀ : ℝ) + 1) * ((T₁ : ℝ) + 1) ^ d₁ * X * ((((d₁ : ℝ) + 1) * T₁ * H) ^ k *
        ((Fintype.card ι : ℝ) * S₁ * H + k) ^ T₀ * H ^ (d₁ * Fintype.card ι * T₁ * S₁)) ∧
      IsIntegral ℤ ((δ : K) ^ (k + T₀ + d₁ * Fintype.card ι * T₁ * S₁) * γ) := by
  classical
  set n := Fintype.card ι with hn_def
  have hn : (1 : ℝ) ≤ n := by exact_mod_cast Fintype.card_pos_iff.mpr ⟨k₀⟩
  have hS₁ : (1 : ℝ) ≤ S₁ := by exact_mod_cast lt_of_le_of_lt (Nat.zero_le _) (s k₀).2
  have hT₁' : (1 : ℝ) ≤ T₁ := by exact_mod_cast hT₁
  /- The `k₀`-th coordinate of the lattice point is `φK v`, `v = Σ s_j η_j`. -/
  set v : K := ∑ j, ((s j : ℕ) : K) * η j with hv
  have hδv : IsIntegral ℤ ((δ : K) * v) := by
    have : (δ : K) * v = ∑ j, ((s j : ℕ) : K) * ((δ : K) * η j) := by
      rw [hv, Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring
    rw [this]
    exact IsIntegral.sum _ fun j _ => (isIntegral_natCast _).mul (hδη j)
  have hvB : house v ≤ (n : ℝ) * S₁ * H := by
    calc house v ≤ ∑ j, house (((s j : ℕ) : K) * η j) := house_sum_le_sum_house _ _
      _ ≤ ∑ j, ((s j : ℕ) : ℝ) * house (η j) :=
          Finset.sum_le_sum fun j _ => house_natCast_mul_le _ _
      _ ≤ ∑ _j : ι, (S₁ : ℝ) * H := Finset.sum_le_sum fun j _ =>
          mul_le_mul (by exact_mod_cast (s j).2.le) (hηH j) (house_nonneg _) (by positivity)
      _ = (n : ℝ) * S₁ * H := by simp [hn_def]; ring
  have hvφ : 0 < T₀ → φK v = ∑ j, ((s j : ℕ) : ℂ) * y j k₀ := by
    intro hT₀
    rw [hv, map_sum]
    exact Finset.sum_congr rfl fun j _ => by rw [map_mul, map_natCast, hη hT₀ j]
  set q : ι → ℂ := ∑ j, ((s j : ℕ) : ℂ) • y j with hq
  have hqν : ∀ ν, q ν = ∑ j, ((s j : ℕ) : ℂ) * y j ν := by
    intro ν; simp [hq, Finset.sum_apply]
  /- One algebraic number for each monomial: node 2, times the exponential factor. -/
  have hterm : ∀ l : Fin (T₀ + 1) × (Fin d₁ → Fin (T₁ + 1)), ∃ γ : K,
      iteratedFDeriv ℂ k (fun z : ι → ℂ => z k₀ ^ (l.1 : ℕ) *
        Complex.exp (∑ ν, (∑ i, ((l.2 i : ℕ) : ℂ) * x i ν) * z ν)) q
        (fun l => Pi.single (L l) 1) = φK γ ∧
      house γ ≤ (((d₁ : ℝ) + 1) * T₁ * H) ^ k * ((n : ℝ) * S₁ * H + k) ^ T₀ *
        H ^ (d₁ * n * T₁ * S₁) ∧
      IsIntegral ℤ ((δ : K) ^ (k + T₀ + d₁ * n * T₁ * S₁) * γ) := by
    intro l
    set t : Fin d₁ → ℕ := fun i => (l.2 i : ℕ) with ht_def
    have ht : ∀ i, t i ≤ T₁ := fun i => Nat.lt_succ_iff.mp (l.2 i).2
    have hτ : (l.1 : ℕ) ≤ T₀ := Nat.lt_succ_iff.mp l.1.2
    set w : ι → K := fun ν => ∑ i, (t i : K) * ξ i ν with hw
    have hwφ : ∀ ν, φK (w ν) = ∑ i, (t i : ℂ) * x i ν := by
      intro ν; simp [hw, map_sum, map_mul, map_natCast, hξ]
    have hδw : ∀ ν, IsIntegral ℤ ((δ : K) * w ν) := by
      intro ν
      have : (δ : K) * w ν = ∑ i, (t i : K) * ((δ : K) * ξ i ν) := by
        rw [hw, Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
      rw [this]
      exact IsIntegral.sum _ fun i _ => (isIntegral_natCast _).mul (hδξ i ν)
    have hA1 : 1 ≤ ((d₁ : ℝ) + 1) * T₁ * H := by
      have : (1 : ℝ) ≤ (d₁ : ℝ) + 1 := by linarith [(Nat.cast_nonneg d₁ : (0 : ℝ) ≤ d₁)]
      exact one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le this hT₁') hH
    obtain ⟨γ₀, hγ₀, hγ₀h, hγ₀i⟩ := Transcendence.exp_monomial_derivs φK k₀ (l.1 : ℕ) w v q
      (fun hτ0 => by rw [hvφ (lt_of_lt_of_le hτ0 hτ), hqν]) hA1
      (fun ν => house_lincomb_le (fun i => ξ i ν) hH (fun i => hξH i ν) t ht) hvB δ hδw hδv k L
    refine ⟨γ₀ * ∏ i, ∏ j, a i j ^ (t i * (s j : ℕ)), ?_, ?_, ?_⟩
    · have hfun : (fun z : ι → ℂ => z k₀ ^ (l.1 : ℕ) *
          Complex.exp (∑ ν, (∑ i, ((l.2 i : ℕ) : ℂ) * x i ν) * z ν)) =
          (fun z : ι → ℂ => z k₀ ^ (l.1 : ℕ) * Complex.exp (∑ ν, φK (w ν) * z ν)) := by
        funext z; simp only [hwφ, ht_def]
      rw [hfun, hγ₀, map_mul, ← exp_factor_eq φK x y a ha t (fun j => (s j : ℕ))]
      simp only [hwφ, hqν]
    · have hBk : 1 ≤ (n : ℝ) * S₁ * H + k := by
        have : (1 : ℝ) ≤ n * S₁ * H := one_le_mul_of_one_le_of_one_le
          (one_le_mul_of_one_le_of_one_le hn hS₁) hH
        linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
      calc house (γ₀ * ∏ i, ∏ j, a i j ^ (t i * (s j : ℕ)))
          ≤ house γ₀ * house (∏ i, ∏ j, a i j ^ (t i * (s j : ℕ))) := house_mul_le _ _
        _ ≤ ((((d₁ : ℝ) + 1) * T₁ * H) ^ k * ((n : ℝ) * S₁ * H + k) ^ (l.1 : ℕ)) *
            H ^ (d₁ * n * T₁ * S₁) :=
            mul_le_mul hγ₀h (house_exp_factor_le a hH haH t ht _ fun j => (s j).2)
              (house_nonneg _) (by positivity)
        _ ≤ _ := by gcongr
    · have hsum : ∑ i, ∑ j, t i * (s j : ℕ) ≤ d₁ * n * T₁ * S₁ :=
        sum_ts_le t ht (fun j => (s j : ℕ)) fun j => (s j).2
      apply isIntegral_pow_mul_of_le (a := k + (l.1 : ℕ) + ∑ i, ∑ j, t i * (s j : ℕ)) (by omega)
      have e : (δ : K) ^ (k + (l.1 : ℕ) + ∑ i, ∑ j, t i * (s j : ℕ)) *
          (γ₀ * ∏ i, ∏ j, a i j ^ (t i * (s j : ℕ))) = ((δ : K) ^ (k + (l.1 : ℕ)) * γ₀) *
          ((δ : K) ^ (∑ i, ∑ j, t i * (s j : ℕ)) * ∏ i, ∏ j, a i j ^ (t i * (s j : ℕ))) := by
        rw [pow_add]; ring
      rw [e]
      exact hγ₀i.mul (isIntegral_exp_factor a hδa t _)
  choose γ hγeq hγh hγi using hterm
  /- The derivative of `F` is `φK (Σ p_λ γ_λ)`. -/
  refine ⟨∑ l, (p l : K) * γ l, ?_, ?_, ?_⟩
  · rw [iteratedFDeriv_lincomb_apply (fun l => (p l : ℂ)) _ (fun l => analytic_expMono k₀ _ _),
      map_sum]
    exact Finset.sum_congr rfl fun l _ => by rw [hγeq l, map_mul, map_intCast]
  · calc house (∑ l, (p l : K) * γ l) ≤ ∑ l, house ((p l : K) * γ l) := house_sum_le_sum_house _ _
      _ ≤ ∑ l, |(p l : ℝ)| * house (γ l) := Finset.sum_le_sum fun l _ => house_intCast_mul_le _ _
      _ ≤ ∑ _l : Fin (T₀ + 1) × (Fin d₁ → Fin (T₁ + 1)), X * ((((d₁ : ℝ) + 1) * T₁ * H) ^ k *
            ((n : ℝ) * S₁ * H + k) ^ T₀ * H ^ (d₁ * n * T₁ * S₁)) := Finset.sum_le_sum fun l _ =>
          mul_le_mul (hp l) (hγh l) (house_nonneg _) (le_trans (abs_nonneg _) (hp l))
      _ = _ := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
          simp only [Fintype.card_prod, Fintype.card_fin, Fintype.card_fun]
          push_cast; ring
  · have : (δ : K) ^ (k + T₀ + d₁ * n * T₁ * S₁) * ∑ l, (p l : K) * γ l =
        ∑ l, (p l : K) * ((δ : K) ^ (k + T₀ + d₁ * n * T₁ * S₁) * γ l) := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun l _ => by ring
    rw [this]
    exact IsIntegral.sum _ fun l _ => (isIntegral_intCast (p l)).mul (hγi l)
