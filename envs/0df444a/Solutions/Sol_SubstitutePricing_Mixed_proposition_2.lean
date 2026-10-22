-- Prove2me | solution 1 for SubstitutePricing.Mixed.proposition_2
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-21T18:49:51.270484+00:00
-- url     : https://prove2.me/submissions/4b204835-54bf-4059-9c6c-dbf9513551db

import Mathlib
import Definitions.Def_SubstitutePricing_Mixed_Model

set_option autoImplicit false

namespace SPM47
open SubstitutePricing.Mixed

variable (M : Model)

lemma den_pos (x : Fin M.n → ℕ) (r : Fin M.n → ℝ) : 0 < M.den x r := by
  unfold Model.den
  have h1 := Real.exp_pos (M.u0 / M.μ)
  have h2 : 0 ≤ ∑ j ∈ M.S x, Real.exp ((M.a j - r j) / M.μ) :=
    Finset.sum_nonneg (fun j _ => (Real.exp_pos _).le)
  linarith

lemma P_of_mem {x : Fin M.n → ℕ} (r : Fin M.n → ℝ) {i : Fin M.n} (hi : i ∈ M.S x) :
    M.P x r i = Real.exp ((M.a i - r i) / M.μ) / M.den x r := by
  simp [Model.P, hi]

lemma P_nonneg (x : Fin M.n → ℕ) (r : Fin M.n → ℝ) (i : Fin M.n) : 0 ≤ M.P x r i := by
  unfold Model.P
  split_ifs
  · exact div_nonneg (Real.exp_pos _).le (den_pos M x r).le
  · exact le_refl 0

lemma P0_nonneg (x : Fin M.n → ℕ) (r : Fin M.n → ℝ) : 0 ≤ M.P0 x r :=
  div_nonneg (Real.exp_pos _).le (den_pos M x r).le

lemma sumP_add_P0 (x : Fin M.n → ℕ) (r : Fin M.n → ℝ) :
    (∑ i ∈ M.S x, M.P x r i) + M.P0 x r = 1 := by
  have hd := den_pos M x r
  rw [Finset.sum_congr rfl (fun i hi => P_of_mem M r hi), ← Finset.sum_div, Model.P0,
    ← add_div, div_eq_one_iff_eq hd.ne']
  rfl

lemma obj_eq (V : (Fin M.n → ℕ) → ℝ) (x : Fin M.n → ℕ) (r : Fin M.n → ℝ) :
    M.obj V x r = V x + M.lam * ∑ i ∈ M.S x, M.P x r i * (r i - (V x - V (M.sell x i))) := by
  have h := sumP_add_P0 M x r
  unfold Model.obj
  have e1 : ∑ i ∈ M.S x, M.P x r i * (r i - (V x - V (M.sell x i))) =
      (∑ i ∈ M.S x, r i * M.P x r i) + (∑ i ∈ M.S x, M.P x r i * V (M.sell x i))
        - (∑ i ∈ M.S x, M.P x r i) * V x := by
    rw [Finset.sum_mul, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun i _ => by ring)
  rw [e1]
  have h0 : M.P0 x r = 1 - ∑ i ∈ M.S x, M.P x r i := by linarith
  rw [h0]; ring

lemma sum_S_split (x : Fin M.n → ℕ) (f : Fin M.n → ℝ) :
    ∑ k ∈ M.S x, f k = (∑ k ∈ M.S1 x, f k) + ∑ k ∈ M.S2 x, f k := by
  rw [Model.S1, Model.S2]
  exact (Finset.sum_inter_add_sum_sdiff (M.S x) M.dyn f).symm

lemma mem_S1 {x : Fin M.n → ℕ} {i : Fin M.n} (h : i ∈ M.S1 x) : i ∈ M.S x ∧ i ∈ M.dyn := by
  rw [Model.S1, Finset.mem_inter] at h; exact h

lemma mem_S2 {x : Fin M.n → ℕ} {j : Fin M.n} (h : j ∈ M.S2 x) : j ∈ M.S x ∧ j ∉ M.dyn := by
  rw [Model.S2, Finset.mem_sdiff] at h; exact h

/-- total weight of the fixed options (no-purchase included) -/
noncomputable def W (x : Fin M.n → ℕ) : ℝ :=
  Real.exp (M.u0 / M.μ) + ∑ j ∈ M.S2 x, Real.exp (M.uf j / M.μ)

/-- weighted margins of the fixed variates -/
noncomputable def SV (x : Fin M.n → ℕ) (δ : Fin M.n → ℝ) : ℝ :=
  ∑ j ∈ M.S2 x, Real.exp (M.uf j / M.μ) * (M.rfix j - δ j)

/-- left side of (15) for general marginal values -/
noncomputable def Lg (x : Fin M.n → ℕ) (δ : Fin M.n → ℝ) (m : ℝ) : ℝ :=
  (m / M.μ - 1) * Real.exp ((m + M.u0) / M.μ) +
  ∑ j ∈ M.S2 x, ((m - (M.rfix j - δ j)) / M.μ - 1) * Real.exp ((m + M.uf j) / M.μ)

/-- right side of (15) for general marginal values -/
noncomputable def Rg (x : Fin M.n → ℕ) (δ : Fin M.n → ℝ) : ℝ :=
  ∑ i ∈ M.S1 x, Real.exp ((M.a i - δ i) / M.μ)

lemma W_pos (x : Fin M.n → ℕ) : 0 < W M x := by
  unfold W
  have h1 := Real.exp_pos (M.u0 / M.μ)
  have h2 : 0 ≤ ∑ j ∈ M.S2 x, Real.exp (M.uf j / M.μ) :=
    Finset.sum_nonneg (fun j _ => (Real.exp_pos _).le)
  linarith

lemma Rg_nonneg (x : Fin M.n → ℕ) (δ : Fin M.n → ℝ) : 0 ≤ Rg M x δ :=
  Finset.sum_nonneg (fun _ _ => (Real.exp_pos _).le)

lemma L_factor (hμ : 0 < M.μ) (x : Fin M.n → ℕ) (δ : Fin M.n → ℝ) (m : ℝ) :
    Lg M x δ m = Real.exp (m / M.μ) * (W M x * (m - M.μ) - SV M x δ) / M.μ := by
  have e : ∀ u : ℝ, Real.exp ((m + u) / M.μ) = Real.exp (m / M.μ) * Real.exp (u / M.μ) :=
    fun u => by rw [← Real.exp_add, add_div]
  have hs : ∑ j ∈ M.S2 x, ((m - (M.rfix j - δ j)) / M.μ - 1) * Real.exp ((m + M.uf j) / M.μ)
      = ∑ j ∈ M.S2 x, Real.exp (m / M.μ) / M.μ *
          (Real.exp (M.uf j / M.μ) * (m - M.μ) - Real.exp (M.uf j / M.μ) * (M.rfix j - δ j)) :=
    Finset.sum_congr rfl (fun j _ => by rw [e]; field_simp; ring)
  unfold Lg
  rw [hs, ← Finset.mul_sum, Finset.sum_sub_distrib, ← Finset.sum_mul, e, W, SV]
  field_simp
  ring

lemma root_ell (hμ : 0 < M.μ) {x : Fin M.n → ℕ} {δ : Fin M.n → ℝ} {m σ : ℝ}
    (hσ : 0 ≤ σ) (h : Lg M x δ m = σ) : 0 ≤ W M x * (m - M.μ) - SV M x δ := by
  rw [L_factor M hμ] at h
  by_contra hc
  push Not at hc
  have : Real.exp (m / M.μ) * (W M x * (m - M.μ) - SV M x δ) / M.μ < 0 :=
    div_neg_of_neg_of_pos (mul_neg_of_pos_of_neg (Real.exp_pos _) hc) hμ
  linarith

lemma root_exists (hμ : 0 < M.μ) (x : Fin M.n → ℕ) (δ : Fin M.n → ℝ) {σ : ℝ} (hσ : 0 ≤ σ) :
    ∃ m, Lg M x δ m = σ := by
  have hW := W_pos M x
  set W0 := W M x with hW0
  set S0 := SV M x δ with hS0
  set m0 := M.μ + S0 / W0 with hm0
  set c := M.μ * σ * Real.exp (-(m0 / M.μ)) / W0 with hc
  have hc0 : 0 ≤ c := div_nonneg (mul_nonneg (mul_nonneg hμ.le hσ) (Real.exp_pos _).le) hW.le
  have hK : m0 ≤ m0 + c := by linarith
  set g : ℝ → ℝ := fun m => Real.exp (m / M.μ) * (W0 * (m - M.μ) - S0) / M.μ with hg
  have hLg : ∀ m, Lg M x δ m = g m := fun m => L_factor M hμ x δ m
  have hcont : ContinuousOn g (Set.Icc m0 (m0 + c)) := by
    rw [hg]; exact (by fun_prop : Continuous _).continuousOn
  have h0 : g m0 = 0 := by
    simp only [hg, hm0]
    have : W0 * (M.μ + S0 / W0 - M.μ) - S0 = 0 := by field_simp; ring
    rw [this]; simp
  have h1 : σ ≤ g (m0 + c) := by
    simp only [hg]
    have e : W0 * (m0 + c - M.μ) - S0 = M.μ * σ * Real.exp (-(m0 / M.μ)) := by
      rw [hc, hm0]; field_simp; ring
    rw [e]
    have hle : Real.exp (m0 / M.μ) ≤ Real.exp ((m0 + c) / M.μ) := by
      apply Real.exp_le_exp.mpr
      rw [div_le_div_iff_of_pos_right hμ]; linarith
    have hinv : Real.exp (m0 / M.μ) * Real.exp (-(m0 / M.μ)) = 1 := by
      rw [← Real.exp_add]; simp
    have e2 : Real.exp ((m0 + c) / M.μ) * (M.μ * σ * Real.exp (-(m0 / M.μ))) / M.μ
        = σ * Real.exp (-(m0 / M.μ)) * Real.exp ((m0 + c) / M.μ) := by
      field_simp
    rw [e2]
    have hp : 0 ≤ σ * Real.exp (-(m0 / M.μ)) := mul_nonneg hσ (Real.exp_pos _).le
    calc σ = σ * Real.exp (-(m0 / M.μ)) * Real.exp (m0 / M.μ) := by
          rw [mul_assoc, mul_comm (Real.exp _) (Real.exp _), hinv, mul_one]
      _ ≤ _ := mul_le_mul_of_nonneg_left hle hp
  obtain ⟨m, _, hm⟩ := intermediate_value_Icc hK hcont ⟨by rw [h0]; exact hσ, h1⟩
  exact ⟨m, by rw [hLg]; exact hm⟩

lemma root_unique (hμ : 0 < M.μ) {x : Fin M.n → ℕ} {δ : Fin M.n → ℝ} {σ m1 m2 : ℝ}
    (hσ : 0 ≤ σ) (h1 : Lg M x δ m1 = σ) (h2 : Lg M x δ m2 = σ) : m1 = m2 := by
  have a1 := root_ell M hμ hσ h1
  have a2 := root_ell M hμ hσ h2
  have hW := W_pos M x
  have mono : ∀ a b, 0 ≤ W M x * (a - M.μ) - SV M x δ → a < b → Lg M x δ a < Lg M x δ b := by
    intro a b ha hab
    rw [L_factor M hμ, L_factor M hμ]
    apply div_lt_div_of_pos_right _ hμ
    have e2 : W M x * (a - M.μ) - SV M x δ < W M x * (b - M.μ) - SV M x δ := by nlinarith
    have e3 : Real.exp (a / M.μ) < Real.exp (b / M.μ) :=
      Real.exp_lt_exp.mpr (div_lt_div_of_pos_right hab hμ)
    have q1 := mul_le_mul_of_nonneg_right e3.le ha
    have q2 := mul_lt_mul_of_pos_left e2 (Real.exp_pos (b / M.μ))
    linarith
  rcases lt_trichotomy m1 m2 with h | h | h
  · have := mono _ _ a1 h; linarith
  · exact h
  · have := mono _ _ a2 h; linarith

lemma root_ge_mu (hμ : 0 < M.μ) {x : Fin M.n → ℕ} {δ : Fin M.n → ℝ} {m σ : ℝ}
    (hσ : 0 ≤ σ) (hSV : 0 ≤ SV M x δ) (h : Lg M x δ m = σ) : M.μ ≤ m := by
  have a := root_ell M hμ hσ h
  have hW := W_pos M x
  by_contra hc
  push Not at hc
  have : W M x * (m - M.μ) < 0 := mul_neg_of_pos_of_neg hW (by linarith)
  linarith

lemma sum_shift (hμ : 0 < M.μ) (x : Fin M.n → ℕ) (δ : Fin M.n → ℝ) (m : ℝ)
    (hm : Lg M x δ m = Rg M x δ) :
    M.μ * ∑ i ∈ M.S1 x, Real.exp ((M.a i - δ i - m) / M.μ)
      = W M x * (m - M.μ) - SV M x δ := by
  have e : ∀ i, Real.exp ((M.a i - δ i - m) / M.μ)
      = Real.exp ((M.a i - δ i) / M.μ) * Real.exp (-(m / M.μ)) := by
    intro i; rw [← Real.exp_add]; congr 1; field_simp; ring
  simp_rw [e]
  rw [← Finset.sum_mul]
  change M.μ * (Rg M x δ * Real.exp (-(m / M.μ))) = _
  rw [← hm, L_factor M hμ]
  have hinv : Real.exp (m / M.μ) * Real.exp (-(m / M.μ)) = 1 := by
    rw [← Real.exp_add]; simp
  calc M.μ * (Real.exp (m / M.μ) * (W M x * (m - M.μ) - SV M x δ) / M.μ
        * Real.exp (-(m / M.μ)))
      = (W M x * (m - M.μ) - SV M x δ) * (Real.exp (m / M.μ) * Real.exp (-(m / M.μ))) := by
        field_simp
    _ = W M x * (m - M.μ) - SV M x δ := by rw [hinv, mul_one]

lemma ratio (x : Fin M.n → ℕ) (δ : Fin M.n → ℝ) (q : Fin M.n → ℝ)
    (hq : ∀ j ∈ M.S2 x, q j = M.rfix j) :
    ∑ k ∈ M.S x, M.P x q k * (q k - δ k)
      = ((∑ i ∈ M.S1 x, Real.exp ((M.a i - q i) / M.μ) * (q i - δ i)) + SV M x δ)
        / ((∑ i ∈ M.S1 x, Real.exp ((M.a i - q i) / M.μ)) + W M x) := by
  have hS2e : ∀ j ∈ M.S2 x, Real.exp ((M.a j - q j) / M.μ) = Real.exp (M.uf j / M.μ) := by
    intro j hj; rw [hq j hj]; rfl
  have hd : M.den x q = (∑ i ∈ M.S1 x, Real.exp ((M.a i - q i) / M.μ)) + W M x := by
    unfold Model.den W
    rw [sum_S_split M x, Finset.sum_congr rfl hS2e]
    ring
  have hn : ∑ k ∈ M.S x, Real.exp ((M.a k - q k) / M.μ) * (q k - δ k)
      = (∑ i ∈ M.S1 x, Real.exp ((M.a i - q i) / M.μ) * (q i - δ i)) + SV M x δ := by
    rw [sum_S_split M x]
    congr 1
    unfold SV
    exact Finset.sum_congr rfl (fun j hj => by rw [hS2e j hj, hq j hj])
  calc ∑ k ∈ M.S x, M.P x q k * (q k - δ k)
      = (∑ k ∈ M.S x, Real.exp ((M.a k - q k) / M.μ) * (q k - δ k)) / M.den x q := by
        rw [Finset.sum_div]
        exact Finset.sum_congr rfl (fun k hk => by rw [P_of_mem M q hk]; ring)
    _ = _ := by rw [hn, hd]

lemma key_le (hμ : 0 < M.μ) (x : Fin M.n → ℕ) (δ : Fin M.n → ℝ) (m : ℝ)
    (hm : Lg M x δ m = Rg M x δ) (q : Fin M.n → ℝ) (hq : ∀ j ∈ M.S2 x, q j = M.rfix j) :
    ∑ k ∈ M.S x, M.P x q k * (q k - δ k) ≤ m - M.μ := by
  have hterm : ∀ i, Real.exp ((M.a i - q i) / M.μ) * (q i - δ i - m + M.μ)
      ≤ M.μ * Real.exp ((M.a i - δ i - m) / M.μ) := by
    intro i
    have h1 : Real.exp ((M.a i - q i) / M.μ) = Real.exp ((M.a i - δ i - m) / M.μ)
        * Real.exp (-((q i - δ i - m) / M.μ)) := by
      rw [← Real.exp_add]; congr 1; field_simp; ring
    have h2 : q i - δ i - m + M.μ = M.μ * ((q i - δ i - m) / M.μ + 1) := by
      field_simp
    have h3 : ((q i - δ i - m) / M.μ + 1) * Real.exp (-((q i - δ i - m) / M.μ)) ≤ 1 := by
      have ha := Real.add_one_le_exp ((q i - δ i - m) / M.μ)
      have hez : Real.exp ((q i - δ i - m) / M.μ) * Real.exp (-((q i - δ i - m) / M.μ)) = 1 := by
        rw [← Real.exp_add]; simp
      have hp := Real.exp_pos (-((q i - δ i - m) / M.μ))
      nlinarith
    rw [h1, h2]
    have hE := Real.exp_pos ((M.a i - δ i - m) / M.μ)
    calc Real.exp ((M.a i - δ i - m) / M.μ) * Real.exp (-((q i - δ i - m) / M.μ))
          * (M.μ * ((q i - δ i - m) / M.μ + 1))
        = M.μ * Real.exp ((M.a i - δ i - m) / M.μ)
          * (((q i - δ i - m) / M.μ + 1) * Real.exp (-((q i - δ i - m) / M.μ))) := by ring
      _ ≤ M.μ * Real.exp ((M.a i - δ i - m) / M.μ) * 1 :=
          mul_le_mul_of_nonneg_left h3 (mul_pos hμ hE).le
      _ = M.μ * Real.exp ((M.a i - δ i - m) / M.μ) := by ring
  have hsum := sum_shift M hμ x δ m hm
  have hW := W_pos M x
  rw [ratio M x δ q hq]
  have hT : 0 ≤ ∑ i ∈ M.S1 x, Real.exp ((M.a i - q i) / M.μ) :=
    Finset.sum_nonneg (fun _ _ => (Real.exp_pos _).le)
  rw [div_le_iff₀ (by linarith)]
  have e : ∑ i ∈ M.S1 x, Real.exp ((M.a i - q i) / M.μ) * (q i - δ i) =
      ∑ i ∈ M.S1 x, Real.exp ((M.a i - q i) / M.μ) * (q i - δ i - m + M.μ)
        + (m - M.μ) * ∑ i ∈ M.S1 x, Real.exp ((M.a i - q i) / M.μ) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun i _ => by ring)
  have hs := Finset.sum_le_sum (fun i (_ : i ∈ M.S1 x) => hterm i)
  rw [← Finset.mul_sum, hsum] at hs
  rw [e]
  nlinarith

lemma key_eq (hμ : 0 < M.μ) (x : Fin M.n → ℕ) (δ : Fin M.n → ℝ) (m : ℝ)
    (hm : Lg M x δ m = Rg M x δ) (q : Fin M.n → ℝ) (hq : ∀ j ∈ M.S2 x, q j = M.rfix j)
    (hq1 : ∀ i ∈ M.S1 x, q i = δ i + m) :
    ∑ k ∈ M.S x, M.P x q k * (q k - δ k) = m - M.μ := by
  have hsum := sum_shift M hμ x δ m hm
  have hW := W_pos M x
  rw [ratio M x δ q hq]
  have hE : ∀ i ∈ M.S1 x, Real.exp ((M.a i - q i) / M.μ) = Real.exp ((M.a i - δ i - m) / M.μ) := by
    intro i hi; rw [hq1 i hi]; congr 1; ring
  have hN : ∑ i ∈ M.S1 x, Real.exp ((M.a i - q i) / M.μ) * (q i - δ i)
      = (∑ i ∈ M.S1 x, Real.exp ((M.a i - δ i - m) / M.μ)) * m := by
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl (fun i hi => by rw [hE i hi, hq1 i hi]; ring)
  rw [hN, Finset.sum_congr rfl hE]
  have hT : 0 ≤ ∑ i ∈ M.S1 x, Real.exp ((M.a i - δ i - m) / M.μ) :=
    Finset.sum_nonneg (fun _ _ => (Real.exp_pos _).le)
  rw [div_eq_iff (by linarith)]
  linear_combination hsum

lemma sell_comm (x : Fin M.n → ℕ) (i j : Fin M.n) :
    M.sell (M.sell x i) j = M.sell (M.sell x j) i := by
  by_cases hij : i = j
  · subst hij; rfl
  · funext k
    by_cases hki : k = i
    · subst hki
      simp [Model.sell, Function.update_apply, hij, Ne.symm hij]
    · by_cases hkj : k = j
      · subst hkj
        simp [Model.sell, Function.update_apply, hki, Ne.symm hki, hij, Ne.symm hij]
      · simp [Model.sell, Function.update_apply, hki, hkj]

lemma mix_dyn {r : Fin M.n → ℝ} {i : Fin M.n} (hi : i ∈ M.dyn) : M.mix r i = r i := by
  simp [Model.mix, hi]

lemma mix_fix {r : Fin M.n → ℝ} {j : Fin M.n} (hj : j ∉ M.dyn) : M.mix r j = M.rfix j := by
  simp [Model.mix, hj]

lemma mix_update (r : Fin M.n → ℝ) {i : Fin M.n} (hi : i ∈ M.dyn) (R : ℝ) :
    Function.update (M.mix r) i R = M.mix (Function.update r i R) := by
  funext k
  by_cases hk : k = i
  · subst hk; simp [Model.mix, hi]
  · simp [Model.mix, Function.update_apply, hk]

lemma real_ineq {lam w0 ε T A1 A2 A2' Vx Vy R : ℝ} (hl0 : 0 < lam) (hl1 : lam ≤ 1)
    (hw : 0 < w0) (hε : 0 < ε) (hT : 0 ≤ T) (hA : A2 ≤ A2') (hV : Vy ≤ Vx)
    (hR : A1 + A2 + w0 * Vy ≤ (R + Vy) * (T + w0)) :
    lam * (A1 / (T + w0)) + lam * (A2 / (T + w0)) + (lam * (w0 / (T + w0)) + 1 - lam) * Vy ≤
    lam * (R * (ε / (ε + T + w0)) + A1 / (ε + T + w0))
      + lam * (ε / (ε + T + w0) * Vy + A2' / (ε + T + w0))
      + (lam * (w0 / (ε + T + w0)) + 1 - lam) * Vx := by
  have hDy : 0 < T + w0 := by linarith
  have hDx : 0 < ε + T + w0 := by linarith
  have c1 : 0 ≤ lam * (w0 / (ε + T + w0)) + 1 - lam := by
    have : 0 ≤ lam * (w0 / (ε + T + w0)) := mul_nonneg hl0.le (div_nonneg hw.le hDx.le)
    linarith
  have s1 := mul_le_mul_of_nonneg_left hV c1
  have key : (A1 + A2 + w0 * Vy) / (T + w0)
      ≤ (A1 + A2 + w0 * Vy + ε * (R + Vy)) / (ε + T + w0) := by
    rw [div_le_div_iff₀ hDy hDx]
    nlinarith [mul_le_mul_of_nonneg_left hR hε.le]
  have e1 : lam * (A1 / (T + w0)) + lam * (A2 / (T + w0)) + (lam * (w0 / (T + w0)) + 1 - lam) * Vy
      = lam * ((A1 + A2 + w0 * Vy) / (T + w0)) + (1 - lam) * Vy := by
    field_simp; ring
  have e2 : lam * (R * (ε / (ε + T + w0)) + A1 / (ε + T + w0))
      + lam * (ε / (ε + T + w0) * Vy + A2 / (ε + T + w0))
      + (lam * (w0 / (ε + T + w0)) + 1 - lam) * Vy
      = lam * ((A1 + A2 + w0 * Vy + ε * (R + Vy)) / (ε + T + w0)) + (1 - lam) * Vy := by
    field_simp; ring
  have s3 := mul_le_mul_of_nonneg_left key hl0.le
  have s4 : lam * (ε / (ε + T + w0) * Vy + A2 / (ε + T + w0))
      ≤ lam * (ε / (ε + T + w0) * Vy + A2' / (ε + T + w0)) := by
    have : A2 / (ε + T + w0) ≤ A2' / (ε + T + w0) := div_le_div_of_nonneg_right hA hDx.le
    nlinarith
  linarith

/-- an extra unit of a dynamically priced variate never lowers the value -/
lemma mono_step (hM : M.Assumptions) (V : (Fin M.n → ℕ) → ℝ) (i : Fin M.n)
    (hV : ∀ z, i ∈ M.S z → V (M.sell z i) ≤ V z) (x : Fin M.n → ℕ)
    (hi : i ∈ M.S x) (r : Fin M.n → ℝ) (hri : 0 ≤ r i) :
    ∃ R : ℝ, 0 ≤ R ∧ M.obj V (M.sell x i) r ≤ M.obj V x (Function.update r i R) := by
  have hμ := hM.mu_pos
  have hl0 := hM.lam_pos
  have hl1 := hM.lam_le_one
  have hxi : 0 < x i := by simpa [Model.S] using hi
  have hmemS : ∀ (z : Fin M.n → ℕ) k, k ∈ M.S z ↔ 0 < z k := fun z k => by simp [Model.S]
  have hsell_i : ∀ j, j ≠ i → M.sell x j i = x i := fun j hj => by
    simp [Model.sell, Function.update_apply, Ne.symm hj]
  have hcont : ∀ j, j ≠ i → V (M.sell (M.sell x i) j) ≤ V (M.sell x j) := by
    intro j hj
    rw [sell_comm M x i j]
    exact hV _ ((hmemS _ _).2 (by rw [hsell_i j hj]; exact hxi))
  rcases Nat.lt_or_ge 1 (x i) with h2 | h1
  · have hS : M.S (M.sell x i) = M.S x := by
      ext k
      rw [hmemS, hmemS]
      by_cases hk : k = i
      · subst hk; simp [Model.sell]; omega
      · simp [Model.sell, Function.update_apply, hk]
    have hden : M.den (M.sell x i) r = M.den x r := by simp only [Model.den, hS]
    have hP : ∀ j, M.P (M.sell x i) r j = M.P x r j := by
      intro j; simp only [Model.P, hden, hS]
    have hP0 : M.P0 (M.sell x i) r = M.P0 x r := by simp only [Model.P0, hden]
    refine ⟨r i, hri, ?_⟩
    rw [Function.update_eq_self]
    unfold Model.obj
    rw [hS, hP0]
    simp only [hP]
    have c1 : 0 ≤ M.lam * M.P0 x r + 1 - M.lam := by
      have := mul_nonneg hl0.le (P0_nonneg M x r); linarith
    have t1 : ∑ j ∈ M.S x, M.P x r j * V (M.sell (M.sell x i) j)
        ≤ ∑ j ∈ M.S x, M.P x r j * V (M.sell x j) := by
      apply Finset.sum_le_sum
      intro j hj
      apply mul_le_mul_of_nonneg_left _ (P_nonneg M x r j)
      by_cases hji : j = i
      · subst hji
        exact hV (M.sell x j) (by rw [hS]; exact hj)
      · exact hcont j hji
    have t2 := mul_le_mul_of_nonneg_left (hV x hi) c1
    have t3 := mul_le_mul_of_nonneg_left t1 hl0.le
    linarith
  · have hx1 : x i = 1 := by omega
    have hiy : i ∉ M.S (M.sell x i) := by
      rw [hmemS]; simp [Model.sell, hx1]
    have hSx : M.S x = insert i (M.S (M.sell x i)) := by
      ext k
      rw [Finset.mem_insert, hmemS, hmemS]
      by_cases hk : k = i
      · subst hk; simp [hxi]
      · simp [Model.sell, Function.update_apply, hk]
    have hne : ∀ j ∈ M.S (M.sell x i), j ≠ i := fun j hj h => hiy (h ▸ hj)
    have hjx : ∀ j ∈ M.S (M.sell x i), j ∈ M.S x := fun j hj => by
      rw [hSx]; exact Finset.mem_insert_of_mem hj
    set y := M.sell x i with hy
    set w0 := Real.exp (M.u0 / M.μ) with hw0
    set T := ∑ j ∈ M.S y, Real.exp ((M.a j - r j) / M.μ) with hT
    set A1 := ∑ j ∈ M.S y, r j * Real.exp ((M.a j - r j) / M.μ) with hA1
    set A2 := ∑ j ∈ M.S y, Real.exp ((M.a j - r j) / M.μ) * V (M.sell y j) with hA2
    set A2' := ∑ j ∈ M.S y, Real.exp ((M.a j - r j) / M.μ) * V (M.sell x j) with hA2'
    set R := max 0 ((A1 + A2 + w0 * V y) / (T + w0) - V y) with hR
    set r' := Function.update r i R with hr'
    set ε := Real.exp ((M.a i - R) / M.μ) with hε
    have hr'i : r' i = R := by simp [r']
    have hr'j : ∀ j ∈ M.S y, r' j = r j := fun j hj => by
      simp [r', Function.update_apply, hne j hj]
    have hT0 : 0 ≤ T := Finset.sum_nonneg (fun _ _ => (Real.exp_pos _).le)
    have hwpos : 0 < w0 := Real.exp_pos _
    have hDy : M.den y r = T + w0 := rfl
    have hDx : M.den x r' = ε + T + w0 := by
      show (∑ j ∈ M.S x, Real.exp ((M.a j - r' j) / M.μ)) + Real.exp (M.u0 / M.μ) = _
      rw [hSx, Finset.sum_insert hiy, hr'i,
        Finset.sum_congr rfl (fun j hj => by rw [hr'j j hj])]
    refine ⟨R, le_max_left _ _, ?_⟩
    have hobjy : M.obj V y r = M.lam * (A1 / (T + w0)) + M.lam * (A2 / (T + w0))
        + (M.lam * (w0 / (T + w0)) + 1 - M.lam) * V y := by
      unfold Model.obj Model.P0
      rw [hDy]
      have u1 : ∑ j ∈ M.S y, r j * M.P y r j = A1 / (T + w0) := by
        rw [hA1, Finset.sum_div]
        exact Finset.sum_congr rfl (fun j hj => by rw [P_of_mem M r hj, hDy]; ring)
      have u2 : ∑ j ∈ M.S y, M.P y r j * V (M.sell y j) = A2 / (T + w0) := by
        rw [hA2, Finset.sum_div]
        exact Finset.sum_congr rfl (fun j hj => by rw [P_of_mem M r hj, hDy]; ring)
      rw [u1, u2]
    have hobjx : M.obj V x r' = M.lam * (R * (ε / (ε + T + w0)) + A1 / (ε + T + w0))
        + M.lam * (ε / (ε + T + w0) * V y + A2' / (ε + T + w0))
        + (M.lam * (w0 / (ε + T + w0)) + 1 - M.lam) * V x := by
      unfold Model.obj Model.P0
      rw [hDx]
      have hPi : M.P x r' i = ε / (ε + T + w0) := by
        rw [P_of_mem M r' hi, hDx, hr'i]
      have u1 : ∑ j ∈ M.S y, r' j * M.P x r' j = A1 / (ε + T + w0) := by
        rw [hA1, Finset.sum_div]
        exact Finset.sum_congr rfl (fun j hj => by
          rw [P_of_mem M r' (hjx j hj), hDx, hr'j j hj]; ring)
      have u2 : ∑ j ∈ M.S y, M.P x r' j * V (M.sell x j) = A2' / (ε + T + w0) := by
        rw [hA2', Finset.sum_div]
        exact Finset.sum_congr rfl (fun j hj => by
          rw [P_of_mem M r' (hjx j hj), hDx, hr'j j hj]; ring)
      rw [hSx, Finset.sum_insert hiy, Finset.sum_insert hiy, hPi, hr'i, u1, u2]
    rw [hobjy, hobjx]
    have hAA : A2 ≤ A2' := by
      apply Finset.sum_le_sum
      intro j hj
      exact mul_le_mul_of_nonneg_left (hcont j (hne j hj)) (Real.exp_pos _).le
    apply real_ineq hl0 hl1 hwpos (Real.exp_pos _) hT0 hAA (hV x hi)
    have hmx := le_max_right 0 ((A1 + A2 + w0 * V y) / (T + w0) - V y)
    rw [← hR] at hmx
    have : (A1 + A2 + w0 * V y) / (T + w0) ≤ R + V y := by linarith
    exact (div_le_iff₀ (by linarith)).mp this

lemma fix_ineq {lam w0 ε T A1 A2 A2' Vx Vy ρ : ℝ} (hl0 : 0 < lam) (hl1 : lam ≤ 1)
    (hw : 0 < w0) (hε : 0 < ε) (hT : 0 ≤ T) (hA : A2' ≤ A2 + ρ * T) (hV : Vx ≤ Vy + ρ) :
    lam * (ρ * (ε / (ε + T + w0)) + A1 / (ε + T + w0))
      + lam * (ε / (ε + T + w0) * Vy + A2' / (ε + T + w0))
      + (lam * (w0 / (ε + T + w0)) + 1 - lam) * Vx
    ≤ max (lam * (A1 / (T + w0)) + lam * (A2 / (T + w0))
        + (lam * (w0 / (T + w0)) + 1 - lam) * Vy) Vy + ρ := by
  have hDy : 0 < T + w0 := by linarith
  have hDx : 0 < ε + T + w0 := by linarith
  have c1 : 0 ≤ lam * (w0 / (ε + T + w0)) + 1 - lam := by
    have : 0 ≤ lam * (w0 / (ε + T + w0)) := mul_nonneg hl0.le (div_nonneg hw.le hDx.le)
    linarith
  have s1 := mul_le_mul_of_nonneg_left hV c1
  have s2 : lam * (ε / (ε + T + w0) * Vy + A2' / (ε + T + w0))
      ≤ lam * (ε / (ε + T + w0) * Vy + (A2 + ρ * T) / (ε + T + w0)) :=
    mul_le_mul_of_nonneg_left (add_le_add_right (div_le_div_of_nonneg_right hA hDx.le) _) hl0.le
  have eU : lam * (ρ * (ε / (ε + T + w0)) + A1 / (ε + T + w0))
      + lam * (ε / (ε + T + w0) * Vy + (A2 + ρ * T) / (ε + T + w0))
      + (lam * (w0 / (ε + T + w0)) + 1 - lam) * (Vy + ρ)
      = ρ + Vy + lam * ((A1 + A2 - T * Vy) / (ε + T + w0)) := by
    field_simp; ring
  have ey : lam * (A1 / (T + w0)) + lam * (A2 / (T + w0)) + (lam * (w0 / (T + w0)) + 1 - lam) * Vy
      = Vy + lam * ((A1 + A2 - T * Vy) / (T + w0)) := by
    field_simp; ring
  rw [ey]
  have hL : lam * (ρ * (ε / (ε + T + w0)) + A1 / (ε + T + w0))
      + lam * (ε / (ε + T + w0) * Vy + A2' / (ε + T + w0))
      + (lam * (w0 / (ε + T + w0)) + 1 - lam) * Vx
      ≤ ρ + Vy + lam * ((A1 + A2 - T * Vy) / (ε + T + w0)) := by
    rw [← eU]; linarith
  by_cases hC : 0 ≤ A1 + A2 - T * Vy
  · have hq : (A1 + A2 - T * Vy) / (ε + T + w0) ≤ (A1 + A2 - T * Vy) / (T + w0) :=
      div_le_div_of_nonneg_left hC hDy (by linarith)
    have := mul_le_mul_of_nonneg_left hq hl0.le
    have hm := le_max_left (Vy + lam * ((A1 + A2 - T * Vy) / (T + w0))) Vy
    linarith
  · push Not at hC
    have hq : (A1 + A2 - T * Vy) / (ε + T + w0) ≤ 0 := (div_neg_of_neg_of_pos hC hDx).le
    have := mul_nonpos_of_nonneg_of_nonpos hl0.le hq
    have hm := le_max_right (Vy + lam * ((A1 + A2 - T * Vy) / (T + w0))) Vy
    linarith

/-- an extra unit of a fixed-price variate is worth at most its price -/
lemma fix_step (hM : M.Assumptions) (V : (Fin M.n → ℕ) → ℝ) (j : Fin M.n)
    (hV : ∀ z, j ∈ M.S z → V z - V (M.sell z j) ≤ M.rfix j) (x : Fin M.n → ℕ)
    (hj : j ∈ M.S x) (q : Fin M.n → ℝ) (hqj : q j = M.rfix j) :
    M.obj V x q ≤ max (M.obj V (M.sell x j) q) (V (M.sell x j)) + M.rfix j := by
  have hμ := hM.mu_pos
  have hl0 := hM.lam_pos
  have hl1 := hM.lam_le_one
  have hxj : 0 < x j := by simpa [Model.S] using hj
  have hmemS : ∀ (z : Fin M.n → ℕ) k, k ∈ M.S z ↔ 0 < z k := fun z k => by simp [Model.S]
  have hsell_j : ∀ k, k ≠ j → M.sell x k j = x j := fun k hk => by
    simp [Model.sell, Function.update_apply, Ne.symm hk]
  have hcont : ∀ k, k ≠ j → V (M.sell x k) ≤ V (M.sell (M.sell x j) k) + M.rfix j := by
    intro k hk
    rw [sell_comm M x j k]
    have := hV (M.sell x k) ((hmemS _ _).2 (by rw [hsell_j k hk]; exact hxj))
    linarith
  have hVx : V x ≤ V (M.sell x j) + M.rfix j := by have := hV x hj; linarith
  rcases Nat.lt_or_ge 1 (x j) with h2 | h1
  · have hS : M.S (M.sell x j) = M.S x := by
      ext k
      rw [hmemS, hmemS]
      by_cases hk : k = j
      · subst hk; simp [Model.sell]; omega
      · simp [Model.sell, Function.update_apply, hk]
    have hden : M.den (M.sell x j) q = M.den x q := by simp only [Model.den, hS]
    have hP : ∀ k, M.P (M.sell x j) q k = M.P x q k := by
      intro k; simp only [Model.P, hden, hS]
    have hP0 : M.P0 (M.sell x j) q = M.P0 x q := by simp only [Model.P0, hden]
    suffices hsuff : M.obj V x q ≤ M.obj V (M.sell x j) q + M.rfix j by
      have := le_max_left (M.obj V (M.sell x j) q) (V (M.sell x j)); linarith
    unfold Model.obj
    rw [hS, hP0]
    simp only [hP]
    have c1 : 0 ≤ M.lam * M.P0 x q + 1 - M.lam := by
      have := mul_nonneg hl0.le (P0_nonneg M x q); linarith
    have t1 : ∑ k ∈ M.S x, M.P x q k * V (M.sell x k)
        ≤ ∑ k ∈ M.S x, M.P x q k * V (M.sell (M.sell x j) k)
          + M.rfix j * ∑ k ∈ M.S x, M.P x q k := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_le_sum
      intro k hk
      have hk' : V (M.sell x k) ≤ V (M.sell (M.sell x j) k) + M.rfix j := by
        by_cases hkj : k = j
        · subst hkj
          have := hV (M.sell x k) (by rw [hS]; exact hk)
          linarith
        · exact hcont k hkj
      calc M.P x q k * V (M.sell x k)
          ≤ M.P x q k * (V (M.sell (M.sell x j) k) + M.rfix j) :=
            mul_le_mul_of_nonneg_left hk' (P_nonneg M x q k)
        _ = M.P x q k * V (M.sell (M.sell x j) k) + M.rfix j * M.P x q k := by ring
    have t2 : (M.lam * M.P0 x q + 1 - M.lam) * V x
        ≤ (M.lam * M.P0 x q + 1 - M.lam) * V (M.sell x j)
          + (M.lam * M.P0 x q + 1 - M.lam) * M.rfix j := by
      rw [← mul_add]; exact mul_le_mul_of_nonneg_left hVx c1
    have t3 : M.lam * ∑ k ∈ M.S x, M.P x q k * V (M.sell x k)
        ≤ M.lam * ∑ k ∈ M.S x, M.P x q k * V (M.sell (M.sell x j) k)
          + M.lam * (M.rfix j * ∑ k ∈ M.S x, M.P x q k) := by
      rw [← mul_add]; exact mul_le_mul_of_nonneg_left t1 hl0.le
    have hsum := sumP_add_P0 M x q
    have hid : M.lam * (M.rfix j * ∑ k ∈ M.S x, M.P x q k)
        + (M.lam * M.P0 x q + 1 - M.lam) * M.rfix j = M.rfix j := by
      have : ∑ k ∈ M.S x, M.P x q k = 1 - M.P0 x q := by linarith
      rw [this]; ring
    linarith
  · have hx1 : x j = 1 := by omega
    have hjy : j ∉ M.S (M.sell x j) := by
      rw [hmemS]; simp [Model.sell, hx1]
    have hSx : M.S x = insert j (M.S (M.sell x j)) := by
      ext k
      rw [Finset.mem_insert, hmemS, hmemS]
      by_cases hk : k = j
      · subst hk; simp [hxj]
      · simp [Model.sell, Function.update_apply, hk]
    have hne : ∀ k ∈ M.S (M.sell x j), k ≠ j := fun k hk h => hjy (h ▸ hk)
    have hkx : ∀ k ∈ M.S (M.sell x j), k ∈ M.S x := fun k hk => by
      rw [hSx]; exact Finset.mem_insert_of_mem hk
    set y := M.sell x j with hy
    set w0 := Real.exp (M.u0 / M.μ) with hw0
    set T := ∑ k ∈ M.S y, Real.exp ((M.a k - q k) / M.μ) with hT
    set A1 := ∑ k ∈ M.S y, q k * Real.exp ((M.a k - q k) / M.μ) with hA1
    set A2 := ∑ k ∈ M.S y, Real.exp ((M.a k - q k) / M.μ) * V (M.sell y k) with hA2
    set A2' := ∑ k ∈ M.S y, Real.exp ((M.a k - q k) / M.μ) * V (M.sell x k) with hA2'
    set ε := Real.exp ((M.a j - q j) / M.μ) with hε
    have hT0 : 0 ≤ T := Finset.sum_nonneg (fun _ _ => (Real.exp_pos _).le)
    have hwpos : 0 < w0 := Real.exp_pos _
    have hDy : M.den y q = T + w0 := rfl
    have hDx : M.den x q = ε + T + w0 := by
      show (∑ k ∈ M.S x, Real.exp ((M.a k - q k) / M.μ)) + Real.exp (M.u0 / M.μ) = _
      rw [hSx, Finset.sum_insert hjy]
    have hobjy : M.obj V y q = M.lam * (A1 / (T + w0)) + M.lam * (A2 / (T + w0))
        + (M.lam * (w0 / (T + w0)) + 1 - M.lam) * V y := by
      unfold Model.obj Model.P0
      rw [hDy]
      have u1 : ∑ k ∈ M.S y, q k * M.P y q k = A1 / (T + w0) := by
        rw [hA1, Finset.sum_div]
        exact Finset.sum_congr rfl (fun k hk => by rw [P_of_mem M q hk, hDy]; ring)
      have u2 : ∑ k ∈ M.S y, M.P y q k * V (M.sell y k) = A2 / (T + w0) := by
        rw [hA2, Finset.sum_div]
        exact Finset.sum_congr rfl (fun k hk => by rw [P_of_mem M q hk, hDy]; ring)
      rw [u1, u2]
    have hobjx : M.obj V x q = M.lam * (M.rfix j * (ε / (ε + T + w0)) + A1 / (ε + T + w0))
        + M.lam * (ε / (ε + T + w0) * V y + A2' / (ε + T + w0))
        + (M.lam * (w0 / (ε + T + w0)) + 1 - M.lam) * V x := by
      unfold Model.obj Model.P0
      rw [hDx]
      have hPj : M.P x q j = ε / (ε + T + w0) := by
        rw [P_of_mem M q hj, hDx]
      have u1 : ∑ k ∈ M.S y, q k * M.P x q k = A1 / (ε + T + w0) := by
        rw [hA1, Finset.sum_div]
        exact Finset.sum_congr rfl (fun k hk => by
          rw [P_of_mem M q (hkx k hk), hDx]; ring)
      have u2 : ∑ k ∈ M.S y, M.P x q k * V (M.sell x k) = A2' / (ε + T + w0) := by
        rw [hA2', Finset.sum_div]
        exact Finset.sum_congr rfl (fun k hk => by
          rw [P_of_mem M q (hkx k hk), hDx]; ring)
      rw [hSx, Finset.sum_insert hjy, Finset.sum_insert hjy, hPj, hqj, u1, u2]
    rw [hobjy, hobjx]
    have hAA : A2' ≤ A2 + M.rfix j * T := by
      rw [hA2', hA2, hT, Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_le_sum
      intro k hk
      calc Real.exp ((M.a k - q k) / M.μ) * V (M.sell x k)
          ≤ Real.exp ((M.a k - q k) / M.μ) * (V (M.sell y k) + M.rfix j) :=
            mul_le_mul_of_nonneg_left (hcont k (hne k hk)) (Real.exp_pos _).le
        _ = _ := by ring
    exact fix_ineq hl0 hl1 hwpos (Real.exp_pos _) hT0 hAA hVx

/-- candidate prices for a general continuation value -/
noncomputable def rs (V : (Fin M.n → ℕ) → ℝ) (x : Fin M.n → ℕ) (m : ℝ) : Fin M.n → ℝ :=
  fun i => if i ∈ M.S1 x then (V x - V (M.sell x i)) + m else 0

lemma closed (hM : M.Assumptions) (V : (Fin M.n → ℕ) → ℝ)
    (hQ1 : ∀ z i, i ∈ M.dyn → i ∈ M.S z → V (M.sell z i) ≤ V z)
    (hQ2 : ∀ z j, j ∉ M.dyn → j ∈ M.S z → V z - V (M.sell z j) ≤ M.rfix j)
    (x : Fin M.n → ℕ) (m : ℝ)
    (hm : Lg M x (fun k => V x - V (M.sell x k)) m = Rg M x (fun k => V x - V (M.sell x k))) :
    rs M V x m ∈ M.feasibleM ∧
    IsGreatest (M.objM V x '' M.feasibleM) (M.objM V x (rs M V x m)) ∧
    M.objM V x (rs M V x m) = V x + M.lam * (m - M.μ) ∧ M.μ ≤ m := by
  have hμ := hM.mu_pos
  have hlam := hM.lam_pos
  have hSV : 0 ≤ SV M x (fun k => V x - V (M.sell x k)) := by
    apply Finset.sum_nonneg
    intro j hj
    obtain ⟨h1, h2⟩ := mem_S2 M hj
    have := hQ2 x j h2 h1
    exact mul_nonneg (Real.exp_pos _).le (by linarith)
  have hmμ := root_ge_mu M hμ (Rg_nonneg M x _) hSV hm
  have hq2 : ∀ j ∈ M.S2 x, M.mix (rs M V x m) j = M.rfix j :=
    fun j hj => mix_fix M (mem_S2 M hj).2
  have hq1 : ∀ i ∈ M.S1 x, M.mix (rs M V x m) i = (V x - V (M.sell x i)) + m := by
    intro i hi
    rw [mix_dyn M (mem_S1 M hi).2]
    simp [rs, hi]
  have e1 := key_eq M hμ x (fun k => V x - V (M.sell x k)) m hm (M.mix (rs M V x m)) hq2 hq1
  have hval : M.objM V x (rs M V x m) = V x + M.lam * (m - M.μ) := by
    show M.obj V x (M.mix (rs M V x m)) = _
    rw [obj_eq, e1]
  have hfeas : rs M V x m ∈ M.feasibleM := by
    intro i hi
    simp only [rs]
    split_ifs with h
    · have := hQ1 x i hi (mem_S1 M h).1; linarith
    · exact le_refl 0
  refine ⟨hfeas, ⟨⟨_, hfeas, rfl⟩, ?_⟩, hval, hmμ⟩
  rintro _ ⟨r, _, rfl⟩
  rw [hval]
  show M.obj V x (M.mix r) ≤ _
  rw [obj_eq]
  have h1 := key_le M hμ x (fun k => V x - V (M.sell x k)) m hm (M.mix r)
    (fun j hj => mix_fix M (mem_S2 M hj).2)
  have h2 := mul_le_mul_of_nonneg_left h1 hlam.le
  linarith

lemma step_facts (hM : M.Assumptions) (s : ℕ)
    (hQ1 : ∀ z i, i ∈ M.dyn → i ∈ M.S z → M.piM s (M.sell z i) ≤ M.piM s z)
    (hQ2 : ∀ z j, j ∉ M.dyn → j ∈ M.S z → M.piM s z - M.piM s (M.sell z j) ≤ M.rfix j)
    (w : Fin M.n → ℕ) (m : ℝ)
    (hm : Lg M w (fun k => M.piM s w - M.piM s (M.sell w k)) m
      = Rg M w (fun k => M.piM s w - M.piM s (M.sell w k))) :
    rs M (M.piM s) w m ∈ M.feasibleM ∧
    IsGreatest (M.objM (M.piM s) w '' M.feasibleM) (M.objM (M.piM s) w (rs M (M.piM s) w m)) ∧
    M.objM (M.piM s) w (rs M (M.piM s) w m) = M.piM s w + M.lam * (m - M.μ) ∧ M.μ ≤ m ∧
    M.piM (s + 1) w = M.objM (M.piM s) w (rs M (M.piM s) w m) := by
  obtain ⟨a, b, c, d⟩ := closed M hM (M.piM s) hQ1 hQ2 w m hm
  refine ⟨a, b, c, d, ?_⟩
  show sSup ((M.objM (M.piM s) w) '' M.feasibleM) = _
  exact b.csSup_eq

lemma Q_all (hM : M.Assumptions) : ∀ s,
    (∀ z i, i ∈ M.dyn → i ∈ M.S z → M.piM s (M.sell z i) ≤ M.piM s z) ∧
    (∀ z j, j ∉ M.dyn → j ∈ M.S z → M.piM s z - M.piM s (M.sell z j) ≤ M.rfix j) := by
  intro s
  induction s with
  | zero =>
    refine ⟨fun z i _ _ => by simp [Model.piM], fun z j hj _ => ?_⟩
    simpa [Model.piM] using hM.rfix_nonneg j hj
  | succ s ih =>
    obtain ⟨h1, h2⟩ := ih
    have fact : ∀ w, ∃ m, rs M (M.piM s) w m ∈ M.feasibleM ∧
        IsGreatest (M.objM (M.piM s) w '' M.feasibleM)
          (M.objM (M.piM s) w (rs M (M.piM s) w m)) ∧
        M.objM (M.piM s) w (rs M (M.piM s) w m) = M.piM s w + M.lam * (m - M.μ) ∧ M.μ ≤ m ∧
        M.piM (s + 1) w = M.objM (M.piM s) w (rs M (M.piM s) w m) := by
      intro w
      obtain ⟨m, hm⟩ := root_exists M hM.mu_pos w (fun k => M.piM s w - M.piM s (M.sell w k))
        (Rg_nonneg M w (fun k => M.piM s w - M.piM s (M.sell w k)))
      exact ⟨m, step_facts M hM s h1 h2 w m hm⟩
    refine ⟨?_, ?_⟩
    · intro z i hi hiz
      obtain ⟨my, fy, -, -, -, ey⟩ := fact (M.sell z i)
      obtain ⟨mz, -, gz, -, -, ez⟩ := fact z
      set r0 := rs M (M.piM s) (M.sell z i) my with hr0
      have hq : 0 ≤ M.mix r0 i := by rw [mix_dyn M hi]; exact fy i hi
      obtain ⟨R, hR, hle⟩ := mono_step M hM (M.piM s) i (fun w hw => h1 w i hi hw) z hiz
        (M.mix r0) hq
      have hfe : Function.update r0 i R ∈ M.feasibleM := by
        intro k hk
        by_cases hki : k = i
        · subst hki; simp only [Function.update_self]; exact hR
        · simp only [Function.update_apply, hki, if_false]; exact fy k hk
      rw [ey, ez]
      calc M.objM (M.piM s) (M.sell z i) r0 = M.obj (M.piM s) (M.sell z i) (M.mix r0) := rfl
        _ ≤ M.obj (M.piM s) z (Function.update (M.mix r0) i R) := hle
        _ = M.objM (M.piM s) z (Function.update r0 i R) := by rw [mix_update M r0 hi]; rfl
        _ ≤ M.objM (M.piM s) z (rs M (M.piM s) z mz) := gz.2 ⟨_, hfe, rfl⟩
    · intro z j hj hjz
      obtain ⟨my, -, gy, vy, hmy, ey⟩ := fact (M.sell z j)
      obtain ⟨mz, fz, -, -, -, ez⟩ := fact z
      set rz := rs M (M.piM s) z mz with hrz
      have hle := fix_step M hM (M.piM s) j (fun w hw => h2 w j hj hw) z hjz (M.mix rz)
        (mix_fix M hj)
      have a1 : M.obj (M.piM s) (M.sell z j) (M.mix rz) ≤ M.piM (s + 1) (M.sell z j) := by
        rw [ey]; exact gy.2 ⟨rz, fz, rfl⟩
      have a2 : M.piM s (M.sell z j) ≤ M.piM (s + 1) (M.sell z j) := by
        rw [ey, vy]
        have := mul_nonneg hM.lam_pos.le (sub_nonneg.mpr hmy); linarith
      have e : M.piM (s + 1) z = M.obj (M.piM s) z (M.mix rz) := ez
      rw [e]
      have := max_le a1 a2
      linarith

end SPM47

open SubstitutePricing.Mixed in
theorem solution (M : Model) (hM : M.Assumptions) (t : ℕ) (ht : 1 ≤ t)
    (x : Fin M.n → ℕ) :
    (∃! m : ℝ, M.lhs15 t x m = M.rhs15 t x) ∧
    (∀ m : ℝ, M.lhs15 t x m = M.rhs15 t x →
      M.rstarM t x m ∈ M.feasibleM ∧
      IsMaxOn (M.objM (M.piM (t - 1)) x) M.feasibleM (M.rstarM t x m) ∧
      M.piM t x = M.objM (M.piM (t - 1)) x (M.rstarM t x m)) ∧
    (∀ ms : ℕ → ℝ,
      (∀ s ∈ Finset.Icc 1 t, M.lhs15 s x (ms s) = M.rhs15 s x) →
      M.piM t x = M.lam * ∑ s ∈ Finset.Icc 1 t, (ms s - M.μ)) := by
  obtain ⟨k, rfl⟩ : ∃ k, t = k + 1 := ⟨t - 1, by omega⟩
  have hQ := SPM47.Q_all M hM
  have hl : ∀ (s : ℕ) (w : Fin M.n → ℕ) (m : ℝ), M.lhs15 (s + 1) w m
      = SPM47.Lg M w (fun j => M.piM s w - M.piM s (M.sell w j)) m := fun s w m => rfl
  have hr : ∀ (s : ℕ) (w : Fin M.n → ℕ), M.rhs15 (s + 1) w
      = SPM47.Rg M w (fun j => M.piM s w - M.piM s (M.sell w j)) := fun s w => rfl
  have hrs : ∀ (s : ℕ) (w : Fin M.n → ℕ) (m : ℝ), M.rstarM (s + 1) w m
      = SPM47.rs M (M.piM s) w m := fun s w m => rfl
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨m, hm⟩ := SPM47.root_exists M hM.mu_pos x
      (fun j => M.piM k x - M.piM k (M.sell x j))
      (SPM47.Rg_nonneg M x (fun j => M.piM k x - M.piM k (M.sell x j)))
    refine ⟨m, by show M.lhs15 (k + 1) x m = M.rhs15 (k + 1) x; rw [hl, hr]; exact hm,
      fun m' hm' => ?_⟩
    have hm'' : M.lhs15 (k + 1) x m' = M.rhs15 (k + 1) x := hm'
    rw [hl, hr] at hm''
    exact SPM47.root_unique M hM.mu_pos (SPM47.Rg_nonneg M x _) hm'' hm
  · intro m hm
    rw [hl, hr] at hm
    obtain ⟨a, b, -, -, e⟩ := SPM47.step_facts M hM k (hQ k).1 (hQ k).2 x m hm
    simp only [Nat.add_sub_cancel]
    rw [hrs]
    exact ⟨a, isMaxOn_iff.mpr (fun r hr => b.2 ⟨r, hr, rfl⟩), e⟩
  · intro ms hms
    have tel : ∀ u, (∀ v ∈ Finset.Icc 1 u, M.lhs15 v x (ms v) = M.rhs15 v x) →
        M.piM u x = M.lam * ∑ v ∈ Finset.Icc 1 u, (ms v - M.μ) := by
      intro u
      induction u with
      | zero => intro _; simp [Model.piM]
      | succ u ih =>
        intro h
        rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ u + 1)]
        have hu := h (u + 1) (Finset.mem_Icc.mpr ⟨by omega, le_refl _⟩)
        rw [hl, hr] at hu
        obtain ⟨-, -, e4, -, e3⟩ := SPM47.step_facts M hM u (hQ u).1 (hQ u).2 x _ hu
        have hih := ih (fun v hv => h v (Finset.mem_Icc.mpr
          ⟨(Finset.mem_Icc.mp hv).1, by have := (Finset.mem_Icc.mp hv).2; omega⟩))
        rw [e3, e4, hih]
        ring
    exact tel _ hms
