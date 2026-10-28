-- Prove2me | solution 1 for PrivLearn.MaskedParity.theorem_5_16
-- status  : ACCEPTED   (prove)
-- author  : @sometik179
-- created : 2026-10-25T00:15:49.24616+00:00
-- url     : https://prove2.me/submissions/4abb606c-65c7-4a79-a77b-b1ec9e83e1d1

import Mathlib
import Definitions.Def_PrivLearn_MaskedParity_Model
import Definitions.Def_PrivLearn_MaskedParity_Oracle
import Definitions.Def_PrivLearn_MaskedParity_AMP


open Finset
open PrivLearn.MaskedParity

namespace MPProof

noncomputable def sign (a : ZMod 2) : ℝ := (-1 : ℝ) ^ a.val

@[simp] theorem sign_zero : sign 0 = 1 := by norm_num [sign]
@[simp] theorem sign_one : sign 1 = -1 := by change (-1 : ℝ) ^ 1 = -1; norm_num

theorem bit_cases (a : ZMod 2) : a = 0 ∨ a = 1 := by
  have hv := ZMod.val_lt a
  have h : a.val = 0 ∨ a.val = 1 := by omega
  rcases h with h | h
  · left; apply ZMod.val_injective 2; change a.val = 0; exact h
  · right; apply ZMod.val_injective 2; change a.val = 1; exact h

theorem sign_values (a : ZMod 2) : sign a = 1 ∨ sign a = -1 := by
  rcases bit_cases a with rfl | rfl <;> simp

theorem sign_add (a b : ZMod 2) : sign (a + b) = sign a * sign b := by
  rcases bit_cases a with rfl | rfl <;> rcases bit_cases b with rfl | rfl <;>
    norm_num [sign, ZMod.val_add, ZMod.val_one]
  change (-1 : ℝ) ^ 0 = 1
  norm_num

@[simp] theorem sign_sq (a : ZMod 2) : sign a ^ 2 = 1 := by
  rcases sign_values a with h | h <;> rw [h] <;> norm_num

@[simp] theorem sign_ne_zero (a : ZMod 2) : sign a ≠ 0 := by
  rcases sign_values a with h | h <;> rw [h] <;> norm_num

theorem sign_add_one (a : ZMod 2) : sign (a + 1) = - sign a := by
  rw [sign_add, sign_one]; ring

theorem sign_eq_neg_one (a : ZMod 2) : sign a = -1 ↔ a = 1 := by
  rcases bit_cases a with rfl | rfl <;> norm_num

theorem sum_zmod_two {M : Type*} [AddCommMonoid M] (f : ZMod 2 → M) :
    ∑ b, f b = f 0 + f 1 := by
  have h : (Finset.univ : Finset (ZMod 2)) = {0, 1} := by decide
  rw [h]; simp

theorem domain_card (d : ℕ) : Fintype.card (Dom d) = 2 ^ d * d * 2 := by
  simp [Dom, Fintype.card_prod, Nat.mul_assoc]

theorem domain_card_pos {d : ℕ} (hd : 0 < d) : 0 < Fintype.card (Dom d) := by
  rw [domain_card]; positivity

theorem domain_card_ne_zero {d : ℕ} (hd : 0 < d) : (Fintype.card (Dom d) : ℝ) ≠ 0 := by
  exact_mod_cast (Nat.ne_of_gt (domain_card_pos hd))

theorem card_parities (d : ℕ) : Fintype.card (Fin d → ZMod 2) = 2 ^ d := by
  simp

theorem card_pairs (d : ℕ) : Fintype.card ((Fin d → ZMod 2) × ZMod 2) = 2 ^ (d + 1) := by
  simp [Fintype.card_prod, pow_succ]

theorem sum_dom {d : ℕ} {M : Type*} [AddCommMonoid M] (f : Dom d → M) :
    ∑ u, f u = ∑ x : Fin d → ZMod 2, ∑ i : Fin d, (f (x, i, 0) + f (x, i, 1)) := by
  simp only [Dom, Fintype.sum_prod_type, sum_zmod_two]

theorem cMP_zero_half {d : ℕ} (r x : Fin d → ZMod 2) (a : ZMod 2) (i : Fin d) :
    cMP r a (x, i, 0) = sign (r ⬝ᵥ x + a) := by simp [cMP, sign]

theorem cMP_one_half {d : ℕ} (r x : Fin d → ZMod 2) (a : ZMod 2) (i : Fin d) :
    cMP r a (x, i, 1) = sign (r i) := by simp [cMP, sign]

theorem cMP_values {d : ℕ} (r : Fin d → ZMod 2) (a : ZMod 2) (u : Dom d) :
    cMP r a u = 1 ∨ cMP r a u = -1 := by
  unfold cMP
  split <;> exact sign_values _

theorem half_zero_neg {d : ℕ} (r : Fin d → ZMod 2) :
    half 0 (cMP r 1) = fun u => - half 0 (cMP r 0) u := by
  funext u
  simp only [half]
  split_ifs with h
  · simpa only [cMP, h, if_pos, add_zero, sign] using sign_add_one (r ⬝ᵥ u.1)
  · simp

theorem half_one_mask_independent {d : ℕ} (r : Fin d → ZMod 2) (a : ZMod 2) :
    half 1 (cMP r a) = half 1 (cMP r 0) := by
  funext u
  simp only [half]
  split_ifs with h
  · simp [cMP, h]
  · rfl

theorem ip_neg_right {d : ℕ} (f h : Dom d → ℝ) :
    ip f (fun u => - h u) = - ip f h := by simp [ip, Finset.sum_neg_distrib]

theorem correlation_abs_mask {d : ℕ} (r : Fin d → ZMod 2) (a : ZMod 2)
    (f : Dom d → ℝ) :
    |ip f (half 0 (cMP r a))| = |ip f (half 0 (cMP r 0))| := by
  rcases bit_cases a with rfl | rfl
  · rfl
  · rw [half_zero_neg, ip_neg_right, abs_neg]

end MPProof


open Finset PrivLearn.MaskedParity

namespace MPProof

theorem qval_decompose {d : ℕ} (r : Fin d → ZMod 2) (a : ZMod 2)
    (g : Dom d → ℝ → ℝ) :
    qval (cMP r a) g = Cg g + ip (fg g) (cMP r a) := by
  unfold qval Cg ip
  rw [← mul_add, ← Finset.sum_add_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro u _
  rcases cMP_values r a u with h | h <;> rw [h] <;> simp only [fg] <;> ring

theorem ip_half_split {d : ℕ} (f h : Dom d → ℝ) :
    ip f h = ip (half 0 f) (half 0 h) + ip (half 1 f) (half 1 h) := by
  unfold ip
  rw [← mul_add, ← Finset.sum_add_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro u _
  rcases bit_cases u.2.2 with hb | hb <;> simp [half, hb]

theorem qval_half_decompose {d : ℕ} (r : Fin d → ZMod 2) (a : ZMod 2)
    (g : Dom d → ℝ → ℝ) :
    qval (cMP r a) g = Cg g + ip (half 0 (fg g)) (half 0 (cMP r a)) +
      ip (half 1 (fg g)) (half 1 (cMP r a)) := by
  rw [qval_decompose, ip_half_split]; ring

theorem oracle_valid_all {d : ℕ} (r : Fin d → ZMod 2) (a : ZMod 2)
    (g : Dom d → ℝ → ℝ) (τ : ℝ) (hτ : 0 < τ) :
    IsLabeledSQAnswer (cMP r a) g τ (oracleO r a g τ) := by
  unfold IsLabeledSQAnswer oracleO
  split_ifs with h
  · rw [qval_half_decompose]
    have he : Cg g + ip (half 1 (fg g)) (half 1 (cMP r a)) -
        (Cg g + ip (half 0 (fg g)) (half 0 (cMP r a)) +
          ip (half 1 (fg g)) (half 1 (cMP r a))) =
          - ip (half 0 (fg g)) (half 0 (cMP r a)) := by ring
    rw [he, abs_neg]
    exact h.le
  · simpa using hτ.le

theorem oracle_good_mask {d : ℕ} (r : Fin d → ZMod 2) (a : ZMod 2)
    (g : Dom d → ℝ → ℝ) (τ : ℝ)
    (h : |ip (half 0 (fg g)) (half 0 (cMP r 0))| < τ) :
    oracleO r a g τ = oracleO r 0 g τ := by
  have ha : |ip (half 0 (fg g)) (half 0 (cMP r a))| < τ := by
    rwa [correlation_abs_mask]
  simp only [oracleO, ha, h, if_pos, half_one_mask_independent]

end MPProof


open Finset PrivLearn.MaskedParity

namespace MPProof

theorem sign_add_ne (z a : ZMod 2) : sign (z + a) ≠ sign z ↔ a = 1 := by
  rcases bit_cases a with rfl | rfl
  · simp
  · rw [sign_add_one]
    have h : - sign z ≠ sign z := by
      intro he
      apply sign_ne_zero z
      linarith
    simp [h]

theorem sum_round1 {d : ℕ} (r : Fin d → ZMod 2) (a : ZMod 2) (j : Fin d) :
    (∑ u, gRound1 j u (cMP r a u)) = (2 : ℝ) ^ d * (if r j = 1 then 1 else 0) := by
  rw [sum_dom]
  simp only [gRound1, cMP_one_half, sign_eq_neg_one]
  by_cases h : r j = 1
  · have he (i : Fin d) : (i = j ∧ r i = 1) ↔ i = j := by
      constructor
      · exact And.left
      · intro hi; exact ⟨hi, hi ▸ h⟩
    simp [h, he]
  · have hn : ∀ i, ¬ (i = j ∧ r i = 1) := by intro i hi; exact h (hi.1 ▸ hi.2)
    simp [h, hn]

theorem qval_round1 {d : ℕ} (hd : 0 < d) (r : Fin d → ZMod 2)
    (a : ZMod 2) (j : Fin d) :
    qval (cMP r a) (gRound1 j) = if r j = 1 then 1 / (2 * (d : ℝ)) else 0 := by
  unfold qval
  rw [sum_round1, domain_card]
  push_cast
  have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hd)
  have hpow : (2 : ℝ) ^ d ≠ 0 := by positivity
  split_ifs
  · field_simp
  · simp

theorem sum_round2 {d : ℕ} (r : Fin d → ZMod 2) (a : ZMod 2) :
    (∑ u, gRound2 r u (cMP r a u)) =
      (2 : ℝ) ^ d * (d : ℝ) * (if a = 1 then 1 else 0) := by
  rw [sum_dom]
  have hh (x : Fin d → ZMod 2) :
      sign (r ⬝ᵥ x + a) = (-1 : ℝ)^((r ⬝ᵥ x).val) ↔ a ≠ 1 := by
    simpa only [not_not, sign] using (not_congr (sign_add_ne (r ⬝ᵥ x) a))
  simp [gRound2, cMP_zero_half, hh]

theorem qval_round2 {d : ℕ} (hd : 0 < d) (r : Fin d → ZMod 2)
    (a : ZMod 2) :
    qval (cMP r a) (gRound2 r) = if a = 1 then 1 / 2 else 0 := by
  unfold qval
  rw [sum_round2, domain_card]
  push_cast
  have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hd)
  have hpow : (2 : ℝ) ^ d ≠ 0 := by positivity
  split_ifs
  · field_simp
  · simp

theorem round1_decode {d : ℕ} (hd : 0 < d) (r : Fin d → ZMod 2)
    (a : ZMod 2) (ans : Fin d → ℝ)
    (ha : ∀ j, IsLabeledSQAnswer (cMP r a) (gRound1 j)
      (1 / (4 * (d : ℝ) + 1)) (ans j)) : rhat ans = r := by
  funext j
  have h := ha j
  rw [IsLabeledSQAnswer, qval_round1 hd] at h
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have ht : 1 / (4 * (d : ℝ) + 1) < 1 / (4 * (d : ℝ)) := by
    apply one_div_lt_one_div_of_lt <;> linarith
  have he : 1 / (2 * (d : ℝ)) = 2 * (1 / (4 * (d : ℝ))) := by field_simp; ring
  rcases bit_cases (r j) with hr | hr
  · rw [hr] at h ⊢
    simp only [zero_ne_one, if_false, sub_zero] at h
    have hle := (abs_le.mp h).2
    simp only [rhat]
    rw [if_neg (by linarith)]
  · rw [hr] at h ⊢
    simp only [if_pos] at h
    have hle := (abs_le.mp h).1
    simp only [rhat]
    rw [if_pos (by linarith)]

theorem round2_decode {d : ℕ} (hd : 0 < d) (r : Fin d → ZMod 2)
    (a : ZMod 2) (v : ℝ)
    (ha : IsLabeledSQAnswer (cMP r a) (gRound2 r) (1 / 5) v) : ahat v = a := by
  rw [IsLabeledSQAnswer, qval_round2 hd] at ha
  rcases bit_cases a with rfl | rfl
  · simp only [zero_ne_one, if_false, sub_zero] at ha
    have h := (abs_le.mp ha).2
    simp only [ahat]
    rw [if_neg (by linarith)]
  · simp only [if_pos] at ha
    have h := (abs_le.mp ha).1
    simp only [ahat]
    rw [if_pos (by linarith)]

theorem amp_exact {d : ℕ} (hd : 0 < d) (r : Fin d → ZMod 2) (a : ZMod 2)
    (ans₁ : Fin d → ℝ) (ans₂ : Fin 1 → ℝ)
    (h₁ : ∀ j, IsLabeledSQAnswer (cMP r a) ((AMP d).q₁ j) ((AMP d).τ₁ j) (ans₁ j))
    (h₂ : ∀ k, IsLabeledSQAnswer (cMP r a) ((AMP d).q₂ ans₁ k) ((AMP d).τ₂ ans₁ k) (ans₂ k)) :
    (AMP d).out ans₁ ans₂ = cMP r a := by
  have hr : rhat ans₁ = r := round1_decode hd r a ans₁ h₁
  have h := h₂ 0
  change IsLabeledSQAnswer (cMP r a) (gRound2 (rhat ans₁)) (1 / 5) (ans₂ 0) at h
  rw [hr] at h
  have ha := round2_decode hd r a (ans₂ 0) h
  change cMP (rhat ans₁) (ahat (ans₂ 0)) = _
  rw [hr, ha]

theorem amp_tolerance {d : ℕ} (hd : 0 < d) : 1 / (4 * (d : ℝ) + 1) ≤ 1 / 5 := by
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
  apply one_div_le_one_div_of_le <;> linarith

end MPProof


open Finset PrivLearn.MaskedParity
namespace MPProof

noncomputable def mistakes {d : ℕ} (f h : Dom d → ℝ) : ℝ :=
  ∑ u, if f u ≠ h u then (1 : ℝ) else 0

theorem err_as_sum {d : ℕ} (f h : Dom d → ℝ) :
    errMP f h = mistakes f h / (Fintype.card (Dom d) : ℝ) := by
  unfold errMP mistakes
  rw [Finset.card_filter]
  push_cast
  rfl

theorem mask_sum_lower {d : ℕ} (r : Fin d → ZMod 2) (h : Dom d → ℝ) :
    (2 : ℝ)^d * d ≤ mistakes (cMP r 0) h + mistakes (cMP r 1) h := by
  unfold mistakes
  rw [sum_dom, sum_dom, ← Finset.sum_add_distrib]
  calc
    (2 : ℝ)^d * d = ∑ x : Fin d → ZMod 2, ∑ i : Fin d, (1 : ℝ) := by simp
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro x hx
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_le_sum
      intro i hi
      have hn : cMP r 0 (x,i,0) ≠ cMP r 1 (x,i,0) := by
        rw [cMP_zero_half, cMP_zero_half, add_zero, sign_add_one]
        intro he
        apply sign_ne_zero (r ⬝ᵥ x)
        linarith
      by_cases h0 : cMP r 0 (x,i,0) = h (x,i,0)
      · have h1 : cMP r 1 (x,i,0) ≠ h (x,i,0) := by
          intro he; exact hn (h0.trans he.symm)
        simp only [h0, ne_eq, not_true_eq_false, if_false, h1, not_false_eq_true, if_true]
        split_ifs <;> norm_num
      · simp only [h0, ne_eq, not_false_eq_true, if_true]
        split_ifs <;> norm_num

theorem mask_error_lower {d : ℕ} (hd : 0 < d) (r : Fin d → ZMod 2)
    (h : Dom d → ℝ) : 1 / 2 ≤ errMP (cMP r 0) h + errMP (cMP r 1) h := by
  rw [err_as_sum, err_as_sum, ← add_div]
  have hc : (0 : ℝ) < Fintype.card (Dom d) := by exact_mod_cast domain_card_pos hd
  apply (le_div_iff₀ hc).2
  have he : (Fintype.card (Dom d) : ℝ) = (2:ℝ)^d*d*2 := by rw [domain_card]; push_cast; rfl
  rw [he]
  nlinarith [mask_sum_lower r h]

end MPProof


open Finset PrivLearn.MaskedParity
namespace MPProof

theorem pair_count {R : Type*} [Fintype R] (G F : R × ZMod 2 → Prop)
    [DecidablePred G] [DecidablePred F]
    (hG : ∀ r a, G (r,a) ↔ G (r,0))
    (hF : ∀ r, G (r,0) → F (r,0) ∨ F (r,1)) :
    ((univ.filter G).card : ℝ) ≤ 2 * ((univ.filter F).card : ℝ) := by
  rw [Finset.card_filter, Finset.card_filter]
  push_cast
  rw [Fintype.sum_prod_type, Fintype.sum_prod_type, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro r hr
  rw [sum_zmod_two, sum_zmod_two]
  by_cases hg : G (r,0)
  · have hg1 : G (r,1) := (hG r 1).2 hg
    rcases hF r hg with hf | hf
    · simp only [hg, hg1, hf, if_true]
      split_ifs <;> norm_num
    · simp only [hg, hg1, hf, if_true]
      split_ifs <;> norm_num
  · have hg1 : ¬ G (r,1) := fun h => hg ((hG r 1).1 h)
    simp only [hg, hg1, if_false]
    split_ifs <;> norm_num

theorem failure_count {d : ℕ} (hd : 0 < d) (t : ℕ)
    (L : NonadaptiveSQLearner (Dom d) t)
    (hτ : ∀ k, 1 / (2 : ℝ)^((d:ℝ)/3) ≤ L.τ k) :
    ((univ.filter fun ra : (Fin d → ZMod 2) × ZMod 2 =>
      ∀ k, |ip (half 0 (fg (L.q k))) (half 0 (cMP ra.1 ra.2))| <
        1 / (2 : ℝ)^((d:ℝ)/3)).card : ℝ) ≤
    2 * ((univ.filter fun ra : (Fin d → ZMod 2) × ZMod 2 =>
      1 / 4 ≤ errMP (cMP ra.1 ra.2)
        (L.out fun k => oracleO ra.1 ra.2 (L.q k) (L.τ k))).card : ℝ) := by
  classical
  apply pair_count
  · intro r a
    simp only [correlation_abs_mask r a]
  · intro r hg
    have ho (a : ZMod 2) :
        (fun k => oracleO r a (L.q k) (L.τ k)) =
        (fun k => oracleO r 0 (L.q k) (L.τ k)) := by
      funext k
      exact oracle_good_mask r a (L.q k) (L.τ k) (lt_of_lt_of_le (hg k) (hτ k))
    have hm := mask_error_lower hd r
      (L.out fun k => oracleO r 0 (L.q k) (L.τ k))
    dsimp only
    rw [ho 1]
    by_contra hn
    push Not at hn
    linarith [hn.1, hn.2]

end MPProof


open Finset PrivLearn.MaskedParity
namespace MPProof

 theorem walsh_sum {d : ℕ} (r : Fin d → ZMod 2) :
    (∑ x : Fin d → ZMod 2, sign (r ⬝ᵥ x)) =
      if r = 0 then (2 : ℝ) ^ d else 0 := by
  classical
  by_cases hr : r = 0
  · subst r
    simp [dotProduct]
  · rw [if_neg hr]
    obtain ⟨i, hi⟩ : ∃ i, r i ≠ 0 := by
      by_contra h
      push Not at h
      exact hr (funext h)
    have hi1 : r i = 1 := (bit_cases (r i)).resolve_left hi
    have hshift : ∀ x : Fin d → ZMod 2,
        sign (r ⬝ᵥ (x + Pi.single i 1)) = -sign (r ⬝ᵥ x) := by
      intro x
      rw [dotProduct_add, dotProduct_single, hi1, one_mul, sign_add_one]
    have hs := Fintype.sum_equiv (Equiv.addRight (Pi.single i (1 : ZMod 2)))
      (fun x : Fin d → ZMod 2 => -sign (r ⬝ᵥ x))
      (fun x : Fin d → ZMod 2 => sign (r ⬝ᵥ x))
      (fun x => (hshift x).symm)
    simp only [sum_neg_distrib] at hs
    linarith

 theorem walsh_kernel {d : ℕ} (x y : Fin d → ZMod 2) :
    (∑ r : Fin d → ZMod 2, sign (r ⬝ᵥ x) * sign (r ⬝ᵥ y)) =
      if x = y then (2 : ℝ) ^ d else 0 := by
  classical
  have hxy : x + y = 0 ↔ x = y := by
    constructor
    · intro h
      funext i
      have hi := congrFun h i
      rcases bit_cases (x i) with hx | hx <;>
        rcases bit_cases (y i) with hy | hy <;> simp_all
    · rintro rfl
      funext i
      rcases bit_cases (x i) with h | h
      · simp [h]
      · simp only [Pi.add_apply, Pi.zero_apply, h]; decide
  simp_rw [← sign_add, ← dotProduct_add, dotProduct_comm _ (x + y)]
  rw [walsh_sum]
  simp only [hxy]

theorem walsh_parseval {d : ℕ} (A : (Fin d → ZMod 2) → ℝ) :
    (∑ r : Fin d → ZMod 2, (∑ x, A x * sign (r ⬝ᵥ x)) ^ 2) =
      (2 : ℝ) ^ d * ∑ x, A x ^ 2 := by
  classical
  calc
    _ = ∑ r : Fin d → ZMod 2, ∑ x, ∑ y,
        A x * A y * (sign (r ⬝ᵥ x) * sign (r ⬝ᵥ y)) := by
      apply sum_congr rfl
      intro r _
      simp only [pow_two, sum_mul, mul_sum]
      apply sum_congr rfl
      intro x _
      apply sum_congr rfl
      intro y _
      ring
    _ = ∑ x, ∑ y, A x * A y * ∑ r : Fin d → ZMod 2,
        sign (r ⬝ᵥ x) * sign (r ⬝ᵥ y) := by
      rw [sum_comm]
      apply sum_congr rfl
      intro x _
      rw [sum_comm]
      simp only [mul_sum]
    _ = ∑ x, A x ^ 2 * (2 : ℝ) ^ d := by
      simp_rw [walsh_kernel]
      apply sum_congr rfl
      intro x _
      simp [mul_ite, pow_two]
    _ = _ := by rw [← sum_mul]; ring

noncomputable def fiberSum {d : ℕ} (f : Dom d → ℝ) (x : Fin d → ZMod 2) : ℝ :=
  ∑ i : Fin d, f (x, i, 0)

theorem correlation_walsh {d : ℕ} (f : Dom d → ℝ) (r : Fin d → ZMod 2) :
    ip (half 0 f) (half 0 (cMP r 0)) =
      (Fintype.card (Dom d) : ℝ)⁻¹ *
        ∑ x : Fin d → ZMod 2, fiberSum f x * sign (r ⬝ᵥ x) := by
  unfold ip
  congr 1
  rw [sum_dom]
  apply sum_congr rfl
  intro x _
  simp [half, cMP, fiberSum, sign, sum_mul]

theorem fiberSum_sq_le {d : ℕ} (f : Dom d → ℝ) (hf : ∀ u, |f u| ≤ 1)
    (x : Fin d → ZMod 2) : fiberSum f x ^ 2 ≤ (d : ℝ) ^ 2 := by
  have h : |fiberSum f x| ≤ (d : ℝ) := by
    unfold fiberSum
    calc
      _ ≤ ∑ i : Fin d, |f (x, i, 0)| := abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i : Fin d, (1 : ℝ) := sum_le_sum fun i _ => hf (x, i, 0)
      _ = _ := by simp
  nlinarith [sq_abs (fiberSum f x), abs_nonneg (fiberSum f x)]

theorem correlation_energy_zero {d : ℕ} (hd : 0 < d)
    (f : Dom d → ℝ) (hf : ∀ u, |f u| ≤ 1) :
    (∑ r : Fin d → ZMod 2, ip (half 0 f) (half 0 (cMP r 0)) ^ 2) ≤ 1 / 4 := by
  have hsum : (∑ x : Fin d → ZMod 2, fiberSum f x ^ 2) ≤
      (2 : ℝ) ^ d * (d : ℝ) ^ 2 := by
    calc
      _ ≤ ∑ _x : Fin d → ZMod 2, (d : ℝ) ^ 2 :=
        sum_le_sum fun x _ => fiberSum_sq_le f hf x
      _ = _ := by simp
  have hn : (2 : ℝ) ^ d ≠ 0 := by positivity
  have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hd
  calc
    _ = (Fintype.card (Dom d) : ℝ)⁻¹ ^ 2 *
        ((2 : ℝ) ^ d * ∑ x : Fin d → ZMod 2, fiberSum f x ^ 2) := by
      simp_rw [correlation_walsh, mul_pow]
      rw [← mul_sum, walsh_parseval]
    _ ≤ (Fintype.card (Dom d) : ℝ)⁻¹ ^ 2 *
        ((2 : ℝ) ^ d * ((2 : ℝ) ^ d * (d : ℝ) ^ 2)) := by
      gcongr
    _ = 1 / 4 := by
      rw [domain_card]
      push_cast
      field_simp [hn, hdR]
      ring

theorem correlation_energy_pair {d : ℕ} (hd : 0 < d)
    (f : Dom d → ℝ) (hf : ∀ u, |f u| ≤ 1) :
    (∑ ra : (Fin d → ZMod 2) × ZMod 2,
      ip (half 0 f) (half 0 (cMP ra.1 ra.2)) ^ 2) ≤ 1 / 2 := by
  have he := correlation_energy_zero hd f hf
  have hm (r : Fin d → ZMod 2) (a : ZMod 2) :
      ip (half 0 f) (half 0 (cMP r a)) ^ 2 =
        ip (half 0 f) (half 0 (cMP r 0)) ^ 2 := by
    rw [← sq_abs (ip (half 0 f) (half 0 (cMP r a))), correlation_abs_mask,
      sq_abs]
  simp only [Fintype.sum_prod_type, sum_zmod_two, hm, sum_add_distrib]
  linarith

theorem fg_abs_le {d : ℕ} (g : Dom d → ℝ → ℝ)
    (hg : ∀ u y, (y = 1 ∨ y = -1) → (g u y = 1 ∨ g u y = -1)) :
    ∀ u, |fg g u| ≤ 1 := by
  intro u
  rcases hg u 1 (Or.inl rfl) with h1 | h1 <;>
    rcases hg u (-1) (Or.inr rfl) with h2 | h2 <;> norm_num [fg, h1, h2]

end MPProof


open Finset PrivLearn.MaskedParity
namespace MPProof

 theorem bad_count_energy {I : Type*} [Fintype I] (c : I → ℝ)
    (ε : ℝ) (hε : 0 < ε) (henergy : ∑ i, c i ^ 2 ≤ 1 / 2) :
    ((univ.filter fun i => ε ≤ |c i|).card : ℝ) * ε ^ 2 ≤ 1 / 2 := by
  classical
  calc
    _ = ∑ i ∈ univ.filter (fun i => ε ≤ |c i|), ε ^ 2 := by simp
    _ ≤ ∑ i ∈ univ.filter (fun i => ε ≤ |c i|), c i ^ 2 := by
      apply sum_le_sum
      intro i hi
      have h := (mem_filter.mp hi).2
      nlinarith [sq_abs (c i), abs_nonneg (c i)]
    _ ≤ ∑ i, c i ^ 2 := by
      apply sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
      intro i _ _
      positivity
    _ ≤ _ := henergy

theorem union_bad_count {I : Type*} [Fintype I] (t : ℕ) (c : Fin t → I → ℝ)
    (ε : ℝ) (hε : 0 < ε) (he : ∀ k, ∑ i, c k i ^ 2 ≤ 1 / 2) :
    ((univ.filter fun i => ¬ ∀ k, |c k i| < ε).card : ℝ) * ε ^ 2 ≤ (t : ℝ) / 2 := by
  classical
  let B : Fin t → Finset I := fun k => univ.filter fun i => ε ≤ |c k i|
  have hset : (univ.filter fun i => ¬ ∀ k, |c k i| < ε) = univ.biUnion B := by
    ext i
    simp [B, not_forall, not_lt]
  have hc : ((univ.biUnion B).card : ℝ) ≤ ∑ k, ((B k).card : ℝ) := by
    exact_mod_cast (card_biUnion_le (s := univ) (t := B))
  rw [hset]
  calc
    _ ≤ (∑ k, ((B k).card : ℝ)) * ε ^ 2 := mul_le_mul_of_nonneg_right hc (sq_nonneg ε)
    _ = ∑ k, ((B k).card : ℝ) * ε ^ 2 := by rw [sum_mul]
    _ ≤ ∑ _k : Fin t, (1 : ℝ) / 2 := by
      apply sum_le_sum
      intro k _
      exact bad_count_energy (c k) ε hε (he k)
    _ = _ := by simp; ring

theorem good_count_scaled {I : Type*} [Fintype I] (t : ℕ) (c : Fin t → I → ℝ)
    (ε : ℝ) (hε : 0 < ε) (he : ∀ k, ∑ i, c k i ^ 2 ≤ 1 / 2) :
    ((Fintype.card I : ℝ) - ((univ.filter fun i => ∀ k, |c k i| < ε).card : ℝ)) *
      ε ^ 2 ≤ (t : ℝ) / 2 := by
  classical
  have hu := union_bad_count t c ε hε he
  have hp := card_filter_add_card_filter_not (s := (univ : Finset I))
    (fun i => ∀ k, |c k i| < ε)
  have hpR : ((univ.filter fun i => ∀ k, |c k i| < ε).card : ℝ) +
      ((univ.filter fun i => ¬ ∀ k, |c k i| < ε).card : ℝ) = Fintype.card I := by
    exact_mod_cast hp
  have hid : (Fintype.card I : ℝ) - ((univ.filter fun i => ∀ k, |c k i| < ε).card : ℝ) =
      ((univ.filter fun i => ¬ ∀ k, |c k i| < ε).card : ℝ) := by linarith
  rw [hid]
  exact hu

theorem threshold_powers (d : ℕ) :
    ((2 : ℝ) ^ ((d : ℝ) / 3)) ^ 2 * (2 : ℝ) ^ ((d : ℝ) / 3 + 2) =
      2 * (2 : ℝ) ^ (d + 1) := by
  calc
    _ = (2 : ℝ) ^ (((d : ℝ) / 3) * 2 + ((d : ℝ) / 3 + 2)) := by
      conv_rhs => rw [Real.rpow_add (by norm_num), Real.rpow_mul (by norm_num), Real.rpow_two]
    _ = (2 : ℝ) ^ ((d : ℝ) + 2) := by congr 1; ring
    _ = 2 * (2 : ℝ) ^ (d + 1) := by
      rw [show (d : ℝ) + 2 = ((d + 1 : ℕ) : ℝ) + 1 by push_cast; ring,
        Real.rpow_add (by norm_num), Real.rpow_natCast, Real.rpow_one]
      ring

theorem good_fraction {d : ℕ} (hd : 0 < d) (t : ℕ)
    (g : Fin t → Dom d → ℝ → ℝ)
    (hg : ∀ k u y, (y = 1 ∨ y = -1) → (g k u y = 1 ∨ g k u y = -1)) :
    1 - (t : ℝ) / (2 : ℝ) ^ ((d : ℝ) / 3 + 2) ≤
      ((univ.filter fun ra : (Fin d → ZMod 2) × ZMod 2 =>
        ∀ k, |ip (half 0 (fg (g k))) (half 0 (cMP ra.1 ra.2))| <
          1 / (2 : ℝ) ^ ((d : ℝ) / 3)).card : ℝ) / (2 : ℝ) ^ (d + 1) := by
  classical
  let c : Fin t → ((Fin d → ZMod 2) × ZMod 2) → ℝ := fun k ra =>
    ip (half 0 (fg (g k))) (half 0 (cMP ra.1 ra.2))
  let R : ℝ := (2 : ℝ) ^ ((d : ℝ) / 3)
  let S : ℝ := (2 : ℝ) ^ ((d : ℝ) / 3 + 2)
  let N : ℝ := (2 : ℝ) ^ (d + 1)
  let G : ℝ := ((univ.filter fun ra => ∀ k, |c k ra| < 1 / R).card : ℝ)
  have hR : 0 < R := by dsimp [R]; positivity
  have hS : 0 < S := by dsimp [S]; positivity
  have hN : 0 < N := by dsimp [N]; positivity
  have hp : R ^ 2 * S = 2 * N := threshold_powers d
  have hu := good_count_scaled t c (1 / R) (by positivity)
    (fun k => correlation_energy_pair hd (fg (g k)) (fg_abs_le (g k) (hg k)))
  rw [card_pairs] at hu
  push_cast at hu
  change (N - G) * (1 / R) ^ 2 ≤ (t : ℝ) / 2 at hu
  have hbad : N - G ≤ (t : ℝ) / 2 * R ^ 2 := by
    apply (div_le_iff₀ (sq_pos_of_pos hR)).mp
    simpa only [div_pow, one_pow, mul_one_div] using hu
  change 1 - (t : ℝ) / S ≤ G / N
  apply (le_div_iff₀ hN).mpr
  apply (le_of_mul_le_mul_right ?_ hS)
  have hh := mul_le_mul_of_nonneg_right hbad hS.le
  have hc : ((1 - (t : ℝ) / S) * N) * S = (S - t) * N := by
    field_simp
  rw [hc]
  nlinarith [hp]

end MPProof


open Finset PrivLearn.MaskedParity MPProof

/-- **Theorem 5.16** (p. 27). Let `d` be a power of two and let the examples be uniform on the
domain `{0,1}^d × {0,1}^{log d} × {0,1}`.

1. There is an adaptive SQ learner for MASKED-PARITY with two rounds (`d` queries, then one), all
   queries `{0,1}`-valued and of tolerance at least `1/(4d+1)`, that outputs the target concept
   `c_{r,a}` for every target and every valid answers of the SQ oracle.
2. The oracle `𝒪` is a valid SQ oracle for every target (answers within `τ` of the true value for
   every query and every `τ > 0`), and every nonadaptive SQ learner making `t` queries, with values
   `±1` on labels `±1` and tolerances at least `2^{−d/3}`, run against `𝒪` on a target `c_{r̄,ā}`
   drawn uniformly from the `2^{d+1}` concepts, outputs a hypothesis `h` with
   `err(c_{r̄,ā}, h) ≥ 1/4` with probability at least `1/2 − t/2^{d/3+2}`. -/
theorem solution {d : ℕ} (hd : ∃ m : ℕ, d = 2 ^ m) :
    (∃ L : TwoRoundSQLearner (Dom d) d 1,
      (∀ j u y, L.q₁ j u y = 0 ∨ L.q₁ j u y = 1) ∧
      (∀ ans k u y, L.q₂ ans k u y = 0 ∨ L.q₂ ans k u y = 1) ∧
      (∀ j, 1 / (4 * (d : ℝ) + 1) ≤ L.τ₁ j) ∧
      (∀ ans k, 1 / (4 * (d : ℝ) + 1) ≤ L.τ₂ ans k) ∧
      ∀ (r : Fin d → ZMod 2) (a : ZMod 2) (ans₁ : Fin d → ℝ) (ans₂ : Fin 1 → ℝ),
        (∀ j, IsLabeledSQAnswer (cMP r a) (L.q₁ j) (L.τ₁ j) (ans₁ j)) →
        (∀ k, IsLabeledSQAnswer (cMP r a) (L.q₂ ans₁ k) (L.τ₂ ans₁ k) (ans₂ k)) →
        L.out ans₁ ans₂ = cMP r a) ∧
    (∀ (r : Fin d → ZMod 2) (a : ZMod 2) (g : Dom d → ℝ → ℝ) (τ : ℝ), 0 < τ →
      IsLabeledSQAnswer (cMP r a) g τ (oracleO r a g τ)) ∧
    (∀ (t : ℕ) (L : NonadaptiveSQLearner (Dom d) t),
      (∀ k, 1 / (2 : ℝ) ^ ((d : ℝ) / 3) ≤ L.τ k) →
      (∀ k u y, (y = 1 ∨ y = -1) → (L.q k u y = 1 ∨ L.q k u y = -1)) →
      1 / 2 - (t : ℝ) / (2 : ℝ) ^ ((d : ℝ) / 3 + 2) ≤
        ((Finset.univ.filter fun ra : (Fin d → ZMod 2) × ZMod 2 =>
            1 / 4 ≤ errMP (cMP ra.1 ra.2)
              (L.out fun k => oracleO ra.1 ra.2 (L.q k) (L.τ k))).card : ℝ) /
          (2 : ℝ) ^ (d + 1))  := by
  have hdpos : 0 < d := by
    obtain ⟨m, rfl⟩ := hd
    positivity
  refine ⟨?_, oracle_valid_all, ?_⟩
  · refine ⟨AMP d, ?_, ?_, ?_, ?_, ?_⟩
    · intro j u y
      simp only [AMP, gRound1]
      split_ifs <;> simp
    · intro ans k u y
      simp only [AMP, gRound2]
      split_ifs <;> simp
    · intro j
      exact le_rfl
    · intro ans k
      exact amp_tolerance hdpos
    · intro r a ans₁ ans₂ h₁ h₂
      exact amp_exact hdpos r a ans₁ ans₂ h₁ h₂
  · intro t L hτ hq
    have hg := good_fraction hdpos t L.q hq
    have hf := failure_count hdpos t L hτ
    have hp : (0 : ℝ) < (2 : ℝ) ^ (d + 1) := by positivity
    have hf' := (div_le_div_iff_of_pos_right hp).2 hf
    rw [mul_div_assoc] at hf'
    have ht : (0 : ℝ) ≤ (t : ℝ) / (2 : ℝ)^((d : ℝ)/3+2) := by positivity
    linarith



namespace PrivLearn.MaskedParity

/-- **Theorem 5.16** (p. 27). Let `d` be a power of two and let the examples be uniform on the
domain `{0,1}^d × {0,1}^{log d} × {0,1}`.

1. There is an adaptive SQ learner for MASKED-PARITY with two rounds (`d` queries, then one), all
   queries `{0,1}`-valued and of tolerance at least `1/(4d+1)`, that outputs the target concept
   `c_{r,a}` for every target and every valid answers of the SQ oracle.
2. The oracle `𝒪` is a valid SQ oracle for every target (answers within `τ` of the true value for
   every query and every `τ > 0`), and every nonadaptive SQ learner making `t` queries, with values
   `±1` on labels `±1` and tolerances at least `2^{−d/3}`, run against `𝒪` on a target `c_{r̄,ā}`
   drawn uniformly from the `2^{d+1}` concepts, outputs a hypothesis `h` with
   `err(c_{r̄,ā}, h) ≥ 1/4` with probability at least `1/2 − t/2^{d/3+2}`. -/
theorem theorem_5_16 {d : ℕ} (hd : ∃ m : ℕ, d = 2 ^ m) :
    (∃ L : TwoRoundSQLearner (Dom d) d 1,
      (∀ j u y, L.q₁ j u y = 0 ∨ L.q₁ j u y = 1) ∧
      (∀ ans k u y, L.q₂ ans k u y = 0 ∨ L.q₂ ans k u y = 1) ∧
      (∀ j, 1 / (4 * (d : ℝ) + 1) ≤ L.τ₁ j) ∧
      (∀ ans k, 1 / (4 * (d : ℝ) + 1) ≤ L.τ₂ ans k) ∧
      ∀ (r : Fin d → ZMod 2) (a : ZMod 2) (ans₁ : Fin d → ℝ) (ans₂ : Fin 1 → ℝ),
        (∀ j, IsLabeledSQAnswer (cMP r a) (L.q₁ j) (L.τ₁ j) (ans₁ j)) →
        (∀ k, IsLabeledSQAnswer (cMP r a) (L.q₂ ans₁ k) (L.τ₂ ans₁ k) (ans₂ k)) →
        L.out ans₁ ans₂ = cMP r a) ∧
    (∀ (r : Fin d → ZMod 2) (a : ZMod 2) (g : Dom d → ℝ → ℝ) (τ : ℝ), 0 < τ →
      IsLabeledSQAnswer (cMP r a) g τ (oracleO r a g τ)) ∧
    (∀ (t : ℕ) (L : NonadaptiveSQLearner (Dom d) t),
      (∀ k, 1 / (2 : ℝ) ^ ((d : ℝ) / 3) ≤ L.τ k) →
      (∀ k u y, (y = 1 ∨ y = -1) → (L.q k u y = 1 ∨ L.q k u y = -1)) →
      1 / 2 - (t : ℝ) / (2 : ℝ) ^ ((d : ℝ) / 3 + 2) ≤
        ((Finset.univ.filter fun ra : (Fin d → ZMod 2) × ZMod 2 =>
            1 / 4 ≤ errMP (cMP ra.1 ra.2)
              (L.out fun k => oracleO ra.1 ra.2 (L.q k) (L.τ k))).card : ℝ) /
          (2 : ℝ) ^ (d + 1)) := _root_.solution hd

end PrivLearn.MaskedParity
