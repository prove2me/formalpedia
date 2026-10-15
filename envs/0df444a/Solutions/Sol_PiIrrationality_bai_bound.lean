-- Prove2me | solution 1 for PiIrrationality.bai_bound
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T20:18:55.521976+00:00
-- url     : https://prove2.me/submissions/cf03921d-15b8-42a6-86ba-468ad03f50b2

import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Definitions.Def_PiIrrationality_UpperBound
import Definitions.Def_PiIrrationality_BaiForms
import Theorems.Thm_PiIrrationality_Bai_linearForm
import Theorems.Thm_PiIrrationality_Bai_integral_bound
import Theorems.Thm_PiIrrationality_Bai_coef_le
import Theorems.Thm_PiIrrationality_Bai_coef_ge
import Theorems.Thm_PiIrrationality_Bai_lam_certificate
import Theorems.Thm_PiIrrationality_Bai_phi_lower_lam_of_MediumPNT
import Theorems.Thm_PiIrrationality_Bai_final_numeric
import Theorems.Thm_PiIrrationality_ratio_linearForm_upperBound
import Theorems.Thm_PiIrrationality_lcmUpto_le_exp
import Theorems.Thm_MediumPNT

/-!
# Bai's bound `μ(π) ≤ 7.101862832357` (campaign 19dd5584 entry): the reduction

Y. Bai, *The irrationality measure of π is at most 7.101862832357*, arXiv:2609.11276.

Children: `Bai.linearForm` (Prop. 2.7), `Bai.integral_bound`, `Bai.coef_le`, `Bai.coef_ge`,
`Bai.lam_certificate`, `Bai.phi_lower_lam_of_MediumPNT`, `Bai.final_numeric`, and the proved generic nodes e178b375
(`ratio_linearForm_upperBound`), ced40b41 (`lcmUpto_le_exp`) and 7cfa31c8 (`MediumPNT`).
All slack (`δ = 10⁻¹⁶` in the lcm and prime-saving bounds, and the constants 4, 8, 16, 32) is absorbed
into the `10⁵ δ` that `final_numeric` reserves, eventually in `n`.
-/

set_option autoImplicit false

open Filter

namespace PiIrrationality.BaiAsm

/-- `U_n` of Proposition 2.7 (junk value `0` at `n = 0`). -/
noncomputable def U (n : ℕ) : ℤ :=
  if h : 1 ≤ n then (Bai.linearForm n h).choose else 0

/-- `V_n` of Proposition 2.7 (junk value `0` at `n = 0`). -/
noncomputable def V (n : ℕ) : ℤ :=
  if h : 1 ≤ n then (Bai.linearForm n h).choose_spec.choose else 0

lemma UV_spec (n : ℕ) (hn : 1 ≤ n) :
    (Bai.M n : ℂ) * Bai.J n = (U n : ℂ) + (V n : ℂ) * (Real.pi : ℂ) ∧
      (V n : ℝ) = -(Bai.M n * 25 ^ n * 2 ^ (3716 * n) * (Bai.coef n : ℝ) / 4) := by
  simp only [U, V, dif_pos hn]
  exact (Bai.linearForm n hn).choose_spec.choose_spec

lemma Phi_pos (n : ℕ) : 0 < Bai.Phi n := by
  unfold Bai.Phi
  refine Finset.prod_pos fun p hp => ?_
  simp only [Bai.deletedPrimes, Finset.mem_filter] at hp
  exact hp.2.1.pos

lemma M_pos (n : ℕ) : 0 < Bai.M n := by
  have hL : (0 : ℝ) < (Nat.lcmUpto (7430 * n) : ℝ) := by exact_mod_cast Nat.lcmUpto_pos _
  have hP : (0 : ℝ) < (Bai.Phi n : ℝ) := by exact_mod_cast Phi_pos n
  unfold Bai.M
  exact div_pos (mul_pos (by norm_num) hL) (mul_pos (by positivity) hP)

/-- `|U_n + V_n π| = M_n ‖J_n‖`. -/
lemma lam_abs (n : ℕ) (hn : 1 ≤ n) :
    |(U n : ℝ) + V n * Real.pi| = Bai.M n * ‖Bai.J n‖ := by
  have h1 := (UV_spec n hn).1
  have hc : (((U n : ℝ) + V n * Real.pi : ℝ) : ℂ) = (Bai.M n : ℂ) * Bai.J n := by
    rw [h1]; push_cast; ring
  rw [← Real.norm_eq_abs, ← Complex.norm_real, hc, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (M_pos n)]

/-- `|V_n| = M_n 25^n 2^{3716n} coef_n / 4`. -/
lemma V_abs (n : ℕ) (hn : 1 ≤ n) :
    |(V n : ℝ)| = Bai.M n * 25 ^ n * 2 ^ (3716 * n) * (Bai.coef n : ℝ) / 4 := by
  rw [(UV_spec n hn).2, abs_neg, abs_of_nonneg]
  exact div_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (M_pos n).le (by positivity)) (by positivity))
    (Nat.cast_nonneg _)) (by norm_num)

lemma pow_eq_exp (x : ℝ) (hx : 0 < x) (k : ℕ) : x ^ k = Real.exp (k * Real.log x) := by
  rw [Real.exp_nat_mul, Real.exp_log hx]

lemma ev_exp_ge (κ C : ℝ) (hκ : 0 < κ) : ∀ᶠ n : ℕ in atTop, C ≤ Real.exp (κ * n) :=
  (Real.tendsto_exp_atTop.comp (tendsto_natCast_atTop_atTop.const_mul_atTop hκ)).eventually_ge_atTop C

/-- ced40b41 (passed as the hypothesis `hLcm`) at `m = 7430 n`. -/
lemma lcm_ev (hLcm : type_of% @PiIrrationality.lcmUpto_le_exp) (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ n : ℕ in atTop, (Nat.lcmUpto (7430 * n) : ℝ) ≤ Real.exp ((1 + δ) * (7430 * (n : ℝ))) := by
  have ht : Tendsto (fun n : ℕ => 7430 * n) atTop atTop :=
    tendsto_atTop_atTop.2 fun b => ⟨b, fun n hn => by omega⟩
  filter_upwards [ht.eventually (hLcm δ hδ)] with n hn
  simpa only [Nat.cast_mul, Nat.cast_ofNat] using hn

/-- A constant factor is absorbed by a positive rate. -/
lemma absorb (K X κ s : ℝ) (n : ℕ) (hK : K ≤ Real.exp (κ * n)) (hs : s = X + κ) :
    K * Real.exp (X * n) ≤ Real.exp (s * n) := by
  rw [hs, add_mul, Real.exp_add, mul_comm (Real.exp (X * n))]
  exact mul_le_mul_of_nonneg_right hK (Real.exp_pos _).le

/-- `M_n ≤ 16 exp(Mb n)` from the lcm and prime-saving bounds. -/
lemma M_le (n : ℕ) (δ₁ δ₂ ω : ℝ)
    (hL : (Nat.lcmUpto (7430 * n) : ℝ) ≤ Real.exp ((1 + δ₁) * (7430 * (n : ℝ))))
    (hP : Real.exp ((ω - δ₂) * (n : ℝ)) ≤ (Bai.Phi n : ℝ)) :
    Bai.M n ≤ 16 * Real.exp ((7430 + 7430 * δ₁ - 4645 * Real.log 2 - ω + δ₂) * n) := by
  unfold Bai.M
  rw [pow_eq_exp 2 two_pos (4645 * n)]
  calc (2 : ℝ) ^ 4 * (Nat.lcmUpto (7430 * n) : ℝ) /
        (Real.exp (((4645 * n : ℕ) : ℝ) * Real.log 2) * (Bai.Phi n : ℝ))
      ≤ 2 ^ 4 * Real.exp ((1 + δ₁) * (7430 * (n : ℝ))) /
        (Real.exp (((4645 * n : ℕ) : ℝ) * Real.log 2) * Real.exp ((ω - δ₂) * (n : ℝ))) := by
        gcongr
    _ = 16 * Real.exp ((7430 + 7430 * δ₁ - 4645 * Real.log 2 - ω + δ₂) * n) := by
        have e : (1 + δ₁) * (7430 * (n : ℝ)) +
            -(((4645 * n : ℕ) : ℝ) * Real.log 2 + (ω - δ₂) * (n : ℝ)) =
            (7430 + 7430 * δ₁ - 4645 * Real.log 2 - ω + δ₂) * n := by
          push_cast; ring
        rw [div_eq_mul_inv, ← Real.exp_add, ← Real.exp_neg, mul_assoc, ← Real.exp_add, e]
        norm_num

/-- `|V_n| ≤ 4 exp((Mb + log 25 + 3716 log 2 + c_up) n)`. -/
lemma V_le (n : ℕ) (Mb cu : ℝ) (hM : Bai.M n ≤ 16 * Real.exp (Mb * n))
    (hC : (Bai.coef n : ℝ) ≤ Real.exp (cu * n)) :
    Bai.M n * 25 ^ n * 2 ^ (3716 * n) * (Bai.coef n : ℝ) / 4 ≤
      4 * Real.exp ((Mb + Real.log 25 + 3716 * Real.log 2 + cu) * n) := by
  have hM0 := (M_pos n).le
  calc Bai.M n * 25 ^ n * 2 ^ (3716 * n) * (Bai.coef n : ℝ) / 4
      ≤ 16 * Real.exp (Mb * n) * 25 ^ n * 2 ^ (3716 * n) * Real.exp (cu * n) / 4 := by gcongr
    _ = 4 * Real.exp ((Mb + Real.log 25 + 3716 * Real.log 2 + cu) * n) := by
        rw [pow_eq_exp 25 (by norm_num) n, pow_eq_exp 2 two_pos (3716 * n)]
        rw [show (Mb + Real.log 25 + 3716 * Real.log 2 + cu) * (n : ℝ) =
            Mb * n + (n * Real.log 25) + (((3716 * n : ℕ) : ℝ) * Real.log 2) + cu * n by
          push_cast; ring]
        rw [Real.exp_add, Real.exp_add, Real.exp_add]
        ring

/-- The ratio bound `M_n ‖J_n‖ ≤ exp(-g n) |V_n|`. -/
lemma ratio_le (n : ℕ) (T cl g κ : ℝ) (hJ : ‖Bai.J n‖ ≤ 2 * Real.exp (-(T * n)))
    (hC : Real.exp (cl * n) ≤ (Bai.coef n : ℝ)) (h8 : 8 ≤ Real.exp (κ * n))
    (hg : -g + Real.log 25 + 3716 * Real.log 2 + cl = -T + κ) :
    Bai.M n * ‖Bai.J n‖ ≤
      Real.exp (-(g * n)) * (Bai.M n * 25 ^ n * 2 ^ (3716 * n) * (Bai.coef n : ℝ) / 4) := by
  have hM := M_pos n
  have key : 2 * Real.exp (-(T * n)) ≤
      Real.exp (-(g * n)) * 25 ^ n * 2 ^ (3716 * n) * Real.exp (cl * n) / 4 := by
    rw [pow_eq_exp 25 (by norm_num) n, pow_eq_exp 2 two_pos (3716 * n)]
    have e : Real.exp (-(g * n)) * Real.exp (n * Real.log 25) *
        Real.exp (((3716 * n : ℕ) : ℝ) * Real.log 2) * Real.exp (cl * n) =
        Real.exp ((-T + κ) * n) := by
      rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add, ← hg]
      congr 1
      push_cast; ring
    rw [e]
    have h := absorb 8 (-T) κ (-T + κ) n h8 rfl
    rw [neg_mul] at h
    linarith
  calc Bai.M n * ‖Bai.J n‖ ≤ Bai.M n * (2 * Real.exp (-(T * n))) :=
        mul_le_mul_of_nonneg_left hJ hM.le
    _ ≤ Bai.M n * (Real.exp (-(g * n)) * 25 ^ n * 2 ^ (3716 * n) * Real.exp (cl * n) / 4) :=
        mul_le_mul_of_nonneg_left key hM.le
    _ ≤ Bai.M n * (Real.exp (-(g * n)) * 25 ^ n * 2 ^ (3716 * n) * (Bai.coef n : ℝ) / 4) :=
        mul_le_mul_of_nonneg_left (by gcongr) hM.le
    _ = Real.exp (-(g * n)) * (Bai.M n * 25 ^ n * 2 ^ (3716 * n) * (Bai.coef n : ℝ) / 4) := by ring

/-- The rate `s` (size of `V_n`), with `ω = ω₀` and `δ = 10⁻¹⁶`. -/
noncomputable def sB : ℝ :=
  7430 - 929 * Real.log 2 - 1202.5657733612916 + Real.log 25 + 15979.97420422751 + 100000 * 1e-16

/-- The rate `t` (smallness of `Λ_n`). -/
noncomputable def tB : ℝ :=
  6542.209753096835 - (7430 - 4645 * Real.log 2 - 1202.5657733612916) - 100000 * 1e-16

/-- The rate `g` (ratio `|Λ_n|/|V_n|`). -/
noncomputable def gB : ℝ :=
  6542.209753096835 + 3716 * Real.log 2 + Real.log 25 + 15979.974204227497 - 100000 * 1e-16

/-- The slack rate left after `δ₁ = δ₂ = 10⁻¹⁶`. -/
noncomputable def κ₁ : ℝ := 100000 * 1e-16 - 7430 * 1e-16 - 1e-16

/-- The Mb of `M_le` at `δ₁ = δ₂ = 10⁻¹⁶`, `ω = ω₀`. -/
noncomputable def Mb : ℝ := 7430 + 7430 * 1e-16 - 4645 * Real.log 2 - 1202.5657733612916 + 1e-16

/-- Prime saving at `ω₀ = 1202.5657733612916`, from the children `Bai.lam_certificate` (an admissible table
with `λ_{10^16} ≥ ω₀`) and `Bai.phi_lower_lam_of_MediumPNT` (prime saving `λ_K(L) - δ` for any admissible table). -/
theorem phi_lower_of_MediumPNT (hPNT : type_of% @MediumPNT) (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ n : ℕ in atTop,
      Real.exp ((1202.5657733612916 - δ) * (n : ℝ)) ≤ (PiIrrationality.Bai.Phi n : ℝ) := by
  obtain ⟨L, hL, hc, hlam⟩ := PiIrrationality.Bai.lam_certificate
  filter_upwards [PiIrrationality.Bai.phi_lower_lam_of_MediumPNT L hL hc hPNT (10 ^ 16) δ hδ] with n hn
  refine le_trans (Real.exp_le_exp.2 ?_) hn
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  nlinarith

/-- **Bai's bound from the three generic statements.** The hypotheses are the exact statements of the
platform nodes e178b375 (`hRatio`), ced40b41 (`hLcm`) and 7cfa31c8 (`hPNT`); this theorem itself uses
no child node directly; every child enters through these three hypotheses or a `Theorems` import. -/
theorem bai_bound_of (hRatio : type_of% @PiIrrationality.ratio_linearForm_upperBound)
    (hLcm : type_of% @PiIrrationality.lcmUpto_le_exp) (hPNT : type_of% @MediumPNT) :
    PiIrrationality.UpperBound (7.101862832357 : ℝ) := by
  obtain ⟨hs, ht, hsg, hB1, hB2⟩ := PiIrrationality.Bai.final_numeric (1202.5657733612916 : ℝ) (1e-16 : ℝ)
    sB tB gB (by norm_num) (by norm_num) (by norm_num) le_rfl rfl rfl rfl
  obtain ⟨N0, hN0⟩ := PiIrrationality.Bai.coef_ge
  have hκ : (0 : ℝ) < κ₁ := by unfold κ₁; norm_num
  have hlcm := lcm_ev hLcm (1e-16) (by norm_num)
  have hphi := phi_lower_of_MediumPNT hPNT (1e-16) (by norm_num)
  have hK1 := ev_exp_ge κ₁ 32 hκ
  have hK2 := ev_exp_ge (100000 * 1e-16) 8 (by norm_num)
  have hn1 : ∀ᶠ n : ℕ in atTop, 1 ≤ n := eventually_ge_atTop 1
  have hnN : ∀ᶠ n : ℕ in atTop, N0 ≤ n := eventually_ge_atTop N0
  refine hRatio U V sB tB gB _ hs ht hsg hB1 hB2 ?_ ?_ ?_
  · filter_upwards [hn1, hnN, hlcm, hphi, hK1] with n h1 hN hL hP hK
    have hM : PiIrrationality.Bai.M n ≤ 16 * Real.exp (Mb * n) :=
      M_le n 1e-16 1e-16 1202.5657733612916 hL hP
    have hCpos : 0 < (PiIrrationality.Bai.coef n : ℝ) := lt_of_lt_of_le (Real.exp_pos _) (hN0 n hN)
    refine ⟨?_, ?_⟩
    · intro h0
      have hv := (UV_spec n h1).2
      rw [h0, Int.cast_zero] at hv
      have : 0 < PiIrrationality.Bai.M n * 25 ^ n * 2 ^ (3716 * n) *
          (PiIrrationality.Bai.coef n : ℝ) / 4 :=
        div_pos (mul_pos (mul_pos (mul_pos (M_pos n) (by positivity)) (by positivity)) hCpos)
          (by norm_num)
      linarith
    · rw [V_abs n h1]
      calc _ ≤ 4 * Real.exp ((Mb + Real.log 25 + 3716 * Real.log 2 + 15979.97420422751) * n) :=
            V_le n _ _ hM (PiIrrationality.Bai.coef_le n)
        _ ≤ Real.exp (sB * n) :=
            absorb 4 _ κ₁ sB n (le_trans (by norm_num) hK) (by unfold sB Mb κ₁; ring)
  · filter_upwards [hn1, hlcm, hphi, hK1] with n h1 hL hP hK
    rw [lam_abs n h1]
    have hM : PiIrrationality.Bai.M n ≤ 16 * Real.exp (Mb * n) :=
      M_le n 1e-16 1e-16 1202.5657733612916 hL hP
    have hJ := PiIrrationality.Bai.integral_bound n
    calc PiIrrationality.Bai.M n * ‖PiIrrationality.Bai.J n‖
        ≤ (16 * Real.exp (Mb * n)) * (2 * Real.exp (-(6542.209753096835 * (n : ℝ)))) :=
          mul_le_mul hM hJ (norm_nonneg _) (by positivity)
      _ = 32 * Real.exp ((Mb - 6542.209753096835) * n) := by
          rw [sub_mul, sub_eq_add_neg, Real.exp_add]; ring
      _ ≤ Real.exp ((-tB) * n) :=
          absorb 32 _ κ₁ (-tB) n hK (by unfold tB Mb κ₁; ring)
      _ = Real.exp (-(tB * n)) := by rw [neg_mul]
  · filter_upwards [hn1, hnN, hK2] with n h1 hN hK
    rw [lam_abs n h1, V_abs n h1]
    exact ratio_le n 6542.209753096835 15979.974204227497 gB (100000 * 1e-16)
      (PiIrrationality.Bai.integral_bound n) (hN0 n hN) hK (by unfold gB; ring)

end PiIrrationality.BaiAsm

/-- **Bai's bound**: the irrationality measure of `π` is at most `7.101862832357`
(Y. Bai, arXiv:2609.11276), from the six Bai leaves and the proved generic nodes
e178b375, ced40b41 and 7cfa31c8. -/
theorem solution : PiIrrationality.UpperBound (7.101862832357 : ℝ) := by
  exact PiIrrationality.BaiAsm.bai_bound_of PiIrrationality.ratio_linearForm_upperBound
    PiIrrationality.lcmUpto_le_exp MediumPNT
