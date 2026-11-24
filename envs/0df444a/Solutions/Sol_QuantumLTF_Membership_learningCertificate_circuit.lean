-- Prove2me | solution 1 for QuantumLTF.Membership.learningCertificate_circuit
-- status  : ACCEPTED   (prove)
-- author  : @Robin Kothari
-- created : 2026-11-24T23:34:12.73319+00:00
-- url     : https://prove2.me/submissions/877245f8-9310-47bf-88f6-bffe95a74bbf

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Circuit
import Definitions.Def_QuantumLTF_Membership_LearningCertificate
import Definitions.Def_QuantumLTF_Membership_Leps
import Definitions.Def_QuantumLTF_Membership_Uncontrolled
import Definitions.Def_QuantumLTF_Membership_disagree
import Definitions.Def_QuantumLTF_Membership_gates12
import Definitions.Def_QuantumLTF_Membership_ltf
import Definitions.Def_QuantumLTF_Membership_memOracle
import Definitions.Def_QuantumLTF_Membership_readFp
import Definitions.Def_QuantumLTF_Membership_rho
import Theorems.Thm_QuantumLTF_Membership_theorem_3_1_parameters
import Theorems.Thm_QuantumLTF_Membership_theorem_3_3
import Theorems.Thm_QuantumLTF_Membership_uniform_dyadic_reference_direction
import Theorems.Thm_QuantumLTF_Membership_uniform_height_circuit
import Theorems.Thm_QuantumLTF_Membership_learningCertificate_assembly

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unusedSimpArgs false
-- ===== module Params =====

/-! Real-number bounds on the parameters of the assembly, all `O(Λ)`, `Λ = log(n/ε)`. -/

namespace LTFC

open Real

theorem log_le_self' {x : ℝ} (hx : 0 < x) : Real.log x ≤ x := by
  have := Real.log_le_sub_one_of_pos hx; linarith

theorem two_pow_ceil_le {y : ℝ} (hy : 1 ≤ y) :
    y ≤ (2 : ℝ) ^ ⌈Real.logb 2 y⌉₊ ∧ (2 : ℝ) ^ ⌈Real.logb 2 y⌉₊ ≤ 2 * y := by
  have hx0 : 0 ≤ Real.logb 2 y := Real.logb_nonneg (by norm_num) hy
  have hc1 := Nat.le_ceil (Real.logb 2 y)
  have hc2 := Nat.ceil_lt_add_one hx0
  rw [← Real.rpow_natCast]
  constructor
  · calc y = (2 : ℝ) ^ Real.logb 2 y := (Real.rpow_logb (by norm_num) (by norm_num) (by linarith)).symm
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by norm_num) hc1
  · calc (2 : ℝ) ^ (⌈Real.logb 2 y⌉₊ : ℝ) ≤ (2 : ℝ) ^ (Real.logb 2 y + 1) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) hc2.le
      _ = 2 * y := by
          rw [Real.rpow_add (by norm_num), Real.rpow_logb (by norm_num) (by norm_num) (by linarith),
            Real.rpow_one]; ring

theorem log_le_128 {x : ℝ} (hx0 : 0 < x) (hx : x ≤ 128) : Real.log x ≤ 5 := by
  have h := Real.log_two_lt_d9
  calc Real.log x ≤ Real.log 128 := Real.log_le_log hx0 hx
    _ = 7 * Real.log 2 := by rw [show (128 : ℝ) = 2 ^ 7 by norm_num, Real.log_pow]; norm_num
    _ ≤ 5 := by linarith

section P

variable {n : ℕ} {ε : ℝ} (hn : 2 ≤ n) (hε : 0 < ε) (hε2 : ε ≤ 1 / 2)

include hn hε hε2

theorem log_inv_eps_ge : Real.log 2 ≤ Real.log (1 / ε) := by
  apply Real.log_le_log (by norm_num); rw [le_div_iff₀ hε]; linarith

theorem log_two_gt : (0.69 : ℝ) < Real.log 2 := by have := Real.log_two_gt_d9; linarith

theorem Lam_split : Real.log (n / ε) = Real.log n + Real.log (1 / ε) := by
  rw [div_eq_mul_one_div, Real.log_mul (by positivity) (by positivity)]

theorem log_n_ge : Real.log 2 ≤ Real.log n := Real.log_le_log (by norm_num) (by exact_mod_cast hn)

theorem Lam_ge_one : 1 ≤ Real.log (n / ε) := by
  rw [Lam_split hn hε hε2]
  have := log_inv_eps_ge hn hε hε2; have := log_n_ge hn hε hε2; have := log_two_gt hn hε hε2
  linarith

theorem log_n_le : Real.log n ≤ Real.log (n / ε) := by
  rw [Lam_split hn hε hε2]; have := log_inv_eps_ge hn hε hε2; have := log_two_gt hn hε hε2; linarith

theorem log_eps_le : Real.log (1 / ε) ≤ Real.log (n / ε) := by
  rw [Lam_split hn hε hε2]; have := log_n_ge hn hε hε2; have := log_two_gt hn hε hε2; linarith

theorem Teps_bounds : 1 ≤ QuantumLTF.Membership.Teps ε ∧
    QuantumLTF.Membership.Teps ε ≤ 1 + Real.log (1 / ε) := by
  unfold QuantumLTF.Membership.Teps
  have hx := log_inv_eps_ge hn hε hε2
  have h2 := log_two_gt hn hε hε2
  constructor
  · rw [Real.le_sqrt (by norm_num) (by linarith)]; linarith
  · rw [Real.sqrt_le_left (by linarith)]; nlinarith

theorem Leps_bounds : 20 * QuantumLTF.Membership.Teps ε ≤ QuantumLTF.Membership.Leps ε ∧
    QuantumLTF.Membership.Leps ε ≤ 40 * (1 + Real.log (1 / ε)) := by
  obtain ⟨h1, h2⟩ := Teps_bounds hn hε hε2
  have := two_pow_ceil_le (y := 20 * QuantumLTF.Membership.Teps ε) (by linarith)
  unfold QuantumLTF.Membership.Leps
  constructor
  · exact this.1
  · linarith [this.2]

theorem Leps_ge_one : 1 ≤ QuantumLTF.Membership.Leps ε := by
  have := (Leps_bounds hn hε hε2).1; have := (Teps_bounds hn hε hε2).1; linarith

theorem Leps_le_Lam : QuantumLTF.Membership.Leps ε ≤ 80 * Real.log (n / ε) := by
  have h := (Leps_bounds hn hε hε2).2
  have := log_eps_le hn hε hε2; have := Lam_ge_one hn hε hε2
  have := log_inv_eps_ge hn hε hε2; have := log_two_gt hn hε hε2
  nlinarith

theorem log_Leps_zeta_le :
    Real.log (QuantumLTF.Membership.Leps ε / (ε / 100)) ≤ 110 * Real.log (1 / ε) := by
  have hL1 := Leps_ge_one hn hε hε2
  have hL2 := (Leps_bounds hn hε hε2).2
  have hx := log_inv_eps_ge hn hε hε2
  have h2 := log_two_gt hn hε hε2
  rw [show QuantumLTF.Membership.Leps ε / (ε / 100) = QuantumLTF.Membership.Leps ε * 100 * (1 / ε) by
    field_simp, Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by norm_num)]
  have h100 : Real.log 100 ≤ 5 := log_le_128 (by norm_num) (by norm_num)
  have := log_le_self' (show 0 < QuantumLTF.Membership.Leps ε by linarith)
  nlinarith

end P

end LTFC

namespace LTFC

open Real

noncomputable def epsG (n : ℕ) (ε : ℝ) : ℝ :=
  ε / (200 * (QuantumLTF.Membership.Leps ε + 1) * Real.sqrt n)

noncomputable def etaP (n : ℕ) (ε : ℝ) : ℝ :=
  QuantumLTF.Membership.rho n * epsG n ε / (48 * Real.pi * (3 * n + 1))

noncomputable def bP (n : ℕ) (ε : ℝ) : ℕ :=
  ⌈Real.logb 2 ((3 * n + 1) / (QuantumLTF.Membership.rho n * epsG n ε))⌉₊

noncomputable def PP (n : ℕ) (ε : ℝ) : ℕ := ⌈Real.logb 2 (1 / epsG n ε)⌉₊

theorem ceil_le_add_one {x : ℝ} (hx : 0 ≤ x) : (⌈x⌉₊ : ℝ) ≤ x + 1 := (Nat.ceil_lt_add_one hx).le

section P2

variable {n : ℕ} {ε : ℝ} (hn : 2 ≤ n) (hε : 0 < ε) (hε2 : ε ≤ 1 / 2)

include hn hε hε2

theorem sqrt_n_ge : 1 ≤ Real.sqrt n := by
  rw [Real.le_sqrt (by norm_num) (by positivity)]; norm_num; exact_mod_cast (by omega : 1 ≤ n)

theorem rho_bounds : 0 < QuantumLTF.Membership.rho n ∧ QuantumLTF.Membership.rho n ≤ 1 ∧
    1 / (80 * Real.sqrt n) ≤ QuantumLTF.Membership.rho n := by
  have hs := sqrt_n_ge hn hε hε2
  have h := two_pow_ceil_le (y := 40 * Real.sqrt n) (by linarith)
  unfold QuantumLTF.Membership.rho
  rw [inv_pow]
  refine ⟨by positivity, ?_, ?_⟩
  · apply inv_le_one_of_one_le₀; exact one_le_pow₀ (by norm_num)
  · rw [one_div]; apply inv_anti₀ (by positivity); linarith [h.2]

theorem epsG_pos : 0 < epsG n ε := by
  have := Leps_ge_one hn hε hε2; have := sqrt_n_ge hn hε hε2
  unfold epsG; positivity

theorem epsG_le : epsG n ε ≤ 1 / 400 := by
  have hL := Leps_ge_one hn hε hε2; have hs := sqrt_n_ge hn hε hε2
  unfold epsG
  rw [div_le_iff₀ (by positivity)]
  have : (2 : ℝ) ≤ (QuantumLTF.Membership.Leps ε + 1) * Real.sqrt n := by nlinarith
  nlinarith

theorem log_inv_epsG_le : Real.log (1 / epsG n ε) ≤ 90 * Real.log (n / ε) := by
  have hL := Leps_ge_one hn hε hε2; have hs := sqrt_n_ge hn hε hε2
  have hLL := Leps_le_Lam hn hε hε2
  have hΛ := Lam_ge_one hn hε hε2
  have hln := log_n_le hn hε hε2; have hle := log_eps_le hn hε hε2
  rw [show 1 / epsG n ε = 200 * (QuantumLTF.Membership.Leps ε + 1) * Real.sqrt n * (1 / ε) by
    unfold epsG; field_simp]
  rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by norm_num) (by positivity), Real.log_sqrt (by positivity)]
  have h200 : Real.log 200 ≤ 6 := by
    have h := Real.log_two_lt_d9
    calc Real.log 200 ≤ Real.log 256 := Real.log_le_log (by norm_num) (by norm_num)
      _ = 8 * Real.log 2 := by rw [show (256 : ℝ) = 2 ^ 8 by norm_num, Real.log_pow]; norm_num
      _ ≤ 6 := by linarith
  have := log_le_self' (show 0 < QuantumLTF.Membership.Leps ε + 1 by linarith)
  nlinarith

theorem log_inv_rho_le : Real.log (1 / QuantumLTF.Membership.rho n) ≤ 6 * Real.log (n / ε) := by
  obtain ⟨h0, h1, h2⟩ := rho_bounds hn hε hε2
  have hs := sqrt_n_ge hn hε hε2
  have hΛ := Lam_ge_one hn hε hε2
  have hln := log_n_le hn hε hε2
  have : Real.log (1 / QuantumLTF.Membership.rho n) ≤ Real.log (80 * Real.sqrt n) := by
    apply Real.log_le_log (by positivity)
    rw [div_le_iff₀ h0]; rw [div_le_iff₀ (by positivity)] at h2; linarith
  rw [Real.log_mul (by norm_num) (by positivity), Real.log_sqrt (by positivity)] at this
  have h80 : Real.log 80 ≤ 5 := log_le_128 (by norm_num) (by norm_num)
  nlinarith

theorem etaP_pos : 0 < etaP n ε := by
  have := (rho_bounds hn hε hε2).1; have := epsG_pos hn hε hε2
  unfold etaP; positivity

theorem etaP_lt : etaP n ε < 1 / 8 := by
  obtain ⟨h0, h1, _⟩ := rho_bounds hn hε hε2
  have he := epsG_pos hn hε hε2; have he2 := epsG_le hn hε hε2
  have hpi := Real.pi_gt_three
  unfold etaP
  rw [div_lt_iff₀ (by positivity)]
  have : (1 : ℝ) ≤ 3 * n + 1 := by have : (0 : ℝ) ≤ n := Nat.cast_nonneg n; linarith
  nlinarith [mul_le_mul h1 he2 he.le (by norm_num : (0:ℝ) ≤ 1)]

theorem log_inv_etaP_le : Real.log (1 / etaP n ε) ≤ 110 * Real.log (n / ε) := by
  obtain ⟨h0, h1, _⟩ := rho_bounds hn hε hε2
  have he := epsG_pos hn hε hε2
  have hΛ := Lam_ge_one hn hε hε2
  have hln := log_n_le hn hε hε2
  have h1' := log_inv_rho_le hn hε hε2
  have h2' := log_inv_epsG_le hn hε hε2
  have hpi := Real.pi_lt_four
  have hpi3 := Real.pi_gt_three
  have hnr : (2 : ℝ) ≤ n := by exact_mod_cast hn
  rw [show 1 / etaP n ε = (1 / QuantumLTF.Membership.rho n) * (1 / epsG n ε) *
      (48 * Real.pi * (3 * n + 1)) by unfold etaP; field_simp]
  rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity)]
  have h3 : Real.log (48 * Real.pi * (3 * n + 1)) ≤ 10 + Real.log n := by
    have : 48 * Real.pi * (3 * n + 1) ≤ 1024 * n := by nlinarith
    calc Real.log (48 * Real.pi * (3 * n + 1)) ≤ Real.log (1024 * n) :=
          Real.log_le_log (by positivity) this
      _ = Real.log 1024 + Real.log n := Real.log_mul (by norm_num) (by positivity)
      _ ≤ 10 + Real.log n := by
          have h := Real.log_two_lt_d9
          have : Real.log 1024 = 10 * Real.log 2 := by
            rw [show (1024 : ℝ) = 2 ^ 10 by norm_num, Real.log_pow]; norm_num
          linarith
  nlinarith

theorem log_inv_etaP_nonneg : 0 ≤ Real.log (1 / etaP n ε) := by
  have := etaP_pos hn hε hε2; have := etaP_lt hn hε hε2
  apply Real.log_nonneg; rw [le_div_iff₀ (by assumption)]; linarith

theorem bP_le : (bP n ε : ℝ) ≤ 160 * Real.log (n / ε) := by
  obtain ⟨h0, h1, _⟩ := rho_bounds hn hε hε2
  have he := epsG_pos hn hε hε2; have he2 := epsG_le hn hε hε2
  have hΛ := Lam_ge_one hn hε hε2
  have hln := log_n_le hn hε hε2
  have h1' := log_inv_rho_le hn hε hε2
  have h2' := log_inv_epsG_le hn hε hε2
  have hnr : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hX : 1 ≤ (3 * n + 1) / (QuantumLTF.Membership.rho n * epsG n ε) := by
    rw [le_div_iff₀ (by positivity)]; nlinarith [mul_le_mul h1 he2 he.le (by norm_num : (0:ℝ) ≤ 1)]
  unfold bP
  have hlb : 0 ≤ Real.logb 2 ((3 * n + 1) / (QuantumLTF.Membership.rho n * epsG n ε)) :=
    Real.logb_nonneg (by norm_num) hX
  refine (ceil_le_add_one hlb).trans ?_
  rw [Real.logb, show (3 * (n : ℝ) + 1) / (QuantumLTF.Membership.rho n * epsG n ε) =
    (3 * n + 1) * (1 / QuantumLTF.Membership.rho n) * (1 / epsG n ε) by field_simp,
    Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity)]
  have h3 : Real.log (3 * n + 1) ≤ 2 + Real.log n := by
    calc Real.log (3 * n + 1) ≤ Real.log (4 * n) := Real.log_le_log (by positivity) (by linarith)
      _ = Real.log 4 + Real.log n := Real.log_mul (by norm_num) (by positivity)
      _ ≤ 2 + Real.log n := by
          have h := Real.log_two_lt_d9
          have : Real.log 4 = 2 * Real.log 2 := by
            rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
          linarith
  have h2 := log_two_gt hn hε hε2
  rw [div_add_one (by linarith), div_le_iff₀ (by linarith)]
  nlinarith

theorem PP_le : (PP n ε : ℝ) ≤ 140 * Real.log (n / ε) := by
  have he := epsG_pos hn hε hε2; have he2 := epsG_le hn hε hε2
  have hΛ := Lam_ge_one hn hε hε2
  have h2' := log_inv_epsG_le hn hε hε2
  have h2 := log_two_gt hn hε hε2
  unfold PP
  have hlb : 0 ≤ Real.logb 2 (1 / epsG n ε) :=
    Real.logb_nonneg (by norm_num) (by rw [le_div_iff₀ he]; linarith)
  refine (ceil_le_add_one hlb).trans ?_
  rw [Real.logb, div_add_one (by linarith), div_le_iff₀ (by linarith)]
  nlinarith

theorem PP_spec : (1 / 2 : ℝ) ^ PP n ε ≤ epsG n ε := by
  have he := epsG_pos hn hε hε2; have he2 := epsG_le hn hε hε2
  have h := (Nat.le_ceil (Real.logb 2 (1 / epsG n ε)))
  have h2 : 1 / epsG n ε ≤ (2 : ℝ) ^ PP n ε := by
    unfold PP
    rw [← Real.rpow_natCast]
    calc 1 / epsG n ε = (2 : ℝ) ^ Real.logb 2 (1 / epsG n ε) :=
          (Real.rpow_logb (by norm_num) (by norm_num) (by positivity)).symm
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by norm_num) h
  rw [div_pow, one_pow, div_le_iff₀ (by positivity)]
  rw [div_le_iff₀ he] at h2; linarith

end P2

end LTFC

-- ===== module Arith =====

namespace LTFC

/-- Pure real arithmetic for the gate bound. -/
theorem gate_arith (N K1 Λ M l1 Q MQ L Kw LoT c3q c3g cAg CA C3 : ℝ)
    (hN : 1 ≤ N) (hK1 : 1 ≤ K1) (hΛ : 1 ≤ Λ) (hM : M = K1 * Λ)
    (hl1 : 0 ≤ l1) (hl1M : l1 ≤ M) (hQ : 0 ≤ Q) (hQM : Q ≤ M) (hMQ : 0 ≤ MQ) (hMQM : MQ ≤ M)
    (hL : 0 ≤ L) (hLM : L ≤ M) (hKw : 0 ≤ Kw) (hKwM : Kw ≤ M) (hLoT : 0 ≤ LoT) (hLoTM : LoT ≤ M)
    (hc3q : 0 ≤ c3q) (hc3qb : c3q ≤ 5 * C3) (hc3g : c3g ≤ 5 * C3 * (8281 * N * Λ ^ 2 + Λ))
    (hcAg0 : 0 ≤ cAg)
    (hcAg : cAg ≤ CA * N * (272 * Λ) ^ 2 * (110 * Λ) + CA * N * L * (110 * Λ))
    (hCA : 0 ≤ CA) (hCAK : CA ≤ K1) (hC3 : 0 ≤ C3) :
    N * l1 + 1200 * (N * L + MQ) * Q + (20 * (2 + 2 * (N * (12 * L)) + 2 * (N * L + 1) + 1) + 2) +
      (c3g + c3q * (7 * cAg)) + 10 * (2 + N * Kw) +
      10 * (3 + N * (15 * LoT) + 18 * LoT + (N + 1) * LoT) ≤
    (4000 + 300000000 * C3) * K1 ^ 3 * N * Λ ^ 3 := by
  have hM1 : 1 ≤ M := by rw [hM]; exact one_le_mul_of_one_le_of_one_le hK1 hΛ
  have hM0 : 0 ≤ M := by linarith only [hM1]
  have hΛM : Λ ≤ M := by rw [hM]; exact le_mul_of_one_le_left (by linarith only [hΛ]) hK1
  have hM2 : M ≤ M ^ 2 := by rw [sq]; exact le_mul_of_one_le_left hM0 hM1
  have hM23 : M ^ 2 ≤ M ^ 3 := pow_le_pow_right₀ hM1 (by norm_num)
  have hM3 : M ^ 3 = K1 ^ 3 * Λ ^ 3 := by rw [hM]; ring
  have hN0 : 0 ≤ N := by linarith only [hN]
  have hNM : N * M ≤ N * M ^ 3 := mul_le_mul_of_nonneg_left (hM2.trans hM23) hN0
  have hNM2 : N * M ^ 2 ≤ N * M ^ 3 := mul_le_mul_of_nonneg_left hM23 hN0
  have hNM3 : 1 ≤ N * M ^ 3 := one_le_mul_of_one_le_of_one_le hN (one_le_pow₀ hM1)
  -- individual terms
  have hNl1 : N * l1 ≤ N * M := mul_le_mul_of_nonneg_left hl1M hN0
  have hNL : N * L ≤ N * M := mul_le_mul_of_nonneg_left hLM hN0
  have hNKw : N * Kw ≤ N * M := mul_le_mul_of_nonneg_left hKwM hN0
  have hNLo : N * LoT ≤ N * M := mul_le_mul_of_nonneg_left hLoTM hN0
  have hMN : M ≤ N * M := le_mul_of_one_le_left hM0 hN
  have t1 : N * l1 ≤ N * M ^ 3 := le_trans hNl1 hNM
  have t2 : 1200 * (N * L + MQ) * Q ≤ 2400 * (N * M ^ 3) := by
    have h1 : N * L + MQ ≤ N * M + M := by linarith only [hNL, hMQM]
    have : (N * L + MQ) * Q ≤ (N * M + M) * M :=
      mul_le_mul h1 hQM hQ (add_nonneg (mul_nonneg hN0 hM0) hM0)
    have hM2N : M ^ 2 ≤ N * M ^ 2 := le_mul_of_one_le_left (by positivity) hN
    have e : (N * M + M) * M = N * M ^ 2 + M ^ 2 := by ring
    linarith only [this, hM2N, e, hNM2]
  have t3 : 20 * (2 + 2 * (N * (12 * L)) + 2 * (N * L + 1) + 1) + 2 ≤ 622 * (N * M ^ 3) := by
    have : 20 * (2 + 2 * (N * (12 * L)) + 2 * (N * L + 1) + 1) + 2 = 102 + 520 * (N * L) := by ring
    rw [this]; linarith only [hNL, hNM, hNM3]
  have hΛ2 : Λ ^ 2 ≤ M ^ 3 := le_trans (pow_le_pow_left₀ (by linarith only [hΛ]) hΛM 2) hM23
  have hNΛ2 : N * Λ ^ 2 ≤ N * M ^ 3 := mul_le_mul_of_nonneg_left hΛ2 hN0
  have t4 : c3g ≤ 41410 * C3 * (N * M ^ 3) := by
    have : 8281 * N * Λ ^ 2 + Λ ≤ 8282 * (N * M ^ 3) := by
      have e : 8281 * N * Λ ^ 2 = 8281 * (N * Λ ^ 2) := by ring
      rw [e]; linarith only [hNΛ2, hΛM, hMN, hNM]
    have h5 : 5 * C3 * (8281 * N * Λ ^ 2 + Λ) ≤ 5 * C3 * (8282 * (N * M ^ 3)) :=
      mul_le_mul_of_nonneg_left this (by linarith only [hC3])
    have e2 : 5 * C3 * (8282 * (N * M ^ 3)) = 41410 * C3 * (N * M ^ 3) := by ring
    linarith only [hc3g, h5, e2]
  have hK13 : K1 ≤ K1 ^ 3 := le_self_pow₀ hK1 (by norm_num)
  have hCAΛ : CA * Λ ^ 3 ≤ M ^ 3 := by
    rw [hM3]; exact mul_le_mul_of_nonneg_right (hCAK.trans hK13) (by positivity)
  have hCAΛ1 : CA * Λ ≤ M := by rw [hM]; exact mul_le_mul_of_nonneg_right hCAK (by linarith only [hΛ])
  have hCAΛL : CA * Λ * L ≤ M ^ 3 := by
    have : CA * Λ * L ≤ M * M := mul_le_mul hCAΛ1 hLM hL hM0
    have e : M * M = M ^ 2 := by ring
    linarith only [this, e, hM23]
  have hcA' : cAg ≤ 8138350 * (N * M ^ 3) := by
    have a1 : CA * N * (272 * Λ) ^ 2 * (110 * Λ) ≤ 8138240 * (N * M ^ 3) := by
      rw [show CA * N * (272 * Λ) ^ 2 * (110 * Λ) = 8138240 * (N * (CA * Λ ^ 3)) by ring]
      have := mul_le_mul_of_nonneg_left hCAΛ hN0
      linarith only [this]
    have a2 : CA * N * L * (110 * Λ) ≤ 110 * (N * M ^ 3) := by
      rw [show CA * N * L * (110 * Λ) = 110 * (N * (CA * Λ * L)) by ring]
      have := mul_le_mul_of_nonneg_left hCAΛL hN0
      linarith only [this]
    linarith only [a1, a2, hcAg]
  have t5 : c3q * (7 * cAg) ≤ 284842250 * C3 * (N * M ^ 3) := by
    have h1 : c3q * cAg ≤ 5 * C3 * (8138350 * (N * M ^ 3)) :=
      mul_le_mul hc3qb hcA' hcAg0 (by positivity)
    have e1 : c3q * (7 * cAg) = 7 * (c3q * cAg) := by ring
    have e2 : 5 * C3 * (8138350 * (N * M ^ 3)) = 40691750 * C3 * (N * M ^ 3) := by ring
    rw [e1]; linarith only [h1, e2]
  have t6 : 10 * (2 + N * Kw) ≤ 30 * (N * M ^ 3) := by linarith only [hNKw, hNM, hNM3]
  have hLoN : LoT ≤ N * M := le_trans hLoTM hMN
  have t7 : 10 * (3 + N * (15 * LoT) + 18 * LoT + (N + 1) * LoT) ≤ 380 * (N * M ^ 3) := by
    have : 10 * (3 + N * (15 * LoT) + 18 * LoT + (N + 1) * LoT) = 30 + 160 * (N * LoT) + 190 * LoT := by ring
    rw [this]; linarith only [hNLo, hLoN, hNM, hNM3]
  have hfin : (4000 + 300000000 * C3) * K1 ^ 3 * N * Λ ^ 3 = (4000 + 300000000 * C3) * (N * M ^ 3) := by
    rw [hM3]; ring
  rw [hfin]
  have hC3' : 0 ≤ C3 * (N * M ^ 3) := by positivity
  have e3 : (4000 + 300000000 * C3) * (N * M ^ 3) = 4000 * (N * M ^ 3) + 300000000 * (C3 * (N * M ^ 3)) := by ring
  have e4 : 41410 * C3 * (N * M ^ 3) = 41410 * (C3 * (N * M ^ 3)) := by ring
  have e5 : 284842250 * C3 * (N * M ^ 3) = 284842250 * (C3 * (N * M ^ 3)) := by ring
  rw [e3]
  linarith only [t1, t2, t3, t4, t5, t6, t7, hC3', hNM3, e4, e5]

end LTFC

-- ===== module FinalT =====

open QAlgorithms

namespace LTFC

theorem main_thmT :
    ∃ (C : ℝ) (K : ℕ), 0 < C ∧ ∀ n : ℕ, 2 ≤ n → ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 2 →
      ∃ (ℓ f m ℓo fo : ℕ)
        (c : QAlgorithms.OracleCircuit QuantumLTF.Membership.gates12
          (fun _ : Fin 1 => n * ℓ + 1) m)
        (oa : Fin n → (Fin ℓo ↪ Fin m)) (ob : Fin ℓo ↪ Fin m),
        QuantumLTF.Membership.Uncontrolled c ∧
        (c.queryCount 0 : ℝ) ≤ C * Real.log (n / ε) ∧
        (c.gateCount : ℝ) ≤ C * n * (Real.log (n / ε)) ^ K ∧
        ∀ w : EuclideanSpace ℝ (Fin n), ‖w‖ = 1 → ∀ θ : ℝ,
          open Classical in
          QAlgorithms.probEvent
            (QAlgorithms.act (c.unitary fun _ => QuantumLTF.Membership.memOracle n ℓ f w θ)
              (QAlgorithms.zeroKet m))
            (fun z => QuantumLTF.Membership.LearningCertificate ε w θ
              (WithLp.toLp 2 fun i => QuantumLTF.Membership.readFp (oa i) fo z)
              (QuantumLTF.Membership.readFp ob fo z)) ≥ 2 / 3 := by
  obtain ⟨Cu, hCu, hU⟩ := QuantumLTF.Membership.uniform_dyadic_reference_direction
  obtain ⟨Cp, hCp, hpar⟩ := QuantumLTF.Membership.theorem_3_1_parameters
  obtain ⟨CA, hCA, hA⟩ := QuantumLTF.Membership.uniform_height_circuit Cu (110 * Cp) hCu.le
    (by positivity)
  obtain ⟨C3, hC3, h33⟩ := QuantumLTF.Membership.theorem_3_3 CA
  set K1 : ℝ := 1000 * (CA + Cu + Cp + C3 + 1) with hK1d
  have hK1 : 1 ≤ K1 := by rw [hK1d]; linarith only [hCA.le, hCu.le, hCp.le, hC3.le]
  refine ⟨(6 + 5 * C3) * K1 + (4000 + 300000000 * C3) * K1 ^ 3, 3, by positivity, ?_⟩
  intro n hn ε hε hε2
  obtain ⟨ℓ₁, f₁, hf₁, hℓ₁, hgood⟩ := hU n hn
  obtain ⟨m, q, hm, hq2, hmq, hqζ⟩ := hpar ε (ε / 100) hε hε2 (by positivity) (by linarith only [hε2])
  have hΛ := Lam_ge_one hn hε hε2
  have hlogn := log_n_le hn hε hε2
  have hloge := log_eps_le hn hε hε2
  have hlogn0 : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ n))
  have hloge0 : 0 ≤ Real.log (1 / ε) := Real.log_nonneg (by rw [le_div_iff₀ hε]; linarith only [hε2])
  have hζ := log_Leps_zeta_le hn hε hε2
  have hBh : ((m + q + 2 : ℕ) : ℝ) ≤ 110 * Cp * Real.log (1 / ε) := by
    have : ((m + q + 2 : ℕ) : ℝ) ≤ Cp * (110 * Real.log (1 / ε)) :=
      le_trans hmq (mul_le_mul_of_nonneg_left hζ hCp.le)
    linarith
  obtain ⟨Vb, Vf, F, D, hVb, hF, hD, hAc⟩ := hA n hn ε (etaP n ε) hε hε2 (etaP_pos hn hε hε2)
    (etaP_lt hn hε hε2) (bP n ε) ℓ₁ f₁ (m + q + 2) (q + 1) hℓ₁ hf₁ hBh (by omega)
  have hf : f₁ + q + 1 ≤ F + f₁ + q + 1 := by omega
  have hℓ : (F + f₁ + q + 1) + m + ℓ₁ + 2 ≤ (F + f₁ + q + 1) + D + m + ℓ₁ + 2 := by omega
  obtain ⟨W, cA, hAu, hAq, hAg, hBD, hAact⟩ := hAc ((F + f₁ + q + 1) + D + m + ℓ₁ + 2)
    (F + f₁ + q + 1) (by omega) (by omega)
  have h33' := h33 n hn ε (epsG n ε) (1 / 6) hε hε2 (epsG_pos hn hε hε2)
    (by linarith only [epsG_le hn hε hε2]) (by norm_num) (by norm_num)
  obtain ⟨m₃, ℓo₃, fo₃, c₃, oa₃, h3u, h3q, h3g, h3p⟩ := h33' Vb Vf W hVb
  -- common real bounds
  set Λ := Real.log (n / ε) with hΛd
  have hK : 0 ≤ CA ∧ 0 ≤ Cu ∧ 0 ≤ Cp ∧ 0 ≤ C3 := ⟨hCA.le, hCu.le, hCp.le, hC3.le⟩
  have hΛ0 : 0 ≤ Λ := by linarith only [hΛ]
  have hlη := log_inv_etaP_le hn hε hε2
  have hlη0 := log_inv_etaP_nonneg hn hε hε2
  have hbP := bP_le hn hε hε2
  have hPP := PP_le hn hε hε2
  have hq2' : ((q + 2 : ℕ) : ℝ) ≤ 110 * Cp * Λ := by
    have := le_trans hq2 (mul_le_mul_of_nonneg_left hζ hCp.le)
    have h2 := mul_le_mul_of_nonneg_left hloge (show 0 ≤ 110 * Cp by positivity)
    linarith only [this, h2]
  have hmq' : ((m + q + 2 : ℕ) : ℝ) ≤ 110 * Cp * Λ := by
    have := le_trans hmq (mul_le_mul_of_nonneg_left hζ hCp.le)
    have h2 := mul_le_mul_of_nonneg_left hloge (show 0 ≤ 110 * Cp by positivity)
    linarith only [this, h2]
  have hℓ₁' : (ℓ₁ : ℝ) ≤ Cu * Λ := le_trans hℓ₁ (mul_le_mul_of_nonneg_left hlogn hCu.le)
  have hsum : (bP n ε : ℝ) + Real.log n + Real.log (1 / ε) + Real.log (1 / etaP n ε) ≤ 272 * Λ := by
    linarith only [hbP, hlogn, hloge, hlη]
  have hsum0 : 0 ≤ (bP n ε : ℝ) + Real.log n + Real.log (1 / ε) + Real.log (1 / etaP n ε) := by
    positivity
  have hsum' : Real.log n + Real.log (1 / ε) + Real.log (1 / etaP n ε) + (bP n ε : ℝ) ≤ 272 * Λ := by
    linarith only [hsum]
  have hF' : (F : ℝ) ≤ CA * (272 * Λ) := by
    exact le_trans hF (mul_le_mul_of_nonneg_left hsum' hCA.le)
  have hD' : (D : ℝ) ≤ CA * (272 * Λ) := by
    exact le_trans hD (mul_le_mul_of_nonneg_left hsum' hCA.le)
  have hf₁' : (f₁ : ℝ) ≤ ℓ₁ := by exact_mod_cast hf₁
  have hAq' : (cA.queryCount 0 : ℝ) ≤ CA * (110 * Λ) :=
    le_trans hAq (mul_le_mul_of_nonneg_left hlη hCA.le)
  have hl6 : Real.log (1 / (1 / 6 : ℝ)) ≤ 5 := log_le_128 (by norm_num) (by norm_num)
  have hl60 : 0 ≤ Real.log (1 / (1 / 6 : ℝ)) := Real.log_nonneg (by norm_num)
  have h3q' : (c₃.queryCount 0 : ℝ) ≤ 5 * C3 := by
    have := mul_le_mul_of_nonneg_left hl6 hC3.le
    have e : C3 * 5 = 5 * C3 := by ring
    linarith only [this, h3q, e]
  have hL1 := Leps_ge_one hn hε hε2
  have hLT := (Leps_bounds hn hε hε2).1
  have hεgn : Real.sqrt n * (2 * epsG n ε) ≤ ε / (100 * (QuantumLTF.Membership.Leps ε + 1)) := by
    have hs : 0 < Real.sqrt n := Real.sqrt_pos.2 (by exact_mod_cast (by omega : 0 < n))
    unfold epsG
    rw [le_div_iff₀ (by positivity)]
    field_simp
    ring_nf
    exact le_refl _
  obtain ⟨M, ℓo, fo, c, oa, ob, cu, hℓo, cq, cg, hprob⟩ :=
    QuantumLTF.Membership.learningCertificate_assembly n ℓ₁ f₁ m q ((F + f₁ + q + 1) + D + m + ℓ₁ + 2) (F + f₁ + q + 1)
      (bP n ε) Vb W Vf m₃ ℓo₃ fo₃ (PP n ε) ε (epsG n ε) (etaP n ε) hf hℓ cA c₃ oa₃ hAu h3u hm hqζ
      hL1 hLT (epsG_pos hn hε hε2).le (by linarith only [epsG_le hn hε hε2]) (PP_spec hn hε hε2)
      hεgn hBD hAact
      (fun w p θ hw h1 h2 Htil hacc OH hOH hact => by
        have := h3p w p θ hw h1 h2 Htil hacc OH hOH hact
        have e : (1 : ℝ) - 1 / 6 = 5 / 6 := by norm_num
        rw [e] at this; exact this)
      hgood
  refine ⟨((F + f₁ + q + 1) + D + m + ℓ₁ + 2), F + f₁ + q + 1, M, ℓo, fo, c, oa, ob, cu, ?_, ?_, hprob⟩
  rotate_left
  · -- gate count
    have hℓR : (((F + f₁ + q + 1) + D + m + ℓ₁ + 2 : ℕ) : ℝ) ≤ K1 * Λ := by
      have e : (((F + f₁ + q + 1) + D + m + ℓ₁ + 2 : ℕ) : ℝ) =
          (F : ℝ) + f₁ + D + ℓ₁ + ((q + 2 : ℕ) : ℝ) + ((m + q + 2 : ℕ) : ℝ) - q - 1 := by
        push_cast; ring
      have hq0 : (0 : ℝ) ≤ q := Nat.cast_nonneg _
      have h1 : (544 * CA + 2 * Cu + 220 * Cp) * Λ ≤ K1 * Λ :=
        mul_le_mul_of_nonneg_right (by rw [hK1d]; linarith only [hCA.le, hCu.le, hCp.le, hC3.le]) hΛ0
      have h2 : (F : ℝ) + f₁ + D + ℓ₁ ≤ 544 * CA * Λ + 2 * Cu * Λ := by
        linarith only [hF', hD', hf₁', hℓ₁']
      rw [e]
      have e2 : (544 * CA + 2 * Cu + 220 * Cp) * Λ = 544 * CA * Λ + 2 * Cu * Λ + 2 * (110 * Cp * Λ) := by ring
      linarith only [h1, h2, hq2', hmq', hq0, e2]
    have hLoTR : (ℓo : ℝ) ≤ K1 * Λ := by
      have : (ℓo : ℝ) ≤ 2 * (PP n ε : ℝ) + ((q + 2 : ℕ) : ℝ) + ((m + q + 2 : ℕ) : ℝ) + 8 := by
        exact_mod_cast hℓo
      have h1 : (288 + 220 * Cp) * Λ ≤ K1 * Λ :=
        mul_le_mul_of_nonneg_right (by rw [hK1d]; linarith only [hCA.le, hCu.le, hCp.le, hC3.le]) hΛ0
      have e2 : (288 + 220 * Cp) * Λ = 288 * Λ + 2 * (110 * Cp * Λ) := by ring
      linarith only [this, h1, hPP, hΛ, hq2', hmq', e2]
    have hqR : ((q + 2 : ℕ) : ℝ) ≤ K1 * Λ := by
      have h1 : (110 * Cp) * Λ ≤ K1 * Λ := mul_le_mul_of_nonneg_right (by rw [hK1d]; linarith only [hCA.le, hCu.le, hCp.le, hC3.le]) hΛ0
      linarith only [h1, hq2']
    have hmqR : ((m + q + 2 : ℕ) : ℝ) ≤ K1 * Λ := by
      have h1 : (110 * Cp) * Λ ≤ K1 * Λ := mul_le_mul_of_nonneg_right (by rw [hK1d]; linarith only [hCA.le, hCu.le, hCp.le, hC3.le]) hΛ0
      linarith only [h1, hmq']
    have hl1R : (ℓ₁ : ℝ) ≤ K1 * Λ := by
      have h1 : Cu * Λ ≤ K1 * Λ := mul_le_mul_of_nonneg_right (by rw [hK1d]; linarith only [hCA.le, hCu.le, hCp.le, hC3.le]) hΛ0
      linarith only [h1, hℓ₁']
    -- c₃ gates
    have hεgp := epsG_pos hn hε hε2
    have hlg : Real.log (n / epsG n ε) ≤ 91 * Λ := by
      rw [div_eq_mul_one_div, Real.log_mul (by positivity) (by positivity)]
      have := log_inv_epsG_le hn hε hε2
      linarith only [this, hlogn]
    have hlg0 : 0 ≤ Real.log (n / epsG n ε) := by
      apply Real.log_nonneg
      rw [le_div_iff₀ hεgp]
      have := epsG_le hn hε hε2
      have : (2 : ℝ) ≤ n := by exact_mod_cast hn
      have h1 : (1 : ℝ) * epsG n ε ≤ 1 / 400 := by linarith only [this, ‹epsG n ε ≤ 1 / 400›]
      linarith only [this, ‹epsG n ε ≤ 1 / 400›, h1]
    have hc3g : (c₃.gateCount : ℝ) ≤ 5 * C3 * (8281 * n * Λ ^ 2 + Λ) := by
      have hsq : Real.log (n / epsG n ε) ^ 2 ≤ (91 * Λ) ^ 2 := pow_le_pow_left₀ hlg0 hlg 2
      have hin : (n : ℝ) * Real.log (n / epsG n ε) ^ 2 + Real.log (1 / ε) ≤ 8281 * n * Λ ^ 2 + Λ := by
        have := mul_le_mul_of_nonneg_left hsq (Nat.cast_nonneg n)
        have e : (n : ℝ) * (91 * Λ) ^ 2 = 8281 * n * Λ ^ 2 := by ring
        linarith only [this, e, hloge]
      have hin0 : 0 ≤ (n : ℝ) * Real.log (n / epsG n ε) ^ 2 + Real.log (1 / ε) := by positivity
      calc (c₃.gateCount : ℝ) ≤ C3 * ((n : ℝ) * Real.log (n / epsG n ε) ^ 2 + Real.log (1 / ε)) *
            Real.log (1 / (1 / 6 : ℝ)) := h3g
        _ ≤ C3 * (8281 * n * Λ ^ 2 + Λ) * 5 := by
            apply mul_le_mul (mul_le_mul_of_nonneg_left hin hC3.le) hl6 hl60
            exact mul_nonneg hC3.le (by positivity)
        _ = 5 * C3 * (8281 * n * Λ ^ 2 + Λ) := by ring
    have hcAg : (cA.gateCount : ℝ) ≤ CA * n * (272 * Λ) ^ 2 * (110 * Λ) +
        CA * n * (((F + f₁ + q + 1) + D + m + ℓ₁ + 2 : ℕ) : ℝ) * (110 * Λ) := by
      refine le_trans hAg (add_le_add ?_ ?_)
      · apply mul_le_mul _ hlη hlη0 (by positivity)
        apply mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hsum0 hsum 2) (by positivity)
      · exact mul_le_mul_of_nonneg_left hlη (by positivity)
    have hga := gate_arith (n : ℝ) K1 Λ (K1 * Λ) (ℓ₁ : ℝ) ((q + 2 : ℕ) : ℝ) ((m + q + 2 : ℕ) : ℝ)
      (((F + f₁ + q + 1) + D + m + ℓ₁ + 2 : ℕ) : ℝ) (ℓo : ℝ)
      (ℓo : ℝ) (c₃.queryCount 0 : ℝ) (c₃.gateCount : ℝ)
      (cA.gateCount : ℝ) CA C3 (by exact_mod_cast (by omega : 1 ≤ n)) hK1 hΛ rfl
      (Nat.cast_nonneg _) hl1R (Nat.cast_nonneg _) hqR (Nat.cast_nonneg _) hmqR
      (Nat.cast_nonneg _) hℓR (Nat.cast_nonneg _) hLoTR (Nat.cast_nonneg _) hLoTR
      (Nat.cast_nonneg _) h3q' hc3g (Nat.cast_nonneg _) hcAg hCA.le
      (by rw [hK1d]; linarith only [hCA.le, hCu.le, hCp.le, hC3.le]) hC3.le
    have hcg : (c.gateCount : ℝ) ≤
        ((n * ℓ₁ + 1200 * (n * ((F + f₁ + q + 1) + D + m + ℓ₁ + 2) + m + q + 2) * (q + 2) +
          (20 * (2 + 2 * (n * (12 * ((F + f₁ + q + 1) + D + m + ℓ₁ + 2))) + 2 * (n * ((F + f₁ + q + 1) + D + m + ℓ₁ + 2) + 1) + 1) + 2) +
          (c₃.gateCount + c₃.queryCount 0 * (7 * cA.gateCount)) + 10 * (2 + n * ℓo) +
          10 * (3 + n * (15 * ℓo) + 18 * ℓo + (n + 1) * ℓo) : ℕ) : ℝ) := by exact_mod_cast cg
    have hC : (4000 + 300000000 * C3) * K1 ^ 3 * n * Λ ^ 3 ≤
        ((6 + 5 * C3) * K1 + (4000 + 300000000 * C3) * K1 ^ 3) * n * Λ ^ 3 := by
      have : 0 ≤ (6 + 5 * C3) * K1 * n * Λ ^ 3 := by positivity
      have e : ((6 + 5 * C3) * K1 + (4000 + 300000000 * C3) * K1 ^ 3) * n * Λ ^ 3 =
        (6 + 5 * C3) * K1 * n * Λ ^ 3 + (4000 + 300000000 * C3) * K1 ^ 3 * n * Λ ^ 3 := by ring
      linarith only [this, e]
    push_cast at hcg hga
    linarith only [hcg, hga, hC]
  · -- query count
    have hcq : (c.queryCount 0 : ℝ) ≤
        2 * ((q + 2 : ℕ) : ℝ) + 4 + (c₃.queryCount 0 : ℝ) * (cA.queryCount 0 : ℝ) := by
      exact_mod_cast cq
    have hprod : (c₃.queryCount 0 : ℝ) * (cA.queryCount 0 : ℝ) ≤ 5 * C3 * (K1 * Λ) := by
      have h1 : CA * (110 * Λ) ≤ K1 * Λ := by
        rw [show CA * (110 * Λ) = (110 * CA) * Λ by ring]
        exact mul_le_mul_of_nonneg_right (by rw [hK1d]; linarith only [hCA.le, hCu.le, hCp.le, hC3.le]) hΛ0
      exact mul_le_mul h3q' (le_trans hAq' h1) (Nat.cast_nonneg _) (by positivity)
    have h1 : 110 * Cp * Λ ≤ K1 * Λ := mul_le_mul_of_nonneg_right (by rw [hK1d]; linarith only [hCA.le, hCu.le, hCp.le, hC3.le]) hΛ0
    have hKΛ : 1 ≤ K1 * Λ := by nlinarith only [hK1, hΛ]
    have hC : (6 + 5 * C3) * K1 * Λ ≤
        ((6 + 5 * C3) * K1 + (4000 + 300000000 * C3) * K1 ^ 3) * Λ := by
      have : 0 ≤ (4000 + 300000000 * C3) * K1 ^ 3 * Λ := by positivity
      have e : ((6 + 5 * C3) * K1 + (4000 + 300000000 * C3) * K1 ^ 3) * Λ =
        (6 + 5 * C3) * K1 * Λ + (4000 + 300000000 * C3) * K1 ^ 3 * Λ := by ring
      linarith only [this, e]
    have e2 : (6 + 5 * C3) * K1 * Λ = 6 * (K1 * Λ) + 5 * C3 * (K1 * Λ) := by ring
    linarith only [hcq, hprod, h1, hKΛ, hC, e2, hq2']

end LTFC

-- ===== final =====
theorem solution :
    ∃ (C : ℝ) (K : ℕ), 0 < C ∧ ∀ n : ℕ, 2 ≤ n → ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 2 →
      ∃ (ℓ f m ℓo fo : ℕ)
        (c : QAlgorithms.OracleCircuit QuantumLTF.Membership.gates12
          (fun _ : Fin 1 => n * ℓ + 1) m)
        (oa : Fin n → (Fin ℓo ↪ Fin m)) (ob : Fin ℓo ↪ Fin m),
        QuantumLTF.Membership.Uncontrolled c ∧
        (c.queryCount 0 : ℝ) ≤ C * Real.log (n / ε) ∧
        (c.gateCount : ℝ) ≤ C * n * (Real.log (n / ε)) ^ K ∧
        ∀ w : EuclideanSpace ℝ (Fin n), ‖w‖ = 1 → ∀ θ : ℝ,
          open Classical in
          QAlgorithms.probEvent
            (QAlgorithms.act (c.unitary fun _ => QuantumLTF.Membership.memOracle n ℓ f w θ)
              (QAlgorithms.zeroKet m))
            (fun z => QuantumLTF.Membership.LearningCertificate ε w θ
              (WithLp.toLp 2 fun i => QuantumLTF.Membership.readFp (oa i) fo z)
              (QuantumLTF.Membership.readFp ob fo z)) ≥ 2 / 3 :=
  LTFC.main_thmT
