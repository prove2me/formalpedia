-- Prove2me | solution 1 for PolyhedralSOC.UpperBound.choice_of_nu
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T17:03:26.448643+00:00
-- url     : https://prove2.me/submissions/bdecd203-a31d-4851-b0b4-704e7ff55d14

import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Complex.Exponential
import Definitions.Def_PolyhedralSOC_UpperBound_System8

open PolyhedralSOC.UpperBound

-- Adapted from Shuze Chen's accepted decay proof, submission a78ca07a.
private theorem delta_bound (ν : ℕ) (hν : 1 ≤ ν) : delta ν ≤ 4 / (4 : ℝ)^ν := by
  have hpi : 0 < Real.pi := Real.pi_pos
  have hpi34 : Real.pi ≤ 4 := Real.pi_le_four
  have hpow : (0:ℝ) < 2 ^ (ν + 1) := by positivity
  have h4 : (4:ℝ) ≤ 2 ^ (ν + 1) := by
    have h2 : (2:ℝ) ^ 2 ≤ 2 ^ (ν + 1) := by
      apply pow_le_pow_right₀ (by norm_num)
      omega
    norm_num at h2
    exact h2
  have hθpos : 0 < Real.pi / 2 ^ (ν + 1) := by positivity
  have hθle : Real.pi / 2 ^ (ν + 1) ≤ Real.pi / 4 := by
    apply div_le_div_of_nonneg_left hpi.le (by norm_num) h4
  -- cos θ ≥ cos (π/3) = 1/2
  have hπ3 : Real.pi / 4 ≤ Real.pi / 3 := by
    apply div_le_div_of_nonneg_left hpi.le (by norm_num) (by norm_num)
  have hcosge : (1:ℝ) / 2 ≤ Real.cos (Real.pi / 2 ^ (ν + 1)) := by
    have hmono := Real.cos_le_cos_of_nonneg_of_le_pi hθpos.le
      (by linarith : Real.pi / 3 ≤ Real.pi) (le_trans hθle hπ3)
    rwa [Real.cos_pi_div_three] at hmono
  have hcospos : 0 < Real.cos (Real.pi / 2 ^ (ν + 1)) := by linarith
  -- 1 - cos θ ≤ θ²/2
  have hlow : 1 - (Real.pi / 2 ^ (ν + 1)) ^ 2 / 2 ≤ Real.cos (Real.pi / 2 ^ (ν + 1)) :=
    Real.one_sub_sq_div_two_le_cos
  -- δ ν = (1 - cos θ)/cos θ ≤ 2 (1 - cos θ) ≤ θ²
  have hdelta : delta ν ≤ (Real.pi / 2 ^ (ν + 1)) ^ 2 := by
    have hd : delta ν = (1 - Real.cos (Real.pi / 2 ^ (ν + 1))) /
        Real.cos (Real.pi / 2 ^ (ν + 1)) := by
      rw [delta]
      field_simp
    rw [hd, div_le_iff₀ hcospos]
    nlinarith [hlow, hcosge, sq_nonneg (Real.pi / 2 ^ (ν + 1))]
  -- θ² = π²/4^{ν+1} ≤ 3/4^ν
  have hsq : (Real.pi / 2 ^ (ν + 1)) ^ 2 = Real.pi ^ 2 / 4 ^ (ν + 1) := by
    rw [div_pow]
    congr 1
    rw [← pow_mul]
    rw [show (4:ℝ) = 2 ^ 2 by norm_num, ← pow_mul]
    ring_nf
  obtain ⟨q, hq, hqpos⟩ : ∃ q : ℝ, q = (4:ℝ) ^ ν ∧ 0 < q := ⟨4 ^ ν, rfl, by positivity⟩
  have h41 : (4:ℝ) ^ (ν + 1) = 4 * q := by rw [hq, pow_succ]; ring
  have hp16 : Real.pi ^ 2 ≤ 16 := by nlinarith [hpi, hpi34]
  rw [hsq, h41] at hdelta
  have hstep : Real.pi ^ 2 / (4 * q) ≤ 4 / q := by
    rw [div_le_div_iff₀ (by positivity) hqpos]
    nlinarith [mul_le_mul_of_nonneg_right hp16 hqpos.le]
  have hgoal : delta ν ≤ 4 / q := le_trans hdelta hstep
  rw [hq] at hgoal
  exact hgoal
private theorem cosine_positive (ν : ℕ) (hν : 1 ≤ ν) :
    0 < Real.cos (Real.pi / (2 : ℝ)^(ν+1)) := by
  have hp : (4 : ℝ) ≤ 2^(ν+1) := by
    have hh := pow_le_pow_right₀ (show (1 : ℝ) ≤ 2 by norm_num) (show 2 ≤ ν+1 by omega)
    norm_num at hh ⊢
    exact hh
  have ht : Real.pi/(2 : ℝ)^(ν+1) ≤ Real.pi/3 := by
    apply div_le_div_of_nonneg_left Real.pi_pos.le (by norm_num)
    linarith
  have hh := Real.cos_le_cos_of_nonneg_of_le_pi
    (show 0 ≤ Real.pi/(2 : ℝ)^(ν+1) by positivity)
    (show Real.pi/3 ≤ Real.pi by linarith [Real.pi_pos]) ht
  rw [Real.cos_pi_div_three] at hh
  linarith

private theorem choose_nu_level (ε : ℝ) (he0 : 0 < ε) (he1 : ε ≤ 1) (l : ℕ) (hl : 1 ≤ l) :
    1 ≤ ⌊16*(l : ℝ)*Real.log (2/ε)⌋₊ ∧
    1/Real.cos (Real.pi/(2 : ℝ)^(⌊16*(l : ℝ)*Real.log (2/ε)⌋₊+1)) ≤ 1+ε/(2 : ℝ)^(l+1) := by
  let L := Real.log (2/ε)
  let ν := ⌊16*(l : ℝ)*L⌋₊
  have hbase : (2 : ℝ) ≤ 2/ε := (le_div_iff₀ he0).mpr (by linarith)
  have hL : (1 : ℝ)/2 ≤ L := by
    have hh := Real.log_le_log (show (0 : ℝ) < 2 by norm_num) hbase
    have hlog := Real.log_two_gt_d9
    dsimp [L]
    linarith
  have hlR : (1 : ℝ) ≤ l := by exact_mod_cast hl
  have hx : 1 ≤ 16*(l : ℝ)*L := by nlinarith [mul_le_mul_of_nonneg_right hlR (show 0 ≤ L by linarith)]
  have hν : 1 ≤ ν := Nat.floor_pos.mpr hx
  refine ⟨hν,?_⟩
  have hfloor := Nat.lt_floor_add_one (16*(l : ℝ)*L)
  have hνlow : ((l+3 : ℕ) : ℝ)*L ≤ (ν : ℝ) := by
    have hh : (l : ℝ)*L ≥ L := by nlinarith [mul_nonneg (sub_nonneg.mpr hlR) (le_trans (by norm_num) hL)]
    simp only [Nat.cast_add,Nat.cast_ofNat] at *
    dsimp [ν]
    nlinarith
  have hexp : Real.exp ((ν : ℝ)) ≤ (4 : ℝ)^ν := by
    have hh := pow_le_pow_left₀ (Real.exp_pos 1).le (show Real.exp 1 ≤ 4 by linarith [Real.exp_one_lt_three]) ν
    rw [← Real.exp_nat_mul] at hh
    simpa using hh
  have hνpow : (2/ε)^(l+3) ≤ (4 : ℝ)^ν := by
    calc
      _ = Real.exp (((l+3 : ℕ) : ℝ)*L) := by rw [Real.exp_nat_mul,Real.exp_log (by positivity : (0 : ℝ) < 2/ε)]
      _ ≤ Real.exp (ν : ℝ) := Real.exp_le_exp.mpr hνlow
      _ ≤ _ := hexp
  have hlow : (2/ε)*(2 : ℝ)^(l+2) ≤ (4 : ℝ)^ν := by
    have hh := pow_le_pow_left₀ (show (0 : ℝ) ≤ 2 by norm_num) hbase (l+2)
    have hh' := mul_le_mul_of_nonneg_left hh (show (0 : ℝ) ≤ 2/ε by positivity)
    calc
      _ ≤ (2/ε)*(2/ε)^(l+2) := hh'
      _ = (2/ε)^(l+3) := by rw [show l+3=(l+2)+1 by omega,pow_succ];ring
      _ ≤ _ := hνpow
  have hd := delta_bound ν hν
  have hdsmall : 4/(4 : ℝ)^ν ≤ ε/(2 : ℝ)^(l+1) := by
    have hq : 0 < (2/ε)*(2 : ℝ)^(l+2) := by positivity
    calc
      _ ≤ 4/((2/ε)*(2 : ℝ)^(l+2)) := div_le_div_of_nonneg_left (by norm_num) hq hlow
      _ = _ := by rw [show l+2=(l+1)+1 by omega,pow_succ];field_simp;ring
  unfold delta at hd
  change 1/Real.cos (Real.pi/(2 : ℝ)^(ν+1)) ≤ _
  linarith

private theorem weighted_levels (θ : ℕ) :
    (∑ l∈Finset.Icc 1 θ,(2 : ℝ)^(θ-l)*(l : ℝ))=2^(θ+1)-(θ : ℝ)-2 := by
  induction θ with
  | zero => norm_num
  | succ θ ih =>
    rw [Finset.sum_Icc_succ_top (show 1 ≤ θ+1 by omega)]
    have he : (∑ l∈Finset.Icc 1 θ,(2 : ℝ)^(θ+1-l)*(l : ℝ))=
        2*(∑ l∈Finset.Icc 1 θ,(2 : ℝ)^(θ-l)*(l : ℝ)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro l hl
      have hlt := (Finset.mem_Icc.mp hl).2
      rw [show θ+1-l=(θ-l)+1 by omega,pow_succ]
      ring
    simp only [Nat.succ_eq_add_one,Nat.sub_self,pow_zero,one_mul] at *
    rw [he,ih,pow_succ]
    push_cast
    ring
private theorem product_levels (ε : ℝ) (he0 : 0 < ε) (he1 : ε ≤ 1) :
    ∀ θ : ℕ,0 ≤ (∏ l∈Finset.Icc 1 θ,1/Real.cos (Real.pi/(2 : ℝ)^(⌊16*(l : ℝ)*Real.log (2/ε)⌋₊+1))) ∧
      (∏ l∈Finset.Icc 1 θ,1/Real.cos (Real.pi/(2 : ℝ)^(⌊16*(l : ℝ)*Real.log (2/ε)⌋₊+1))) ≤
        1+ε*(1-1/(2 : ℝ)^θ) := by
  intro θ
  induction θ with
  | zero => norm_num
  | succ θ ih =>
    rw [Finset.prod_Icc_succ_top (show 1 ≤ θ+1 by omega)]
    have hlevel := choose_nu_level ε he0 he1 (θ+1) (by omega)
    have hfac : 0 ≤ 1/Real.cos (Real.pi/(2 : ℝ)^(⌊16*((θ+1 : ℕ) : ℝ)*Real.log (2/ε)⌋₊+1)) :=
      le_of_lt (one_div_pos.mpr (cosine_positive _ hlevel.1))
    refine ⟨mul_nonneg ih.1 hfac,?_⟩
    have htwo : (∏ l∈Finset.Icc 1 θ,1/Real.cos (Real.pi/(2 : ℝ)^(⌊16*(l : ℝ)*Real.log (2/ε)⌋₊+1))) ≤ 2 := by
      have hh : 0 ≤ ε*(1/(2 : ℝ)^θ) := by positivity
      nlinarith [ih.2]
    have hmul := mul_le_mul_of_nonneg_left hlevel.2 ih.1
    have htwo' := mul_le_mul_of_nonneg_right htwo (show 0 ≤ ε/(2 : ℝ)^((θ+1)+1) by positivity)
    calc
      _ ≤ (1+ε*(1-1/(2 : ℝ)^θ))+2*(ε/(2 : ℝ)^((θ+1)+1)) := by nlinarith [ih.2]
      _ = 1+ε*(1-1/(2 : ℝ)^(θ+1)) := by
        rw [pow_succ,pow_succ]
        field_simp
        ring

theorem solution :
    ∃ c : ℝ,0 < c ∧ ∃ C : ℝ,0 < C ∧
      ∀ θ : ℕ,1 ≤ θ → ∀ ε : ℝ,0 < ε → ε ≤ 1 →
        (∀ l : ℕ,1 ≤ l → l ≤ θ → 1 ≤ ⌊c*l*Real.log (2/ε)⌋₊) ∧
        (∏ l∈Finset.Icc 1 θ,1/Real.cos (Real.pi/2^(⌊c*l*Real.log (2/ε)⌋₊+1)))-1 ≤ ε ∧
        ((∑ l∈Finset.Icc 1 θ,2^(θ-l)*⌊c*l*Real.log (2/ε)⌋₊ : ℕ) : ℝ) ≤ C*2^θ*Real.log (2/ε) := by
  refine ⟨16,by norm_num,32,by norm_num,?_⟩
  intro θ hθ ε he0 he1
  refine ⟨fun l hl hlt => (choose_nu_level ε he0 he1 l hl).1,?_,?_⟩
  · have hh := (product_levels ε he0 he1 θ).2
    have hn : 0 ≤ ε*(1/(2 : ℝ)^θ) := by positivity
    nlinarith
  · have hL : 0 ≤ Real.log (2/ε) := Real.log_nonneg ((le_div_iff₀ he0).mpr (by linarith))
    simp only [Nat.cast_sum,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat]
    calc
      _ ≤ 16*Real.log (2/ε)*(∑ l∈Finset.Icc 1 θ,(2 : ℝ)^(θ-l)*(l : ℝ)) := by
        rw [Finset.mul_sum]
        apply Finset.sum_le_sum
        intro l hl
        have hf := Nat.floor_le (show 0 ≤ 16*(l : ℝ)*Real.log (2/ε) by positivity)
        have hh := mul_le_mul_of_nonneg_left hf (show 0 ≤ (2 : ℝ)^(θ-l) by positivity)
        nlinarith
      _ ≤ 16*Real.log (2/ε)*(2 : ℝ)^(θ+1) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        rw [weighted_levels]
        have hh : (0 : ℝ) ≤ θ := Nat.cast_nonneg θ
        linarith
      _ = 32*(2 : ℝ)^θ*Real.log (2/ε) := by rw [pow_succ];ring
