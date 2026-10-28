-- Prove2me | solution 1 for TaoFivePrimes.sine_weight_positive_bin_bound_65000
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-27T22:08:18.971909+00:00
-- url     : https://prove2.me/submissions/ab90414e-a3a4-4d6f-94a1-6f828be6f117

-- Uses the published bin, arithmetic, and zero-count certificates.
import Theorems.Thm_TaoFivePrimes_sine_bin_65000_all
import Theorems.Thm_TaoFivePrimes_sine_bin_65000_arithmetic_all
import Theorems.Thm_TaoFivePrimes_positive_zero_bin_counts_65000
import Mathlib.Tactic

set_option autoImplicit false
set_option maxHeartbeats 2000000
open DusartSmoothing Complex Set

theorem solution (i : Fin 180) (r : ℝ) (hr0 : (1/2151:ℝ) ≤ r)
    (hr1 : r ≤ (1/2149:ℝ)) (Z : Finset ℂ)
    (hZ : ∀ ρ ∈ Z, RvM.IsNontrivialZero ρ ∧
      65000+1290*(i.val:ℝ) < ρ.im ∧ ρ.im ≤ 65000+1290*(i.val:ℝ)+1290) :
    (∑ ρ ∈ Z, (RvM.zeroMult ρ : ℝ) *
      ((min (4*(Real.sin (ρ.im*r/2))^2 + 8*r + 3*ρ.im*r^2) 4) / ρ.im^3)) ≤
      (TaoFivePrimes.sineBinTerm65k i.val:ℝ)/(2*10^21) := by
  classical
  let L : ℝ := 65000+1290*(i.val:ℝ)
  let U : ℝ := L+1290
  let C : ℝ := (TaoFivePrimes.sineBinCount65k i.val:ℝ)
  let B : ℝ := (TaoFivePrimes.sineBinNumerator65k i.val:ℝ)/10000
  let F : ℝ := 4*B + 8/2149 + 3*U/2149^2
  have hL : 65000 ≤ L := by
    dsimp [L]
    nlinarith [Nat.cast_nonneg (α := ℝ) i.val]
  have hLp : 0 < L := by linarith
  have hUp : 0 < U := by dsimp [U]; linarith
  have hpositive : 0 ≤ r := by linarith
  have hF0 : 0 ≤ F := by dsimp [F,B]; positivity
  have hi := i.isLt
  let k : Fin 15 := ⟨i.val/12, by omega⟩
  have hi_group : i.val ≤ 12*k.val+11 := by dsimp [k]; omega
  have hi_group_real : (i.val:ℝ) ≤ 12*(k.val:ℝ)+11 := by exact_mod_cast hi_group
  have hU : U ≤ 80480+15480*(k.val:ℝ) := by dsimp [U,L]; nlinarith only [hi_group_real]
  have hZ' : ∀ ρ ∈ Z, RvM.IsNontrivialZero ρ ∧ L < ρ.im ∧ ρ.im ≤ U := by
    simpa [L,U] using hZ
  have hc := TaoFivePrimes.positive_zero_bin_counts_65000 k Z L U hL
    (by dsimp [U]; ring) hU hZ'
  have hd : (12*k.val)/12 = i.val/12 := by dsimp [k]; omega
  have heq : TaoFivePrimes.sineBinCount65k (12*k.val) = TaoFivePrimes.sineBinCount65k i.val := by
    dsimp [TaoFivePrimes.sineBinCount65k]
    rw [hd]
  have hC : (∑ ρ ∈ Z, (RvM.zeroMult ρ : ℝ)) ≤ C := by
    simpa [C,heq] using hc
  have hterm (ρ : ℂ) (hρ : ρ ∈ Z) :
      (min (4*(Real.sin (ρ.im*r/2))^2 + 8*r + 3*ρ.im*r^2) 4)/ρ.im^3 ≤ F/L^3 := by
    have hleft := (hZ' ρ hρ).2.1
    have hright := (hZ' ρ hρ).2.2
    have hγ : 0 < ρ.im := by linarith
    have hp0 := mul_le_mul (le_of_lt hleft) hr0 (by norm_num : (0:ℝ) ≤ 1/2151) hγ.le
    have hp1 := mul_le_mul hright hr1 hpositive hUp.le
    have hx0 : L/(2*2151) ≤ ρ.im*r/2 := by linarith
    have hx1 : ρ.im*r/2 ≤ U/(2*2149) := by linarith
    have hs := TaoFivePrimes.sine_bin_65000_all i (ρ.im*r/2)
      (by simpa [L] using hx0) (by simpa [L,U] using hx1)
    have hr2 : r^2 ≤ (1/2149:ℝ)^2 := pow_le_pow_left₀ hpositive hr1 2
    have hγr := mul_le_mul hright hr2 (sq_nonneg r) hUp.le
    have hf : min (4*(Real.sin (ρ.im*r/2))^2 + 8*r + 3*ρ.im*r^2) 4 ≤ F := by
      apply (min_le_left _ _).trans
      dsimp [F,B]
      nlinarith only [hs,hr1,hγr]
    have hden : L^3 ≤ ρ.im^3 := pow_le_pow_left₀ hLp.le hleft.le 3
    exact div_le_div₀ hF0 hf (pow_pos hLp 3) hden
  calc
    _ ≤ ∑ ρ ∈ Z, (RvM.zeroMult ρ : ℝ) * (F/L^3) := by
      apply Finset.sum_le_sum
      intro ρ hρ
      exact mul_le_mul_of_nonneg_left (hterm ρ hρ) (Nat.cast_nonneg _)
    _ = (∑ ρ ∈ Z, (RvM.zeroMult ρ : ℝ)) * (F/L^3) := by rw [Finset.sum_mul]
    _ ≤ C*(F/L^3) := mul_le_mul_of_nonneg_right hC (by positivity)
    _ ≤ _ := by
      have ha := TaoFivePrimes.sine_bin_65000_arithmetic_all i
      have he : 2*C*(F/L^3) =
          (2*(TaoFivePrimes.sineBinCount65k i.val:ℝ)*
            (4*(TaoFivePrimes.sineBinNumerator65k i.val:ℝ)/10000 + 8/2149 +
              3*(65000+1290*((i.val:ℝ)+1))/2149^2))/
                (65000+1290*(i.val:ℝ))^3 := by
        dsimp [C,F,B,L,U]
        ring
      rw [←he] at ha
      nlinarith only [ha]
