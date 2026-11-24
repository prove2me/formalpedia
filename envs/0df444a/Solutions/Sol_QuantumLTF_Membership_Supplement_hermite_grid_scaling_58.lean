-- Prove2me | solution 1 for QuantumLTF.Membership.Supplement.hermite_grid_scaling_58
-- status  : ACCEPTED   (prove)
-- author  : @stockfish-soup
-- created : 2026-11-24T19:53:18.304214+00:00
-- url     : https://prove2.me/submissions/5d9fcd80-2206-4bce-9f84-856ff2d96faf

import Mathlib

set_option autoImplicit false

theorem section5_hermite_grid_main_term (n K A C : ℝ)
    (hn : 0 ≤ n) (hK : 1 ≤ K) (hA : 0 < A) (hC : 0 ≤ C) :
    C * (2*K+1)^(9/4:ℝ) * (4*n / (A / K^(1/4:ℝ)))^(13/4:ℝ) ≤
      (C * 3^(9/4:ℝ) * (4/A)^(13/4:ℝ)) * n^(13/4:ℝ) * K^(49/16:ℝ) := by
  have hK0 : 0 < K := by linarith
  have hkp : 0 < K^(1/4:ℝ) := Real.rpow_pos_of_pos hK0 _
  have hbase : 4*n / (A / K^(1/4:ℝ)) = (4/A) * n * K^(1/4:ℝ) := by
    field_simp
  calc
    _ ≤ C * (3*K)^(9/4:ℝ) * (4*n / (A / K^(1/4:ℝ)))^(13/4:ℝ) := by
      apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (by positivity) _)
      exact mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (by positivity) (by linarith) (by norm_num)) hC
    _ = _ := by
      rw [hbase, Real.mul_rpow (by norm_num : (0:ℝ) ≤ 3) hK0.le,
        Real.mul_rpow (by positivity : 0 ≤ (4/A)*n) hkp.le,
        Real.mul_rpow (by positivity : 0 ≤ 4/A) hn,
        ← Real.rpow_mul hK0.le]
      have hexp : K^(9/4:ℝ) * K^((1/4:ℝ)*(13/4:ℝ)) = K^(49/16:ℝ) := by
        rw [← Real.rpow_add hK0]
        norm_num
      calc
        _ = (C * 3^(9/4:ℝ) * (4/A)^(13/4:ℝ)) * n^(13/4:ℝ) *
            (K^(9/4:ℝ) * K^((1/4:ℝ)*(13/4:ℝ))) := by ring
        _ = _ := by rw [hexp]

theorem solution (A C : ℝ) (hA : 0 < A) (hC : 0 ≤ C) :
    ∃ B : ℝ, 0 < B ∧ ∀ n K : ℝ, 1 ≤ n → 1 ≤ K →
      let η := A / K^(1/4:ℝ)
      let D := 2*K+1
      let S := n^(13/4:ℝ) * K^(49/16:ℝ)
      64*n^2*(D+1) ≤ B*S ∧
      20736*n^2*(D+1)/η^2 ≤ B*S ∧
      165888*n/η^4 ≤ B*S ∧
      4/Real.pi * Real.log (12*Real.sqrt (2*n)/η) ≤ B*S ∧
      C * D^(9/4:ℝ) * (4*n/η)^(13/4:ℝ) ≤ B*S := by
  let c2 := 82944/A^2
  let c3 := 165888/A^4
  let c4 := (4/Real.pi)*(24/A)
  let c5 := C*3^(9/4:ℝ)*(4/A)^(13/4:ℝ)
  let B := 1+256+c2+c3+c4+c5
  have hc2 : 0 ≤ c2 := by dsimp [c2]; positivity
  have hc3 : 0 ≤ c3 := by dsimp [c3]; positivity
  have hc4 : 0 ≤ c4 := by dsimp [c4]; positivity
  have hc5 : 0 ≤ c5 := by dsimp [c5]; positivity
  have h256 : 256 ≤ B := by dsimp [B]; linarith
  have h2 : c2 ≤ B := by dsimp [B]; linarith
  have h3 : c3 ≤ B := by dsimp [B]; linarith
  have h4 : c4 ≤ B := by dsimp [B]; linarith
  have h5 : c5 ≤ B := by dsimp [B]; linarith
  refine ⟨B, by linarith, ?_⟩
  intro n K hn hK
  dsimp only
  let η := A/K^(1/4:ℝ)
  let S := n^(13/4:ℝ)*K^(49/16:ℝ)
  have hn0 : 0 < n := by linarith
  have hK0 : 0 < K := by linarith
  have hη : 0 < η := div_pos hA (Real.rpow_pos_of_pos hK0 _)
  have hS : 0 ≤ S := by dsimp [S]; positivity
  have mon (a b : ℝ) (ha : a ≤ 13/4) (hb : b ≤ 49/16) : n^a*K^b ≤ S := by
    exact mul_le_mul
      (Real.rpow_le_rpow_of_exponent_le hn ha)
      (Real.rpow_le_rpow_of_exponent_le hK hb)
      (Real.rpow_nonneg hK0.le _) (Real.rpow_nonneg hn0.le _)
  have hm21 : n^2*K ≤ S := by simpa using mon 2 1 (by norm_num) (by norm_num)
  have hm23 : n^2*K^(3/2:ℝ) ≤ S := by simpa using mon 2 (3/2) (by norm_num) (by norm_num)
  have hm11 : n*K ≤ S := by simpa using mon 1 1 (by norm_num) (by norm_num)
  have hm14 : n*K^(1/4:ℝ) ≤ S := by simpa using mon 1 (1/4) (by norm_num) (by norm_num)
  have hraw : n^2*(2*K+1+1) ≤ 4*n^2*K := by
    nlinarith [mul_nonneg (sq_nonneg n) (show 0 ≤ K-1 by linarith)]
  have hη2 : η^2 = A^2/K^(1/2:ℝ) := by
    dsimp [η]
    rw [div_pow]
    congr 1
    rw [← Real.rpow_natCast, ← Real.rpow_mul hK0.le]
    norm_num
  have hη4 : η^4 = A^4/K := by
    dsimp [η]
    rw [div_pow]
    congr 1
    rw [← Real.rpow_natCast, ← Real.rpow_mul hK0.le]
    norm_num
  have hK15 : K*K^(1/2:ℝ) = K^(3/2:ℝ) := by
    conv_lhs => lhs; rw [← Real.rpow_one K]
    rw [← Real.rpow_add hK0]
    norm_num
  have ht1 : 64*n^2*(2*K+1+1) ≤ 256*S := by nlinarith
  have ht2 : 20736*n^2*(2*K+1+1)/η^2 ≤ c2*S := by
    calc
      _ ≤ 82944*n^2*K/η^2 := by
        apply div_le_div_of_nonneg_right _ (sq_nonneg η)
        nlinarith
      _ = c2*(n^2*K^(3/2:ℝ)) := by
        rw [hη2, div_div_eq_mul_div]
        dsimp [c2]
        rw [show 82944*n^2*K*K^(1/2:ℝ)/A^2 = (82944/A^2)*(n^2*(K*K^(1/2:ℝ))) by ring]
        rw [hK15]
      _ ≤ c2*S := mul_le_mul_of_nonneg_left hm23 hc2
  have ht3 : 165888*n/η^4 ≤ c3*S := by
    calc
      _ = c3*(n*K) := by rw [hη4, div_div_eq_mul_div]; dsimp [c3]; ring
      _ ≤ c3*S := mul_le_mul_of_nonneg_left hm11 hc3
  have hsqrt : Real.sqrt (2*n) ≤ 2*n := by
    nlinarith [Real.sq_sqrt (show 0 ≤ 2*n by positivity), Real.sqrt_nonneg (2*n)]
  have harg : 0 < 12*Real.sqrt (2*n)/η := by positivity
  have hlog : Real.log (12*Real.sqrt (2*n)/η) ≤ 12*Real.sqrt (2*n)/η :=
    le_trans (Real.log_le_sub_one_of_pos harg) (by linarith)
  have ht4 : 4/Real.pi * Real.log (12*Real.sqrt (2*n)/η) ≤ c4*S := by
    calc
      _ ≤ 4/Real.pi * (12*Real.sqrt (2*n)/η) :=
        mul_le_mul_of_nonneg_left hlog (by positivity)
      _ ≤ 4/Real.pi * (24*n/η) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply div_le_div_of_nonneg_right _ hη.le
        linarith
      _ = c4*(n*K^(1/4:ℝ)) := by dsimp [c4,η]; field_simp
      _ ≤ c4*S := mul_le_mul_of_nonneg_left hm14 hc4
  have ht5 : C*(2*K+1)^(9/4:ℝ)*(4*n/η)^(13/4:ℝ) ≤ c5*S := by
    simpa [η,c5,S,mul_assoc] using section5_hermite_grid_main_term n K A C hn0.le hK hA hC
  exact ⟨ht1.trans (mul_le_mul_of_nonneg_right h256 hS),
    ht2.trans (mul_le_mul_of_nonneg_right h2 hS),
    ht3.trans (mul_le_mul_of_nonneg_right h3 hS),
    ht4.trans (mul_le_mul_of_nonneg_right h4 hS),
    ht5.trans (mul_le_mul_of_nonneg_right h5 hS)⟩
