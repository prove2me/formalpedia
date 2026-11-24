-- Prove2me | solution 1 for QuantumLTF.Membership.Supplement.main_parameter_certificate_58
-- status  : ACCEPTED   (prove)
-- author  : @stockfish-soup
-- created : 2026-11-24T23:18:56.1628+00:00
-- url     : https://prove2.me/submissions/3fd4b06f-84dd-4d3a-86dc-d4bcd53aadd4

import Mathlib
import Theorems.Thm_QuantumLTF_Membership_Supplement_hermite_band_bounds_53

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

theorem section5_grid_all_terms (A C : ℝ) (hA : 0 < A) (hC : 0 ≤ C) :
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

theorem section5_hermite_degree_condition (A : ℝ) (hA : 0 < A) (hA' : A < 1/2) :
    ∃ L : ℝ, 0 < L ∧ ∀ n K : ℝ, 1 ≤ n → 1 ≤ K → L*n ≤ K →
      0 < A/K^(1/4:ℝ) ∧ A/K^(1/4:ℝ) < 1/2 ∧
      Real.log (4*n/(A/K^(1/4:ℝ))) < 2*K+1 := by
  let L := 4*(1+|Real.log (4/A)|)
  have hL : 0 < L := by dsimp [L]; positivity
  refine ⟨L,hL,?_⟩
  intro n K hn hK hsize
  have hn0 : 0 < n := by linarith
  have hK0 : 0 < K := by linarith
  have hquarter : 1 ≤ K^(1/4:ℝ) := Real.one_le_rpow hK (by norm_num)
  have hquarter0 : 0 < K^(1/4:ℝ) := Real.rpow_pos_of_pos hK0 _
  have hη : 0 < A/K^(1/4:ℝ) := div_pos hA hquarter0
  have hη' : A/K^(1/4:ℝ) < 1/2 := by
    apply (div_lt_iff₀ hquarter0).mpr
    linarith
  refine ⟨hη,hη',?_⟩
  have hKn : 4*n ≤ K := by
    have hL4 : 4 ≤ L := by dsimp [L]; linarith [abs_nonneg (Real.log (4/A))]
    exact (mul_le_mul_of_nonneg_right hL4 hn0.le).trans hsize
  have hKL : L ≤ K := (le_mul_of_one_le_right hL.le hn).trans hsize
  have hlogA : Real.log (4/A) ≤ K/4 := by
    have hh := le_abs_self (Real.log (4/A))
    dsimp [L] at hKL
    linarith
  have hlogn := Real.log_le_sub_one_of_pos hn0
  have hlogK := Real.log_le_sub_one_of_pos hK0
  have hbase : 4*n/(A/K^(1/4:ℝ)) = (4/A)*n*K^(1/4:ℝ) := by field_simp
  rw [hbase, Real.log_mul (by positivity : (4/A)*n ≠ 0) hquarter0.ne',
    Real.log_mul (by positivity : 4/A ≠ 0) hn0.ne', Real.log_rpow hK0]
  linarith

theorem section5_dyadic_grid_round_up (x : ℝ) (hx : 0 < x) :
    x ≤ (2:ℝ)^⌈Real.logb 2 x⌉₊ := by
  have hh : x ≤ (2:ℝ)^((⌈Real.logb 2 x⌉₊ : ℕ) : ℝ) :=
    (Real.logb_le_iff_le_rpow (b := 2) (x := x)
      (y := (⌈Real.logb 2 x⌉₊ : ℕ)) (by norm_num) hx).mp (Nat.le_ceil _)
  simpa only [Real.rpow_natCast] using hh

theorem section5_preparation_parameter_certificate (A C : ℝ)
    (hA : 0 < A) (hA' : A < 1/2) (hC : 0 ≤ C) :
    ∃ L B : ℝ, 0 < L ∧ 0 < B ∧ ∀ n K c2 : ℝ,
      1 ≤ n → 1 ≤ K → L*n ≤ K → B ≤ c2 →
      let η := A/K^(1/4:ℝ)
      let D := 2*K+1
      let q : ℕ := ⌈Real.logb 2 (c2*n^(13/4:ℝ)*K^(49/16:ℝ))⌉₊
      2 ≤ D ∧ 0 < η ∧ η < 1/2 ∧ Real.log (4*n/η) < D ∧
      64*n^2*(D+1) ≤ (2:ℝ)^q ∧
      20736*n^2*(D+1)/η^2 ≤ (2:ℝ)^q ∧
      165888*n/η^4 ≤ (2:ℝ)^q ∧
      4/Real.pi * Real.log (12*Real.sqrt (2*n)/η) ≤ (2:ℝ)^q ∧
      C * D^(9/4:ℝ) * (4*n/η)^(13/4:ℝ) ≤ (2:ℝ)^q := by
  obtain ⟨L,hL,hdegree⟩ := section5_hermite_degree_condition A hA hA'
  obtain ⟨B,hB,hterms⟩ := section5_grid_all_terms A C hA hC
  refine ⟨L,B,hL,hB,?_⟩
  intro n K c2 hn hK hKn hc2
  obtain ⟨hη,hη',hlog⟩ := hdegree n K hn hK hKn
  obtain ⟨h1,h2,h3,h4,h5⟩ := hterms n K hn hK
  have hS : 0 < n^(13/4:ℝ)*K^(49/16:ℝ) := by positivity
  have hcommon : B*(n^(13/4:ℝ)*K^(49/16:ℝ)) ≤
      (2:ℝ)^⌈Real.logb 2 (c2*n^(13/4:ℝ)*K^(49/16:ℝ))⌉₊ := by
    calc
      _ ≤ c2*(n^(13/4:ℝ)*K^(49/16:ℝ)) := mul_le_mul_of_nonneg_right hc2 hS.le
      _ = c2*n^(13/4:ℝ)*K^(49/16:ℝ) := by ring
      _ ≤ _ := section5_dyadic_grid_round_up _ (by
        rw [mul_assoc]; exact mul_pos (hB.trans_le hc2) hS)
  exact ⟨by linarith, hη,hη',hlog,
    h1.trans hcommon,h2.trans hcommon,h3.trans hcommon,h4.trans hcommon,h5.trans hcommon⟩


set_option autoImplicit false

theorem section5_copy_ceiling_bounds (c1 n ε : ℝ) (hc1 : 0 ≤ c1)
    (hn : 1 ≤ n) (hε : 0 < ε) (hε' : ε < 1) :
    let K : ℕ := ⌈c1*n/ε^2⌉₊
    c1*n/ε^2 ≤ (K:ℝ) ∧ (K:ℝ) ≤ (c1+1)*n/ε^2 := by
  dsimp only
  refine ⟨Nat.le_ceil _, ?_⟩
  have hR : 1 ≤ n/ε^2 := by
    apply (le_div_iff₀ (sq_pos_of_pos hε)).mpr
    nlinarith
  have hceil : (⌈c1*n/ε^2⌉₊ : ℝ) < c1*n/ε^2+1 :=
    Nat.ceil_lt_add_one (by positivity)
  calc
    _ ≤ c1*n/ε^2+1 := hceil.le
    _ ≤ c1*n/ε^2+n/ε^2 := by linarith
    _ = _ := by ring

theorem section5_copy_fourth_root_bound (c1 n ε : ℝ) (hc1 : 0 ≤ c1)
    (hn : 1 ≤ n) (hε : 0 < ε) (hε' : ε < 1) :
    ((⌈c1*n/ε^2⌉₊ : ℕ) : ℝ)^(1/4:ℝ) ≤
      (c1+1)^(1/4:ℝ)*n^(1/4:ℝ)/Real.sqrt ε := by
  have hupper := (section5_copy_ceiling_bounds c1 n ε hc1 hn hε hε').2
  have hh := Real.rpow_le_rpow (Nat.cast_nonneg _) hupper (show (0:ℝ) ≤ 1/4 by norm_num)
  rw [Real.div_rpow (by positivity) (sq_nonneg ε),
    Real.mul_rpow (by positivity : 0 ≤ c1+1) (by linarith : 0 ≤ n)] at hh
  have heps : (ε^2)^(1/4:ℝ) = Real.sqrt ε := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hε.le, Real.sqrt_eq_rpow]
    norm_num
  rwa [heps] at hh

theorem section5_query_scaling (c1 : ℝ) (hc1 : 0 ≤ c1) :
    ∃ B : ℝ, 0 < B ∧ ∀ n ε : ℝ, 1 ≤ n → 0 < ε → ε < 1 →
      ((⌈c1*n/ε^2⌉₊ : ℕ) : ℝ)^(1/4:ℝ)+3 ≤ B*n^(1/4:ℝ)/Real.sqrt ε := by
  let B := (c1+1)^(1/4:ℝ)+3
  have hB : 0 < B := by dsimp [B]; positivity
  refine ⟨B,hB,?_⟩
  intro n ε hn hε hε'
  have hh := section5_copy_fourth_root_bound c1 n ε hc1 hn hε hε'
  have hnq : 1 ≤ n^(1/4:ℝ) := Real.one_le_rpow hn (by norm_num)
  have hs : 0 < Real.sqrt ε := Real.sqrt_pos.mpr hε
  have hs1 : Real.sqrt ε ≤ 1 := by
    nlinarith [Real.sq_sqrt hε.le, Real.sqrt_nonneg ε]
  have hr : 1 ≤ n^(1/4:ℝ)/Real.sqrt ε := (le_div_iff₀ hs).mpr (by linarith)
  dsimp [B]
  simp only [add_mul, add_div, mul_div_assoc] at *
  nlinarith

theorem section5_gate_scaling (c1 : ℝ) (hc1 : 0 ≤ c1) :
    ∃ B : ℝ, 0 < B ∧ ∀ n ε : ℝ, 1 ≤ n → 0 < ε → ε < 1 →
      let K : ℕ := ⌈c1*n/ε^2⌉₊
      n*(K:ℝ)^(1/4:ℝ)+(K:ℝ) ≤ B*(n^(5/4:ℝ)/Real.sqrt ε+n/ε^2) := by
  let b1 := (c1+1)^(1/4:ℝ)
  let b2 := c1+1
  let B := b1+b2
  have hb1 : 0 < b1 := by dsimp [b1]; positivity
  have hb2 : 0 < b2 := by dsimp [b2]; linarith
  refine ⟨B, by dsimp [B]; linarith, ?_⟩
  intro n ε hn hε hε'
  have hn0 : 0 < n := by linarith
  have hroot := section5_copy_fourth_root_bound c1 n ε hc1 hn hε hε'
  have hceil := (section5_copy_ceiling_bounds c1 n ε hc1 hn hε hε').2
  have hnprod : n*n^(1/4:ℝ) = n^(5/4:ℝ) := by
    conv_lhs => lhs; rw [← Real.rpow_one n]
    rw [← Real.rpow_add hn0]
    norm_num
  have hnroot : n*((⌈c1*n/ε^2⌉₊ : ℕ):ℝ)^(1/4:ℝ) ≤ b1*n^(5/4:ℝ)/Real.sqrt ε := by
    calc
      _ ≤ n*((c1+1)^(1/4:ℝ)*n^(1/4:ℝ)/Real.sqrt ε) :=
        mul_le_mul_of_nonneg_left hroot hn0.le
      _ = b1*n^(5/4:ℝ)/Real.sqrt ε := by dsimp [b1]; rw [← hnprod]; ring
  have hp1 : 0 ≤ n^(5/4:ℝ)/Real.sqrt ε := by positivity
  have hp2 : 0 ≤ n/ε^2 := by positivity
  change n*_+_ ≤ _
  dsimp [B]
  dsimp [b2] at hb2 ⊢
  simp only [mul_div_assoc] at hnroot hceil ⊢
  nlinarith [mul_nonneg hb1.le hp2, mul_nonneg hb2.le hp1]


set_option autoImplicit false

theorem section5_main_parameter_suite (A C : ℝ)
    (hA : 0 < A) (hA' : A < 1/2) (hC : 0 ≤ C) :
    ∃ c1₀ c2₀ : ℝ, 0 < c1₀ ∧ 0 < c2₀ ∧
      ∀ c1 c2 : ℝ, c1₀ ≤ c1 → c2₀ ≤ c2 →
        ∃ R : ℝ, 0 < R ∧ ∀ n ε : ℝ, 1 ≤ n → 0 < ε → ε < 1/2 →
          let K : ℕ := ⌈c1*n/ε^2⌉₊
          let η := A/(K:ℝ)^(1/4:ℝ)
          let D := 2*(K:ℝ)+1
          let q : ℕ := ⌈Real.logb 2 (c2*n^(13/4:ℝ)*(K:ℝ)^(49/16:ℝ))⌉₊
          (2 ≤ D ∧ 0 < η ∧ η < 1/2 ∧ Real.log (4*n/η) < D ∧
            64*n^2*(D+1) ≤ (2:ℝ)^q ∧
            20736*n^2*(D+1)/η^2 ≤ (2:ℝ)^q ∧
            165888*n/η^4 ≤ (2:ℝ)^q ∧
            4/Real.pi * Real.log (12*Real.sqrt (2*n)/η) ≤ (2:ℝ)^q ∧
            C*D^(9/4:ℝ)*(4*n/η)^(13/4:ℝ) ≤ (2:ℝ)^q) ∧
          (K:ℝ)^(1/4:ℝ)+3 ≤ R*n^(1/4:ℝ)/Real.sqrt ε ∧
          n*(K:ℝ)^(1/4:ℝ)+(K:ℝ) ≤ R*(n^(5/4:ℝ)/Real.sqrt ε+n/ε^2) := by
  obtain ⟨L,B,hL,hB,hprep⟩ := section5_preparation_parameter_certificate A C hA hA' hC
  refine ⟨max L 1,B,lt_of_lt_of_le (by norm_num) (le_max_right _ _),hB,?_⟩
  intro c1 c2 hc1 hc2
  have hc11 : 1 ≤ c1 := (le_max_right L 1).trans hc1
  have hc1L : L ≤ c1 := (le_max_left L 1).trans hc1
  have hc10 : 0 ≤ c1 := by linarith
  obtain ⟨R1,hR1,hquery⟩ := section5_query_scaling c1 hc10
  obtain ⟨R2,hR2,hgate⟩ := section5_gate_scaling c1 hc10
  refine ⟨R1+R2,by linarith,?_⟩
  intro n ε hn hε hε'
  let K : ℕ := ⌈c1*n/ε^2⌉₊
  have hn0 : 0 ≤ n := by linarith
  have hε1 : ε < 1 := by linarith
  have hlo : c1*n/ε^2 ≤ (K:ℝ) := Nat.le_ceil _
  have hdiv : c1*n ≤ c1*n/ε^2 := by
    apply (le_div_iff₀ (sq_pos_of_pos hε)).mpr
    nlinarith [mul_nonneg (mul_nonneg hc10 hn0) (show 0 ≤ 1-ε^2 by nlinarith)]
  have hcn : n ≤ c1*n := by nlinarith
  have hK : 1 ≤ (K:ℝ) := hn.trans ((hcn.trans hdiv).trans hlo)
  have hKL : L*n ≤ (K:ℝ) :=
    ((mul_le_mul_of_nonneg_right hc1L hn0).trans hdiv).trans hlo
  refine ⟨hprep n (K:ℝ) c2 hn hK hKL hc2,?_,?_⟩
  · exact (hquery n ε hn hε hε1).trans (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right (by linarith : R1 ≤ R1+R2) (Real.rpow_nonneg hn0 _))
      (Real.sqrt_nonneg ε))
  · exact (hgate n ε hn hε hε1).trans (mul_le_mul_of_nonneg_right
      (by linarith : R2 ≤ R1+R2) (by positivity))


set_option autoImplicit false
open QuantumLTF.Membership.Supplement

theorem section5_uniform_band_error_budget :
    ∃ A : ℝ, 0 < A ∧ A < 1/2 ∧
      ∀ n K : ℕ, 1 ≤ K → ∀ w : EuclideanSpace ℝ (Fin n), ‖w‖ = 1 →
        A/(K:ℝ)^(1/4:ℝ) ≤ Real.sqrt (bandWeight w K)/192 := by
  obtain ⟨c,hc,hmass,hrot⟩ := hermite_band_bounds_53.1
  have hc1 : c ≤ 1 := by
    have hh := (hmass 1 (by norm_num)).1
    norm_num at hh
    exact hh.trans (hmass 1 (by norm_num)).2
  let A := Real.sqrt c/192
  have hA : 0 < A := by dsimp [A]; positivity
  have hA' : A < 1/2 := by
    have hs := Real.sq_sqrt hc.le
    have hs0 := Real.sqrt_nonneg c
    have hs1 : Real.sqrt c ≤ 1 := by nlinarith
    dsimp [A]
    linarith
  refine ⟨A,hA,hA',?_⟩
  intro n K hK w hw
  have hK0 : (0:ℝ) < K := by exact_mod_cast hK
  have hl : c/Real.sqrt (K:ℝ) ≤ bandWeight w K := by
    rw [hrot n K w hw]
    exact (hmass K hK).1
  have hr : Real.sqrt c/Real.sqrt (Real.sqrt (K:ℝ)) ≤ Real.sqrt (bandWeight w K) := by
    simpa only [Real.sqrt_div hc.le] using Real.sqrt_le_sqrt hl
  have hquarter : (K:ℝ)^(1/4:ℝ) = Real.sqrt (Real.sqrt (K:ℝ)) := by
    rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, ← Real.rpow_mul hK0.le]
    norm_num
  calc
    _ = (Real.sqrt c/Real.sqrt (Real.sqrt (K:ℝ)))/192 := by rw [hquarter]; dsimp [A]; ring
    _ ≤ _ := div_le_div_of_nonneg_right hr (by norm_num)


theorem solution :
    ∃ A : ℝ, 0 < A ∧ A < 1/2 ∧
      (∀ n K : ℕ, 1 ≤ K → ∀ w : EuclideanSpace ℝ (Fin n), ‖w‖ = 1 →
        A/(K:ℝ)^(1/4:ℝ) ≤ Real.sqrt (bandWeight w K)/192) ∧
      ∀ C : ℝ, 0 ≤ C →
      ∃ c1₀ c2₀ : ℝ, 0 < c1₀ ∧ 0 < c2₀ ∧
      ∀ c1 c2 : ℝ, c1₀ ≤ c1 → c2₀ ≤ c2 →
        ∃ R : ℝ, 0 < R ∧ ∀ n ε : ℝ, 1 ≤ n → 0 < ε → ε < 1/2 →
          let K : ℕ := ⌈c1*n/ε^2⌉₊
          let η := A/(K:ℝ)^(1/4:ℝ)
          let D := 2*(K:ℝ)+1
          let q : ℕ := ⌈Real.logb 2 (c2*n^(13/4:ℝ)*(K:ℝ)^(49/16:ℝ))⌉₊
          (2 ≤ D ∧ 0 < η ∧ η < 1/2 ∧ Real.log (4*n/η) < D ∧
            64*n^2*(D+1) ≤ (2:ℝ)^q ∧
            20736*n^2*(D+1)/η^2 ≤ (2:ℝ)^q ∧
            165888*n/η^4 ≤ (2:ℝ)^q ∧
            4/Real.pi * Real.log (12*Real.sqrt (2*n)/η) ≤ (2:ℝ)^q ∧
            C*D^(9/4:ℝ)*(4*n/η)^(13/4:ℝ) ≤ (2:ℝ)^q) ∧
          (K:ℝ)^(1/4:ℝ)+3 ≤ R*n^(1/4:ℝ)/Real.sqrt ε ∧
          n*(K:ℝ)^(1/4:ℝ)+(K:ℝ) ≤ R*(n^(5/4:ℝ)/Real.sqrt ε+n/ε^2) := by
  obtain ⟨A,hA,hA',hband⟩ := section5_uniform_band_error_budget
  refine ⟨A,hA,hA',hband,?_⟩
  intro C hC
  exact section5_main_parameter_suite A C hA hA' hC
