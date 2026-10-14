-- Prove2me | solution 1 for ThreeSumSharpTail.rational_cost_regime
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-13T18:24:01.898886+00:00
-- url     : https://prove2.me/submissions/c07f7f9e-790c-472a-a9b6-23e9c94e74b2

import Definitions.Def_ThreeSumSharpTail_Analysis
import Definitions.Def_APSP299791_Defs4
import Theorems.Thm_ThreeSumSharpTail_pruned_cost_certificate

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace Nat

private theorem ceil_div_eq_ceilDiv (a : ℕ) {b : ℕ} (hb : 0 < b) :
    ⌈(a : ℝ) / (b : ℝ)⌉₊ = a ⌈/⌉ b := by
  refine eq_of_forall_ge_iff fun k => ?_
  rw [Nat.ceil_le, div_le_iff₀ (Nat.cast_pos.2 hb), ceilDiv_le_iff_le_mul hb]
  norm_cast
  simp [Nat.mul_comm]

end Nat

open ThreeSumApsp Light.Sec4

namespace ThreeSumApsp

private theorem levelsOf_div (a m : ℕ) {b : ℕ} (hb : 1 ≤ b) :
    levelsOf ((a : ℝ) / b) m = (a * m + b - 1) / b := by
  unfold levelsOf
  rw [← Nat.ceilDiv_eq_add_pred_div, ← Nat.ceil_div_eq_ceilDiv (a * m) hb]
  congr 1
  push_cast
  ring

private theorem switchOf_div (p m : ℕ) {q : ℕ} (hq : 1 ≤ q) :
    switchOf ((p : ℝ) / q) m = (p * m + q - 1) / q := by
  unfold switchOf
  rw [← Nat.ceilDiv_eq_add_pred_div, ← Nat.ceil_div_eq_ceilDiv (p * m) hq]
  congr 1
  push_cast
  ring

end ThreeSumApsp

theorem solution
    (c : ℕ) (η a s : ℚ) (hc : 10 < c)
    (hη0 : 0 < η) (hη9 : η < 9 / 10)
    (ha0 : 0 < a) (ha1 : (a : ℝ) < 1)
    (hs0 : 0 < s) (hs5 : (s : ℝ) < 1 / 2)
    (henc : (a : ℝ) * (ThreeSumSharpTail.encodingExponent c +
      ThreeSumSharpTail.sharpSaving c (η : ℝ)) < 1)
    (hprep : (s : ℝ) < ThreeSumSharpTail.sharpSaving c (η : ℝ))
    (hquery : (s : ℝ) < 1 / 2 - ThreeSumSharpTail.queryExponent (η : ℝ)) :
    ∃ G : Light.Sec4.RatParams, ∃ C : ℝ, 0 ≤ C ∧
      ∀ N D₀ : ℕ, 1 ≤ D₀ → (D₀ : ℝ) ≤ (N : ℝ) ^ (a : ℝ) →
        Light.Sec4.CostsWithinP G C N D₀
          ((N : ℝ) ^ 2 * (Real.log (D₀ : ℝ) + 1) ^ 2 / (D₀ : ℝ) ^ (s : ℝ))
          ((D₀ : ℝ) ^ (1 / 2 - (s : ℝ)) * (Real.log (D₀ : ℝ) + 1)) := by
  have hcR : 10 < (c : ℝ) := by exact_mod_cast hc
  have hη0R : 0 < (η : ℝ) := by exact_mod_cast hη0
  have hη9R : (η : ℝ) < 9 / 10 := by
    have hcast : (η : ℝ) < ((9 / 10 : ℚ) : ℝ) := Rat.cast_lt.mpr hη9
    norm_num at hcast
    exact hcast
  have ha0R : 0 < (a : ℝ) := by exact_mod_cast ha0
  have hs0R : 0 < (s : ℝ) := by exact_mod_cast hs0
  let p : ℕ := η.num.natAbs
  let q : ℕ := η.den
  have hq : 0 < q := by exact_mod_cast η.den_pos
  have hnumR : (η.num : ℝ) = (η : ℝ) * (η.den : ℝ) := by
    have hcast : (η.num : ℝ) / (η.den : ℝ) = (η : ℝ) := by
      exact_mod_cast Rat.num_div_den η
    exact (div_eq_iff (by exact_mod_cast (ne_of_gt η.den_pos))).1 hcast
  have hnum_nonneg : 0 ≤ η.num := (Rat.num_pos.mpr hη0).le
  have hpCast : (p : ℝ) = (η.num : ℝ) := by
    dsimp [p]
    have hi : (η.num.natAbs : ℤ) = η.num := Int.natAbs_of_nonneg hnum_nonneg
    have hr := congrArg (fun z : ℤ => (z : ℝ)) hi
    simpa using hr
  have heta : (p : ℝ) / (q : ℝ) = (η : ℝ) := by
    rw [hpCast]
    dsimp [q]
    rw [hnumR]
    field_simp
  have hp : 0 < p := by
    dsimp [p]
    exact Int.natAbs_pos.mpr (ne_of_gt (Rat.num_pos.mpr hη0))
  have hpBound : 10 * p < 9 * q := by
    have hqR : (0 : ℝ) < q := by exact_mod_cast hq
    have hmul : (p : ℝ) = (η : ℝ) * q := by
      have := heta
      field_simp at this ⊢
      nlinarith
    have h := mul_lt_mul_of_pos_right hη9R hqR
    rw [← hmul] at h
    have hNat : (10 : ℝ) * (p : ℝ) < 9 * (q : ℝ) := by norm_num at h ⊢; nlinarith
    exact_mod_cast hNat
  obtain ⟨C, mC, hC, hcert⟩ :=
    ThreeSumSharpTail.pruned_cost_certificate c (η : ℝ) a s hc hη0R hη9R ha0 henc hprep hquery
  let mThreshold := max mC 1
  let G : Light.Sec4.RatParams := {
    a := c
    b := 1
    p := p
    q := q
    m₀ := mThreshold
    hb := by norm_num
    hq := by exact_mod_cast hq
    hc := by simpa using hc
    hp := by exact_mod_cast hp
    hθ := by exact_mod_cast hpBound
    hm₀ := le_max_right _ _
  }
  have hL (m : ℕ) : G.L m = ThreeSumApsp.levelsOf (c : ℝ) m := by
    change (c * m + 1 - 1) / 1 = ThreeSumApsp.levelsOf (c : ℝ) m
    simpa using (ThreeSumApsp.levelsOf_div c m (b := 1) (by norm_num)).symm
  have ht (m : ℕ) : G.t m = switchOf (η : ℝ) m := by
    change (p * m + q - 1) / q = ⌈(η : ℝ) * (m : ℝ)⌉₊
    rw [← heta]
    exact (ThreeSumApsp.switchOf_div p m (Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hq))).symm
  refine ⟨G, C, hC, fun N D₀ hD hDN => ?_⟩
  have hDnat : 1 ≤ D₀ := hD
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by
    by_contra hN
    have hNlt : (N : ℝ) < 1 := lt_of_not_ge hN
    have hpowLt : (N : ℝ) ^ (a : ℝ) < 1 :=
      Real.rpow_lt_one (by positivity) hNlt ha0R
    have hDcast : (1 : ℝ) ≤ (D₀ : ℝ) := by exact_mod_cast hD
    linarith
  have hNpos : 0 < (N : ℝ) := lt_of_lt_of_le (by norm_num) hN1
  have hN : 1 ≤ N := by exact_mod_cast hN1
  have haLe : (a : ℝ) ≤ 1 := ha1.le
  have hNa : (N : ℝ) ^ (a : ℝ) ≤ (N : ℝ) := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hN1 haLe
  have hDleN : D₀ ≤ N := by exact_mod_cast (hDN.trans hNa)
  have hlog : 0 ≤ Real.log (D₀ : ℝ) := Real.log_nonneg (by exact_mod_cast hDnat)
  have hlog1 : 1 ≤ Real.log (D₀ : ℝ) + 1 := by linarith
  have hpowS_leN : (D₀ : ℝ) ^ (s : ℝ) ≤ (N : ℝ) := by
    have hbase := Real.rpow_le_rpow (by positivity : (0 : ℝ) ≤ (D₀ : ℝ)) hDN hs0R.le
    have hmulpow : ((N : ℝ) ^ (a : ℝ)) ^ (s : ℝ) =
        (N : ℝ) ^ ((a : ℝ) * (s : ℝ)) := by
      rw [← Real.rpow_mul hNpos.le]
    have has : (a : ℝ) * (s : ℝ) ≤ 1 := by nlinarith [ha1, hs5]
    have hpowN : (N : ℝ) ^ ((a : ℝ) * (s : ℝ)) ≤ (N : ℝ) := by
      simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hN1 has
    rw [hmulpow] at hbase
    exact hbase.trans hpowN
  have hpre : 1 ≤
      (N : ℝ) ^ 2 * (Real.log (D₀ : ℝ) + 1) ^ 2 / (D₀ : ℝ) ^ (s : ℝ) := by
    have hdenpos : 0 < (D₀ : ℝ) ^ (s : ℝ) := Real.rpow_pos_of_pos (by positivity) _
    have hN2 : (N : ℝ) ≤ (N : ℝ) ^ 2 := by nlinarith [hN1]
    apply (one_le_div hdenpos).2
    calc
      (D₀ : ℝ) ^ (s : ℝ) ≤ (N : ℝ) := hpowS_leN
      _ ≤ (N : ℝ) ^ 2 := hN2
      _ ≤ (N : ℝ) ^ 2 * (Real.log (D₀ : ℝ) + 1) ^ 2 := by
        have hsq : (1 : ℝ) ≤ (Real.log (D₀ : ℝ) + 1) ^ 2 := by nlinarith [hlog1]
        calc
          (N : ℝ) ^ 2 = (N : ℝ) ^ 2 * 1 := by ring
          _ ≤ (N : ℝ) ^ 2 * (Real.log (D₀ : ℝ) + 1) ^ 2 :=
            mul_le_mul_of_nonneg_left hsq (sq_nonneg (N : ℝ))
  have hqueryBase : 1 ≤
      (D₀ : ℝ) ^ (1 / 2 - (s : ℝ)) * (Real.log (D₀ : ℝ) + 1) := by
    have hexp : 0 ≤ 1 / 2 - (s : ℝ) := by linarith
    have hpow : 1 ≤ (D₀ : ℝ) ^ (1 / 2 - (s : ℝ)) :=
      Real.one_le_rpow (by exact_mod_cast hDnat) hexp
    nlinarith [hpow, hlog1]
  refine ⟨hN, hDnat, hDleN, hpre, hqueryBase, ?_⟩
  intro hthreshold
  have hm0 : mC ≤ logFour D₀ := by
    change mThreshold ≤ logFour D₀ at hthreshold
    exact (le_trans (le_max_left _ _) hthreshold)
  have hm : logFour D₀ = ⌈Real.logb 4 (D₀ : ℝ)⌉₊ := by
    unfold logFour
    exact (Real.natCeil_logb_natCast 4 D₀).symm
  have hD2 : 2 ≤ D₀ := by
    by_contra h
    have : D₀ = 1 := by omega
    subst D₀
    have hzero : logFour 1 = 0 := by simp [logFour]
    rw [hzero] at hthreshold
    change mThreshold ≤ 0 at hthreshold
    omega
  have hresult := hcert D₀ N (logFour D₀) hD2 hDN hm hm0
  rcases hresult with ⟨hsize, hpreCert, hqueryCert⟩
  have hpreLog :
      (N : ℝ) ^ 2 * Real.log (D₀ : ℝ) ^ 2 / (D₀ : ℝ) ^ (s : ℝ) ≤
      (N : ℝ) ^ 2 * (Real.log (D₀ : ℝ) + 1) ^ 2 / (D₀ : ℝ) ^ (s : ℝ) := by
    have hsq : Real.log (D₀ : ℝ) ^ 2 ≤
        (Real.log (D₀ : ℝ) + 1) ^ 2 := by nlinarith [hlog]
    have hnum := mul_le_mul_of_nonneg_left hsq (sq_nonneg (N : ℝ))
    exact div_le_div_of_nonneg_right hnum (by positivity)
  have hqueryLog : Real.log (D₀ : ℝ) ≤ Real.log (D₀ : ℝ) + 1 := by linarith
  have hpreFinal :
      cost8p (G.L (logFour D₀)) (logFour D₀) (switchOf31 G D₀) N ≤
        C * ((N : ℝ) ^ 2 * (Real.log (D₀ : ℝ) + 1) ^ 2 /
          (D₀ : ℝ) ^ (s : ℝ)) := by
      simpa [Light.Sec4.switchOf31, hL, ht] using
      hpreCert.trans (mul_le_mul_of_nonneg_left hpreLog hC)
  have hqueryFinal :
      costQuery (G.L (logFour D₀)) (logFour D₀) (switchOf31 G D₀) ≤
        C * ((D₀ : ℝ) ^ (1 / 2 - (s : ℝ)) *
          (Real.log (D₀ : ℝ) + 1)) := by
      have hD0R : (0 : ℝ) ≤ (D₀ : ℝ) := by
        exact_mod_cast (show 0 ≤ D₀ by omega)
      have hlogScaled := mul_le_mul_of_nonneg_left hqueryLog
        (Real.rpow_nonneg hD0R (1 / 2 - (s : ℝ)))
      simpa [Light.Sec4.switchOf31, hL, ht] using
        hqueryCert.trans (mul_le_mul_of_nonneg_left hlogScaled hC)
  have hHyp : Hyp30 (parOf G N D₀) (switchOf31 G D₀) := by
    have hmpos : 1 ≤ logFour D₀ := by
      unfold logFour
      exact Nat.succ_le_iff.mpr
        (Nat.clog_pos (b := 4) (n := D₀) (by norm_num) (by omega))
    have htle : switchOf (η : ℝ) (logFour D₀) ≤ logFour D₀ :=
      switchOf_le (by linarith : (η : ℝ) ≤ 1) _
    have hsize' : sqrtKN0 (parOf G N D₀).L (parOf G N D₀).m ≤
        ((parOf G N D₀).N : ℝ) := by
      simpa [Light.Sec4.parOf, hL] using hsize
    refine ⟨hmpos, ?_, ?_, hsize'⟩
    · simpa [Light.Sec4.parOf, hL] using G.ten_le_L (logFour D₀)
    · change switchOf31 G D₀ ≤ logFour D₀
      simpa [Light.Sec4.switchOf31, ht] using htle
  exact ⟨hHyp, hpreFinal, hqueryFinal⟩

#print axioms solution
