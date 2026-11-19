-- Prove2me | solution 1 for TightCoreset2027.Euclidean.numeric_scale_selection
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T14:19:50.608517+00:00
-- url     : https://prove2.me/submissions/52a25b76-4212-411e-a059-63f8fbccf976

import Definitions.Def_TightCoreset2027_Euclidean_generalPowers
open scoped BigOperators Classical
set_option autoImplicit false
set_option linter.all false
set_option maxHeartbeats 2000000
namespace TightCoreset2027.Euclidean
lemma copyCountZ_bounds (z : ℝ) (hz : 1 ≤ z) (n : ℕ) (hn : 1 ≤ n) :
    (n : ℝ) ^ (z / 2) ≤ (copyCountZ z n : ℝ) ∧
      (copyCountZ z n : ℝ) ≤ 2 * (n : ℝ) ^ (z / 2) := by
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hp : 1 ≤ (n : ℝ) ^ (z / 2) := Real.one_le_rpow hnR (by linarith)
  unfold copyCountZ
  simp only [Real.rpow_eq_pow]
  constructor
  · exact Nat.le_ceil _
  · have hh := Nat.ceil_lt_add_one (show 0 ≤ (n : ℝ) ^ (z / 2) by positivity)
    linarith

lemma copyCountZ_pos (z : ℝ) (hz : 1 ≤ z) (n : ℕ) (hn : 1 ≤ n) : 1 ≤ copyCountZ z n := by
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hp : 1 ≤ (n : ℝ) ^ (z / 2) := Real.one_le_rpow hnR (by linarith)
  have h := (copyCountZ_bounds z hz n hn).1
  have : (1 : ℝ) ≤ copyCountZ z n := hp.trans h
  exact_mod_cast this


end TightCoreset2027.Euclidean
open scoped BigOperators Classical
set_option autoImplicit false
set_option linter.all false
set_option maxHeartbeats 2000000
namespace TightCoreset2027.Euclidean

lemma floor_bounds_of_one_le (x : ℝ) (hx : 1 ≤ x) :
    1 ≤ ⌊x⌋₊ ∧ (⌊x⌋₊ : ℝ) ≤ x ∧ x / 2 ≤ (⌊x⌋₊ : ℝ) := by
  have h1 : 1 ≤ ⌊x⌋₊ := Nat.le_floor (by simpa using hx)
  have h1R : (1 : ℝ) ≤ ⌊x⌋₊ := by exact_mod_cast h1
  have hf := Nat.lt_floor_add_one x
  exact ⟨h1, Nat.floor_le (by linarith), by linarith⟩

lemma inverse_square_rpow (ε : ℝ) (hε : 0 < ε) :
    Real.rpow ε (-2) = (1 / ε) ^ 2 := by
  rw [Real.rpow_eq_pow, Real.rpow_neg hε.le, Real.rpow_two]
  simp [one_div, inv_pow]

lemma lowerBoundScale_factor (z : ℝ) (hz : 1 ≤ z) (k : ℕ) (hk : 1 ≤ k)
    (ε : ℝ) (hε : 0 < ε) :
    lowerBoundScale z k ε =
      (k : ℝ) * ((1 / ε) ^ 2) *
        (min ((k : ℝ) ^ (2 / (z + 2))) ((1 / ε) ^ 2)) ^ (z / 2) := by
  have hkR : (0 : ℝ) < k := by positivity
  have hz2 : z + 2 ≠ 0 := by linarith
  have hβ : 0 ≤ z / 2 := by linarith
  have h1 : (k : ℝ) ^ ((2 * z + 2) / (z + 2)) =
      (k : ℝ) * (((k : ℝ) ^ (2 / (z + 2))) ^ (z / 2)) := by
    calc
      _ = (k : ℝ) ^ (1 + (2 / (z + 2)) * (z / 2)) := by congr 1; field_simp; ring
      _ = (k : ℝ) ^ (1 : ℝ) * (k : ℝ) ^ ((2 / (z + 2)) * (z / 2)) := Real.rpow_add hkR _ _
      _ = _ := by rw [Real.rpow_one, Real.rpow_mul hkR.le]
  have h2 : (k : ℝ) * ε ^ (-z - 2) =
      (k : ℝ) * ((1 / ε) ^ 2) * (((1 / ε) ^ 2) ^ (z / 2)) := by
    rw [← inverse_square_rpow ε hε]
    simp only [Real.rpow_eq_pow]
    rw [← Real.rpow_mul hε.le]
    calc
      _ = (k : ℝ) * ε ^ ((-2 : ℝ) + (-2 : ℝ) * (z / 2)) := by congr 1; congr 1; ring
      _ = (k : ℝ) * (ε ^ (-2 : ℝ) * ε ^ ((-2 : ℝ) * (z / 2))) := by rw [Real.rpow_add hε]
      _ = _ := by ring
  have hinverse : ε ^ (-2 : ℝ) = (1 / ε) ^ 2 := by simpa only [Real.rpow_eq_pow] using inverse_square_rpow ε hε
  unfold lowerBoundScale
  simp only [Real.rpow_eq_pow]
  rw [h1, h2, hinverse]
  by_cases hh : (k : ℝ) ^ (2 / (z + 2)) ≤ (1 / ε) ^ 2
  · rw [min_eq_left hh]
    have hp := Real.rpow_le_rpow (by positivity) hh hβ
    have hm := mul_le_mul_of_nonneg_left hp (show 0 ≤ (k : ℝ) * (1 / ε) ^ 2 by positivity)
    rw [show (k : ℝ) * ((k : ℝ) ^ (2 / (z + 2))) ^ (z / 2) * (1 / ε) ^ 2 =
      (k : ℝ) * (1 / ε) ^ 2 * ((k : ℝ) ^ (2 / (z + 2))) ^ (z / 2) by ring, min_eq_left hm]
  · rw [min_eq_right (le_of_not_ge hh)]
    have hp := Real.rpow_le_rpow (sq_nonneg (1 / ε)) (le_of_not_ge hh) hβ
    have hm := mul_le_mul_of_nonneg_left hp (show 0 ≤ (k : ℝ) * (1 / ε) ^ 2 by positivity)
    rw [show (k : ℝ) * ((k : ℝ) ^ (2 / (z + 2))) ^ (z / 2) * (1 / ε) ^ 2 =
      (k : ℝ) * (1 / ε) ^ 2 * ((k : ℝ) ^ (2 / (z + 2))) ^ (z / 2) by ring, min_eq_right hm]

lemma code_length_control :
    ∃ D : ℝ, 0 < D ∧ ∀ ε : ℝ, 0 < ε → ε < 1 →
      ∃ L : ℕ, 1 ≤ L ∧ (L : ℝ) ≤ D * Real.log (2 + 1 / ε) ∧
        ∀ q : ℕ, (q : ℝ) ≤ Real.rpow ε (-2) → q + Nat.choose q 3 < 2 ^ L := by
  let D : ℝ := 8 / Real.log 2 + 1 / Real.log 3
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  refine ⟨D, by dsimp [D]; positivity, ?_⟩
  intro ε hε hε1
  let t : ℝ := 2 + 1 / ε
  let R : ℝ := (1 / ε) ^ 2
  have hinv : 1 < 1 / ε := (lt_div_iff₀ hε).mpr (by simpa using hε1)
  have ht3 : 3 < t := by dsimp [t]; linarith
  have htp : 0 < t := by linarith
  have hlogt : 0 < Real.log t := Real.log_pos (by linarith)
  have hlog3t : Real.log 3 ≤ Real.log t := Real.log_le_log (by norm_num) ht3.le
  let raw : ℝ := 8 * Real.log t / Real.log 2
  let L : ℕ := ⌈raw⌉₊
  have hraw : 0 < raw := by dsimp [raw]; positivity
  have hL : 1 ≤ L := Nat.ceil_pos.mpr hraw
  have hLraw : (L : ℝ) ≤ raw + 1 := (Nat.ceil_lt_add_one hraw.le).le
  have hLlog : (L : ℝ) ≤ D * Real.log t := by
    have h1 : 1 ≤ Real.log t / Real.log 3 := (le_div_iff₀ hlog3).mpr (by simpa using hlog3t)
    calc
      _ ≤ raw + 1 := hLraw
      _ ≤ raw + Real.log t / Real.log 3 := by linarith
      _ = _ := by dsimp [D, raw]; ring
  refine ⟨L, hL, hLlog, ?_⟩
  intro q hq
  rw [inverse_square_rpow ε hε] at hq
  have hchoose : (Nat.choose q 3 : ℝ) ≤ (q : ℝ) ^ 3 := by exact_mod_cast Nat.choose_le_pow q 3
  have hR1 : 1 ≤ R := by dsimp [R]; nlinarith
  have hR0 : 0 ≤ R := by dsimp [R]; positivity
  have hRt : R ≤ t ^ 2 := by dsimp [R, t]; nlinarith
  have hR3 : R ≤ R ^ 3 := by nlinarith [mul_nonneg (show 0 ≤ R ^ 2 - 1 by nlinarith) hR0]
  have hq3 : (q : ℝ) ^ 3 ≤ R ^ 3 := pow_le_pow_left₀ (by positivity) hq 3
  have ht6 : R ^ 3 ≤ t ^ 6 := by
    have hh := pow_le_pow_left₀ hR0 hRt 3
    calc
      _ ≤ (t ^ 2) ^ 3 := hh
      _ = _ := by ring
  have ht8 : 2 * t ^ 6 < t ^ 8 := by
    have hh := mul_lt_mul_of_pos_left (show (2 : ℝ) < t ^ 2 by nlinarith) (pow_pos htp 6)
    calc
      _ < t ^ 2 * t ^ 6 := by nlinarith only [hh]
      _ = _ := by ring
  have hexp : (2 : ℝ) ^ raw = t ^ 8 := by
    rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2), ← Real.rpow_natCast t 8, Real.rpow_def_of_pos htp]
    congr 1
    dsimp [raw]
    field_simp
  have hpowL : t ^ 8 ≤ (2 : ℝ) ^ L := by
    have hh := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) (Nat.le_ceil raw)
    rw [hexp, Real.rpow_natCast] at hh
    exact hh
  have hqpow : (q : ℝ) + (Nat.choose q 3 : ℝ) < (2 : ℝ) ^ L := by
    calc
      _ ≤ R + R ^ 3 := by linarith
      _ ≤ 2 * R ^ 3 := by linarith
      _ ≤ 2 * t ^ 6 := by linarith
      _ < t ^ 8 := ht8
      _ ≤ _ := hpowL
  exact_mod_cast hqpow

set_option maxHeartbeats 100000 in
lemma integer_parameters_or_boundary (z : ℝ) (hz : 1 ≤ z) (A : ℝ) (hA : 0 < A)
    (C E : ℝ) (hC8 : 8 ≤ C) (hCA : 4 ≤ C * A ^ 2)
    (hE : 8 * C ^ 2 * (2 * C) ^ (z / 2) ≤ E)
    (hEC : C ^ (z / 2) ≤ E) (hEC' : C ≤ E)
    (b : ℕ) (hb : 2 * z + 5 ≤ (b : ℝ))
    (k : ℕ) (hk : 1 ≤ k) (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1)
    (L : ℕ) (hL : 1 ≤ L) :
    (min ((k : ℝ) ^ (2 / (z + 2))) ((1 / ε) ^ 2)) ^ (z / 2) ≤ E * (L : ℝ) ^ b ∨
    ∃ n m q : ℕ, 1 ≤ n ∧ 1 ≤ m ∧ 1 ≤ q ∧
      (q : ℝ) ≤ Real.rpow ε (-2) ∧
      n * (copyCountZ z n - 1) + m * (L + 1) ≤ k ∧
      ε * Real.sqrt ((n : ℝ) * (q : ℝ)) * (L : ℝ) ^ 2 < A ∧
      (k : ℝ) * ((1 / ε) ^ 2) *
        (min ((k : ℝ) ^ (2 / (z + 2))) ((1 / ε) ^ 2)) ^ (z / 2) ≤
        E * (L : ℝ) ^ b * (((copyCountZ z n : ℝ) * (n : ℝ) * (m : ℝ) * (q : ℝ)) / 2) := by
  classical
  let K : ℝ := k
  let R : ℝ := (1 / ε) ^ 2
  let β : ℝ := z / 2
  let α : ℝ := 2 / (z + 2)
  let U : ℝ := min (K ^ α) R
  let l : ℝ := L
  have hK1 : 1 ≤ K := by dsimp [K]; exact_mod_cast hk
  have hKp : 0 < K := by linarith
  have hR1 : 1 ≤ R := by
    have hi : 1 < 1 / ε := (lt_div_iff₀ hε).mpr (by simpa using hε1)
    dsimp [R]
    nlinarith
  have hRp : 0 < R := by linarith
  have hl1 : 1 ≤ l := by dsimp [l]; exact_mod_cast hL
  have hlp : 0 < l := by linarith
  have hCp : 0 < C := by linarith
  have hEp : 0 < E := by linarith
  have hβ : 0 < β := by dsimp [β]; linarith
  have hα : 0 < α := by dsimp [α]; positivity
  have hαβ : α * (β + 1) = 1 := by dsimp [α, β]; field_simp
  have hβ1 : 1 ≤ β + 1 := by linarith
  have hU1 : 1 ≤ U := le_min (Real.one_le_rpow hK1 hα.le) hR1
  have hUp : 0 < U := by linarith
  have hUK : U ≤ K ^ α := min_le_left _ _
  have hUR : U ≤ R := min_le_right _ _
  have hl4 : 1 ≤ l ^ 4 := one_le_pow₀ hl1
  have hl4p : 0 < l ^ 4 := by positivity
  have hb1 : (1 : ℝ) ≤ b := by linarith
  have hl4β : l ^ (4 * β) ≤ l ^ b := by
    have hh := Real.rpow_le_rpow_of_exponent_le hl1 (show 4 * β ≤ (b : ℝ) by dsimp [β]; linarith)
    simpa only [Real.rpow_natCast] using hh
  have hllb : l ≤ l ^ b := by
    have hh := Real.rpow_le_rpow_of_exponent_le hl1 hb1
    simpa only [Real.rpow_one, Real.rpow_natCast] using hh
  have hlcombined : l ^ (4 * β + 5) ≤ l ^ b := by
    have hh := Real.rpow_le_rpow_of_exponent_le hl1 (show 4 * β + 5 ≤ (b : ℝ) by dsimp [β]; linarith)
    simpa only [Real.rpow_natCast] using hh
  by_cases hnr : 1 ≤ U / (C * l ^ 4)
  swap
  · left
    have hU : U ≤ C * l ^ 4 := by
      have hh := (div_lt_iff₀ (by positivity : 0 < C * l ^ 4)).mp (lt_of_not_ge hnr)
      linarith
    have hup := Real.rpow_le_rpow hUp.le hU hβ.le
    rw [Real.mul_rpow hCp.le (by positivity : 0 ≤ l ^ 4)] at hup
    have hpow : (l ^ (4 : ℕ)) ^ β = l ^ (4 * β) := by simpa only [Nat.cast_ofNat] using (Real.rpow_natCast_mul hlp.le 4 β).symm
    rw [hpow] at hup
    have hh := mul_le_mul hEC hl4β (by positivity : 0 ≤ l ^ (4 * β)) hEp.le
    exact hup.trans hh
  by_cases hmr : 1 ≤ K / (C * l)
  swap
  · left
    have hK : K ≤ C * l := by
      have hh := (div_lt_iff₀ (by positivity : 0 < C * l)).mp (lt_of_not_ge hmr)
      linarith
    have hup := Real.rpow_le_rpow hUp.le hUK hβ.le
    rw [← Real.rpow_mul hKp.le] at hup
    have hαβle : α * β ≤ 1 := by nlinarith only [hαβ, hα]
    have hh := Real.rpow_le_self_of_one_le hK1 hαβle
    have hcl := mul_le_mul hEC' hllb hlp.le hEp.le
    exact hup.trans (hh.trans (hK.trans hcl))
  right
  let n : ℕ := ⌊U / (C * l ^ 4)⌋₊
  let m : ℕ := ⌊K / (C * l)⌋₊
  obtain ⟨hn, hnup, hnlo⟩ := floor_bounds_of_one_le _ hnr
  obtain ⟨hm, hmup, hmlo⟩ := floor_bounds_of_one_le _ hmr
  change 1 ≤ n at hn
  change 1 ≤ m at hm
  have hN1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hM1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hNp : (0 : ℝ) < n := by positivity
  have hMp : (0 : ℝ) < m := by positivity
  have hNupper : (n : ℝ) * (C * l ^ 4) ≤ U := (le_div_iff₀ (by positivity)).mp hnup
  have hUlower : U ≤ 2 * C * l ^ 4 * (n : ℝ) := by
    have hh := (div_le_iff₀ (by positivity : 0 < C * l ^ 4)).mp (show U / 2 / (C * l ^ 4) ≤ (n : ℝ) by convert hnlo using 1 <;> ring)
    nlinarith only [hh]
  have hMupper : (m : ℝ) * (C * l) ≤ K := (le_div_iff₀ (by positivity)).mp hmup
  have hKlower : K ≤ 2 * C * l * (m : ℝ) := by
    have hh := (div_le_iff₀ (by positivity : 0 < C * l)).mp (show K / 2 / (C * l) ≤ (m : ℝ) by convert hmlo using 1 <;> ring)
    nlinarith only [hh]
  let q : ℕ := ⌊R / (C * (n : ℝ) * l ^ 4)⌋₊
  have hqraw : 1 ≤ R / (C * (n : ℝ) * l ^ 4) := by
    apply (le_div_iff₀ (by positivity : 0 < C * (n : ℝ) * l ^ 4)).mpr
    nlinarith only [hNupper, hUR]
  obtain ⟨hq, hqup, hqlo⟩ := floor_bounds_of_one_le _ hqraw
  change 1 ≤ q at hq
  have hQ1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hQp : (0 : ℝ) < q := by positivity
  have hQupper : (q : ℝ) * (C * (n : ℝ) * l ^ 4) ≤ R := (le_div_iff₀ (by positivity)).mp hqup
  have hRlower : R ≤ 2 * C * (n : ℝ) * l ^ 4 * (q : ℝ) := by
    have hh := (div_le_iff₀ (by positivity : 0 < C * (n : ℝ) * l ^ 4)).mp
      (show R / 2 / (C * (n : ℝ) * l ^ 4) ≤ (q : ℝ) by convert hqlo using 1 <;> ring)
    nlinarith only [hh]
  have hden1 : 1 ≤ C * (n : ℝ) * l ^ 4 := by
    have hh : 1 ≤ C * (n : ℝ) := one_le_mul_of_one_le_of_one_le (by linarith) hN1
    exact one_le_mul_of_one_le_of_one_le hh hl4
  have hqR : (q : ℝ) ≤ R := by nlinarith only [hQupper, mul_le_mul_of_nonneg_left hden1 hQp.le]
  have herror : ε * Real.sqrt ((n : ℝ) * (q : ℝ)) * (L : ℝ) ^ 2 < A := by
    let err := ε * Real.sqrt ((n : ℝ) * (q : ℝ)) * (L : ℝ) ^ 2
    have herr0 : 0 ≤ err := by dsimp [err]; positivity
    have heq : err ^ 2 = ε ^ 2 * (n : ℝ) * (q : ℝ) * l ^ 4 := by
      dsimp [err, l]
      rw [mul_pow, mul_pow, Real.sq_sqrt (by positivity : 0 ≤ (n : ℝ) * (q : ℝ))]
      ring
    have hRidentity : ε ^ 2 * R = 1 := by dsimp [R]; field_simp
    have hh := mul_le_mul_of_nonneg_left hQupper (sq_nonneg ε)
    have hCerr : C * err ^ 2 ≤ 1 := by rw [heq]; nlinarith only [hh, hRidentity]
    have hsqbound : err ^ 2 ≤ 1 / C := (le_div_iff₀ hCp).mpr (by nlinarith only [hCerr])
    have hless : 1 / C < A ^ 2 := (div_lt_iff₀ hCp).mpr (by nlinarith only [hCA])
    change err < A
    nlinarith only [herr0, hsqbound, hless, hA]
  have h8n : 8 * (n : ℝ) ≤ K ^ α := by
    have hcN := mul_le_mul_of_nonneg_right hC8 hNp.le
    have hlN := mul_le_mul_of_nonneg_left hl4 (show 0 ≤ C * (n : ℝ) by positivity)
    nlinarith only [hcN, hlN, hNupper, hUK]
  have hnPow : 8 * (n : ℝ) ^ (β + 1) ≤ K := by
    have hh := Real.rpow_le_rpow (by positivity : 0 ≤ 8 * (n : ℝ)) h8n (by positivity : 0 ≤ β + 1)
    rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 8) hNp.le, ← Real.rpow_mul hKp.le, hαβ, Real.rpow_one] at hh
    have h8 := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 8) hβ1
    rw [Real.rpow_one] at h8
    have hp := mul_le_mul_of_nonneg_right h8 (show 0 ≤ (n : ℝ) ^ (β + 1) by positivity)
    linarith only [hh, hp]
  have h8m : 8 * (m : ℝ) * l ≤ K := by
    have hh := mul_le_mul_of_nonneg_right hC8 (show 0 ≤ (m : ℝ) * l by positivity)
    nlinarith only [hh, hMupper]
  have hcopylo := (copyCountZ_bounds z hz n hn).1
  have hcopyhi := (copyCountZ_bounds z hz n hn).2
  have hNβ : (n : ℝ) * (n : ℝ) ^ β = (n : ℝ) ^ (β + 1) := by
    rw [Real.rpow_add hNp, Real.rpow_one]
    ring
  have hbudget : n * (copyCountZ z n - 1) + m * (L + 1) ≤ k := by
    have hsub : ((copyCountZ z n - 1 : ℕ) : ℝ) ≤ (copyCountZ z n : ℝ) := by exact_mod_cast Nat.sub_le (copyCountZ z n) 1
    have hsubN := mul_le_mul_of_nonneg_left hsub hNp.le
    have hNhi := mul_le_mul_of_nonneg_left hcopyhi hNp.le
    have hM := mul_le_mul_of_nonneg_left hl1 hMp.le
    have hh : (n : ℝ) * ((copyCountZ z n - 1 : ℕ) : ℝ) + (m : ℝ) * ((L : ℝ) + 1) ≤ (k : ℝ) := by
      change (n : ℝ) * _ + (m : ℝ) * (l + 1) ≤ K
      have hNhi' : (n : ℝ) * (copyCountZ z n : ℝ) ≤ 2 * (n : ℝ) ^ (β + 1) := by
        rw [← hNβ]
        nlinarith only [hNhi]
      nlinarith only [hsubN, hNhi', hnPow, h8m, hM]
    exact_mod_cast hh
  have hupower : U ^ β ≤ (2 * C) ^ β * l ^ (4 * β) * (n : ℝ) ^ β := by
    have hh := Real.rpow_le_rpow hUp.le hUlower hβ.le
    have heq : 2 * C * l ^ 4 * (n : ℝ) = (2 * C) * (l ^ 4) * (n : ℝ) := by ring
    rw [heq, Real.mul_rpow (by positivity : 0 ≤ (2 * C) * l ^ 4) hNp.le,
      Real.mul_rpow (by positivity : 0 ≤ 2 * C) (by positivity : 0 ≤ l ^ 4),
      ← Real.rpow_natCast_mul hlp.le] at hh
    exact hh
  have hKR : K * R ≤ 4 * C ^ 2 * (n : ℝ) * (m : ℝ) * (q : ℝ) * l ^ 5 := by
    have hh := mul_le_mul hKlower hRlower hRp.le (show 0 ≤ 2 * C * l * (m : ℝ) by positivity)
    calc
      _ ≤ (2 * C * l * (m : ℝ)) * (2 * C * (n : ℝ) * l ^ 4 * (q : ℝ)) := hh
      _ = _ := by ring
  have hproduct := mul_le_mul hKR hupower (show 0 ≤ U ^ β by positivity)
    (show 0 ≤ 4 * C ^ 2 * (n : ℝ) * (m : ℝ) * (q : ℝ) * l ^ 5 by positivity)
  have hsize : K * R * U ^ β ≤ E * l ^ b * (((copyCountZ z n : ℝ) * (n : ℝ) * (m : ℝ) * (q : ℝ)) / 2) := by
    calc
      _ ≤ (8 * C ^ 2 * (2 * C) ^ β) * l ^ (4 * β + 5) *
          (((n : ℝ) ^ β * (n : ℝ) * (m : ℝ) * (q : ℝ)) / 2) := by
        rw [Real.rpow_add hlp]
        have h5 : l ^ (5 : ℝ) = l ^ (5 : ℕ) := by simpa only [Nat.cast_ofNat] using Real.rpow_natCast l 5
        rw [h5]
        exact hproduct.trans_eq (by ring)
      _ ≤ (8 * C ^ 2 * (2 * C) ^ β) * l ^ b *
          (((copyCountZ z n : ℝ) * (n : ℝ) * (m : ℝ) * (q : ℝ)) / 2) := by
        gcongr
      _ ≤ _ := by gcongr
  exact ⟨n, m, q, hn, hm, hq, by simpa only [inverse_square_rpow ε hε] using hqR, hbudget, herror, hsize⟩

 theorem numeric_selection_proof (z : ℝ) (hz : 1 ≤ z) (A : ℝ) (hA : 0 < A) :
    ∃ c : ℝ, 0 < c ∧ ∃ b : ℕ,
      ∀ k : ℕ, 1 ≤ k → ∀ ε : ℝ, 0 < ε → ε < 1 →
        c * lowerBoundScale z k ε / (Real.log (2 + 1 / ε)) ^ b ≤
          (k : ℝ) * Real.rpow ε (-2) ∨
        ∃ n m L q : ℕ, 1 ≤ n ∧ 1 ≤ m ∧ 1 ≤ L ∧ 1 ≤ q ∧
          q + Nat.choose q 3 < 2 ^ L ∧
          n * (copyCountZ z n - 1) + m * (L + 1) ≤ k ∧
          ε * Real.sqrt ((n : ℝ) * (q : ℝ)) * (L : ℝ) ^ 2 < A ∧
          c * lowerBoundScale z k ε / (Real.log (2 + 1 / ε)) ^ b ≤
            ((copyCountZ z n : ℝ) * (n : ℝ) * (m : ℝ) * (q : ℝ)) / 2 := by
  let C : ℝ := 8 + 4 / A ^ 2
  let β : ℝ := z / 2
  let E : ℝ := 8 * C ^ 2 * (2 * C) ^ β + C ^ β + C + 1
  let b : ℕ := ⌈2 * z + 5⌉₊
  have hC8 : 8 ≤ C := by
    dsimp [C]
    have hp : 0 ≤ 4 / A ^ 2 := by positivity
    linarith only [hp]
  have hCp : 0 < C := by linarith
  have hCA : 4 ≤ C * A ^ 2 := by
    dsimp [C]
    rw [add_mul, div_mul_cancel₀ _ (ne_of_gt (sq_pos_of_pos hA))]
    nlinarith only [sq_nonneg A]
  have hEp : 0 < E := by dsimp [E]; positivity
  have hE : 8 * C ^ 2 * (2 * C) ^ (z / 2) ≤ E := by
    dsimp [E, β]
    have hp : 0 ≤ C ^ (z / 2) := by positivity
    linarith only [hp, hCp]
  have hEC : C ^ (z / 2) ≤ E := by
    dsimp [E, β]
    have hp : 0 ≤ 8 * C ^ 2 * (2 * C) ^ (z / 2) := by positivity
    linarith only [hp, hCp]
  have hEC' : C ≤ E := by
    dsimp [E]
    have hp : 0 ≤ C ^ β := by positivity
    have hp' : 0 ≤ 8 * C ^ 2 * (2 * C) ^ β := by positivity
    linarith only [hp, hp']
  have hb : 2 * z + 5 ≤ (b : ℝ) := Nat.le_ceil _
  obtain ⟨D, hD, hlength⟩ := code_length_control
  let c : ℝ := 1 / (E * D ^ b)
  have hc : 0 < c := by dsimp [c]; positivity
  refine ⟨c, hc, b, ?_⟩
  intro k hk ε hε hε1
  obtain ⟨L, hL, hLlog, hcode⟩ := hlength ε hε hε1
  have hlog : 0 < Real.log (2 + 1 / ε) := Real.log_pos (by have := one_div_pos.mpr hε; linarith)
  have hLpower : (L : ℝ) ^ b ≤ D ^ b * (Real.log (2 + 1 / ε)) ^ b := by
    have hh := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ L) hLlog b
    rwa [mul_pow] at hh
  have hden : 0 < E * D ^ b * (Real.log (2 + 1 / ε)) ^ b := by positivity
  have hscale : c * lowerBoundScale z k ε / (Real.log (2 + 1 / ε)) ^ b =
      lowerBoundScale z k ε / (E * D ^ b * (Real.log (2 + 1 / ε)) ^ b) := by dsimp [c]; ring
  have hED := mul_le_mul_of_nonneg_left hLpower hEp.le
  rcases integer_parameters_or_boundary z hz A hA C E hC8 hCA hE hEC hEC' b hb k hk ε hε hε1 L hL with hboundary|hparameters
  · left
    rw [hscale]
    apply (div_le_iff₀ hden).mpr
    rw [lowerBoundScale_factor z hz k hk ε hε, inverse_square_rpow ε hε]
    have hcoeff := hboundary.trans hED
    have hh := mul_le_mul_of_nonneg_left hcoeff (show 0 ≤ (k : ℝ) * (1 / ε) ^ 2 by positivity)
    nlinarith
  · obtain ⟨n, m, q, hn, hm, hq, hqR, hbudget, herror, hsize⟩ := hparameters
    right
    refine ⟨n, m, L, q, hn, hm, hL, hq, hcode q hqR, hbudget, herror, ?_⟩
    rw [hscale]
    apply (div_le_iff₀ hden).mpr
    rw [lowerBoundScale_factor z hz k hk ε hε]
    have hh := mul_le_mul_of_nonneg_right hED
      (show 0 ≤ ((copyCountZ z n : ℝ) * (n : ℝ) * (m : ℝ) * (q : ℝ)) / 2 by positivity)
    nlinarith [hsize]

end TightCoreset2027.Euclidean
open TightCoreset2027.Euclidean

 theorem solution (z : ℝ) (hz : 1 ≤ z) (A : ℝ) (hA : 0 < A) :
    ∃ c : ℝ, 0 < c ∧ ∃ b : ℕ,
      ∀ k : ℕ, 1 ≤ k → ∀ ε : ℝ, 0 < ε → ε < 1 →
        c * lowerBoundScale z k ε / (Real.log (2 + 1 / ε)) ^ b ≤
          (k : ℝ) * Real.rpow ε (-2) ∨
        ∃ n m L q : ℕ, 1 ≤ n ∧ 1 ≤ m ∧ 1 ≤ L ∧ 1 ≤ q ∧
          q + Nat.choose q 3 < 2 ^ L ∧
          n * (copyCountZ z n - 1) + m * (L + 1) ≤ k ∧
          ε * Real.sqrt ((n : ℝ) * (q : ℝ)) * (L : ℝ) ^ 2 < A ∧
          c * lowerBoundScale z k ε / (Real.log (2 + 1 / ε)) ^ b ≤
            ((copyCountZ z n : ℝ) * (n : ℝ) * (m : ℝ) * (q : ℝ)) / 2 := by
  exact TightCoreset2027.Euclidean.numeric_selection_proof z hz A hA
