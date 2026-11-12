-- Prove2me | solution 1 for Tao2022Collatz.renewal_large_black_triangle_case
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-12T01:27:33.26465+00:00
-- url     : https://prove2.me/submissions/996595d3-8398-4319-8e47-dd8c99f6dc29

import Mathlib
set_option autoImplicit false
namespace Tao31
noncomputable def Box (n K : ℕ) : Finset (Fin n → ℕ) := Fintype.piFinset (fun _ => Finset.Icc 1 K)


lemma box_gen (n K : ℕ) (z : ℝ) :
    ∑ w ∈ Box n K, ((1 : ℝ) / 2) ^ (∑ i, w i) * z ^ (∑ i, w i) =
      (∑ a ∈ Finset.Icc 1 K, (z / 2) ^ a) ^ n := by
  calc ∑ w ∈ Box n K, ((1 : ℝ) / 2) ^ (∑ i, w i) * z ^ (∑ i, w i)
      = ∑ w ∈ Box n K, ∏ i, (z / 2) ^ (w i) := by
        apply Finset.sum_congr rfl
        intro w _
        rw [Finset.prod_pow_eq_pow_sum, div_eq_mul_one_div z 2, mul_pow, mul_comm]
    _ = ∏ _i : Fin n, ∑ a ∈ Finset.Icc 1 K, (z / 2) ^ a := (Finset.prod_univ_sum _ _).symm
    _ = (∑ a ∈ Finset.Icc 1 K, (z / 2) ^ a) ^ n := Fin.prod_const n _

lemma geom_Icc_le (x : ℝ) (h0 : 0 ≤ x) (h1 : x < 1) (K : ℕ) :
    ∑ a ∈ Finset.Icc 1 K, x ^ a ≤ x / (1 - x) := by
  calc ∑ a ∈ Finset.Icc 1 K, x ^ a ≤ ∑ a ∈ Finset.Ico 1 (K + 1), x ^ a := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro a ha
          simp only [Finset.mem_Icc, Finset.mem_Ico] at ha ⊢
          omega
        · intro a _ _; positivity
    _ ≤ x ^ 1 / (1 - x) := geom_sum_Ico_le_of_lt_one h0 h1
    _ = x / (1 - x) := by rw [pow_one]

lemma box_mass_le (j K : ℕ) : ∑ v ∈ Box j K, ((1 : ℝ) / 2) ^ (∑ i, v i) ≤ 1 := by
  have h := box_gen j K 1
  simp only [one_pow, mul_one] at h
  rw [h]
  have hg := geom_Icc_le ((1 : ℝ) / 2) (by norm_num) (by norm_num) K
  have hg' : ∑ a ∈ Finset.Icc 1 K, ((1 : ℝ) / 2) ^ a ≤ 1 := by
    have : (1 : ℝ) / 2 / (1 - 1 / 2) = 1 := by norm_num
    linarith
  have h0 : 0 ≤ ∑ a ∈ Finset.Icc 1 K, ((1 : ℝ) / 2) ^ a := by positivity
  exact pow_le_one₀ h0 hg'


noncomputable def thZ (n : ℕ) (ξ : ℤ) (J L : ℕ) : ZMod (3 ^ n) :=
  (ξ : ZMod (3 ^ n)) * 9 ^ (J - 1) * ((2 : ZMod (3 ^ n))⁻¹) ^ (L - 1)

def White (n : ℕ) (ξ : ℤ) (ε : ℝ) (J L : ℕ) : Prop :=
  ε * 3 ^ n < ((thZ n ξ J L).val : ℝ) ∧ ((thZ n ξ J L).val : ℝ) < (1 - ε) * 3 ^ n


open Classical in
noncomputable def cf (n : ℕ) (ξ : ℤ) (ε : ℝ) (J L b : ℕ) : ℝ :=
  if b = 3 ∧ White n ξ ε J L then Real.exp (-ε ^ 3) else 1

noncomputable def Vt (n K : ℕ) (ξ : ℤ) (ε : ℝ) : ℕ → ℕ → ℕ → ℝ
  | 0, _, _ => 1
  | r + 1, j, l => ∑ u ∈ Box 2 K, ((1 : ℝ) / 2) ^ (∑ i, u i) *
      cf n ξ ε (j + 1) (l + ∑ i, u i) (∑ i, u i) * Vt n K ξ ε r (j + 1) (l + ∑ i, u i)

lemma cf_nonneg (n : ℕ) (ξ : ℤ) (ε : ℝ) (J L b : ℕ) : 0 ≤ cf n ξ ε J L b := by
  unfold cf; split_ifs <;> positivity

lemma Vt_nonneg (n K : ℕ) (ξ : ℤ) (ε : ℝ) : ∀ r j l, 0 ≤ Vt n K ξ ε r j l
  | 0, _, _ => by simp [Vt]
  | r + 1, j, l => by
    simp only [Vt]
    exact Finset.sum_nonneg (fun u _ => mul_nonneg (mul_nonneg (by positivity) (cf_nonneg _ _ _ _ _ _))
      (Vt_nonneg n K ξ ε r _ _))

lemma box2_three (K : ℕ) (hK : 2 ≤ K) :
    (Box 2 K).filter (fun u => ∑ i, u i = 3) = {![1, 2], ![2, 1]} := by
  ext u
  simp only [Finset.mem_filter, Box, Fintype.mem_piFinset, Finset.mem_Icc, Fin.sum_univ_two,
    Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨hb, hs⟩
    have h0 := hb 0
    have h1 := hb 1
    rcases (by omega : (u 0 = 1 ∧ u 1 = 2) ∨ (u 0 = 2 ∧ u 1 = 1)) with h | h
    · left; funext i; fin_cases i <;> simp [h.1, h.2]
    · right; funext i; fin_cases i <;> simp [h.1, h.2]
  · rintro (rfl | rfl)
    · refine ⟨fun i => ?_, by simp⟩
      fin_cases i <;> simp <;> omega
    · refine ⟨fun i => ?_, by simp⟩
      fin_cases i <;> simp <;> omega

lemma cf_le_one (n : ℕ) (ξ : ℤ) (ε : ℝ) (hε : 0 ≤ ε) (J L b : ℕ) : cf n ξ ε J L b ≤ 1 := by
  unfold cf
  split_ifs
  · exact Real.exp_le_one_iff.2 (by have := pow_nonneg hε 3; linarith)
  · exact le_rfl

/-! ### 8c.0 Comparison principle: `Vt ≤ H` for any super-solution of the stopped recursion -/

lemma step_white (n K : ℕ) (ξ : ℤ) (ε : ℝ) (hε : 0 ≤ ε) (hK : 2 ≤ K) (j l : ℕ)
    (hW : White n ξ ε (j + 1) (l + 3)) (f : ℕ → ℝ) (F : ℝ) (hf0 : ∀ b, 0 ≤ f b) (hfF : ∀ b, f b ≤ F) :
    ∑ u ∈ Box 2 K, ((1 : ℝ) / 2) ^ (∑ i, u i) * cf n ξ ε (j + 1) (l + ∑ i, u i) (∑ i, u i) * f (∑ i, u i)
      ≤ F * (1 - (1 - Real.exp (-ε ^ 3)) / 4) := by
  have hF0 : 0 ≤ F := (hf0 0).trans (hfF 0)
  have hc3 : cf n ξ ε (j + 1) (l + 3) 3 = Real.exp (-ε ^ 3) := by
    unfold cf; rw [if_pos ⟨rfl, hW⟩]
  have hcard : ((Box 2 K).filter (fun u => ∑ i, u i = 3)).card = 2 := by
    rw [box2_three K hK]
    exact Finset.card_pair (by intro h; have := congrFun h 0; simp at this)
  have h3 : ∀ u ∈ (Box 2 K).filter (fun u => ∑ i, u i = 3),
      ((1 : ℝ) / 2) ^ (∑ i, u i) * cf n ξ ε (j + 1) (l + ∑ i, u i) (∑ i, u i) * f (∑ i, u i)
        = 1 / 8 * Real.exp (-ε ^ 3) * f 3 := by
    intro u hu
    rw [(Finset.mem_filter.1 hu).2, hc3]; norm_num
  have h3w : ∀ u ∈ (Box 2 K).filter (fun u => ∑ i, u i = 3), ((1 : ℝ) / 2) ^ (∑ i, u i) = 1 / 8 := by
    intro u hu; rw [(Finset.mem_filter.1 hu).2]; norm_num
  have hmass := box_mass_le 2 K
  rw [← Finset.sum_filter_add_sum_filter_not (Box 2 K) (fun u => ∑ i, u i = 3),
    Finset.sum_congr rfl h3w, Finset.sum_const, hcard] at hmass
  rw [← Finset.sum_filter_add_sum_filter_not (Box 2 K) (fun u => ∑ i, u i = 3),
    Finset.sum_congr rfl h3, Finset.sum_const, hcard]
  have hrest : ∑ u ∈ (Box 2 K).filter (fun u => ¬ ∑ i, u i = 3), ((1 : ℝ) / 2) ^ (∑ i, u i) *
        cf n ξ ε (j + 1) (l + ∑ i, u i) (∑ i, u i) * f (∑ i, u i)
      ≤ (∑ u ∈ (Box 2 K).filter (fun u => ¬ ∑ i, u i = 3), ((1 : ℝ) / 2) ^ (∑ i, u i)) * F := by
    rw [Finset.sum_mul]
    apply Finset.sum_le_sum
    intro u _
    have hcf1 := cf_le_one n ξ ε hε (j + 1) (l + ∑ i, u i) (∑ i, u i)
    have hcf0 := cf_nonneg n ξ ε (j + 1) (l + ∑ i, u i) (∑ i, u i)
    have hp : (0 : ℝ) ≤ ((1 : ℝ) / 2) ^ (∑ i, u i) := by positivity
    have hcf : cf n ξ ε (j + 1) (l + ∑ i, u i) (∑ i, u i) * f (∑ i, u i) ≤ F :=
      calc _ ≤ 1 * f (∑ i, u i) := mul_le_mul_of_nonneg_right hcf1 (hf0 _)
        _ ≤ F := by linarith [hfF (∑ i, u i)]
    calc _ = ((1 : ℝ) / 2) ^ (∑ i, u i) * (cf n ξ ε (j + 1) (l + ∑ i, u i) (∑ i, u i) * f (∑ i, u i)) := by
          ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hcf hp
  set mR := ∑ u ∈ (Box 2 K).filter (fun u => ¬ ∑ i, u i = 3), ((1 : ℝ) / 2) ^ (∑ i, u i)
  rw [nsmul_eq_mul] at hmass ⊢
  push_cast at hmass ⊢
  have a1 : mR * F ≤ 3 / 4 * F := mul_le_mul_of_nonneg_right (by linarith) hF0
  have a2 : Real.exp (-ε ^ 3) * f 3 ≤ Real.exp (-ε ^ 3) * F :=
    mul_le_mul_of_nonneg_left (hfF 3) (Real.exp_pos _).le
  (first | linarith | nlinarith)

lemma two_mul_inv (n : ℕ) : (2 : ZMod (3 ^ n)) * (2 : ZMod (3 ^ n))⁻¹ = 1 := by
  have hc : Nat.Coprime 2 (3 ^ n) := Nat.Coprime.pow_right _ (by norm_num)
  have := ZMod.coe_mul_inv_eq_one (n := 3 ^ n) 2 hc
  simpa using this


/-! ### 8b (arithmetic form) -/

noncomputable def Nz (n : ℕ) (ξ : ℤ) (J L : ℕ) : ℤ := (thZ n ξ J L).valMinAbs

lemma white_iff (n : ℕ) (ξ : ℤ) (ε : ℝ) (hε : 0 < ε) (hε2 : ε < 1 / 2) (J L : ℕ) :
    White n ξ ε J L ↔ ε * 3 ^ n < |(Nz n ξ J L : ℝ)| := by
  unfold White Nz
  have hv : (thZ n ξ J L).val < 3 ^ n := ZMod.val_lt _
  have hN : (0 : ℝ) < 3 ^ n := by positivity
  have hεN : ε * 3 ^ n < 1 / 2 * 3 ^ n := by (first | linarith | nlinarith)
  rw [ZMod.valMinAbs_def_pos]
  split_ifs with h
  · have h2 : (thZ n ξ J L).val * 2 ≤ 3 ^ n := (Nat.le_div_iff_mul_le (by norm_num)).1 h
    have h2' : ((thZ n ξ J L).val : ℝ) * 2 ≤ 3 ^ n := by exact_mod_cast h2
    push_cast
    rw [abs_of_nonneg (by positivity)]
    constructor
    · rintro ⟨h1, -⟩; exact h1
    · intro h1; refine ⟨h1, ?_⟩; (first | linarith | nlinarith)
  · have h2 : 3 ^ n < (thZ n ξ J L).val * 2 := (Nat.div_lt_iff_lt_mul (by norm_num)).1 (by omega)
    have h2' : (3 ^ n : ℝ) < ((thZ n ξ J L).val : ℝ) * 2 := by exact_mod_cast h2
    have hv' : ((thZ n ξ J L).val : ℝ) < 3 ^ n := by exact_mod_cast hv
    push_cast
    rw [abs_of_neg (by linarith)]
    constructor
    · rintro ⟨-, h1⟩; linarith
    · intro h1; constructor <;> (first | linarith | nlinarith)

lemma inv_two_mul (n : ℕ) : (2 : ZMod (3 ^ n))⁻¹ * 2 = 1 := by
  rw [mul_comm]; exact two_mul_inv n

lemma thZ_shift (n : ℕ) (ξ : ℤ) (J L a c : ℕ) (hJ : 1 ≤ J) (hL : 1 ≤ L) :
    thZ n ξ (J + a) (L + c) * 2 ^ c = thZ n ξ J L * 9 ^ a := by
  unfold thZ
  have e1 : J + a - 1 = (J - 1) + a := by omega
  have e2 : L + c - 1 = (L - 1) + c := by omega
  rw [e1, e2, pow_add, pow_add]
  calc (ξ : ZMod (3 ^ n)) * (9 ^ (J - 1) * 9 ^ a) * ((2⁻¹) ^ (L - 1) * (2⁻¹) ^ c) * 2 ^ c
        = (ξ : ZMod (3 ^ n)) * 9 ^ (J - 1) * (2⁻¹) ^ (L - 1) * 9 ^ a * ((2⁻¹ * 2) ^ c) := by ring
    _ = _ := by rw [inv_two_mul, one_pow, mul_one]

lemma Nz_shift_dvd (n : ℕ) (ξ : ℤ) (J L a c : ℕ) (hJ : 1 ≤ J) (hL : 1 ≤ L) :
    (3 : ℤ) ^ n ∣ 2 ^ c * Nz n ξ (J + a) (L + c) - 9 ^ a * Nz n ξ J L := by
  have h := thZ_shift n ξ J L a c hJ hL
  have h0 : ((2 ^ c * Nz n ξ (J + a) (L + c) - 9 ^ a * Nz n ξ J L : ℤ) : ZMod (3 ^ n)) = 0 := by
    simp only [Nz]
    push_cast
    rw [mul_comm ((2 : ZMod (3 ^ n)) ^ c), h]
    ring
  have := (ZMod.intCast_zmod_eq_zero_iff_dvd _ (3 ^ n)).1 h0
  exact_mod_cast this

lemma isCoprime_two_three : IsCoprime (2 : ℤ) 3 := Int.isCoprime_iff_gcd_eq_one.mpr (by norm_num)
lemma isCoprime_two_nine : IsCoprime (2 : ℤ) 9 := Int.isCoprime_iff_gcd_eq_one.mpr (by norm_num)

lemma exit_bound (n a c β : ℕ) (X Y : ℤ) (hd : (3 : ℤ) ^ n ∣ 2 ^ c * Y - 9 ^ a * X)
    (hβ : (2 : ℤ) ^ β ∣ X) (hβ1 : ¬ (2 : ℤ) ^ (β + 1) ∣ X) (hc : β < c) :
    (2 : ℤ) ^ β * 3 ^ n ≤ 2 ^ c * |Y| + 9 ^ a * |X| := by
  set D := 2 ^ c * Y - 9 ^ a * X with hD
  have h2 : (2 : ℤ) ^ β ∣ D :=
    dvd_sub (Dvd.dvd.mul_right (pow_dvd_pow 2 hc.le) _) (Dvd.dvd.mul_left hβ _)
  have hcop : IsCoprime ((2 : ℤ) ^ β) ((3 : ℤ) ^ n) := isCoprime_two_three.pow
  have h23 : (2 : ℤ) ^ β * 3 ^ n ∣ D := hcop.mul_dvd h2 hd
  have hD0 : D ≠ 0 := by
    intro h0
    apply hβ1
    have e : (9 : ℤ) ^ a * X = 2 ^ c * Y := by rw [hD] at h0; linarith
    have h3 : (2 : ℤ) ^ (β + 1) ∣ 9 ^ a * X := e ▸ Dvd.dvd.mul_right (pow_dvd_pow 2 (by omega)) Y
    have hc2 : IsCoprime ((2 : ℤ) ^ (β + 1)) ((9 : ℤ) ^ a) := isCoprime_two_nine.pow
    first
      | exact hc2.dvd_of_dvd_mul_left h3
      | exact hc2.dvd_of_dvd_mul_right h3
      | exact hc2.dvd_of_dvd_mul_left (by rwa [mul_comm] at h3)
      | exact hc2.dvd_of_dvd_mul_right (by rwa [mul_comm] at h3)
  have hle : (2 : ℤ) ^ β * 3 ^ n ≤ |D| := Int.le_of_dvd (abs_pos.2 hD0) ((dvd_abs _ _).2 h23)
  have p1 : (0 : ℤ) < 2 ^ c := by positivity
  have p2 : (0 : ℤ) < 9 ^ a := by positivity
  have q1 := mul_le_mul_of_nonneg_left (le_abs_self Y) p1.le
  have q2 := mul_le_mul_of_nonneg_left (neg_abs_le Y) p1.le
  have q3 := mul_le_mul_of_nonneg_left (le_abs_self X) p2.le
  have q4 := mul_le_mul_of_nonneg_left (neg_abs_le X) p2.le
  have hDle : |D| ≤ 2 ^ c * |Y| + 9 ^ a * |X| := by
    rw [abs_le]; constructor <;> [skip; skip] <;> (rw [hD]; nlinarith)
  linarith

theorem white_of_exit (n : ℕ) (ξ : ℤ) (ε : ℝ) (hε : 0 < ε) (hε2 : ε < 1 / 2)
    (J L a c β : ℕ) (hJ : 1 ≤ J) (hL : 1 ≤ L)
    (hβ : (2 : ℤ) ^ β ∣ Nz n ξ J L) (hβ1 : ¬ (2 : ℤ) ^ (β + 1) ∣ Nz n ξ J L) (hc : β < c)
    (hsm : ε * 3 ^ n * 2 ^ c + 9 ^ a * |(Nz n ξ J L : ℝ)| < 2 ^ β * 3 ^ n) :
    White n ξ ε (J + a) (L + c) := by
  rw [white_iff n ξ ε hε hε2]
  have h := exit_bound n a c β _ _ (Nz_shift_dvd n ξ J L a c hJ hL) hβ hβ1 hc
  have h' : (2 : ℝ) ^ β * 3 ^ n ≤
      2 ^ c * |(Nz n ξ (J + a) (L + c) : ℝ)| + 9 ^ a * |(Nz n ξ J L : ℝ)| := by
    exact_mod_cast h
  by_contra hcon
  push_neg at hcon
  have : (2 : ℝ) ^ c * |(Nz n ξ (J + a) (L + c) : ℝ)| ≤ 2 ^ c * (ε * 3 ^ n) :=
    mul_le_mul_of_nonneg_left hcon (by positivity)
  (first | linarith | nlinarith)

lemma Nz_three_adic (n : ℕ) (ξ : ℤ) (hξ : ¬ (3 : ℤ) ∣ ξ) (J L : ℕ) (hJn : 2 * (J - 1) < n) :
    (9 : ℤ) ^ (J - 1) ∣ Nz n ξ J L ∧ Nz n ξ J L ≠ 0 := by
  have hrel : (3 : ℤ) ^ n ∣ 2 ^ (L - 1) * Nz n ξ J L - ξ * 9 ^ (J - 1) := by
    have h0 : ((2 ^ (L - 1) * Nz n ξ J L - ξ * 9 ^ (J - 1) : ℤ) : ZMod (3 ^ n)) = 0 := by
      simp only [Nz]
      push_cast
      unfold thZ
      calc (2 : ZMod (3 ^ n)) ^ (L - 1) * ((ξ : ZMod (3 ^ n)) * 9 ^ (J - 1) * (2⁻¹) ^ (L - 1))
            - (ξ : ZMod (3 ^ n)) * 9 ^ (J - 1)
          = (ξ : ZMod (3 ^ n)) * 9 ^ (J - 1) * ((2⁻¹ * 2) ^ (L - 1)) - ξ * 9 ^ (J - 1) := by ring
        _ = 0 := by rw [inv_two_mul, one_pow]; ring
    have := (ZMod.intCast_zmod_eq_zero_iff_dvd _ (3 ^ n)).1 h0
    exact_mod_cast this
  have e9 : (9 : ℤ) ^ (J - 1) = 3 ^ (2 * (J - 1)) := by rw [pow_mul]; norm_num
  have h9 : (9 : ℤ) ^ (J - 1) ∣ 3 ^ n := by rw [e9]; exact pow_dvd_pow 3 (by omega)
  have hA : (9 : ℤ) ^ (J - 1) ∣ 2 ^ (L - 1) * Nz n ξ J L := by
    have := dvd_add (h9.trans hrel) (Dvd.intro_left ξ rfl : (9 : ℤ) ^ (J - 1) ∣ ξ * 9 ^ (J - 1))
    simpa using this
  have hcop : IsCoprime ((9 : ℤ) ^ (J - 1)) ((2 : ℤ) ^ (L - 1)) := isCoprime_two_nine.symm.pow
  refine ⟨?_, ?_⟩
  · first
      | exact hcop.dvd_of_dvd_mul_left hA
      | exact hcop.dvd_of_dvd_mul_right hA
      | exact hcop.dvd_of_dvd_mul_left (by rwa [mul_comm] at hA)
      | exact hcop.dvd_of_dvd_mul_right (by rwa [mul_comm] at hA)
  · intro h0
    rw [h0, mul_zero, zero_sub, dvd_neg, e9] at hrel
    have h1 : (3 : ℤ) ^ (2 * (J - 1)) * 3 ∣ ξ * 3 ^ (2 * (J - 1)) := by
      have := (pow_dvd_pow (3 : ℤ) (show 2 * (J - 1) + 1 ≤ n by omega)).trans hrel
      rwa [pow_succ] at this
    rw [mul_comm ξ] at h1
    exact hξ ((mul_dvd_mul_iff_left (by positivity)).1 h1)

lemma budget_le (n : ℕ) (ξ : ℤ) (hξ : ¬ (3 : ℤ) ∣ ξ) (ε : ℝ) (hε : 0 < ε) (hε2 : ε < 1 / 2)
    (J L β : ℕ) (hJn : 2 * (J - 1) < n) (hB : ¬ White n ξ ε J L) (hβ : (2 : ℤ) ^ β ∣ Nz n ξ J L) :
    (2 : ℝ) ^ β * 9 ^ (J - 1) ≤ ε * 3 ^ n := by
  rw [white_iff n ξ ε hε hε2, not_lt] at hB
  obtain ⟨h9, h0⟩ := Nz_three_adic n ξ hξ J L hJn
  have hcop : IsCoprime ((2 : ℤ) ^ β) ((9 : ℤ) ^ (J - 1)) := isCoprime_two_nine.pow
  have hd : (2 : ℤ) ^ β * 9 ^ (J - 1) ∣ Nz n ξ J L := hcop.mul_dvd hβ h9
  have hle : (2 : ℤ) ^ β * 9 ^ (J - 1) ≤ |Nz n ξ J L| :=
    Int.le_of_dvd (abs_pos.2 h0) ((dvd_abs _ _).2 hd)
  have hle' : (2 : ℝ) ^ β * 9 ^ (J - 1) ≤ |(Nz n ξ J L : ℝ)| := by exact_mod_cast hle
  linarith


/-! ### 8d.1 Black runs end in a white probe (Tao (7.51) / Case-2 core, arithmetic form)
A black probe with exact 2-adic budget `β` keeps the run black only while the pair sums fit in the budget;
the first overshoot of at most `D` columns is white (`white_of_exit`). Overshoot `> D` has relative mass
`≤ (D+1) 2^-D`, so `Vt ≤ h (1 - η (1 - (D+1) 2^-D))` whenever `Vt ≤ h` on the next `β/2 + 3` rows. -/

lemma box2_sum (K : ℕ) (F : ℕ → ℝ) :
    ∑ u ∈ Box 2 K, F (∑ i, u i) = ∑ a ∈ Finset.Icc 1 K, ∑ b ∈ Finset.Icc 1 K, F (a + b) := by
  rw [← Finset.sum_product']
  refine Finset.sum_nbij' (fun u => (u 0, u 1)) (fun p => ![p.1, p.2]) ?_ ?_ ?_ ?_ ?_
  · intro u hu
    simp only [Box, Fintype.mem_piFinset] at hu
    simp only [Finset.mem_product]
    exact ⟨hu 0, hu 1⟩
  · intro p hp
    simp only [Finset.mem_product] at hp
    simp only [Box, Fintype.mem_piFinset]
    intro i
    fin_cases i
    · exact hp.1
    · exact hp.2
  · intro u _
    funext i
    fin_cases i <;> rfl
  · intro p _
    rfl
  · intro u _
    simp [Fin.sum_univ_two]

lemma geom_Icc_eq (m : ℕ) : ∑ b ∈ Finset.Icc 1 m, ((1 : ℝ) / 2) ^ b = 1 - (1 / 2) ^ m := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_Icc_succ_top (by omega), ih, pow_succ]
    ring

lemma low1 (K m : ℕ) : ∑ b ∈ Finset.Icc 1 K, (if b ≤ m then ((1 : ℝ) / 2) ^ b else 0) ≤ 1 - (1 / 2) ^ m := by
  rw [← Finset.sum_filter, ← geom_Icc_eq m]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro b
    simp only [Finset.mem_filter, Finset.mem_Icc]
    omega
  · intro b _ _
    positivity

lemma high1 (K m : ℕ) : ∑ b ∈ Finset.Icc 1 K, (if m < b then ((1 : ℝ) / 2) ^ b else 0) ≤ (1 / 2) ^ m := by
  rw [← Finset.sum_filter]
  have hsplit := Finset.sum_filter_add_sum_filter_not (Finset.Icc 1 K) (fun b => m < b)
    (fun b => ((1 : ℝ) / 2) ^ b)
  have hf : (Finset.Icc 1 K).filter (fun b => ¬ m < b) = Finset.Icc 1 (min K m) := by
    ext b
    simp only [Finset.mem_filter, Finset.mem_Icc]
    omega
  rw [hf, geom_Icc_eq, geom_Icc_eq] at hsplit
  have h2 : (0 : ℝ) ≤ (1 / 2) ^ K := by positivity
  rcases le_total m K with hmk | hmk
  · rw [min_eq_right hmk] at hsplit
    linarith
  · rw [min_eq_left hmk] at hsplit
    have : (0 : ℝ) ≤ (1 / 2) ^ m := by positivity
    linarith

lemma low2 (K β : ℕ) :
    ∑ a ∈ Finset.Icc 1 K, ∑ b ∈ Finset.Icc 1 K, (if a + b ≤ β then ((1 : ℝ) / 2) ^ (a + b) else 0)
      ≤ 1 - (β + 1) * (1 / 2) ^ β := by
  have step : ∀ a ∈ Finset.Icc 1 K,
      ∑ b ∈ Finset.Icc 1 K, (if a + b ≤ β then ((1 : ℝ) / 2) ^ (a + b) else 0)
        ≤ if a ≤ β then (1 / 2) ^ a - (1 / 2) ^ β else 0 := by
    intro a _
    have hpt : ∀ b ∈ Finset.Icc 1 K, (if a + b ≤ β then ((1 : ℝ) / 2) ^ (a + b) else 0)
        = (1 / 2) ^ a * (if b ≤ β - a then (1 / 2) ^ b else 0) := by
      intro b hb
      have hb1 := (Finset.mem_Icc.1 hb).1
      by_cases h : a + b ≤ β
      · rw [if_pos h, if_pos (by omega), pow_add]
      · rw [if_neg h, if_neg (by omega), mul_zero]
    rw [Finset.sum_congr rfl hpt, ← Finset.mul_sum]
    have hpa : (0 : ℝ) ≤ (1 / 2) ^ a := by positivity
    by_cases ha : a ≤ β
    · rw [if_pos ha]
      have e : ((1 : ℝ) / 2) ^ a * (1 / 2) ^ (β - a) = (1 / 2) ^ β := by
        rw [← pow_add, Nat.add_sub_cancel' ha]
      calc ((1 : ℝ) / 2) ^ a * ∑ b ∈ Finset.Icc 1 K, (if b ≤ β - a then ((1 : ℝ) / 2) ^ b else 0)
          ≤ (1 / 2) ^ a * (1 - (1 / 2) ^ (β - a)) := mul_le_mul_of_nonneg_left (low1 K (β - a)) hpa
        _ = (1 / 2) ^ a - (1 / 2) ^ β := by rw [mul_sub, mul_one, e]
    · rw [if_neg ha]
      have hz : ∑ b ∈ Finset.Icc 1 K, (if b ≤ β - a then ((1 : ℝ) / 2) ^ b else 0) = 0 := by
        apply Finset.sum_eq_zero
        intro b hb
        have hb1 := (Finset.mem_Icc.1 hb).1
        rw [if_neg (by omega)]
      rw [hz, mul_zero]
  calc _ ≤ ∑ a ∈ Finset.Icc 1 K, (if a ≤ β then ((1 : ℝ) / 2) ^ a - (1 / 2) ^ β else 0) :=
        Finset.sum_le_sum step
    _ ≤ ∑ a ∈ Finset.Icc 1 β, (((1 : ℝ) / 2) ^ a - (1 / 2) ^ β) := by
        rw [← Finset.sum_filter]
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro a
          simp only [Finset.mem_filter, Finset.mem_Icc]
          omega
        · intro a ha _
          have := (Finset.mem_Icc.1 ha).2
          have : ((1 : ℝ) / 2) ^ β ≤ (1 / 2) ^ a := pow_le_pow_of_le_one (by norm_num) (by norm_num) this
          linarith
    _ = 1 - (β + 1) * (1 / 2) ^ β := by
        rw [Finset.sum_sub_distrib, geom_Icc_eq, Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]
        simp only [Nat.add_sub_cancel]
        ring

lemma high2 (K x : ℕ) :
    ∑ a ∈ Finset.Icc 1 K, ∑ b ∈ Finset.Icc 1 K, (if x < a + b then ((1 : ℝ) / 2) ^ (a + b) else 0)
      ≤ ((x : ℝ) + 1) * (1 / 2) ^ x := by
  have step : ∀ a ∈ Finset.Icc 1 K,
      ∑ b ∈ Finset.Icc 1 K, (if x < a + b then ((1 : ℝ) / 2) ^ (a + b) else 0)
        ≤ (if a ≤ x then (1 / 2) ^ x else 0) + (if x < a then (1 / 2) ^ a else 0) := by
    intro a _
    have hpt : ∀ b ∈ Finset.Icc 1 K, (if x < a + b then ((1 : ℝ) / 2) ^ (a + b) else 0)
        = (1 / 2) ^ a * (if x - a < b then (1 / 2) ^ b else 0) := by
      intro b hb
      have hb1 := (Finset.mem_Icc.1 hb).1
      by_cases h : x < a + b
      · rw [if_pos h, if_pos (by omega), pow_add]
      · rw [if_neg h, if_neg (by omega), mul_zero]
    rw [Finset.sum_congr rfl hpt, ← Finset.mul_sum]
    have hpa : (0 : ℝ) ≤ (1 / 2) ^ a := by positivity
    have h1 := mul_le_mul_of_nonneg_left (high1 K (x - a)) hpa
    by_cases ha : a ≤ x
    · rw [if_pos ha, if_neg (by omega), add_zero]
      rwa [← pow_add, Nat.add_sub_cancel' ha] at h1
    · rw [if_neg ha, if_pos (by omega), zero_add]
      rw [show x - a = 0 by omega] at h1 ⊢
      rw [pow_zero, mul_one] at h1
      exact h1
  calc _ ≤ ∑ a ∈ Finset.Icc 1 K, ((if a ≤ x then ((1 : ℝ) / 2) ^ x else 0) + (if x < a then (1 / 2) ^ a else 0)) :=
        Finset.sum_le_sum step
    _ = ∑ a ∈ Finset.Icc 1 K, (if a ≤ x then ((1 : ℝ) / 2) ^ x else 0)
          + ∑ a ∈ Finset.Icc 1 K, (if x < a then ((1 : ℝ) / 2) ^ a else 0) := Finset.sum_add_distrib
    _ ≤ (x : ℝ) * (1 / 2) ^ x + (1 / 2) ^ x := by
        apply add_le_add
        · rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
          have hc : ((Finset.Icc 1 K).filter (fun a => a ≤ x)).card ≤ x := by
            calc _ ≤ (Finset.Icc 1 x).card := Finset.card_le_card (by
                    intro a
                    simp only [Finset.mem_filter, Finset.mem_Icc]
                    omega)
              _ = x := by simp
          have : (((Finset.Icc 1 K).filter (fun a => a ≤ x)).card : ℝ) ≤ x := by exact_mod_cast hc
          exact mul_le_mul_of_nonneg_right this (by positivity)
        · exact high1 K x
    _ = ((x : ℝ) + 1) * (1 / 2) ^ x := by ring

lemma box_low (K β : ℕ) :
    ∑ u ∈ Box 2 K, (if ∑ i, u i ≤ β then ((1 : ℝ) / 2) ^ (∑ i, u i) else 0) ≤ 1 - (β + 1) * (1 / 2) ^ β :=
  (box2_sum K (fun s => if s ≤ β then ((1 : ℝ) / 2) ^ s else 0)).trans_le (low2 K β)

lemma box_high (K x : ℕ) :
    ∑ u ∈ Box 2 K, (if x < ∑ i, u i then ((1 : ℝ) / 2) ^ (∑ i, u i) else 0) ≤ ((x : ℝ) + 1) * (1 / 2) ^ x :=
  (box2_sum K (fun s => if x < s then ((1 : ℝ) / 2) ^ s else 0)).trans_le (high2 K x)

lemma Nz_abs_le (n : ℕ) (ξ : ℤ) (J L : ℕ) : 2 * |Nz n ξ J L| ≤ 3 ^ n := by
  have h : (Nz n ξ J L).natAbs ≤ 3 ^ n / 2 := ZMod.natAbs_valMinAbs_le (thZ n ξ J L)
  have h2 : 2 * (Nz n ξ J L).natAbs ≤ 3 ^ n :=
    (Nat.mul_le_mul_left 2 h).trans (Nat.mul_div_le (3 ^ n) 2)
  have h3 : ((2 * (Nz n ξ J L).natAbs : ℕ) : ℤ) ≤ ((3 ^ n : ℕ) : ℤ) := by exact_mod_cast h2
  push_cast at h3
  exact h3

lemma Nz_step_exact (n : ℕ) (ξ : ℤ) (ε : ℝ) (hε : 9 * ε < 2) (J L b : ℕ) (hJ : 1 ≤ J) (hL : 1 ≤ L)
    (hb : 2 ≤ b) (X' : ℤ) (hX : Nz n ξ J L = 2 ^ b * X') (hsm : |(Nz n ξ J L : ℝ)| ≤ ε * 3 ^ n) :
    Nz n ξ (J + 1) (L + b) = 9 * X' := by
  have hd := Nz_shift_dvd n ξ J L 1 b hJ hL
  rw [hX, pow_one] at hd
  have hd2 : (3 : ℤ) ^ n ∣ 2 ^ b * (Nz n ξ (J + 1) (L + b) - 9 * X') := by
    have e : (2 : ℤ) ^ b * (Nz n ξ (J + 1) (L + b) - 9 * X')
        = 2 ^ b * Nz n ξ (J + 1) (L + b) - 9 * (2 ^ b * X') := by ring
    rw [e]
    exact hd
  have hcop : IsCoprime ((3 : ℤ) ^ n) (2 ^ b) :=
    IsCoprime.pow (Int.isCoprime_iff_gcd_eq_one.mpr (by norm_num))
  have hd3 := hcop.dvd_of_dvd_mul_left hd2
  have hXr : (2 : ℝ) ^ b * |(X' : ℝ)| ≤ ε * 3 ^ n := by
    have e : (Nz n ξ J L : ℝ) = 2 ^ b * X' := by rw [hX]; push_cast; ring
    rw [e, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 ^ b)] at hsm
    exact hsm
  have h4r : (4 : ℝ) ≤ 2 ^ b := by
    calc (4 : ℝ) = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ b := pow_le_pow_right₀ (by norm_num) hb
  have hpos : (0 : ℝ) < 3 ^ n := by positivity
  have a1 : 4 * |(X' : ℝ)| ≤ 2 ^ b * |(X' : ℝ)| := mul_le_mul_of_nonneg_right h4r (abs_nonneg _)
  have a2 : 9 * ε * 3 ^ n < 2 * 3 ^ n := by (first | linarith | nlinarith)
  have hYr : 2 * |(Nz n ξ (J + 1) (L + b) : ℝ)| ≤ 3 ^ n := by
    exact_mod_cast Nz_abs_le n ξ (J + 1) (L + b)
  have hlt : |((Nz n ξ (J + 1) (L + b) - 9 * X' : ℤ) : ℝ)| < 3 ^ n := by
    push_cast
    have := abs_sub (Nz n ξ (J + 1) (L + b) : ℝ) (9 * X')
    rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 9)] at this
    linarith
  have hlt' : |Nz n ξ (J + 1) (L + b) - 9 * X'| < 3 ^ n := by exact_mod_cast hlt
  have := Int.eq_zero_of_abs_lt_dvd hd3 hlt'
  linarith

lemma Vt_le_one (n K : ℕ) (ξ : ℤ) (ε : ℝ) (hε : 0 ≤ ε) : ∀ r j l, Vt n K ξ ε r j l ≤ 1 := by
  intro r
  induction r with
  | zero => intro j l; simp [Vt]
  | succ r ih =>
    intro j l
    simp only [Vt]
    calc _ ≤ ∑ u ∈ Box 2 K, ((1 : ℝ) / 2) ^ (∑ i, u i) := by
          apply Finset.sum_le_sum
          intro u _
          have h1 := cf_le_one n ξ ε hε (j + 1) (l + ∑ i, u i) (∑ i, u i)
          have h2 := cf_nonneg n ξ ε (j + 1) (l + ∑ i, u i) (∑ i, u i)
          have h3 := ih (j + 1) (l + ∑ i, u i)
          have h4 := Vt_nonneg n K ξ ε r (j + 1) (l + ∑ i, u i)
          have hp : (0 : ℝ) ≤ ((1 : ℝ) / 2) ^ (∑ i, u i) := by positivity
          calc _ = ((1 : ℝ) / 2) ^ (∑ i, u i) * (cf n ξ ε (j + 1) (l + ∑ i, u i) (∑ i, u i) *
                Vt n K ξ ε r (j + 1) (l + ∑ i, u i)) := by ring
            _ ≤ ((1 : ℝ) / 2) ^ (∑ i, u i) * 1 := by
                apply mul_le_mul_of_nonneg_left _ hp
                calc _ ≤ 1 * 1 := mul_le_mul h1 h3 h4 zero_le_one
                  _ = 1 := by norm_num
            _ = _ := by ring
      _ ≤ 1 := box_mass_le 2 K

lemma rpow_neg_anti (A : ℝ) (hA : 0 ≤ A) (x y : ℝ) (hx : 0 < x) (hxy : x ≤ y) : y ^ (-A) ≤ x ^ (-A) := by
  rw [Real.rpow_neg hx.le, Real.rpow_neg (hx.le.trans hxy)]
  exact inv_anti₀ (Real.rpow_pos_of_pos hx A) (Real.rpow_le_rpow hx.le hxy hA)

def Case3Hyp (ε : ℝ) : Prop :=
  ∀ A : ℝ, 0 < A → ∀ θ : ℝ, 0 < θ → θ ≤ 1 / 2 → ∃ R1 : ℕ, ∀ R0 : ℕ, R1 ≤ R0 → ∀ M : ℝ, 1 ≤ M →
    ∀ (n K : ℕ) (ξ : ℤ), ¬ (3 : ℤ) ∣ ξ → 2 ≤ K →
    ∀ r j l β : ℕ, R0 ≤ r → j + r = n / 2 →
      (∀ r' j' l' : ℕ, r' < r → j' + r' = n / 2 → Vt n K ξ ε r' j' l' ≤ M * ((r' : ℝ) + 1) ^ (-A)) →
      ¬ White n ξ ε (j + 1) (l + 3) → (2 : ℤ) ^ β ∣ Nz n ξ (j + 1) (l + 3) →
      ¬ (2 : ℤ) ^ (β + 1) ∣ Nz n ξ (j + 1) (l + 3) → θ * r < ((β / 2 + 3 : ℕ) : ℝ) →
      Vt n K ξ ε r j l ≤ M * ((r : ℝ) + 1) ^ (-A)

noncomputable def Wk1 (K : ℕ) : ℕ → ℕ → ℝ
  | 0, c => if c = 0 then 1 else 0
  | s + 1, c => ∑ u ∈ Finset.Icc 1 K, ((1 : ℝ) / 2) ^ u * (if u ≤ c then Wk1 K s (c - u) else 0)

lemma Wk1_succ (K s c : ℕ) : Wk1 K (s + 1) c =
    ∑ u ∈ Finset.Icc 1 K, ((1 : ℝ) / 2) ^ u * (if u ≤ c then Wk1 K s (c - u) else 0) := rfl

lemma Wk1_nonneg (K : ℕ) : ∀ s c, 0 ≤ Wk1 K s c
  | 0, c => by simp only [Wk1]; split_ifs <;> norm_num
  | s + 1, c => by
      rw [Wk1_succ]
      apply Finset.sum_nonneg; intro u _
      apply mul_nonneg (by positivity)
      split_ifs
      · exact Wk1_nonneg K s _
      · exact le_refl 0


/-! W3 (session 31): kill process. `Vk` = the recursion killed (value 0) on a position set `S`;
`VisB` = the `B`-weighted mass of first hits of `S`. Then `Vt ≤ Vk + VisB` whenever `Vt ≤ B` on `S`. -/

open Classical in
noncomputable def Vk (n K : ℕ) (ξ : ℤ) (ε : ℝ) (S : ℕ → ℕ → Prop) : ℕ → ℕ → ℕ → ℝ
  | 0, _, _ => 1
  | r + 1, j, l => ∑ u ∈ Box 2 K, ((1 : ℝ) / 2) ^ (∑ i, u i) *
      cf n ξ ε (j + 1) (l + ∑ i, u i) (∑ i, u i) *
      (if S (j + 1) (l + ∑ i, u i) then 0 else Vk n K ξ ε S r (j + 1) (l + ∑ i, u i))

open Classical in
noncomputable def VisB (K : ℕ) (S : ℕ → ℕ → Prop) (B : ℕ → ℕ → ℝ) : ℕ → ℕ → ℕ → ℝ
  | 0, _, _ => 0
  | r + 1, j, l => ∑ u ∈ Box 2 K, ((1 : ℝ) / 2) ^ (∑ i, u i) *
      (if S (j + 1) (l + ∑ i, u i) then B (j + 1) (l + ∑ i, u i) else VisB K S B r (j + 1) (l + ∑ i, u i))

lemma VisB_nonneg (K : ℕ) (S : ℕ → ℕ → Prop) (B : ℕ → ℕ → ℝ) (hB : ∀ j l, 0 ≤ B j l) :
    ∀ r j l, 0 ≤ VisB K S B r j l
  | 0, _, _ => by simp [VisB]
  | r + 1, j, l => by
    classical
    simp only [VisB]
    apply Finset.sum_nonneg; intro u _
    apply mul_nonneg (by positivity)
    split_ifs
    · exact hB _ _
    · exact VisB_nonneg K S B hB r _ _

lemma Wk1_push (K s N : ℕ) (F : ℕ → ℝ) (hF : ∀ c, 0 ≤ F c) :
    ∑ u ∈ Finset.Icc 1 K, ((1 : ℝ) / 2) ^ u * ∑ c ∈ Finset.range N, Wk1 K s c * F (u + c) ≤
      ∑ c ∈ Finset.range (N + K), Wk1 K (s + 1) c * F c := by
  have hR : ∑ c ∈ Finset.range (N + K), Wk1 K (s + 1) c * F c =
      ∑ u ∈ Finset.Icc 1 K, ((1 : ℝ) / 2) ^ u *
        ∑ c ∈ Finset.range (N + K), (if u ≤ c then Wk1 K s (c - u) * F c else 0) := by
    simp only [Wk1_succ, Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro u _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro c _
    split_ifs <;> ring
  rw [hR]
  apply Finset.sum_le_sum; intro u hu
  simp only [Finset.mem_Icc] at hu
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  rw [← Finset.sum_filter]
  have hsub : (Finset.range N).map (addLeftEmbedding u) ⊆
      (Finset.range (N + K)).filter (fun c => u ≤ c) := by
    intro c hc
    simp only [Finset.mem_map, Finset.mem_range, addLeftEmbedding_apply] at hc
    obtain ⟨c', hc', rfl⟩ := hc
    simp only [Finset.mem_filter, Finset.mem_range]; omega
  calc ∑ c ∈ Finset.range N, Wk1 K s c * F (u + c)
      = ∑ c ∈ (Finset.range N).map (addLeftEmbedding u), Wk1 K s (c - u) * F c := by
        rw [Finset.sum_map]
        apply Finset.sum_congr rfl; intro c _
        simp only [addLeftEmbedding_apply, Nat.add_sub_cancel_left]
    _ ≤ ∑ c ∈ (Finset.range (N + K)).filter (fun c => u ≤ c), Wk1 K s (c - u) * F c := by
        apply Finset.sum_le_sum_of_subset_of_nonneg hsub
        intro c _ _; exact mul_nonneg (Wk1_nonneg K s _) (hF c)

lemma Wk1_push2 (K s N : ℕ) (F : ℕ → ℝ) (hF : ∀ c, 0 ≤ F c) :
    ∑ u ∈ Box 2 K, ((1 : ℝ) / 2) ^ (∑ i, u i) * ∑ c ∈ Finset.range N, Wk1 K s c * F ((∑ i, u i) + c) ≤
      ∑ c ∈ Finset.range (N + 2 * K), Wk1 K (s + 2) c * F c := by
  rw [box2_sum K (fun t => ((1 : ℝ) / 2) ^ t * ∑ c ∈ Finset.range N, Wk1 K s c * F (t + c))]
  have h1 : ∀ a, ∑ b ∈ Finset.Icc 1 K, ((1 : ℝ) / 2) ^ (a + b) *
      ∑ c ∈ Finset.range N, Wk1 K s c * F (a + b + c) =
      ((1 : ℝ) / 2) ^ a * ∑ b ∈ Finset.Icc 1 K, ((1 : ℝ) / 2) ^ b *
        ∑ c ∈ Finset.range N, Wk1 K s c * F (b + c + a) := by
    intro a
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro b _
    rw [pow_add]
    have : ∀ c, F (a + b + c) = F (b + c + a) := fun c => by congr 1; ring
    simp only [this]; ring
  simp only [h1]
  calc ∑ a ∈ Finset.Icc 1 K, ((1 : ℝ) / 2) ^ a * ∑ b ∈ Finset.Icc 1 K, ((1 : ℝ) / 2) ^ b *
        ∑ c ∈ Finset.range N, Wk1 K s c * F (b + c + a)
      ≤ ∑ a ∈ Finset.Icc 1 K, ((1 : ℝ) / 2) ^ a *
          ∑ c ∈ Finset.range (N + K), Wk1 K (s + 1) c * F (c + a) := by
        apply Finset.sum_le_sum; intro a _
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact Wk1_push K s N (fun t => F (t + a)) (fun t => hF _)
    _ = ∑ a ∈ Finset.Icc 1 K, ((1 : ℝ) / 2) ^ a *
          ∑ c ∈ Finset.range (N + K), Wk1 K (s + 1) c * F (a + c) := by
        apply Finset.sum_congr rfl; intro a _
        congr 1; apply Finset.sum_congr rfl; intro c _; rw [Nat.add_comm c a]
    _ ≤ ∑ c ∈ Finset.range (N + K + K), Wk1 K (s + 1 + 1) c * F c := Wk1_push K (s + 1) (N + K) F hF
    _ = ∑ c ∈ Finset.range (N + 2 * K), Wk1 K (s + 2) c * F c := by
        rw [show N + K + K = N + 2 * K by ring]

open Classical in
theorem VisB_le (K : ℕ) (S : ℕ → ℕ → Prop) (B : ℕ → ℕ → ℝ) (hB : ∀ j l, 0 ≤ B j l) :
    ∀ r j l, VisB K S B r j l ≤ ∑ a ∈ Finset.range r, ∑ c ∈ Finset.range (2 * K * (a + 1) + 1),
      Wk1 K (2 * (a + 1)) c * (if S (j + a + 1) (l + c) then B (j + a + 1) (l + c) else 0) := by
  intro r
  induction r with
  | zero => intro j l; simp [VisB]
  | succ r ih =>
    intro j l
    set G : ℕ → ℕ → ℝ := fun j l => if S j l then B j l else 0 with hG
    have hG0 : ∀ j l, 0 ≤ G j l := fun j l => by simp only [hG]; split_ifs; exact hB j l; exact le_rfl
    -- termwise: first hit ≤ G + VisB
    have h1 : VisB K S B (r + 1) j l ≤ ∑ u ∈ Box 2 K, ((1 : ℝ) / 2) ^ (∑ i, u i) *
        (G (j + 1) (l + ∑ i, u i) + VisB K S B r (j + 1) (l + ∑ i, u i)) := by
      simp only [VisB]
      apply Finset.sum_le_sum; intro u _
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      have hv := VisB_nonneg K S B hB r (j + 1) (l + ∑ i, u i)
      simp only [hG]; split_ifs <;> linarith
    -- first part: one pair from Wk1 K 0
    have h2 : ∑ u ∈ Box 2 K, ((1 : ℝ) / 2) ^ (∑ i, u i) * G (j + 1) (l + ∑ i, u i) ≤
        ∑ c ∈ Finset.range (2 * K * (0 + 1) + 1), Wk1 K (2 * (0 + 1)) c * G (j + 0 + 1) (l + c) := by
      have h := Wk1_push2 K 0 1 (fun t => G (j + 1) (l + t)) (fun t => hG0 _ _)
      have e : ∀ t, ∑ c ∈ Finset.range 1, Wk1 K 0 c * G (j + 1) (l + (t + c)) = G (j + 1) (l + t) := by
        intro t; simp [Wk1]
      simp only [e] at h
      have e2 : 2 * K * (0 + 1) + 1 = 1 + 2 * K := by ring
      rw [e2]; simpa using h
    -- second part: push the IH bound one pair
    have h3 : ∑ u ∈ Box 2 K, ((1 : ℝ) / 2) ^ (∑ i, u i) * VisB K S B r (j + 1) (l + ∑ i, u i) ≤
        ∑ a ∈ Finset.range r, ∑ c ∈ Finset.range (2 * K * (a + 1 + 1) + 1),
          Wk1 K (2 * (a + 1 + 1)) c * G (j + (a + 1) + 1) (l + c) := by
      calc _ ≤ ∑ u ∈ Box 2 K, ((1 : ℝ) / 2) ^ (∑ i, u i) * ∑ a ∈ Finset.range r,
              ∑ c ∈ Finset.range (2 * K * (a + 1) + 1),
                Wk1 K (2 * (a + 1)) c * G (j + 1 + a + 1) ((l + ∑ i, u i) + c) := by
            apply Finset.sum_le_sum; intro u _
            exact mul_le_mul_of_nonneg_left (ih _ _) (by positivity)
        _ = ∑ a ∈ Finset.range r, ∑ u ∈ Box 2 K, ((1 : ℝ) / 2) ^ (∑ i, u i) *
              ∑ c ∈ Finset.range (2 * K * (a + 1) + 1),
                Wk1 K (2 * (a + 1)) c * G (j + 1 + a + 1) (l + ((∑ i, u i) + c)) := by
            simp only [Finset.mul_sum]
            rw [Finset.sum_comm]
            apply Finset.sum_congr rfl; intro a _
            apply Finset.sum_congr rfl; intro u _
            apply Finset.sum_congr rfl; intro c _
            rw [Nat.add_assoc l]
        _ ≤ ∑ a ∈ Finset.range r, ∑ c ∈ Finset.range (2 * K * (a + 1) + 1 + 2 * K),
              Wk1 K (2 * (a + 1) + 2) c * G (j + 1 + a + 1) (l + c) := by
            apply Finset.sum_le_sum; intro a _
            exact Wk1_push2 K (2 * (a + 1)) _ (fun t => G (j + 1 + a + 1) (l + t)) (fun t => hG0 _ _)
        _ = _ := by
            apply Finset.sum_congr rfl; intro a _
            rw [show 2 * K * (a + 1) + 1 + 2 * K = 2 * K * (a + 1 + 1) + 1 by ring,
              show 2 * (a + 1) + 2 = 2 * (a + 1 + 1) by ring,
              show j + 1 + a + 1 = j + (a + 1) + 1 by ring]
    rw [Finset.sum_range_succ']
    calc VisB K S B (r + 1) j l ≤ _ := h1
      _ = ∑ u ∈ Box 2 K, ((1 : ℝ) / 2) ^ (∑ i, u i) * VisB K S B r (j + 1) (l + ∑ i, u i) +
          ∑ u ∈ Box 2 K, ((1 : ℝ) / 2) ^ (∑ i, u i) * G (j + 1) (l + ∑ i, u i) := by
        rw [← Finset.sum_add_distrib]; apply Finset.sum_congr rfl; intro u _; ring
      _ ≤ _ := add_le_add h3 h2


/-! W5 (session 32): kill-set calculus for `Vk` and the exit-overshoot bound. -/

lemma Vk_nonneg (n K : ℕ) (ξ : ℤ) (ε : ℝ) (S : ℕ → ℕ → Prop) : ∀ r j l, 0 ≤ Vk n K ξ ε S r j l
  | 0, _, _ => by simp [Vk]
  | r + 1, j, l => by
    classical
    simp only [Vk]
    apply Finset.sum_nonneg; intro u _
    apply mul_nonneg (mul_nonneg (by positivity) (cf_nonneg n ξ ε _ _ _))
    split_ifs
    · exact le_rfl
    · exact Vk_nonneg n K ξ ε S r _ _

lemma Vk_anti (n K : ℕ) (ξ : ℤ) (ε : ℝ) (S S' : ℕ → ℕ → Prop) (h : ∀ j l, S j l → S' j l) :
    ∀ r j l, Vk n K ξ ε S' r j l ≤ Vk n K ξ ε S r j l := by
  classical
  intro r
  induction r with
  | zero => intro j l; simp [Vk]
  | succ r ih =>
    intro j l
    simp only [Vk]
    apply Finset.sum_le_sum; intro u _
    have hwc : 0 ≤ ((1 : ℝ) / 2) ^ (∑ i, u i) * cf n ξ ε (j + 1) (l + ∑ i, u i) (∑ i, u i) :=
      mul_nonneg (by positivity) (cf_nonneg n ξ ε _ _ _)
    apply mul_le_mul_of_nonneg_left _ hwc
    by_cases h' : S' (j + 1) (l + ∑ i, u i)
    · rw [if_pos h']
      split_ifs
      · exact le_rfl
      · exact Vk_nonneg n K ξ ε S r _ _
    · rw [if_neg h', if_neg (fun hs => h' (h _ _ hs))]
      exact ih _ _

lemma Vk_le_Vt (n K : ℕ) (ξ : ℤ) (ε : ℝ) (S : ℕ → ℕ → Prop) :
    ∀ r j l, Vk n K ξ ε S r j l ≤ Vt n K ξ ε r j l := by
  classical
  intro r
  induction r with
  | zero => intro j l; simp [Vk, Vt]
  | succ r ih =>
    intro j l
    simp only [Vk, Vt]
    apply Finset.sum_le_sum; intro u _
    have hwc : 0 ≤ ((1 : ℝ) / 2) ^ (∑ i, u i) * cf n ξ ε (j + 1) (l + ∑ i, u i) (∑ i, u i) :=
      mul_nonneg (by positivity) (cf_nonneg n ξ ε _ _ _)
    apply mul_le_mul_of_nonneg_left _ hwc
    split_ifs
    · exact Vt_nonneg n K ξ ε r _ _
    · exact ih _ _

lemma VisB_mono (K : ℕ) (S : ℕ → ℕ → Prop) (B1 B2 : ℕ → ℕ → ℝ) (h : ∀ j l, B1 j l ≤ B2 j l) :
    ∀ r j l, VisB K S B1 r j l ≤ VisB K S B2 r j l := by
  classical
  intro r
  induction r with
  | zero => intro j l; simp [VisB]
  | succ r ih =>
    intro j l
    simp only [VisB]
    apply Finset.sum_le_sum; intro u _
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    split_ifs
    · exact h _ _
    · exact ih _ _

lemma VisB_add (K : ℕ) (S : ℕ → ℕ → Prop) (B1 B2 : ℕ → ℕ → ℝ) :
    ∀ r j l, VisB K S (fun j l => B1 j l + B2 j l) r j l = VisB K S B1 r j l + VisB K S B2 r j l := by
  classical
  intro r
  induction r with
  | zero => intro j l; simp [VisB]
  | succ r ih =>
    intro j l
    simp only [VisB, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro u _
    split_ifs
    · ring
    · rw [ih]; ring

lemma VisB_smul (K : ℕ) (S : ℕ → ℕ → Prop) (c : ℝ) (B : ℕ → ℕ → ℝ) :
    ∀ r j l, VisB K S (fun j l => c * B j l) r j l = c * VisB K S B r j l := by
  classical
  intro r
  induction r with
  | zero => intro j l; simp [VisB]
  | succ r ih =>
    intro j l
    simp only [VisB, Finset.mul_sum]
    apply Finset.sum_congr rfl; intro u _
    split_ifs
    · ring
    · rw [ih]; ring

lemma VisB_drop (K : ℕ) (S S2 : ℕ → ℕ → Prop) (B : ℕ → ℕ → ℝ) (hB0 : ∀ j l, 0 ≤ B j l)
    (hz : ∀ j l, S2 j l → ¬ S j l → B j l = 0) :
    ∀ r j l, VisB K (fun j l => S j l ∨ S2 j l) B r j l ≤ VisB K S B r j l := by
  classical
  intro r
  induction r with
  | zero => intro j l; simp [VisB]
  | succ r ih =>
    intro j l
    simp only [VisB]
    apply Finset.sum_le_sum; intro u _
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    by_cases hS : S (j + 1) (l + ∑ i, u i)
    · rw [if_pos (Or.inl hS), if_pos hS]
    · rw [if_neg hS]
      by_cases h2 : S2 (j + 1) (l + ∑ i, u i)
      · rw [if_pos (Or.inr h2), hz _ _ h2 hS]
        exact VisB_nonneg K S B hB0 r _ _
      · rw [if_neg (by tauto)]
        exact ih _ _

lemma Vk_row_kill (n K : ℕ) (ξ : ℤ) (ε : ℝ) (S : ℕ → ℕ → Prop) (J : ℕ) (hrow : ∀ l', S J l') :
    ∀ r j l, j < J → J ≤ j + r → Vk n K ξ ε S r j l = 0 := by
  classical
  intro r
  induction r with
  | zero => intro j l h1 h2; omega
  | succ r ih =>
    intro j l h1 h2
    simp only [Vk]
    apply Finset.sum_eq_zero; intro u _
    by_cases hJ : j + 1 = J
    · rw [if_pos (by rw [hJ]; exact hrow _), mul_zero]
    · rw [ih (j + 1) _ (by omega) (by omega)]
      split_ifs <;> simp

open Classical in
lemma overshoot (K L E : ℕ) :
    ∀ r j l, l ≤ L → VisB K (fun _ l' => L < l') (fun _ l' => if L + E < l' then 1 else 0) r j l ≤
      ((E : ℝ) + 1) * (1 / 2) ^ E := by
  intro r
  induction r with
  | zero => intro j l _; simp only [VisB]; positivity
  | succ r ih =>
    intro j l hl
    simp only [VisB]
    have hγ : (0 : ℝ) ≤ ((E : ℝ) + 1) * (1 / 2) ^ E := by positivity
    calc _ ≤ ∑ u ∈ Box 2 K, ((if (L - l) + E < ∑ i, u i then ((1 : ℝ) / 2) ^ (∑ i, u i) else 0) +
          ((E : ℝ) + 1) * (1 / 2) ^ E * (if ∑ i, u i ≤ L - l then ((1 : ℝ) / 2) ^ (∑ i, u i) else 0)) := by
          apply Finset.sum_le_sum; intro u _
          have hw : (0 : ℝ) ≤ ((1 : ℝ) / 2) ^ (∑ i, u i) := by positivity
          by_cases h1 : L < l + ∑ i, u i
          · rw [if_pos h1, if_neg (show ¬ (∑ i, u i ≤ L - l) by omega), mul_zero, add_zero]
            by_cases h2 : L + E < l + ∑ i, u i
            · rw [if_pos h2, if_pos (show L - l + E < ∑ i, u i by omega), mul_one]
            · rw [if_neg h2, if_neg (show ¬ (L - l + E < ∑ i, u i) by omega), mul_zero]
          · rw [if_neg h1, if_neg (show ¬ (L - l + E < ∑ i, u i) by omega),
              if_pos (show ∑ i, u i ≤ L - l by omega), zero_add]
            have := ih (j + 1) (l + ∑ i, u i) (by omega)
            (first | linarith [mul_le_mul_of_nonneg_left this hw] | nlinarith [mul_le_mul_of_nonneg_left this hw])
      _ = ∑ u ∈ Box 2 K, (if (L - l) + E < ∑ i, u i then ((1 : ℝ) / 2) ^ (∑ i, u i) else 0) +
          ((E : ℝ) + 1) * (1 / 2) ^ E *
            ∑ u ∈ Box 2 K, (if ∑ i, u i ≤ L - l then ((1 : ℝ) / 2) ^ (∑ i, u i) else 0) := by
          rw [Finset.sum_add_distrib, Finset.mul_sum]
      _ ≤ ((E : ℝ) + 1) * (1 / 2) ^ E := by
          refine le_trans (add_le_add (box_high K (L - l + E))
            (mul_le_mul_of_nonneg_left (box_low K (L - l)) hγ)) ?_
          generalize L - l = d
          have hq : (0 : ℝ) ≤ (1 / 2) ^ d := by positivity
          have hp : (0 : ℝ) ≤ (1 / 2) ^ E := by positivity
          have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
          have hE0 : (0 : ℝ) ≤ E := Nat.cast_nonneg E
          have hdE : ((d : ℝ) + E + 1) ≤ ((E : ℝ) + 1) * ((d : ℝ) + 1) := by (first | linarith | nlinarith)
          push_cast
          rw [pow_add]
          (first | linarith [mul_le_mul_of_nonneg_right hdE (mul_nonneg hq hp)] | nlinarith [mul_le_mul_of_nonneg_right hdE (mul_nonneg hq hp)])


open Classical in
theorem black_run_Vk (n K : ℕ) (ξ : ℤ) (ε : ℝ) (D : ℕ) (hε : 0 < ε) (hεD : ε * (2 ^ D + 9) < 1)
    (hK : 2 ≤ K) (S : ℕ → ℕ → Prop) (h : ℝ) (hh : 0 ≤ h) :
    ∀ β r j l, β / 2 + 3 ≤ r → ¬ White n ξ ε (j + 1) (l + 3) →
      (2 : ℤ) ^ β ∣ Nz n ξ (j + 1) (l + 3) → ¬ (2 : ℤ) ^ (β + 1) ∣ Nz n ξ (j + 1) (l + 3) →
      (∀ t l', 1 ≤ t → t ≤ β / 2 + 3 → ¬ S (j + t) l' → Vk n K ξ ε S (r - t) (j + t) l' ≤ h) →
      Vk n K ξ ε S r j l ≤ h * (1 - (1 - Real.exp (-ε ^ 3)) / 4 * (1 - (D + 1) * (1 / 2) ^ D)) := by
  have hD9 : (10 : ℝ) ≤ 2 ^ D + 9 := by
    have : (1 : ℝ) ≤ 2 ^ D := one_le_pow₀ (by norm_num)
    linarith
  have hε2 : ε < 1 / 2 := by (first | linarith | nlinarith)
  have hε9 : 9 * ε < 2 := by (first | linarith | nlinarith)
  set η := (1 - Real.exp (-ε ^ 3)) / 4 with hη
  set δ : ℝ := (D + 1) * (1 / 2) ^ D with hδ
  have hη0 : 0 ≤ η := by
    have : Real.exp (-ε ^ 3) ≤ 1 := Real.exp_le_one_iff.2 (by have := pow_pos hε 3; linarith)
    rw [hη]; linarith
  have hη1 : η ≤ 1 := by
    have := Real.exp_pos (-ε ^ 3)
    rw [hη]; linarith
  have hδ0 : 0 ≤ δ := by positivity
  intro β
  induction β using Nat.strong_induction_on with
  | _ β ih =>
  intro r j l hr hB hβ hβ1 hV
  obtain ⟨r', rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
  obtain ⟨r'', rfl⟩ : ∃ r'', r' = r'' + 1 := ⟨r' - 1, by omega⟩
  have hsm : |(Nz n ξ (j + 1) (l + 3) : ℝ)| ≤ ε * 3 ^ n :=
    not_lt.1 ((white_iff n ξ ε hε hε2 (j + 1) (l + 3)).not.1 hB)
  have hcf : ∀ s, cf n ξ ε (j + 1) (l + s) s = 1 := by
    intro s
    unfold cf
    rw [if_neg]
    rintro ⟨rfl, hw⟩
    exact hB hw
  set g : ℕ → ℝ := fun s => h * (1 - η) + h * η * (δ * (if s ≤ β then 1 else 0) +
    (if β + D < s then 1 else 0)) with hg
  have hterm : ∀ u ∈ Box 2 K, (if S (j + 1) (l + ∑ i, u i) then 0 else
      Vk n K ξ ε S (r'' + 1) (j + 1) (l + ∑ i, u i)) ≤ g (∑ i, u i) := by
    intro u hu
    have hs2 : 2 ≤ ∑ i, u i := by
      simp only [Box, Fintype.mem_piFinset, Finset.mem_Icc] at hu
      rw [Fin.sum_univ_two]
      have := (hu 0).1
      have := (hu 1).1
      omega
    generalize ∑ i, u i = s at hs2 ⊢
    have hgw : h * (1 - η) ≤ g s := by
      simp only [hg]
      have : 0 ≤ h * η * (δ * (if s ≤ β then 1 else 0) + (if β + D < s then 1 else 0)) := by
        apply mul_nonneg (mul_nonneg hh hη0)
        apply add_nonneg (mul_nonneg hδ0 (by split_ifs <;> norm_num)) (by split_ifs <;> norm_num)
      linarith
    by_cases hSs : S (j + 1) (l + s)
    · rw [if_pos hSs]
      exact le_trans (mul_nonneg hh (by linarith)) hgw
    rw [if_neg hSs]
    have hWcase : White n ξ ε (j + 1 + 1) (l + s + 3) →
        Vk n K ξ ε S (r'' + 1) (j + 1) (l + s) ≤ g s := by
      intro hW
      refine le_trans ?_ hgw
      rw [Vk]
      refine step_white n K ξ ε hε.le hK (j + 1) (l + s) hW
        (fun b => if S (j + 1 + 1) (l + s + b) then 0 else Vk n K ξ ε S r'' (j + 1 + 1) (l + s + b)) h
        (fun b => ?_) (fun b => ?_)
      · show 0 ≤ (if S (j + 1 + 1) (l + s + b) then (0 : ℝ) else Vk n K ξ ε S r'' (j + 1 + 1) (l + s + b))
        split_ifs
        · exact le_rfl
        · exact Vk_nonneg n K ξ ε S _ _ _
      show (if S (j + 1 + 1) (l + s + b) then (0 : ℝ) else Vk n K ξ ε S r'' (j + 1 + 1) (l + s + b)) ≤ h
      split_ifs with hS2
      · exact hh
      have := hV 2 (l + s + b) (by norm_num) (by omega)
        (by rw [show j + 2 = j + 1 + 1 by omega]; exact hS2)
      rw [show r'' + 1 + 1 - 2 = r'' by omega, show j + 2 = j + 1 + 1 by omega] at this
      exact this
    by_cases hsb : s ≤ β
    · by_cases hW : White n ξ ε (j + 1 + 1) (l + s + 3)
      · exact hWcase hW
      · obtain ⟨X', hX'⟩ : (2 : ℤ) ^ s ∣ Nz n ξ (j + 1) (l + 3) := (pow_dvd_pow 2 hsb).trans hβ
        have hex := Nz_step_exact n ξ ε hε9 (j + 1) (l + 3) s (by omega) (by omega) hs2 X' hX' hsm
        rw [show l + 3 + s = l + s + 3 by omega] at hex
        have hsplit : (2 : ℤ) ^ β = 2 ^ s * 2 ^ (β - s) := by rw [← pow_add, Nat.add_sub_cancel' hsb]
        have hd1 : (2 : ℤ) ^ (β - s) ∣ X' := by
          have hβ' := hβ
          rw [hX', hsplit] at hβ'
          exact (mul_dvd_mul_iff_left (by positivity)).1 hβ'
        have hd2 : ¬ (2 : ℤ) ^ (β - s + 1) ∣ 9 * X' := by
          intro hc
          have hc2 : (2 : ℤ) ^ (β - s + 1) ∣ X' :=
            (IsCoprime.pow_left (Int.isCoprime_iff_gcd_eq_one.mpr (by norm_num) :
              IsCoprime (2 : ℤ) 9)).dvd_of_dvd_mul_left hc
          apply hβ1
          rw [hX', show β + 1 = s + (β - s + 1) by omega, pow_add]
          exact mul_dvd_mul_left _ hc2
        have hV' : ∀ t l', 1 ≤ t → t ≤ (β - s) / 2 + 3 → ¬ S (j + 1 + t) l' →
            Vk n K ξ ε S (r'' + 1 - t) (j + 1 + t) l' ≤ h := by
          intro t l' ht1 ht2 hSt
          have := hV (t + 1) l' (by omega) (by omega)
            (by rw [show j + (t + 1) = j + 1 + t by omega]; exact hSt)
          rw [show r'' + 1 + 1 - (t + 1) = r'' + 1 - t by omega,
            show j + (t + 1) = j + 1 + t by omega] at this
          exact this
        have hIH := ih (β - s) (by omega) (r'' + 1) (j + 1) (l + s) (by omega) hW
          (by rw [hex]; exact dvd_mul_of_dvd_right hd1 9) (by rw [hex]; exact hd2) hV'
        refine le_trans hIH (le_of_eq ?_)
        have : ¬ β + D < s := by omega
        simp only [hg, if_pos hsb, if_neg this]
        ring
    · by_cases hsD : s ≤ β + D
      · apply hWcase
        have h3 : (0 : ℝ) < 3 ^ n := by positivity
        have h2b : (1 : ℝ) ≤ 2 ^ β := one_le_pow₀ (by norm_num)
        have h2s : (2 : ℝ) ^ s ≤ 2 ^ β * 2 ^ D := by
          rw [← pow_add]
          exact pow_le_pow_right₀ (by norm_num) hsD
        have e1 : ε * 3 ^ n * 2 ^ s ≤ ε * 3 ^ n * (2 ^ β * 2 ^ D) :=
          mul_le_mul_of_nonneg_left h2s (by positivity)
        have e2 : ε * 3 ^ n ≤ ε * 3 ^ n * 2 ^ β := le_mul_of_one_le_right (by positivity) h2b
        have e3 : ε * (2 ^ D + 9) * (2 ^ β * 3 ^ n) < 1 * (2 ^ β * 3 ^ n) :=
          mul_lt_mul_of_pos_right hεD (by positivity)
        have hw := white_of_exit n ξ ε hε hε2 (j + 1) (l + 3) 1 s β (by omega) (by omega) hβ hβ1
          (by omega) (by rw [pow_one]; nlinarith)
        rw [show l + 3 + s = l + s + 3 by omega] at hw
        exact hw
      · have hv1 := hV 1 (l + s) le_rfl (by omega) hSs
        rw [show r'' + 1 + 1 - 1 = r'' + 1 by omega] at hv1
        have hgs : g s = h := by
          simp only [hg, if_neg hsb, if_pos (by omega : β + D < s)]
          ring
        linarith
  rw [Vk]
  have hsum : ∑ u ∈ Box 2 K, ((1 : ℝ) / 2) ^ (∑ i, u i) * cf n ξ ε (j + 1) (l + ∑ i, u i) (∑ i, u i) *
      (if S (j + 1) (l + ∑ i, u i) then 0 else Vk n K ξ ε S (r'' + 1) (j + 1) (l + ∑ i, u i))
        ≤ ∑ u ∈ Box 2 K, ((1 : ℝ) / 2) ^ (∑ i, u i) * g (∑ i, u i) := by
    apply Finset.sum_le_sum
    intro u hu
    rw [hcf, mul_one]
    exact mul_le_mul_of_nonneg_left (hterm u hu) (by positivity)
  refine le_trans hsum ?_
  have hexp : ∑ u ∈ Box 2 K, ((1 : ℝ) / 2) ^ (∑ i, u i) * g (∑ i, u i) =
      h * (1 - η) * (∑ u ∈ Box 2 K, ((1 : ℝ) / 2) ^ (∑ i, u i))
      + h * η * δ * (∑ u ∈ Box 2 K, (if ∑ i, u i ≤ β then ((1 : ℝ) / 2) ^ (∑ i, u i) else 0))
      + h * η * (∑ u ∈ Box 2 K, (if β + D < ∑ i, u i then ((1 : ℝ) / 2) ^ (∑ i, u i) else 0)) := by
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib,
      ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro u _
    simp only [hg]
    split_ifs <;> ring
  rw [hexp]
  have hm := box_mass_le 2 K
  have hlo := box_low K β
  have hhi := box_high K (β + D)
  have key : (((β + D : ℕ) : ℝ) + 1) * (1 / 2) ^ (β + D) ≤ δ * ((β + 1) * (1 / 2) ^ β) := by
    rw [hδ, pow_add]
    have hp : (0 : ℝ) ≤ (1 / 2) ^ β * (1 / 2) ^ D := by positivity
    have hc : (((β + D : ℕ) : ℝ) + 1) ≤ (D + 1) * (β + 1) := by
      push_cast
      (first | linarith [mul_nonneg (Nat.cast_nonneg β : (0 : ℝ) ≤ β) (Nat.cast_nonneg D : (0 : ℝ) ≤ D)] | nlinarith [mul_nonneg (Nat.cast_nonneg β : (0 : ℝ) ≤ β) (Nat.cast_nonneg D : (0 : ℝ) ≤ D)])
    (first | linarith [mul_le_mul_of_nonneg_right hc hp] | nlinarith [mul_le_mul_of_nonneg_right hc hp])
  have a1 := mul_le_mul_of_nonneg_left hm (mul_nonneg hh (by linarith : (0 : ℝ) ≤ 1 - η))
  have a2 := mul_le_mul_of_nonneg_left hlo (mul_nonneg (mul_nonneg hh hη0) hδ0)
  have a3 := mul_le_mul_of_nonneg_left (hhi.trans key) (mul_nonneg hh hη0)
  (first | linarith | nlinarith)

/-! ## 8e (session 29): Tao Prop 7.8 induction, Cases 1 and 2 discharged; Case 3 isolated as `Case3Hyp`. -/



/-! ## W6 (session 33): block gains, Claim(k). -/

lemma Wk1_zero_col (K s : ℕ) : Wk1 K (s + 1) 0 = 0 := by
  rw [Wk1_succ]
  apply Finset.sum_eq_zero; intro u hu
  have : ¬ u ≤ 0 := by have := (Finset.mem_Icc.1 hu).1; omega
  rw [if_neg this, mul_zero]

theorem Vk_refineN (n K : ℕ) (ξ : ℤ) (ε : ℝ) (hε : 0 ≤ ε) (S S' : ℕ → ℕ → Prop) (B : ℕ → ℕ → ℝ) (N : ℕ)
    (hB0 : ∀ j l, 0 ≤ B j l)
    (hB : ∀ r j l, j + r = N → S' j l → ¬ S j l → Vk n K ξ ε S r j l ≤ B j l) :
    ∀ r j l, j + r = N →
      Vk n K ξ ε S r j l ≤ Vk n K ξ ε (fun j l => S j l ∨ S' j l) r j l + VisB K S' B r j l := by
  classical
  intro r
  induction r with
  | zero => intro j l _; simp [Vk, VisB]
  | succ r ih =>
    intro j l hN
    simp only [Vk, VisB, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum; intro u _
    have hw : (0 : ℝ) ≤ ((1 : ℝ) / 2) ^ (∑ i, u i) := by positivity
    have hc0 := cf_nonneg n ξ ε (j + 1) (l + ∑ i, u i) (∑ i, u i)
    have hc1 := cf_le_one n ξ ε hε (j + 1) (l + ∑ i, u i) (∑ i, u i)
    have hwc : 0 ≤ ((1 : ℝ) / 2) ^ (∑ i, u i) * cf n ξ ε (j + 1) (l + ∑ i, u i) (∑ i, u i) :=
      mul_nonneg hw hc0
    have hv := VisB_nonneg K S' B hB0 r (j + 1) (l + ∑ i, u i)
    by_cases hS : S (j + 1) (l + ∑ i, u i)
    · rw [if_pos hS, if_pos (Or.inl hS), mul_zero, zero_add]
      split_ifs
      · exact mul_nonneg hw (hB0 _ _)
      · exact mul_nonneg hw hv
    · rw [if_neg hS]
      by_cases hS' : S' (j + 1) (l + ∑ i, u i)
      · rw [if_pos (Or.inr hS'), if_pos hS', mul_zero, zero_add]
        have h1 := hB r (j + 1) (l + ∑ i, u i) (by omega) hS' hS
        have h2 := Vk_nonneg n K ξ ε S r (j + 1) (l + ∑ i, u i)
        have h3 : cf n ξ ε (j + 1) (l + ∑ i, u i) (∑ i, u i) * Vk n K ξ ε S r (j + 1) (l + ∑ i, u i) ≤
            B (j + 1) (l + ∑ i, u i) := by (first | linarith | nlinarith)
        (first | linarith [mul_le_mul_of_nonneg_left h3 hw] | nlinarith [mul_le_mul_of_nonneg_left h3 hw])
      · rw [if_neg (by tauto), if_neg hS']
        have h1 := ih (j + 1) (l + ∑ i, u i) (by omega)
        have h3 : cf n ξ ε (j + 1) (l + ∑ i, u i) (∑ i, u i) * VisB K S' B r (j + 1) (l + ∑ i, u i) ≤
            VisB K S' B r (j + 1) (l + ∑ i, u i) := by (first | linarith | nlinarith)
        (first | linarith [mul_le_mul_of_nonneg_left h1 hwc, mul_le_mul_of_nonneg_left h3 hw] | nlinarith [mul_le_mul_of_nonneg_left h1 hwc, mul_le_mul_of_nonneg_left h3 hw])

lemma VisB_block (K blk Dmax : ℕ) (W ρ : ℝ) (hW : 0 ≤ W) (S' : ℕ → ℕ → Prop) (j l : ℕ)
    (hS' : ∀ j' l', S' j' l' → j < j' ∧ j' ≤ j + blk ∧ (l + blk * Dmax < l' ∨ l' ≤ l))
    (hρ : ∑ a ∈ Finset.range blk, ∑ c ∈ Finset.range (2 * K * (a + 1) + 1),
      Wk1 K (2 * (a + 1)) c * (if blk * Dmax < c then (1 : ℝ) else 0) ≤ ρ) (r : ℕ) :
    VisB K S' (fun _ _ => W) r j l ≤ W * ρ := by
  classical
  refine (VisB_le K S' (fun _ _ => W) (fun _ _ => hW) r j l).trans ?_
  have hg0 : ∀ a, 0 ≤ ∑ c ∈ Finset.range (2 * K * (a + 1) + 1),
      Wk1 K (2 * (a + 1)) c * (if blk * Dmax < c then (1 : ℝ) else 0) :=
    fun a => Finset.sum_nonneg (fun c _ => mul_nonneg (Wk1_nonneg K _ c) (by split_ifs <;> norm_num))
  calc _ ≤ ∑ a ∈ Finset.range r, (if a < blk then W * ∑ c ∈ Finset.range (2 * K * (a + 1) + 1),
        Wk1 K (2 * (a + 1)) c * (if blk * Dmax < c then (1 : ℝ) else 0) else 0) := by
        apply Finset.sum_le_sum; intro a _
        split_ifs with hab
        · rw [Finset.mul_sum]; apply Finset.sum_le_sum; intro c _
          have hwk := Wk1_nonneg K (2 * (a + 1)) c
          by_cases h : S' (j + a + 1) (l + c)
          · rw [if_pos h]
            obtain ⟨_, _, h3⟩ := hS' _ _ h
            rcases h3 with h3 | h3
            · rw [if_pos (by omega : blk * Dmax < c)]; (first | linarith | nlinarith)
            · have hc : c = 0 := by omega
              subst hc
              rw [show 2 * (a + 1) = (2 * a + 1) + 1 by ring, Wk1_zero_col]; simp
          · rw [if_neg h, mul_zero]
            split_ifs <;> (first | linarith | nlinarith)
        · apply le_of_eq; apply Finset.sum_eq_zero; intro c _
          rw [if_neg (fun h => by have := hS' _ _ h; omega), mul_zero]
    _ = ∑ a ∈ (Finset.range r).filter (fun a => a < blk), W * ∑ c ∈ Finset.range (2 * K * (a + 1) + 1),
        Wk1 K (2 * (a + 1)) c * (if blk * Dmax < c then (1 : ℝ) else 0) := by
        rw [Finset.sum_filter]
    _ ≤ ∑ a ∈ Finset.range blk, W * ∑ c ∈ Finset.range (2 * K * (a + 1) + 1),
        Wk1 K (2 * (a + 1)) c * (if blk * Dmax < c then (1 : ℝ) else 0) :=
        Finset.sum_le_sum_of_subset_of_nonneg
          (fun a ha => by simp only [Finset.mem_filter, Finset.mem_range] at ha ⊢; omega)
          (fun a _ _ => mul_nonneg hW (hg0 a))
    _ = W * ∑ a ∈ Finset.range blk, ∑ c ∈ Finset.range (2 * K * (a + 1) + 1),
        Wk1 K (2 * (a + 1)) c * (if blk * Dmax < c then (1 : ℝ) else 0) := by rw [Finset.mul_sum]
    _ ≤ W * ρ := mul_le_mul_of_nonneg_left hρ hW

theorem claim_k (n K : ℕ) (ξ : ℤ) (ε : ℝ) (D : ℕ) (hε : 0 < ε) (hεD : ε * (2 ^ D + 9) < 1)
    (hD : ((D : ℝ) + 1) * (1 / 2) ^ D < 1) (hK : 2 ≤ K)
    (S : ℕ → ℕ → Prop) (N j0 J1 L0 L1 blk Dmax : ℕ) (W ρ : ℝ) (hW : 0 ≤ W) (hρ0 : 0 ≤ ρ)
    (hblk : 1 ≤ blk) (hJ1 : J1 ≤ N)
    (hρ : ∑ a ∈ Finset.range blk, ∑ c ∈ Finset.range (2 * K * (a + 1) + 1),
      Wk1 K (2 * (a + 1)) c * (if blk * Dmax < c then (1 : ℝ) else 0) ≤ ρ)
    (hbase : ∀ r j l, j + r = N → j0 < j → j ≤ J1 → ¬ S j l → Vk n K ξ ε S r j l ≤ W)
    (hprobe : ∀ j l, j0 < j → j ≤ J1 → L0 < l → l ≤ L1 → ¬ S j l → ¬ White n ξ ε (j + 1) (l + 3) →
      ∃ β, (2 : ℤ) ^ β ∣ Nz n ξ (j + 1) (l + 3) ∧ ¬ (2 : ℤ) ^ (β + 1) ∣ Nz n ξ (j + 1) (l + 3) ∧
        β / 2 + 3 ≤ blk) :
    ∀ k r j l, j + r = N → j0 < j → j + k * blk ≤ J1 → L0 < l → l + k * (blk * Dmax) ≤ L1 → ¬ S j l →
      Vk n K ξ ε S r j l ≤
        W * ((1 - (1 - Real.exp (-ε ^ 3)) / 4 * (1 - (D + 1) * (1 / 2) ^ D)) ^ k + (k : ℝ) * ρ) := by
  classical
  set η' : ℝ := (1 - Real.exp (-ε ^ 3)) / 4 * (1 - (D + 1) * (1 / 2) ^ D) with hη'
  have hex1 : Real.exp (-ε ^ 3) ≤ 1 := Real.exp_le_one_iff.2 (by have := pow_pos hε 3; linarith)
  have hex0 := Real.exp_pos (-ε ^ 3)
  have hδ0 : (0 : ℝ) ≤ (D + 1) * (1 / 2) ^ D := by positivity
  have hη'0 : 0 ≤ η' := by rw [hη']; apply mul_nonneg <;> linarith
  have hη'η : η' ≤ (1 - Real.exp (-ε ^ 3)) / 4 := by
    rw [hη']; have : 0 ≤ (1 - Real.exp (-ε ^ 3)) / 4 := by linarith
    (first | linarith | nlinarith)
  have hη'1 : η' ≤ 1 := by linarith
  intro k
  induction k with
  | zero =>
    intro r j l hN hj0 hJ _ _ hS
    rw [pow_zero, Nat.cast_zero, zero_mul, add_zero, mul_one]
    exact hbase r j l hN hj0 (by omega) hS
  | succ k ih =>
    intro r j l hN hj0 hJ hL0 hL1 hS
    have hk1 : (k + 1) * blk = k * blk + blk := Nat.succ_mul k blk
    have hk2 : (k + 1) * (blk * Dmax) = k * (blk * Dmax) + blk * Dmax := Nat.succ_mul k _
    set F : ℝ := W * ((1 - η') ^ k + (k : ℝ) * ρ) with hF
    have hF0 : 0 ≤ F := by
      rw [hF]; apply mul_nonneg hW
      have := pow_nonneg (by linarith : (0 : ℝ) ≤ 1 - η') k
      have := mul_nonneg (Nat.cast_nonneg k : (0 : ℝ) ≤ k) hρ0
      linarith
    obtain ⟨S', hS'⟩ : ∃ S' : ℕ → ℕ → Prop, ∀ j' l', S' j' l' ↔
        (j < j' ∧ j' ≤ j + blk ∧ (l + blk * Dmax < l' ∨ l' ≤ l)) :=
      ⟨fun j' l' => j < j' ∧ j' ≤ j + blk ∧ (l + blk * Dmax < l' ∨ l' ≤ l), fun _ _ => Iff.rfl⟩
    have href := Vk_refineN n K ξ ε hε.le S S' (fun _ _ => W) N (fun _ _ => hW) (by
      intro r' j' l' hN' hS'j hSj
      have := (hS' j' l').1 hS'j
      exact hbase r' j' l' hN' (by omega) (by omega) hSj) r j l hN
    have hvis := VisB_block K blk Dmax W ρ hW S' j l (fun j' l' h => (hS' j' l').1 h) hρ r
    have hFF : ∀ t l', 1 ≤ t → t ≤ blk → t ≤ r → ¬ (S (j + t) l' ∨ S' (j + t) l') →
        Vk n K ξ ε (fun j l => S j l ∨ S' j l) (r - t) (j + t) l' ≤ F := by
      intro t l' ht1 ht2 htr hn
      have hnS : ¬ S (j + t) l' := fun h => hn (Or.inl h)
      have hnS' : ¬ S' (j + t) l' := fun h => hn (Or.inr h)
      rw [hS'] at hnS'
      have hl1 : l < l' := by
        by_contra h; exact hnS' ⟨by omega, by omega, Or.inr (by omega)⟩
      have hl2 : l' ≤ l + blk * Dmax := by
        by_contra h; exact hnS' ⟨by omega, by omega, Or.inl (by omega)⟩
      refine (Vk_anti n K ξ ε S _ (fun j l h => Or.inl h) (r - t) (j + t) l').trans ?_
      exact ih (r - t) (j + t) l' (by omega) (by omega) (by omega) (by omega) (by omega) hnS
    have hmain : Vk n K ξ ε (fun j l => S j l ∨ S' j l) r j l ≤ F * (1 - η') := by
      by_cases hWt : White n ξ ε (j + 1) (l + 3)
      · obtain ⟨r', rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
        have hsw := step_white n K ξ ε hε.le hK j l hWt
          (fun b => if (S (j + 1) (l + b) ∨ S' (j + 1) (l + b)) then 0 else
            Vk n K ξ ε (fun j l => S j l ∨ S' j l) r' (j + 1) (l + b)) F
          (fun b => by
            split_ifs
            · exact le_rfl
            · exact Vk_nonneg n K ξ ε _ r' _ _)
          (fun b => by
            split_ifs with h
            · exact hF0
            · have := hFF 1 (l + b) le_rfl hblk (by omega) h
              rwa [Nat.add_sub_cancel] at this)
        refine le_trans (le_of_eq ?_) (hsw.trans (mul_le_mul_of_nonneg_left (by linarith) hF0))
        simp only [Vk]
        apply Finset.sum_congr rfl; intro u _
        by_cases h : S (j + 1) (l + ∑ i, u i) ∨ S' (j + 1) (l + ∑ i, u i)
        · rw [if_pos h, if_pos h]
        · rw [if_neg h, if_neg h]
      · obtain ⟨β, hβ1, hβ2, hβ3⟩ := hprobe j l hj0 (by omega) hL0 (by omega) hS hWt
        exact black_run_Vk n K ξ ε D hε hεD hK (fun j l => S j l ∨ S' j l) F hF0 β r j l (by omega) hWt
          hβ1 hβ2 (fun t l' ht1 ht2 hn => hFF t l' ht1 (by omega) (by omega) hn)
    have hfin : F * (1 - η') + W * ρ ≤ W * ((1 - η') ^ (k + 1) + ((k + 1 : ℕ) : ℝ) * ρ) := by
      rw [hF, pow_succ]; push_cast
      have h := mul_nonneg (mul_nonneg (mul_nonneg hW (Nat.cast_nonneg k : (0 : ℝ) ≤ k)) hρ0) hη'0
      (first | linarith [h] | nlinarith [h])
    linarith [href, hvis, hmain, hfin]


/-! ## W7a (session 33): diagonal kill comparison and the exit decomposition. -/

theorem Vt_le_killN (n K : ℕ) (ξ : ℤ) (ε : ℝ) (hε : 0 ≤ ε) (S : ℕ → ℕ → Prop) (B : ℕ → ℕ → ℝ) (N : ℕ)
    (hB0 : ∀ j l, 0 ≤ B j l) (hB : ∀ r j l, j + r = N → S j l → Vt n K ξ ε r j l ≤ B j l) :
    ∀ r j l, j + r = N → Vt n K ξ ε r j l ≤ Vk n K ξ ε S r j l + VisB K S B r j l := by
  classical
  intro r
  induction r with
  | zero => intro j l _; simp [Vt, Vk, VisB]
  | succ r ih =>
    intro j l hN
    simp only [Vt, Vk, VisB, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum; intro u _
    have hw : (0 : ℝ) ≤ ((1 : ℝ) / 2) ^ (∑ i, u i) := by positivity
    have hc0 := cf_nonneg n ξ ε (j + 1) (l + ∑ i, u i) (∑ i, u i)
    have hc1 := cf_le_one n ξ ε hε (j + 1) (l + ∑ i, u i) (∑ i, u i)
    have hwc : 0 ≤ ((1 : ℝ) / 2) ^ (∑ i, u i) * cf n ξ ε (j + 1) (l + ∑ i, u i) (∑ i, u i) :=
      mul_nonneg hw hc0
    have hvt := Vt_nonneg n K ξ ε r (j + 1) (l + ∑ i, u i)
    by_cases hS : S (j + 1) (l + ∑ i, u i)
    · rw [if_pos hS, if_pos hS, mul_zero, zero_add]
      have h1 := hB r (j + 1) (l + ∑ i, u i) (by omega) hS
      have h3 : cf n ξ ε (j + 1) (l + ∑ i, u i) (∑ i, u i) * Vt n K ξ ε r (j + 1) (l + ∑ i, u i) ≤
          B (j + 1) (l + ∑ i, u i) := by (first | linarith | nlinarith)
      (first | linarith [mul_le_mul_of_nonneg_left h3 hw] | nlinarith [mul_le_mul_of_nonneg_left h3 hw])
    · rw [if_neg hS, if_neg hS]
      have h1 := ih (j + 1) (l + ∑ i, u i) (by omega)
      have hv := VisB_nonneg K S B hB0 r (j + 1) (l + ∑ i, u i)
      have h3 : cf n ξ ε (j + 1) (l + ∑ i, u i) (∑ i, u i) * VisB K S B r (j + 1) (l + ∑ i, u i) ≤
          VisB K S B r (j + 1) (l + ∑ i, u i) := by (first | linarith | nlinarith)
      (first | linarith [mul_le_mul_of_nonneg_left h1 hwc, mul_le_mul_of_nonneg_left h3 hw] | nlinarith [mul_le_mul_of_nonneg_left h1 hwc, mul_le_mul_of_nonneg_left h3 hw])

lemma VisB_const_le (K : ℕ) (S : ℕ → ℕ → Prop) (c : ℝ) (hc : 0 ≤ c) :
    ∀ r j l, VisB K S (fun _ _ => c) r j l ≤ c := by
  classical
  intro r
  induction r with
  | zero => intro j l; simp [VisB, hc]
  | succ r ih =>
    intro j l
    simp only [VisB]
    calc _ ≤ ∑ u ∈ Box 2 K, ((1 : ℝ) / 2) ^ (∑ i, u i) * c := by
          apply Finset.sum_le_sum; intro u _
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          split_ifs
          · exact le_rfl
          · exact ih _ _
      _ = (∑ u ∈ Box 2 K, ((1 : ℝ) / 2) ^ (∑ i, u i)) * c := by rw [Finset.sum_mul]
      _ ≤ 1 * c := mul_le_mul_of_nonneg_right (box_mass_le 2 K) hc
      _ = c := one_mul c

lemma VisB_row_cut (K : ℕ) (S : ℕ → ℕ → Prop) (B : ℕ → ℕ → ℝ) (j0 J : ℕ) (hrow : ∀ l', S J l') :
    ∀ r j l, j0 ≤ j → j < J →
      VisB K S B r j l = VisB K S (fun j' l' => if j0 < j' ∧ j' ≤ J then B j' l' else 0) r j l := by
  classical
  intro r
  induction r with
  | zero => intro j l _ _; simp [VisB]
  | succ r ih =>
    intro j l h0 hJ
    simp only [VisB]
    apply Finset.sum_congr rfl; intro u _
    congr 1
    by_cases hS : S (j + 1) (l + ∑ i, u i)
    · rw [if_pos hS, if_pos hS, if_pos (by omega : j0 < j + 1 ∧ j + 1 ≤ J)]
    · rw [if_neg hS, if_neg hS]
      have hJ' : j + 1 < J := by
        rcases Nat.lt_or_ge (j + 1) J with h | h
        · exact h
        · exfalso
          have he : j + 1 = J := by omega
          exact hS (by rw [he]; exact hrow _)
      exact ih (j + 1) _ (by omega) hJ'

lemma VisB_rowJ (K : ℕ) (S' : ℕ → ℕ → Prop) (L0 j l as r : ℕ) (W : ℝ) (hW : 0 ≤ W) (has1 : 1 ≤ as)
    (hasr : as ≤ r) (hl : l ≤ L0) (hS : ∀ j' l', S' j' l' → l' ≤ L0 → j' = j + as) :
    VisB K S' (fun _ l' => if l' ≤ L0 then W else 0) r j l ≤
      W * ∑ c ∈ Finset.range (L0 - l + 1), Wk1 K (2 * as) c := by
  classical
  refine (VisB_le K S' _ (fun _ l' => by split_ifs <;> linarith) r j l).trans ?_
  have hX0 : 0 ≤ W * ∑ c ∈ Finset.range (L0 - l + 1), Wk1 K (2 * as) c :=
    mul_nonneg hW (Finset.sum_nonneg (fun c _ => Wk1_nonneg K _ c))
  calc _ ≤ ∑ a ∈ Finset.range r,
        (if a + 1 = as then W * ∑ c ∈ Finset.range (L0 - l + 1), Wk1 K (2 * as) c else 0) := by
        apply Finset.sum_le_sum; intro a _
        split_ifs with ha
        · subst ha
          rw [Finset.mul_sum]
          calc _ ≤ ∑ c ∈ Finset.range (2 * K * (a + 1) + 1),
                (if c ≤ L0 - l then W * Wk1 K (2 * (a + 1)) c else 0) := by
                apply Finset.sum_le_sum; intro c _
                have hwk := Wk1_nonneg K (2 * (a + 1)) c
                split_ifs <;> first | nlinarith | (exfalso; omega)
            _ = ∑ c ∈ (Finset.range (2 * K * (a + 1) + 1)).filter (fun c => c ≤ L0 - l),
                W * Wk1 K (2 * (a + 1)) c := by rw [Finset.sum_filter]
            _ ≤ ∑ c ∈ Finset.range (L0 - l + 1), W * Wk1 K (2 * (a + 1)) c :=
                Finset.sum_le_sum_of_subset_of_nonneg
                  (fun c hc => by simp only [Finset.mem_filter, Finset.mem_range] at hc ⊢; omega)
                  (fun c _ _ => mul_nonneg hW (Wk1_nonneg K _ c))
        · apply le_of_eq; apply Finset.sum_eq_zero; intro c _
          split_ifs with h1 h2
          · exact absurd (hS _ _ h1 h2) (by omega)
          · simp
          · simp
    _ = W * ∑ c ∈ Finset.range (L0 - l + 1), Wk1 K (2 * as) c := by
        rw [Finset.sum_eq_single (as - 1) (fun b _ hb => if_neg (by omega))
          (fun h => absurd (Finset.mem_range.2 (by omega)) h)]
        rw [if_pos (by omega)]

theorem exit_W7a (n K : ℕ) (ξ : ℤ) (ε : ℝ) (hε : 0 ≤ ε) (S : ℕ → ℕ → Prop) (N j l r L0 E as : ℕ)
    (W Q : ℝ) (hW : 0 ≤ W) (hQ : 0 ≤ Q) (hN : j + r = N) (hl : l ≤ L0) (has1 : 1 ≤ as) (hasr : as ≤ r)
    (hbase : ∀ r' j' l', j' + r' = N → j < j' → j' ≤ j + as → ¬ S j' l' → Vk n K ξ ε S r' j' l' ≤ W)
    (hclaim : ∀ r' j' l', j' + r' = N → j < j' → j' ≤ j + as → L0 < l' → l' ≤ L0 + E → ¬ S j' l' →
      Vk n K ξ ε S r' j' l' ≤ W * Q) :
    Vk n K ξ ε S r j l ≤ W * Q + W * (((E : ℝ) + 1) * (1 / 2) ^ E) +
      W * ∑ c ∈ Finset.range (L0 - l + 1), Wk1 K (2 * as) c := by
  classical
  obtain ⟨S', hS'eq⟩ : ∃ S' : ℕ → ℕ → Prop, S' = fun j' l' => L0 < l' ∨ j' = j + as := ⟨_, rfl⟩
  obtain ⟨B, hBe⟩ : ∃ B : ℕ → ℕ → ℝ, ∀ j' l', B j' l' = if j < j' ∧ j' ≤ j + as then
      W * Q + (W * (if L0 + E < l' then (1 : ℝ) else 0) + (if l' ≤ L0 then W else 0)) else 1 :=
    ⟨_, fun _ _ => rfl⟩
  have hWQ := mul_nonneg hW hQ
  have hB0 : ∀ j' l', 0 ≤ B j' l' := by
    intro j' l'; rw [hBe]; split_ifs <;> (first | linarith | nlinarith)
  have href := Vk_refineN n K ξ ε hε S S' B N hB0 (by
    intro r' j' l' hN' _ hnS
    rw [hBe]
    by_cases hg : j < j' ∧ j' ≤ j + as
    · rw [if_pos hg]
      by_cases hA : L0 < l' ∧ l' ≤ L0 + E
      · have := hclaim r' j' l' hN' hg.1 hg.2 hA.1 hA.2 hnS
        rw [if_neg (by omega : ¬ L0 + E < l'), if_neg (by omega : ¬ l' ≤ L0)]
        linarith
      · have := hbase r' j' l' hN' hg.1 hg.2 hnS
        by_cases h1 : L0 + E < l'
        · rw [if_pos h1, if_neg (by omega : ¬ l' ≤ L0)]; (first | linarith | nlinarith)
        · rw [if_neg h1, if_pos (by omega : l' ≤ L0)]; (first | linarith | nlinarith)
    · rw [if_neg hg]
      exact (Vk_le_Vt n K ξ ε S r' j' l').trans (Vt_le_one n K ξ ε hε r' j' l')) r j l hN
  have hkill : Vk n K ξ ε (fun j l => S j l ∨ S' j l) r j l = 0 :=
    Vk_row_kill n K ξ ε (fun j l => S j l ∨ S' j l) (j + as)
      (fun l' => Or.inr (by rw [hS'eq]; exact Or.inr rfl)) r j l (by omega) (by omega)
  have hcut := VisB_row_cut K S' B j (j + as) (fun l' => by rw [hS'eq]; exact Or.inr rfl) r j l le_rfl
    (by omega)
  have hmono := VisB_mono K S' (fun j' l' => if j < j' ∧ j' ≤ j + as then B j' l' else 0)
    (fun j' l' => W * Q + (W * (if L0 + E < l' then (1 : ℝ) else 0) + (if l' ≤ L0 then W else 0)))
    (by
      intro j' l'
      by_cases hg : j < j' ∧ j' ≤ j + as
      · rw [if_pos hg, hBe, if_pos hg]
      · rw [if_neg hg]; split_ifs <;> nlinarith) r j l
  have hadd1 := VisB_add K S' (fun _ _ => W * Q)
    (fun _ l' => W * (if L0 + E < l' then (1 : ℝ) else 0) + (if l' ≤ L0 then W else 0)) r j l
  have hadd2 := VisB_add K S' (fun _ l' => W * (if L0 + E < l' then (1 : ℝ) else 0))
    (fun _ l' => if l' ≤ L0 then W else 0) r j l
  have h5 := VisB_const_le K S' (W * Q) hWQ r j l
  have h6 : VisB K S' (fun _ l' => W * (if L0 + E < l' then (1 : ℝ) else 0)) r j l ≤
      W * (((E : ℝ) + 1) * (1 / 2) ^ E) := by
    calc _ ≤ VisB K (fun _ l' => L0 < l') (fun _ l' => W * (if L0 + E < l' then (1 : ℝ) else 0)) r j l := by
          rw [hS'eq]
          exact VisB_drop K (fun _ l' => L0 < l') (fun j' _ => j' = j + as)
            (fun _ l' => W * (if L0 + E < l' then (1 : ℝ) else 0))
            (fun _ l' => by split_ifs <;> nlinarith)
            (fun j' l' _ h => by
              show W * (if L0 + E < l' then (1 : ℝ) else 0) = 0
              rw [if_neg (by omega), mul_zero]) r j l
      _ = W * VisB K (fun _ l' => L0 < l') (fun _ l' => if L0 + E < l' then (1 : ℝ) else 0) r j l :=
          VisB_smul K _ W _ r j l
      _ ≤ W * (((E : ℝ) + 1) * (1 / 2) ^ E) :=
          mul_le_mul_of_nonneg_left (overshoot K L0 E r j l hl) hW
  have h7 := VisB_rowJ K S' L0 j l as r W hW has1 hasr hl (fun j' l' h hl' => by
    rw [hS'eq] at h
    rcases h with h | h
    · omega
    · exact h)
  linarith [href, hkill, hcut, hmono, hadd1, hadd2, h5, h6, h7]


/-! W7c (session 34): the bad-probe kill set and its link to `W4_arith`. `Sbad` = post-exit window
positions (rows `j < j' ≤ j + as`, columns `l + β < l' ≤ l + β + E`) whose probe is black with 2-adic
budget at least `B0`. -/
def Sbad (n : ℕ) (ξ : ℤ) (ε : ℝ) (j l β as E B0 : ℕ) (j' l' : ℕ) : Prop :=
  j < j' ∧ j' ≤ j + as ∧ l + β < l' ∧ l' ≤ l + β + E ∧ ¬ White n ξ ε (j' + 1) (l' + 3) ∧
    (2 : ℤ) ^ B0 ∣ Nz n ξ (j' + 1) (l' + 3)

lemma nine_le_two_pow (a β : ℕ) (h : 10 * a ≤ 3 * β) : 9 ^ a ≤ 2 ^ β := by
  by_contra hlt; push_neg at hlt
  have h3 := Nat.pow_lt_pow_left hlt (by norm_num : (3 : ℕ) ≠ 0)
  have e1 : (9 ^ a) ^ 3 = 729 ^ a := by rw [pow_right_comm]; norm_num
  have e2 : (2 ^ β) ^ 3 = 2 ^ (3 * β) := by rw [← pow_mul, mul_comm]
  have h4 : 729 ^ a ≤ 1024 ^ a := Nat.pow_le_pow_left (by norm_num) _
  have h5 : 1024 ^ a = 2 ^ (10 * a) := by rw [pow_mul]; norm_num
  have h6 : 2 ^ (10 * a) ≤ 2 ^ (3 * β) := Nat.pow_le_pow_right (by norm_num) h
  have h7 : 729 ^ a ≤ 2 ^ (3 * β) := h4.trans (h5.le.trans h6)
  rw [e1, e2] at h3
  exact absurd h3 (not_lt.2 h7)

lemma Sbad_facts (n : ℕ) (ξ : ℤ) (ε : ℝ) (hε : 0 < ε) (hε2 : ε < 1 / 2) (j l β as E B0 : ℕ) (m : ℤ)
    (has : 10 * as ≤ 3 * β) (hX : Nz n ξ (j + 1) (l + 3) = 2 ^ β * m) (a c : ℕ)
    (h : Sbad n ξ ε j l β as E B0 (j + a + 1) (l + c)) :
    β < c ∧ c ≤ β + E ∧ (9 : ℝ) ^ (a + 1) * |(m : ℝ)| ≤ 3 ^ n ∧
      ∃ Y : ℤ, (3 : ℤ) ^ n ∣ 2 ^ c * Y - 9 ^ (a + 1) * Nz n ξ (j + 1) (l + 3) ∧
        |(Y : ℝ)| ≤ ε * 3 ^ n ∧ (2 : ℤ) ^ B0 ∣ Y := by
  obtain ⟨h1, h2, h3, h4, hW, hB⟩ := h
  refine ⟨by omega, by omega, ?_, Nz n ξ (j + a + 1 + 1) (l + c + 3), ?_, ?_, hB⟩
  · have h9n : 9 ^ (a + 1) ≤ 2 ^ β := nine_le_two_pow (a + 1) β (by omega)
    have h9r : (9 : ℝ) ^ (a + 1) ≤ 2 ^ β := by exact_mod_cast h9n
    have hz : |Nz n ξ (j + 1) (l + 3)| = 2 ^ β * |m| := by
      rw [hX, abs_mul, abs_of_pos (by positivity : (0 : ℤ) < 2 ^ β)]
    have hz2 : (2 : ℤ) ^ β * |m| ≤ 3 ^ n := by
      have := Nz_abs_le n ξ (j + 1) (l + 3)
      have := abs_nonneg (Nz n ξ (j + 1) (l + 3))
      rw [← hz]; linarith
    have hz3 : (2 : ℝ) ^ β * |(m : ℝ)| ≤ 3 ^ n := by exact_mod_cast hz2
    exact (mul_le_mul_of_nonneg_right h9r (abs_nonneg _)).trans hz3
  · have := Nz_shift_dvd n ξ (j + 1) (l + 3) (a + 1) c (by omega) (by omega)
    have e1 : j + 1 + (a + 1) = j + a + 1 + 1 := by omega
    have e2 : l + 3 + c = l + c + 3 := by omega
    rwa [e1, e2] at this
  · have := (white_iff n ξ ε hε hε2 _ _).not.1 hW
    push_neg at this
    exact this


lemma exact_budget_lt (X : ℤ) (B0 : ℕ) (h : ¬ (2 : ℤ) ^ B0 ∣ X) :
    ∃ b : ℕ, (2 : ℤ) ^ b ∣ X ∧ ¬ (2 : ℤ) ^ (b + 1) ∣ X ∧ b < B0 := by
  classical
  have hB0 : 1 ≤ B0 := by
    by_contra h0; push_neg at h0
    interval_cases B0; exact h (by simp)
  have hex : ∃ b, ¬ (2 : ℤ) ^ (b + 1) ∣ X := ⟨B0 - 1, by rwa [Nat.sub_add_cancel hB0]⟩
  refine ⟨Nat.find hex, ?_, Nat.find_spec hex, ?_⟩
  · rcases Nat.eq_zero_or_pos (Nat.find hex) with h0 | hpos
    · rw [h0]; simp
    · have hmin := Nat.find_min hex (show Nat.find hex - 1 < Nat.find hex by omega)
      push_neg at hmin
      rwa [Nat.sub_add_cancel hpos] at hmin
  · have := Nat.find_min' hex (show ¬ (2 : ℤ) ^ (B0 - 1 + 1) ∣ X by rwa [Nat.sub_add_cancel hB0])
    omega

lemma hprobe_Sbad (n : ℕ) (ξ : ℤ) (ε : ℝ) (j l β as E B0 blk : ℕ) (hblk : B0 / 2 + 3 ≤ blk)
    (S : ℕ → ℕ → Prop) (hS : ∀ j' l', Sbad n ξ ε j l β as E B0 j' l' → S j' l') :
    ∀ j' l', j < j' → j' ≤ j + as → l + β < l' → l' ≤ l + β + E → ¬ S j' l' →
      ¬ White n ξ ε (j' + 1) (l' + 3) →
      ∃ b, (2 : ℤ) ^ b ∣ Nz n ξ (j' + 1) (l' + 3) ∧ ¬ (2 : ℤ) ^ (b + 1) ∣ Nz n ξ (j' + 1) (l' + 3) ∧
        b / 2 + 3 ≤ blk := by
  intro j' l' h1 h2 h3 h4 hnS hW
  have hnd : ¬ (2 : ℤ) ^ B0 ∣ Nz n ξ (j' + 1) (l' + 3) := fun hd => hnS (hS _ _ ⟨h1, h2, h3, h4, hW, hd⟩)
  obtain ⟨b, hb1, hb2, hb3⟩ := exact_budget_lt _ _ hnd
  exact ⟨b, hb1, hb2, by omega⟩

/-! ## merged from _s8i_rho (session 35) -/

lemma centralBinom_sq_le (N : ℕ) : (Nat.centralBinom N) ^ 2 * (N + 1) ≤ 16 ^ N := by
  induction N with
  | zero => simp
  | succ N ih =>
    have hrec := Nat.succ_mul_centralBinom_succ N
    have key : 4 * (2 * N + 1) ^ 2 * (N + 2) ≤ 16 * (N + 1) ^ 3 := by (first | linarith | nlinarith)
    have hpos : 0 < (N + 1) ^ 2 := by positivity
    apply Nat.le_of_mul_le_mul_left _ hpos
    calc (N + 1) ^ 2 * (Nat.centralBinom (N + 1) ^ 2 * (N + 1 + 1))
        = ((N + 1) * Nat.centralBinom (N + 1)) ^ 2 * (N + 2) := by ring
      _ = 4 * (2 * N + 1) ^ 2 * (N + 2) * Nat.centralBinom N ^ 2 := by rw [hrec]; ring
      _ ≤ 16 * (N + 1) ^ 3 * Nat.centralBinom N ^ 2 := Nat.mul_le_mul_right _ key
      _ = 16 * (N + 1) ^ 2 * (Nat.centralBinom N ^ 2 * (N + 1)) := by ring
      _ ≤ 16 * (N + 1) ^ 2 * 16 ^ N := Nat.mul_le_mul_left _ ih
      _ = (N + 1) ^ 2 * 16 ^ (N + 1) := by ring

lemma nine_order (m d : ℕ) (hd : d ≠ 0) (h : 2 ^ m ∣ 9 ^ d - 1) : 2 ^ (m - 3) ∣ d := by
  have h1 := @padicValNat.pow_two_sub_pow 3 1 (by norm_num) (by norm_num) (by norm_num) (2 * d)
    (by omega) (even_two_mul d)
  have e1 : 3 ^ (2 * d) - 1 ^ (2 * d) = 9 ^ d - 1 := by rw [one_pow, pow_mul]; norm_num
  have e2 : padicValNat 2 (3 + 1) = 2 := by
    have : (3 + 1 : ℕ) = 2 ^ 2 := by norm_num
    rw [this, padicValNat.prime_pow]
  have e3 : padicValNat 2 (3 - 1) = 1 := by
    have : (3 - 1 : ℕ) = 2 := by norm_num
    rw [this, padicValNat_self]
  have e4 : padicValNat 2 (2 * d) = 1 + padicValNat 2 d := by
    rw [padicValNat.mul (by norm_num) hd, padicValNat_self]
  rw [e1, e2, e3, e4] at h1
  have hne : 9 ^ d - 1 ≠ 0 := by
    have : 1 < 9 ^ d := Nat.one_lt_pow hd (by norm_num)
    omega
  have hm := (padicValNat_dvd_iff_le hne).1 h
  exact (padicValNat_dvd_iff_le hd).2 (by omega)


/-! Session 30: Lemma 7.10 arithmetic (relation + residue class) and the unimodal AP-sum bound. -/

lemma l710_rel (n a c β : ℕ) (X Y m : ℤ) (hd : (3 : ℤ) ^ n ∣ 2 ^ c * Y - 9 ^ a * X)
    (hX : X = 2 ^ β * m) (hc : β ≤ c) :
    ∃ k : ℤ, 2 ^ (c - β) * Y = 9 ^ a * m + k * 3 ^ n := by
  obtain ⟨q, hq⟩ := hd
  have e : (2 : ℤ) ^ c = 2 ^ β * 2 ^ (c - β) := by rw [← pow_add]; congr 1; omega
  have h2 : (2 : ℤ) ^ β ∣ 3 ^ n * q := by
    rw [← hq, hX, e]
    exact dvd_sub ⟨2 ^ (c - β) * Y, by ring⟩ ⟨9 ^ a * m, by ring⟩
  have hcop : IsCoprime ((2 : ℤ) ^ β) ((3 : ℤ) ^ n) :=
    (Int.isCoprime_iff_gcd_eq_one.mpr (by norm_num) : IsCoprime (2 : ℤ) 3).pow
  obtain ⟨k, hk⟩ := hcop.dvd_of_dvd_mul_left h2
  refine ⟨k, ?_⟩
  have hpos : (2 : ℤ) ^ β ≠ 0 := by positivity
  apply mul_left_cancel₀ hpos
  rw [hX, e, hk] at hq
  linear_combination hq

lemma same_class (n t a1 a2 : ℕ) (m k : ℤ) (hm : ¬ (2 : ℤ) ∣ m) (h12 : a1 ≤ a2)
    (h1 : (2 : ℤ) ^ t ∣ 9 ^ a1 * m + k * 3 ^ n) (h2 : (2 : ℤ) ^ t ∣ 9 ^ a2 * m + k * 3 ^ n) :
    2 ^ (t - 3) ∣ a2 - a1 := by
  by_cases hd : a2 - a1 = 0
  · rw [hd]; exact dvd_zero _
  have hsub : (2 : ℤ) ^ t ∣ 9 ^ a1 * (m * (9 ^ (a2 - a1) - 1)) := by
    have h := dvd_sub h2 h1
    have e9 : (9 : ℤ) ^ a2 = 9 ^ a1 * 9 ^ (a2 - a1) := by rw [← pow_add]; congr 1; omega
    have e : 9 ^ a2 * m + k * 3 ^ n - (9 ^ a1 * m + k * 3 ^ n) =
        9 ^ a1 * (m * (9 ^ (a2 - a1) - 1)) := by rw [e9]; ring
    rwa [e] at h
  have c9 : IsCoprime ((2 : ℤ) ^ t) (9 ^ a1) :=
    (Int.isCoprime_iff_gcd_eq_one.mpr (by norm_num) : IsCoprime (2 : ℤ) 9).pow
  have cm : IsCoprime ((2 : ℤ) ^ t) m :=
    IsCoprime.pow_left ((Irreducible.coprime_iff_not_dvd Int.prime_two.irreducible).2 hm)
  have h3 : (2 : ℤ) ^ t ∣ 9 ^ (a2 - a1) - 1 := cm.dvd_of_dvd_mul_left (c9.dvd_of_dvd_mul_left hsub)
  have hcast : ((9 ^ (a2 - a1) - 1 : ℕ) : ℤ) = 9 ^ (a2 - a1) - 1 := by
    have : 1 ≤ 9 ^ (a2 - a1) := Nat.one_le_pow _ _ (by norm_num)
    push_cast [Nat.cast_sub this]; ring
  rw [← hcast, show (2 : ℤ) ^ t = ((2 ^ t : ℕ) : ℤ) by push_cast; ring] at h3
  exact nine_order t (a2 - a1) hd (Int.natCast_dvd_natCast.mp h3)

lemma mul_add_inj (m a a' s s' : ℕ) (hs : s < m) (hs' : s' < m) (h : m * a + s = m * a' + s') :
    a = a' ∧ s = s' := by
  have hm : 0 < m := by omega
  have h1 : (m * a + s) / m = a := by
    rw [Nat.mul_comm, Nat.add_comm, Nat.add_mul_div_right _ _ hm, Nat.div_eq_of_lt hs, zero_add]
  have h2 : (m * a' + s') / m = a' := by
    rw [Nat.mul_comm, Nat.add_comm, Nat.add_mul_div_right _ _ hm, Nat.div_eq_of_lt hs', zero_add]
  have ha : a = a' := by rw [← h1, ← h2, h]
  subst ha
  exact ⟨rfl, by omega⟩

lemma ap_unimodal (f : ℕ → ℝ) (hf0 : ∀ i, 0 ≤ f i) (p : ℕ)
    (hup : ∀ i j, i ≤ j → j ≤ p → f i ≤ f j) (hdn : ∀ i j, p ≤ i → i ≤ j → f j ≤ f i)
    (F : ℝ) (hF : ∀ i, f i ≤ F) (m i0 T : ℕ) (hm : 1 ≤ m) :
    (m : ℝ) * ∑ t ∈ Finset.range T, f (i0 + m * t) ≤
      ∑ i ∈ Finset.range (i0 + m * T), f i + 3 * m * F := by
  classical
  set N := i0 + m * T with hN
  set PA : ℕ → Prop := fun t => i0 + m * (t + 1) ≤ p with hPA
  set PB : ℕ → Prop := fun t => 1 ≤ t ∧ p ≤ i0 + m * (t - 1) with hPB
  have hmT : ∀ t, t < T → m * (t + 1) ≤ m * T := fun t ht => Nat.mul_le_mul_left _ (by omega)
  -- part A: increasing side
  have hA : (m : ℝ) * ∑ t ∈ (Finset.range T).filter PA, f (i0 + m * t) ≤
      ∑ i ∈ (Finset.range N).filter (fun i => i < p), f i := by
    rw [Finset.mul_sum]
    calc ∑ t ∈ (Finset.range T).filter PA, (m : ℝ) * f (i0 + m * t)
        ≤ ∑ t ∈ (Finset.range T).filter PA, ∑ s ∈ Finset.range m, f (i0 + m * t + s) := by
          apply Finset.sum_le_sum
          intro t ht
          simp only [Finset.mem_filter, Finset.mem_range, hPA] at ht
          have : ∑ s ∈ Finset.range m, f (i0 + m * t) ≤ ∑ s ∈ Finset.range m, f (i0 + m * t + s) := by
            apply Finset.sum_le_sum
            intro s hs
            simp only [Finset.mem_range] at hs
            apply hup _ _ (by omega)
            have : m * (t + 1) = m * t + m := by ring
            omega
          simpa using this
      _ = ∑ x ∈ (Finset.range T).filter PA ×ˢ Finset.range m, f (i0 + m * x.1 + x.2) := by
          rw [Finset.sum_product]
      _ = ∑ i ∈ ((Finset.range T).filter PA ×ˢ Finset.range m).image
            (fun x => i0 + m * x.1 + x.2), f i := by
          rw [Finset.sum_image]
          intro x hx y hy hxy
          simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe, Finset.mem_range,
            Finset.mem_product] at hx hy
          have h' : m * x.1 + x.2 = m * y.1 + y.2 := by simp only at hxy; omega
          obtain ⟨e1, e2⟩ := mul_add_inj m _ _ _ _ hx.2 hy.2 h'
          exact Prod.ext e1 e2
      _ ≤ _ := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro i hi
            simp only [Finset.mem_image, Finset.mem_product, Finset.mem_filter, Finset.mem_range,
              hPA] at hi
            obtain ⟨⟨t, s⟩, ⟨⟨ht, hp⟩, hs⟩, rfl⟩ := hi
            dsimp only at hp ⊢
            simp only [Finset.mem_filter, Finset.mem_range]
            have e : m * (t + 1) = m * t + m := by ring
            have := hmT t ht
            constructor <;> omega
          · intro i _ _; exact hf0 i
  -- part B: decreasing side
  have hB : (m : ℝ) * ∑ t ∈ ((Finset.range T).filter (fun t => ¬ PA t)).filter PB, f (i0 + m * t) ≤
      ∑ i ∈ (Finset.range N).filter (fun i => ¬ i < p), f i := by
    rw [Finset.mul_sum]
    calc ∑ t ∈ ((Finset.range T).filter (fun t => ¬ PA t)).filter PB, (m : ℝ) * f (i0 + m * t)
        ≤ ∑ t ∈ ((Finset.range T).filter (fun t => ¬ PA t)).filter PB,
            ∑ s ∈ Finset.range m, f (i0 + m * (t - 1) + (s + 1)) := by
          apply Finset.sum_le_sum
          intro t ht
          simp only [Finset.mem_filter, Finset.mem_range, hPB] at ht
          have : ∑ s ∈ Finset.range m, f (i0 + m * t) ≤
              ∑ s ∈ Finset.range m, f (i0 + m * (t - 1) + (s + 1)) := by
            apply Finset.sum_le_sum
            intro s hs
            simp only [Finset.mem_range] at hs
            apply hdn _ _ (by omega)
            have : m * t = m * (t - 1) + m := by
              obtain ⟨u, rfl⟩ : ∃ u, t = u + 1 := ⟨t - 1, by omega⟩
              simp only [Nat.add_sub_cancel]; ring
            omega
          simpa using this
      _ = ∑ x ∈ ((Finset.range T).filter (fun t => ¬ PA t)).filter PB ×ˢ Finset.range m,
            f (i0 + m * (x.1 - 1) + (x.2 + 1)) := by
          rw [Finset.sum_product]
      _ = ∑ i ∈ (((Finset.range T).filter (fun t => ¬ PA t)).filter PB ×ˢ Finset.range m).image
            (fun x => i0 + m * (x.1 - 1) + (x.2 + 1)), f i := by
          rw [Finset.sum_image]
          intro x hx y hy hxy
          simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe, Finset.mem_range,
            Finset.mem_product, Finset.mem_filter, hPB] at hx hy
          have h' : m * (x.1 - 1) + x.2 = m * (y.1 - 1) + y.2 := by simp only at hxy; omega
          obtain ⟨e1, e2⟩ := mul_add_inj m _ _ _ _ hx.2 hy.2 h'
          exact Prod.ext (by omega) e2
      _ ≤ _ := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro i hi
            simp only [Finset.mem_image, Finset.mem_product, Finset.mem_filter, Finset.mem_range,
              hPB] at hi
            obtain ⟨⟨t, s⟩, ⟨⟨⟨ht, _⟩, ht1, hp⟩, hs⟩, rfl⟩ := hi
            dsimp only at hp ht1 ⊢
            simp only [Finset.mem_filter, Finset.mem_range]
            have e : m * t = m * (t - 1) + m := by
              obtain ⟨u, rfl⟩ : ∃ u, t = u + 1 := ⟨t - 1, by omega⟩
              simp only [Nat.add_sub_cancel]; ring
            have := hmT t ht
            have e2 : m * (t + 1) = m * t + m := by ring
            constructor <;> omega
          · intro i _ _; exact hf0 i
  -- part C: at most three exceptional terms
  have hC : (m : ℝ) * ∑ t ∈ ((Finset.range T).filter (fun t => ¬ PA t)).filter (fun t => ¬ PB t),
      f (i0 + m * t) ≤ 3 * m * F := by
    set q := (p - i0) / m with hq
    have hsub : ((Finset.range T).filter (fun t => ¬ PA t)).filter (fun t => ¬ PB t) ⊆ {0, q, q + 1} := by
      intro t ht
      simp only [Finset.mem_filter, Finset.mem_range, hPA, hPB, not_and, not_le] at ht
      simp only [Finset.mem_insert, Finset.mem_singleton]
      by_cases h0 : t = 0
      · left; exact h0
      right
      have h1 := ht.2 (by omega)
      have h2 := ht.1.2
      have hm0 : 0 < m := by omega
      have hq1 : m * q ≤ p - i0 := by rw [hq]; exact Nat.mul_div_le _ _
      have hq2 : p - i0 < m * (q + 1) := by
        rw [hq]; exact Nat.lt_mul_div_succ _ hm0
      have a1 : m * (t - 1) < m * (q + 1) := by omega
      have a2 : m * q < m * (t + 1) := by omega
      have b1 := Nat.lt_of_mul_lt_mul_left a1
      have b2 := Nat.lt_of_mul_lt_mul_left a2
      omega
    have hs1 : ∑ t ∈ ((Finset.range T).filter (fun t => ¬ PA t)).filter (fun t => ¬ PB t),
        f (i0 + m * t) ≤ ∑ t ∈ ({0, q, q + 1} : Finset ℕ), f (i0 + m * t) :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun i _ _ => hf0 _)
    have hs2 : ∑ t ∈ ({0, q, q + 1} : Finset ℕ), f (i0 + m * t) ≤
        ({0, q, q + 1} : Finset ℕ).card • F := Finset.sum_le_card_nsmul _ _ F (fun t _ => hF _)
    have hc3 : (({0, q, q + 1} : Finset ℕ).card : ℝ) ≤ 3 := by exact_mod_cast Finset.card_le_three
    rw [nsmul_eq_mul] at hs2
    have hF0 : 0 ≤ F := (hf0 0).trans (hF 0)
    have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    have : (({0, q, q + 1} : Finset ℕ).card : ℝ) * F ≤ 3 * F := mul_le_mul_of_nonneg_right hc3 hF0
    (first | linarith | nlinarith)
  have s1 := Finset.sum_filter_add_sum_filter_not (Finset.range T) PA (fun t => f (i0 + m * t))
  have s2 := Finset.sum_filter_add_sum_filter_not ((Finset.range T).filter (fun t => ¬ PA t)) PB
    (fun t => f (i0 + m * t))
  have s3 := Finset.sum_filter_add_sum_filter_not (Finset.range N) (fun i => i < p) f
  rw [← s1, ← s2, ← s3, mul_add, mul_add]
  linarith

/-! W1: the walk measure (single geometric steps) and its binomial majorant. -/

lemma Wk1_zero (K s : ℕ) : Wk1 K (s + 1) 0 = 0 := by
  rw [Wk1_succ]
  apply Finset.sum_eq_zero
  intro u hu
  simp only [Finset.mem_Icc] at hu
  rw [if_neg (by omega), mul_zero]

lemma sum_range_choose' (c s : ℕ) :
    ∑ i ∈ Finset.range c, (i.choose s : ℝ) = (c.choose (s + 1) : ℝ) := by
  induction c with
  | zero => simp
  | succ c ih =>
    rw [Finset.sum_range_succ, ih, Nat.choose_succ_succ' c s]
    push_cast; ring

lemma sum_Icc_reflect_choose (c s : ℕ) :
    ∑ u ∈ Finset.Icc 1 c, ((c - u).choose s : ℝ) = (c.choose (s + 1) : ℝ) := by
  have hI : Finset.Icc 1 c = Finset.Ico 1 (c + 1) := by ext x; simp only [Finset.mem_Icc, Finset.mem_Ico]; omega
  rw [← sum_range_choose' c s, hI,
    Finset.sum_Ico_reflect (fun i => (i.choose s : ℝ)) 1 (le_refl (c + 1)), Finset.range_eq_Ico]
  simp

lemma Wk1_le (K : ℕ) : ∀ s c, Wk1 K (s + 1) (c + 1) ≤ (c.choose s : ℝ) * ((1 : ℝ) / 2) ^ (c + 1) := by
  intro s
  induction s with
  | zero =>
    intro c
    rw [Wk1_succ]
    simp only [Nat.choose_zero_right, Nat.cast_one, one_mul]
    calc _ ≤ ∑ u ∈ Finset.Icc 1 K, (if u = c + 1 then ((1 : ℝ) / 2) ^ (c + 1) else 0) := by
          apply Finset.sum_le_sum; intro u _
          by_cases h : u = c + 1
          · subst h; simp [Wk1]
          · rw [if_neg h]
            simp only [Wk1]
            split_ifs with h1 h2 <;> first | omega | simp
      _ ≤ ((1 : ℝ) / 2) ^ (c + 1) := by
          rw [Finset.sum_ite_eq']
          split_ifs
          · exact le_rfl
          · positivity
  | succ s ih =>
    intro c
    rw [Wk1_succ]
    calc _ ≤ ∑ u ∈ Finset.Icc 1 K,
          (if u ≤ c then ((c - u).choose s : ℝ) * ((1 : ℝ) / 2) ^ (c + 1) else 0) := by
          apply Finset.sum_le_sum; intro u _
          by_cases h : u ≤ c
          · rw [if_pos h, if_pos (by omega)]
            have e : c + 1 - u = (c - u) + 1 := by omega
            rw [e]
            have h2 := ih (c - u)
            have e2 : ((1 : ℝ) / 2) ^ u * ((1 : ℝ) / 2) ^ (c - u + 1) = ((1 : ℝ) / 2) ^ (c + 1) := by
              rw [← pow_add]; congr 1; omega
            calc ((1 : ℝ) / 2) ^ u * Wk1 K (s + 1) (c - u + 1)
                ≤ ((1 : ℝ) / 2) ^ u * (((c - u).choose s : ℝ) * ((1 : ℝ) / 2) ^ (c - u + 1)) :=
                  mul_le_mul_of_nonneg_left h2 (by positivity)
              _ = _ := by rw [← e2]; ring
          · rw [if_neg h]
            by_cases h' : u = c + 1
            · subst h'; rw [if_pos le_rfl, Nat.sub_self, Wk1_zero, mul_zero]
            · rw [if_neg (by omega), mul_zero]
      _ = ∑ u ∈ (Finset.Icc 1 K).filter (fun u => u ≤ c),
          ((c - u).choose s : ℝ) * ((1 : ℝ) / 2) ^ (c + 1) := by rw [Finset.sum_filter]
      _ ≤ ∑ u ∈ Finset.Icc 1 c, ((c - u).choose s : ℝ) * ((1 : ℝ) / 2) ^ (c + 1) := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro u hu
            simp only [Finset.mem_filter, Finset.mem_Icc] at hu ⊢
            omega
          · intro i _ _; positivity
      _ = _ := by rw [← Finset.sum_mul, sum_Icc_reflect_choose]

lemma choose_mid_sq (c : ℕ) : (c.choose (c / 2)) ^ 2 * (c / 2 + 1) ≤ 4 ^ c := by
  obtain ⟨N, rfl | rfl⟩ := Nat.even_or_odd' c
  · have h := centralBinom_sq_le N
    rw [Nat.centralBinom_eq_two_mul_choose] at h
    have e : 2 * N / 2 = N := by omega
    rw [e]
    have e4 : (4 : ℕ) ^ (2 * N) = 16 ^ N := by rw [pow_mul]; norm_num
    rw [e4]; exact h
  · have h := centralBinom_sq_le (N + 1)
    have e : (2 * N + 1) / 2 = N := by omega
    rw [e]
    have e2 : Nat.centralBinom (N + 1) = 2 * (2 * N + 1).choose N := by
      rw [Nat.centralBinom_eq_two_mul_choose,
        show 2 * (N + 1) = (2 * N + 1) + 1 by ring, Nat.choose_succ_succ, Nat.choose_symm_half]
      ring
    rw [e2] at h
    have e4 : (16 : ℕ) ^ (N + 1) = 4 * 4 ^ (2 * N + 1) := by
      rw [pow_succ, pow_succ, pow_mul]; norm_num; ring
    rw [e4] at h
    (first | linarith | nlinarith)

lemma Wk1_max (K s c : ℕ) : (Wk1 K (s + 1) (c + 1)) ^ 2 * (((c / 2 : ℕ) : ℝ) + 1) ≤ 1 / 4 := by
  have h1 := Wk1_le K s c
  have h0 := Wk1_nonneg K (s + 1) (c + 1)
  have hm : (c.choose s : ℝ) ≤ (c.choose (c / 2) : ℝ) := by exact_mod_cast Nat.choose_le_middle s c
  have hq : ((c.choose (c / 2) : ℕ) : ℝ) ^ 2 * (((c / 2 : ℕ) : ℝ) + 1) ≤ (4 : ℝ) ^ c := by
    exact_mod_cast choose_mid_sq c
  have hW : Wk1 K (s + 1) (c + 1) ≤ (c.choose (c / 2) : ℝ) * ((1 : ℝ) / 2) ^ (c + 1) :=
    h1.trans (mul_le_mul_of_nonneg_right hm (by positivity))
  have hsq : (Wk1 K (s + 1) (c + 1)) ^ 2 ≤ ((c.choose (c / 2) : ℝ) * ((1 : ℝ) / 2) ^ (c + 1)) ^ 2 :=
    pow_le_pow_left₀ h0 hW 2
  have e : (((1 : ℝ) / 2) ^ (c + 1)) ^ 2 * (4 : ℝ) ^ c = 1 / 4 := by
    have e1 : ((1 : ℝ) / 2) ^ (c + 1) = ((1 : ℝ) / 2) ^ c * (1 / 2) := pow_succ _ _
    have e2 : (4 : ℝ) ^ c = (2 ^ c) ^ 2 := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
    have e3 : ((1 : ℝ) / 2) ^ c * 2 ^ c = 1 := by rw [← mul_pow]; norm_num
    rw [e1, e2, show (((1 : ℝ) / 2) ^ c * (1 / 2)) ^ 2 * ((2 : ℝ) ^ c) ^ 2 =
      (((1 : ℝ) / 2) ^ c * 2 ^ c) ^ 2 * (1 / 4) by ring, e3]; norm_num
  have hpos : (0 : ℝ) ≤ ((c / 2 : ℕ) : ℝ) + 1 := by positivity
  calc (Wk1 K (s + 1) (c + 1)) ^ 2 * (((c / 2 : ℕ) : ℝ) + 1)
      ≤ ((c.choose (c / 2) : ℝ) * ((1 : ℝ) / 2) ^ (c + 1)) ^ 2 * (((c / 2 : ℕ) : ℝ) + 1) :=
        mul_le_mul_of_nonneg_right hsq hpos
    _ = (((1 : ℝ) / 2) ^ (c + 1)) ^ 2 * (((c.choose (c / 2) : ℕ) : ℝ) ^ 2 * (((c / 2 : ℕ) : ℝ) + 1)) := by
        ring
    _ ≤ (((1 : ℝ) / 2) ^ (c + 1)) ^ 2 * (4 : ℝ) ^ c := mul_le_mul_of_nonneg_left hq (by positivity)
    _ = 1 / 4 := e

/-! W1b (session 31): Wk1 summed over an arithmetic progression of pair rows. -/

lemma choose_up (n i j : ℕ) (hij : i ≤ j) (hj : j ≤ n / 2) : n.choose i ≤ n.choose j := by
  induction j, hij using Nat.le_induction with
  | base => exact le_refl _
  | succ j hij ih =>
    exact (ih (by omega)).trans (Nat.choose_le_succ_of_lt_half_left (by omega))

lemma choose_dn_step (n j : ℕ) (hj : n / 2 ≤ j) : n.choose (j + 1) ≤ n.choose j := by
  have h := Nat.choose_succ_right_eq n j
  by_cases hjn : j < n
  · have h2 : n - j ≤ j + 1 := by omega
    have h3 : n.choose (j + 1) * (j + 1) ≤ n.choose j * (j + 1) := by
      rw [h]; exact Nat.mul_le_mul_left _ h2
    exact Nat.le_of_mul_le_mul_right h3 (by omega)
  · rw [Nat.choose_eq_zero_of_lt (by omega : n < j + 1)]; exact Nat.zero_le _

lemma choose_dn (n i j : ℕ) (hi : n / 2 ≤ i) (hij : i ≤ j) : n.choose j ≤ n.choose i := by
  induction j, hij using Nat.le_induction with
  | base => exact le_refl _
  | succ j hij ih => exact (choose_dn_step n j (by omega)).trans ih

lemma sum_range_choose_le (x L : ℕ) : ∑ i ∈ Finset.range L, (x.choose i : ℝ) ≤ 2 ^ x := by
  have h1 : ∑ i ∈ Finset.range L, x.choose i ≤ ∑ i ∈ Finset.range (L + x + 1), x.choose i :=
    Finset.sum_le_sum_of_subset ((fun i hi => by simp only [Finset.mem_range] at hi ⊢; omega))
  have h2 : ∑ i ∈ Finset.range (x + 1), x.choose i = ∑ i ∈ Finset.range (L + x + 1), x.choose i := by
    apply Finset.sum_subset ((fun i hi => by simp only [Finset.mem_range] at hi ⊢; omega))
    intro i _ hi
    simp only [Finset.mem_range, not_lt] at hi
    exact Nat.choose_eq_zero_of_lt (by omega)
  rw [Nat.sum_range_choose] at h2
  have h3 : ∑ i ∈ Finset.range L, x.choose i ≤ 2 ^ x := h2 ▸ h1
  exact_mod_cast h3

noncomputable def gB (x j : ℕ) : ℝ := if j = 0 then 0 else (x.choose (j - 1) : ℝ) * ((1 : ℝ) / 2) ^ (x + 1)

lemma gB_nonneg (x j : ℕ) : 0 ≤ gB x j := by
  unfold gB; split_ifs <;> positivity

lemma Wk1_le_gB (K x j : ℕ) : Wk1 K j (x + 1) ≤ gB x j := by
  rcases j with _ | s
  · simp [Wk1, gB]
  · simpa [gB] using Wk1_le K s x

lemma gB_sum (x L : ℕ) : ∑ i ∈ Finset.range L, gB x i ≤ 1 / 2 := by
  rcases L with _ | L
  · simp
  rw [Finset.sum_range_succ']
  have e : ∀ i, gB x (i + 1) = (x.choose i : ℝ) * ((1 : ℝ) / 2) ^ (x + 1) := fun i => by simp [gB]
  have h0 : gB x 0 = 0 := by simp [gB]
  rw [h0, add_zero, Finset.sum_congr rfl (fun i _ => e i), ← Finset.sum_mul]
  have h := sum_range_choose_le x L
  have hp : ((1 : ℝ) / 2) ^ (x + 1) * 2 ^ x = 1 / 2 := by
    rw [pow_succ, mul_comm, ← mul_assoc, ← mul_pow]; norm_num
  calc (∑ i ∈ Finset.range L, (x.choose i : ℝ)) * ((1 : ℝ) / 2) ^ (x + 1)
      ≤ 2 ^ x * ((1 : ℝ) / 2) ^ (x + 1) := mul_le_mul_of_nonneg_right h (by positivity)
    _ = 1 / 2 := by rw [mul_comm]; exact hp

lemma W1b (K x M a0 T : ℕ) (hM : 1 ≤ M) :
    ∑ t ∈ Finset.range T, Wk1 K (2 * (a0 + M * t)) (x + 1) ≤
      1 / (4 * M) + 3 * ((x.choose (x / 2) : ℝ) * ((1 : ℝ) / 2) ^ (x + 1)) := by
  set F := (x.choose (x / 2) : ℝ) * ((1 : ℝ) / 2) ^ (x + 1) with hFdef
  have hup : ∀ i j, i ≤ j → j ≤ x / 2 + 1 → gB x i ≤ gB x j := by
    intro i j hij hj
    by_cases hi : i = 0
    · subst hi; simp only [gB]; exact gB_nonneg x j
    · have hj0 : j ≠ 0 := by omega
      simp only [gB, if_neg hi, if_neg hj0]
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact_mod_cast choose_up x (i - 1) (j - 1) (by omega) (by omega)
  have hdn : ∀ i j, x / 2 + 1 ≤ i → i ≤ j → gB x j ≤ gB x i := by
    intro i j hi hij
    have hi0 : i ≠ 0 := by omega
    have hj0 : j ≠ 0 := by omega
    simp only [gB, if_neg hi0, if_neg hj0]
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    exact_mod_cast choose_dn x (i - 1) (j - 1) (by omega) (by omega)
  have hF : ∀ i, gB x i ≤ F := by
    intro i
    unfold gB; split_ifs
    · positivity
    · apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact_mod_cast Nat.choose_le_middle (i - 1) x
  have hap := ap_unimodal (gB x) (gB_nonneg x) (x / 2 + 1) hup hdn F hF (2 * M) (2 * a0) T (by omega)
  have hs := gB_sum x (2 * a0 + 2 * M * T)
  have hterm : ∑ t ∈ Finset.range T, Wk1 K (2 * (a0 + M * t)) (x + 1) ≤
      ∑ t ∈ Finset.range T, gB x (2 * a0 + 2 * M * t) := by
    apply Finset.sum_le_sum; intro t _
    have e : 2 * a0 + 2 * M * t = 2 * (a0 + M * t) := by ring
    rw [e]; exact Wk1_le_gB K x _
  have hM' : (0 : ℝ) < 2 * M := by have : (1 : ℝ) ≤ M := by exact_mod_cast hM
                                   linarith
  have hcast : ((2 * M : ℕ) : ℝ) = 2 * (M : ℝ) := by push_cast; ring
  rw [hcast] at hap
  have key : (2 * (M : ℝ)) * ∑ t ∈ Finset.range T, gB x (2 * a0 + 2 * M * t) ≤
      (2 * (M : ℝ)) * (1 / (4 * M) + 3 * F) := by
    have e2 : (2 * (M : ℝ)) * (1 / (4 * M) + 3 * F) = 1 / 2 + 3 * (2 * M) * F := by
      field_simp; ring
    rw [e2]; linarith
  exact hterm.trans (le_of_mul_le_mul_left key hM')

lemma W1b_F (x : ℕ) : ((x.choose (x / 2) : ℝ) * ((1 : ℝ) / 2) ^ (x + 1)) ^ 2 * (((x / 2 : ℕ) : ℝ) + 1) ≤ 1 / 4 := by
  have h := Wk1_max 0 0 x
  have hq : ((x.choose (x / 2) : ℕ) : ℝ) ^ 2 * (((x / 2 : ℕ) : ℝ) + 1) ≤ (4 : ℝ) ^ x := by
    exact_mod_cast choose_mid_sq x
  have e : (((1 : ℝ) / 2) ^ (x + 1)) ^ 2 * (4 : ℝ) ^ x = 1 / 4 := by
    have e1 : ((1 : ℝ) / 2) ^ (x + 1) = ((1 : ℝ) / 2) ^ x * (1 / 2) := pow_succ _ _
    have e2 : (4 : ℝ) ^ x = (2 ^ x) ^ 2 := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
    have e3 : ((1 : ℝ) / 2) ^ x * 2 ^ x = 1 := by rw [← mul_pow]; norm_num
    rw [e1, e2, show (((1 : ℝ) / 2) ^ x * (1 / 2)) ^ 2 * ((2 : ℝ) ^ x) ^ 2 =
      (((1 : ℝ) / 2) ^ x * 2 ^ x) ^ 2 * (1 / 4) by ring, e3]; norm_num
  calc ((x.choose (x / 2) : ℝ) * ((1 : ℝ) / 2) ^ (x + 1)) ^ 2 * (((x / 2 : ℕ) : ℝ) + 1)
      = (((1 : ℝ) / 2) ^ (x + 1)) ^ 2 * (((x.choose (x / 2) : ℕ) : ℝ) ^ 2 * (((x / 2 : ℕ) : ℝ) + 1)) := by ring
    _ ≤ (((1 : ℝ) / 2) ^ (x + 1)) ^ 2 * (4 : ℝ) ^ x := mul_le_mul_of_nonneg_left hq (by positivity)
    _ = 1 / 4 := e

lemma geom_Icc_le' (x : ℝ) (h0 : 0 ≤ x) (h1 : x < 1) (K : ℕ) :
    ∑ a ∈ Finset.Icc 1 K, x ^ a ≤ x / (1 - x) := by
  have hI : Finset.Icc 1 K ⊆ Finset.range (K + 1) := by
    intro a ha; simp only [Finset.mem_Icc, Finset.mem_range] at ha ⊢; omega
  have hs : ∑ a ∈ Finset.Icc 1 K, x ^ a = x * ∑ a ∈ Finset.Icc 1 K, x ^ (a - 1) := by
    rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro a ha
    simp only [Finset.mem_Icc] at ha
    rw [← pow_succ']; congr 1; omega
  have hg : ∑ a ∈ Finset.Icc 1 K, x ^ (a - 1) ≤ 1 / (1 - x) := by
    have e : ∑ a ∈ Finset.Icc 1 K, x ^ (a - 1) = ∑ i ∈ Finset.range K, x ^ i := by
      apply Finset.sum_nbij' (fun a => a - 1) (fun i => i + 1)
      · intro a ha; simp only [Finset.mem_Icc, Finset.mem_range, Finset.mem_coe] at ha ⊢; omega
      · intro i hi; simp only [Finset.mem_Icc, Finset.mem_range, Finset.mem_coe] at hi ⊢; omega
      · intro a ha; simp only [Finset.mem_Icc, Finset.mem_coe] at ha; omega
      · intro i _; simp
      · intro a _; rfl
    rw [e, geom_sum_eq h1.ne K]
    have hxK : 0 ≤ x ^ K := pow_nonneg h0 K
    have e2 : (x ^ K - 1) / (x - 1) = (1 - x ^ K) / (1 - x) := by
      rw [div_eq_div_iff (by linarith) (by linarith)]; ring
    rw [e2]
    exact div_le_div_of_nonneg_right (by linarith) (by linarith)
  rw [hs]
  calc x * ∑ a ∈ Finset.Icc 1 K, x ^ (a - 1) ≤ x * (1 / (1 - x)) := mul_le_mul_of_nonneg_left hg h0
    _ = x / (1 - x) := by ring

/-! W2 (session 31): exponential-moment (Chernoff) bounds for the single-step walk `Wk1`. -/

lemma shift_sum_le (N u : ℕ) (g : ℕ → ℝ) (hg : ∀ c, 0 ≤ g c) :
    ∑ c ∈ Finset.range N, (if u ≤ c then g (c - u) else 0) ≤ ∑ c ∈ Finset.range N, g c := by
  rw [← Finset.sum_filter]
  have hI : (Finset.range N).filter (fun c => u ≤ c) = Finset.Ico u N := by
    ext c; simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]; omega
  rw [hI, Finset.sum_Ico_eq_sum_range]
  have e : ∀ k, g (u + k - u) = g k := fun k => by rw [Nat.add_sub_cancel_left]
  simp only [e]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro c hc; simp only [Finset.mem_range] at hc ⊢; omega
  · intro c _ _; exact hg c

lemma Wk1_mgf (K : ℕ) (z : ℝ) (hz0 : 0 ≤ z) (hz2 : z < 2) :
    ∀ s N, ∑ c ∈ Finset.range N, Wk1 K s c * z ^ c ≤ (z / (2 - z)) ^ s := by
  intro s
  induction s with
  | zero =>
    intro N
    rcases N with _ | N
    · simp
    · rw [Finset.sum_range_succ']
      have h0 : ∀ c, Wk1 K 0 (c + 1) * z ^ (c + 1) = 0 := fun c => by simp [Wk1]
      simp only [h0, Finset.sum_const_zero, zero_add, pow_zero]
      simp [Wk1]
  | succ s ih =>
    intro N
    have hq0 : 0 ≤ z / (2 - z) := div_nonneg hz0 (by linarith)
    calc ∑ c ∈ Finset.range N, Wk1 K (s + 1) c * z ^ c
        = ∑ u ∈ Finset.Icc 1 K, ((z / 2) ^ u *
            ∑ c ∈ Finset.range N, (if u ≤ c then Wk1 K s (c - u) * z ^ (c - u) else 0)) := by
          simp only [Wk1_succ, Finset.sum_mul]
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl; intro u _
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl; intro c _
          split_ifs with h
          · have e : z ^ c = z ^ u * z ^ (c - u) := by rw [← pow_add]; congr 1; omega
            rw [e]
            have h2 : ((1 : ℝ) / 2) ^ u * 2 ^ u = 1 := by rw [← mul_pow]; norm_num
            have h3 : (z / 2) ^ u = z ^ u * ((1 : ℝ) / 2) ^ u := by rw [← mul_pow]; ring
            rw [h3]; ring
          · simp
      _ ≤ ∑ u ∈ Finset.Icc 1 K, ((z / 2) ^ u * (z / (2 - z)) ^ s) := by
          apply Finset.sum_le_sum; intro u _
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact (shift_sum_le N u (fun c => Wk1 K s c * z ^ c)
            (fun c => mul_nonneg (Wk1_nonneg K s c) (pow_nonneg hz0 c))).trans (ih N)
      _ = (∑ u ∈ Finset.Icc 1 K, (z / 2) ^ u) * (z / (2 - z)) ^ s := by rw [Finset.sum_mul]
      _ ≤ (z / 2 / (1 - z / 2)) * (z / (2 - z)) ^ s :=
          mul_le_mul_of_nonneg_right (geom_Icc_le' (z / 2) (by positivity) (by linarith) K)
            (pow_nonneg hq0 s)
      _ = (z / (2 - z)) ^ (s + 1) := by
          have h2z : (2 : ℝ) - z ≠ 0 := by linarith
          rw [pow_succ]; field_simp <;> ring

lemma Wk1_low (K s L : ℕ) (z : ℝ) (hz0 : 0 < z) (hz1 : z ≤ 1) :
    ∑ c ∈ Finset.range (L + 1), Wk1 K s c ≤ (1 / z) ^ L * (z / (2 - z)) ^ s := by
  have hm := Wk1_mgf K z hz0.le (by linarith) s (L + 1)
  have hzL : 0 < z ^ L := pow_pos hz0 L
  have key : ∑ c ∈ Finset.range (L + 1), Wk1 K s c * z ^ L ≤
      ∑ c ∈ Finset.range (L + 1), Wk1 K s c * z ^ c := by
    apply Finset.sum_le_sum; intro c hc
    simp only [Finset.mem_range] at hc
    exact mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hz0.le hz1 (by omega)) (Wk1_nonneg K s c)
  rw [← Finset.sum_mul] at key
  have h1 : (∑ c ∈ Finset.range (L + 1), Wk1 K s c) * z ^ L ≤ (z / (2 - z)) ^ s := key.trans hm
  have e : (1 / z) ^ L * z ^ L = 1 := by rw [← mul_pow]; field_simp; simp
  calc ∑ c ∈ Finset.range (L + 1), Wk1 K s c
      = (1 / z) ^ L * ((∑ c ∈ Finset.range (L + 1), Wk1 K s c) * z ^ L) := by
        rw [mul_comm ((∑ c ∈ Finset.range (L + 1), Wk1 K s c)), ← mul_assoc, e, one_mul]
    _ ≤ (1 / z) ^ L * (z / (2 - z)) ^ s := mul_le_mul_of_nonneg_left h1 (by positivity)

lemma Wk1_high (K s L N : ℕ) (z : ℝ) (hz1 : 1 ≤ z) (hz2 : z < 2) :
    ∑ c ∈ Finset.Ico L N, Wk1 K s c ≤ (1 / z) ^ L * (z / (2 - z)) ^ s := by
  have hz0 : 0 < z := by linarith
  have hm := Wk1_mgf K z hz0.le hz2 s N
  have key : ∑ c ∈ Finset.Ico L N, Wk1 K s c * z ^ L ≤ ∑ c ∈ Finset.range N, Wk1 K s c * z ^ c := by
    calc ∑ c ∈ Finset.Ico L N, Wk1 K s c * z ^ L ≤ ∑ c ∈ Finset.Ico L N, Wk1 K s c * z ^ c := by
          apply Finset.sum_le_sum; intro c hc
          simp only [Finset.mem_Ico] at hc
          exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hz1 hc.1) (Wk1_nonneg K s c)
      _ ≤ ∑ c ∈ Finset.range N, Wk1 K s c * z ^ c := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro c hc; simp only [Finset.mem_Ico, Finset.mem_range] at hc ⊢; omega
          · intro c _ _; exact mul_nonneg (Wk1_nonneg K s c) (pow_nonneg hz0.le c)
  rw [← Finset.sum_mul] at key
  have h1 := key.trans hm
  have e : (1 / z) ^ L * z ^ L = 1 := by rw [← mul_pow]; field_simp; simp
  calc ∑ c ∈ Finset.Ico L N, Wk1 K s c
      = (1 / z) ^ L * ((∑ c ∈ Finset.Ico L N, Wk1 K s c) * z ^ L) := by
        rw [mul_comm ((∑ c ∈ Finset.Ico L N, Wk1 K s c)), ← mul_assoc, e, one_mul]
    _ ≤ (1 / z) ^ L * (z / (2 - z)) ^ s := mul_le_mul_of_nonneg_left h1 (by positivity)


/-! W4 (session 32): bad-visit mass. A black probe past the run end with budget `≥ s` pins its row to
one class mod `2^(e+s-3)` per odd multiplier `k` (`W4_arith` + `same_class`); summing the pair-walk
visit mass over such rows is at most `(2 kmax + 1) (1/(4·2^(t-3)) + 3F)` (`class_sum_le` + `W1b`). -/

lemma W4_arith (n a c β s : ℕ) (X Y m : ℤ) (ε : ℝ) (hd : (3 : ℤ) ^ n ∣ 2 ^ c * Y - 9 ^ a * X)
    (hX : X = 2 ^ β * m) (hc : β ≤ c) (hY : |(Y : ℝ)| ≤ ε * 3 ^ n) (hs : (2 : ℤ) ^ s ∣ Y)
    (h9 : (9 : ℝ) ^ a * |(m : ℝ)| ≤ 3 ^ n) :
    ∃ k : ℤ, |(k : ℝ)| ≤ ε * 2 ^ (c - β) + 1 ∧ (2 : ℤ) ^ (c - β + s) ∣ 9 ^ a * m + k * 3 ^ n := by
  obtain ⟨k, hk⟩ := l710_rel n a c β X Y m hd hX hc
  refine ⟨k, ?_, ?_⟩
  · have hk' : (k : ℝ) * 3 ^ n = 2 ^ (c - β) * (Y : ℝ) - 9 ^ a * (m : ℝ) := by
      have := congrArg (fun z : ℤ => (z : ℝ)) hk
      push_cast at this
      linarith
    have h3 : (0 : ℝ) < 3 ^ n := by positivity
    have hp : (0 : ℝ) < 2 ^ (c - β) := by positivity
    obtain ⟨hY1, hY2⟩ := abs_le.mp hY
    have hm' : |(9 : ℝ) ^ a * (m : ℝ)| ≤ 3 ^ n := by
      rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 9 ^ a)]; exact h9
    obtain ⟨hm1, hm2⟩ := abs_le.mp hm'
    have l1 := mul_le_mul_of_nonneg_left hY1 hp.le
    have l2 := mul_le_mul_of_nonneg_left hY2 hp.le
    rw [abs_le]
    constructor
    · have : (-(ε * 2 ^ (c - β) + 1)) * 3 ^ n ≤ (k : ℝ) * 3 ^ n := by rw [hk']; (first | linarith | nlinarith)
      exact le_of_mul_le_mul_right this h3
    · have : (k : ℝ) * 3 ^ n ≤ (ε * 2 ^ (c - β) + 1) * 3 ^ n := by rw [hk']; (first | linarith | nlinarith)
      exact le_of_mul_le_mul_right this h3
  · rw [pow_add, hk.symm]
    exact mul_dvd_mul_left _ hs

lemma class_sum_le (f : ℕ → ℝ) (hf : ∀ i, 0 ≤ f i) (M T : ℕ) (hM : 1 ≤ M) (P : ℕ → Prop)
    [DecidablePred P] (hcl : ∀ a1 a2, P a1 → P a2 → a1 ≤ a2 → M ∣ a2 - a1) :
    ∃ a0, ∑ a ∈ Finset.range T, (if P a then f a else 0) ≤ ∑ i ∈ Finset.range T, f (a0 + M * i) := by
  by_cases hne : ∃ a, a < T ∧ P a
  · set s := (Finset.range T).filter P with hsdef
    have hs : s.Nonempty := by
      obtain ⟨a, ha, hPa⟩ := hne
      exact ⟨a, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr ha, hPa⟩⟩
    refine ⟨s.min' hs, ?_⟩
    set a0 := s.min' hs with ha0def
    have ha0 : a0 ∈ s := Finset.min'_mem s hs
    have hP0 : P a0 := (Finset.mem_filter.mp ha0).2
    rw [← Finset.sum_filter]
    have hsub : s ⊆ (Finset.range T).image (fun i => a0 + M * i) := by
      intro a ha
      have haT := Finset.mem_filter.mp ha
      have hle : a0 ≤ a := Finset.min'_le s a ha
      obtain ⟨q, hq⟩ := hcl a0 a hP0 haT.2 hle
      have hqM : q ≤ M * q := by (first | linarith | nlinarith)
      have haT' : a < T := Finset.mem_range.mp haT.1
      rw [Finset.mem_image]
      refine ⟨q, ?_, ?_⟩
      · rw [Finset.mem_range]
        generalize M * q = w at *
        omega
      · generalize M * q = w at *
        omega
    calc ∑ a ∈ s, f a ≤ ∑ a ∈ (Finset.range T).image (fun i => a0 + M * i), f a :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub (fun i _ _ => hf i)
      _ = ∑ i ∈ Finset.range T, f (a0 + M * i) := by
          rw [Finset.sum_image]
          intro x _ y _ h
          have h' : a0 + M * x = a0 + M * y := h
          exact Nat.eq_of_mul_eq_mul_left hM (Nat.add_left_cancel h')
  · refine ⟨0, ?_⟩
    have h0 : ∑ a ∈ Finset.range T, (if P a then f a else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro a ha
      rw [if_neg]
      intro hPa
      exact hne ⟨a, Finset.mem_range.mp ha, hPa⟩
    rw [h0]
    exact Finset.sum_nonneg (fun i _ => hf _)

lemma W4_core (K x T t n kmax : ℕ) (m : ℤ) (hm : ¬ (2 : ℤ) ∣ m) (P : ℕ → Prop) [DecidablePred P]
    (hP : ∀ a, P a → ∃ k : ℤ, |k| ≤ kmax ∧ (2 : ℤ) ^ t ∣ 9 ^ (a + 1) * m + k * 3 ^ n) :
    ∑ a ∈ Finset.range T, (if P a then Wk1 K (2 * (a + 1)) (x + 1) else 0) ≤
      (2 * kmax + 1) * (1 / (4 * ((2 ^ (t - 3) : ℕ) : ℝ)) +
        3 * ((x.choose (x / 2) : ℝ) * ((1 : ℝ) / 2) ^ (x + 1))) := by
  set F := (x.choose (x / 2) : ℝ) * ((1 : ℝ) / 2) ^ (x + 1) with hF
  set Q : ℤ → ℕ → Prop := fun k a => (2 : ℤ) ^ t ∣ 9 ^ (a + 1) * m + k * 3 ^ n with hQ
  have hW : ∀ a, 0 ≤ Wk1 K (2 * (a + 1)) (x + 1) := fun a => Wk1_nonneg K _ _
  have h1 : ∀ a, (if P a then Wk1 K (2 * (a + 1)) (x + 1) else 0) ≤
      ∑ k ∈ Finset.Icc (-(kmax : ℤ)) kmax, (if Q k a then Wk1 K (2 * (a + 1)) (x + 1) else 0) := by
    intro a
    by_cases hPa : P a
    · rw [if_pos hPa]
      obtain ⟨k, hk, hdk⟩ := hP a hPa
      have hkmem : k ∈ Finset.Icc (-(kmax : ℤ)) kmax := by
        rw [Finset.mem_Icc]
        constructor
        · linarith [neg_abs_le k]
        · linarith [le_abs_self k]
      have hnn : ∀ k' ∈ Finset.Icc (-(kmax : ℤ)) kmax,
          0 ≤ (if Q k' a then Wk1 K (2 * (a + 1)) (x + 1) else 0) := by
        intro k' _; split_ifs; exact hW a; exact le_rfl
      have := Finset.single_le_sum hnn hkmem
      rw [if_pos hdk] at this
      exact this
    · rw [if_neg hPa]
      exact Finset.sum_nonneg (fun k' _ => by split_ifs; exact hW a; exact le_rfl)
  have hk : ∀ k : ℤ, ∑ a ∈ Finset.range T, (if Q k a then Wk1 K (2 * (a + 1)) (x + 1) else 0) ≤
      1 / (4 * ((2 ^ (t - 3) : ℕ) : ℝ)) + 3 * F := by
    intro k
    have hcl : ∀ a1 a2, Q k a1 → Q k a2 → a1 ≤ a2 → 2 ^ (t - 3) ∣ a2 - a1 := by
      intro a1 a2 h1 h2 h12
      have := same_class n t (a1 + 1) (a2 + 1) m k hm (by omega) h1 h2
      rwa [show a2 + 1 - (a1 + 1) = a2 - a1 by omega] at this
    obtain ⟨a0, ha0⟩ := class_sum_le (fun a => Wk1 K (2 * (a + 1)) (x + 1)) hW (2 ^ (t - 3)) T
      Nat.one_le_two_pow (Q k) hcl
    have hb := W1b K x (2 ^ (t - 3)) (a0 + 1) T Nat.one_le_two_pow
    refine le_trans ha0 (le_of_eq_of_le ?_ hb)
    apply Finset.sum_congr rfl
    intro i _
    congr 2
    ring
  calc ∑ a ∈ Finset.range T, (if P a then Wk1 K (2 * (a + 1)) (x + 1) else 0)
      ≤ ∑ a ∈ Finset.range T, ∑ k ∈ Finset.Icc (-(kmax : ℤ)) kmax,
          (if Q k a then Wk1 K (2 * (a + 1)) (x + 1) else 0) := Finset.sum_le_sum (fun a _ => h1 a)
    _ = ∑ k ∈ Finset.Icc (-(kmax : ℤ)) kmax, ∑ a ∈ Finset.range T,
          (if Q k a then Wk1 K (2 * (a + 1)) (x + 1) else 0) := Finset.sum_comm
    _ ≤ ∑ k ∈ Finset.Icc (-(kmax : ℤ)) kmax, (1 / (4 * ((2 ^ (t - 3) : ℕ) : ℝ)) + 3 * F) :=
          Finset.sum_le_sum (fun k _ => hk k)
    _ = (2 * kmax + 1) * (1 / (4 * ((2 ^ (t - 3) : ℕ) : ℝ)) + 3 * F) := by
          rw [Finset.sum_const, nsmul_eq_mul, Int.card_Icc]
          congr 1
          have : (kmax + 1 - -(kmax : ℤ)).toNat = 2 * kmax + 1 := by omega
          rw [this]; push_cast; ring


lemma rho_bound (K blk Dmax : ℕ) :
    ∑ a ∈ Finset.range blk, ∑ c ∈ Finset.range (2 * K * (a + 1) + 1),
      Wk1 K (2 * (a + 1)) c * (if blk * Dmax < c then (1 : ℝ) else 0) ≤
      (blk : ℝ) * (9 ^ blk * (2 / 3) ^ (blk * Dmax + 1)) := by
  have hstep : ∀ a ∈ Finset.range blk, ∑ c ∈ Finset.range (2 * K * (a + 1) + 1),
      Wk1 K (2 * (a + 1)) c * (if blk * Dmax < c then (1 : ℝ) else 0) ≤
      9 ^ blk * (2 / 3) ^ (blk * Dmax + 1) := by
    intro a ha
    rw [Finset.mem_range] at ha
    have h1 : ∑ c ∈ Finset.range (2 * K * (a + 1) + 1),
        Wk1 K (2 * (a + 1)) c * (if blk * Dmax < c then (1 : ℝ) else 0) ≤
        ∑ c ∈ Finset.Ico (blk * Dmax + 1) (2 * K * (a + 1) + 1), Wk1 K (2 * (a + 1)) c := by
      simp only [mul_ite, mul_one, mul_zero]
      rw [← Finset.sum_filter]
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro c hc
        simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico] at hc ⊢; omega
      · intro c _ _; exact Wk1_nonneg K _ c
    have h2 := Wk1_high K (2 * (a + 1)) (blk * Dmax + 1) (2 * K * (a + 1) + 1) (3 / 2)
      (by norm_num) (by norm_num)
    have e1 : (1 : ℝ) / (3 / 2) = 2 / 3 := by norm_num
    have e2 : ((3 : ℝ) / 2) / (2 - 3 / 2) = 3 := by norm_num
    rw [e1, e2] at h2
    have e3 : (3 : ℝ) ^ (2 * (a + 1)) = 9 ^ (a + 1) := by rw [pow_mul]; norm_num
    have h3 : (3 : ℝ) ^ (2 * (a + 1)) ≤ 9 ^ blk := by
      rw [e3]; exact pow_le_pow_right₀ (by norm_num) (by omega)
    have h4 : (0 : ℝ) ≤ (2 / 3) ^ (blk * Dmax + 1) := by positivity
    (first | linarith [mul_le_mul_of_nonneg_left h3 h4] | nlinarith [mul_le_mul_of_nonneg_left h3 h4])
  calc _ ≤ ∑ a ∈ Finset.range blk, (9 : ℝ) ^ blk * (2 / 3) ^ (blk * Dmax + 1) := Finset.sum_le_sum hstep
    _ = (blk : ℝ) * (9 ^ blk * (2 / 3) ^ (blk * Dmax + 1)) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]


/-! W7c (session 34): mass of the bad-probe kill set, arithmetic half. Any position predicate `P a c` that
forces the W4_arith hypotheses (post-exit column `β < c ≤ β + E`, 2-adic budget `B0` at the probe) has
pair-walk visit mass at most `W (2 kmax + 1) Σ_c (class term + point-mass term)`. -/
open Classical in
lemma Sbad_sum_gen (K n r β E B0 : ℕ) (X m : ℤ) (ε W : ℝ) (hε : 0 ≤ ε) (hW : 0 ≤ W)
    (hX : X = 2 ^ β * m) (hm : ¬ (2 : ℤ) ∣ m) (P : ℕ → ℕ → Prop)
    (hP : ∀ a c, P a c → β < c ∧ c ≤ β + E ∧ (9 : ℝ) ^ (a + 1) * |(m : ℝ)| ≤ 3 ^ n ∧
      ∃ Y : ℤ, (3 : ℤ) ^ n ∣ 2 ^ c * Y - 9 ^ (a + 1) * X ∧ |(Y : ℝ)| ≤ ε * 3 ^ n ∧ (2 : ℤ) ^ B0 ∣ Y) :
    ∑ a ∈ Finset.range r, ∑ c ∈ Finset.range (2 * K * (a + 1) + 1),
      Wk1 K (2 * (a + 1)) c * (if P a c then W else 0) ≤
      W * ∑ c ∈ Finset.Ioc β (β + E), (2 * ((⌊ε * 2 ^ (c - β) + 1⌋₊ : ℕ) : ℝ) + 1) *
        (1 / (4 * ((2 ^ (c - β + B0 - 3) : ℕ) : ℝ)) +
          3 * (((c - 1).choose ((c - 1) / 2) : ℝ) * ((1 : ℝ) / 2) ^ c)) := by
  have hf0 : ∀ a c, 0 ≤ Wk1 K (2 * (a + 1)) c * (if P a c then W else 0) := by
    intro a c; apply mul_nonneg (Wk1_nonneg K _ _); split_ifs <;> linarith
  have h1 : ∀ a, ∑ c ∈ Finset.range (2 * K * (a + 1) + 1), Wk1 K (2 * (a + 1)) c * (if P a c then W else 0)
      ≤ ∑ c ∈ Finset.Ioc β (β + E), Wk1 K (2 * (a + 1)) c * (if P a c then W else 0) := by
    intro a
    calc _ = ∑ c ∈ Finset.range (2 * K * (a + 1) + 1), (if c ∈ Finset.Ioc β (β + E) then
            Wk1 K (2 * (a + 1)) c * (if P a c then W else 0) else 0) := by
          apply Finset.sum_congr rfl; intro c _
          by_cases hc : c ∈ Finset.Ioc β (β + E)
          · rw [if_pos hc]
          · rw [if_neg hc]
            have hnP : ¬ P a c := fun h => hc (by
              obtain ⟨h1, h2, -⟩ := hP a c h; exact Finset.mem_Ioc.2 ⟨h1, h2⟩)
            rw [if_neg hnP, mul_zero]
      _ = ∑ c ∈ Finset.range (2 * K * (a + 1) + 1) ∩ Finset.Ioc β (β + E),
            Wk1 K (2 * (a + 1)) c * (if P a c then W else 0) := Finset.sum_ite_mem _ _ _
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_right (fun c _ _ => hf0 a c)
  calc _ ≤ ∑ a ∈ Finset.range r, ∑ c ∈ Finset.Ioc β (β + E),
        Wk1 K (2 * (a + 1)) c * (if P a c then W else 0) := Finset.sum_le_sum (fun a _ => h1 a)
    _ = ∑ c ∈ Finset.Ioc β (β + E), ∑ a ∈ Finset.range r,
        Wk1 K (2 * (a + 1)) c * (if P a c then W else 0) := Finset.sum_comm
    _ ≤ ∑ c ∈ Finset.Ioc β (β + E), W * ((2 * ((⌊ε * 2 ^ (c - β) + 1⌋₊ : ℕ) : ℝ) + 1) *
        (1 / (4 * ((2 ^ (c - β + B0 - 3) : ℕ) : ℝ)) +
          3 * (((c - 1).choose ((c - 1) / 2) : ℝ) * ((1 : ℝ) / 2) ^ c))) := by
        apply Finset.sum_le_sum; intro c hc
        rw [Finset.mem_Ioc] at hc
        have hc1 : c - 1 + 1 = c := by omega
        have hcore := W4_core K (c - 1) r (c - β + B0) n ⌊ε * 2 ^ (c - β) + 1⌋₊ m hm (fun a => P a c) (by
          intro a hPa
          obtain ⟨-, -, h9, Y, hd, hY, hs⟩ := hP a c hPa
          obtain ⟨k, hk, hdv⟩ := W4_arith n (a + 1) c β B0 X Y m ε hd hX (by omega) hY hs h9
          refine ⟨k, ?_, hdv⟩
          have hk' : |(k : ℝ)| ≤ ε * 2 ^ (c - β) + 1 := hk
          have hnat : k.natAbs ≤ ⌊ε * 2 ^ (c - β) + 1⌋₊ := by
            apply Nat.le_floor
            simp only [Nat.cast_natAbs, Int.cast_abs]; exact hk'
          have habs : |k| = (k.natAbs : ℤ) := (Int.natCast_natAbs k).symm
          rw [habs]; exact_mod_cast hnat)
        rw [hc1] at hcore
        have hsum : ∑ a ∈ Finset.range r, Wk1 K (2 * (a + 1)) c * (if P a c then W else 0) =
            W * ∑ a ∈ Finset.range r, (if P a c then Wk1 K (2 * (a + 1)) c else 0) := by
          rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro a _; split_ifs <;> ring
        rw [hsum]; exact mul_le_mul_of_nonneg_left hcore hW
    _ = _ := by rw [← Finset.mul_sum]


lemma row_chernoffD (D0 : ℕ) (δ : ℝ) (hδ : 0 < δ) : ∃ β1 : ℕ, ∀ β : ℕ, β1 ≤ β → ∀ as K : ℕ,
    3 * β ≤ 10 * as + D0 → ∑ c ∈ Finset.range (β + 1), Wk1 K (2 * as) c ≤ δ := by
  set q : ℝ := (5 / 4) ^ 5 * (2 / 3) ^ 3 with hq
  have hq0 : 0 ≤ q := by positivity
  have hq1 : q < 1 := by rw [hq]; norm_num
  have hc : (0 : ℝ) < (3 / 2) ^ D0 := by positivity
  obtain ⟨β1, hβ1⟩ := exists_pow_lt_of_lt_one (show 0 < δ ^ 5 / (3 / 2) ^ D0 by positivity) hq1
  refine ⟨β1, fun β hβ as K h => ?_⟩
  have hlow := Wk1_low K (2 * as) β (4 / 5) (by norm_num) (by norm_num)
  have e1 : (1 / (4 / 5 : ℝ)) = 5 / 4 := by norm_num
  have e2 : ((4 / 5 : ℝ) / (2 - 4 / 5)) = 2 / 3 := by norm_num
  rw [e1, e2] at hlow
  have a1 : ((5 / 4 : ℝ) ^ β * (2 / 3) ^ (2 * as)) ^ 5 = ((5 / 4 : ℝ) ^ 5) ^ β * (2 / 3 : ℝ) ^ (10 * as) := by
    rw [mul_pow, pow_right_comm (5 / 4 : ℝ) β 5, ← pow_mul (2 / 3 : ℝ) (2 * as) 5, show 2 * as * 5 = 10 * as by ring]
  have a2 : (2 / 3 : ℝ) ^ (10 * as) = (2 / 3) ^ (10 * as + D0) * (3 / 2) ^ D0 := by
    rw [pow_add, mul_assoc, ← mul_pow, show (2 / 3 : ℝ) * (3 / 2) = 1 by norm_num, one_pow, mul_one]
  have a3 : (2 / 3 : ℝ) ^ (10 * as + D0) ≤ (2 / 3) ^ (3 * β) :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) h
  have a4 : q ^ β = ((5 / 4 : ℝ) ^ 5) ^ β * (2 / 3) ^ (3 * β) := by
    rw [hq, mul_pow, ← pow_mul (2 / 3 : ℝ) 3 β]
  have hX5 : ((5 / 4 : ℝ) ^ β * (2 / 3) ^ (2 * as)) ^ 5 ≤ (3 / 2) ^ D0 * q ^ β := by
    rw [a1, a2, a4]
    have := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right a3 hc.le)
      (by positivity : (0 : ℝ) ≤ ((5 / 4 : ℝ) ^ 5) ^ β)
    linarith
  have hqβ : q ^ β ≤ q ^ β1 := pow_le_pow_of_le_one hq0 hq1.le hβ
  have hX5' : ((5 / 4 : ℝ) ^ β * (2 / 3) ^ (2 * as)) ^ 5 < δ ^ 5 := by
    have h1 := mul_le_mul_of_nonneg_left hqβ hc.le
    have h2 := mul_lt_mul_of_pos_left hβ1 hc
    have h3 : (3 / 2 : ℝ) ^ D0 * (δ ^ 5 / (3 / 2) ^ D0) = δ ^ 5 := by field_simp
    linarith
  have hXδ : (5 / 4 : ℝ) ^ β * (2 / 3) ^ (2 * as) ≤ δ := by
    by_contra hc'; push_neg at hc'
    have := pow_lt_pow_left₀ hc' hδ.le (by norm_num : (5 : ℕ) ≠ 0)
    linarith
  exact hlow.trans hXδ


/-! ## W7e (session 35): Case 3 assembly (`Case3Hyp ε` from the W1-W7 pieces). -/

lemma ev_small (C x τ : ℝ) (hx0 : 0 ≤ x) (hx1 : x < 1) (hτ : 0 < τ) :
    ∀ᶠ t : ℕ in Filter.atTop, C * (((t : ℝ) + 1) * x ^ t) < τ := by
  have h1 := tendsto_self_mul_const_pow_of_lt_one hx0 hx1
  have h2 := tendsto_pow_atTop_nhds_zero_of_lt_one hx0 hx1
  have h3 : Filter.Tendsto (fun t : ℕ => C * (((t : ℝ) + 1) * x ^ t)) Filter.atTop (nhds (C * (0 + 0))) :=
    ((h1.add h2).const_mul C).congr (fun t => by ring)
  rw [show C * (0 + 0 : ℝ) = 0 by ring] at h3
  exact h3.eventually (gt_mem_nhds hτ)

lemma T_bound (ε γ : ℝ) (hε : 0 ≤ ε) (β E t : ℕ) (ht : 2 ≤ t)
    (hF : ∀ c, β < c → ((c - 1).choose ((c - 1) / 2) : ℝ) * ((1 : ℝ) / 2) ^ c ≤ γ) :
    ∑ c ∈ Finset.Ioc β (β + E), (2 * ((⌊ε * 2 ^ (c - β) + 1⌋₊ : ℕ) : ℝ) + 1) *
        (1 / (4 * ((2 ^ (c - β + 2 * t - 3) : ℕ) : ℝ)) +
          3 * (((c - 1).choose ((c - 1) / 2) : ℝ) * ((1 : ℝ) / 2) ^ c)) ≤
      (E : ℝ) * (2 * (2 * ε + 3) * (1 / 4) ^ t) + (E : ℝ) * ((2 * ε * 2 ^ E + 3) * (3 * γ)) := by
  have hterm : ∀ c ∈ Finset.Ioc β (β + E), (2 * ((⌊ε * 2 ^ (c - β) + 1⌋₊ : ℕ) : ℝ) + 1) *
        (1 / (4 * ((2 ^ (c - β + 2 * t - 3) : ℕ) : ℝ)) +
          3 * (((c - 1).choose ((c - 1) / 2) : ℝ) * ((1 : ℝ) / 2) ^ c)) ≤
      2 * (2 * ε + 3) * (1 / 4) ^ t + (2 * ε * 2 ^ E + 3) * (3 * γ) := by
    intro c hc
    rw [Finset.mem_Ioc] at hc
    have hFc := hF c hc.1
    have he1 : 1 ≤ c - β := by omega
    have heE : c - β ≤ E := by omega
    have hfl : ((⌊ε * 2 ^ (c - β) + 1⌋₊ : ℕ) : ℝ) ≤ ε * 2 ^ (c - β) + 1 := Nat.floor_le (by positivity)
    have hfl0 : (0 : ℝ) ≤ ((⌊ε * 2 ^ (c - β) + 1⌋₊ : ℕ) : ℝ) := Nat.cast_nonneg _
    have hp1 : (1 : ℝ) ≤ 2 ^ (c - β) := one_le_pow₀ (by norm_num)
    have hpE : (2 : ℝ) ^ (c - β) ≤ 2 ^ E := pow_le_pow_right₀ (by norm_num) heE
    have hG1 : 2 * ((⌊ε * 2 ^ (c - β) + 1⌋₊ : ℕ) : ℝ) + 1 ≤ (2 * ε + 3) * 2 ^ (c - β) := by (first | linarith | nlinarith)
    have hG2 : 2 * ((⌊ε * 2 ^ (c - β) + 1⌋₊ : ℕ) : ℝ) + 1 ≤ 2 * ε * 2 ^ E + 3 := by (first | linarith | nlinarith)
    have hNat : 2 ^ (c - β + 2 * t - 3) * 8 = 2 ^ (c - β) * 4 ^ t := by
      have h3 : c - β + 2 * t - 3 + 3 = c - β + 2 * t := by omega
      calc 2 ^ (c - β + 2 * t - 3) * 8 = 2 ^ (c - β + 2 * t - 3 + 3) := by rw [pow_add]; norm_num
        _ = 2 ^ (c - β + 2 * t) := by rw [h3]
        _ = 2 ^ (c - β) * 4 ^ t := by rw [pow_add, pow_mul]; norm_num
    have hReal : ((2 ^ (c - β + 2 * t - 3) : ℕ) : ℝ) * 8 = 2 ^ (c - β) * 4 ^ t := by exact_mod_cast hNat
    have hP4 : 4 * ((2 ^ (c - β + 2 * t - 3) : ℕ) : ℝ) = 2 ^ (c - β) * 4 ^ t / 2 := by linarith
    have h4P : 0 < 4 * ((2 ^ (c - β + 2 * t - 3) : ℕ) : ℝ) := by positivity
    have h14 : (1 / 4 : ℝ) ^ t * 4 ^ t = 1 := by rw [← mul_pow]; norm_num
    have hclass : (2 * ((⌊ε * 2 ^ (c - β) + 1⌋₊ : ℕ) : ℝ) + 1) * (1 / (4 * ((2 ^ (c - β + 2 * t - 3) : ℕ) : ℝ)))
        ≤ 2 * (2 * ε + 3) * (1 / 4) ^ t := by
      rw [mul_one_div, div_le_iff₀ h4P, hP4]
      calc 2 * ((⌊ε * 2 ^ (c - β) + 1⌋₊ : ℕ) : ℝ) + 1 ≤ (2 * ε + 3) * 2 ^ (c - β) := hG1
        _ = 2 * (2 * ε + 3) * (1 / 4) ^ t * (2 ^ (c - β) * 4 ^ t / 2) := by
          rw [show 2 * (2 * ε + 3) * (1 / 4 : ℝ) ^ t * (2 ^ (c - β) * 4 ^ t / 2) =
            (2 * ε + 3) * 2 ^ (c - β) * ((1 / 4) ^ t * 4 ^ t) by ring, h14, mul_one]
    have hF0 : (0 : ℝ) ≤ ((c - 1).choose ((c - 1) / 2) : ℝ) * ((1 : ℝ) / 2) ^ c := by positivity
    have hpm : (2 * ((⌊ε * 2 ^ (c - β) + 1⌋₊ : ℕ) : ℝ) + 1) *
        (3 * (((c - 1).choose ((c - 1) / 2) : ℝ) * ((1 : ℝ) / 2) ^ c)) ≤ (2 * ε * 2 ^ E + 3) * (3 * γ) :=
      mul_le_mul hG2 (by linarith) (by linarith) (by positivity)
    rw [mul_add]
    linarith
  calc _ ≤ ∑ c ∈ Finset.Ioc β (β + E), (2 * (2 * ε + 3) * (1 / 4) ^ t + (2 * ε * 2 ^ E + 3) * (3 * γ)) :=
        Finset.sum_le_sum hterm
    _ = (E : ℝ) * (2 * (2 * ε + 3) * (1 / 4) ^ t) + (E : ℝ) * ((2 * ε * 2 ^ E + 3) * (3 * γ)) := by
        rw [Finset.sum_const, Nat.card_Ioc, nsmul_eq_mul, show β + E - β = E by omega]; ring

theorem case3_core (n K : ℕ) (ξ : ℤ) (ε : ℝ) (D : ℕ) (hε : 0 < ε) (hεD : ε * (2 ^ D + 9) < 1)
    (hD : ((D : ℝ) + 1) * (1 / 2) ^ D < 1) (hK : 2 ≤ K)
    (Sn Ee as blk B0 E r j l β : ℕ) (W : ℝ) (hW : 0 ≤ W) (hN : j + r = n / 2)
    (has : 10 * as ≤ 3 * β) (hblk : B0 / 2 + 3 ≤ blk) (hE : E = Ee + Sn * (blk * 9))
    (hasr : as ≤ r) (hase : Sn * blk + 1 ≤ as)
    (hIH : ∀ r' j' l', j' + r' = n / 2 → j < j' → j' ≤ j + as → Vt n K ξ ε r' j' l' ≤ W)
    (hB : ¬ White n ξ ε (j + 1) (l + 3)) (hb1 : (2 : ℤ) ^ β ∣ Nz n ξ (j + 1) (l + 3))
    (hb2 : ¬ (2 : ℤ) ^ (β + 1) ∣ Nz n ξ (j + 1) (l + 3)) :
    Vt n K ξ ε r j l ≤ W * (((1 - (1 - Real.exp (-ε ^ 3)) / 4 * (1 - (D + 1) * (1 / 2) ^ D)) ^ Sn
        + (Sn : ℝ) * ((blk : ℝ) * (9 ^ blk * (2 / 3) ^ (blk * 9 + 1))))
      + (((Ee : ℝ) + 1) * (1 / 2) ^ Ee)
      + ∑ c ∈ Finset.range (β + 1), Wk1 K (2 * (as - Sn * blk)) c)
      + W * ∑ c ∈ Finset.Ioc β (β + E), (2 * ((⌊ε * 2 ^ (c - β) + 1⌋₊ : ℕ) : ℝ) + 1) *
        (1 / (4 * ((2 ^ (c - β + B0 - 3) : ℕ) : ℝ)) +
          3 * (((c - 1).choose ((c - 1) / 2) : ℝ) * ((1 : ℝ) / 2) ^ c)) := by
  have h2D : (0 : ℝ) < 2 ^ D := by positivity
  have hε2 : ε < 1 / 2 := by (first | linarith | nlinarith)
  obtain ⟨m, hm⟩ := hb1
  have hmodd : ¬ (2 : ℤ) ∣ m := by
    rintro ⟨k, hk⟩
    exact hb2 ⟨k, by rw [hm, hk, pow_succ]; ring⟩
  have hBS : ∀ r' j' l', j' + r' = n / 2 → Sbad n ξ ε j l β as E B0 j' l' →
      Vt n K ξ ε r' j' l' ≤ (fun _ _ => W) j' l' :=
    fun r' j' l' h1 h2 => hIH r' j' l' h1 h2.1 h2.2.1
  have h1 := Vt_le_killN n K ξ ε hε.le (Sbad n ξ ε j l β as E B0) (fun _ _ => W) (n / 2)
    (fun _ _ => hW) hBS r j l hN
  have h2 := VisB_le K (Sbad n ξ ε j l β as E B0) (fun _ _ => W) (fun _ _ => hW) r j l
  have h3 := Sbad_sum_gen K n r β E B0 (Nz n ξ (j + 1) (l + 3)) m ε W hε.le hW hm hmodd
    (fun a c => Sbad n ξ ε j l β as E B0 (j + a + 1) (l + c))
    (fun a c h => Sbad_facts n ξ ε hε hε2 j l β as E B0 m has hm a c h)
  have h23 := h2.trans h3
  have hbaseV : ∀ r' j' l', j' + r' = n / 2 → j < j' → j' ≤ j + as → ¬ Sbad n ξ ε j l β as E B0 j' l' →
      Vk n K ξ ε (Sbad n ξ ε j l β as E B0) r' j' l' ≤ W := fun r' j' l' h1 h2 h3 _ =>
    (Vk_le_Vt n K ξ ε _ r' j' l').trans (hIH r' j' l' h1 h2 h3)
  have hρ := rho_bound K blk 9
  have hck := claim_k n K ξ ε D hε hεD hD hK (Sbad n ξ ε j l β as E B0) (n / 2) j (j + as) (l + β)
    (l + β + E) blk 9 W ((blk : ℝ) * (9 ^ blk * (2 / 3) ^ (blk * 9 + 1))) hW (by positivity)
    (by omega) (by omega) hρ hbaseV
    (hprobe_Sbad n ξ ε j l β as E B0 blk hblk _ (fun _ _ h => h))
  have hexp1 : Real.exp (-ε ^ 3) < 1 := by
    have h := Real.exp_lt_exp.mpr (show -ε ^ 3 < 0 by have := pow_pos hε 3; linarith)
    rwa [Real.exp_zero] at h
  have hexp0 : 0 < Real.exp (-ε ^ 3) := Real.exp_pos _
  have hD0 : 0 ≤ ((D : ℝ) + 1) * (1 / 2) ^ D := by positivity
  have hq0 : 0 ≤ 1 - (1 - Real.exp (-ε ^ 3)) / 4 * (1 - (D + 1) * (1 / 2) ^ D) := by
    (first | linarith [mul_le_mul_of_nonneg_right hexp1.le hD0] | nlinarith [mul_le_mul_of_nonneg_right hexp1.le hD0])
  have hQ : 0 ≤ (1 - (1 - Real.exp (-ε ^ 3)) / 4 * (1 - (D + 1) * (1 / 2) ^ D)) ^ Sn
      + (Sn : ℝ) * ((blk : ℝ) * (9 ^ blk * (2 / 3) ^ (blk * 9 + 1))) := by positivity
  have h4 := exit_W7a n K ξ ε hε.le (Sbad n ξ ε j l β as E B0) (n / 2) j l r (l + β) Ee (as - Sn * blk) W _
    hW hQ hN (by omega) (by omega) (by omega)
    (fun r' j' l' h1 h2 h3 h4 => hbaseV r' j' l' h1 h2 (by omega) h4)
    (fun r' j' l' h1 h2 h3 h4 h5 h6 => hck Sn r' j' l' h1 h2 (by omega) h4 (by omega) h6)
  rw [Nat.add_sub_cancel_left] at h4
  calc Vt n K ξ ε r j l ≤ _ := h1
    _ ≤ _ := add_le_add h4 h23
    _ = _ := by ring

lemma F_small (γ : ℝ) (hγ0 : 0 < γ) (N0 : ℕ) (hN0 : 1 / (4 * γ ^ 2) ≤ N0) : ∀ β c : ℕ, 2 * N0 + 2 ≤ β → β < c →
    ((c - 1).choose ((c - 1) / 2) : ℝ) * ((1 : ℝ) / 2) ^ c ≤ γ := by
  intro β c hβ hc
  have hW := W1b_F (c - 1)
  rw [show c - 1 + 1 = c by omega] at hW
  have hX : 1 / (4 * γ ^ 2) ≤ (((c - 1) / 2 : ℕ) : ℝ) + 1 := by
    have h3 : (N0 : ℝ) ≤ (((c - 1) / 2 : ℕ) : ℝ) := by exact_mod_cast (show N0 ≤ (c - 1) / 2 by omega)
    linarith
  by_contra hc'
  push_neg at hc'
  have h4 : γ ^ 2 * (1 / (4 * γ ^ 2)) = 1 / 4 := by
    rw [mul_one_div, div_eq_iff (by positivity)]; ring
  have h5 : γ ^ 2 < (((c - 1).choose ((c - 1) / 2) : ℝ) * ((1 : ℝ) / 2) ^ c) ^ 2 :=
    pow_lt_pow_left₀ hc' hγ0.le (by norm_num)
  have hXp : 0 < (((c - 1) / 2 : ℕ) : ℝ) + 1 := by positivity
  have k1 := mul_le_mul_of_nonneg_left hX (sq_nonneg γ)
  have k2 := mul_lt_mul_of_pos_right h5 hXp
  linarith

set_option maxHeartbeats 1000000 in
theorem case3_of (ε : ℝ) (D : ℕ) (hε : 0 < ε) (hεD : ε * (2 ^ D + 9) < 1)
    (hD : ((D : ℝ) + 1) * (1 / 2) ^ D < 1) : Case3Hyp ε := by
  intro A hA θ hθ hθ2
  have h2D : (0 : ℝ) < 2 ^ D := by positivity
  have hε2 : ε < 1 / 2 := by
    first | linarith [mul_pos hε h2D] | nlinarith [mul_pos hε h2D]
  obtain ⟨τ, hτ⟩ : ∃ τ : ℝ, τ = (25 : ℝ) ^ (-A) := ⟨_, rfl⟩
  have hτ0 : 0 < τ := by rw [hτ]; exact Real.rpow_pos_of_pos (by norm_num) _
  have hexp1 : Real.exp (-ε ^ 3) < 1 := by
    have h := Real.exp_lt_exp.mpr (show -ε ^ 3 < 0 by have := pow_pos hε 3; linarith)
    rwa [Real.exp_zero] at h
  have hq1 : 1 - (1 - Real.exp (-ε ^ 3)) / 4 * (1 - ((D : ℝ) + 1) * (1 / 2) ^ D) < 1 := by
    (first | linarith [mul_pos (sub_pos.2 hexp1) (sub_pos.2 hD)] | nlinarith [mul_pos (sub_pos.2 hexp1) (sub_pos.2 hD)])
  obtain ⟨Sn, hSn⟩ := exists_pow_lt_of_lt_one (show 0 < τ / 10 by positivity) hq1
  obtain ⟨Ee, hEe⟩ := (ev_small 1 (1 / 2) (τ / 5) (by norm_num) (by norm_num) (by positivity)).exists
  have hev1 := ev_small ((Sn : ℝ) * 3 * 9 ^ 3 * (2 / 3) ^ 28) (9 * (2 / 3) ^ 9) (τ / 10)
    (by norm_num) (by norm_num) (by positivity)
  have hev2 := ev_small (2 * (2 * ε + 3) * ((Ee : ℝ) + 27 * Sn)) (1 / 4) (τ / 5)
    (by norm_num) (by norm_num) (by positivity)
  obtain ⟨t, ht1, ht2, ht3⟩ := (hev1.and (hev2.and (Filter.eventually_ge_atTop 2))).exists
  -- the block-escape term
  have hρt : (Sn : ℝ) * (((t + 3 : ℕ) : ℝ) * (9 ^ (t + 3) * (2 / 3) ^ ((t + 3) * 9 + 1))) ≤
      (Sn : ℝ) * 3 * 9 ^ 3 * (2 / 3) ^ 28 * (((t : ℝ) + 1) * (9 * (2 / 3) ^ 9) ^ t) := by
    have e : (9 : ℝ) ^ (t + 3) * (2 / 3) ^ ((t + 3) * 9 + 1) = 9 ^ 3 * (2 / 3) ^ 28 * (9 * (2 / 3) ^ 9) ^ t := by
      rw [show (t + 3) * 9 + 1 = 9 * t + 28 by ring, pow_add, pow_add, pow_mul, mul_pow]; ring
    rw [e]; push_cast
    have h0 : (0 : ℝ) ≤ (Sn : ℝ) * (9 ^ 3 * (2 / 3) ^ 28 * (9 * (2 / 3) ^ 9) ^ t) := by positivity
    have ht0 : (0 : ℝ) ≤ t := Nat.cast_nonneg t
    first | linarith [mul_nonneg h0 ht0] | nlinarith [mul_nonneg h0 ht0]
  -- the class term
  have hEr : ((Ee + Sn * ((t + 3) * 9) : ℕ) : ℝ) ≤ ((Ee : ℝ) + 27 * Sn) * ((t : ℝ) + 1) := by
    push_cast
    have hE0 : (0 : ℝ) ≤ Ee := Nat.cast_nonneg _
    have hS0 : (0 : ℝ) ≤ Sn := Nat.cast_nonneg _
    have ht0 : (0 : ℝ) ≤ t := Nat.cast_nonneg _
    first | linarith [mul_nonneg hE0 ht0, mul_nonneg hS0 ht0] | nlinarith [mul_nonneg hE0 ht0, mul_nonneg hS0 ht0]
  have hcl : ((Ee + Sn * ((t + 3) * 9) : ℕ) : ℝ) * (2 * (2 * ε + 3) * (1 / 4) ^ t) < τ / 5 := by
    have h0 : (0 : ℝ) ≤ 2 * (2 * ε + 3) * (1 / 4) ^ t := by positivity
    have := mul_le_mul_of_nonneg_right hEr h0
    (first | linarith | nlinarith)
  -- the point-mass term: choose γ
  obtain ⟨γ, hγ0, hγb⟩ : ∃ γ : ℝ, 0 < γ ∧ ((Ee + Sn * ((t + 3) * 9) : ℕ) : ℝ) *
      ((2 * ε * 2 ^ (Ee + Sn * ((t + 3) * 9)) + 3) * (3 * γ)) ≤ τ / 5 := by
    obtain ⟨P, hP⟩ : ∃ P : ℝ, P = ((Ee + Sn * ((t + 3) * 9) : ℕ) : ℝ) *
        (2 * ε * 2 ^ (Ee + Sn * ((t + 3) * 9)) + 3) := ⟨_, rfl⟩
    have hP0 : 0 ≤ P := by rw [hP]; positivity
    refine ⟨τ / (15 * (P + 1)), by positivity, ?_⟩
    rw [show ((Ee + Sn * ((t + 3) * 9) : ℕ) : ℝ) * ((2 * ε * 2 ^ (Ee + Sn * ((t + 3) * 9)) + 3) *
        (3 * (τ / (15 * (P + 1))))) = (((Ee + Sn * ((t + 3) * 9) : ℕ) : ℝ) *
        (2 * ε * 2 ^ (Ee + Sn * ((t + 3) * 9)) + 3)) * 3 * τ / (15 * (P + 1)) by ring, ← hP,
      div_le_iff₀ (by positivity)]
    (first | linarith | nlinarith)
  obtain ⟨N0, hN0⟩ : ∃ N0 : ℕ, 1 / (4 * γ ^ 2) ≤ N0 := ⟨_, Nat.le_ceil _⟩
  have hF := F_small γ hγ0 N0 hN0
  -- Chernoff for the exit row
  obtain ⟨β1, hβ1⟩ := row_chernoffD (9 + 10 * (Sn * (t + 3))) (τ / 5) (by positivity)
  obtain ⟨βs, hβs1, hβs2, hβs3⟩ : ∃ βs : ℕ, β1 ≤ βs ∧ 2 * N0 + 2 ≤ βs ∧ 10 * (Sn * (t + 3)) + 20 ≤ βs :=
    ⟨β1 + (2 * N0 + 2) + (10 * (Sn * (t + 3)) + 20), by omega, by omega, by omega⟩
  obtain ⟨R1, hR1a, hR1b⟩ : ∃ R1 : ℕ, 11 ≤ R1 ∧ ((βs : ℝ) + 6) / θ ≤ R1 :=
    ⟨11 + ⌈((βs : ℝ) + 6) / θ⌉₊, by omega, by
      have := Nat.le_ceil (((βs : ℝ) + 6) / θ); push_cast; linarith⟩
  refine ⟨R1, ?_⟩
  intro R0 hR0 M hM n K ξ hξ hK r j l β hr hN hIH hB hb1 hb2 hθr
  have hr11 : 11 ≤ r := by omega
  have hβs : βs ≤ β := by
    by_contra hlt
    push_neg at hlt
    have h2 : ((β / 2 + 3 : ℕ) : ℝ) ≤ (βs : ℝ) + 6 := by exact_mod_cast (show β / 2 + 3 ≤ βs + 6 by omega)
    have h3 : ((βs : ℝ) + 6) / θ ≤ r := hR1b.trans (by exact_mod_cast hR0.trans hr)
    rw [div_le_iff₀ hθ] at h3
    linarith
  -- budget: 5 β < 16 r + 8
  have hJn : 2 * (j + 1 - 1) < n := by omega
  have hbud := budget_le n ξ hξ ε hε hε2 (j + 1) (l + 3) β hJn hB hb1
  rw [show j + 1 - 1 = j by omega] at hbud
  have hbudN : 2 ^ β * 9 ^ j ≤ 3 ^ n := by
    have h3n : (0 : ℝ) < 3 ^ n := by positivity
    have : (2 : ℝ) ^ β * 9 ^ j ≤ 3 ^ n := by (first | linarith | nlinarith)
    exact_mod_cast this
  have h5 : 5 * β < 16 * r + 8 := by
    have h1 : 3 ^ n ≤ 3 ^ (2 * j + 2 * r + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h2 : 3 ^ (2 * j + 2 * r + 1) = 9 ^ j * (3 * 9 ^ r) := by
      rw [pow_add, pow_add, pow_mul, pow_mul]; ring
    have h9 : 0 < 9 ^ j := by positivity
    have h3 : 2 ^ β ≤ 3 * 9 ^ r := by
      have := hbudN.trans (h1.trans h2.le)
      rw [mul_comm (2 ^ β)] at this
      exact Nat.le_of_mul_le_mul_left this h9
    have h4 : (2 ^ β) ^ 5 ≤ (3 * 9 ^ r) ^ 5 := Nat.pow_le_pow_left h3 5
    have e1 : (3 * 9 ^ r) ^ 5 = 243 * 59049 ^ r := by
      rw [mul_pow, ← pow_mul, mul_comm r 5, pow_mul]; norm_num
    have e2 : 2 ^ (16 * r + 8) = 256 * 65536 ^ r := by
      rw [pow_add, pow_mul, mul_comm]; norm_num
    have e3 : 59049 ^ r ≤ 65536 ^ r := Nat.pow_le_pow_left (by norm_num) r
    have e4 : 0 < 65536 ^ r := by positivity
    have e5 : (2 ^ β) ^ 5 = 2 ^ (5 * β) := by rw [← pow_mul, mul_comm]
    by_contra hc
    push_neg at hc
    have := Nat.pow_le_pow_right (show 0 < 2 by norm_num) hc
    omega
  have hasr : 3 * β / 10 ≤ r := by omega
  have h25 : r + 1 ≤ 25 * (r - 3 * β / 10 + 1) := by omega
  -- W
  obtain ⟨W, hWdef⟩ : ∃ W : ℝ, W = M * (((r - 3 * β / 10 : ℕ) : ℝ) + 1) ^ (-A) := ⟨_, rfl⟩
  have hW0 : 0 ≤ W := by rw [hWdef]; exact mul_nonneg (by linarith) (Real.rpow_nonneg (by positivity) _)
  have hIHW : ∀ r' j' l', j' + r' = n / 2 → j < j' → j' ≤ j + 3 * β / 10 → Vt n K ξ ε r' j' l' ≤ W := by
    intro r' j' l' h1 h2 h3
    refine (hIH r' j' l' (by omega) h1).trans ?_
    rw [hWdef]
    apply mul_le_mul_of_nonneg_left _ (by linarith)
    apply rpow_neg_anti A hA.le _ _ (by positivity)
    have : ((r - 3 * β / 10 : ℕ) : ℝ) ≤ (r' : ℝ) := by exact_mod_cast (show r - 3 * β / 10 ≤ r' by omega)
    linarith
  have hcore := case3_core n K ξ ε D hε hεD hD hK Sn Ee (3 * β / 10) (t + 3) (2 * t) (Ee + Sn * ((t + 3) * 9))
    r j l β W hW0 hN (by omega) (by omega) rfl hasr (by omega) hIHW hB hb1 hb2
  have hT := T_bound ε γ hε.le β (Ee + Sn * ((t + 3) * 9)) t ht3 (fun c hc => hF β c (by omega) hc)
  have hch := hβ1 β (by omega) (3 * β / 10 - Sn * (t + 3)) K (by omega)
  have hsum : ((1 - (1 - Real.exp (-ε ^ 3)) / 4 * (1 - (D + 1) * (1 / 2) ^ D)) ^ Sn
        + (Sn : ℝ) * (((t + 3 : ℕ) : ℝ) * (9 ^ (t + 3) * (2 / 3) ^ ((t + 3) * 9 + 1))))
      + (((Ee : ℝ) + 1) * (1 / 2) ^ Ee)
      + ∑ c ∈ Finset.range (β + 1), Wk1 K (2 * (3 * β / 10 - Sn * (t + 3))) c
      + ∑ c ∈ Finset.Ioc β (β + (Ee + Sn * ((t + 3) * 9))), (2 * ((⌊ε * 2 ^ (c - β) + 1⌋₊ : ℕ) : ℝ) + 1) *
        (1 / (4 * ((2 ^ (c - β + 2 * t - 3) : ℕ) : ℝ)) +
          3 * (((c - 1).choose ((c - 1) / 2) : ℝ) * ((1 : ℝ) / 2) ^ c)) ≤ τ := by
    linarith
  have hfin : W * τ ≤ M * ((r : ℝ) + 1) ^ (-A) := by
    rw [hWdef, hτ, mul_assoc, ← Real.mul_rpow (by positivity) (by norm_num)]
    apply mul_le_mul_of_nonneg_left _ (by linarith)
    apply rpow_neg_anti A hA.le _ _ (by positivity)
    have : ((r : ℝ) + 1) ≤ 25 * (((r - 3 * β / 10 : ℕ) : ℝ) + 1) := by exact_mod_cast h25
    linarith
  calc Vt n K ξ ε r j l ≤ _ := hcore
    _ = W * (((1 - (1 - Real.exp (-ε ^ 3)) / 4 * (1 - (D + 1) * (1 / 2) ^ D)) ^ Sn
        + (Sn : ℝ) * (((t + 3 : ℕ) : ℝ) * (9 ^ (t + 3) * (2 / 3) ^ ((t + 3) * 9 + 1))))
      + (((Ee : ℝ) + 1) * (1 / 2) ^ Ee)
      + ∑ c ∈ Finset.range (β + 1), Wk1 K (2 * (3 * β / 10 - Sn * (t + 3))) c
      + ∑ c ∈ Finset.Ioc β (β + (Ee + Sn * ((t + 3) * 9))), (2 * ((⌊ε * 2 ^ (c - β) + 1⌋₊ : ℕ) : ℝ) + 1) *
        (1 / (4 * ((2 ^ (c - β + 2 * t - 3) : ℕ) : ℝ)) +
          3 * (((c - 1).choose ((c - 1) / 2) : ℝ) * ((1 : ℝ) / 2) ^ c))) := by ring
    _ ≤ W * τ := mul_le_mul_of_nonneg_left hsum hW0
    _ ≤ _ := hfin

def VRec (n K : ℕ) (ξ : ℤ) (ε : ℝ) (V : ℕ → ℕ → ℕ → ℝ) : Prop :=
  (∀ j l : ℕ, V 0 j l = 1) ∧ ∀ r j l : ℕ, V (r + 1) j l =
    ∑ u ∈ Fintype.piFinset (fun _ : Fin 2 => Finset.Icc 1 K), ((1 : ℝ) / 2) ^ (∑ i, u i) *
      (if (∑ i, u i) = 3 ∧
          ε * 3 ^ n < ((((ξ : ZMod (3 ^ n)) * 9 ^ (j + 1 - 1) *
            ((2 : ZMod (3 ^ n))⁻¹) ^ (l + ∑ i, u i - 1)).val : ℕ) : ℝ) ∧
          ((((ξ : ZMod (3 ^ n)) * 9 ^ (j + 1 - 1) *
            ((2 : ZMod (3 ^ n))⁻¹) ^ (l + ∑ i, u i - 1)).val : ℕ) : ℝ) < (1 - ε) * 3 ^ n
        then Real.exp (-ε ^ 3) else 1) * V r (j + 1) (l + ∑ i, u i)

theorem Vt_rec (n K : ℕ) (ξ : ℤ) (ε : ℝ) : VRec n K ξ ε (Vt n K ξ ε) := by
  refine ⟨fun j l => rfl, fun r j l => Finset.sum_congr rfl fun u _ => ?_⟩
  exact congrArg (· * Vt n K ξ ε r (j + 1) (l + ∑ i, u i))
    (congrArg (((1 : ℝ) / 2) ^ (∑ i, u i) * ·) (by
      unfold cf White thZ
      split_ifs with h1 h2 h2 <;> first | rfl | (exact absurd h1 h2) | (exact absurd h2 h1)))

theorem eq_Vt_of_rec (n K : ℕ) (ξ : ℤ) (ε : ℝ) (V : ℕ → ℕ → ℕ → ℝ) (h : VRec n K ξ ε V) :
    ∀ r j l, V r j l = Vt n K ξ ε r j l := by
  intro r
  induction r with
  | zero => intro j l; rw [h.1]; rfl
  | succ r ih =>
    intro j l
    rw [h.2, (Vt_rec n K ξ ε).2]
    simp only [ih]



end Tao31

open Tao31 in
theorem solution :
    ∀ ε : ℝ, 0 < ε → ε < 1 / 100 → ∀ A : ℝ, 0 < A → ∀ θ : ℝ, 0 < θ → θ ≤ 1 / 2 →
      ∃ R1 : ℕ, ∀ R0 : ℕ, R1 ≤ R0 → ∀ M : ℝ, 1 ≤ M →
      ∀ n K : ℕ, ∀ ξ : ℤ, ¬ (3 : ℤ) ∣ ξ → 2 ≤ K → ∀ V : ℕ → ℕ → ℕ → ℝ,
        (∀ j l : ℕ, V 0 j l = 1) →
        (∀ r j l : ℕ, V (r + 1) j l =
          ∑ u ∈ Fintype.piFinset (fun _ : Fin 2 => Finset.Icc 1 K), ((1 : ℝ) / 2) ^ (∑ i, u i) *
            (if (∑ i, u i) = 3 ∧
                ε * 3 ^ n < ((((ξ : ZMod (3 ^ n)) * 9 ^ (j + 1 - 1) *
                  ((2 : ZMod (3 ^ n))⁻¹) ^ (l + ∑ i, u i - 1)).val : ℕ) : ℝ) ∧
                ((((ξ : ZMod (3 ^ n)) * 9 ^ (j + 1 - 1) *
                  ((2 : ZMod (3 ^ n))⁻¹) ^ (l + ∑ i, u i - 1)).val : ℕ) : ℝ) < (1 - ε) * 3 ^ n
              then Real.exp (-ε ^ 3) else 1) * V r (j + 1) (l + ∑ i, u i)) →
        ∀ r j l β : ℕ, R0 ≤ r → j + r = n / 2 →
        (∀ r' j' l' : ℕ, r' < r → j' + r' = n / 2 → V r' j' l' ≤ M * ((r' : ℝ) + 1) ^ (-A)) →
        ¬ (ε * 3 ^ n < ((((ξ : ZMod (3 ^ n)) * 9 ^ (j + 1 - 1) * ((2 : ZMod (3 ^ n))⁻¹) ^ (l + 3 - 1)).val : ℕ) : ℝ) ∧
            ((((ξ : ZMod (3 ^ n)) * 9 ^ (j + 1 - 1) * ((2 : ZMod (3 ^ n))⁻¹) ^ (l + 3 - 1)).val : ℕ) : ℝ) < (1 - ε) * 3 ^ n) →
        (2 : ℤ) ^ β ∣ ((ξ : ZMod (3 ^ n)) * 9 ^ (j + 1 - 1) * ((2 : ZMod (3 ^ n))⁻¹) ^ (l + 3 - 1)).valMinAbs →
        ¬ (2 : ℤ) ^ (β + 1) ∣ ((ξ : ZMod (3 ^ n)) * 9 ^ (j + 1 - 1) * ((2 : ZMod (3 ^ n))⁻¹) ^ (l + 3 - 1)).valMinAbs →
        θ * r < ((β / 2 + 3 : ℕ) : ℝ) →
        V r j l ≤ M * ((r : ℝ) + 1) ^ (-A) := by
  intro ε hε hε1 A hA θ hθ hθ2
  obtain ⟨R1, hR1⟩ := case3_of ε 2 hε (by norm_num; linarith) (by norm_num) A hA θ hθ hθ2
  refine ⟨R1, fun R0 hR0 M hM n K ξ hξ hK V h0 h1 r j l β hr hjr hind hW hb hb1 hθr => ?_⟩
  have hV := eq_Vt_of_rec n K ξ ε V ⟨h0, h1⟩
  rw [hV]
  refine hR1 R0 hR0 M hM n K ξ hξ hK r j l β hr hjr (fun r' j' l' h1' h2' => ?_) hW hb hb1 hθr
  rw [← hV]
  exact hind r' j' l' h1' h2'
