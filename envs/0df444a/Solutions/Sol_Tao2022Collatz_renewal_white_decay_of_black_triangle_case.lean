-- Prove2me | solution 1 for Tao2022Collatz.renewal_white_decay_of_black_triangle_case
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-12T01:24:50.905733+00:00
-- url     : https://prove2.me/submissions/b5cbb8c1-6c37-4851-b725-f37311112cad

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

lemma weight_ratio (A η : ℝ) (hA : 0 ≤ A) (hη : 0 < η) (hη1 : η < 1) :
    ∃ R0 : ℕ, ∀ r : ℕ, R0 ≤ r → 1 ≤ r → (1 - η) * (((r : ℝ) + 1) / r) ^ A ≤ 1 := by
  set δ := Real.log (1 / (1 - η)) with hδ
  have h1η : 0 < 1 - η := by linarith
  have hδ0 : 0 < δ := Real.log_pos (by rw [lt_div_iff₀ h1η]; linarith)
  refine ⟨⌈A / δ⌉₊ + 1, fun r hr hr1 => ?_⟩
  have hr0 : (0 : ℝ) < r := by exact_mod_cast hr1
  have hrA : A / r ≤ δ := by
    have : A / δ < r := by
      have := Nat.le_ceil (A / δ)
      have h' : ((⌈A / δ⌉₊ + 1 : ℕ) : ℝ) ≤ r := by exact_mod_cast hr
      push_cast at h'; linarith
    rw [div_le_iff₀ hr0]; rw [div_lt_iff₀ hδ0] at this; linarith
  have hb : ((r : ℝ) + 1) / r = 1 + 1 / r := by field_simp
  have he : (1 + 1 / (r : ℝ)) ^ A ≤ Real.exp (A / r) := by
    calc (1 + 1 / (r : ℝ)) ^ A ≤ (Real.exp (1 / r)) ^ A := by
          apply Real.rpow_le_rpow (by positivity) _ hA
          have := Real.add_one_le_exp (1 / (r : ℝ)); linarith
      _ = Real.exp (A / r) := by rw [← Real.exp_mul]; congr 1; ring
  have he2 : Real.exp (A / r) ≤ 1 / (1 - η) := by
    calc Real.exp (A / r) ≤ Real.exp δ := Real.exp_le_exp.2 hrA
      _ = 1 / (1 - η) := by rw [hδ, Real.exp_log (by positivity)]
  rw [hb]
  calc (1 - η) * (1 + 1 / (r : ℝ)) ^ A ≤ (1 - η) * (1 / (1 - η)) :=
        mul_le_mul_of_nonneg_left (he.trans he2) h1η.le
    _ = 1 := by field_simp


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

theorem black_run (n K : ℕ) (ξ : ℤ) (ε : ℝ) (D : ℕ) (hε : 0 < ε) (hεD : ε * (2 ^ D + 9) < 1)
    (hK : 2 ≤ K) (h : ℝ) (hh : 0 ≤ h) :
    ∀ β r j l, β / 2 + 3 ≤ r → ¬ White n ξ ε (j + 1) (l + 3) →
      (2 : ℤ) ^ β ∣ Nz n ξ (j + 1) (l + 3) → ¬ (2 : ℤ) ^ (β + 1) ∣ Nz n ξ (j + 1) (l + 3) →
      (∀ t l', 1 ≤ t → t ≤ β / 2 + 3 → Vt n K ξ ε (r - t) (j + t) l' ≤ h) →
      Vt n K ξ ε r j l ≤ h * (1 - (1 - Real.exp (-ε ^ 3)) / 4 * (1 - (D + 1) * (1 / 2) ^ D)) := by
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
  have hterm : ∀ u ∈ Box 2 K, Vt n K ξ ε (r'' + 1) (j + 1) (l + ∑ i, u i) ≤ g (∑ i, u i) := by
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
    have hWcase : White n ξ ε (j + 1 + 1) (l + s + 3) →
        Vt n K ξ ε (r'' + 1) (j + 1) (l + s) ≤ g s := by
      intro hW
      refine le_trans ?_ hgw
      rw [Vt]
      refine step_white n K ξ ε hε.le hK (j + 1) (l + s) hW
        (fun b => Vt n K ξ ε r'' (j + 1 + 1) (l + s + b)) h
        (fun b => Vt_nonneg n K ξ ε _ _ _) (fun b => ?_)
      have := hV 2 (l + s + b) (by norm_num) (by omega)
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
        have hV' : ∀ t l', 1 ≤ t → t ≤ (β - s) / 2 + 3 →
            Vt n K ξ ε (r'' + 1 - t) (j + 1 + t) l' ≤ h := by
          intro t l' ht1 ht2
          have := hV (t + 1) l' (by omega) (by omega)
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
      · have hv1 := hV 1 (l + s) le_rfl (by omega)
        rw [show r'' + 1 + 1 - 1 = r'' + 1 by omega] at hv1
        have hgs : g s = h := by
          simp only [hg, if_neg hsb, if_pos (by omega : β + D < s)]
          ring
        linarith
  rw [Vt]
  have hsum : ∑ u ∈ Box 2 K, ((1 : ℝ) / 2) ^ (∑ i, u i) * cf n ξ ε (j + 1) (l + ∑ i, u i) (∑ i, u i) *
      Vt n K ξ ε (r'' + 1) (j + 1) (l + ∑ i, u i)
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

lemma rpow_neg_split (A x y : ℝ) (hx : 0 < x) (hy : 0 < y) : x ^ (-A) = y ^ (-A) * (y / x) ^ A := by
  have hyA : 0 < y ^ A := Real.rpow_pos_of_pos hy A
  rw [Real.div_rpow hy.le hx.le, Real.rpow_neg hx.le, Real.rpow_neg hy.le, div_eq_mul_inv, ← mul_assoc,
    inv_mul_cancel₀ hyA.ne', one_mul]

lemma rpow_neg_anti (A : ℝ) (hA : 0 ≤ A) (x y : ℝ) (hx : 0 < x) (hxy : x ≤ y) : y ^ (-A) ≤ x ^ (-A) := by
  rw [Real.rpow_neg hx.le, Real.rpow_neg (hx.le.trans hxy)]
  exact inv_anti₀ (Real.rpow_pos_of_pos hx A) (Real.rpow_le_rpow hx.le hxy hA)

lemma theta_exists (A η : ℝ) (hA : 0 < A) (hη : 0 < η) (hη1 : η < 1) :
    ∃ θ : ℝ, 0 < θ ∧ θ ≤ 1 / 2 ∧ (1 - η) * (1 / (1 - θ)) ^ A ≤ 1 := by
  set δ := Real.log (1 / (1 - η)) with hδ
  have h1η : 0 < 1 - η := by linarith
  have hδ0 : 0 < δ := Real.log_pos (by rw [lt_div_iff₀ h1η]; linarith)
  have hθ0 : 0 < min (1 / 2) (δ / (2 * A)) := lt_min (by norm_num) (by positivity)
  refine ⟨min (1 / 2) (δ / (2 * A)), hθ0, min_le_left _ _, ?_⟩
  set θ := min (1 / 2) (δ / (2 * A)) with hθdef
  have hθ1 : θ ≤ 1 / 2 := min_le_left _ _
  have hθ2 : θ ≤ δ / (2 * A) := min_le_right _ _
  have hθ3 : θ * (2 * A) ≤ δ := (le_div_iff₀ (by positivity)).1 hθ2
  have hb : 1 / (1 - θ) ≤ Real.exp (2 * θ) := by
    have h1 : 1 / (1 - θ) ≤ 1 + 2 * θ := by
      rw [div_le_iff₀ (by linarith)]; (first | linarith | nlinarith)
    have h2 := Real.add_one_le_exp (2 * θ)
    linarith
  have he : (1 / (1 - θ)) ^ A ≤ Real.exp (2 * θ * A) := by
    have hpos : 0 < 1 / (1 - θ) := by
      have : 0 < 1 - θ := by linarith
      positivity
    calc (1 / (1 - θ)) ^ A ≤ (Real.exp (2 * θ)) ^ A := Real.rpow_le_rpow hpos.le hb hA.le
      _ = Real.exp (2 * θ * A) := by rw [← Real.exp_mul]
  have he2 : Real.exp (2 * θ * A) ≤ 1 / (1 - η) := by
    calc Real.exp (2 * θ * A) ≤ Real.exp δ := Real.exp_le_exp.2 (by linarith)
      _ = 1 / (1 - η) := by rw [hδ, Real.exp_log (by positivity)]
  calc (1 - η) * (1 / (1 - θ)) ^ A ≤ (1 - η) * (1 / (1 - η)) :=
        mul_le_mul_of_nonneg_left (he.trans he2) h1η.le
    _ = 1 := by field_simp

theorem vt_induct (n K : ℕ) (ξ : ℤ) (hξ : ¬ (3 : ℤ) ∣ ξ) (ε : ℝ) (D : ℕ) (hε : 0 < ε)
    (hεD : ε * (2 ^ D + 9) < 1) (hK : 2 ≤ K) (A : ℝ) (hA : 0 ≤ A) (θ : ℝ) (hθ0 : 0 ≤ θ) (hθ1 : θ < 1)
    (hθ : (1 - (1 - Real.exp (-ε ^ 3)) / 4 * (1 - (D + 1) * (1 / 2) ^ D)) * (1 / (1 - θ)) ^ A ≤ 1)
    (R0 : ℕ) (hR01 : 1 ≤ R0)
    (hR0 : ∀ r : ℕ, R0 ≤ r → 1 ≤ r → (1 - (1 - Real.exp (-ε ^ 3)) / 4) * (((r : ℝ) + 1) / r) ^ A ≤ 1)
    (M : ℝ) (hM : ∀ r : ℕ, r < R0 → 1 ≤ M * ((r : ℝ) + 1) ^ (-A))
    (h3 : ∀ r j l β : ℕ, R0 ≤ r → j + r = n / 2 →
      (∀ r' j' l' : ℕ, r' < r → j' + r' = n / 2 → Vt n K ξ ε r' j' l' ≤ M * ((r' : ℝ) + 1) ^ (-A)) →
      ¬ White n ξ ε (j + 1) (l + 3) → (2 : ℤ) ^ β ∣ Nz n ξ (j + 1) (l + 3) →
      ¬ (2 : ℤ) ^ (β + 1) ∣ Nz n ξ (j + 1) (l + 3) → θ * r < ((β / 2 + 3 : ℕ) : ℝ) →
      Vt n K ξ ε r j l ≤ M * ((r : ℝ) + 1) ^ (-A)) :
    ∀ r j l : ℕ, j + r = n / 2 → Vt n K ξ ε r j l ≤ M * ((r : ℝ) + 1) ^ (-A) := by
  have hM1 : 1 ≤ M := by have := hM 0 (by omega); simpa using this
  have hM0 : 0 ≤ M := by linarith
  intro r
  induction r using Nat.strong_induction_on with
  | _ r ih =>
  intro j l hjr
  have IH : ∀ r' j' l' : ℕ, r' < r → j' + r' = n / 2 → Vt n K ξ ε r' j' l' ≤ M * ((r' : ℝ) + 1) ^ (-A) :=
    fun r' j' l' h1 h2 => ih r' h1 j' l' h2
  by_cases hr : r < R0
  · exact (Vt_le_one n K ξ ε hε.le r j l).trans (hM r hr)
  push_neg at hr
  have hr1 : 1 ≤ r := le_trans hR01 hr
  obtain ⟨r', rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
  by_cases hW : White n ξ ε (j + 1) (l + 3)
  · -- Case 1: white probe
    have hF : ∀ b, Vt n K ξ ε r' (j + 1) (l + b) ≤ M * ((r' : ℝ) + 1) ^ (-A) :=
      fun b => IH r' (j + 1) (l + b) (by omega) (by omega)
    have hstep := step_white n K ξ ε hε.le hK j l hW (fun b => Vt n K ξ ε r' (j + 1) (l + b))
      (M * ((r' : ℝ) + 1) ^ (-A)) (fun b => Vt_nonneg n K ξ ε r' (j + 1) (l + b)) hF
    have hV : Vt n K ξ ε (r' + 1) j l = ∑ u ∈ Box 2 K, ((1 : ℝ) / 2) ^ (∑ i, u i) *
        cf n ξ ε (j + 1) (l + ∑ i, u i) (∑ i, u i) * Vt n K ξ ε r' (j + 1) (l + ∑ i, u i) := by
      simp only [Vt]
    rw [hV]
    refine hstep.trans ?_
    have hw := hR0 (r' + 1) hr hr1
    rw [Nat.cast_succ] at hw ⊢
    have hsplit := rpow_neg_split A ((r' : ℝ) + 1) ((r' : ℝ) + 1 + 1) (by positivity) (by positivity)
    rw [hsplit]
    have hp : 0 ≤ ((r' : ℝ) + 1 + 1) ^ (-A) := by positivity
    calc _ = M * ((r' : ℝ) + 1 + 1) ^ (-A) * ((1 - (1 - Real.exp (-ε ^ 3)) / 4) *
            (((r' : ℝ) + 1 + 1) / ((r' : ℝ) + 1)) ^ A) := by ring
      _ ≤ M * ((r' : ℝ) + 1 + 1) ^ (-A) * 1 := mul_le_mul_of_nonneg_left hw (mul_nonneg hM0 hp)
      _ = _ := by ring
  · -- black probe: exact 2-adic budget
    have hjn : 2 * (j + 1 - 1) < n := by omega
    obtain ⟨_, hNz⟩ := Nz_three_adic n ξ hξ (j + 1) (l + 3) hjn
    have hZn : (Nz n ξ (j + 1) (l + 3)).natAbs ≠ 0 := Int.natAbs_ne_zero.2 hNz
    set β := padicValNat 2 (Nz n ξ (j + 1) (l + 3)).natAbs with hβdef
    have hβ : (2 : ℤ) ^ β ∣ Nz n ξ (j + 1) (l + 3) := by
      have h := @pow_padicValNat_dvd 2 (Nz n ξ (j + 1) (l + 3)).natAbs
      exact Int.natAbs_dvd_natAbs.1 (by simpa [Int.natAbs_pow] using h)
    have hβ1 : ¬ (2 : ℤ) ^ (β + 1) ∣ Nz n ξ (j + 1) (l + 3) := by
      intro h
      have h' := Int.natAbs_dvd_natAbs.2 h
      have hnd : ¬ 2 ^ (β + 1) ∣ (Nz n ξ (j + 1) (l + 3)).natAbs := pow_succ_padicValNat_not_dvd hZn
      apply hnd
      simpa [Int.natAbs_pow] using h'
    by_cases h3c : θ * ((r' + 1 : ℕ) : ℝ) < ((β / 2 + 3 : ℕ) : ℝ)
    · exact h3 (r' + 1) j l β hr hjr IH hW hβ hβ1 h3c
    · -- Case 2: small budget, `black_run`
      push_neg at h3c
      have hsr : β / 2 + 3 ≤ r' + 1 := by
        have : ((β / 2 + 3 : ℕ) : ℝ) ≤ ((r' + 1 : ℕ) : ℝ) := by
          calc ((β / 2 + 3 : ℕ) : ℝ) ≤ θ * ((r' + 1 : ℕ) : ℝ) := h3c
            _ ≤ 1 * ((r' + 1 : ℕ) : ℝ) := mul_le_mul_of_nonneg_right hθ1.le (by positivity)
            _ = _ := one_mul _
        exact_mod_cast this
      have hh0 : 0 ≤ M * (((r' + 1 - (β / 2 + 3) : ℕ) : ℝ) + 1) ^ (-A) :=
        mul_nonneg hM0 (by positivity)
      have hV : ∀ t l', 1 ≤ t → t ≤ β / 2 + 3 → Vt n K ξ ε (r' + 1 - t) (j + t) l' ≤
          M * (((r' + 1 - (β / 2 + 3) : ℕ) : ℝ) + 1) ^ (-A) := by
        intro t l' ht1 ht2
        refine (IH (r' + 1 - t) (j + t) l' (by omega) (by omega)).trans ?_
        apply mul_le_mul_of_nonneg_left _ hM0
        apply rpow_neg_anti A hA _ _ (by positivity)
        have h1 : r' + 1 - (β / 2 + 3) ≤ r' + 1 - t := by omega
        have h2 : ((r' + 1 - (β / 2 + 3) : ℕ) : ℝ) ≤ ((r' + 1 - t : ℕ) : ℝ) := by exact_mod_cast h1
        linarith
      have hbr := black_run n K ξ ε D hε hεD hK _ hh0 β (r' + 1) j l hsr hW hβ hβ1 hV
      refine hbr.trans ?_
      have hcast : ((r' + 1 - (β / 2 + 3) : ℕ) : ℝ) = ((r' + 1 : ℕ) : ℝ) - ((β / 2 + 3 : ℕ) : ℝ) :=
        Nat.cast_sub hsr
      rw [hcast]
      set R : ℝ := ((r' + 1 : ℕ) : ℝ) with hR
      set s : ℝ := ((β / 2 + 3 : ℕ) : ℝ) with hs
      have hsR : s ≤ R := by rw [hs, hR]; exact_mod_cast hsr
      have hRs : 0 < R - s + 1 := by linarith
      have hR0' : 0 ≤ R := by rw [hR]; positivity
      rw [rpow_neg_split A (R - s + 1) (R + 1) hRs (by linarith)]
      have hratio : (R + 1) / (R - s + 1) ≤ 1 / (1 - θ) := by
        rw [div_le_div_iff₀ hRs (by linarith)]
        have he : (R + 1) * (1 - θ) = R + 1 - θ * R - θ := by ring
        rw [he]; linarith
      have hpow : ((R + 1) / (R - s + 1)) ^ A ≤ (1 / (1 - θ)) ^ A :=
        Real.rpow_le_rpow (by positivity) hratio hA
      have hη0 : 0 ≤ (1 - Real.exp (-ε ^ 3)) / 4 := by
        have : Real.exp (-ε ^ 3) ≤ 1 := Real.exp_le_one_iff.2 (by have := pow_pos hε 3; linarith)
        linarith
      have hη1 : (1 - Real.exp (-ε ^ 3)) / 4 ≤ 1 / 4 := by
        have := Real.exp_pos (-ε ^ 3); linarith
      have hδ0 : (0 : ℝ) ≤ ((D : ℝ) + 1) * (1 / 2) ^ D := by positivity
      have hq : 0 ≤ 1 - (1 - Real.exp (-ε ^ 3)) / 4 * (1 - ((D : ℝ) + 1) * (1 / 2) ^ D) := by (first | linarith | nlinarith)
      have hp : 0 ≤ (R + 1) ^ (-A) := by positivity
      calc _ = M * (R + 1) ^ (-A) * ((1 - (1 - Real.exp (-ε ^ 3)) / 4 * (1 - ((D : ℝ) + 1) * (1 / 2) ^ D)) *
            ((R + 1) / (R - s + 1)) ^ A) := by ring
        _ ≤ M * (R + 1) ^ (-A) * ((1 - (1 - Real.exp (-ε ^ 3)) / 4 * (1 - ((D : ℝ) + 1) * (1 / 2) ^ D)) *
            (1 / (1 - θ)) ^ A) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hpow hq) (mul_nonneg hM0 hp)
        _ ≤ M * (R + 1) ^ (-A) * 1 := mul_le_mul_of_nonneg_left hθ (mul_nonneg hM0 hp)
        _ = _ := by ring

def Case3Hyp (ε : ℝ) : Prop :=
  ∀ A : ℝ, 0 < A → ∀ θ : ℝ, 0 < θ → θ ≤ 1 / 2 → ∃ R1 : ℕ, ∀ R0 : ℕ, R1 ≤ R0 → ∀ M : ℝ, 1 ≤ M →
    ∀ (n K : ℕ) (ξ : ℤ), ¬ (3 : ℤ) ∣ ξ → 2 ≤ K →
    ∀ r j l β : ℕ, R0 ≤ r → j + r = n / 2 →
      (∀ r' j' l' : ℕ, r' < r → j' + r' = n / 2 → Vt n K ξ ε r' j' l' ≤ M * ((r' : ℝ) + 1) ^ (-A)) →
      ¬ White n ξ ε (j + 1) (l + 3) → (2 : ℤ) ^ β ∣ Nz n ξ (j + 1) (l + 3) →
      ¬ (2 : ℤ) ^ (β + 1) ∣ Nz n ξ (j + 1) (l + 3) → θ * r < ((β / 2 + 3 : ℕ) : ℝ) →
      Vt n K ξ ε r j l ≤ M * ((r : ℝ) + 1) ^ (-A)

def Prop73e (ε : ℝ) : Prop :=
  ∀ A : ℝ, 0 < A → ∃ C : ℝ, 0 < C ∧ ∀ n K : ℕ, 1 ≤ n → n ≤ K →
    ∀ ξ : ℤ, ¬ (3 : ℤ) ∣ ξ → Vt n K ξ ε (n / 2) 0 0 ≤ C * (n : ℝ) ^ (-A)

theorem prop73_of_case3 (ε : ℝ) (D : ℕ) (hε : 0 < ε) (hε1 : ε ≤ 1) (hεD : ε * (2 ^ D + 9) < 1)
    (hD : ((D : ℝ) + 1) * (1 / 2) ^ D < 1) (h3 : Case3Hyp ε) : Prop73e ε := by
  intro A hA
  have hexp : Real.exp (-ε ^ 3) < 1 := by
    have h := Real.exp_lt_exp.2 (show -ε ^ 3 < 0 by have := pow_pos hε 3; linarith)
    rwa [Real.exp_zero] at h
  have hη0 : 0 < (1 - Real.exp (-ε ^ 3)) / 4 := by linarith
  have hη1 : (1 - Real.exp (-ε ^ 3)) / 4 < 1 := by have := Real.exp_pos (-ε ^ 3); linarith
  have hδ0 : (0 : ℝ) ≤ ((D : ℝ) + 1) * (1 / 2) ^ D := by positivity
  have hη'0 : 0 < (1 - Real.exp (-ε ^ 3)) / 4 * (1 - ((D : ℝ) + 1) * (1 / 2) ^ D) :=
    mul_pos hη0 (by linarith)
  have hη'1 : (1 - Real.exp (-ε ^ 3)) / 4 * (1 - ((D : ℝ) + 1) * (1 / 2) ^ D) < 1 := by
    calc _ ≤ (1 - Real.exp (-ε ^ 3)) / 4 * 1 := mul_le_mul_of_nonneg_left (by linarith) hη0.le
      _ < 1 := by linarith
  obtain ⟨θ, hθ0, hθ1, hθ⟩ := theta_exists A _ hA hη'0 hη'1
  obtain ⟨R0, hR0⟩ := weight_ratio A _ hA.le hη0 hη1
  obtain ⟨R1, hR1⟩ := h3 A hA θ hθ0 hθ1
  have hRpos : (0 : ℝ) ≤ (max (max R0 R1) 1 : ℕ) := Nat.cast_nonneg _
  have hM1 : 1 ≤ (((max (max R0 R1) 1 : ℕ) : ℝ) + 1) ^ A := Real.one_le_rpow (by linarith) hA.le
  refine ⟨(((max (max R0 R1) 1 : ℕ) : ℝ) + 1) ^ A * 2 ^ A, mul_pos (by linarith) (by positivity),
    fun n K hn hnK ξ hξ => ?_⟩
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have h2A : (1 : ℝ) ≤ 2 ^ A := Real.one_le_rpow (by norm_num) hA.le
  by_cases hn2 : n < 2
  · have hn1 : n = 1 := by omega
    subst hn1
    simp only [Nat.reduceDiv, Nat.cast_one, Real.one_rpow, mul_one]
    simp only [Vt]
    first
      | exact one_le_mul_of_one_le_of_one_le hM1 h2A
      | linarith [one_le_mul_of_one_le_of_one_le hM1 h2A]
      | (first | linarith [one_le_mul_of_one_le_of_one_le hM1 h2A] | nlinarith [one_le_mul_of_one_le_of_one_le hM1 h2A])
  push_neg at hn2
  have hK : 2 ≤ K := le_trans hn2 hnK
  have hM : ∀ r : ℕ, r < max (max R0 R1) 1 → 1 ≤ (((max (max R0 R1) 1 : ℕ) : ℝ) + 1) ^ A *
      ((r : ℝ) + 1) ^ (-A) := by
    intro r hr
    have hr' : (r : ℝ) + 1 ≤ ((max (max R0 R1) 1 : ℕ) : ℝ) + 1 := by
      have : (r : ℝ) ≤ ((max (max R0 R1) 1 : ℕ) : ℝ) := by exact_mod_cast hr.le
      linarith
    have hpos : (0 : ℝ) < (r : ℝ) + 1 := by positivity
    rw [Real.rpow_neg hpos.le, ← div_eq_mul_inv, one_le_div (Real.rpow_pos_of_pos hpos A)]
    exact Real.rpow_le_rpow hpos.le hr' hA.le
  have hv := vt_induct n K ξ hξ ε D hε hεD hK A hA.le θ hθ0.le (by linarith) hθ (max (max R0 R1) 1)
    (le_max_right _ _)
    (fun r hr h1 => hR0 r (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hr) h1) _ hM
    (fun r j l β => hR1 (max (max R0 R1) 1) (le_trans (le_max_right R0 R1) (le_max_left _ 1)) _ hM1
      n K ξ hξ hK r j l β) (n / 2) 0 0 (by simp)
  have hn2' : (n : ℝ) / 2 ≤ ((n / 2 : ℕ) : ℝ) + 1 := by
    have h1 : n ≤ 2 * (n / 2) + 1 := by omega
    have h2 : (n : ℝ) ≤ 2 * ((n / 2 : ℕ) : ℝ) + 1 := by exact_mod_cast h1
    linarith
  have h1 := rpow_neg_anti A hA.le ((n : ℝ) / 2) _ (by positivity) hn2'
  have h2 := rpow_neg_split A ((n : ℝ) / 2) n (by positivity) hnpos
  have h3' : (n : ℝ) / ((n : ℝ) / 2) = 2 := by
    rw [div_div_eq_mul_div]; exact mul_div_cancel_left₀ 2 hnpos.ne'
  rw [h2, h3'] at h1
  calc _ ≤ _ := hv
    _ ≤ (((max (max R0 R1) 1 : ℕ) : ℝ) + 1) ^ A * ((n : ℝ) ^ (-A) * 2 ^ A) :=
      mul_le_mul_of_nonneg_left h1 (by linarith)
    _ = _ := by ring

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
    (∀ ε : ℝ, 0 < ε → ε < 1 / 100 → ∀ A : ℝ, 0 < A → ∀ θ : ℝ, 0 < θ → θ ≤ 1 / 2 →
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
        V r j l ≤ M * ((r : ℝ) + 1) ^ (-A)) →
    ∀ ε : ℝ, 0 < ε → ε < 1 / 100 → ∀ A : ℝ, 0 < A → ∃ C : ℝ, 0 < C ∧
      ∀ n K : ℕ, 1 ≤ n → n ≤ K → ∀ ξ : ℤ, ¬ (3 : ℤ) ∣ ξ → ∀ V : ℕ → ℕ → ℕ → ℝ,
        (∀ j l : ℕ, V 0 j l = 1) →
        (∀ r j l : ℕ, V (r + 1) j l =
          ∑ u ∈ Fintype.piFinset (fun _ : Fin 2 => Finset.Icc 1 K), ((1 : ℝ) / 2) ^ (∑ i, u i) *
            (if (∑ i, u i) = 3 ∧
                ε * 3 ^ n < ((((ξ : ZMod (3 ^ n)) * 9 ^ (j + 1 - 1) *
                  ((2 : ZMod (3 ^ n))⁻¹) ^ (l + ∑ i, u i - 1)).val : ℕ) : ℝ) ∧
                ((((ξ : ZMod (3 ^ n)) * 9 ^ (j + 1 - 1) *
                  ((2 : ZMod (3 ^ n))⁻¹) ^ (l + ∑ i, u i - 1)).val : ℕ) : ℝ) < (1 - ε) * 3 ^ n
              then Real.exp (-ε ^ 3) else 1) * V r (j + 1) (l + ∑ i, u i)) →
        V (n / 2) 0 0 ≤ C * (n : ℝ) ^ (-A) := by
  intro h3 ε hε hε1 A hA
  have hc : Case3Hyp ε := by
    intro A' hA' θ hθ hθ2
    obtain ⟨R1, hR1⟩ := h3 ε hε hε1 A' hA' θ hθ hθ2
    exact ⟨R1, fun R0 hR0 M hM n K ξ hξ hK r j l β hr hjr hind hW hb hb1 hθr =>
      hR1 R0 hR0 M hM n K ξ hξ hK (Vt n K ξ ε) (Vt_rec n K ξ ε).1 (Vt_rec n K ξ ε).2
        r j l β hr hjr hind hW hb hb1 hθr⟩
  obtain ⟨C, hC, hb⟩ := prop73_of_case3 ε 2 hε (by linarith) (by norm_num; linarith) (by norm_num) hc A hA
  exact ⟨C, hC, fun n K hn hK ξ hξ V h0 h1 => by
    rw [eq_Vt_of_rec n K ξ ε V ⟨h0, h1⟩]; exact hb n K hn hK ξ hξ⟩
