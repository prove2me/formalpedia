-- Prove2me | solution 1 for VeinottWagnerSS.Bounds.theorem4a_optimal_sS_within_bounds
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-22T06:38:49.545073+00:00
-- url     : https://prove2.me/submissions/a1fe8b4c-8e7d-4c73-86bf-9302ebd20cd7

import Mathlib
import Definitions.Def_VeinottWagnerSS_Bounds_Model
import Definitions.Def_VeinottWagnerSS_Bounds_CriticalNumbers

open scoped ENNReal


namespace VeinottWagnerSS.Bounds

/-! ## K-convexity on the integers -/

/-- integer `K`-convexity, real valued -/
def KConvR (K : ℝ) (f : ℤ → ℝ) : Prop :=
  ∀ (x : ℤ) (a b : ℕ), 1 ≤ a → 1 ≤ b →
    ((a : ℝ) + b) * f x ≤ (b : ℝ) * K + (b : ℝ) * f (x + a) + (a : ℝ) * f (x - b)

/-- integer `K`-convexity, `ℝ≥0∞` valued -/
def KConvE (K : ℝ≥0∞) (f : ℤ → ℝ≥0∞) : Prop :=
  ∀ (x : ℤ) (a b : ℕ), 1 ≤ a → 1 ≤ b →
    ((a : ℝ≥0∞) + b) * f x ≤ (b : ℝ≥0∞) * K + (b : ℝ≥0∞) * f (x + a) + (a : ℝ≥0∞) * f (x - b)

lemma KConvR_mono {K K' : ℝ} (hKK : K ≤ K') {f : ℤ → ℝ} (hf : KConvR K f) : KConvR K' f := by
  intro x a b ha hb
  have := hf x a b ha hb
  have : (b : ℝ) * K ≤ b * K' := mul_le_mul_of_nonneg_left hKK (Nat.cast_nonneg _)
  linarith

lemma KConvR_add {K : ℝ} {g f : ℤ → ℝ} (hg : KConvR 0 g) (hf : KConvR K f) :
    KConvR K (fun x => g x + f x) := by
  intro x a b ha hb
  have h1 := hg x a b ha hb
  have h2 := hf x a b ha hb
  simp only [mul_zero, zero_add] at h1
  linarith

lemma KConvR_smul {K c : ℝ} (hc : 0 ≤ c) {f : ℤ → ℝ} (hf : KConvR K f) :
    KConvR (c * K) (fun x => c * f x) := by
  intro x a b ha hb
  have := mul_le_mul_of_nonneg_left (hf x a b ha hb) hc
  linarith

lemma KConvE_shift {K : ℝ≥0∞} {f : ℤ → ℝ≥0∞} (hf : KConvE K f) (ξ : ℤ) :
    KConvE K (fun y => f (y - ξ)) := by
  intro x a b ha hb
  have := hf (x - ξ) a b ha hb
  have e1 : x - ξ + a = x + a - ξ := by ring
  have e2 : x - ξ - b = x - b - ξ := by ring
  rw [e1, e2] at this
  exact this

lemma KConvE_expect (φ : PMF ℕ) {K : ℝ≥0∞} {f : ℤ → ℝ≥0∞} (hf : KConvE K f) :
    KConvE K (fun y => ∑' ξ : ℕ, φ ξ * f (y - ξ)) := by
  intro x a b ha hb
  simp only
  rw [show (b : ℝ≥0∞) * K = ∑' ξ : ℕ, φ ξ * ((b : ℝ≥0∞) * K) by
    rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]]
  rw [← ENNReal.tsum_mul_left, ← ENNReal.tsum_mul_left, ← ENNReal.tsum_mul_left,
    ← ENNReal.tsum_add, ← ENNReal.tsum_add]
  refine ENNReal.tsum_le_tsum fun ξ => ?_
  have := KConvE_shift hf (ξ : ℤ) x a b ha hb
  simp only at this
  calc ((a : ℝ≥0∞) + b) * (φ ξ * f (x - ξ)) = φ ξ * (((a : ℝ≥0∞) + b) * f (x - ξ)) := by ring
    _ ≤ φ ξ * ((b : ℝ≥0∞) * K + (b : ℝ≥0∞) * f (x + a - ξ) + (a : ℝ≥0∞) * f (x - b - ξ)) :=
        mul_le_mul_of_nonneg_left this bot_le
    _ = _ := by ring

lemma KConvE_of_R {K : ℝ} (hK : 0 ≤ K) {f : ℤ → ℝ} (hf0 : ∀ x, 0 ≤ f x) (hf : KConvR K f) :
    KConvE (ENNReal.ofReal K) (fun x => ENNReal.ofReal (f x)) := by
  intro x a b ha hb
  simp only
  have hab : (0 : ℝ) ≤ (a : ℝ) + b := by positivity
  calc ((a : ℝ≥0∞) + b) * ENNReal.ofReal (f x) = ENNReal.ofReal (((a : ℝ) + b) * f x) := by
        rw [ENNReal.ofReal_mul hab, ENNReal.ofReal_add (Nat.cast_nonneg _) (Nat.cast_nonneg _),
          ENNReal.ofReal_natCast, ENNReal.ofReal_natCast]
    _ ≤ ENNReal.ofReal ((b : ℝ) * K + (b : ℝ) * f (x + a) + (a : ℝ) * f (x - b)) :=
        ENNReal.ofReal_le_ofReal (hf x a b ha hb)
    _ = _ := by
        rw [ENNReal.ofReal_add (add_nonneg (mul_nonneg (Nat.cast_nonneg _) hK)
            (mul_nonneg (Nat.cast_nonneg _) (hf0 _))) (mul_nonneg (Nat.cast_nonneg _) (hf0 _)),
          ENNReal.ofReal_add (mul_nonneg (Nat.cast_nonneg _) hK)
            (mul_nonneg (Nat.cast_nonneg _) (hf0 _)),
          ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_mul (Nat.cast_nonneg _),
          ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast, ENNReal.ofReal_natCast]

lemma KConvR_of_E {K : ℝ} (hK : 0 ≤ K) {f : ℤ → ℝ≥0∞} (hft : ∀ x, f x ≠ ⊤)
    (hf : KConvE (ENNReal.ofReal K) f) : KConvR K (fun x => (f x).toReal) := by
  intro x a b ha hb
  simp only
  have h := hf x a b ha hb
  have h1 : (b : ℝ≥0∞) * ENNReal.ofReal K ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) ENNReal.ofReal_ne_top
  have h2 : (b : ℝ≥0∞) * f (x + a) ≠ ⊤ := ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) (hft _)
  have h3 : (a : ℝ≥0∞) * f (x - b) ≠ ⊤ := ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) (hft _)
  have hne : (b : ℝ≥0∞) * ENNReal.ofReal K + (b : ℝ≥0∞) * f (x + a) + (a : ℝ≥0∞) * f (x - b) ≠ ⊤ :=
    ENNReal.add_ne_top.2 ⟨ENNReal.add_ne_top.2 ⟨h1, h2⟩, h3⟩
  have := ENNReal.toReal_mono hne h
  have e1 : (((a : ℝ≥0∞) + b) * f x).toReal = ((a : ℝ) + b) * (f x).toReal := by
    rw [ENNReal.toReal_mul, ENNReal.toReal_add (ENNReal.natCast_ne_top _) (ENNReal.natCast_ne_top _),
      ENNReal.toReal_natCast, ENNReal.toReal_natCast]
  have e2 : ((b : ℝ≥0∞) * ENNReal.ofReal K + (b : ℝ≥0∞) * f (x + a) +
      (a : ℝ≥0∞) * f (x - b)).toReal =
      (b : ℝ) * K + (b : ℝ) * (f (x + a)).toReal + (a : ℝ) * (f (x - b)).toReal := by
    rw [ENNReal.toReal_add (ENNReal.add_ne_top.2 ⟨h1, h2⟩) h3, ENNReal.toReal_add h1 h2,
      ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_natCast,
      ENNReal.toReal_natCast, ENNReal.toReal_ofReal hK]
  rw [e1, e2] at this
  exact this

/-! ## convexity of `G` -/

lemma vw_incr_mono (G : ℤ → ℝ) (hconv : ∀ y : ℤ, G (y + 1) - G y ≤ G (y + 2) - G (y + 1))
    (a b : ℤ) (hab : a ≤ b) : G (a + 1) - G a ≤ G (b + 1) - G b := by
  obtain ⟨k, rfl⟩ : ∃ k : ℕ, b = a + k := ⟨(b - a).toNat, by omega⟩
  induction k with
  | zero => simp
  | succ k ih =>
    have h := hconv (a + k)
    have e1 : a + (k : ℤ) + 2 = a + ((k + 1 : ℕ) : ℤ) + 1 := by push_cast; ring
    have e2 : a + (k : ℤ) + 1 = a + ((k + 1 : ℕ) : ℤ) := by push_cast; ring
    rw [e1, e2] at h
    rw [e2] at ih
    linarith [ih (by omega)]

lemma vw_fwd (G : ℤ → ℝ) (hconv : ∀ y : ℤ, G (y + 1) - G y ≤ G (y + 2) - G (y + 1)) (x : ℤ) :
    ∀ a : ℕ, (a : ℝ) * (G (x + 1) - G x) ≤ G (x + a) - G x := by
  intro a
  induction a with
  | zero => simp
  | succ a ih =>
    have := vw_incr_mono G hconv x (x + a) (by omega)
    have e : x + ((a + 1 : ℕ) : ℤ) = x + a + 1 := by push_cast; ring
    rw [e]; push_cast
    linarith

lemma vw_bwd (G : ℤ → ℝ) (hconv : ∀ y : ℤ, G (y + 1) - G y ≤ G (y + 2) - G (y + 1)) (x : ℤ) :
    ∀ b : ℕ, G x - G (x - b) ≤ (b : ℝ) * (G x - G (x - 1)) := by
  intro b
  induction b with
  | zero => simp
  | succ b ih =>
    have := vw_incr_mono G hconv (x - b - 1) (x - 1) (by omega)
    have e1 : x - b - 1 + 1 = x - b := by ring
    have e2 : x - 1 + 1 = x := by ring
    rw [e1, e2] at this
    have e : x - ((b + 1 : ℕ) : ℤ) = x - b - 1 := by push_cast; ring
    rw [e]; push_cast
    linarith

lemma vw_KConvR_zero (G : ℤ → ℝ) (hconv : ∀ y : ℤ, G (y + 1) - G y ≤ G (y + 2) - G (y + 1)) :
    KConvR 0 G := by
  intro x a b ha hb
  have h1 := vw_fwd G hconv x a
  have h2 := vw_bwd G hconv x b
  have h3 := vw_incr_mono G hconv (x - 1) x (by omega)
  have e : x - 1 + 1 = x := by ring
  rw [e] at h3
  have ha0 : (0 : ℝ) ≤ a := Nat.cast_nonneg _
  have hb0 : (0 : ℝ) ≤ b := Nat.cast_nonneg _
  have h4 : (b : ℝ) * ((a : ℝ) * (G (x + 1) - G x)) ≤ b * (G (x + a) - G x) :=
    mul_le_mul_of_nonneg_left h1 hb0
  have h5 : (a : ℝ) * (G x - G (x - b)) ≤ a * ((b : ℝ) * (G x - G (x - 1))) :=
    mul_le_mul_of_nonneg_left h2 ha0
  have h6 : (a : ℝ) * b * (G x - G (x - 1)) ≤ a * b * (G (x + 1) - G x) :=
    mul_le_mul_of_nonneg_left h3 (mul_nonneg ha0 hb0)
  nlinarith

/-! ## Scarf's lemma (real valued) -/

section Scarf
variable (K : ℝ) (h : ℤ → ℝ)

lemma scarf_exists_min (hco : ∀ c : ℝ, ∃ N : ℕ, ∀ y : ℤ, h y ≤ c → |y| ≤ N) :
    ∃ S : ℤ, ∀ y, h S ≤ h y := by
  obtain ⟨N, hN⟩ := hco (h 0)
  obtain ⟨m, hm, hmin⟩ := (Finset.Icc (-(N : ℤ)) N).exists_min_image h ⟨0, by simp⟩
  refine ⟨m, fun y => ?_⟩
  by_cases hy : y ∈ Finset.Icc (-(N : ℤ)) N
  · exact hmin y hy
  · by_contra hc
    push_neg at hc
    have h0 : h y ≤ h 0 := hc.le.trans (hmin 0 (by simp))
    have := abs_le.1 (hN y h0)
    apply hy
    rw [Finset.mem_Icc]
    exact this

lemma scarf_exists_s (hK : 0 ≤ K) (hco : ∀ c : ℝ, ∃ N : ℕ, ∀ y : ℤ, h y ≤ c → |y| ≤ N)
    (S : ℤ) (hS : ∀ y, h S ≤ h y) :
    sInf {y : ℤ | h y ≤ K + h S} ≤ S ∧ h (sInf {y : ℤ | h y ≤ K + h S}) ≤ K + h S ∧
      ∀ y, y < sInf {y : ℤ | h y ≤ K + h S} → K + h S < h y := by
  obtain ⟨N, hN⟩ := hco (K + h S)
  have hbdd : BddBelow {y : ℤ | h y ≤ K + h S} := ⟨-(N : ℤ), fun y hy => (abs_le.1 (hN y hy)).1⟩
  have hne : S ∈ {y : ℤ | h y ≤ K + h S} := by show h S ≤ K + h S; linarith
  refine ⟨csInf_le hbdd hne, Int.csInf_mem ⟨S, hne⟩ hbdd, fun y hy => ?_⟩
  by_contra hc
  push_neg at hc
  have := csInf_le hbdd (show y ∈ {y : ℤ | h y ≤ K + h S} from hc)
  omega

variable (hK : 0 ≤ K) (hKc : KConvR K h) (S s : ℤ) (hS : ∀ y, h S ≤ h y) (hsS : s ≤ S)
  (hs : h s ≤ K + h S) (hs' : ∀ y, y < s → K + h S < h y)
include hK hKc hS hsS hs

/-- for `s ≤ x ≤ S`, `h x ≤ K + h S` -/
lemma scarf_le_c (x : ℤ) (hx1 : s ≤ x) (hx2 : x ≤ S) : h x ≤ K + h S := by
  rcases eq_or_lt_of_le hx1 with e | hlt
  · subst e; exact hs
  rcases eq_or_lt_of_le hx2 with e | hlt2
  · subst e; linarith
  obtain ⟨a, ha1, ha2⟩ : ∃ a : ℕ, (a : ℤ) = S - x ∧ 1 ≤ a := ⟨(S - x).toNat, by omega, by omega⟩
  obtain ⟨b, hb1, hb2⟩ : ∃ b : ℕ, (b : ℤ) = x - s ∧ 1 ≤ b := ⟨(x - s).toNat, by omega, by omega⟩
  have h1 := hKc x a b ha2 hb2
  rw [show x + a = S by omega, show x - b = s by omega] at h1
  have ha0 : (0 : ℝ) ≤ a := Nat.cast_nonneg _
  have hb0 : (0 : ℝ) < b := by exact_mod_cast hb2
  have h2 : (a : ℝ) * h s ≤ a * (K + h S) := mul_le_mul_of_nonneg_left hs ha0
  have h3 : ((a : ℝ) + b) * h x ≤ ((a : ℝ) + b) * (K + h S) := by linarith
  exact le_of_mul_le_mul_left h3 (by linarith)

/-- for `s ≤ x < y`, not ordering is at least as good: `h x ≤ K + h y` -/
lemma scarf_no_order (x y : ℤ) (hx : s ≤ x) (hxy : x < y) : h x ≤ K + h y := by
  rcases le_or_gt x S with hxS | hxS
  · have := scarf_le_c K h hK hKc S s hS hsS hs x hx hxS
    linarith [hS y]
  obtain ⟨a, ha1, ha2⟩ : ∃ a : ℕ, (a : ℤ) = y - x ∧ 1 ≤ a := ⟨(y - x).toNat, by omega, by omega⟩
  obtain ⟨b, hb1, hb2⟩ : ∃ b : ℕ, (b : ℤ) = x - S ∧ 1 ≤ b := ⟨(x - S).toNat, by omega, by omega⟩
  have h1 := hKc x a b ha2 hb2
  rw [show x + a = y by omega, show x - b = S by omega] at h1
  have ha0 : (0 : ℝ) ≤ a := Nat.cast_nonneg _
  have hb0 : (0 : ℝ) < b := by exact_mod_cast hb2
  have h2 : (a : ℝ) * h S ≤ a * h x := mul_le_mul_of_nonneg_left (hS x) ha0
  have h3 : (b : ℝ) * h x ≤ b * (K + h y) := by linarith
  exact le_of_mul_le_mul_left h3 hb0

include hs'

lemma scarf_min (x y : ℤ) (hxy : x ≤ y) :
    K * (if x < sSRule s S x then (1 : ℝ) else 0) + h (sSRule s S x) ≤
      K * (if x < y then (1 : ℝ) else 0) + h y := by
  unfold sSRule
  by_cases hx : x < s
  · rw [if_pos hx, if_pos (by omega)]
    rcases eq_or_lt_of_le hxy with e | hlt
    · subst e; rw [if_neg (lt_irrefl _)]; have := hs' x hx; linarith
    · rw [if_pos hlt]; linarith [hS y]
  · rw [if_neg hx, if_neg (lt_irrefl _)]
    rcases eq_or_lt_of_le hxy with e | hlt
    · subst e; rw [if_neg (lt_irrefl _)]
    · rw [if_pos hlt]
      have := scarf_no_order K h hK hKc S s hS hsS hs x y (by omega) hlt
      linarith

lemma scarf_f_eq (x : ℤ) :
    K * (if x < sSRule s S x then (1 : ℝ) else 0) + h (sSRule s S x) =
      if x < s then K + h S else h x := by
  unfold sSRule
  by_cases hx : x < s
  · rw [if_pos hx, if_pos hx, if_pos (by omega)]; ring
  · rw [if_neg hx, if_neg hx, if_neg (lt_irrefl _)]; ring

lemma scarf_KConv :
    KConvR K (fun x => K * (if x < sSRule s S x then (1 : ℝ) else 0) + h (sSRule s S x)) := by
  intro x a b ha hb
  simp only [scarf_f_eq K h hK hKc S s hS hsS hs hs']
  have ha0 : (0 : ℝ) ≤ a := Nat.cast_nonneg _
  have hb0 : (0 : ℝ) ≤ b := Nat.cast_nonneg _
  have hbK : (0 : ℝ) ≤ b * K := mul_nonneg hb0 hK
  have haK : (0 : ℝ) ≤ a * K := mul_nonneg ha0 hK
  by_cases hA : x + a < s
  · -- all three below s
    rw [if_pos hA, if_pos (by omega), if_pos (by omega)]
    nlinarith
  by_cases hB : x < s
  · -- x < s ≤ x + a
    rw [if_neg hA, if_pos hB, if_pos (by omega)]
    have := mul_le_mul_of_nonneg_left (hS (x + a)) hb0
    nlinarith
  by_cases hC : x - b < s
  · -- x - b < s ≤ x
    rw [if_neg hA, if_neg hB, if_pos hC]
    have hkey := scarf_no_order K h hK hKc S s hS hsS hs x (x + a) (by omega) (by omega)
    have h1 : (b : ℝ) * h x ≤ b * (K + h (x + a)) := mul_le_mul_of_nonneg_left hkey hb0
    rcases le_or_gt x S with hxS | hxS
    · have := scarf_le_c K h hK hKc S s hS hsS hs x (by omega) hxS
      have h2 : (a : ℝ) * h x ≤ a * (K + h S) := mul_le_mul_of_nonneg_left this ha0
      nlinarith
    · obtain ⟨b', hb'1, hb'2⟩ : ∃ b' : ℕ, (b' : ℤ) = x - S ∧ 1 ≤ b' :=
        ⟨(x - S).toNat, by omega, by omega⟩
      have h3 := hKc x a b' ha hb'2
      rw [show x - b' = S by omega] at h3
      have hbb : b' < b := by omega
      have hbb' : (b' : ℝ) < b := by exact_mod_cast hbb
      have h4 : ((b : ℝ) - b') * h x ≤ ((b : ℝ) - b') * (K + h (x + a)) :=
        mul_le_mul_of_nonneg_left hkey (by linarith)
      nlinarith
  · rw [if_neg hA, if_neg hB, if_neg hC]
    exact hKc x a b ha hb

end Scarf


/-! ## G facts (from the lemma 2 solution) -/

section GFacts
variable (G : ℤ → ℝ)

lemma vw_bdd_below (hG_bot : Filter.Tendsto G Filter.atBot Filter.atTop) (c : ℝ) :
    ∃ N : ℤ, ∀ y, G y ≤ c → N < y := by
  have := Filter.tendsto_atTop.1 hG_bot (c + 1)
  obtain ⟨N, hN⟩ := Filter.eventually_atBot.1 this
  refine ⟨N, fun y hy => ?_⟩
  by_contra h
  have := hN y (by omega)
  linarith

lemma vw_exists_min (hG_top : Filter.Tendsto G Filter.atTop Filter.atTop)
    (hG_bot : Filter.Tendsto G Filter.atBot Filter.atTop) :
    ∃ m : ℤ, ∀ z, G m ≤ G z := by
  obtain ⟨N1, hN1⟩ := Filter.eventually_atBot.1 (Filter.tendsto_atTop.1 hG_bot (G 0 + 1))
  obtain ⟨N2, hN2⟩ := Filter.eventually_atTop.1 (Filter.tendsto_atTop.1 hG_top (G 0 + 1))
  obtain ⟨m, hm, hmin⟩ := (Finset.Icc (min N1 0) (max N2 0)).exists_min_image G
    ⟨0, by simp⟩
  refine ⟨m, fun z => ?_⟩
  have h0 : G m ≤ G 0 := hmin 0 (by simp)
  by_cases hz : z ∈ Finset.Icc (min N1 0) (max N2 0)
  · exact hmin z hz
  · simp only [Finset.mem_Icc, not_and_or, not_le] at hz
    rcases hz with hz | hz
    · have := hN1 z (by omega); linarith
    · have := hN2 z (by omega); linarith

lemma vw_coercive (hG_top : Filter.Tendsto G Filter.atTop Filter.atTop)
    (hG_bot : Filter.Tendsto G Filter.atBot Filter.atTop) :
    ∀ c : ℝ, ∃ N : ℕ, ∀ y : ℤ, G y ≤ c → |y| ≤ N := by
  intro c
  obtain ⟨N1, hN1⟩ := Filter.eventually_atBot.1 (Filter.tendsto_atTop.1 hG_bot (c + 1))
  obtain ⟨N2, hN2⟩ := Filter.eventually_atTop.1 (Filter.tendsto_atTop.1 hG_top (c + 1))
  set A := |N1| with hA
  set B := |N2| with hB
  have a1 : -A ≤ N1 := neg_abs_le N1
  have a2 : N2 ≤ B := le_abs_self N2
  have a3 : 0 ≤ A := abs_nonneg N1
  have a4 : 0 ≤ B := abs_nonneg N2
  refine ⟨(A + B).toNat, fun y hy => ?_⟩
  have a5 : (((A + B).toNat : ℕ) : ℤ) = A + B := Int.toNat_of_nonneg (by linarith)
  have h1 : N1 < y := by
    by_contra hc; push_neg at hc; have := hN1 y hc; linarith
  have h2 : y < N2 := by
    by_contra hc; push_neg at hc; have := hN2 y hc; linarith
  rw [abs_le]
  constructor <;> omega

variable (hconv : ∀ y : ℤ, G (y + 1) - G y ≤ G (y + 2) - G (y + 1))
  (hG_top : Filter.Tendsto G Filter.atTop Filter.atTop)
  (hG_bot : Filter.Tendsto G Filter.atBot Filter.atTop)
include hG_top hG_bot

lemma vw_SLow_min : ∀ z, G (SLow G) ≤ G z := by
  obtain ⟨m, hm⟩ := vw_exists_min G hG_top hG_bot
  obtain ⟨N, hN⟩ := vw_bdd_below G hG_bot (G m)
  have hmem : SLow G ∈ {y : ℤ | ∀ z : ℤ, G y ≤ G z} :=
    Int.csInf_mem ⟨m, hm⟩ ⟨N, fun y hy => (hN y (hy m)).le⟩
  exact hmem

lemma vw_SLow_strict (y : ℤ) (hy : y < SLow G) : G (SLow G) < G y := by
  obtain ⟨m, hm⟩ := vw_exists_min G hG_top hG_bot
  obtain ⟨N, hN⟩ := vw_bdd_below G hG_bot (G m)
  by_contra h
  push_neg at h
  have hmin := vw_SLow_min G hG_top hG_bot
  have : SLow G ≤ y := csInf_le ⟨N, fun y hy => (hN y (hy m)).le⟩
    (show ∀ z, G y ≤ G z from fun z => h.trans (hmin z))
  omega

include hconv

lemma vw_anti (a b : ℤ) (hab : a ≤ b) (hb : b ≤ SLow G) : G b ≤ G a := by
  have hmin := vw_SLow_min G hG_top hG_bot
  have hd : ∀ y, y < SLow G → G (y + 1) - G y ≤ 0 := by
    intro y hy
    have := vw_incr_mono G hconv y (SLow G - 1) (by omega)
    have e : SLow G - 1 + 1 = SLow G := by ring
    rw [e] at this
    linarith [hmin (SLow G - 1)]
  obtain ⟨k, rfl⟩ : ∃ k : ℕ, b = a + k := ⟨(b - a).toNat, by omega⟩
  induction k with
  | zero => simp
  | succ k ih =>
    have := hd (a + k) (by push_cast at hb; omega)
    have e : a + ((k + 1 : ℕ) : ℤ) = a + k + 1 := by push_cast; ring
    rw [e]
    linarith [ih (by push_cast at hb ⊢; omega) (by omega)]

lemma vw_mono (a b : ℤ) (hab : a ≤ b) (ha : SLow G ≤ a) : G a ≤ G b := by
  have hmin := vw_SLow_min G hG_top hG_bot
  have hd : ∀ y, SLow G ≤ y → 0 ≤ G (y + 1) - G y := by
    intro y hy
    have := vw_incr_mono G hconv (SLow G) y hy
    linarith [hmin (SLow G + 1)]
  obtain ⟨k, rfl⟩ : ∃ k : ℕ, b = a + k := ⟨(b - a).toNat, by omega⟩
  induction k with
  | zero => simp
  | succ k ih =>
    have := hd (a + k) (by omega)
    have e : a + ((k + 1 : ℕ) : ℤ) = a + k + 1 := by push_cast; ring
    rw [e]
    linarith [ih (by omega)]

omit hconv in
lemma vw_sHigh_mem (K α : ℝ) (hα₁ : α ≤ 1) (hK : 0 ≤ K) :
    G (sHigh G K α) ≤ G (SLow G) + (1 - α) * K := by
  obtain ⟨N, hN⟩ := vw_bdd_below G hG_bot (G (SLow G) + (1 - α) * K)
  have hmem : sHigh G K α ∈ {y : ℤ | G y ≤ G (SLow G) + (1 - α) * K} :=
    Int.csInf_mem ⟨SLow G, by
      show G (SLow G) ≤ G (SLow G) + (1 - α) * K
      nlinarith⟩ ⟨N, fun y hy => (hN y hy).le⟩
  exact hmem

omit hconv in
lemma vw_sHigh_le_SLow (K α : ℝ) (hα₁ : α ≤ 1) (hK : 0 ≤ K) :
    sHigh G K α ≤ SLow G := by
  obtain ⟨N, hN⟩ := vw_bdd_below G hG_bot (G (SLow G) + (1 - α) * K)
  exact csInf_le ⟨N, fun y hy => (hN y hy).le⟩
    (show G (SLow G) ≤ G (SLow G) + (1 - α) * K by nlinarith)

omit hconv in
lemma vw_SHigh_mem (K α : ℝ) :
    SLow G ≤ SHigh G K α ∧ G (SLow G) + α * K ≤ G (SHigh G K α + 1) := by
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1
    (Filter.tendsto_atTop.1 hG_top (G (SLow G) + α * K))
  have hmem : SHigh G K α ∈ {y : ℤ | SLow G ≤ y ∧ G (SLow G) + α * K ≤ G (y + 1)} :=
    Int.csInf_mem ⟨max N (SLow G), le_max_right _ _, hN _ (by omega)⟩
      ⟨SLow G, fun y hy => hy.1⟩
  exact hmem

end GFacts

/-! ## ENNReal-valued cost -/

noncomputable def gE (φ : PMF ℕ) (G : ℤ → ℝ) (Y : Policy) (x : ℤ) (t : ℕ) : ℝ≥0∞ :=
  ∑' h : Fin t → ℕ, weight φ h * ENNReal.ofReal (G (Y t x h))

noncomputable def pcE (φ : PMF ℕ) (G : ℤ → ℝ) (K : ℝ) (Y : Policy) (x : ℤ) (t : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal K * orderProb φ Y x t + gE φ G Y x t

noncomputable def costE (φ : PMF ℕ) (G : ℤ → ℝ) (K α : ℝ) (n : ℕ) (x : ℤ) (Y : Policy) :
    ℝ≥0∞ :=
  ∑ t ∈ Finset.range n, ENNReal.ofReal (α ^ t) * pcE φ G K Y x t

lemma vw_expectedG_eq (φ : PMF ℕ) (G : ℤ → ℝ) (hG0 : ∀ y, 0 ≤ G y) (Y : Policy) (x : ℤ)
    (t : ℕ) : expectedG φ G Y x t = (gE φ G Y x t : EReal) := by
  unfold expectedG gE
  have : ∀ h : Fin t → ℕ, weight φ h * ENNReal.ofReal (-G (Y t x h)) = 0 := fun h => by
    rw [ENNReal.ofReal_of_nonpos (by linarith [hG0 (Y t x h)]), mul_zero]
  simp only [this, tsum_zero, EReal.coe_ennreal_zero, sub_zero]

lemma vw_periodCost_eq (φ : PMF ℕ) (G : ℤ → ℝ) (K : ℝ) (hG0 : ∀ y, 0 ≤ G y) (hK : 0 ≤ K)
    (Y : Policy) (x : ℤ) (t : ℕ) : periodCost φ G K Y x t = (pcE φ G K Y x t : EReal) := by
  unfold periodCost pcE
  rw [EReal.coe_ennreal_add, EReal.coe_ennreal_mul, vw_expectedG_eq φ G hG0 Y x t,
    EReal.coe_ennreal_ofReal, max_eq_left hK]

lemma vw_cost_eq (φ : PMF ℕ) (G : ℤ → ℝ) (K α : ℝ) (hG0 : ∀ y, 0 ≤ G y) (hK : 0 ≤ K)
    (hα₀ : 0 ≤ α) (x : ℤ) (Y : Policy) (n : ℕ) :
    cost φ G K α n x Y = (costE φ G K α n x Y : EReal) := by
  induction n with
  | zero => simp [cost, costE]
  | succ n ih =>
    unfold cost costE at ih ⊢
    rw [Finset.sum_range_succ, Finset.sum_range_succ, EReal.coe_ennreal_add, ih,
      vw_periodCost_eq φ G K hG0 hK, EReal.coe_ennreal_mul, EReal.coe_ennreal_ofReal,
      max_eq_left (pow_nonneg hα₀ n)]

/-! ## shifting a policy by one period -/

def shiftP (Y : Policy) (x : ℤ) (ξ : ℕ) : Policy :=
  fun t x' h => if x' = Y 0 x finZeroElim - ξ then Y (t + 1) x (Fin.cons ξ h) else x'

lemma fin_init_cons {n : ℕ} (ξ : ℕ) (h : Fin (n + 1) → ℕ) :
    Fin.init (Fin.cons ξ h : Fin (n + 2) → ℕ) = Fin.cons ξ (Fin.init h) := by
  ext i
  refine Fin.cases ?_ ?_ i
  · simp [Fin.init]
  · intro j; simp [Fin.init, Fin.cons_succ]

lemma fin_init_cons0 (ξ : ℕ) (h : Fin 0 → ℕ) :
    Fin.init (Fin.cons ξ h : Fin 1 → ℕ) = finZeroElim := Subsingleton.elim _ _

lemma shift_state (Y : Policy) (x : ℤ) (ξ : ℕ) (t : ℕ) (h : Fin t → ℕ) :
    state (shiftP Y x ξ) (Y 0 x finZeroElim - ξ) t h = state Y x (t + 1) (Fin.cons ξ h) := by
  cases t with
  | zero => simp [state, shiftP, fin_init_cons0, Fin.last]
  | succ t => simp [state, shiftP, fin_init_cons]

lemma shift_apply (Y : Policy) (x : ℤ) (ξ : ℕ) (t : ℕ) (h : Fin t → ℕ) :
    shiftP Y x ξ t (Y 0 x finZeroElim - ξ) h = Y (t + 1) x (Fin.cons ξ h) := by
  simp [shiftP]

lemma shift_adm (Y : Policy) (hY : Admissible Y) (x : ℤ) (ξ : ℕ) : Admissible (shiftP Y x ξ) := by
  intro t x' h
  by_cases hx : x' = Y 0 x finZeroElim - ξ
  · subst hx
    rw [shift_state, shift_apply]
    exact hY (t + 1) x (Fin.cons ξ h)
  · have e : shiftP Y x ξ t x' h = x' := by simp only [shiftP, if_neg hx]
    rw [e]
    cases t with
    | zero => exact le_rfl
    | succ t =>
      show shiftP Y x ξ t x' (Fin.init h) - (h (Fin.last t) : ℤ) ≤ x'
      have e2 : shiftP Y x ξ t x' (Fin.init h) = x' := by simp only [shiftP, if_neg hx]
      rw [e2]
      omega

lemma vw_tsum_cons (φ : PMF ℕ) (t : ℕ) (F : (Fin (t + 1) → ℕ) → ℝ≥0∞) :
    ∑' h : Fin (t + 1) → ℕ, weight φ h * F h =
      ∑' ξ : ℕ, φ ξ * ∑' h : Fin t → ℕ, weight φ h * F (Fin.cons ξ h) := by
  rw [← (Fin.consEquiv (fun _ : Fin (t + 1) => ℕ)).tsum_eq (fun h => weight φ h * F h)]
  have hw : ∀ c : ℕ × (Fin t → ℕ), weight φ ((Fin.consEquiv (fun _ : Fin (t + 1) => ℕ)) c) =
      φ c.1 * weight φ c.2 := by
    intro c
    simp [weight, Fin.prod_univ_succ, Fin.consEquiv]
  have hF : ∀ c : ℕ × (Fin t → ℕ), F ((Fin.consEquiv (fun _ : Fin (t + 1) => ℕ)) c) =
      F (Fin.cons c.1 c.2) := fun c => rfl
  simp only [hw, hF, mul_assoc]
  rw [ENNReal.tsum_prod (f := fun a (g : Fin t → ℕ) => φ a * (weight φ g * F (Fin.cons a g)))]
  simp only [ENNReal.tsum_mul_left]

lemma vw_op_succ (φ : PMF ℕ) (Y : Policy) (x : ℤ) (t : ℕ) :
    orderProb φ Y x (t + 1) =
      ∑' ξ : ℕ, φ ξ * orderProb φ (shiftP Y x ξ) (Y 0 x finZeroElim - ξ) t := by
  unfold orderProb
  rw [vw_tsum_cons]
  apply tsum_congr; intro ξ; congr 1
  apply tsum_congr; intro h
  rw [shift_state, shift_apply]

lemma vw_gE_succ (φ : PMF ℕ) (G : ℤ → ℝ) (Y : Policy) (x : ℤ) (t : ℕ) :
    gE φ G Y x (t + 1) =
      ∑' ξ : ℕ, φ ξ * gE φ G (shiftP Y x ξ) (Y 0 x finZeroElim - ξ) t := by
  unfold gE
  rw [vw_tsum_cons]
  apply tsum_congr; intro ξ; congr 1
  apply tsum_congr; intro h
  rw [shift_apply]

lemma vw_pcE_succ (φ : PMF ℕ) (G : ℤ → ℝ) (K : ℝ) (Y : Policy) (x : ℤ) (t : ℕ) :
    pcE φ G K Y x (t + 1) =
      ∑' ξ : ℕ, φ ξ * pcE φ G K (shiftP Y x ξ) (Y 0 x finZeroElim - ξ) t := by
  unfold pcE
  rw [vw_op_succ, vw_gE_succ, ← ENNReal.tsum_mul_left, ← ENNReal.tsum_add]
  apply tsum_congr; intro ξ; ring

lemma vw_pcE_zero (φ : PMF ℕ) (G : ℤ → ℝ) (K : ℝ) (Y : Policy) (x : ℤ) :
    pcE φ G K Y x 0 = ENNReal.ofReal K * (if x < Y 0 x finZeroElim then 1 else 0) +
      ENNReal.ofReal (G (Y 0 x finZeroElim)) := by
  have hu : ∀ f : (Fin 0 → ℕ) → ℝ≥0∞, ∑' h, f h = f finZeroElim := fun f =>
    tsum_eq_single _ (fun h hh => absurd (Subsingleton.elim h _) hh)
  have hw : weight φ (finZeroElim : Fin 0 → ℕ) = 1 := by simp [weight]
  unfold pcE orderProb gE
  rw [hu, hu, hw, one_mul, one_mul]
  rfl

lemma vw_costE_succ (φ : PMF ℕ) (G : ℤ → ℝ) (K α : ℝ) (hα₀ : 0 ≤ α) (n : ℕ) (x : ℤ)
    (Y : Policy) :
    costE φ G K α (n + 1) x Y = pcE φ G K Y x 0 + ENNReal.ofReal α *
      ∑' ξ : ℕ, φ ξ * costE φ G K α n (Y 0 x finZeroElim - ξ) (shiftP Y x ξ) := by
  unfold costE
  rw [Finset.sum_range_succ', pow_zero, ENNReal.ofReal_one, one_mul, add_comm]
  congr 1
  have : ∀ t ∈ Finset.range n, ENNReal.ofReal (α ^ (t + 1)) * pcE φ G K Y x (t + 1) =
      ∑' ξ : ℕ, φ ξ * (ENNReal.ofReal α *
        (ENNReal.ofReal (α ^ t) * pcE φ G K (shiftP Y x ξ) (Y 0 x finZeroElim - ξ) t)) := by
    intro t _
    rw [vw_pcE_succ, pow_succ, ENNReal.ofReal_mul (pow_nonneg hα₀ t), ← ENNReal.tsum_mul_left]
    apply tsum_congr; intro ξ; ring
  rw [Finset.sum_congr rfl this, ← Summable.tsum_finsetSum (fun i _ => ENNReal.summable),
    ← ENNReal.tsum_mul_left]
  apply tsum_congr; intro ξ
  rw [Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl; intro t _; ring

lemma vw_costE_congr (φ : PMF ℕ) (G : ℤ → ℝ) (K α : ℝ) (n : ℕ) (x : ℤ) (Y Y' : Policy)
    (h : ∀ t hh, Y' t x hh = Y t x hh) : costE φ G K α n x Y' = costE φ G K α n x Y := by
  have hs : ∀ t hh, state Y' x t hh = state Y x t hh := by
    intro t hh; cases t <;> simp [state, h]
  unfold costE pcE orderProb gE
  simp only [hs, h]

/-! ## Markov policies -/

def mkP (r : ℕ → ℤ → ℤ) : (t : ℕ) → ℤ → (Fin t → ℕ) → ℤ
  | 0, x, _ => r 0 x
  | t + 1, x, h => r (t + 1) (mkP r t x (Fin.init h) - (h (Fin.last t) : ℤ))

lemma mkP_eq (r : ℕ → ℤ → ℤ) (t : ℕ) (x : ℤ) (h : Fin t → ℕ) :
    mkP r t x h = r t (state (mkP r) x t h) := by
  cases t <;> rfl

lemma mkP_adm (r : ℕ → ℤ → ℤ) (hr : ∀ t x, x ≤ r t x) : Admissible (mkP r) := by
  intro t x h; rw [mkP_eq]; exact hr _ _

lemma mkP_rule (r : ℕ → ℤ → ℤ) (t : ℕ) (s S : ℤ) (hr : ∀ x, r t x = sSRule s S x) :
    UsesRule (mkP r) t s S := by
  intro x h; rw [mkP_eq, hr]

lemma mkP_shift (r : ℕ → ℤ → ℤ) (x : ℤ) (ξ : ℕ) :
    ∀ (t : ℕ) (h : Fin t → ℕ),
      mkP r (t + 1) x (Fin.cons ξ h) = mkP (fun t => r (t + 1)) t (r 0 x - ξ) h
  | 0, h => by
    show r 1 (mkP r 0 x (Fin.init (Fin.cons ξ h : Fin 1 → ℕ)) -
        ((Fin.cons ξ h : Fin 1 → ℕ) (Fin.last 0) : ℤ)) =
      r 1 (r 0 x - ξ)
    rw [fin_init_cons0]
    simp [mkP, Fin.last]
  | t + 1, h => by
    show r (t + 2) (mkP r (t + 1) x (Fin.init (Fin.cons ξ h : Fin (t + 2) → ℕ)) -
        ((Fin.cons ξ h : Fin (t + 2) → ℕ) (Fin.last (t + 1)) : ℤ)) =
      r (t + 2) (mkP (fun t => r (t + 1)) t (r 0 x - ξ) (Fin.init h) - (h (Fin.last t) : ℤ))
    rw [fin_init_cons, Fin.cons_last, mkP_shift r x ξ t (Fin.init h)]

lemma vw_shift_mkP_cost (φ : PMF ℕ) (G : ℤ → ℝ) (K α : ℝ) (r : ℕ → ℤ → ℤ) (x : ℤ) (ξ : ℕ)
    (n : ℕ) :
    costE φ G K α n (mkP r 0 x finZeroElim - ξ) (shiftP (mkP r) x ξ) =
      costE φ G K α n (r 0 x - ξ) (mkP (fun t => r (t + 1))) := by
  apply vw_costE_congr
  intro t hh
  rw [shift_apply]
  exact mkP_shift r x ξ t hh

/-! ## dynamic programme -/

noncomputable def EE (φ : PMF ℕ) (f : ℤ → ℝ) (y : ℤ) : ℝ≥0∞ :=
  ∑' ξ : ℕ, φ ξ * ENNReal.ofReal (f (y - ξ))

noncomputable def hfun (φ : PMF ℕ) (G : ℤ → ℝ) (α : ℝ) (f : ℤ → ℝ) (y : ℤ) : ℝ :=
  G y + α * (EE φ f y).toReal

open Classical in
noncomputable def SOf (h : ℤ → ℝ) : ℤ :=
  if hex : ∃ S : ℤ, ∀ y, h S ≤ h y then Classical.choose hex else 0

noncomputable def sOf (K : ℝ) (h : ℤ → ℝ) : ℤ := sInf {y : ℤ | h y ≤ K + h (SOf h)}

noncomputable def minForm (K : ℝ) (h : ℤ → ℝ) (x : ℤ) : ℝ :=
  K * (if x < sSRule (sOf K h) (SOf h) x then 1 else 0) + h (sSRule (sOf K h) (SOf h) x)

noncomputable def dp (φ : PMF ℕ) (G : ℤ → ℝ) (K α : ℝ) : ℕ → ℤ → ℝ
  | 0 => fun _ => 0
  | n + 1 => minForm K (hfun φ G α (dp φ G K α n))

lemma SOf_spec (h : ℤ → ℝ) (hco : ∀ c : ℝ, ∃ N : ℕ, ∀ y : ℤ, h y ≤ c → |y| ≤ N) :
    ∀ y, h (SOf h) ≤ h y := by
  have hex := scarf_exists_min h hco
  unfold SOf
  rw [dif_pos hex]
  exact Classical.choose_spec hex

theorem scarf_pack (K : ℝ) (h : ℤ → ℝ) (hK : 0 ≤ K) (hKc : KConvR K h)
    (hco : ∀ c : ℝ, ∃ N : ℕ, ∀ y : ℤ, h y ≤ c → |y| ≤ N) :
    sOf K h ≤ SOf h ∧
      (∀ x y : ℤ, x ≤ y → minForm K h x ≤ K * (if x < y then (1 : ℝ) else 0) + h y) ∧
      KConvR K (minForm K h) := by
  have hS := SOf_spec h hco
  obtain ⟨hsS, hs, hs'⟩ := scarf_exists_s K h hK hco (SOf h) hS
  exact ⟨hsS, scarf_min K h hK hKc (SOf h) (sOf K h) hS hsS hs hs',
    scarf_KConv K h hK hKc (SOf h) (sOf K h) hS hsS hs hs'⟩

section DP
variable (φ : PMF ℕ) (G : ℤ → ℝ) (K α : ℝ)
  (hα₀ : 0 ≤ α) (hα₁ : α ≤ 1) (hK : 0 ≤ K) (hG0 : ∀ y, 0 ≤ G y)
  (hconv : ∀ y : ℤ, G (y + 1) - G y ≤ G (y + 2) - G (y + 1))
  (hG_top : Filter.Tendsto G Filter.atTop Filter.atTop)
  (hG_bot : Filter.Tendsto G Filter.atBot Filter.atTop)

include hK hconv hG_top hG_bot in
lemma vw_EE_bound (f : ℤ → ℝ) (n : ℕ)
    (hf : ∀ z, f z ≤ n * (K + G (max z (SLow G)))) (y : ℤ) :
    EE φ f y ≤ ENNReal.ofReal (n * (K + G (max y (SLow G)))) := by
  unfold EE
  calc ∑' ξ : ℕ, φ ξ * ENNReal.ofReal (f (y - ξ))
      ≤ ∑' ξ : ℕ, φ ξ * ENNReal.ofReal (n * (K + G (max y (SLow G)))) := by
        refine ENNReal.tsum_le_tsum fun ξ => ?_
        refine mul_le_mul_of_nonneg_left (ENNReal.ofReal_le_ofReal ?_) bot_le
        have h1 := hf (y - ξ)
        have h2 : G (max (y - ξ) (SLow G)) ≤ G (max y (SLow G)) :=
          vw_mono G hconv hG_top hG_bot _ _ (by omega) (le_max_right _ _)
        have : (0 : ℝ) ≤ n := Nat.cast_nonneg _
        nlinarith
    _ = ENNReal.ofReal (n * (K + G (max y (SLow G)))) := by
        rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]

include hα₀ hG0 in
lemma vw_ofReal_hfun (f : ℤ → ℝ) (y : ℤ) (hfin : EE φ f y ≠ ⊤) :
    ENNReal.ofReal (hfun φ G α f y) = ENNReal.ofReal (G y) + ENNReal.ofReal α * EE φ f y := by
  unfold hfun
  rw [ENNReal.ofReal_add (hG0 y) (mul_nonneg hα₀ ENNReal.toReal_nonneg), ENNReal.ofReal_mul hα₀,
    ENNReal.ofReal_toReal hfin]

include hα₀ hG0 in
lemma vw_hfun_nonneg (f : ℤ → ℝ) (y : ℤ) : 0 ≤ hfun φ G α f y :=
  add_nonneg (hG0 y) (mul_nonneg hα₀ ENNReal.toReal_nonneg)

include hα₀ hα₁ hK hG0 hconv hG_top hG_bot in
/-- one stage of the dynamic programme -/
lemma vw_stage (f : ℤ → ℝ) (n : ℕ) (hf0 : ∀ x, 0 ≤ f x)
    (hfb : ∀ z, f z ≤ n * (K + G (max z (SLow G)))) (hfc : KConvR K f) :
    (∀ y, EE φ f y ≠ ⊤) ∧
    sOf K (hfun φ G α f) ≤ SOf (hfun φ G α f) ∧
    (∀ x y : ℤ, x ≤ y → minForm K (hfun φ G α f) x ≤
      K * (if x < y then (1 : ℝ) else 0) + hfun φ G α f y) ∧
    KConvR K (minForm K (hfun φ G α f)) ∧
    (∀ x, 0 ≤ minForm K (hfun φ G α f) x) ∧
    (∀ x, minForm K (hfun φ G α f) x ≤ (n + 1 : ℕ) * (K + G (max x (SLow G)))) := by
  have hfin : ∀ y, EE φ f y ≠ ⊤ := fun y =>
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top (vw_EE_bound φ G K hK hconv hG_top hG_bot f n hfb y)
  have hKc : KConvR K (hfun φ G α f) := by
    have h1 : KConvE (ENNReal.ofReal K) (fun y => ENNReal.ofReal (f y)) := KConvE_of_R hK hf0 hfc
    have h2 : KConvE (ENNReal.ofReal K) (EE φ f) := KConvE_expect φ h1
    have h3 : KConvR K (fun y => (EE φ f y).toReal) := KConvR_of_E hK hfin h2
    have h4 : KConvR (α * K) (fun y => α * (EE φ f y).toReal) := KConvR_smul hα₀ h3
    have h5 : KConvR K (fun y => α * (EE φ f y).toReal) := KConvR_mono (by nlinarith) h4
    exact KConvR_add (vw_KConvR_zero G hconv) h5
  have hco : ∀ c : ℝ, ∃ N : ℕ, ∀ y : ℤ, hfun φ G α f y ≤ c → |y| ≤ N := by
    intro c
    obtain ⟨N, hN⟩ := vw_coercive G hG_top hG_bot c
    refine ⟨N, fun y hy => hN y ?_⟩
    have : G y ≤ hfun φ G α f y := by
      unfold hfun; linarith [mul_nonneg hα₀ (ENNReal.toReal_nonneg (a := EE φ f y))]
    linarith
  obtain ⟨hsS, hmin, hKc'⟩ := scarf_pack K (hfun φ G α f) hK hKc hco
  refine ⟨hfin, hsS, hmin, hKc', fun x => ?_, fun x => ?_⟩
  · unfold minForm
    have := vw_hfun_nonneg φ G α hα₀ hG0 f (sSRule (sOf K (hfun φ G α f)) (SOf (hfun φ G α f)) x)
    split_ifs <;> nlinarith
  · have hxy : x ≤ max x (SLow G) := le_max_left _ _
    have h1 := hmin x (max x (SLow G)) hxy
    have h2 := vw_EE_bound φ G K hK hconv hG_top hG_bot f n hfb (max x (SLow G))
    rw [max_eq_left (le_max_right x (SLow G))] at h2
    have h3 : (EE φ f (max x (SLow G))).toReal ≤ n * (K + G (max x (SLow G))) :=
      ENNReal.toReal_le_of_le_ofReal
        (mul_nonneg (Nat.cast_nonneg _) (add_nonneg hK (hG0 _))) h2
    have h4 : K * (if x < max x (SLow G) then (1 : ℝ) else 0) ≤ K := by split_ifs <;> linarith
    have h5 : 0 ≤ K + G (max x (SLow G)) := add_nonneg hK (hG0 _)
    have h6 : (0 : ℝ) ≤ n := Nat.cast_nonneg _
    rw [show hfun φ G α f (max x (SLow G)) =
      G (max x (SLow G)) + α * (EE φ f (max x (SLow G))).toReal from rfl] at h1
    push_cast
    nlinarith [mul_le_mul_of_nonneg_left h3 hα₀, mul_le_mul_of_nonneg_left hα₁ (mul_nonneg h6 h5)]

include hα₀ hα₁ hK hG0 hconv hG_top hG_bot in
lemma vw_dp_props : ∀ n : ℕ, (∀ x, 0 ≤ dp φ G K α n x) ∧
    (∀ x, dp φ G K α n x ≤ n * (K + G (max x (SLow G)))) ∧ KConvR K (dp φ G K α n)
  | 0 => by
    refine ⟨fun x => le_rfl, fun x => by simp [dp], ?_⟩
    intro x a b ha hb; simp [dp]; exact mul_nonneg (Nat.cast_nonneg _) hK
  | n + 1 => by
    obtain ⟨h0, hb, hc⟩ := vw_dp_props n
    obtain ⟨_, _, _, h3, h4, h5⟩ :=
      vw_stage φ G K α hα₀ hα₁ hK hG0 hconv hG_top hG_bot (dp φ G K α n) n h0 hb hc
    exact ⟨h4, h5, h3⟩

include hα₀ hα₁ hK hG0 hconv hG_top hG_bot in
lemma vw_stage_dp (n : ℕ) :
    (∀ y, EE φ (dp φ G K α n) y ≠ ⊤) ∧
    sOf K (hfun φ G α (dp φ G K α n)) ≤ SOf (hfun φ G α (dp φ G K α n)) ∧
    (∀ x y : ℤ, x ≤ y → dp φ G K α (n + 1) x ≤
      K * (if x < y then (1 : ℝ) else 0) + hfun φ G α (dp φ G K α n) y) := by
  obtain ⟨h0, hb, hc⟩ := vw_dp_props φ G K α hα₀ hα₁ hK hG0 hconv hG_top hG_bot n
  obtain ⟨h1, h2, h3, _⟩ :=
    vw_stage φ G K α hα₀ hα₁ hK hG0 hconv hG_top hG_bot (dp φ G K α n) n h0 hb hc
  exact ⟨h1, h2, h3⟩

include hα₀ hα₁ hK hG0 hconv hG_top hG_bot in
lemma vw_dp_mono_K : ∀ (n : ℕ) (z z' : ℤ), z' ≤ z → dp φ G K α n z' ≤ K + dp φ G K α n z
  | 0, z, z', _ => by simp [dp, hK]
  | n + 1, z, z', hzz => by
    obtain ⟨_, hsS, hmin⟩ := vw_stage_dp φ G K α hα₀ hα₁ hK hG0 hconv hG_top hG_bot n
    set s := sOf K (hfun φ G α (dp φ G K α n))
    set S := SOf (hfun φ G α (dp φ G K α n))
    have hy : z ≤ sSRule s S z := by unfold sSRule; split_ifs <;> omega
    have h1 := hmin z' (sSRule s S z) (hzz.trans hy)
    have h2 : dp φ G K α (n + 1) z = K * (if z < sSRule s S z then (1 : ℝ) else 0) +
        hfun φ G α (dp φ G K α n) (sSRule s S z) := rfl
    rw [h2]
    have h3 : K * (if z' < sSRule s S z then (1 : ℝ) else 0) ≤ K := by split_ifs <;> linarith
    have h4 : 0 ≤ K * (if z < sSRule s S z then (1 : ℝ) else 0) := by split_ifs <;> linarith
    linarith

include hK in
lemma vw_EE_mono_K (f : ℤ → ℝ) (hf0 : ∀ z, 0 ≤ f z) (hfK : ∀ z z', z' ≤ z → f z' ≤ K + f z)
    (hfin : ∀ y, EE φ f y ≠ ⊤) (y y' : ℤ) (hyy : y' ≤ y) :
    (EE φ f y').toReal ≤ K + (EE φ f y).toReal := by
  have h1 : EE φ f y' ≤ ENNReal.ofReal K + EE φ f y := by
    unfold EE
    calc ∑' ξ : ℕ, φ ξ * ENNReal.ofReal (f (y' - ξ))
        ≤ ∑' ξ : ℕ, φ ξ * (ENNReal.ofReal K + ENNReal.ofReal (f (y - ξ))) := by
          refine ENNReal.tsum_le_tsum fun ξ => ?_
          refine mul_le_mul_of_nonneg_left ?_ bot_le
          rw [← ENNReal.ofReal_add hK (hf0 _)]
          exact ENNReal.ofReal_le_ofReal (hfK _ _ (by omega))
      _ = ENNReal.ofReal K + ∑' ξ : ℕ, φ ξ * ENNReal.ofReal (f (y - ξ)) := by
          simp only [mul_add]
          rw [ENNReal.tsum_add, ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]
  have h2 := ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨ENNReal.ofReal_ne_top, hfin y⟩) h1
  rw [ENNReal.toReal_add ENNReal.ofReal_ne_top (hfin y), ENNReal.toReal_ofReal hK] at h2
  exact h2

include hα₀ hK in
lemma vw_hfun_compare (f : ℤ → ℝ) (hf0 : ∀ z, 0 ≤ f z) (hfK : ∀ z z', z' ≤ z → f z' ≤ K + f z)
    (hfin : ∀ y, EE φ f y ≠ ⊤) (x y y' : ℤ) (hyy : y' ≤ y)
    (hG : K * (if x < y' then (1 : ℝ) else 0) + G y' + α * K ≤
      K * (if x < y then (1 : ℝ) else 0) + G y) :
    K * (if x < y' then (1 : ℝ) else 0) + hfun φ G α f y' ≤
      K * (if x < y then (1 : ℝ) else 0) + hfun φ G α f y := by
  unfold hfun
  have := vw_EE_mono_K φ K hK f hf0 hfK hfin y y' hyy
  nlinarith [mul_le_mul_of_nonneg_left this hα₀]

/-! ## lower and upper bounds -/

lemma vw_ofReal_Kδ (hK : 0 ≤ K) (b : Prop) [Decidable b] :
    ENNReal.ofReal (K * if b then (1 : ℝ) else 0) =
      ENNReal.ofReal K * (if b then (1 : ℝ≥0∞) else 0) := by
  split_ifs <;> simp

include hα₀ hK hG0 in
lemma vw_ofReal_stage (f : ℤ → ℝ) (hfin : ∀ y, EE φ f y ≠ ⊤) (x y : ℤ) :
    ENNReal.ofReal (K * (if x < y then (1 : ℝ) else 0) + hfun φ G α f y) =
      ENNReal.ofReal K * (if x < y then (1 : ℝ≥0∞) else 0) + ENNReal.ofReal (G y) +
        ENNReal.ofReal α * EE φ f y := by
  rw [ENNReal.ofReal_add (by split_ifs <;> linarith) (vw_hfun_nonneg φ G α hα₀ hG0 f y),
    vw_ofReal_Kδ K hK, vw_ofReal_hfun φ G α hα₀ hG0 f y (hfin y), add_assoc]

include hα₀ hα₁ hK hG0 hconv hG_top hG_bot in
lemma vw_lower : ∀ (n : ℕ) (Y : Policy), Admissible Y → ∀ x : ℤ,
    ENNReal.ofReal (dp φ G K α n x) ≤ costE φ G K α n x Y
  | 0, Y, _, x => by simp [dp]
  | n + 1, Y, hY, x => by
    obtain ⟨hfin, _, hmin⟩ := vw_stage_dp φ G K α hα₀ hα₁ hK hG0 hconv hG_top hG_bot n
    rw [vw_costE_succ φ G K α hα₀, vw_pcE_zero]
    set y := Y 0 x finZeroElim with hy
    have hxy : x ≤ y := hY 0 x finZeroElim
    calc ENNReal.ofReal (dp φ G K α (n + 1) x)
        ≤ ENNReal.ofReal (K * (if x < y then (1 : ℝ) else 0) + hfun φ G α (dp φ G K α n) y) :=
          ENNReal.ofReal_le_ofReal (hmin x y hxy)
      _ = ENNReal.ofReal K * (if x < y then (1 : ℝ≥0∞) else 0) + ENNReal.ofReal (G y) +
          ENNReal.ofReal α * EE φ (dp φ G K α n) y :=
          vw_ofReal_stage φ G K α hα₀ hK hG0 _ hfin x y
      _ ≤ _ := by
          refine add_le_add le_rfl (mul_le_mul_of_nonneg_left ?_ bot_le)
          unfold EE
          refine ENNReal.tsum_le_tsum fun ξ => mul_le_mul_of_nonneg_left ?_ bot_le
          exact vw_lower n (shiftP Y x ξ) (shift_adm Y hY x ξ) (y - ξ)

/-- the rule used when `m + 1` periods remain -/
noncomputable def ruleOf (m : ℕ) : ℤ → ℤ :=
  sSRule (sOf K (hfun φ G α (dp φ G K α m))) (SOf (hfun φ G α (dp φ G K α m)))

include hα₀ hα₁ hK hG0 hconv hG_top hG_bot in
lemma vw_ruleOf_ge (m : ℕ) (x : ℤ) : x ≤ ruleOf φ G K α m x := by
  obtain ⟨_, hsS, _⟩ := vw_stage_dp φ G K α hα₀ hα₁ hK hG0 hconv hG_top hG_bot m
  unfold ruleOf sSRule
  split_ifs <;> omega

include hα₀ hα₁ hK hG0 hconv hG_top hG_bot in
lemma vw_costE_mkP : ∀ (n : ℕ) (r : ℕ → ℤ → ℤ), (∀ t, t < n → r t = ruleOf φ G K α (n - 1 - t)) →
    ∀ x : ℤ, costE φ G K α n x (mkP r) = ENNReal.ofReal (dp φ G K α n x)
  | 0, r, _, x => by simp [costE, dp]
  | n + 1, r, hr, x => by
    obtain ⟨hfin, _, _⟩ := vw_stage_dp φ G K α hα₀ hα₁ hK hG0 hconv hG_top hG_bot n
    rw [vw_costE_succ φ G K α hα₀, vw_pcE_zero]
    have h0 : mkP r 0 x finZeroElim = r 0 x := rfl
    have hr0 : r 0 = ruleOf φ G K α n := by
      have := hr 0 (by omega); rwa [show n + 1 - 1 - 0 = n by omega] at this
    have hr' : ∀ t, t < n → r (t + 1) = ruleOf φ G K α (n - 1 - t) := by
      intro t ht
      have := hr (t + 1) (by omega)
      rwa [show n + 1 - 1 - (t + 1) = n - 1 - t by omega] at this
    have hsh : ∀ ξ : ℕ, costE φ G K α n (r 0 x - ξ) (shiftP (mkP r) x ξ) =
        ENNReal.ofReal (dp φ G K α n (r 0 x - ξ)) := fun ξ =>
      (vw_shift_mkP_cost φ G K α r x ξ n).trans (vw_costE_mkP n (fun t => r (t + 1)) hr' (r 0 x - ξ))
    simp only [hsh, h0]
    have e : dp φ G K α (n + 1) x = K * (if x < r 0 x then (1 : ℝ) else 0) +
        hfun φ G α (dp φ G K α n) (r 0 x) := by
      rw [hr0]; rfl
    rw [e, vw_ofReal_stage φ G K α hα₀ hK hG0 _ hfin x (r 0 x)]
    rfl

include hα₀ hα₁ hK hG0 hconv hG_top hG_bot in
lemma vw_costE_mkP_succ (n : ℕ) (r : ℕ → ℤ → ℤ)
    (hr : ∀ t, t < n → r (t + 1) = ruleOf φ G K α (n - 1 - t)) (x : ℤ) :
    costE φ G K α (n + 1) x (mkP r) =
      ENNReal.ofReal (K * (if x < r 0 x then (1 : ℝ) else 0) + hfun φ G α (dp φ G K α n) (r 0 x)) := by
  obtain ⟨hfin, _, _⟩ := vw_stage_dp φ G K α hα₀ hα₁ hK hG0 hconv hG_top hG_bot n
  rw [vw_costE_succ φ G K α hα₀, vw_pcE_zero]
  have h0 : mkP r 0 x finZeroElim = r 0 x := rfl
  have hsh : ∀ ξ : ℕ, costE φ G K α n (r 0 x - ξ) (shiftP (mkP r) x ξ) =
      ENNReal.ofReal (dp φ G K α n (r 0 x - ξ)) := fun ξ =>
    (vw_shift_mkP_cost φ G K α r x ξ n).trans
      (vw_costE_mkP φ G K α hα₀ hα₁ hK hG0 hconv hG_top hG_bot n (fun t => r (t + 1)) hr (r 0 x - ξ))
  simp only [hsh, h0]
  rw [vw_ofReal_stage φ G K α hα₀ hK hG0 _ hfin x (r 0 x)]
  rfl

end DP


/-! ## lemmas 2 and 5 (copied from their solutions) -/

lemma vw_ofReal_sub (g : ℝ) :
    ((ENNReal.ofReal g : ℝ≥0∞) : EReal) - ((ENNReal.ofReal (-g) : ℝ≥0∞) : EReal) = (g : EReal) := by
  rw [EReal.coe_ennreal_ofReal, EReal.coe_ennreal_ofReal, ← EReal.coe_sub]
  congr 1
  rcases le_total 0 g with h | h
  · rw [max_eq_left h, max_eq_right (by linarith)]; ring
  · rw [max_eq_right h, max_eq_left (by linarith)]; ring

lemma vw_pc0 (φ : PMF ℕ) (G : ℤ → ℝ) (K : ℝ) (Z : Policy) (x : ℤ) :
    periodCost φ G K Z x 0 =
      (K : EReal) * (((if x < Z 0 x finZeroElim then 1 else 0 : ℝ≥0∞)) : EReal) +
        (G (Z 0 x finZeroElim) : EReal) := by
  have hu : ∀ f : (Fin 0 → ℕ) → ℝ≥0∞, ∑' h, f h = f finZeroElim := fun f =>
    tsum_eq_single _ (fun h hh => absurd (Subsingleton.elim h _) hh)
  have hw : weight φ (finZeroElim : Fin 0 → ℕ) = 1 := by simp [weight]
  unfold periodCost orderProb expectedG
  rw [hu, hu, hu, hw, one_mul, one_mul, one_mul, vw_ofReal_sub]
  rfl

lemma vw_Y0 (Y : Policy) (s S : ℤ) (hrule : UsesRule Y 0 s S) (x : ℤ) :
    Y 0 x finZeroElim = sSRule s S x := hrule x finZeroElim

/-! ## strict improvement by coupling (lemmas 2 and 5) -/

lemma vw_wsum (φ : PMF ℕ) : ∀ t : ℕ, ∑' h : Fin t → ℕ, weight φ h = 1
  | 0 => by
    rw [tsum_eq_single (finZeroElim : Fin 0 → ℕ) (fun h hh => absurd (Subsingleton.elim h _) hh)]
    simp [weight]
  | t + 1 => by
    rw [← (Fin.consEquiv (fun _ : Fin (t + 1) => ℕ)).tsum_eq (fun h => weight φ h)]
    have : ∀ c : ℕ × (Fin t → ℕ), weight φ ((Fin.consEquiv (fun _ : Fin (t + 1) => ℕ)) c) =
        φ c.1 * weight φ c.2 := by
      intro c
      simp [weight, Fin.prod_univ_succ, Fin.consEquiv]
    simp only [this]
    rw [ENNReal.tsum_prod (f := fun a (g : Fin t → ℕ) => φ a * weight φ g)]
    simp only [ENNReal.tsum_mul_left, vw_wsum φ t, mul_one, PMF.tsum_coe]

def vwAux (Y : Policy) (x0 S : ℤ) : (t : ℕ) → ℤ → (Fin t → ℕ) → ℤ
  | 0, x, h => if x = x0 then S else Y 0 x h
  | t + 1, x, h => max (vwAux Y x0 S t x (Fin.init h) - (h (Fin.last t) : ℤ)) (Y (t + 1) x h)

lemma vwAux_state (Y : Policy) (x0 S : ℤ) (x : ℤ) (t : ℕ) (h : Fin (t + 1) → ℕ) :
    state (vwAux Y x0 S) x (t + 1) h = vwAux Y x0 S t x (Fin.init h) - (h (Fin.last t) : ℤ) := rfl

lemma vwAux_adm (Y : Policy) (hY : Admissible Y) (x0 S : ℤ) (hx0 : x0 ≤ S) :
    Admissible (vwAux Y x0 S) := by
  intro t x h
  rcases t with _ | t
  · show x ≤ vwAux Y x0 S 0 x h
    simp only [vwAux]
    split_ifs with hx
    · omega
    · exact hY 0 x h
  · rw [vwAux_state]; simp only [vwAux]; exact le_max_left _ _

lemma vwAux_inv (Y : Policy) (hY : Admissible Y) (x0 S : ℤ) (h0 : Y 0 x0 finZeroElim ≤ S) :
    ∀ t (h : Fin t → ℕ), Y t x0 h ≤ vwAux Y x0 S t x0 h ∧
      (vwAux Y x0 S t x0 h = Y t x0 h ∨ vwAux Y x0 S t x0 h ≤ S) := by
  intro t
  induction t with
  | zero =>
    intro h
    have e : h = finZeroElim := Subsingleton.elim _ _
    subst e
    simp only [vwAux, if_pos rfl]
    exact ⟨h0, Or.inr le_rfl⟩
  | succ t ih =>
    intro h
    simp only [vwAux]
    refine ⟨le_max_right _ _, ?_⟩
    rcases le_or_gt (vwAux Y x0 S t x0 (Fin.init h) - (h (Fin.last t) : ℤ)) (Y (t + 1) x0 h)
      with hc | hc
    · left; exact max_eq_right hc
    · right
      rw [max_eq_left hc.le]
      rcases (ih (Fin.init h)).2 with he | he
      · have := hY (t + 1) x0 h
        simp only [state] at this
        rw [he] at hc
        have : (h (Fin.last t) : ℤ) ≥ 0 := by positivity
        omega
      · have : (h (Fin.last t) : ℤ) ≥ 0 := by positivity
        omega

lemma vw_pc_succ_le (φ : PMF ℕ) (G : ℤ → ℝ) (K : ℝ) (hK : 0 ≤ K)
    (hconv : ∀ y : ℤ, G (y + 1) - G y ≤ G (y + 2) - G (y + 1))
    (hG_top : Filter.Tendsto G Filter.atTop Filter.atTop)
    (hG_bot : Filter.Tendsto G Filter.atBot Filter.atTop)
    (Y : Policy) (hY : Admissible Y) (x0 : ℤ) (h0 : Y 0 x0 finZeroElim ≤ SLow G) (t : ℕ) :
    periodCost φ G K (vwAux Y x0 (SLow G)) x0 (t + 1) ≤ periodCost φ G K Y x0 (t + 1) := by
  have hinv := vwAux_inv Y hY x0 (SLow G) h0
  have hG : ∀ h : Fin (t + 1) → ℕ, G (vwAux Y x0 (SLow G) (t + 1) x0 h) ≤ G (Y (t + 1) x0 h) := by
    intro h
    rcases hinv (t + 1) h with ⟨hle, he | he⟩
    · rw [he]
    · exact vw_anti G hconv hG_top hG_bot _ _ hle he
  unfold periodCost
  apply add_le_add
  · apply mul_le_mul_of_nonneg_left _ (by exact_mod_cast hK)
    apply EReal.coe_ennreal_le_coe_ennreal_iff.2
    unfold orderProb
    refine ENNReal.tsum_le_tsum fun h => ?_
    refine mul_le_mul_of_nonneg_left ?_ (by simp)
    have hst : state Y x0 (t + 1) h ≤ state (vwAux Y x0 (SLow G)) x0 (t + 1) h := by
      rw [vwAux_state]; simp only [state]
      have := (hinv t (Fin.init h)).1
      omega
    split_ifs with h1 h2 <;> try simp
    exfalso
    apply h2
    have : vwAux Y x0 (SLow G) (t + 1) x0 h = Y (t + 1) x0 h := by
      rw [vwAux_state] at h1
      simp only [vwAux] at h1 ⊢
      rcases le_total (vwAux Y x0 (SLow G) t x0 (Fin.init h) - (h (Fin.last t) : ℤ))
        (Y (t + 1) x0 h) with hc | hc
      · exact max_eq_right hc
      · rw [max_eq_left hc] at h1; omega
    rw [this] at h1
    omega
  · unfold expectedG
    apply EReal.sub_le_sub
    · apply EReal.coe_ennreal_le_coe_ennreal_iff.2
      refine ENNReal.tsum_le_tsum fun h => ?_
      gcongr; exact hG h
    · apply EReal.coe_ennreal_le_coe_ennreal_iff.2
      refine ENNReal.tsum_le_tsum fun h => ?_
      gcongr; linarith [hG h]

lemma vw_pc_lower (φ : PMF ℕ) (G : ℤ → ℝ) (K : ℝ) (hK : 0 ≤ K) (m : ℝ) (hm : ∀ y, m ≤ G y)
    (Z : Policy) (x : ℤ) (t : ℕ) : ((-(max (-m) 0) : ℝ) : EReal) ≤ periodCost φ G K Z x t := by
  have hB : (∑' h : Fin t → ℕ, weight φ h * ENNReal.ofReal (-G (Z t x h))) ≤ ENNReal.ofReal (-m) := by
    calc (∑' h : Fin t → ℕ, weight φ h * ENNReal.ofReal (-G (Z t x h)))
        ≤ ∑' h : Fin t → ℕ, weight φ h * ENNReal.ofReal (-m) :=
          ENNReal.tsum_le_tsum fun h => by gcongr; linarith [hm (Z t x h)]
      _ = ENNReal.ofReal (-m) := by rw [ENNReal.tsum_mul_right, vw_wsum, one_mul]
  have hB' : ((∑' h : Fin t → ℕ, weight φ h * ENNReal.ofReal (-G (Z t x h)) : ℝ≥0∞) : EReal) ≤
      ((max (-m) 0 : ℝ) : EReal) := by
    rw [← EReal.coe_ennreal_ofReal]; exact_mod_cast hB
  unfold periodCost expectedG
  have h1 : (0 : EReal) ≤ (K : EReal) * ((orderProb φ Z x t : ℝ≥0∞) : EReal) :=
    mul_nonneg (by exact_mod_cast hK) (EReal.coe_ennreal_nonneg _)
  calc ((-(max (-m) 0) : ℝ) : EReal) = 0 + ((0 : ℝ) - ((max (-m) 0 : ℝ)) : EReal) := by
        rw [zero_add, EReal.coe_neg, EReal.coe_zero, zero_sub]
    _ ≤ _ := by
        refine add_le_add h1 (EReal.sub_le_sub ?_ hB')
        exact EReal.coe_ennreal_nonneg _

lemma vw_term_ne_bot (φ : PMF ℕ) (G : ℤ → ℝ) (K α : ℝ) (hα₀ : 0 ≤ α) (hK : 0 ≤ K) (m : ℝ)
    (hm : ∀ y, m ≤ G y) (Z : Policy) (x : ℤ) (t : ℕ) :
    ((α ^ t : ℝ) : EReal) * periodCost φ G K Z x t ≠ ⊥ := by
  have := mul_le_mul_of_nonneg_left (vw_pc_lower φ G K hK m hm Z x t)
    (show (0 : EReal) ≤ ((α ^ t : ℝ) : EReal) by exact_mod_cast pow_nonneg hα₀ t)
  intro h
  rw [h, ← EReal.coe_mul] at this
  exact EReal.coe_ne_bot _ (le_bot_iff.1 this)

lemma vw_base_finite (φ : PMF ℕ) (G : ℤ → ℝ) (K α : ℝ) (hα₀ : 0 ≤ α) (hK : 0 ≤ K) (m : ℝ)
    (hm : ∀ y, m ≤ G y) (n : ℕ) (c : ℤ → ℤ) (x : ℤ) :
    cost φ G K α n x (fun _ x _ => c x) ≠ ⊤ := by
  unfold cost
  refine Finset.sum_induction _ (fun z => z ≠ ⊤) (fun a b ha hb => ?_) (by simp) ?_
  · exact (EReal.add_lt_top ha hb).ne
  intro t _
  have hlow := vw_pc_lower φ G K hK m hm (fun _ x _ => c x) x t
  have hop : orderProb φ (fun _ x _ => c x) x t ≠ ⊤ := by
    apply ne_top_of_le_ne_top ENNReal.one_ne_top
    unfold orderProb
    calc _ ≤ ∑' h : Fin t → ℕ, weight φ h := ENNReal.tsum_le_tsum fun h => by
            split_ifs <;> simp
      _ = 1 := vw_wsum φ t
  have hA : (∑' h : Fin t → ℕ, weight φ h * ENNReal.ofReal (G (c x))) ≠ ⊤ := by
    rw [ENNReal.tsum_mul_right, vw_wsum, one_mul]; exact ENNReal.ofReal_ne_top
  have hup : periodCost φ G K (fun _ x _ => c x) x t ≤
      (((K * (orderProb φ (fun _ x _ => c x) x t).toReal) +
        (∑' h : Fin t → ℕ, weight φ h * ENNReal.ofReal (G (c x))).toReal : ℝ) : EReal) := by
    unfold periodCost expectedG
    rw [EReal.coe_add, EReal.coe_mul, EReal.coe_ennreal_toReal hop, EReal.coe_ennreal_toReal hA]
    refine add_le_add le_rfl ?_
    calc _ ≤ (((∑' h : Fin t → ℕ, weight φ h * ENNReal.ofReal (G (c x)) : ℝ≥0∞)) : EReal) - 0 :=
          EReal.sub_le_sub le_rfl (EReal.coe_ennreal_nonneg _)
      _ = _ := sub_zero _
  set P := periodCost φ G K (fun _ x _ => c x) x t
  have hP1 : P ≠ ⊤ := ne_top_of_le_ne_top (EReal.coe_ne_top _) hup
  have hP2 : P ≠ ⊥ := ne_bot_of_le_ne_bot (EReal.coe_ne_bot _) hlow
  rw [← EReal.coe_toReal hP1 hP2, ← EReal.coe_mul]
  exact EReal.coe_ne_top _

lemma vw_strict (φ : PMF ℕ) (G : ℤ → ℝ) (K α : ℝ) (hα₀ : 0 ≤ α) (hK : 0 ≤ K)
    (hconv : ∀ y : ℤ, G (y + 1) - G y ≤ G (y + 2) - G (y + 1))
    (hG_top : Filter.Tendsto G Filter.atTop Filter.atTop)
    (hG_bot : Filter.Tendsto G Filter.atBot Filter.atTop)
    (n : ℕ) (hn : 1 ≤ n) (Y : Policy) (hY : IsOptimal φ G K α n Y) (x0 : ℤ)
    (h0 : Y 0 x0 finZeroElim ≤ SLow G) (hx0 : x0 ≤ SLow G)
    (hreal : K * (if x0 < SLow G then 1 else 0) + G (SLow G) <
      K * (if x0 < Y 0 x0 finZeroElim then 1 else 0) + G (Y 0 x0 finZeroElim)) : False := by
  have hmin := vw_SLow_min G hG_top hG_bot
  set S := SLow G
  set Yc := vwAux Y x0 S
  have hadm := vwAux_adm Y hY.1 x0 S hx0
  have hle := hY.2 Yc hadm x0
  have hbadm : Admissible (fun _ x _ => max x S) := by
    intro t x h
    rcases t with _ | t
    · exact le_max_left _ _
    · simp only [state]
      have : (h (Fin.last t) : ℤ) ≥ 0 := by positivity
      omega
  have hfin := lt_of_le_of_lt (hY.2 _ hbadm x0)
    (vw_base_finite φ G K α hα₀ hK (G S) hmin n (fun x => max x S) x0).lt_top
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  unfold cost at hle hfin
  rw [Finset.sum_range_succ', Finset.sum_range_succ'] at hle
  rw [Finset.sum_range_succ'] at hfin
  set R' := ∑ t ∈ Finset.range m, ((α ^ (t + 1) : ℝ) : EReal) * periodCost φ G K Yc x0 (t + 1)
  set R := ∑ t ∈ Finset.range m, ((α ^ (t + 1) : ℝ) : EReal) * periodCost φ G K Y x0 (t + 1)
  have hRR : R' ≤ R := Finset.sum_le_sum fun t _ =>
    mul_le_mul_of_nonneg_left (vw_pc_succ_le φ G K hK hconv hG_top hG_bot Y hY.1 x0 h0 t)
      (by exact_mod_cast pow_nonneg hα₀ _)
  have hR'bot : R' ≠ ⊥ := Finset.sum_induction _ (fun z => z ≠ ⊥)
    (fun a b ha hb => by simp [EReal.add_eq_bot_iff, ha, hb]) (by simp)
    (fun t _ => vw_term_ne_bot φ G K α hα₀ hK (G S) hmin Yc x0 (t + 1))
  have hp0 : ∀ Z : Policy, ((α ^ 0 : ℝ) : EReal) * periodCost φ G K Z x0 0 =
      (((K * (if x0 < Z 0 x0 finZeroElim then 1 else 0 : ℝ)) + G (Z 0 x0 finZeroElim) : ℝ) :
        EReal) := by
    intro Z
    rw [vw_pc0, pow_zero, EReal.coe_one, one_mul, EReal.coe_add, EReal.coe_mul]
    split_ifs <;> simp
  rw [hp0] at hle hfin
  rw [hp0] at hle
  have hYc0 : Yc 0 x0 finZeroElim = S := by simp [Yc, vwAux]
  rw [hYc0] at hle
  have hRtop : R ≠ ⊤ := by
    intro h; rw [h, EReal.top_add_coe] at hfin; exact lt_irrefl _ hfin
  have hlt := EReal.add_lt_add_of_lt_of_le (EReal.coe_lt_coe_iff.2 hreal) hRR hR'bot hRtop
  rw [add_comm, add_comm _ R] at hlt
  exact absurd hle (not_le.2 hlt)

theorem lemma2_core (G : ℤ → ℝ) (K α : ℝ) (hα₀ : 0 ≤ α) (hK : 0 ≤ K)
    (hconv : ∀ y : ℤ, G (y + 1) - G y ≤ G (y + 2) - G (y + 1))
    (hG_top : Filter.Tendsto G Filter.atTop Filter.atTop)
    (hG_bot : Filter.Tendsto G Filter.atBot Filter.atTop)
    (φ : PMF ℕ) (n : ℕ) (hn : 2 ≤ n)
    (Y : Policy) (sn Sn : ℤ) (hY : IsOptimal φ G K α n Y) (hsS : sn ≤ Sn)
    (hrule : UsesRule Y 0 sn Sn) : SLow G ≤ Sn := by
  by_contra hc
  push_neg at hc
  have hY0 := vw_Y0 Y sn Sn hrule (sn - 1)
  have e : sSRule sn Sn (sn - 1) = Sn := by unfold sSRule; rw [if_pos (by omega)]
  rw [e] at hY0
  apply vw_strict φ G K α hα₀ hK hconv hG_top hG_bot n (by omega) Y hY (sn - 1)
    (by omega) (by omega)
  rw [hY0, if_pos (by omega), if_pos (by omega)]
  have := vw_SLow_strict G hG_top hG_bot Sn hc
  linarith

theorem lemma5_core (G : ℤ → ℝ) (K α : ℝ) (hα₀ : 0 ≤ α) (hK : 0 ≤ K)
    (hconv : ∀ y : ℤ, G (y + 1) - G y ≤ G (y + 2) - G (y + 1))
    (hG_top : Filter.Tendsto G Filter.atTop Filter.atTop)
    (hG_bot : Filter.Tendsto G Filter.atBot Filter.atTop)
    (φ : PMF ℕ) (n : ℕ) (hn : 2 ≤ n)
    (Y : Policy) (sn Sn : ℤ) (hY : IsOptimal φ G K α n Y) (hsS : sn ≤ Sn)
    (hrule : UsesRule Y 0 sn Sn) : sLow G K ≤ sn := by
  by_contra hc
  push_neg at hc
  obtain ⟨N, hN⟩ := vw_bdd_below G hG_bot (G (SLow G) + K)
  have hbdd : BddBelow {y : ℤ | G y ≤ G (SLow G) + K} := ⟨N, fun y hy => (hN y hy).le⟩
  have hsl : sLow G K ≤ SLow G := csInf_le hbdd (show G (SLow G) ≤ G (SLow G) + K by linarith)
  have hnot : ¬ G sn ≤ G (SLow G) + K := fun h => absurd (csInf_le hbdd h) (not_le.2 hc)
  have hY0 := vw_Y0 Y sn Sn hrule sn
  have e : sSRule sn Sn sn = sn := by unfold sSRule; rw [if_neg (lt_irrefl _)]
  rw [e] at hY0
  apply vw_strict φ G K α hα₀ hK hconv hG_top hG_bot n (by omega) Y hY sn
    (by omega) (by omega)
  rw [hY0, if_neg (lt_irrefl _)]
  have hi : K * (if sn < SLow G then (1:ℝ) else 0) ≤ K := by split_ifs <;> linarith
  linarith


/-! ## the main theorem for `G ≥ 0` -/

theorem vw_main_nonneg (G : ℤ → ℝ) (K α : ℝ) (hα₀ : 0 ≤ α) (hα₁ : α ≤ 1) (hK : 0 ≤ K)
    (hconv : ∀ y : ℤ, G (y + 1) - G y ≤ G (y + 2) - G (y + 1))
    (hG_top : Filter.Tendsto G Filter.atTop Filter.atTop)
    (hG_bot : Filter.Tendsto G Filter.atBot Filter.atTop)
    (hG0 : ∀ y, 0 ≤ G y) (φ : PMF ℕ) (n : ℕ) (hn : 2 ≤ n) :
    ∃ (Y : Policy) (sn Sn : ℤ), IsOptimal φ G K α n Y ∧ IsSSPolicy n Y ∧
      sn ≤ Sn ∧ UsesRule Y 0 sn Sn ∧
      sLow G K ≤ sn ∧ sn ≤ sHigh G K α ∧ sHigh G K α ≤ SLow G ∧
      SLow G ≤ Sn ∧ Sn ≤ SHigh G K α := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hst := fun k => vw_stage_dp φ G K α hα₀ hα₁ hK hG0 hconv hG_top hG_bot k
  have hprops := vw_dp_props φ G K α hα₀ hα₁ hK hG0 hconv hG_top hG_bot m
  obtain ⟨hfin, hsS, hmin⟩ := hst m
  set sn := sOf K (hfun φ G α (dp φ G K α m)) with hsn
  set Sn := SOf (hfun φ G α (dp φ G K α m)) with hSn
  -- generic optimality criterion
  have hopt : ∀ Y : Policy, Admissible Y →
      (∀ x, costE φ G K α (m + 1) x Y ≤ ENNReal.ofReal (dp φ G K α (m + 1) x)) →
      IsOptimal φ G K α (m + 1) Y := by
    intro Y hY hle
    refine ⟨hY, fun Y' hY' x => ?_⟩
    rw [vw_cost_eq φ G K α hG0 hK hα₀, vw_cost_eq φ G K α hG0 hK hα₀]
    exact EReal.coe_ennreal_le_coe_ennreal_iff.2 ((hle x).trans
      (vw_lower φ G K α hα₀ hα₁ hK hG0 hconv hG_top hG_bot (m + 1) Y' hY' x))
  -- the dynamic-programming policy
  let r : ℕ → ℤ → ℤ := fun t => ruleOf φ G K α (m + 1 - 1 - t)
  have hradm : ∀ t x, x ≤ r t x := fun t x =>
    vw_ruleOf_ge φ G K α hα₀ hα₁ hK hG0 hconv hG_top hG_bot _ x
  have hcostY : ∀ x, costE φ G K α (m + 1) x (mkP r) = ENNReal.ofReal (dp φ G K α (m + 1) x) :=
    vw_costE_mkP φ G K α hα₀ hα₁ hK hG0 hconv hG_top hG_bot (m + 1) r (fun t _ => rfl)
  have hYopt : IsOptimal φ G K α (m + 1) (mkP r) :=
    hopt _ (mkP_adm r hradm) (fun x => (hcostY x).le)
  have hYrule : UsesRule (mkP r) 0 sn Sn := mkP_rule r 0 sn Sn (fun x => by
    show ruleOf φ G K α (m + 1 - 1 - 0) x = _
    rw [show m + 1 - 1 - 0 = m by omega]; rfl)
  have hSLow : SLow G ≤ Sn := lemma2_core G K α hα₀ hK hconv hG_top hG_bot φ (m + 1) (by omega)
    (mkP r) sn Sn hYopt hsS hYrule
  -- facts about `G`
  have hmin0 := vw_SLow_min G hG_top hG_bot
  have hsHm := vw_sHigh_mem G hG_top hG_bot K α hα₁ hK
  have hsHle := vw_sHigh_le_SLow G hG_top hG_bot K α hα₁ hK
  obtain ⟨hSH1, hSH2⟩ := vw_SHigh_mem G hG_top hG_bot K α
  -- the modified first-period rule
  set s' := min sn (sHigh G K α) with hs'
  set S' := if SHigh G K α < Sn then SLow G else Sn with hS'
  have hs'S' : s' ≤ S' := by rw [hS']; split_ifs <;> omega
  have hS'le : S' ≤ Sn := by rw [hS']; split_ifs <;> omega
  let r' : ℕ → ℤ → ℤ := fun t => if t = 0 then sSRule s' S' else ruleOf φ G K α (m + 1 - 1 - t)
  have hr'0 : r' 0 = sSRule s' S' := rfl
  have hr'succ : ∀ t, t < m → r' (t + 1) = ruleOf φ G K α (m - 1 - t) := by
    intro t ht
    show (if t + 1 = 0 then sSRule s' S' else ruleOf φ G K α (m + 1 - 1 - (t + 1))) = _
    rw [if_neg (by omega), show m + 1 - 1 - (t + 1) = m - 1 - t by omega]
  have hr'adm : ∀ t x, x ≤ r' t x := by
    intro t x
    cases t with
    | zero =>
      show x ≤ sSRule s' S' x
      unfold sSRule; split_ifs <;> omega
    | succ t =>
      show x ≤ ruleOf φ G K α (m + 1 - 1 - (t + 1)) x
      exact vw_ruleOf_ge φ G K α hα₀ hα₁ hK hG0 hconv hG_top hG_bot _ x
  have hcostY' : ∀ x, costE φ G K α (m + 1) x (mkP r') ≤
      ENNReal.ofReal (dp φ G K α (m + 1) x) := by
    intro x
    rw [vw_costE_mkP_succ φ G K α hα₀ hα₁ hK hG0 hconv hG_top hG_bot m r' hr'succ x, hr'0]
    apply ENNReal.ofReal_le_ofReal
    have e : dp φ G K α (m + 1) x = K * (if x < sSRule sn Sn x then (1 : ℝ) else 0) +
        hfun φ G α (dp φ G K α m) (sSRule sn Sn x) := rfl
    rw [e]
    by_cases heq : sSRule s' S' x = sSRule sn Sn x
    · rw [heq]
    apply vw_hfun_compare φ G K α hα₀ hK (dp φ G K α m) hprops.1
      (fun z z' hz => vw_dp_mono_K φ G K α hα₀ hα₁ hK hG0 hconv hG_top hG_bot m z z' hz) hfin x
    · unfold sSRule; split_ifs <;> omega
    · have hx1 : x < sn := by
        by_contra hc
        apply heq
        unfold sSRule; rw [if_neg (by omega), if_neg (by omega)]
      have e2 : sSRule sn Sn x = Sn := by unfold sSRule; rw [if_pos hx1]
      rw [e2, if_pos (by omega : x < Sn)]
      by_cases hx2 : x < s'
      · have e1 : sSRule s' S' x = S' := by unfold sSRule; rw [if_pos hx2]
        rw [e1, if_pos (by omega : x < S')]
        have hc : SHigh G K α < Sn := by
          by_contra hc
          apply heq
          rw [e1, e2, hS', if_neg hc]
        rw [hS', if_pos hc]
        have := vw_mono G hconv hG_top hG_bot (SHigh G K α + 1) Sn (by omega) (by omega)
        linarith
      · have e1 : sSRule s' S' x = x := by unfold sSRule; rw [if_neg hx2]
        rw [e1, if_neg (lt_irrefl x)]
        have hsH : sHigh G K α ≤ x := by
          by_contra hc
          push_neg at hc
          apply hx2
          rw [hs']; exact lt_min hx1 hc
        rcases le_or_gt x (SLow G) with hxS | hxS
        · have := vw_anti G hconv hG_top hG_bot (sHigh G K α) x hsH hxS
          have := hmin0 Sn
          nlinarith
        · have := vw_mono G hconv hG_top hG_bot x Sn (by omega) hxS.le
          nlinarith
  have hY'opt : IsOptimal φ G K α (m + 1) (mkP r') := hopt (mkP r') (mkP_adm r' hr'adm) hcostY'
  have hY'rule : UsesRule (mkP r') 0 s' S' := mkP_rule r' 0 s' S' (fun x => rfl)
  have hsLow : sLow G K ≤ s' := lemma5_core G K α hα₀ hK hconv hG_top hG_bot φ (m + 1) (by omega)
    (mkP r') s' S' hY'opt hs'S' hY'rule
  refine ⟨mkP r', s', S', hY'opt, ?_, hs'S', hY'rule, hsLow, min_le_right _ _, hsHle, ?_, ?_⟩
  · refine ⟨fun t => if t = 0 then s' else sOf K (hfun φ G α (dp φ G K α (m + 1 - 1 - t))),
      fun t => if t = 0 then S' else SOf (hfun φ G α (dp φ G K α (m + 1 - 1 - t))),
      fun t ht => ?_⟩
    dsimp only
    by_cases h0 : t = 0
    · subst h0
      rw [if_pos rfl, if_pos rfl]
      exact ⟨hs'S', hY'rule⟩
    · rw [if_neg h0, if_neg h0]
      refine ⟨(hst _).2.1, mkP_rule r' t _ _ (fun x => ?_)⟩
      show (if t = 0 then sSRule s' S' else ruleOf φ G K α (m + 1 - 1 - t)) x = _
      rw [if_neg h0]; rfl
  · rw [hS']; split_ifs <;> omega
  · rw [hS']; split_ifs <;> omega

/-! ## shifting `G` by a constant -/

lemma vw_SLow_shift (G : ℤ → ℝ) (c : ℝ) : SLow (fun y => G y - c) = SLow G := by
  unfold SLow
  congr 1
  ext y
  simp only [Set.mem_setOf_eq, sub_le_sub_iff_right]

lemma vw_SHigh_shift (G : ℤ → ℝ) (c K α : ℝ) : SHigh (fun y => G y - c) K α = SHigh G K α := by
  unfold SHigh
  rw [vw_SLow_shift]
  congr 1
  ext y
  simp only [Set.mem_setOf_eq]
  constructor <;> rintro ⟨h1, h2⟩ <;> exact ⟨h1, by linarith⟩

lemma vw_sLow_shift (G : ℤ → ℝ) (c K : ℝ) : sLow (fun y => G y - c) K = sLow G K := by
  unfold sLow
  rw [vw_SLow_shift]
  congr 1
  ext y
  simp only [Set.mem_setOf_eq]
  constructor <;> intro h <;> linarith

lemma vw_sHigh_shift (G : ℤ → ℝ) (c K α : ℝ) : sHigh (fun y => G y - c) K α = sHigh G K α := by
  unfold sHigh
  rw [vw_SLow_shift]
  congr 1
  ext y
  simp only [Set.mem_setOf_eq]
  constructor <;> intro h <;> linarith

lemma vw_ofReal_shift_id (g c : ℝ) (h : c ≤ g) :
    ENNReal.ofReal (g - c) + ENNReal.ofReal (-g) + ENNReal.ofReal c =
      ENNReal.ofReal g + ENNReal.ofReal (-c) := by
  rcases le_total 0 c with hc | hc
  · rw [ENNReal.ofReal_of_nonpos (by linarith : -g ≤ 0),
      ENNReal.ofReal_of_nonpos (by linarith : -c ≤ 0), add_zero, add_zero,
      ← ENNReal.ofReal_add (by linarith) hc]
    exact congrArg ENNReal.ofReal (by ring)
  · rcases le_total 0 g with hg | hg
    · rw [ENNReal.ofReal_of_nonpos (by linarith : -g ≤ 0), ENNReal.ofReal_of_nonpos hc, add_zero,
        add_zero, ← ENNReal.ofReal_add hg (by linarith)]
      exact congrArg ENNReal.ofReal (by ring)
    · rw [ENNReal.ofReal_of_nonpos hg, ENNReal.ofReal_of_nonpos hc, zero_add, add_zero,
        ← ENNReal.ofReal_add (by linarith) (by linarith)]
      exact congrArg ENNReal.ofReal (by ring)

lemma vw_expectedG_shift (φ : PMF ℕ) (G : ℤ → ℝ) (Y : Policy) (x : ℤ) (t : ℕ) (c : ℝ)
    (hc : ∀ y, c ≤ G y) :
    expectedG φ G Y x t = expectedG φ (fun y => G y - c) Y x t + (c : EReal) := by
  unfold expectedG
  set A := ∑' h : Fin t → ℕ, weight φ h * ENNReal.ofReal (G (Y t x h)) with hA
  set B := ∑' h : Fin t → ℕ, weight φ h * ENNReal.ofReal (-G (Y t x h)) with hB
  set A' := ∑' h : Fin t → ℕ, weight φ h * ENNReal.ofReal (G (Y t x h) - c) with hA'
  have hB' : (∑' h : Fin t → ℕ, weight φ h * ENNReal.ofReal (-(G (Y t x h) - c))) = 0 := by
    have : ∀ h : Fin t → ℕ, weight φ h * ENNReal.ofReal (-(G (Y t x h) - c)) = 0 := fun h => by
      rw [ENNReal.ofReal_of_nonpos (by linarith [hc (Y t x h)]), mul_zero]
    simp only [this, tsum_zero]
  rw [hB', EReal.coe_ennreal_zero, sub_zero]
  have hid : A' + B + ENNReal.ofReal c = A + ENNReal.ofReal (-c) := by
    have h1 : ∀ h : Fin t → ℕ, weight φ h * ENNReal.ofReal (G (Y t x h) - c) +
        weight φ h * ENNReal.ofReal (-G (Y t x h)) + weight φ h * ENNReal.ofReal c =
        weight φ h * ENNReal.ofReal (G (Y t x h)) + weight φ h * ENNReal.ofReal (-c) := by
      intro h
      rw [← mul_add, ← mul_add, ← mul_add, vw_ofReal_shift_id _ _ (hc _)]
    have e1 : ∑' h : Fin t → ℕ, (weight φ h * ENNReal.ofReal (G (Y t x h) - c) +
        weight φ h * ENNReal.ofReal (-G (Y t x h)) + weight φ h * ENNReal.ofReal c) =
        ∑' h : Fin t → ℕ, (weight φ h * ENNReal.ofReal (G (Y t x h)) +
          weight φ h * ENNReal.ofReal (-c)) := tsum_congr h1
    rw [ENNReal.tsum_add, ENNReal.tsum_add, ENNReal.tsum_add, ENNReal.tsum_mul_right,
      ENNReal.tsum_mul_right, vw_wsum, one_mul, one_mul] at e1
    exact e1
  have hBfin : B ≠ ⊤ := by
    refine ne_top_of_le_ne_top (ENNReal.ofReal_ne_top (r := -c)) ?_
    rw [hB]
    calc ∑' h : Fin t → ℕ, weight φ h * ENNReal.ofReal (-G (Y t x h))
        ≤ ∑' h : Fin t → ℕ, weight φ h * ENNReal.ofReal (-c) :=
          ENNReal.tsum_le_tsum fun h => mul_le_mul_of_nonneg_left
            (ENNReal.ofReal_le_ofReal (by linarith [hc (Y t x h)])) bot_le
      _ = ENNReal.ofReal (-c) := by rw [ENNReal.tsum_mul_right, vw_wsum, one_mul]
  clear_value A B A'
  by_cases hAtop : A = ⊤
  · have hA'top : A' = ⊤ := by
      by_contra hA'
      have : A' + B + ENNReal.ofReal c ≠ ⊤ :=
        ENNReal.add_ne_top.2 ⟨ENNReal.add_ne_top.2 ⟨hA', hBfin⟩, ENNReal.ofReal_ne_top⟩
      rw [hid, hAtop] at this
      exact this (by simp)
    rw [hAtop, hA'top, ← EReal.coe_ennreal_toReal hBfin, EReal.coe_ennreal_top,
      EReal.top_sub_coe, EReal.top_add_coe]
  · have hA'top : A' ≠ ⊤ := by
      intro hA'
      have : A' + B + ENNReal.ofReal c = ⊤ := by rw [hA']; simp
      rw [hid] at this
      exact absurd this (ENNReal.add_ne_top.2 ⟨hAtop, ENNReal.ofReal_ne_top⟩)
    have hr := congrArg ENNReal.toReal hid
    rw [ENNReal.toReal_add (ENNReal.add_ne_top.2 ⟨hA'top, hBfin⟩) ENNReal.ofReal_ne_top,
      ENNReal.toReal_add hA'top hBfin, ENNReal.toReal_add hAtop ENNReal.ofReal_ne_top,
      ENNReal.toReal_ofReal', ENNReal.toReal_ofReal'] at hr
    rw [← EReal.coe_ennreal_toReal hAtop, ← EReal.coe_ennreal_toReal hBfin,
      ← EReal.coe_ennreal_toReal hA'top, ← EReal.coe_sub, ← EReal.coe_add, EReal.coe_eq_coe_iff]
    rcases le_total 0 c with h0 | h0
    · rw [max_eq_left h0, max_eq_right (by linarith)] at hr; linarith
    · rw [max_eq_right h0, max_eq_left (by linarith)] at hr; linarith

lemma vw_cost_shift (φ : PMF ℕ) (G : ℤ → ℝ) (K α : ℝ) (hα₀ : 0 ≤ α) (c : ℝ) (hc : ∀ y, c ≤ G y)
    (x : ℤ) (Y : Policy) (n : ℕ) :
    cost φ G K α n x Y = cost φ (fun y => G y - c) K α n x Y +
      ((∑ t ∈ Finset.range n, α ^ t * c : ℝ) : EReal) := by
  induction n with
  | zero => simp [cost]
  | succ n ih =>
    unfold cost at ih ⊢
    rw [Finset.sum_range_succ, Finset.sum_range_succ, ih, Finset.sum_range_succ]
    have hp : periodCost φ G K Y x n = periodCost φ (fun y => G y - c) K Y x n + (c : EReal) := by
      unfold periodCost; rw [vw_expectedG_shift φ G Y x n c hc, add_assoc]
    rw [hp, EReal.left_distrib_of_nonneg_of_ne_top (by exact_mod_cast pow_nonneg hα₀ n)
      (EReal.coe_ne_top _), ← EReal.coe_mul, EReal.coe_add]
    abel

lemma vw_IsOptimal_shift (φ : PMF ℕ) (G : ℤ → ℝ) (K α : ℝ) (hα₀ : 0 ≤ α) (c : ℝ)
    (hc : ∀ y, c ≤ G y) (n : ℕ) (Y : Policy)
    (h : IsOptimal φ (fun y => G y - c) K α n Y) : IsOptimal φ G K α n Y := by
  refine ⟨h.1, fun Y' hY' x => ?_⟩
  rw [vw_cost_shift φ G K α hα₀ c hc, vw_cost_shift φ G K α hα₀ c hc]
  exact add_le_add (h.2 Y' hY' x) le_rfl

theorem theorem4a_core (G : ℤ → ℝ) (K α : ℝ) (hα₀ : 0 ≤ α) (hα₁ : α ≤ 1) (hK : 0 ≤ K)
    (hconv : ∀ y : ℤ, G (y + 1) - G y ≤ G (y + 2) - G (y + 1))
    (hG_top : Filter.Tendsto G Filter.atTop Filter.atTop)
    (hG_bot : Filter.Tendsto G Filter.atBot Filter.atTop)
    (φ : PMF ℕ) (n : ℕ) (hn : 2 ≤ n) :
    ∃ (Y : Policy) (sn Sn : ℤ), IsOptimal φ G K α n Y ∧ IsSSPolicy n Y ∧
      sn ≤ Sn ∧ UsesRule Y 0 sn Sn ∧
      sLow G K ≤ sn ∧ sn ≤ sHigh G K α ∧ sHigh G K α ≤ SLow G ∧
      SLow G ≤ Sn ∧ Sn ≤ SHigh G K α := by
  set c := G (SLow G) with hcdef
  have hc : ∀ y, c ≤ G y := vw_SLow_min G hG_top hG_bot
  have hconv' : ∀ y : ℤ, (fun y => G y - c) (y + 1) - (fun y => G y - c) y ≤
      (fun y => G y - c) (y + 2) - (fun y => G y - c) (y + 1) := fun y => by
    show G (y + 1) - c - (G y - c) ≤ G (y + 2) - c - (G (y + 1) - c)
    linarith [hconv y]
  have htop' : Filter.Tendsto (fun y => G y - c) Filter.atTop Filter.atTop :=
    (Filter.tendsto_atTop_add_const_right _ (-c) hG_top).congr (fun y => by ring)
  have hbot' : Filter.Tendsto (fun y => G y - c) Filter.atBot Filter.atTop :=
    (Filter.tendsto_atTop_add_const_right _ (-c) hG_bot).congr (fun y => by ring)
  obtain ⟨Y, sn, Sn, hopt, hss, hsS, hrule, h1, h2, h3, h4, h5⟩ :=
    vw_main_nonneg (fun y => G y - c) K α hα₀ hα₁ hK hconv' htop' hbot'
      (fun y => by show (0:ℝ) ≤ G y - c; linarith [hc y]) φ n hn
  rw [vw_sLow_shift] at h1
  rw [vw_sHigh_shift] at h2 h3
  rw [vw_SLow_shift] at h3 h4
  rw [vw_SHigh_shift] at h5
  exact ⟨Y, sn, Sn, vw_IsOptimal_shift φ G K α hα₀ c hc n Y hopt, hss, hsS, hrule, h1, h2, h3,
    h4, h5⟩


end VeinottWagnerSS.Bounds

open VeinottWagnerSS.Bounds


theorem solution (G : ℤ → ℝ) (K α : ℝ) (hα₀ : 0 ≤ α) (hα₁ : α ≤ 1) (hK : 0 ≤ K)
    (hconv : ∀ y : ℤ, G (y + 1) - G y ≤ G (y + 2) - G (y + 1))
    (hG_top : Filter.Tendsto G Filter.atTop Filter.atTop)
    (hG_bot : Filter.Tendsto G Filter.atBot Filter.atTop)
    (φ : PMF ℕ) (hμ : ∑' k : ℕ, (k : ℝ≥0∞) * φ k ≠ ⊤)
    (n : ℕ) (hn : 2 ≤ n) :
    ∃ (Y : Policy) (sn Sn : ℤ), IsOptimal φ G K α n Y ∧ IsSSPolicy n Y ∧
      sn ≤ Sn ∧ UsesRule Y 0 sn Sn ∧
      sLow G K ≤ sn ∧ sn ≤ sHigh G K α ∧ sHigh G K α ≤ SLow G ∧
      SLow G ≤ Sn ∧ Sn ≤ SHigh G K α := by
  exact theorem4a_core G K α hα₀ hα₁ hK hconv hG_top hG_bot φ n hn
