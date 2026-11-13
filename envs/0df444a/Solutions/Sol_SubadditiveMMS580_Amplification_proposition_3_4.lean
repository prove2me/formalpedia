-- Prove2me | solution 1 for SubadditiveMMS580.Amplification.proposition_3_4
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T03:11:47.196199+00:00
-- url     : https://prove2.me/submissions/dadc8b64-65a9-420a-bd22-dcbec85858d4

import Mathlib
import Definitions.Def_SubadditiveMMS580_Amplification_Setting
import Definitions.Def_MultiAllocToAlloc_Subadditive_Valuation
import Definitions.Def_MultiAllocToAlloc_Subadditive_Allocation
import Definitions.Def_SubmodOrder_Subadditive
import Theorems.Thm_SubadditiveMMS580_Amplification_corollary_3_3
import Theorems.Thm_SubadditiveMMS580_Amplification_theorem_1_4

section
set_option autoImplicit false

open MultiAllocToAlloc.Subadditive

namespace SubadditiveMMS580.Amplification.Dev.P34

variable {n m : ℕ}

/-- `U` can be served within `K` layers. -/
def Good (v : Fin n → Finset (Fin m) → ℝ) (K : ℕ) (U : Finset (Fin n)) : Prop :=
  ∃ (B : Fin n → Finset (Fin m)) (ℓ : Fin n → ℕ),
    (∀ i ∈ U, (1 : ℝ) / 2 ≤ v i (B i) ∧ ℓ i < K) ∧
    ∀ i ∈ U, ∀ j ∈ U, i ≠ j → ℓ i = ℓ j → Disjoint (B i) (B j)

theorem good_empty (v : Fin n → Finset (Fin m) → ℝ) (K : ℕ) : Good v K ∅ :=
  ⟨fun _ => ∅, fun _ => 0, by simp, by simp⟩

theorem good_mono (v : Fin n → Finset (Fin m) → ℝ) {K K' : ℕ} (h : K ≤ K')
    {U : Finset (Fin n)} (hU : Good v K U) : Good v K' U := by
  obtain ⟨B, ℓ, h1, h2⟩ := hU
  exact ⟨B, ℓ, fun i hi => ⟨(h1 i hi).1, lt_of_lt_of_le (h1 i hi).2 h⟩, h2⟩

theorem good_step (v : Fin n → Finset (Fin m) → ℝ) (K : ℕ) (U U' : Finset (Fin n))
    (C : Fin n → Finset (Fin m)) (hC : IsAllocation C) (_hsub : U' ⊆ U)
    (hserve : ∀ i ∈ U, i ∉ U' → (1 : ℝ) / 2 ≤ v i (C i)) (h : Good v K U') :
    Good v (K + 1) U := by
  classical
  obtain ⟨B, ℓ, h1, h2⟩ := h
  refine ⟨fun i => if i ∈ U' then B i else C i, fun i => if i ∈ U' then ℓ i else K, ?_, ?_⟩
  · intro i hi
    by_cases h' : i ∈ U'
    · simp only [h', if_true]
      exact ⟨(h1 i h').1, by have := (h1 i h').2; omega⟩
    · simp only [h', if_false]
      exact ⟨hserve i hi h', by omega⟩
  · intro i hi j hj hij hl
    by_cases hi' : i ∈ U' <;> by_cases hj' : j ∈ U'
    · simp only [hi', hj', if_true] at hl ⊢
      exact h2 i hi' j hj' hij hl
    · simp only [hi', hj', if_true, if_false] at hl ⊢
      have := (h1 i hi').2; omega
    · simp only [hi', hj', if_true, if_false] at hl ⊢
      have := (h1 j hj').2; omega
    · simp only [hi', hj', if_false]
      exact hC i j hij

theorem good_single (v : Fin n → Finset (Fin m) → ℝ) (hn : 1 ≤ n)
    (W : Fin n → Fin n → Finset (Fin m))
    (hW : ∀ i, SubadditiveMMS580.Amplification.IsValuableFamily (v i) (W i))
    (U : Finset (Fin n)) (hU : U.card = 1) : Good v 1 U := by
  obtain ⟨a, rfl⟩ := Finset.card_eq_one.1 hU
  refine ⟨fun i => W i ⟨0, hn⟩, fun _ => 0, ?_, ?_⟩
  · intro i hi
    refine ⟨?_, Nat.zero_lt_one⟩
    have := (hW i).2 ⟨0, hn⟩
    linarith
  · intro i hi j hj hij
    simp at hi hj
    exact absurd (hi.trans hj.symm) hij

/-- Index of the `a`-th member of `U`. -/
noncomputable def sig (U : Finset (Fin n)) (a : Fin U.card) : Fin n := ((U.equivFin.symm a : U) : Fin n)

theorem sig_injective (U : Finset (Fin n)) : Function.Injective (sig U) := by
  intro a b h
  have : (U.equivFin.symm a : U) = U.equivFin.symm b := Subtype.ext h
  exact U.equivFin.symm.injective this

theorem sig_mem (U : Finset (Fin n)) (a : Fin U.card) : sig U a ∈ U :=
  (U.equivFin.symm a).2

theorem transfer (U : Finset (Fin n)) (A : Fin U.card → Finset (Fin m))
    (hA : IsAllocation A) :
    ∃ C : Fin n → Finset (Fin m), IsAllocation C ∧ ∀ a, C (sig U a) = A a := by
  classical
  refine ⟨fun i => if h : i ∈ U then A (U.equivFin ⟨i, h⟩) else ∅, ?_, ?_⟩
  · intro i j hij
    by_cases hi : i ∈ U <;> by_cases hj : j ∈ U
    · simp only [hi, hj, dif_pos]
      apply hA
      intro h
      exact hij (by simpa using congrArg Subtype.val (U.equivFin.injective h))
    · simp [hj]
    · simp [hi]
    · simp [hi]
  · intro a
    have h := sig_mem U a
    simp only [h, dif_pos]
    congr 1
    have : (⟨sig U a, h⟩ : U) = U.equivFin.symm a := rfl
    rw [this]; simp

theorem card_transfer (U : Finset (Fin n)) (A : Fin U.card → Finset (Fin m))
    (C : Fin n → Finset (Fin m)) (hC : ∀ a, C (sig U a) = A a)
    (p : Fin n → Finset (Fin m) → Prop) [∀ i S, Decidable (p i S)] :
    (Finset.univ.filter (fun a : Fin U.card => p (sig U a) (A a))).card =
      (U.filter (fun i => p i (C i))).card := by
  classical
  have : U.filter (fun i => p i (C i)) =
      (Finset.univ.filter (fun a : Fin U.card => p (sig U a) (A a))).image (sig U) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨hi, hp⟩
      refine ⟨U.equivFin ⟨i, hi⟩, ?_, ?_⟩
      · have : sig U (U.equivFin ⟨i, hi⟩) = i := by simp [sig]
        rw [this, ← hC, this]; exact hp
      · simp [sig]
    · rintro ⟨a, hp, rfl⟩
      refine ⟨sig_mem U a, ?_⟩
      rw [hC]; exact hp
  rw [this, Finset.card_image_of_injective _ (sig_injective U)]

end SubadditiveMMS580.Amplification.Dev.P34
end

section
set_option autoImplicit false

open MultiAllocToAlloc.Subadditive

namespace SubadditiveMMS580.Amplification.Dev.P34

variable {n m : ℕ}

theorem step_cor (v : Fin n → Finset (Fin m) → ℝ)
    (hnorm : ∀ i, IsNormalized (v i)) (hmono : ∀ i, IsMonotone (v i))
    (hsub : ∀ i, SubmodOrder.Subadditive (v i))
    (W : Fin n → Fin n → Finset (Fin m))
    (hW : ∀ i, SubadditiveMMS580.Amplification.IsValuableFamily (v i) (W i))
    (U : Finset (Fin n)) :
    ∃ U' ⊆ U, (n / U.card + 1) * U'.card ≤ U.card ∧
      ∀ K, Good v K U' → Good v (K + 1) U := by
  classical
  by_cases hU : U = ∅
  · refine ⟨∅, by simp, by simp [hU], fun K h => ?_⟩
    subst hU; exact good_empty v _
  have hu : 1 ≤ U.card := Finset.card_pos.2 (Finset.nonempty_iff_ne_empty.2 hU)
  have hun : U.card ≤ n := by simpa using Finset.card_le_univ U
  obtain ⟨A, hA, hcount⟩ := SubadditiveMMS580.Amplification.corollary_3_3 U.card n hu hun
    (fun a => v (sig U a)) (fun a => hnorm _) (fun a => hmono _) (fun a => hsub _)
    (fun a => W (sig U a)) (fun a => hW _)
  obtain ⟨C, hC, hCa⟩ := transfer U A hA
  have hcard := card_transfer U A C hCa (fun i S => (1 : ℝ) / 2 ≤ v i S)
  refine ⟨U.filter (fun i => ¬ (1 : ℝ) / 2 ≤ v i (C i)), Finset.filter_subset _ _, ?_, ?_⟩
  · have hsum := Finset.card_filter_add_card_filter_not (s := U)
      (fun i => (1 : ℝ) / 2 ≤ v i (C i))
    have h1 : ((U.filter (fun i => (1 : ℝ) / 2 ≤ v i (C i))).card : ℝ) ≥
        (U.card : ℝ) * ((n / U.card : ℕ) : ℝ) / (((n / U.card : ℕ) : ℝ) + 1) := by
      rw [← hcard]; exact hcount
    have hk : (0 : ℝ) < ((n / U.card : ℕ) : ℝ) + 1 := by positivity
    rw [ge_iff_le, div_le_iff₀ hk] at h1
    have hsumR : ((U.filter (fun i => (1 : ℝ) / 2 ≤ v i (C i))).card : ℝ) +
        ((U.filter (fun i => ¬ (1 : ℝ) / 2 ≤ v i (C i))).card : ℝ) = U.card := by
      exact_mod_cast hsum
    have : (((n / U.card : ℕ) : ℝ) + 1) *
        ((U.filter (fun i => ¬ (1 : ℝ) / 2 ≤ v i (C i))).card : ℝ) ≤ U.card := by
      nlinarith
    exact_mod_cast this
  · intro K hK
    refine good_step v K U _ C hC (Finset.filter_subset _ _) ?_ hK
    intro i hi hi'
    simp only [Finset.mem_filter, not_and, not_not] at hi'
    exact hi' hi

theorem step_amp (v : Fin n → Finset (Fin m) → ℝ)
    (hnorm : ∀ i, IsNormalized (v i)) (hmono : ∀ i, IsMonotone (v i))
    (hsub : ∀ i, SubmodOrder.Subadditive (v i))
    (hn : 1 ≤ n)
    (W : Fin n → Fin n → Finset (Fin m))
    (hW : ∀ i, SubadditiveMMS580.Amplification.IsValuableFamily (v i) (W i))
    (U : Finset (Fin n)) (hU : 2 ≤ U.card) (ℓ : ℕ) (hℓ : 1 ≤ ℓ)
    (h4 : 4 * ℓ * (U.card - 1) ≤ n) :
    ∃ U' ⊆ U, U'.card ≤ ⌊(U.card : ℝ) * ((3 : ℝ) / 4) ^ ℓ⌋₊ ∧
      ∀ K, Good v K U' → Good v (K + 1) U := by
  classical
  obtain ⟨A, hA, hcount⟩ := (SubadditiveMMS580.Amplification.theorem_1_4 U.card n hU hn
    (fun a => v (sig U a)) (fun a => hnorm _) (fun a => hmono _) (fun a => hsub _)
    (fun a => W (sig U a)) (fun a => hW _) ℓ hℓ (le_trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (by omega))) h4)).2 h4
  obtain ⟨C, hC, hCa⟩ := transfer U A hA
  have hcard := card_transfer U A C hCa (fun i S => v i S < (1 : ℝ) / 2)
  refine ⟨U.filter (fun i => v i (C i) < (1 : ℝ) / 2), Finset.filter_subset _ _, ?_, ?_⟩
  · rw [← hcard]; exact hcount
  · intro K hK
    refine good_step v K U _ C hC (Finset.filter_subset _ _) ?_ hK
    intro i hi hi'
    simp only [Finset.mem_filter, not_and, not_lt] at hi'
    exact hi' hi

end SubadditiveMMS580.Amplification.Dev.P34
end

section
set_option autoImplicit false

open MultiAllocToAlloc.Subadditive

namespace SubadditiveMMS580.Amplification.Dev.P34

variable {n m : ℕ}

theorem tower_pos (s : ℕ) : 1 ≤ tower s := by
  induction s with
  | zero => simp [tower]
  | succ k ih => simp only [tower]; exact Nat.one_le_two_pow

theorem tower_mono : Monotone tower := by
  apply monotone_nat_of_le_succ
  intro s
  show tower s ≤ 2 ^ tower s
  exact Nat.lt_two_pow_self.le

theorem tower_three : tower 3 = 16 := by
  simp [tower]

theorem le_tower_logStar (n : ℕ) : n ≤ tower (logStar n) :=
  Nat.find_spec (⟨n, le_tower_self n⟩ : ∃ r, n ≤ tower r)

theorem frac_pow_le (N ℓ : ℕ) (h : 3 * N ≤ ℓ) :
    ((3 : ℝ) / 4) ^ ℓ * 2 ^ N ≤ 1 := by
  have h1 : ((3 : ℝ) / 4) ^ ℓ ≤ ((3 : ℝ) / 4) ^ (3 * N) :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) h
  have h2 : ((3 : ℝ) / 4) ^ (3 * N) * 2 ^ N = ((27 : ℝ) / 32) ^ N := by
    rw [pow_mul, ← mul_pow]; norm_num
  calc ((3 : ℝ) / 4) ^ ℓ * 2 ^ N ≤ ((3 : ℝ) / 4) ^ (3 * N) * 2 ^ N := by gcongr
    _ = ((27 : ℝ) / 32) ^ N := h2
    _ ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)

variable (v : Fin n → Finset (Fin m) → ℝ)
    (hnorm : ∀ i, IsNormalized (v i)) (hmono : ∀ i, IsMonotone (v i))
    (hsub : ∀ i, SubmodOrder.Subadditive (v i)) (hn : 1 ≤ n)
    (W : Fin n → Fin n → Finset (Fin m))
    (hW : ∀ i, SubadditiveMMS580.Amplification.IsValuableFamily (v i) (W i))

include hnorm hmono hsub hn hW

theorem claim_s (t : ℕ) : ∀ s, 3 ≤ s → s + t = logStar n →
    ∀ U : Finset (Fin n), 1 ≤ U.card → 12 * U.card * tower s ≤ n → Good v t U := by
  induction t with
  | zero =>
    intro s hs hst U hU h
    exfalso
    have h1 := le_tower_logStar n
    have h2 : s = logStar n := by omega
    rw [← h2] at h1
    have := tower_pos s
    nlinarith
  | succ t ih =>
    intro s hs hst U hU h
    by_cases h1 : U.card = 1
    · exact good_mono v (by omega) (good_single v hn W hW U h1)
    have hU2 : 2 ≤ U.card := by omega
    have hN : 16 ≤ tower s := by
      rw [← tower_three]; exact tower_mono hs
    set N := tower s with hNdef
    set u := U.card with hu
    set ℓ := n / (4 * (u - 1)) with hℓdef
    have hℓ3 : 3 * N ≤ ℓ := by
      rw [hℓdef, Nat.le_div_iff_mul_le (by omega)]
      have : 3 * N * (4 * (u - 1)) ≤ 12 * u * N := by
        have : (u - 1) ≤ u := Nat.sub_le _ _
        nlinarith
      omega
    have hℓn : 4 * ℓ * (u - 1) ≤ n := by
      have := Nat.div_mul_le_self n (4 * (u - 1))
      rw [← hℓdef] at this
      nlinarith
    obtain ⟨U', hU'U, hcard, hstep⟩ := step_amp v hnorm hmono hsub hn W hW U hU2 ℓ (by omega) hℓn
    by_cases hemp : U'.card = 0
    · rw [Finset.card_eq_zero] at hemp
      subst hemp
      exact good_mono v (by omega) (hstep 0 (good_empty v 0))
    · have hU'1 : 1 ≤ U'.card := by omega
      refine hstep t (ih (s + 1) (by omega) (by omega) U' hU'1 ?_)
      have hreal : (U'.card : ℝ) ≤ (u : ℝ) * ((3 : ℝ) / 4) ^ ℓ :=
        le_trans (by exact_mod_cast hcard) (Nat.floor_le (by positivity))
      have hfr := frac_pow_le N ℓ hℓ3
      have : (U'.card : ℝ) * 2 ^ N ≤ u := by
        calc (U'.card : ℝ) * 2 ^ N ≤ (u : ℝ) * ((3 : ℝ) / 4) ^ ℓ * 2 ^ N := by gcongr
          _ = (u : ℝ) * (((3 : ℝ) / 4) ^ ℓ * 2 ^ N) := by ring
          _ ≤ (u : ℝ) * 1 := by gcongr
          _ = u := by ring
      have h3 : U'.card * 2 ^ N ≤ u := by exact_mod_cast this
      show 12 * U'.card * tower (s + 1) ≤ n
      have : tower (s + 1) = 2 ^ N := rfl
      rw [this]
      nlinarith

theorem claim_zero (hk : 3 ≤ logStar n) (U : Finset (Fin n)) (hU : 1 ≤ U.card)
    (h : 36 * U.card ≤ n) : Good v (logStar n - 2) U := by
  by_cases h1 : U.card = 1
  · exact good_mono v (by omega) (good_single v hn W hW U h1)
  have hU2 : 2 ≤ U.card := by omega
  set u := U.card with hu
  set ℓ := n / (4 * (u - 1)) with hℓdef
  have hℓ9 : 9 ≤ ℓ := by
    rw [hℓdef, Nat.le_div_iff_mul_le (by omega)]
    omega
  have hℓn : 4 * ℓ * (u - 1) ≤ n := by
    have := Nat.div_mul_le_self n (4 * (u - 1))
    rw [← hℓdef] at this
    nlinarith
  obtain ⟨U', hU'U, hcard, hstep⟩ := step_amp v hnorm hmono hsub hn W hW U hU2 ℓ (by omega) hℓn
  by_cases hemp : U'.card = 0
  · rw [Finset.card_eq_zero] at hemp
    subst hemp
    exact good_mono v (by omega) (hstep 0 (good_empty v 0))
  · have hU'1 : 1 ≤ U'.card := by omega
    have hk3 : logStar n - 2 = (logStar n - 3) + 1 := by omega
    rw [hk3]
    refine hstep _ (claim_s v hnorm hmono hsub hn W hW (logStar n - 3) 3 le_rfl (by omega) U' hU'1 ?_)
    have hreal : (U'.card : ℝ) ≤ (u : ℝ) * ((3 : ℝ) / 4) ^ ℓ :=
      le_trans (by exact_mod_cast hcard) (Nat.floor_le (by positivity))
    have h9 : ((3 : ℝ) / 4) ^ ℓ ≤ ((3 : ℝ) / 4) ^ 9 :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) hℓ9
    have : (U'.card : ℝ) ≤ (u : ℝ) * (19683 / 262144) := by
      calc (U'.card : ℝ) ≤ (u : ℝ) * ((3 : ℝ) / 4) ^ ℓ := hreal
        _ ≤ (u : ℝ) * ((3 : ℝ) / 4) ^ 9 := by gcongr
        _ = (u : ℝ) * (19683 / 262144) := by norm_num
    have h3 : (12 * U'.card * 16 : ℝ) ≤ 36 * u := by nlinarith
    show 12 * U'.card * tower 3 ≤ n
    rw [tower_three]
    have h4 : 12 * U'.card * 16 ≤ 36 * u := by exact_mod_cast h3
    omega

end SubadditiveMMS580.Amplification.Dev.P34
end

section
set_option autoImplicit false

open MultiAllocToAlloc.Subadditive

namespace SubadditiveMMS580.Amplification
open SubadditiveMMS580.Amplification.Dev.P34 in
theorem chk_proposition_3_4 (n : ℕ) (hn : 2 ≤ n) {m : ℕ}
    (v : Fin n → Finset (Fin m) → ℝ)
    (hnorm : ∀ i, IsNormalized (v i)) (hmono : ∀ i, IsMonotone (v i))
    (hsub : ∀ i, SubmodOrder.Subadditive (v i))
    (W : Fin n → Fin n → Finset (Fin m)) (hW : ∀ i, IsValuableFamily (v i) (W i)) :
    ∃ B : Fin n → Finset (Fin m), IsMultiAllocation (1 + logStar n) B ∧
      ∀ i : Fin n, (1 : ℝ) / 2 ≤ v i (B i) := by
  have hn1 : 1 ≤ n := by omega
  have hk1 : 1 ≤ logStar n := by
    by_contra hk
    have h0 : logStar n = 0 := by omega
    have := le_tower_logStar n
    rw [h0] at this
    simp [tower] at this
    omega
  have hcn : (Finset.univ : Finset (Fin n)).card = n := by simp
  -- three layers
  obtain ⟨U1, hU1, h1, s1⟩ := step_cor v hnorm hmono hsub W hW Finset.univ
  obtain ⟨U2, hU2, h2, s2⟩ := step_cor v hnorm hmono hsub W hW U1
  obtain ⟨U3, hU3, h3, s3⟩ := step_cor v hnorm hmono hsub W hW U2
  rw [hcn, Nat.div_self hn1] at h1
  have hu1 : 2 * U1.card ≤ n := by omega
  have hu2 : 6 * U2.card ≤ n := by
    by_cases h : U1.card = 0
    · have : U2.card = 0 := by
        have := Finset.card_le_card hU2; omega
      omega
    · have : 2 ≤ n / U1.card := (Nat.le_div_iff_mul_le (by omega)).2 (by omega)
      nlinarith
  have hu3 : 42 * U3.card ≤ n := by
    by_cases h : U2.card = 0
    · have : U3.card = 0 := by
        have := Finset.card_le_card hU3; omega
      omega
    · have : 6 ≤ n / U2.card := (Nat.le_div_iff_mul_le (by omega)).2 (by omega)
      nlinarith
  have hgood : Good v (1 + logStar n) Finset.univ := by
    by_cases hsmall : n ≤ 4
    · have hu2' : U2.card = 0 := by omega
      rw [Finset.card_eq_zero] at hu2'
      subst hu2'
      have g1 : Good v 1 U1 := good_mono v (by omega) (s2 0 (good_empty v 0))
      have g2 : Good v 2 Finset.univ := s1 1 g1
      exact good_mono v (by omega) g2
    · have hk3 : 3 ≤ logStar n := by
        by_contra hk
        have hle : logStar n ≤ 2 := by omega
        have := le_tower_logStar n
        have := tower_mono hle
        have h4 : tower 2 = 4 := by simp [tower]
        omega
      have g3 : Good v (logStar n - 2) U3 := by
        by_cases h : U3.card = 0
        · rw [Finset.card_eq_zero] at h; subst h; exact good_empty v _
        · exact claim_zero v hnorm hmono hsub hn1 W hW hk3 U3 (by omega) (by omega)
      have g2 := s3 _ g3
      have g1 := s2 _ g2
      have g0 := s1 _ g1
      exact good_mono v (by omega) g0
  obtain ⟨B, ℓ, hB1, hB2⟩ := hgood
  refine ⟨B, ?_, fun i => (hB1 i (Finset.mem_univ i)).1⟩
  intro e
  classical
  have hmaps : ∀ i ∈ Finset.univ.filter (fun i : Fin n => e ∈ B i), ℓ i ∈ Finset.range (1 + logStar n) := by
    intro i _
    exact Finset.mem_range.2 (hB1 i (Finset.mem_univ i)).2
  have hinj : Set.InjOn ℓ (Finset.univ.filter (fun i : Fin n => e ∈ B i) : Set (Fin n)) := by
    intro i hi j hj hij
    by_contra hne
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hi hj
    exact Finset.disjoint_left.1 (hB2 i (Finset.mem_univ _) j (Finset.mem_univ _) hne hij) hi hj
  have := Finset.card_le_card_of_injOn ℓ hmaps hinj
  simpa using this

end SubadditiveMMS580.Amplification
end

theorem solution : type_of% @SubadditiveMMS580.Amplification.chk_proposition_3_4 := @SubadditiveMMS580.Amplification.chk_proposition_3_4
