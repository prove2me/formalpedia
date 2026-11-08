-- Prove2me | solution 1 for SymNormLoad.lemma_2_3
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T18:42:20.963732+00:00
-- url     : https://prove2.me/submissions/0d0102f8-f395-48fc-8e69-c09650040db0

import Mathlib
import Definitions.Def_SymNormLoad_IsMonotoneSymmetricNorm
import Definitions.Def_SymNormLoad_phiBar

namespace Aux_SymNormLoad_23
open SymNormLoad

variable {M : ℕ} {Ψ : (Fin M → ℝ) → ℝ}

lemma psi_zero (hΨ : IsMonotoneSymmetricNorm Ψ) : Ψ 0 = 0 := by
  have := hΨ.smul 0 0
  simpa using this

lemma phi_zero (hΨ : IsMonotoneSymmetricNorm Ψ) : phi Ψ 0 = 0 := by
  unfold phi
  have : flatVec M 0 = 0 := by funext i; simp [flatVec]
  rw [this, psi_zero hΨ]

lemma phi_mono (hΨ : IsMonotoneSymmetricNorm Ψ) (k : ℕ) : phi Ψ k ≤ phi Ψ (k + 1) := by
  unfold phi
  apply hΨ.mono
  · intro i; simp only [flatVec, Pi.zero_apply]; split_ifs <;> norm_num
  · intro i; simp only [flatVec]; split_ifs <;> (try norm_num) <;> omega

lemma phi_mono' (hΨ : IsMonotoneSymmetricNorm Ψ) {a b : ℕ} (h : a ≤ b) : phi Ψ a ≤ phi Ψ b := by
  induction b, h using Nat.le_induction with
  | base => exact le_rfl
  | succ b _ ih => exact ih.trans (phi_mono hΨ b)

lemma psi_sum (hΨ : IsMonotoneSymmetricNorm Ψ) {ι : Type*} (S : Finset ι) (v : ι → Fin M → ℝ) :
    Ψ (∑ j ∈ S, v j) ≤ ∑ j ∈ S, Ψ (v j) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [psi_zero hΨ]
  | insert a S ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact (hΨ.triangle _ _).trans (by linarith)

lemma key (hΨ : IsMonotoneSymmetricNorm Ψ) (k : ℕ) (hk : k + 1 ≤ M) :
    (k : ℝ) * phi Ψ (k + 1) ≤ (k + 1) * phi Ψ k := by
  classical
  set S : Finset (Fin M) := (Finset.univ : Finset (Fin (k + 1))).map
    (Fin.castLEEmb (by omega : k + 1 ≤ M)) with hS
  have hcard : S.card = k + 1 := by
    rw [hS, Finset.card_map, Finset.card_univ, Fintype.card_fin]
  have hmemS : ∀ j : Fin M, j ∈ S ↔ (j : ℕ) < k + 1 := by
    intro j
    rw [hS, Finset.mem_map]
    constructor
    · rintro ⟨a, _, rfl⟩; have := a.isLt; simp; omega
    · intro h; exact ⟨⟨j, h⟩, Finset.mem_univ _, by ext; simp⟩
  let kM : Fin M := ⟨k, by omega⟩
  let v : Fin M → Fin M → ℝ := fun j => flatVec M (k + 1) - Pi.single j 1
  have hv : ∀ j ∈ S, Ψ (v j) = phi Ψ k := by
    intro j hj
    have hj' : (j : ℕ) < k + 1 := (hmemS j).1 hj
    have : v j = flatVec M k ∘ Equiv.swap j kM := by
      funext i
      simp only [v, Pi.sub_apply, Function.comp_apply, flatVec]
      by_cases hij : i = j
      · subst hij
        rw [Equiv.swap_apply_left]
        simp [kM, hj']
      · rw [Pi.single_eq_of_ne hij]
        by_cases hik : i = kM
        · subst hik
          rw [Equiv.swap_apply_right]
          have hjk : (j : ℕ) < k := by
            rcases Nat.lt_or_ge (j : ℕ) k with h | h
            · exact h
            · exfalso; apply hij; ext; simp [kM]; omega
          simp [kM, hjk]
        · rw [Equiv.swap_apply_of_ne_of_ne hij hik]
          have hik' : (i : ℕ) ≠ k := fun h => hik (Fin.ext h)
          by_cases hi : (i : ℕ) < k
          · simp [hi, show (i : ℕ) < k + 1 by omega]
          · simp [hi, show ¬ (i : ℕ) < k + 1 by omega]
    rw [this, hΨ.perm]
    rfl
  have hsum : ∑ j ∈ S, v j = (k : ℝ) • flatVec M (k + 1) := by
    funext i
    simp only [v, Finset.sum_apply, Pi.sub_apply, Finset.sum_sub_distrib, Finset.sum_const,
      hcard, Pi.smul_apply, smul_eq_mul, nsmul_eq_mul]
    simp only [Finset.sum_pi_single, hmemS]
    simp only [flatVec]
    push_cast
    split_ifs <;> ring
  have h1 := psi_sum hΨ S v
  rw [hsum, hΨ.smul, Finset.sum_congr rfl hv, Finset.sum_const, hcard, nsmul_eq_mul] at h1
  rw [abs_of_nonneg (Nat.cast_nonneg k)] at h1
  unfold phi
  push_cast at h1
  exact h1

lemma pb_eq (s : ℝ) (hs0 : 0 ≤ s) (hsM : s ≤ M) :
    phiBar Ψ s = phi Ψ ⌊s⌋₊ + (s - ⌊s⌋₊) * (phi Ψ (⌊s⌋₊ + 1) - phi Ψ ⌊s⌋₊) := by
  unfold phiBar
  have : max 0 (min s (M : ℝ)) = s := by rw [min_eq_left hsM, max_eq_right hs0]
  simp only [this]

end Aux_SymNormLoad_23

open SymNormLoad Aux_SymNormLoad_23 in
theorem solution (M : ℕ) (hM : 2 ≤ M) (Ψ : (Fin M → ℝ) → ℝ)
    (hΨ : IsMonotoneSymmetricNorm Ψ) :
    MonotoneOn (phiBar Ψ) (Set.Icc 0 (M : ℝ)) ∧
      AntitoneOn (fun s => phiBar Ψ s / s) (Set.Ioc 0 (M : ℝ)) := by
  -- floor facts
  have fl : ∀ s : ℝ, 0 ≤ s → s ≤ M → (⌊s⌋₊ : ℝ) ≤ s ∧ s < ⌊s⌋₊ + 1 ∧ ⌊s⌋₊ ≤ M := by
    intro s h0 h1
    refine ⟨Nat.floor_le h0, Nat.lt_floor_add_one s, ?_⟩
    have := Nat.floor_mono h1
    rwa [Nat.floor_natCast] at this
  -- value at an integer point is bounded by the piece endpoints
  have piece_le : ∀ s : ℝ, 0 ≤ s → s ≤ M → phiBar Ψ s ≤ phi Ψ (⌊s⌋₊ + 1) := by
    intro s h0 h1
    obtain ⟨a1, a2, _⟩ := fl s h0 h1
    rw [pb_eq s h0 h1]
    have := phi_mono hΨ ⌊s⌋₊
    nlinarith
  have piece_ge : ∀ s : ℝ, 0 ≤ s → s ≤ M → phi Ψ ⌊s⌋₊ ≤ phiBar Ψ s := by
    intro s h0 h1
    obtain ⟨a1, a2, _⟩ := fl s h0 h1
    rw [pb_eq s h0 h1]
    have := phi_mono hΨ ⌊s⌋₊
    nlinarith
  constructor
  · intro s hs t ht hst
    obtain ⟨hs0, hs1⟩ := hs
    obtain ⟨ht0, ht1⟩ := ht
    have hfl : ⌊s⌋₊ ≤ ⌊t⌋₊ := Nat.floor_le_floor hst
    rcases eq_or_lt_of_le hfl with heq | hlt
    · rw [pb_eq s hs0 hs1, pb_eq t ht0 ht1, ← heq]
      have := phi_mono hΨ ⌊s⌋₊
      nlinarith
    · calc phiBar Ψ s ≤ phi Ψ (⌊s⌋₊ + 1) := piece_le s hs0 hs1
        _ ≤ phi Ψ ⌊t⌋₊ := phi_mono' hΨ hlt
        _ ≤ phiBar Ψ t := piece_ge t ht0 ht1
  · intro s hs t ht hst
    obtain ⟨hs0, hs1⟩ := hs
    obtain ⟨ht0, ht1⟩ := ht
    simp only
    rw [div_le_div_iff₀ ht0 hs0]
    obtain ⟨a1, a2, a3⟩ := fl s hs0.le hs1
    obtain ⟨b1, b2, b3⟩ := fl t ht0.le ht1
    set k := ⌊s⌋₊ with hk
    set m := ⌊t⌋₊ with hm
    have hfl : k ≤ m := Nat.floor_le_floor hst
    rw [pb_eq s hs0.le hs1, pb_eq t ht0.le ht1, ← hk, ← hm]
    -- goal : (φ m + (t - m) (φ(m+1) - φ m)) * s ≤ (φ k + (s - k)(φ(k+1) - φ k)) * t
    rcases eq_or_lt_of_le hfl with heq | hlt
    · rw [← heq]
      -- same piece
      by_cases hkM : k + 1 ≤ M
      · have h := key hΨ k hkM
        have hnn : 0 ≤ (k + 1 : ℝ) * phi Ψ k - k * phi Ψ (k + 1) := by linarith
        have := mul_nonneg (sub_nonneg.2 hst) hnn
        nlinarith
      · -- k = M, then s = t = M
        have hkM' : k = M := by omega
        have hs' : s = M := by
          have : (M : ℝ) ≤ s := by rw [← hkM']; exact a1
          linarith
        have ht' : t = M := by linarith
        rw [hs', ht']
    · -- different pieces: k + 1 ≤ m
      have hk1 : k + 1 ≤ M := by omega
      have hm1 : 1 ≤ m := by omega
      -- (a) (k+1) f(s) ≥ s φ(k+1)
      have ha : s * phi Ψ (k + 1) ≤ (k + 1) * (phi Ψ k + (s - k) * (phi Ψ (k + 1) - phi Ψ k)) := by
        have h := key hΨ k hk1
        have : 0 ≤ (k + 1 - s) * ((k + 1) * phi Ψ k - k * phi Ψ (k + 1)) :=
          mul_nonneg (by linarith) (by linarith)
        nlinarith
      -- (c) m φ(k+1) ≥ (k+1) φ(m)
      have hc : ∀ j : ℕ, k + 1 ≤ j → j ≤ m → (j : ℝ) * phi Ψ (k + 1) ≥ (k + 1) * phi Ψ j := by
        intro j hj1
        induction j, hj1 using Nat.le_induction with
        | base => intro _; apply le_of_eq; push_cast; ring
        | succ j hj ih =>
          intro hj2
          have ih' := ih (by omega)
          have hkey := key hΨ j (by omega)
          have hj0 : (0 : ℝ) < j := by exact_mod_cast (by omega : 0 < j)
          have s1 : ((k : ℝ) + 1) * ((j : ℝ) * phi Ψ (j + 1)) ≤ ((k : ℝ) + 1) * (((j : ℝ) + 1) * phi Ψ j) :=
            mul_le_mul_of_nonneg_left hkey (by positivity)
          have s2 : ((j : ℝ) + 1) * (((k : ℝ) + 1) * phi Ψ j) ≤ ((j : ℝ) + 1) * ((j : ℝ) * phi Ψ (k + 1)) :=
            mul_le_mul_of_nonneg_left ih' (by positivity)
          have s3 : (j : ℝ) * (((k : ℝ) + 1) * phi Ψ (j + 1)) ≤ (j : ℝ) * (((j : ℝ) + 1) * phi Ψ (k + 1)) := by
            nlinarith
          have s4 := le_of_mul_le_mul_left s3 hj0
          push_cast
          linarith
      have hcm := hc m hlt le_rfl
      -- (b) m f(t) ≤ t φ(m)
      have hb : (m : ℝ) * (phi Ψ m + (t - m) * (phi Ψ (m + 1) - phi Ψ m)) ≤ t * phi Ψ m := by
        rcases eq_or_lt_of_le b1 with hteq | htgt
        · rw [← hteq]; apply le_of_eq; ring
        · have hmM : m + 1 ≤ M := by
            have : (m : ℝ) < M := lt_of_lt_of_le htgt ht1
            exact_mod_cast this
          have h := key hΨ m hmM
          have : 0 ≤ (t - m) * ((m + 1) * phi Ψ m - m * phi Ψ (m + 1)) :=
            mul_nonneg (by linarith) (by linarith)
          nlinarith
      have hm0 : (0 : ℝ) < m := by exact_mod_cast hm1
      have hk0 : (0 : ℝ) < k + 1 := by positivity
      -- combine: f(t)/t ≤ φ(m)/m ≤ φ(k+1)/(k+1) ≤ f(s)/s
      have e1 : (phi Ψ m + (t - m) * (phi Ψ (m + 1) - phi Ψ m)) / t ≤ phi Ψ m / m :=
        (div_le_div_iff₀ ht0 hm0).2 (by linarith)
      have e2 : phi Ψ m / m ≤ phi Ψ (k + 1) / (k + 1) :=
        (div_le_div_iff₀ hm0 hk0).2 (by linarith)
      have e3 : phi Ψ (k + 1) / (k + 1) ≤ (phi Ψ k + (s - k) * (phi Ψ (k + 1) - phi Ψ k)) / s :=
        (div_le_div_iff₀ hk0 hs0).2 (by linarith)
      have := e1.trans (e2.trans e3)
      rwa [div_le_div_iff₀ ht0 hs0] at this
