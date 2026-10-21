-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Renew46.P29.increasingComplement_permutation_sign
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-20T23:23:21.908912+00:00
-- url     : https://prove2.me/submissions/69c384a6-b0f8-4c84-b7cf-4ff3875be4e3

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P29
open QAlgorithms.Papers.Independent.Renew46.P29

open Set Filter Topology

universe u v


theorem g64p_cr {n : ℕ} (m v : Fin (n + 1)) :
    ((Fin.cycleRange m v : Fin (n + 1)) : ℕ) =
      if (v : ℕ) < m then (v : ℕ) + 1 else if (v : ℕ) = m then 0 else v := by
  rcases lt_trichotomy v m with h | h | h
  · rw [Fin.coe_cycleRange_of_lt h, if_pos (show (v : ℕ) < m from h)]
  · subst h; simp
  · rw [Fin.cycleRange_of_gt h, if_neg (by omega), if_neg (by omega)]

theorem g64p_one {m : ℕ} (τ : Equiv.Perm (Fin m)) (h : StrictMono τ) : τ = 1 := by
  have hs : StrictMono τ.symm := by
    intro x y hxy
    by_contra hc; push Not at hc
    have := h.monotone hc; simp at this; exact absurd hxy (not_lt.mpr this)
  ext a
  have h1 : a ≤ τ a := h.le_apply
  have h3 : a ≤ τ.symm a := hs.le_apply
  have h4 : τ a ≤ τ (τ.symm a) := h.monotone h3
  simp only [Equiv.apply_symm_apply] at h4
  simp [le_antisymm h4 h1]

theorem g64p_crd {n : ℕ} (m v : Fin (n + 1)) :
    (((Fin.cycleRange m v : Fin (n + 1)) : ℕ) = (v : ℕ) + 1 ∧ (v : ℕ) < m) ∨
    (((Fin.cycleRange m v : Fin (n + 1)) : ℕ) = 0 ∧ (v : ℕ) = m) ∨
    (((Fin.cycleRange m v : Fin (n + 1)) : ℕ) = v ∧ (m : ℕ) < v) := by
  rw [g64p_cr]; split_ifs <;> omega

theorem g64p_key {n : ℕ} (sigma : Equiv.Perm (Fin (n + 1))) (i : Fin (n + 1)) (hi0 : (i : ℕ) ≠ 0)
    (hab : ((sigma 0 : Fin (n + 1)) : ℕ) < sigma i)
    (hIncreasing : StrictMonoOn sigma {j : Fin (n + 1) | j ≠ 0 ∧ j ≠ i})
    (q q' : Fin (n + 1))
    (hqq : (Fin.cycleRange i q : ℕ) < Fin.cycleRange i q') :
    (Fin.cycleRange (sigma i) (Fin.cycleRange (sigma 0) (sigma q)) : ℕ) <
      Fin.cycleRange (sigma i) (Fin.cycleRange (sigma 0) (sigma q')) := by
  have fact : ∀ r : Fin (n + 1), ((r : ℕ) ≠ 0 ∨ (sigma r : ℕ) = sigma 0) ∧
      ((r : ℕ) ≠ i ∨ (sigma r : ℕ) = sigma i) ∧
      ((r : ℕ) = 0 ∨ (r : ℕ) = i ∨ ((sigma r : ℕ) ≠ sigma 0 ∧ (sigma r : ℕ) ≠ sigma i)) := by
    intro r
    by_cases h0 : (r : ℕ) = 0
    · have : r = 0 := Fin.ext h0
      subst this; exact ⟨Or.inr rfl, Or.inl (by omega), Or.inl rfl⟩
    by_cases h1 : (r : ℕ) = i
    · have : r = i := Fin.ext h1
      subst this; exact ⟨Or.inl h0, Or.inr rfl, Or.inr (Or.inl rfl)⟩
    refine ⟨Or.inl h0, Or.inl h1, Or.inr (Or.inr ⟨?_, ?_⟩)⟩
    · intro h; exact h0 (by rw [sigma.injective (Fin.ext h)]; rfl)
    · intro h; exact h1 (by rw [sigma.injective (Fin.ext h)])
  have hMM : (q : ℕ) = 0 ∨ (q : ℕ) = i ∨ (q' : ℕ) = 0 ∨ (q' : ℕ) = i ∨
      ((q : ℕ) < q' ∧ (sigma q : ℕ) < sigma q') ∨ ((q' : ℕ) < q ∧ (sigma q' : ℕ) < sigma q) ∨
      (q : ℕ) = q' := by
    by_cases h0 : (q : ℕ) = 0
    · left; exact h0
    by_cases h1 : (q : ℕ) = i
    · right; left; exact h1
    by_cases h2 : (q' : ℕ) = 0
    · right; right; left; exact h2
    by_cases h3 : (q' : ℕ) = i
    · right; right; right; left; exact h3
    have n0 : q ≠ 0 := fun h => h0 (by rw [h]; rfl)
    have ni : q ≠ i := fun h => h1 (by rw [h])
    have n0' : q' ≠ 0 := fun h => h2 (by rw [h]; rfl)
    have ni' : q' ≠ i := fun h => h3 (by rw [h])
    rcases lt_trichotomy (q : ℕ) q' with h | h | h
    · right; right; right; right; left; exact ⟨h, hIncreasing ⟨n0, ni⟩ ⟨n0', ni'⟩ h⟩
    · right; right; right; right; right; right; exact h
    · right; right; right; right; right; left; exact ⟨h, hIncreasing ⟨n0', ni'⟩ ⟨n0, ni⟩ h⟩
  have f1 := fact q
  have f2 := fact q'
  have c1 := g64p_crd i q
  have c2 := g64p_crd i q'
  have c3 := g64p_crd (sigma 0) (sigma q)
  have c4 := g64p_crd (sigma 0) (sigma q')
  have c5 := g64p_crd (sigma i) (Fin.cycleRange (sigma 0) (sigma q))
  have c6 := g64p_crd (sigma i) (Fin.cycleRange (sigma 0) (sigma q'))
  omega

theorem g64p_main (n : ℕ) (sigma : Equiv.Perm (Fin (n + 1)))
    (i : Fin (n + 1)) (hi : i ≠ 0)
    (hOrder : sigma 0 < sigma i)
    (hIncreasing : StrictMonoOn sigma {j : Fin (n + 1) | j ≠ 0 ∧ j ≠ i}) :
    Equiv.Perm.sign sigma =
      (-1 : ℤˣ) ^ (i.val + (sigma 0).val + 1 + (sigma i).val + 1) := by
  have hi0 : (i : ℕ) ≠ 0 := fun h => hi (Fin.ext h)
  set F : Equiv.Perm (Fin (n + 1)) :=
    Fin.cycleRange (sigma i) * Fin.cycleRange (sigma 0) * sigma * (Fin.cycleRange i)⁻¹ with hF
  have hmono : StrictMono F := by
    intro p p' hpp
    have := g64p_key sigma i hi0 hOrder hIncreasing ((Fin.cycleRange i).symm p)
      ((Fin.cycleRange i).symm p') (by simpa using hpp)
    exact this
  have h1 := g64p_one F hmono
  have h2 : Fin.cycleRange (sigma i) * Fin.cycleRange (sigma 0) * sigma = Fin.cycleRange i := by
    rw [hF, mul_inv_eq_one] at h1; exact h1
  have h3 := congrArg Equiv.Perm.sign h2
  simp only [map_mul, Fin.sign_cycleRange] at h3
  set X : ℤˣ := (-1) ^ ((sigma i : Fin (n + 1)) : ℕ) * (-1) ^ ((sigma 0 : Fin (n + 1)) : ℕ) with hX
  have hs : Equiv.Perm.sign sigma = X * (-1) ^ (i : ℕ) := by
    calc Equiv.Perm.sign sigma = (X * X) * Equiv.Perm.sign sigma := by rw [Int.units_mul_self, one_mul]
      _ = X * (X * Equiv.Perm.sign sigma) := mul_assoc _ _ _
      _ = X * (-1) ^ (i : ℕ) := by rw [h3]
  rw [hs, hX]
  apply Units.ext
  simp only [Units.val_mul, Units.val_pow_eq_pow_val, Units.val_neg, Units.val_one]
  ring

/-- Lemma A.5, PDF p. 58 (with its application on p. 60): the complement
is taken in all n+1 positions, correcting the printed n. Fin uses zero-based
indices: i is the paper's i, while k and ell are the two images plus one.
The strict inequality makes the two distinguished positions distinct. -/
theorem solution
    (n : ℕ) (sigma : Equiv.Perm (Fin (n + 1)))
    (i : Fin (n + 1)) (hi : i ≠ 0)
    (hOrder : sigma 0 < sigma i)
    (hIncreasing : StrictMonoOn sigma {j : Fin (n + 1) | j ≠ 0 ∧ j ≠ i}) :
    Equiv.Perm.sign sigma =
      (-1 : ℤˣ) ^ (i.val + (sigma 0).val + 1 + (sigma i).val + 1) := g64p_main n sigma i hi hOrder hIncreasing

