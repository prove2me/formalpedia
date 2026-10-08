-- Prove2me | solution 1 for SecretaryWD.KnownOpt.good_perms_card_ge
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-04T11:27:49.136997+00:00
-- url     : https://prove2.me/submissions/073d539e-f191-4677-84aa-4e0b2ac95e04

import Mathlib
import Definitions.Def_SecretaryWD_KnownOpt_Model

set_option autoImplicit false

open SecretaryWD.KnownOpt in
theorem e0478c29_notacc {n : ℕ} [NeZero n] (d v : Fin n → ℝ) (Z : ℝ)
    (π : Equiv.Perm (Fin n)) (hπ : π ∈ Finset.univ \ acceptingPerms d v Z) (k : Fin n) :
    d k * v (π k) < Z / 2 := by
  rw [Finset.mem_sdiff] at hπ
  have h := hπ.2
  rw [acceptingPerms, Finset.mem_filter] at h
  have h' : optValue d v π < Z / 2 := lt_of_not_ge (fun hle => h ⟨Finset.mem_univ _, hle⟩)
  rw [optValue, Finset.sup'_lt_iff] at h'
  exact h' k (Finset.mem_univ _)

open SecretaryWD.KnownOpt in
theorem solution {n : ℕ} [NeZero n] (d v : Fin n → ℝ)
    (hd : ∀ i, 0 ≤ d i) (hv : ∀ e, 0 ≤ v e) (Z : ℝ) (i j : Fin n)
    (hij : Z / 2 ≤ d i * v j) :
    (Finset.univ \ acceptingPerms d v Z).card ≤ n * (goodPerms d v Z i j).card ∧
      (2 * (acceptingPerms d v Z).card ≤ n.factorial →
        n.factorial ≤ 2 * n * (goodPerms d v Z i j).card) := by
  have part1 : (Finset.univ \ acceptingPerms d v Z).card ≤ n * (goodPerms d v Z i j).card := by
    classical
    refine Finset.card_le_mul_card_image_of_maps_to
      (f := fun π : Equiv.Perm (Fin n) => π * Equiv.swap i (π.symm j)) ?_ n ?_
    · intro π hπ
      have hna := e0478c29_notacc d v Z π hπ
      rw [goodPerms, Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_, ?_⟩
      · rw [Equiv.Perm.mul_apply, Equiv.swap_apply_left, Equiv.apply_symm_apply]
      intro k hk
      simp only [discProd, Equiv.Perm.mul_apply]
      have hki : k ≠ i := ne_of_lt hk
      by_cases hkm : k = π.symm j
      · subst hkm
        rw [Equiv.swap_apply_right]
        have h1 : d (π.symm j) * v j < Z / 2 := by
          have := hna (π.symm j); rwa [Equiv.apply_symm_apply] at this
        have hlt : d (π.symm j) * v j < d i * v j := lt_of_lt_of_le h1 hij
        have hvj : 0 < v j := by
          by_contra hcon
          have : v j = 0 := le_antisymm (not_lt.mp hcon) (hv j)
          rw [this, mul_zero, mul_zero] at hlt; exact lt_irrefl _ hlt
        have hdle : d (π.symm j) ≤ d i := le_of_lt (lt_of_mul_lt_mul_right hlt hvj.le)
        calc d (π.symm j) * v (π i) ≤ d i * v (π i) :=
              mul_le_mul_of_nonneg_right hdle (hv _)
          _ < Z / 2 := hna i
      · rw [Equiv.swap_apply_of_ne_of_ne hki hkm]
        exact hna k
    · intro σ _
      calc (Finset.filter (fun π : Equiv.Perm (Fin n) => π * Equiv.swap i (π.symm j) = σ)
              (Finset.univ \ acceptingPerms d v Z)).card
          ≤ (Finset.univ.image (fun m : Fin n => σ * Equiv.swap i m)).card := by
            apply Finset.card_le_card
            intro π hπ
            simp only [Finset.mem_filter] at hπ
            simp only [Finset.mem_image, Finset.mem_univ, true_and]
            refine ⟨π.symm j, ?_⟩
            rw [← hπ.2, mul_assoc, Equiv.swap_mul_self, mul_one]
        _ ≤ Finset.univ.card := Finset.card_image_le
        _ = n := by simp
  refine ⟨part1, fun h2 => ?_⟩
  have hsplit : (Finset.univ \ acceptingPerms d v Z).card + (acceptingPerms d v Z).card
      = n.factorial := by
    rw [Finset.card_sdiff_add_card_eq_card (Finset.subset_univ _), Finset.card_univ,
      Fintype.card_perm, Fintype.card_fin]
  calc n.factorial ≤ 2 * (Finset.univ \ acceptingPerms d v Z).card := by omega
    _ ≤ 2 * (n * (goodPerms d v Z i j).card) := Nat.mul_le_mul_left 2 part1
    _ = 2 * n * (goodPerms d v Z i j).card := by ring
