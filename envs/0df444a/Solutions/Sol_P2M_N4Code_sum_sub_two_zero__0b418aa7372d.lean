-- Prove2me | solution 1 for P2M_N4Code_sum_sub_two_zero__0b418aa7372d
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:19:12.252801+00:00
-- url     : https://prove2.me/submissions/94c2a23d-4d71-49bd-ac9b-81d3f981ecd5

import Definitions.Def_N4Code_ZeroColumn
import Definitions.Def_N4Code_TwoColumn

set_option autoImplicit true
open N4Code
set_option maxRecDepth 1000000
open scoped BigOperators
namespace N4Code
theorem _root_.solution {n : ℕ} (f g : Fin n → ℕ) (t₁ t₂ : Fin n) (htne : t₁ ≠ t₂)
    (h1 : f t₁ = g t₁ + 1) (h2 : f t₂ + 1 = g t₂)
    (hrest : ∀ u : Fin n, u ≠ t₁ → u ≠ t₂ → f u = g u) :
    (∑ u : Fin n, f u) = (∑ u : Fin n, g u) := by
  have he1 : (∑ u ∈ (Finset.univ.erase t₁).erase t₂, f u) =
      ∑ u ∈ (Finset.univ.erase t₁).erase t₂, g u := by
    apply Finset.sum_congr rfl
    intro u hu
    have hu2 : u ≠ t₂ := (Finset.mem_erase.mp hu).1
    have hu1 : u ≠ t₁ := (Finset.mem_erase.mp (Finset.mem_erase.mp hu).2).1
    exact hrest u hu1 hu2
  have hf1 : (∑ u : Fin n, f u) =
      (∑ u ∈ (Finset.univ.erase t₁).erase t₂, f u) + f t₂ + f t₁ := by
    rw [sum_split_at f t₁]
    have hb : (∑ u ∈ (Finset.univ.erase t₁), f u) =
        (∑ u ∈ (Finset.univ.erase t₁).erase t₂, f u) + f t₂ := by
      exact (Finset.sum_erase_add (Finset.univ.erase t₁) f
        (Finset.mem_erase.mpr ⟨htne.symm, Finset.mem_univ t₂⟩)).symm
    rw [hb]
  have hg1 : (∑ u : Fin n, g u) =
      (∑ u ∈ (Finset.univ.erase t₁).erase t₂, g u) + g t₂ + g t₁ := by
    rw [sum_split_at g t₁]
    have hb : (∑ u ∈ (Finset.univ.erase t₁), g u) =
        (∑ u ∈ (Finset.univ.erase t₁).erase t₂, g u) + g t₂ := by
      exact (Finset.sum_erase_add (Finset.univ.erase t₁) g
        (Finset.mem_erase.mpr ⟨htne.symm, Finset.mem_univ t₂⟩)).symm
    rw [hb]
  calc
    (∑ u : Fin n, f u) = (∑ u ∈ (Finset.univ.erase t₁).erase t₂, f u) + f t₂ + f t₁ := hf1
    _ = (∑ u ∈ (Finset.univ.erase t₁).erase t₂, g u) + (g t₂ - 1) + (g t₁ + 1) := by
          have hf₂ : f t₂ = g t₂ - 1 := by omega
          rw [he1, h1, hf₂]
    _ = (∑ u : Fin n, g u) := by
          rw [hg1]
          omega
end N4Code
