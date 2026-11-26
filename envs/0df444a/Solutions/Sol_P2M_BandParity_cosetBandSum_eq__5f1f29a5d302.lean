-- Prove2me | solution 1 for P2M_BandParity_cosetBandSum_eq__5f1f29a5d302
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T22:58:51.378142+00:00
-- url     : https://prove2.me/submissions/db66949c-60b3-4452-ac66-c7ec97775e51

module
public import Definitions.Def_BandParity_Matching
public import Definitions.Def_BandParity_OddSubgroup
public import Theorems.Thm_BandParity_unit_val_ne_zero
public import Theorems.Thm_BandParity_uSign_neg
public import Theorems.Thm_BandParity_bandSignPow_eq
public import Theorems.Thm_BandParity_not_both

set_option autoImplicit true
@[expose] public section
public section
open BandParity
open Finset
variable {N : ℕ} [NeZero N]
variable (hN : Odd N) (hN3 : 3 ≤ N)
include hN hN3
variable {H : Subgroup (ZMod N)ˣ} [DecidablePred (· ∈ H)] (hH : Odd (Nat.card H))
include hH
namespace BandParity
theorem _root_.solution (x : (ZMod N)ˣ) {e : ℕ} (he : Even e) (he0 : e ≠ 0) :
    cosetBandSum H x e = ∑ u ∈ coset H x, uSign u * uSign (u ^ e) := by
  set G : (ZMod N)ˣ → ℤ := fun u => uSign u * uSign (u ^ e) with hG
  have hGneg : ∀ u, G (-u) = -G u := by
    intro u; simp only [hG, uSign_neg hN hN3, he.neg_pow, neg_mul]
  have hNodd : N % 2 = 1 := Nat.odd_iff.1 hN
  -- split the defining sum according to `X` and `-X`
  have hsplit : cosetBandSum H x e =
      ∑ u : (ZMod N)ˣ, (if 2 * (u : ZMod N).val < N ∧ x⁻¹ * u ∈ H then G u else 0) +
      ∑ u : (ZMod N)ˣ, (if 2 * (u : ZMod N).val < N ∧ -(x⁻¹ * u) ∈ H then -G u else 0) := by
    unfold cosetBandSum
    simp only [mul_neg]
    rw [Finset.sum_filter, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun u _ => ?_
    have hnb := not_both hN3 hH x u
    rw [bandSignPow_eq hN he0]
    by_cases hl : 2 * (u : ZMod N).val < N
    · by_cases h1 : x⁻¹ * u ∈ H
      · have h2 : -(x⁻¹ * u) ∉ H := fun h2 => hnb ⟨h1, h2⟩
        simp [hl, h1, h2, hG]
      · by_cases h2 : -(x⁻¹ * u) ∈ H
        · simp [hl, h1, h2, hG]
        · simp [hl, h1, h2]
    · simp [hl]
  -- reflect the second sum by `u ↦ -u`
  have hrefl : ∑ u : (ZMod N)ˣ, (if 2 * (u : ZMod N).val < N ∧ -(x⁻¹ * u) ∈ H then -G u else 0) =
      ∑ u : (ZMod N)ˣ, (if ¬ 2 * (u : ZMod N).val < N ∧ x⁻¹ * u ∈ H then G u else 0) := by
    refine Fintype.sum_equiv (Equiv.neg (ZMod N)ˣ) _ _ fun u => ?_
    simp only [Equiv.neg_apply, mul_neg, hGneg]
    have hv := ZMod.val_lt (u : ZMod N)
    have : Nontrivial (ZMod N) := ZMod.nontrivial_iff.2 (by omega)
    have hnv : (-(u : ZMod N)).val = N - (u : ZMod N).val := by
      rw [ZMod.neg_val]; simp only [u.ne_zero, ↓reduceIte]
    have hu0 := unit_val_ne_zero hN3 u
    by_cases hl : 2 * (u : ZMod N).val < N
    · have h' : N ≤ 2 * (-(u : ZMod N)).val := by rw [hnv]; omega
      simp [hl, h']
    · have h' : ¬ N ≤ 2 * (-(u : ZMod N)).val := by rw [hnv]; omega
      simp [hl, h']
  rw [hsplit, hrefl, ← Finset.sum_add_distrib, coset, Finset.sum_filter]
  refine Finset.sum_congr rfl fun u _ => ?_
  by_cases hl : 2 * (u : ZMod N).val < N <;> by_cases h1 : x⁻¹ * u ∈ H <;> simp [hl, h1, hG]
end BandParity
