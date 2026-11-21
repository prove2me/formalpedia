-- Prove2me | solution 1 for ZeroOneSimplex.claim_4
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-20T21:42:17.72901+00:00
-- url     : https://prove2.me/submissions/f0c09d16-8a31-4c32-b03f-f5c447ad9c96

import Mathlib
import Definitions.Def_ZeroOneSimplex_LPData
import Definitions.Def_ZeroOneSimplex_IsEdge
import Definitions.Def_ZeroOneSimplex_LPData_orderedShadowVec
set_option autoImplicit false

open Matrix

namespace Aux_ZeroOneSimplex_claim_4

open ZeroOneSimplex

lemma le_fIndex {n : ℕ} (x0 u : Fin n → ℝ) (k : Fin n) (hne : u k ≠ x0 k) :
    k.val + 1 ≤ fIndex x0 u := by
  unfold fIndex
  exact Finset.le_sup (f := fun k : Fin n => k.val + 1)
    (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hne⟩)

lemma fIndex_eq {n : ℕ} (x0 u : Fin n → ℝ) (k : Fin n) (hk : fIndex x0 u < k.val + 1) :
    u k = x0 k := by
  by_contra hne
  have h1 := le_fIndex x0 u k hne
  omega

lemma fIndex_le {n : ℕ} (x0 u : Fin n → ℝ) : fIndex x0 u ≤ n := by
  unfold fIndex
  apply Finset.sup_le
  intro k _
  have := k.isLt
  omega

lemma at1_succ {n : ℕ} (z : Fin n → ℝ) (k : Fin n) : at1 z (k.val + 1) = z k := by
  have hk := k.isLt
  have hc : 1 ≤ k.val + 1 ∧ k.val + 1 ≤ n := ⟨by omega, by omega⟩
  unfold at1
  rw [dif_pos hc]
  exact congrArg z (Fin.ext (by simp))

end Aux_ZeroOneSimplex_claim_4

open Aux_ZeroOneSimplex_claim_4 in
open ZeroOneSimplex in
theorem solution {n m p : ℕ} (L : LPData n m p) (h01 : L.IsZeroOneLP) (x0 : Fin n → ℝ)
    (hx0 : x0 ∈ Set.extremePoints ℝ L.feasibleRegion) (x u0 u1 : Fin n → ℝ)
    (hu0 : IsEdge L.feasibleRegion x u0) (hu1 : IsEdge L.feasibleRegion x u1)
    (hc0 : L.c ⬝ᵥ x < L.c ⬝ᵥ u0) (hc1 : L.c ⬝ᵥ x < L.c ⬝ᵥ u1)
    (hv0 : L.orderedShadowVec x0 ⬝ᵥ x < L.orderedShadowVec x0 ⬝ᵥ u0)
    (hv1 : L.orderedShadowVec x0 ⬝ᵥ x < L.orderedShadowVec x0 ⬝ᵥ u1)
    (hfx : fIndex x0 x ≤ max (fIndex x0 u0) (fIndex x0 u1)) :
    (L.c ⬝ᵥ (u1 - x) / L.orderedShadowVec x0 ⬝ᵥ (u1 - x) <
        L.c ⬝ᵥ (u0 - x) / L.orderedShadowVec x0 ⬝ᵥ (u0 - x)) ↔
      ∑ j ∈ Finset.Ico 1 (max (fIndex x0 u0) (fIndex x0 u1)),
          -kappa L.c x0 x u0 u1 j * L.cStar ^ j <
        kappa L.c x0 x u0 u1 (max (fIndex x0 u0) (fIndex x0 u1)) *
          L.cStar ^ (max (fIndex x0 u0) (fIndex x0 u1)) := by
  obtain ⟨b, hb⟩ : ∃ b, b = max (fIndex x0 u0) (fIndex x0 u1) := ⟨_, rfl⟩
  have hb0 : fIndex x0 u0 ≤ b := by rw [hb]; exact le_max_left _ _
  have hb1 : fIndex x0 u1 ≤ b := by rw [hb]; exact le_max_right _ _
  have hbx : fIndex x0 x ≤ b := by rw [hb]; exact hfx
  have hbn : b ≤ n := by
    rw [hb]
    exact max_le (fIndex_le x0 u0) (fIndex_le x0 u1)
  rw [← hb]
  have hbpos : 1 ≤ b := by
    by_contra hb0'
    push_neg at hb0'
    apply hu0.1
    funext k
    rw [fIndex_eq x0 x k (by omega), fIndex_eq x0 u0 k (by omega)]
  have hV0 : 0 < L.orderedShadowVec x0 ⬝ᵥ (u0 - x) := by
    rw [dotProduct_sub]
    linarith
  have hV1 : 0 < L.orderedShadowVec x0 ⬝ᵥ (u1 - x) := by
    rw [dotProduct_sub]
    linarith
  have hdot : ∀ (w z : Fin n → ℝ), w ⬝ᵥ (z - x) = ∑ i, w i * (z i - x i) := by
    intro w z
    simp only [dotProduct, Pi.sub_apply]
  have hterm : ∀ k : Fin n,
      L.c ⬝ᵥ (u0 - x) * (L.orderedShadowVec x0 k * (u1 k - x k)) -
        L.c ⬝ᵥ (u1 - x) * (L.orderedShadowVec x0 k * (u0 k - x k)) =
      kappa L.c x0 x u0 u1 (k.val + 1) * L.cStar ^ (k.val + 1) := by
    intro k
    have hv : L.orderedShadowVec x0 k =
        (if x0 k = 0 then (1 : ℝ) else -1) * L.cStar ^ (k.val + 1) := rfl
    have hs : sgnAt x0 (k.val + 1) = if x0 k = 0 then (1 : ℝ) else -1 := by
      unfold sgnAt
      rw [at1_succ]
    unfold kappa
    rw [hs, hv]
    simp only [at1_succ]
    ring
  have hIco : ∑ j ∈ Finset.Ico 1 (n + 1), kappa L.c x0 x u0 u1 j * L.cStar ^ j =
      ∑ j ∈ Finset.range n, kappa L.c x0 x u0 u1 (j + 1) * L.cStar ^ (j + 1) := by
    rw [Finset.sum_Ico_eq_sum_range, Nat.add_sub_cancel]
    exact Finset.sum_congr rfl fun j _ => by rw [add_comm 1 j]
  have hid : L.c ⬝ᵥ (u0 - x) * L.orderedShadowVec x0 ⬝ᵥ (u1 - x) -
      L.c ⬝ᵥ (u1 - x) * L.orderedShadowVec x0 ⬝ᵥ (u0 - x) =
      ∑ j ∈ Finset.Ico 1 (b + 1), kappa L.c x0 x u0 u1 j * L.cStar ^ j := by
    rw [hdot (L.orderedShadowVec x0) u1, hdot (L.orderedShadowVec x0) u0,
      Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    simp only [hterm]
    rw [Fin.sum_univ_eq_sum_range (fun j => kappa L.c x0 x u0 u1 (j + 1) * L.cStar ^ (j + 1)) n]
    rw [← hIco]
    symm
    have hsub : Finset.Ico 1 (b + 1) ⊆ Finset.Ico 1 (n + 1) :=
      Finset.Ico_subset_Ico_right (by omega)
    apply Finset.sum_subset hsub
    intro j hj hnot
    simp only [Finset.mem_Ico] at hj hnot
    have hjb : b < j := by omega
    have hc : 1 ≤ j ∧ j ≤ n := ⟨hj.1, by omega⟩
    have hz : ∀ z : Fin n → ℝ, fIndex x0 z ≤ b → at1 z j = at1 x0 j := by
      intro z hzb
      unfold at1
      rw [dif_pos hc, dif_pos hc]
      apply fIndex_eq
      show fIndex x0 z < (j - 1) + 1
      omega
    unfold kappa
    rw [hz u1 hb1, hz u0 hb0, hz x hbx]
    simp
  have hsplit : ∑ j ∈ Finset.Ico 1 (b + 1), kappa L.c x0 x u0 u1 j * L.cStar ^ j =
      ∑ j ∈ Finset.Ico 1 b, kappa L.c x0 x u0 u1 j * L.cStar ^ j +
        kappa L.c x0 x u0 u1 b * L.cStar ^ b :=
    Finset.sum_Ico_succ_top hbpos _
  rw [div_lt_div_iff₀ hV1 hV0]
  simp only [neg_mul, Finset.sum_neg_distrib]
  constructor
  · intro h
    linarith
  · intro h
    linarith
