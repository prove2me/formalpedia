-- Prove2me | solution 1 for ZeroOneSimplex.claim_2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-20T21:37:20.737008+00:00
-- url     : https://prove2.me/submissions/7722c771-dba3-4783-9ebd-2cf9becb6519

import Mathlib
import Definitions.Def_ZeroOneSimplex_LPData
import Definitions.Def_ZeroOneSimplex_IsEdge
import Definitions.Def_ZeroOneSimplex_LPData_orderedShadowVec
set_option autoImplicit false

open Matrix

namespace Aux_ZeroOneSimplex_claim_2

open ZeroOneSimplex

lemma left_ext {n : ℕ} (x u : Fin n → ℝ) (hxu : x ≠ u) :
    x ∈ (segment ℝ x u).extremePoints ℝ := by
  refine ⟨left_mem_segment ℝ x u, ?_⟩
  intro x1 hx1 x2 hx2 hx
  rw [segment_eq_image'] at hx1 hx2
  obtain ⟨s, ⟨hs0, hs1⟩, rfl⟩ := hx1
  obtain ⟨t, ⟨ht0, ht1⟩, rfl⟩ := hx2
  obtain ⟨a, b, ha, hb, hab, hx⟩ := hx
  have key : (a * s + b * t) • (u - x) = 0 := by
    funext i
    have := congrFun hx i
    simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, Pi.zero_apply] at this ⊢
    linear_combination this - x i * hab
  show x + s • (u - x) = x
  rcases smul_eq_zero.mp key with h | h
  · have has : a * s = 0 := by
      linarith [mul_nonneg ha.le hs0, mul_nonneg hb.le ht0]
    have hs : s = 0 := (mul_eq_zero.mp has).resolve_left ha.ne'
    rw [hs, zero_smul, add_zero]
  · exact absurd (sub_eq_zero.mp h).symm hxu

lemma ext_left {n : ℕ} {Q : Set (Fin n → ℝ)} {x u : Fin n → ℝ} (h : IsEdge Q x u) :
    x ∈ Q.extremePoints ℝ :=
  h.2.extremePoints_subset_extremePoints (left_ext x u h.1)

lemma ext_right {n : ℕ} {Q : Set (Fin n → ℝ)} {x u : Fin n → ℝ} (h : IsEdge Q x u) :
    u ∈ Q.extremePoints ℝ := by
  apply h.2.extremePoints_subset_extremePoints
  rw [segment_symm]
  exact left_ext u x (Ne.symm h.1)

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

lemma fIndex_attain {n : ℕ} (x0 u : Fin n → ℝ) (h : 1 ≤ fIndex x0 u) :
    ∃ K : Fin n, K.val + 1 = fIndex x0 u ∧ u K ≠ x0 K := by
  by_contra hcon
  push_neg at hcon
  have hsup : fIndex x0 u ≤ fIndex x0 u - 1 := by
    unfold fIndex
    apply Finset.sup_le
    intro k hk
    have hne := (Finset.mem_filter.mp hk).2
    have h1 := le_fIndex x0 u k hne
    have h2 : k.val + 1 ≠ fIndex x0 u := fun heq => hne (hcon k heq)
    change k.val + 1 ≤ fIndex x0 u - 1
    omega
  omega

lemma geom (cs : ℝ) (K : ℕ) :
    (cs - 1) * ∑ j ∈ Finset.range K, cs ^ (j + 1) = cs ^ (K + 1) - cs := by
  induction K with
  | zero => simp
  | succ K ih =>
    rw [Finset.sum_range_succ, mul_add, ih]
    ring

end Aux_ZeroOneSimplex_claim_2

open Aux_ZeroOneSimplex_claim_2 in
open ZeroOneSimplex in
theorem solution {n m p : ℕ} (L : LPData n m p) (h01 : L.IsZeroOneLP) (x0 : Fin n → ℝ)
    (hx0 : x0 ∈ Set.extremePoints ℝ L.feasibleRegion) (x u0 u1 : Fin n → ℝ)
    (hu0 : IsEdge L.feasibleRegion x u0) (hu1 : IsEdge L.feasibleRegion x u1)
    (hc0 : L.c ⬝ᵥ x < L.c ⬝ᵥ u0) (hc1 : L.c ⬝ᵥ x < L.c ⬝ᵥ u1)
    (hv0 : L.orderedShadowVec x0 ⬝ᵥ x < L.orderedShadowVec x0 ⬝ᵥ u0)
    (hv1 : L.orderedShadowVec x0 ⬝ᵥ x < L.orderedShadowVec x0 ⬝ᵥ u1)
    (hf : fIndex x0 u0 < fIndex x0 u1) (hfx : fIndex x0 x < fIndex x0 u1) :
    L.c ⬝ᵥ (u1 - x) / L.orderedShadowVec x0 ⬝ᵥ (u1 - x) <
      L.c ⬝ᵥ (u0 - x) / L.orderedShadowVec x0 ⬝ᵥ (u0 - x) := by
  obtain ⟨_, _, h01v, hcint⟩ := h01
  have hx_ext := ext_left hu0
  have hu0_ext := ext_right hu0
  have hu1_ext := ext_right hu1
  have b01 : ∀ y ∈ L.feasibleRegion.extremePoints ℝ, ∀ i, 0 ≤ y i ∧ y i ≤ 1 := by
    intro y hy i
    rcases h01v y hy i with h | h <;> rw [h] <;> norm_num
  have hb1 : 1 ≤ fIndex x0 u1 := by omega
  obtain ⟨K, hKb, hK⟩ := fIndex_attain x0 u1 hb1
  have hKn := K.isLt
  have hxK : x K = x0 K := fIndex_eq x0 x K (by omega)
  have hu0K : ∀ k : Fin n, K.val ≤ k.val → u0 k = x k := by
    intro k hk
    rw [fIndex_eq x0 u0 k (by omega), fIndex_eq x0 x k (by omega)]
  have hu1K : ∀ k : Fin n, K.val < k.val → u1 k = x k := by
    intro k hk
    rw [fIndex_eq x0 u1 k (by omega), fIndex_eq x0 x k (by omega)]
  have hcs2 : 2 ≤ L.cStar := by
    unfold LPData.cStar
    have := Finset.sum_nonneg (fun i (_ : i ∈ Finset.univ) => abs_nonneg (L.c i))
    linarith
  have hv : ∀ k, L.orderedShadowVec x0 k =
      (if x0 k = 0 then (1 : ℝ) else -1) * L.cStar ^ (k.val + 1) := fun k => rfl
  have hdot : ∀ (w z : Fin n → ℝ), w ⬝ᵥ (z - x) = ∑ i, w i * (z i - x i) := by
    intro w z
    simp only [dotProduct, Pi.sub_apply]
  have hd1 : ∀ z ∈ L.feasibleRegion.extremePoints ℝ, ∀ k, |z k - x k| ≤ 1 := by
    intro z hz k
    have h1 := b01 z hz k
    have h2 := b01 x hx_ext k
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  have hterm_abs : ∀ z ∈ L.feasibleRegion.extremePoints ℝ, ∀ k : Fin n,
      |L.orderedShadowVec x0 k * (z k - x k)| ≤ L.cStar ^ (k.val + 1) := by
    intro z hz k
    have hP : 0 ≤ L.cStar ^ (k.val + 1) := pow_nonneg (by linarith) _
    have hs : |(if x0 k = 0 then (1 : ℝ) else -1)| = 1 := by
      split_ifs <;> simp
    rw [hv, abs_mul, abs_mul, hs, one_mul, abs_of_nonneg hP]
    calc L.cStar ^ (k.val + 1) * |z k - x k| ≤ L.cStar ^ (k.val + 1) * 1 :=
          mul_le_mul_of_nonneg_left (hd1 z hz k) hP
      _ = L.cStar ^ (k.val + 1) := mul_one _
  obtain ⟨S, hSdef⟩ : ∃ S : ℝ, S = ∑ j ∈ Finset.range K.val, L.cStar ^ (j + 1) := ⟨_, rfl⟩
  have hS_fin : ∑ k : Fin n, (if k.val < K.val then L.cStar ^ (k.val + 1) else 0) = S := by
    rw [hSdef, Fin.sum_univ_eq_sum_range (fun j => if j < K.val then L.cStar ^ (j + 1) else 0) n,
      ← Finset.sum_filter]
    congr 1
    ext j
    simp only [Finset.mem_filter, Finset.mem_range]
    omega
  have hS0 : 0 ≤ S := by
    rw [hSdef]
    exact Finset.sum_nonneg fun j _ => pow_nonneg (by linarith) _
  have hgeom : (L.cStar - 1) * S = L.cStar ^ (K.val + 1) - L.cStar := by
    rw [hSdef]
    exact geom _ _
  have hv0_le : L.orderedShadowVec x0 ⬝ᵥ (u0 - x) ≤ S := by
    rw [hdot, ← hS_fin]
    apply Finset.sum_le_sum
    intro k _
    split_ifs with hk
    · exact (le_abs_self _).trans (hterm_abs u0 hu0_ext k)
    · rw [hu0K k (by omega), sub_self, mul_zero]
  have hKterm : L.orderedShadowVec x0 K * (u1 K - x K) = L.cStar ^ (K.val + 1) := by
    rw [hv, hxK]
    rcases h01v x0 hx0 K with h0 | h1
    · rw [if_pos h0]
      have hu : u1 K = 1 := by
        rcases h01v u1 hu1_ext K with h | h
        · exact absurd (h.trans h0.symm) hK
        · exact h
      rw [hu, h0]
      ring
    · have hne0 : x0 K ≠ 0 := by rw [h1]; norm_num
      rw [if_neg hne0]
      have hu : u1 K = 0 := by
        rcases h01v u1 hu1_ext K with h | h
        · exact h
        · exact absurd (h.trans h1.symm) hK
      rw [hu, h1]
      ring
  have hv1_ge : L.cStar ^ (K.val + 1) - S ≤ L.orderedShadowVec x0 ⬝ᵥ (u1 - x) := by
    rw [hdot, ← hS_fin]
    have hsplit : L.cStar ^ (K.val + 1) -
        ∑ k : Fin n, (if k.val < K.val then L.cStar ^ (k.val + 1) else 0) =
        ∑ k : Fin n, ((if k = K then L.cStar ^ (K.val + 1) else 0) -
          (if k.val < K.val then L.cStar ^ (k.val + 1) else 0)) := by
      rw [Finset.sum_sub_distrib]
      simp
    rw [hsplit]
    apply Finset.sum_le_sum
    intro k _
    by_cases hkK : k = K
    · rw [hkK, if_pos rfl, if_neg (lt_irrefl _), sub_zero]
      exact hKterm.ge
    · rw [if_neg hkK, zero_sub]
      by_cases hlt : k.val < K.val
      · rw [if_pos hlt]
        exact neg_le_of_abs_le (hterm_abs u1 hu1_ext k)
      · have hne : k.val ≠ K.val := fun h => hkK (Fin.ext h)
        rw [if_neg hlt, neg_zero, hu1K k (by omega), sub_self, mul_zero]
  have hc1_le : L.c ⬝ᵥ (u1 - x) ≤ L.cStar - 2 := by
    rw [hdot]
    have hcs : L.cStar - 2 = ∑ i, |L.c i| := by
      unfold LPData.cStar
      ring
    rw [hcs]
    apply Finset.sum_le_sum
    intro i _
    calc L.c i * (u1 i - x i) ≤ |L.c i * (u1 i - x i)| := le_abs_self _
      _ = |L.c i| * |u1 i - x i| := abs_mul _ _
      _ ≤ |L.c i| * 1 := mul_le_mul_of_nonneg_left (hd1 u1 hu1_ext i) (abs_nonneg _)
      _ = |L.c i| := mul_one _
  have hc0_ge : 1 ≤ L.c ⬝ᵥ (u0 - x) := by
    choose zc hzc using hcint
    have hz : ∀ i, ∃ z : ℤ, u0 i - x i = z := by
      intro i
      rcases h01v u0 hu0_ext i with h | h <;> rcases h01v x hx_ext i with h' | h'
      · exact ⟨0, by rw [h, h']; norm_num⟩
      · exact ⟨-1, by rw [h, h']; norm_num⟩
      · exact ⟨1, by rw [h, h']; norm_num⟩
      · exact ⟨0, by rw [h, h']; norm_num⟩
    choose zd hzd using hz
    have hint : L.c ⬝ᵥ (u0 - x) = ((∑ i, zc i * zd i : ℤ) : ℝ) := by
      rw [hdot]
      push_cast
      exact Finset.sum_congr rfl fun i _ => by rw [hzc i, hzd i]
    have hpos : 0 < L.c ⬝ᵥ (u0 - x) := by
      rw [dotProduct_sub]
      linarith
    rw [hint] at hpos ⊢
    have hpos' : (0 : ℤ) < ∑ i, zc i * zd i := by exact_mod_cast hpos
    have h1 : (1 : ℤ) ≤ ∑ i, zc i * zd i := by omega
    exact_mod_cast h1
  have hv0pos : 0 < L.orderedShadowVec x0 ⬝ᵥ (u0 - x) := by
    rw [dotProduct_sub]
    linarith
  have hv1pos : 0 < L.orderedShadowVec x0 ⬝ᵥ (u1 - x) := by
    rw [dotProduct_sub]
    linarith
  rw [div_lt_div_iff₀ hv1pos hv0pos]
  calc L.c ⬝ᵥ (u1 - x) * L.orderedShadowVec x0 ⬝ᵥ (u0 - x) ≤ (L.cStar - 2) * S :=
        mul_le_mul hc1_le hv0_le hv0pos.le (by linarith)
    _ < L.cStar ^ (K.val + 1) - S := by linarith
    _ ≤ 1 * L.orderedShadowVec x0 ⬝ᵥ (u1 - x) := by linarith
    _ ≤ L.c ⬝ᵥ (u0 - x) * L.orderedShadowVec x0 ⬝ᵥ (u1 - x) :=
        mul_le_mul_of_nonneg_right hc0_ge hv1pos.le
