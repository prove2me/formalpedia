-- Prove2me | solution 1 for WeierstrassCurve.veluPointHom_surjective_of_isAlgClosed
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/8d1d21fe-229b-551b-b7eb-3ed17482731f

import Mathlib
import Definitions.Def_WeierstrassCurve_Velu
import Definitions.Def_WeierstrassCurve_VeluQuotientMap
import Definitions.Def_WeierstrassCurve_VeluPointMap
import Definitions.Def_WeierstrassCurve_OddOrderSummingSet
import Theorems.Thm_WeierstrassCurve_isOddVeluSet_oddOrderSummingSet
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_veluPointHom_surjective_of_isAlgClosed

set_option autoImplicit false

open Polynomial WeierstrassCurve WeierstrassCurve.Affine

namespace VeluOddSurjAux

variable {K : Type*} [Field K]

theorem exists_quadratic_root [IsAlgClosed K] (b c : K) : ∃ y : K, y ^ 2 + b * y + c = 0 := by
  obtain ⟨y, hy⟩ := IsAlgClosed.exists_root (C 1 * X ^ 2 + C b * X + C c)
    (by rw [degree_quadratic (one_ne_zero' K)]; decide)
  exact ⟨y, by simpa [IsRoot] using hy⟩

theorem some_ext {W' : Affine K} {x₁ x₂ y₁ y₂ : K} {h₁ : W'.Nonsingular x₁ y₁}
    {h₂ : W'.Nonsingular x₂ y₂} (hx : x₁ = x₂) (hy : y₁ = y₂) :
    Point.some x₁ y₁ h₁ = Point.some x₂ y₂ h₂ := by
  subst hx; subst hy; rfl

section Poly

variable [DecidableEq K] (W : WeierstrassCurve K) (S : Finset (K × K))

noncomputable def D : K[X] := ∏ P ∈ S, (X - C P.1) ^ 2

noncomputable def N : K[X] :=
  X * D S + ∑ P ∈ S, (C (W.veluT P.1 P.2) * (X - C P.1) + C (W.veluU P.1 P.2)) *
    ∏ P' ∈ S.erase P, (X - C P'.1) ^ 2

theorem monic_D : (D S).Monic :=
  monic_prod_of_monic _ _ fun P _ => (monic_X_sub_C P.1).pow 2

theorem natDegree_D : (D S).natDegree = 2 * S.card := by
  rw [D, natDegree_prod_of_monic _ _ fun P _ => (monic_X_sub_C P.1).pow 2]
  simp [natDegree_pow, Finset.sum_const, mul_comm]

theorem eval_D (x : K) : (D S).eval x = ∏ P ∈ S, (x - P.1) ^ 2 := by
  simp [D, eval_prod]

theorem eval_N (x : K) : (N W S).eval x = x * ∏ P ∈ S, (x - P.1) ^ 2 +
    ∑ P ∈ S, (W.veluT P.1 P.2 * (x - P.1) + W.veluU P.1 P.2) * ∏ P' ∈ S.erase P, (x - P'.1) ^ 2 := by
  simp [N, D, eval_prod, eval_finset_sum]

theorem monic_N_sub (u : K) : (N W S - C u * D S).Monic ∧ (N W S - C u * D S).degree ≠ 0 := by
  have hD := monic_D S
  have hp : (X * D S).Monic := monic_X.mul hD
  have hpdeg : (X * D S).natDegree = 2 * S.card + 1 := by
    rw [natDegree_X_mul hD.ne_zero, natDegree_D]

  set q : K[X] := ∑ P ∈ S, (C (W.veluT P.1 P.2) * (X - C P.1) + C (W.veluU P.1 P.2)) *
    ∏ P' ∈ S.erase P, (X - C P'.1) ^ 2 - C u * D S with hq
  have hq1 : (∑ P ∈ S, (C (W.veluT P.1 P.2) * (X - C P.1) + C (W.veluU P.1 P.2)) *
      ∏ P' ∈ S.erase P, (X - C P'.1) ^ 2).natDegree ≤ 2 * S.card := by
    refine natDegree_sum_le_of_forall_le _ _ fun P hP => ?_
    have h1 : (C (W.veluT P.1 P.2) * (X - C P.1) + C (W.veluU P.1 P.2)).natDegree ≤ 1 := by
      refine (natDegree_add_le _ _).trans (max_le ?_ ?_)
      · exact (natDegree_C_mul_le _ _).trans (natDegree_X_sub_C P.1).le
      · rw [natDegree_C]; exact zero_le_one
    have h2 : (∏ P' ∈ S.erase P, (X - C P'.1) ^ 2).natDegree = 2 * (S.card - 1) := by
      rw [natDegree_prod_of_monic _ _ fun P' _ => (monic_X_sub_C P'.1).pow 2]
      simp [natDegree_pow, Finset.sum_const, Finset.card_erase_of_mem hP, mul_comm]
    refine (natDegree_mul_le).trans ?_
    rw [h2]
    have : 1 ≤ S.card := Finset.card_pos.mpr ⟨P, hP⟩
    omega
  have hq2 : (C u * D S).natDegree ≤ 2 * S.card :=
    (natDegree_C_mul_le _ _).trans (natDegree_D S).le
  have hqdeg : q.natDegree ≤ 2 * S.card := (natDegree_sub_le _ _).trans (max_le hq1 hq2)
  have hlt : q.degree < (X * D S).degree :=
    degree_lt_degree (lt_of_le_of_lt hqdeg (by rw [hpdeg]; exact Nat.lt_succ_self _))
  have heq : N W S - C u * D S = X * D S + q := by rw [hq, N]; ring
  rw [heq]
  refine ⟨hp.add_of_left hlt, ?_⟩
  have hnat : (X * D S + q).natDegree = 2 * S.card + 1 := by
    rw [natDegree_add_eq_left_of_degree_lt hlt, hpdeg]
  exact (natDegree_pos_iff_degree_pos.mp (by rw [hnat]; exact Nat.succ_pos _)).ne'

theorem veluX_mul_eval_D {x : K} (hx : ∀ P ∈ S, x ≠ P.1) :
    W.veluX S x * (D S).eval x = (N W S).eval x := by
  rw [W.veluX_def_of_ne S hx, eval_D, eval_N, add_mul, Finset.sum_mul]
  congr 1
  refine Finset.sum_congr rfl fun P hP => ?_
  have h0 : (x - P.1) ^ 2 ≠ 0 := pow_ne_zero _ (sub_ne_zero.mpr (hx P hP))
  rw [← Finset.mul_prod_erase S (fun P' => (x - P'.1) ^ 2) hP, ← mul_assoc, div_mul_cancel₀ _ h0]

theorem eval_N_sub_at {P : K × K} (hP : P ∈ S) (u : K) :
    (N W S - C u * D S).eval P.1 = W.veluU P.1 P.2 * ∏ P' ∈ S.erase P, (P.1 - P'.1) ^ 2 := by
  have hD0 : ∏ P' ∈ S, (P.1 - P'.1) ^ 2 = 0 := Finset.prod_eq_zero hP (by simp)
  rw [eval_sub, eval_mul, eval_C, eval_D, eval_N, hD0, mul_zero, mul_zero, sub_zero, zero_add,
    Finset.sum_eq_single P]
  · rw [sub_self, mul_zero, zero_add]
  · intro P'' hP'' hne
    have hmem : P ∈ S.erase P'' := Finset.mem_erase.mpr ⟨hne.symm, hP⟩
    rw [Finset.prod_eq_zero hmem (by simp), mul_zero]
  · intro h; exact absurd hP h

end Poly

theorem exists_mem_fst_eq_of_mem_zmultiples [DecidableEq K] {W : WeierstrassCurve K}
    {Q : W.toAffine.Point} {ℓ : ℕ} (hℓ : 0 < ℓ) (hQord : addOrderOf Q = ℓ) {x y : K}
    {h : W.toAffine.Nonsingular x y}
    (hmem : (Point.some x y h : W.toAffine.Point) ∈ AddSubgroup.zmultiples Q) :
    ∃ P ∈ W.oddOrderSummingSet Q (ℓ / 2), P.1 = x := by
  classical
  have hfin : IsOfFinAddOrder Q := addOrderOf_pos_iff.mp (hQord ▸ hℓ)
  rw [hfin.mem_zmultiples_iff_mem_range_addOrderOf, Finset.mem_image] at hmem
  obtain ⟨k, hk, hkQ⟩ := hmem
  rw [Finset.mem_range, hQord] at hk
  have hk0 : k ≠ 0 := by
    rintro rfl
    rw [zero_nsmul] at hkQ
    cases hkQ
  by_cases hkl : k ≤ ℓ / 2
  · refine ⟨(k • Q).coordsOrZero, (mem_oddOrderSummingSet W).mpr
      ⟨k, Nat.one_le_iff_ne_zero.mpr hk0, hkl, rfl⟩, ?_⟩
    rw [hkQ]
    rfl
  · have hk' : (ℓ - k) • Q = -(k • Q) := by
      rw [eq_neg_iff_add_eq_zero, ← add_nsmul, Nat.sub_add_cancel hk.le, ← hQord,
        addOrderOf_nsmul_eq_zero]
    refine ⟨((ℓ - k) • Q).coordsOrZero, (mem_oddOrderSummingSet W).mpr
      ⟨ℓ - k, by omega, by omega, rfl⟩, ?_⟩
    rw [hk', hkQ, Affine.Point.neg_some]
    rfl

end VeluOddSurjAux

open VeluOddSurjAux in
theorem solution
    {K : Type*} [Field K] [DecidableEq K] [IsAlgClosed K] (W : WeierstrassCurve K) [W.IsElliptic]
    {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) (hℓK : (ℓ : K) ≠ 0)
    (Q : W.toAffine.Point) (hQord : addOrderOf Q = ℓ) :
    let S := W.oddOrderSummingSet Q (ℓ / 2)
    ∀ φ : W.toAffine.Point →+ (W.veluQuotient S).toAffine.Point,
      (∀ (x y : K) (h : W.toAffine.Nonsingular x y),
        (.some x y h : W.toAffine.Point) ∉ AddSubgroup.zmultiples Q →
          ∃ h', φ (.some x y h) = .some (W.veluX S x) (W.veluY S x y) h') →
      Function.Surjective φ := by
  intro S φ hφ T

  have hodd : ℓ / 2 ≤ (ℓ - 1) / 2 := by
    rcases hℓ.eq_two_or_odd' with h | ⟨m, hm⟩
    · exact absurd h hℓ2
    · omega
  have hS : W.IsOddVeluSet S := isOddVeluSet_oddOrderSummingSet hℓ hℓ2 hQord hodd
  rcases T with _ | ⟨u, v, huv⟩
  · exact ⟨0, map_zero φ⟩
  ·
    obtain ⟨hmonic, hdeg⟩ := monic_N_sub W S u
    obtain ⟨xs, hxs⟩ := IsAlgClosed.exists_root _ hdeg

    have hxS : ∀ P ∈ S, xs ≠ P.1 := by
      intro P hP hx
      have hval0 : (N W S - C u * D S).eval P.1 = 0 := hx ▸ hxs
      rw [eval_N_sub_at W S hP u] at hval0
      refine (mul_ne_zero (pow_ne_zero 2 (hS.gy_ne_zero P hP)) ?_) hval0
      refine Finset.prod_ne_zero_iff.mpr fun P' hP' => pow_ne_zero 2 (sub_ne_zero.mpr fun h => ?_)
      exact (Finset.mem_erase.mp hP').1 (hS.x_injOn P hP P' (Finset.mem_of_mem_erase hP') h).symm

    have hD0 : (D S).eval xs ≠ 0 := by
      rw [eval_D]
      exact Finset.prod_ne_zero_iff.mpr fun P hP => pow_ne_zero 2 (sub_ne_zero.mpr (hxS P hP))
    have hu : W.veluX S xs = u := by
      have h1 := veluX_mul_eval_D W S hxS
      have h2 : (N W S - C u * D S).eval xs = 0 := hxs
      rw [eval_sub, eval_mul, eval_C, sub_eq_zero] at h2
      rw [h2] at h1
      exact mul_right_cancel₀ hD0 h1

    obtain ⟨ys, hys⟩ := exists_quadratic_root (W.a₁ * xs + W.a₃)
      (-(xs ^ 3 + W.a₂ * xs ^ 2 + W.a₄ * xs + W.a₆))
    have hP : W.toAffine.Equation xs ys := by
      rw [Affine.equation_iff]
      linear_combination hys
    have hPns : W.toAffine.Nonsingular xs ys := W.toAffine.equation_iff_nonsingular.mp hP

    have hnot : (Point.some xs ys hPns : W.toAffine.Point) ∉ AddSubgroup.zmultiples Q := by
      intro hmem
      obtain ⟨P, hP, hPx⟩ := exists_mem_fst_eq_of_mem_zmultiples hℓ.pos hQord hmem
      exact hxS P hP hPx.symm
    obtain ⟨h', hφP⟩ := hφ xs ys hPns hnot

    rcases Affine.Y_eq_of_X_eq h'.left huv.left hu with hv | hv
    · exact ⟨Point.some xs ys hPns, hφP.trans (some_ext hu hv)⟩
    · refine ⟨-Point.some xs ys hPns, ?_⟩
      rw [map_neg, hφP, Affine.Point.neg_some]
      exact some_ext hu (by rw [hv, hu, Affine.negY_negY])

end S_WeierstrassCurve_veluPointHom_surjective_of_isAlgClosed
end P2MW
export P2MW.S_WeierstrassCurve_veluPointHom_surjective_of_isAlgClosed (solution)
