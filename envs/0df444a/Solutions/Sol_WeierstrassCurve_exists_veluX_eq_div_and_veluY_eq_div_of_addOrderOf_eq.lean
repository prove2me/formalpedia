-- Prove2me | solution 1 for WeierstrassCurve.exists_veluX_eq_div_and_veluY_eq_div_of_addOrderOf_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/5c8981ce-d13e-59bf-b52d-3bc10873aa21

import Mathlib
import Definitions.Def_WeierstrassCurve_Velu
import Definitions.Def_WeierstrassCurve_VeluQuotientMap
import Definitions.Def_WeierstrassCurve_VeluPointMap
import Definitions.Def_WeierstrassCurve_OddOrderSummingSet
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_exists_veluX_eq_div_and_veluY_eq_div_of_addOrderOf_eq

set_option autoImplicit false

open Polynomial
open scoped Polynomial.Bivariate

noncomputable section

namespace WeierstrassCurve
p2m_export "WeierstrassCurve" "Affine Affine.negY mk.injEq a₃ a₁ map b₂ mk Ψ₂Sq a₄ a₂ a₆ Affine.Point.some Affine.Point.some.injEq toAffine Affine.Point Affine.Point.some_ne_zero Affine.Y_eq_of_X_eq Affine.equation_iff Affine.Point.neg_some j b₄ veluGx veluGy veluT veluU veluT_eq veluU_eq_Ψ₂Sq_eval IsOddVeluSet veluX veluY Affine.Point.coordsOrZero_some oddOrderSummingSet mem_oddOrderSummingSet"
namespace VeluFactor
p2m_open "WeierstrassCurve"

section Poly

variable {k : Type*} [Field k] (Xs : Finset k)

def D : k[X] := ∏ ξ ∈ Xs, (X - C ξ)

theorem monic_D : (D Xs).Monic := monic_prod_of_monic _ _ fun ξ _ => monic_X_sub_C ξ

theorem natDegree_D : (D Xs).natDegree = Xs.card := by
  rw [D, natDegree_prod_of_monic _ _ fun ξ _ => monic_X_sub_C ξ]
  simp

theorem eval_D (x : k) : (D Xs).eval x = ∏ ξ ∈ Xs, (x - ξ) := by
  simp only [D, eval_prod, eval_sub, eval_X, eval_C]

theorem eval_D_ne_zero {x : k} (hx : x ∉ Xs) : (D Xs).eval x ≠ 0 := by
  rw [eval_D]
  exact Finset.prod_ne_zero_iff.mpr fun ξ hξ => sub_ne_zero.mpr fun h => hx (h ▸ hξ)

theorem eval_D_eq_zero {ξ : k} (hξ : ξ ∈ Xs) : (D Xs).eval ξ = 0 := by
  rw [eval_D]
  exact Finset.prod_eq_zero hξ (sub_self ξ)

variable [DecidableEq k] (t u A : k → k) (a₁ a₃ : k)

def E (ξ : k) : k[X] := ∏ ξ' ∈ Xs.erase ξ, (X - C ξ')

def Pk : k[X] := X * D Xs ^ 2 + ∑ ξ ∈ Xs, (C (t ξ) * (X - C ξ) + C (u ξ)) * E Xs ξ ^ 2

def M1 (ξ : k) : k[X] := (C (2 * u ξ) + C (t ξ) * (X - C ξ)) * E Xs ξ ^ 3

def M0 (ξ : k) : k[X] :=
  (C (u ξ) * (C a₁ * X + C a₃) + (C (a₁ * t ξ) * (X - C ξ) + C (A ξ)) * (X - C ξ)) * E Xs ξ ^ 3

def N1 : k[X] := D Xs ^ 3 - ∑ ξ ∈ Xs, M1 Xs t u ξ

def N0 : k[X] := -∑ ξ ∈ Xs, M0 Xs t u A a₁ a₃ ξ

theorem monic_E (ξ : k) : (E Xs ξ).Monic := monic_prod_of_monic _ _ fun ξ _ => monic_X_sub_C ξ

theorem natDegree_E {ξ : k} (hξ : ξ ∈ Xs) : (E Xs ξ).natDegree = Xs.card - 1 := by
  rw [E, natDegree_prod_of_monic _ _ fun ξ _ => monic_X_sub_C ξ]
  simp [Finset.card_erase_of_mem hξ]

theorem natDegree_tail_lt :
    (∑ ξ ∈ Xs, (C (t ξ) * (X - C ξ) + C (u ξ)) * E Xs ξ ^ 2).natDegree <
      (X * D Xs ^ 2 : k[X]).natDegree := by
  rw [monic_X.natDegree_mul ((monic_D Xs).pow 2), natDegree_X, natDegree_pow, natDegree_D]
  have hle : (∑ ξ ∈ Xs, (C (t ξ) * (X - C ξ) + C (u ξ)) * E Xs ξ ^ 2).natDegree ≤
      2 * Xs.card - 1 := by
    refine natDegree_sum_le_of_forall_le _ _ fun ξ hξ => ?_
    have hcard : 1 ≤ Xs.card := Finset.card_pos.mpr ⟨ξ, hξ⟩
    calc ((C (t ξ) * (X - C ξ) + C (u ξ)) * E Xs ξ ^ 2).natDegree
        ≤ (C (t ξ) * (X - C ξ) + C (u ξ)).natDegree + (E Xs ξ ^ 2).natDegree := natDegree_mul_le
      _ ≤ 1 + 2 * (Xs.card - 1) := by
          gcongr
          · exact (natDegree_add_le _ _).trans
              (max_le ((natDegree_C_mul_le _ _).trans (natDegree_X_sub_C ξ).le) (by simp))
          · rw [natDegree_pow, natDegree_E Xs hξ]
      _ = 2 * Xs.card - 1 := by omega
  omega

theorem monic_Pk : (Pk Xs t u).Monic :=
  (monic_X.mul ((monic_D Xs).pow 2)).add_of_left (degree_lt_degree (natDegree_tail_lt Xs t u))

theorem natDegree_Pk : (Pk Xs t u).natDegree = (D Xs ^ 2).natDegree + 1 := by
  rw [Pk, natDegree_add_eq_left_of_natDegree_lt (natDegree_tail_lt Xs t u),
    monic_X.natDegree_mul ((monic_D Xs).pow 2), natDegree_X]
  ring

theorem eval_E_mul {ξ : k} (hξ : ξ ∈ Xs) (x : k) :
    (E Xs ξ).eval x * (x - ξ) = (D Xs).eval x := by
  simp only [E, eval_D, eval_prod, eval_sub, eval_X, eval_C]
  exact Finset.prod_erase_mul Xs (fun ξ' => x - ξ') hξ

theorem eval_E_self_ne_zero (ξ : k) : (E Xs ξ).eval ξ ≠ 0 := by
  simp only [E, eval_prod, eval_sub, eval_X, eval_C]
  exact Finset.prod_ne_zero_iff.mpr fun ξ' hξ' => sub_ne_zero.mpr (Finset.ne_of_mem_erase hξ').symm

theorem eval_E_of_ne {ξ ξ₀ : k} (hξ₀ : ξ₀ ∈ Xs) (hne : ξ ≠ ξ₀) : (E Xs ξ).eval ξ₀ = 0 := by
  simp only [E, eval_prod, eval_sub, eval_X, eval_C]
  exact Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hne.symm, hξ₀⟩) (sub_self ξ₀)

theorem eval_Pk_self {ξ₀ : k} (hξ₀ : ξ₀ ∈ Xs) :
    (Pk Xs t u).eval ξ₀ = u ξ₀ * (E Xs ξ₀).eval ξ₀ ^ 2 := by
  simp only [Pk, eval_add, eval_mul, eval_pow, eval_X, eval_C, eval_sub, eval_finsetSum,
    eval_D_eq_zero Xs hξ₀]
  rw [Finset.sum_eq_single_of_mem ξ₀ hξ₀ fun ξ _ hne => by rw [eval_E_of_ne Xs hξ₀ hne]; ring]
  ring

theorem isCoprime_Pk (hu : ∀ ξ ∈ Xs, u ξ ≠ 0) : IsCoprime (Pk Xs t u) (D Xs ^ 2) := by
  refine IsCoprime.pow_right ?_
  rw [D]
  refine IsCoprime.prod_right fun ξ hξ => ((irreducible_X_sub_C ξ).coprime_iff_not_dvd.mpr ?_).symm
  rw [dvd_iff_isRoot, IsRoot.def, eval_Pk_self Xs t u hξ]
  exact mul_ne_zero (hu ξ hξ) (pow_ne_zero _ (eval_E_self_ne_zero Xs ξ))

theorem eval_Pk_div {x : k} (hx : x ∉ Xs) :
    (Pk Xs t u).eval x / (D Xs).eval x ^ 2 =
      x + ∑ ξ ∈ Xs, (t ξ / (x - ξ) + u ξ / (x - ξ) ^ 2) := by
  have hd := eval_D_ne_zero Xs hx
  rw [div_eq_iff (pow_ne_zero 2 hd), add_mul, Finset.sum_mul]
  simp only [Pk, eval_add, eval_mul, eval_pow, eval_X, eval_C, eval_sub, eval_finsetSum]
  congr 1
  refine Finset.sum_congr rfl fun ξ hξ => ?_
  have hxξ : x - ξ ≠ 0 := sub_ne_zero.mpr fun h => hx (h ▸ hξ)
  rw [← eval_E_mul Xs hξ, div_add_div _ _ hxξ (pow_ne_zero 2 hxξ),
    div_mul_eq_mul_div, eq_div_iff (mul_ne_zero hxξ (pow_ne_zero 2 hxξ))]
  ring

theorem eval_N_div {x : k} (hx : x ∉ Xs) (y : k) :
    ((N0 Xs t u A a₁ a₃).eval x + (N1 Xs t u).eval x * y) / (D Xs).eval x ^ 3 =
      y - ∑ ξ ∈ Xs, (u ξ * (2 * y + a₁ * x + a₃) / (x - ξ) ^ 3 +
        (t ξ * (a₁ * (x - ξ) + y) + A ξ) / (x - ξ) ^ 2) := by
  have hd := eval_D_ne_zero Xs hx
  have key : ∀ ξ ∈ Xs, (M0 Xs t u A a₁ a₃ ξ).eval x + (M1 Xs t u ξ).eval x * y =
      (u ξ * (2 * y + a₁ * x + a₃) / (x - ξ) ^ 3 +
        (t ξ * (a₁ * (x - ξ) + y) + A ξ) / (x - ξ) ^ 2) * (D Xs).eval x ^ 3 := by
    intro ξ hξ
    have hxξ : x - ξ ≠ 0 := sub_ne_zero.mpr fun h => hx (h ▸ hξ)
    rw [← eval_E_mul Xs hξ, div_add_div _ _ (pow_ne_zero 3 hxξ) (pow_ne_zero 2 hxξ),
      div_mul_eq_mul_div, eq_div_iff (mul_ne_zero (pow_ne_zero 3 hxξ) (pow_ne_zero 2 hxξ))]
    simp only [M0, M1, eval_add, eval_mul, eval_pow, eval_X, eval_C, eval_sub]
    ring
  rw [div_eq_iff (pow_ne_zero 3 hd), sub_mul, Finset.sum_mul, ← Finset.sum_congr rfl key,
    Finset.sum_add_distrib, ← Finset.sum_mul]
  simp only [N0, N1, eval_neg, eval_sub, eval_pow, eval_finsetSum]
  ring

end Poly

section Curve

variable {F : Type*} [Field F] (W : WeierstrassCurve F)

def AF : F[X] :=
  C (2 * W.a₁) * (X ^ 3 + C W.a₂ * X ^ 2 + C W.a₄ * X + C W.a₆) +
    C W.a₁ * (C W.a₁ * X + C W.a₃) ^ 2 +
      (C 3 * X ^ 2 + C (2 * W.a₂) * X + C W.a₄) * (C W.a₁ * X + C W.a₃)

theorem veluA_eq {ξ η : F} (h : W.toAffine.Equation ξ η) :
    -(W.veluT ξ η * η) + (W.a₁ * W.veluU ξ η - W.veluGx ξ η * W.veluGy ξ η)
      = (AF W).eval ξ := by
  rw [Affine.equation_iff] at h
  simp only [AF, veluT, veluU, veluGx, veluGy, eval_add, eval_mul, eval_pow, eval_C, eval_X]
  linear_combination 2 * W.a₁ * h

theorem veluT_eq_eval (ξ η : F) :
    W.veluT ξ η = (C 6 * X ^ 2 + C W.b₂ * X + C W.b₄ : F[X]).eval ξ := by
  rw [veluT_eq]
  simp only [eval_add, eval_mul, eval_pow, eval_C, eval_X]

variable {W}

variable [DecidableEq F]

omit [DecidableEq F] in

theorem some_eq_or_eq_neg_of_x_eq {x y y' : F} (h : W.toAffine.Nonsingular x y)
    (h' : W.toAffine.Nonsingular x y') :
    (Affine.Point.some x y' h' : W.toAffine.Point) = .some x y h ∨
      (Affine.Point.some x y' h' : W.toAffine.Point) = -.some x y h := by
  rcases Affine.Y_eq_of_X_eq h'.left h.left rfl with hy | hy
  · left; simp only [hy]
  · right
    rw [Affine.Point.neg_some]
    simp only [hy]

variable {Q : W.toAffine.Point} {n : ℕ}

theorem nsmul_ne_zero_of_lt (hQ : addOrderOf Q = 2 * n + 1) {j : ℕ} (hj1 : 1 ≤ j)
    (hj2 : j ≤ 2 * n) : j • Q ≠ 0 :=
  nsmul_ne_zero_of_lt_addOrderOf (by omega) (by rw [hQ]; omega)

theorem mem_image_fst_iff (hQ : addOrderOf Q = 2 * n + 1) (ξ : F) :
    ξ ∈ (W.oddOrderSummingSet Q n).image Prod.fst ↔
      ∃ η h, (.some ξ η h : W.toAffine.Point) ∈ AddSubgroup.zmultiples Q := by
  constructor
  · intro hξ
    obtain ⟨P, hP, rfl⟩ := Finset.mem_image.mp hξ
    obtain ⟨j, hj1, hjn, hjP⟩ := (W.mem_oddOrderSummingSet).mp hP
    have hjQ : j • Q ≠ 0 := nsmul_ne_zero_of_lt hQ hj1 (by omega)
    rcases hj : j • Q with _ | ⟨x, y, h⟩
    · exact absurd hj hjQ
    · rw [hj, Affine.Point.coordsOrZero_some] at hjP
      subst hjP
      exact ⟨y, h, hj ▸ ⟨(j : ℤ), natCast_zsmul Q j⟩⟩
  · rintro ⟨η, h, hmem⟩
    have hfin : IsOfFinAddOrder Q := addOrderOf_pos_iff.mp (by rw [hQ]; omega)
    rw [hfin.mem_zmultiples_iff_mem_range_addOrderOf, Finset.mem_image] at hmem
    obtain ⟨j, hj, hjP⟩ := hmem
    rw [Finset.mem_range, hQ] at hj
    have hj0 : j ≠ 0 := by
      rintro rfl
      rw [zero_nsmul] at hjP
      exact Affine.Point.some_ne_zero h hjP.symm
    by_cases hjn : j ≤ n
    · refine Finset.mem_image.mpr ⟨(ξ, η), (W.mem_oddOrderSummingSet).mpr
        ⟨j, by omega, hjn, ?_⟩, rfl⟩
      simp only [hjP, Affine.Point.coordsOrZero_some]
    · refine Finset.mem_image.mpr ⟨(ξ, W.toAffine.negY ξ η),
        (W.mem_oddOrderSummingSet).mpr ⟨2 * n + 1 - j, by omega, by omega, ?_⟩, rfl⟩
      have hneg : (2 * n + 1 - j) • Q = -(j • Q) := by
        rw [eq_neg_iff_add_eq_zero, ← add_nsmul, Nat.sub_add_cancel (by omega), ← hQ,
          addOrderOf_nsmul_eq_zero]
      simp only [hneg, hjP, Affine.Point.neg_some, Affine.Point.coordsOrZero_some]

theorem isOddVeluSet_of_addOrderOf_eq (hQ : addOrderOf Q = 2 * n + 1) :
    W.IsOddVeluSet (W.oddOrderSummingSet Q n) := by

  have hdesc : ∀ P ∈ W.oddOrderSummingSet Q n, ∃ (j : ℕ) (x y : F)
      (h : W.toAffine.Nonsingular x y), 1 ≤ j ∧ j ≤ n ∧ j • Q = .some x y h ∧ P = (x, y) := by
    intro P hP
    obtain ⟨j, hj1, hjn, hjP⟩ := (W.mem_oddOrderSummingSet).mp hP
    have hjQ : j • Q ≠ 0 := nsmul_ne_zero_of_lt hQ hj1 (by omega)
    rcases hj : j • Q with _ | ⟨x, y, h⟩
    · exact absurd hj hjQ
    · rw [hj, Affine.Point.coordsOrZero_some] at hjP
      exact ⟨j, x, y, h, hj1, hjn, hj, hjP.symm⟩
  refine ⟨fun P hP => ?_, fun P hP => ?_, fun P hP P' hP' hx => ?_⟩
  · obtain ⟨j, x, y, h, -, -, -, rfl⟩ := hdesc P hP
    exact h.left
  · obtain ⟨j, x, y, h, hj1, hjn, hjQ, rfl⟩ := hdesc P hP
    intro hgy
    have hneg : W.toAffine.negY x y = y := by
      have h0 : -(2 * y + W.a₁ * x + W.a₃) = 0 := hgy
      simp only [Affine.negY]
      linear_combination -(neg_eq_zero.mp h0)
    have hself : -(Affine.Point.some x y h : W.toAffine.Point) = .some x y h := by
      rw [Affine.Point.neg_some]
      exact (Affine.Point.some.injEq _ _ _ _ _ _).mpr ⟨rfl, hneg⟩
    have h2 : (2 * j) • Q = 0 := by
      rw [mul_comm, mul_nsmul, hjQ, two_nsmul]
      nth_rewrite 2 [← hself]
      exact add_neg_cancel _
    exact nsmul_ne_zero_of_lt hQ (j := 2 * j) (by omega) (by omega) h2
  · obtain ⟨j, x, y, h, hj1, hjn, hjQ, rfl⟩ := hdesc P hP
    obtain ⟨j', x', y', h', hj1', hjn', hjQ', rfl⟩ := hdesc P' hP'
    simp only at hx
    subst hx
    rcases some_eq_or_eq_neg_of_x_eq h h' with e | e
    · simp only [Prod.mk.injEq, true_and]
      have := (Affine.Point.some.injEq x y' h' x y h).mp e
      exact this.2.symm
    · exfalso
      have hsum : (j + j') • Q = 0 := by rw [add_nsmul, hjQ, hjQ', e, add_neg_cancel]
      exact nsmul_ne_zero_of_lt hQ (j := j + j') (by omega) (by omega) hsum

end Curve

section Main

variable {F : Type*} [Field F] [DecidableEq F] (W : WeierstrassCurve F)
variable {n : ℕ} (Q : W.toAffine.Point) (hQ : addOrderOf Q = 2 * n + 1)

include hQ in
theorem shape : ∃ (P S N₀ N₁ R : F[X]) (B : Finset F), P.Monic ∧ P.natDegree = S.natDegree + 1 ∧
    IsCoprime P S ∧
    (∀ (x y : F) (h : W.toAffine.Nonsingular x y),
      (x ∈ B ↔ (.some x y h : W.toAffine.Point) ∈ AddSubgroup.zmultiples Q)) ∧
    ∀ x : F, x ∉ B → S.eval x ≠ 0 ∧ R.eval x ≠ 0 ∧
      W.veluX (W.oddOrderSummingSet Q n) x = P.eval x / S.eval x ∧
      ∀ y : F, W.veluY (W.oddOrderSummingSet Q n) x y
        = (N₀.eval x + N₁.eval x * y) / R.eval x := by
  have hOdd := isOddVeluSet_of_addOrderOf_eq hQ
  set Xs : Finset F := (W.oddOrderSummingSet Q n).image Prod.fst with hXsdef
  have hmemXs : ∀ ξ, ξ ∈ Xs ↔ ∃ η h,
      (.some ξ η h : W.toAffine.Point) ∈ AddSubgroup.zmultiples Q := mem_image_fst_iff hQ
  set t : F → F := fun ξ => (C 6 * X ^ 2 + C W.b₂ * X + C W.b₄ : F[X]).eval ξ with htdef
  set u : F → F := fun ξ => W.Ψ₂Sq.eval ξ with hudef
  set A : F → F := fun ξ => (AF W).eval ξ with hAdef
  have hveluX : ∀ x, x ∉ Xs → W.veluX (W.oddOrderSummingSet Q n) x
      = (Pk Xs t u).eval x / (D Xs).eval x ^ 2 := by
    intro x hx
    rw [eval_Pk_div Xs t u hx, veluX, hXsdef,
      Finset.sum_image fun P hP P' hP' h => hOdd.x_injOn P hP P' hP' h]
    refine congr_arg _ (Finset.sum_congr rfl fun P hP => ?_)
    rw [veluT_eq_eval, veluU_eq_Ψ₂Sq_eval _ (hOdd.equation P hP)]
  have hveluY : ∀ x y, x ∉ Xs → W.veluY (W.oddOrderSummingSet Q n) x y =
      ((N0 Xs t u A W.a₁ W.a₃).eval x + (N1 Xs t u).eval x * y) / (D Xs).eval x ^ 3 := by
    intro x y hx
    rw [eval_N_div Xs t u A _ _ hx, veluY, hXsdef,
      Finset.sum_image fun P hP P' hP' h => hOdd.x_injOn P hP P' hP' h]
    refine congr_arg _ (Finset.sum_congr rfl fun P hP => ?_)
    rw [hAdef]
    dsimp only
    rw [← veluA_eq W (hOdd.equation P hP), veluT_eq_eval,
      veluU_eq_Ψ₂Sq_eval _ (hOdd.equation P hP)]
    ring
  refine ⟨Pk Xs t u, D Xs ^ 2, N0 Xs t u A W.a₁ W.a₃, N1 Xs t u, D Xs ^ 3, Xs, monic_Pk Xs t u,
    natDegree_Pk Xs t u, ?_, ?_, ?_⟩
  · refine isCoprime_Pk Xs t u fun ξ hξ => ?_
    obtain ⟨P₀, hP₀, rfl⟩ := Finset.mem_image.mp hξ
    rw [hudef]
    dsimp only
    rw [← veluU_eq_Ψ₂Sq_eval _ (hOdd.equation P₀ hP₀), veluU]
    exact pow_ne_zero _ (hOdd.gy_ne_zero P₀ hP₀)
  · intro x y h
    rw [hmemXs]
    constructor
    · rintro ⟨η, h', hmem⟩
      rcases some_eq_or_eq_neg_of_x_eq h' h with e | e
      · rw [e]; exact hmem
      · rw [e]; exact AddSubgroup.neg_mem _ hmem
    · intro hmem; exact ⟨y, h, hmem⟩
  · intro x hx
    have hD := eval_D_ne_zero Xs hx
    refine ⟨by rw [eval_pow]; exact pow_ne_zero _ hD, by rw [eval_pow]; exact pow_ne_zero _ hD,
      by rw [eval_pow, hveluX x hx], fun y => by rw [eval_pow, hveluY x y hx]⟩

end Main

end WeierstrassCurve.VeluFactor

end

theorem solution
    {F : Type*} [Field F] [DecidableEq F] (W : WeierstrassCurve F)
    (n : ℕ) (Q : W.toAffine.Point) (hQ : addOrderOf Q = 2 * n + 1) :
    ∃ (P S N₀ N₁ R : Polynomial F) (B : Finset F), P.Monic ∧ P.natDegree = S.natDegree + 1 ∧
      IsCoprime P S ∧
      (∀ (x y : F) (h : W.toAffine.Nonsingular x y),
        (x ∈ B ↔ (.some x y h : W.toAffine.Point) ∈ AddSubgroup.zmultiples Q)) ∧
      ∀ x : F, x ∉ B → S.eval x ≠ 0 ∧ R.eval x ≠ 0 ∧
        W.veluX (W.oddOrderSummingSet Q n) x = P.eval x / S.eval x ∧
        ∀ y : F, W.veluY (W.oddOrderSummingSet Q n) x y
          = (N₀.eval x + N₁.eval x * y) / R.eval x :=
  WeierstrassCurve.VeluFactor.shape W Q hQ

end S_WeierstrassCurve_exists_veluX_eq_div_and_veluY_eq_div_of_addOrderOf_eq
end P2MW
export P2MW.S_WeierstrassCurve_exists_veluX_eq_div_and_veluY_eq_div_of_addOrderOf_eq (solution)
