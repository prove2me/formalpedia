-- Prove2me | solution 1 for OddOrder.Peterfalvi.S15.inner_eq_zero_of_conj_diff_orthogonal
-- status  : ACCEPTED   (prove)
-- author  : @burkh4rt
-- created : 2026-11-12T16:51:26.730203+00:00
-- url     : https://prove2.me/submissions/9ce70a00-4f3d-459a-bb2a-c89f6d93de12

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Peterfalvi/S15_Tau1T.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_Peterfalvi_S15_Tau1T

-- ===== OddOrder/Peterfalvi/S15_Tau1T.lean =====
namespace OddOrder.Peterfalvi.S15

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Isaacs

open scoped Pointwise

variable {G : Type*} [Group G]

/-- Conjugation commutes with integer-cast scalars: `conj(ε•φ) = ε•conj(φ)` for `ε : ℤ`. -/
theorem ClassFunction.conj_intCast_smul {G : Type*} [Group G] (ε : ℤ)
    (φ : ClassFunction G ℂ) :
    ((ε : ℂ) • φ).conj = (ε : ℂ) • φ.conj :=
  ClassFunction.ext fun g => by
    rw [ClassFunction.conj_apply, ClassFunction.smul_apply, ClassFunction.smul_apply,
      ClassFunction.conj_apply, star_mul', star_intCast]

open scoped FiniteInduce in
/-- **The dirr conjugate identification** (the "(4.1)" step of Peterfalvi (13.4)): if `A, B`
are norm-one `ℤ`-irreducible virtual characters with `⟨A, B⟩ = 0` and the difference is
conjugation-antisymmetric (`Ā − B̄ = B − A` — automatic when `A − B` is a `conj`-negated
induced character), then `B = Ā`, and the common constituent is non-real (`⟨A, Ā⟩ = 0`). -/
theorem conj_eq_of_norm_one_conj_antisym {G : Type*} [Group G] [Finite G]
    {A B : ClassFunction G ℂ}
    (hAZ : A ∈ ZIrr G) (hBZ : B ∈ ZIrr G)
    (hA1 : ClassFunction.inner A A = 1) (hB1 : ClassFunction.inner B B = 1)
    (hAB : ClassFunction.inner A B = 0)
    (hconj : A.conj - B.conj = B - A) :
    B = A.conj ∧ ClassFunction.inner A A.conj = 0 := by
  classical
  obtain ⟨χA, εA, hεA, hAeq⟩ :=
    OddOrder.Peterfalvi.S16.exists_sign_irr_of_inner_self_one hAZ hA1
  obtain ⟨χB, εB, hεB, hBeq⟩ :=
    OddOrder.Peterfalvi.S16.exists_sign_irr_of_inner_self_one hBZ hB1
  have hεA0 : ((εA : ℂ)) ≠ 0 := by rcases hεA with h | h <;> rw [h] <;> norm_num
  have hεB0 : ((εB : ℂ)) ≠ 0 := by rcases hεB with h | h <;> rw [h] <;> norm_num
  -- distinct constituents: `χA ≠ χB`
  have hχne : (χA : ClassFunction G ℂ) ≠ (χB : ClassFunction G ℂ) := by
    intro h
    rw [hAeq, hBeq, ClassFunction.inner_smul_left,
      OddOrder.RepresentationTheory.inner_smul_right,
      OddOrder.RepresentationTheory.irr_cf_inner χA.isIrreducible χB.isIrreducible,
      if_pos h, star_intCast, mul_one] at hAB
    exact (mul_ne_zero hεA0 hεB0) hAB
  -- the rearranged conjugation identity `Ā + A = B + B̄`
  rw [sub_eq_sub_iff_add_eq_add] at hconj
  -- inner the identity with `χA`
  have hkey := congrArg (fun f : ClassFunction G ℂ =>
    ClassFunction.inner f (χA : ClassFunction G ℂ)) hconj
  simp only [ClassFunction.inner_add_left] at hkey
  rw [hAeq, ClassFunction.conj_intCast_smul, ClassFunction.inner_smul_left,
    ClassFunction.inner_smul_left, hBeq, ClassFunction.conj_intCast_smul,
    ClassFunction.inner_smul_left, ClassFunction.inner_smul_left,
    OddOrder.RepresentationTheory.irr_cf_inner χA.isIrreducible.conj χA.isIrreducible,
    OddOrder.RepresentationTheory.irr_cf_inner χA.isIrreducible χA.isIrreducible,
    OddOrder.RepresentationTheory.irr_cf_inner χB.isIrreducible χA.isIrreducible,
    OddOrder.RepresentationTheory.irr_cf_inner χB.isIrreducible.conj χA.isIrreducible,
    if_pos rfl,
    if_neg (show ¬ ((χB : ClassFunction G ℂ) = (χA : ClassFunction G ℂ)) from
      fun h => hχne h.symm)] at hkey
  -- case on the reality of `χA` and on the `χ̄B = χA` indicator
  by_cases hreal : ((χA : ClassFunction G ℂ)).conj = (χA : ClassFunction G ℂ)
  · -- real `χA`: `2εA = εB·[χ̄B = χA]`, impossible for `εA, εB = ±1`
    exfalso
    rw [if_pos hreal] at hkey
    by_cases hBcA : ((χB : ClassFunction G ℂ)).conj = (χA : ClassFunction G ℂ) <;>
      [rw [if_pos hBcA] at hkey; rw [if_neg hBcA] at hkey] <;>
      rcases hεA with h1 | h1 <;> rcases hεB with h2 | h2 <;>
      rw [h1, h2] at hkey <;> norm_num at hkey
  · -- non-real `χA`: `εA = εB·[χ̄B = χA]` forces the indicator `1` and `εA = εB`
    rw [if_neg hreal] at hkey
    by_cases hBcA : ((χB : ClassFunction G ℂ)).conj = (χA : ClassFunction G ℂ)
    · rw [if_pos hBcA] at hkey
      -- `χB = χ̄A` and `εA = εB`
      have hχBA : (χB : ClassFunction G ℂ) = ((χA : ClassFunction G ℂ)).conj := by
        rw [← hBcA, ClassFunction.conj_conj]
      have hεeq : (εA : ℂ) = (εB : ℂ) := by linear_combination hkey
      refine ⟨?_, ?_⟩
      · rw [hBeq, hχBA, ← hεeq, hAeq, ClassFunction.conj_intCast_smul]
      · rw [hAeq, ClassFunction.conj_intCast_smul, ClassFunction.inner_smul_left,
          OddOrder.RepresentationTheory.inner_smul_right,
          OddOrder.RepresentationTheory.irr_cf_inner χA.isIrreducible χA.isIrreducible.conj,
          if_neg (fun h => hreal h.symm), star_intCast]
        ring
    · exfalso
      rw [if_neg hBcA] at hkey
      exact hεA0 (by linear_combination hkey)

open scoped FiniteInduce in
/-- **The (13.4) cross-`τ` orthogonality brick**: for two conjugation-antisymmetric norm-one
pairs `(A, B)` and `(C, D)` (each `B = Ā`, `D = C̄` by `conj_eq_of_norm_one_conj_antisym`) with
orthogonal differences `⟨A − B, C − D⟩ = 0` (the (13.2.e) disjoint-support input), the leads
are orthogonal: `⟨A, C⟩ = 0`.  This is the "pairwise orthogonality of `λ^{τ₁}` and `θ^{τ₁}`"
of Peterfalvi (13.4) — the conjunct-5 producer of the θ-package. -/
theorem _root_.solution {G : Type*} [Group G] [Finite G]
    {A B C D : ClassFunction G ℂ}
    (hAZ : A ∈ ZIrr G) (hBZ : B ∈ ZIrr G) (hCZ : C ∈ ZIrr G) (hDZ : D ∈ ZIrr G)
    (hA1 : ClassFunction.inner A A = 1) (hB1 : ClassFunction.inner B B = 1)
    (hC1 : ClassFunction.inner C C = 1) (hD1 : ClassFunction.inner D D = 1)
    (hAB : ClassFunction.inner A B = 0) (hCD : ClassFunction.inner C D = 0)
    (hABconj : A.conj - B.conj = B - A) (hCDconj : C.conj - D.conj = D - C)
    (h0 : ClassFunction.inner (A - B) (C - D) = 0) :
    ClassFunction.inner A C = 0 := by
  classical
  obtain ⟨hBeq, hAAc⟩ := conj_eq_of_norm_one_conj_antisym hAZ hBZ hA1 hB1 hAB hABconj
  obtain ⟨hDeq, hCCc⟩ := conj_eq_of_norm_one_conj_antisym hCZ hDZ hC1 hD1 hCD hCDconj
  subst hBeq
  subst hDeq
  obtain ⟨χA, εA, hεA, hAeq⟩ :=
    OddOrder.Peterfalvi.S16.exists_sign_irr_of_inner_self_one hAZ hA1
  obtain ⟨χC, εC, hεC, hCeq⟩ :=
    OddOrder.Peterfalvi.S16.exists_sign_irr_of_inner_self_one hCZ hC1
  have hεA0 : ((εA : ℂ)) ≠ 0 := by rcases hεA with h | h <;> rw [h] <;> norm_num
  have hεC0 : ((εC : ℂ)) ≠ 0 := by rcases hεC with h | h <;> rw [h] <;> norm_num
  -- non-realness of the constituents (from `⟨A, Ā⟩ = 0`, `⟨C, C̄⟩ = 0`)
  have hArealne : ((χA : ClassFunction G ℂ)) ≠ ((χA : ClassFunction G ℂ)).conj := by
    intro h
    rw [hAeq, ClassFunction.conj_intCast_smul, ClassFunction.inner_smul_left,
      OddOrder.RepresentationTheory.inner_smul_right,
      OddOrder.RepresentationTheory.irr_cf_inner χA.isIrreducible χA.isIrreducible.conj,
      if_pos h, star_intCast, mul_one] at hAAc
    exact (mul_ne_zero hεA0 hεA0) hAAc
  have hCrealne : ((χC : ClassFunction G ℂ)) ≠ ((χC : ClassFunction G ℂ)).conj := by
    intro h
    rw [hCeq, ClassFunction.conj_intCast_smul, ClassFunction.inner_smul_left,
      OddOrder.RepresentationTheory.inner_smul_right,
      OddOrder.RepresentationTheory.irr_cf_inner χC.isIrreducible χC.isIrreducible.conj,
      if_pos h, star_intCast, mul_one] at hCCc
    exact (mul_ne_zero hεC0 hεC0) hCCc
  by_cases hAC : (χA : ClassFunction G ℂ) = (χC : ClassFunction G ℂ)
  · -- shared constituent: `h0 = ±2 ≠ 0`, contradiction
    exfalso
    have hACc : ((χA : ClassFunction G ℂ)) ≠ ((χC : ClassFunction G ℂ)).conj := by
      intro h
      exact hCrealne (hAC.symm.trans h)
    have hAcC : ((χA : ClassFunction G ℂ)).conj ≠ (χC : ClassFunction G ℂ) := by
      intro h
      exact hArealne ((h.trans hAC.symm).symm)
    have hAcCc : ((χA : ClassFunction G ℂ)).conj = ((χC : ClassFunction G ℂ)).conj := by
      rw [hAC]
    rw [hAeq, hCeq, ClassFunction.conj_intCast_smul, ClassFunction.conj_intCast_smul,
      ← smul_sub, ← smul_sub, ClassFunction.inner_smul_left,
      OddOrder.RepresentationTheory.inner_smul_right, star_intCast,
      ClassFunction.inner_sub_left, ClassFunction.inner_sub_right,
      ClassFunction.inner_sub_right,
      OddOrder.RepresentationTheory.irr_cf_inner χA.isIrreducible χC.isIrreducible,
      OddOrder.RepresentationTheory.irr_cf_inner χA.isIrreducible χC.isIrreducible.conj,
      OddOrder.RepresentationTheory.irr_cf_inner χA.isIrreducible.conj χC.isIrreducible,
      OddOrder.RepresentationTheory.irr_cf_inner χA.isIrreducible.conj
        χC.isIrreducible.conj,
      if_pos hAC, if_neg hACc, if_neg hAcC, if_pos hAcCc] at h0
    rcases hεA with h1 | h1 <;> rcases hεC with h2 | h2 <;>
      rw [h1, h2] at h0 <;> norm_num at h0
  · -- distinct constituents: the lead inner product vanishes
    rw [hAeq, hCeq, ClassFunction.inner_smul_left,
      OddOrder.RepresentationTheory.inner_smul_right,
      OddOrder.RepresentationTheory.irr_cf_inner χA.isIrreducible χC.isIrreducible,
      if_neg hAC, star_intCast]
    ring

end OddOrder.Peterfalvi.S15
