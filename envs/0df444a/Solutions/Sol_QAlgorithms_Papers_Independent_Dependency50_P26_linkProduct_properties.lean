-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Dependency50.P26.linkProduct_properties
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-20T00:46:56.205273+00:00
-- url     : https://prove2.me/submissions/6d82add0-2f12-4fd2-97e8-30506128c25e

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P26

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

open QAlgorithms

attribute [local instance] Classical.decEq Classical.propDecidable

open QAlgorithms QAlgorithms.Papers QAlgorithms.Papers.Independent QAlgorithms.Papers.Independent.Dependency50 QAlgorithms.Papers.Independent.Dependency50.P26

lemma g52a_partialLink_psd {X Y J : Type} [Fintype X] [Fintype Y] [Fintype J]
    (M : Matrix (X × J) (X × J) ℂ) (N : Matrix (Y × J) (Y × J) ℂ)
    (hM : M.PosSemidef) (hN : N.PosSemidef) : (partialLink M N).PosSemidef := by
  classical
  let f : (X × Y) × J → (X × J) × (Y × J) := fun p => ((p.1.1, p.2), (p.1.2, p.2))
  let K' := (Matrix.kronecker M N).submatrix f f
  have hK' : K'.PosSemidef := (hM.kronecker hN).submatrix f
  let V : Matrix ((X × Y) × J) (X × Y) ℂ := Matrix.of fun p a => if p.1 = a then 1 else 0
  have h1 : ∀ a q, (Vᴴ * K') a q = ∑ u, K' (a, u) q := by
    intro a q
    rw [Matrix.mul_apply, Fintype.sum_prod_type, Finset.sum_eq_single a]
    · simp [V]
    · intro a' _ ha'
      refine Finset.sum_eq_zero fun u _ => ?_
      simp [V, ha']
    · simp
  have h2 : ∀ (Z : Matrix (X × Y) ((X × Y) × J) ℂ) a b, (Z * V) a b = ∑ v, Z a (b, v) := by
    intro Z a b
    rw [Matrix.mul_apply, Fintype.sum_prod_type, Finset.sum_eq_single b]
    · simp [V]
    · intro a' _ ha'
      refine Finset.sum_eq_zero fun u _ => ?_
      simp [V, ha']
    · simp
  have e : partialLink M N = Vᴴ * K' * V := by
    ext a b
    rw [h2]
    simp only [h1]
    rw [Finset.sum_comm]
    rfl
  rw [e]
  exact hK'.conjTranspose_mul_mul_same V

/-- PDF pp.3–4, Theorem 2, all four clauses. Swap conjugation is expressed by the
basis swap; associativity groups the six disjoint Venn regions and therefore encodes
exactly the empty triple-intersection hypothesis. No network admissibility assumption
is imposed on these algebraic operators. -/
theorem solution :
    (∀ (X Y J : Type) [Fintype X] [Fintype Y] [Fintype J]
        [Nonempty X] [Nonempty Y] [Nonempty J]
        (M : Matrix (X × J) (X × J) ℂ) (N : Matrix (Y × J) (Y × J) ℂ),
      partialLink M N = regroup Prod.swap (partialLink N M) ∧
      (M.IsHermitian → N.IsHermitian → (partialLink M N).IsHermitian) ∧
      (M.PosSemidef → N.PosSemidef → (partialLink M N).PosSemidef)) ∧
    (∀ (A B C AB AC BC : Type)
        [Fintype A] [Fintype B] [Fintype C] [Fintype AB] [Fintype AC] [Fintype BC]
        [Nonempty A] [Nonempty B] [Nonempty C]
        [Nonempty AB] [Nonempty AC] [Nonempty BC]
        (M1 : Matrix (A × (AB × AC)) (A × (AB × AC)) ℂ)
        (M2 : Matrix (B × (AB × BC)) (B × (AB × BC)) ℂ)
        (M3 : Matrix (C × (AC × BC)) (C × (AC × BC)) ℂ),
      linkRightNested M1 M2 M3 = linkLeftNested M1 M2 M3) := by
  refine ⟨?_, ?_⟩
  · intro X Y J _ _ _ _ _ _ M N
    refine ⟨?_, ?_, g52a_partialLink_psd M N⟩
    · ext a b
      simp only [partialLink, regroup, Prod.fst_swap, Prod.snd_swap]
      refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => ?_
      ring
    · intro hM hN
      unfold Matrix.IsHermitian
      ext a b
      simp only [partialLink, Matrix.conjTranspose_apply, star_sum, star_mul']
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => ?_
      rw [← Matrix.conjTranspose_apply M, ← Matrix.conjTranspose_apply N, hM.eq, hN.eq]
  · intro A B C AB AC BC _ _ _ _ _ _ _ _ _ _ _ _ M1 M2 M3
    ext a b
    simp only [linkRightNested, linkLeftNested, partialLink, regroup, Fintype.sum_prod_type,
      Finset.mul_sum, Finset.sum_mul]
    simp only [mul_assoc]
    conv_lhs => rw [Finset.sum_comm]
    conv_lhs => enter [2, i0, 2, i1, 2, i2]; rw [Finset.sum_comm]
    conv_lhs => enter [2, i0, 2, i1]; rw [Finset.sum_comm]
    conv_lhs => enter [2, i0]; rw [Finset.sum_comm]
    conv_lhs => enter [2, i0, 2, i1, 2, i2]; rw [Finset.sum_comm]
    conv_lhs => enter [2, i0, 2, i1]; rw [Finset.sum_comm]
    conv_lhs => enter [2, i0, 2, i1, 2, i2, 2, i3]; rw [Finset.sum_comm]
    conv_lhs => enter [2, i0, 2, i1, 2, i2]; rw [Finset.sum_comm]


end

