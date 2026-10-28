-- Prove2me | solution 1 for WernerExt.TwoSided.flip_generators
-- status  : ACCEPTED   (prove)
-- author  : @frknbls
-- created : 2026-10-27T18:23:22.732985+00:00
-- url     : https://prove2.me/submissions/43638c11-a770-4b03-bb1b-19315ae7b646

import Definitions.Def_WernerExt_TwoSided_Model

namespace WernerExt.TwoSided
open Matrix
open scoped Kronecker ComplexOrder

theorem gen_apply (d : ℕ) (a b u u' : Fin d) :
    gen d a b u u' = (if u = b ∧ u' = a then 1 else 0) - (if a = b ∧ u = u' then (d : ℂ)⁻¹ else 0) := by
  simp only [gen, Matrix.sub_apply, Matrix.smul_apply, Matrix.single_apply, Matrix.one_apply,
    smul_eq_mul]
  congr 1
  · by_cases h1 : u = b <;> by_cases h2 : u' = a <;> simp [h1, h2] <;> aesop
  · by_cases h1 : a = b <;> by_cases h2 : u = u' <;> simp [h1, h2]

theorem gen_key (d : ℕ) (hd : 2 ≤ d) (u u' v v' : Fin d) :
    ∑ a : Fin d, ∑ b : Fin d, gen d a b u u' * gen d b a v v' =
      (if u = v' ∧ v = u' then 1 else 0) - (if u = u' ∧ v = v' then (d : ℂ)⁻¹ else 0) := by
  have hd0 : (d : ℂ) ≠ 0 := by exact_mod_cast (show d ≠ 0 by omega)
  simp only [gen_apply]
  simp only [sub_mul, mul_sub, Finset.sum_sub_distrib]
  simp only [ite_mul, mul_ite, one_mul, mul_one, zero_mul, mul_zero]
  simp only [ite_and]
  simp [Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.sum_ite_irrel]
  by_cases h1 : u = v' <;> by_cases h2 : u' = v <;> by_cases h3 : v = v' <;>
    by_cases h4 : u = u' <;> simp [h1, h2, h3, h4, eq_comm] <;> field_simp <;> ring_nf <;> simp_all

theorem agree_iff {d n : ℕ} (i : Fin n) (x x' : Fin n → Fin d) (c : Fin d) :
    ((∀ k, k ≠ i → x k = x' k) ∧ x i = c) ↔ x = Function.update x' i c := by
  constructor
  · rintro ⟨h1, h2⟩
    funext k
    by_cases hk : k = i
    · subst hk; simp [h2]
    · simp [hk, h1 k hk]
  · rintro rfl
    exact ⟨fun k hk => by simp [hk], by simp⟩

theorem flip_generators (d : ℕ) (hd : 2 ≤ d) :
    flip d = ∑ a : Fin d, ∑ b : Fin d, (gen d a b ⊗ₖ gen d b a) +
        ((d : ℂ)⁻¹) • (1 : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) ∧
      ∀ (nA nB : ℕ) (i : Fin nA) (j : Fin nB),
        flipAB (d := d) i j =
          ∑ a : Fin d, ∑ b : Fin d,
            (siteOp i (gen d a b) ⊗ₖ (1 : Matrix (Fin nB → Fin d) (Fin nB → Fin d) ℂ)) *
              ((1 : Matrix (Fin nA → Fin d) (Fin nA → Fin d) ℂ) ⊗ₖ siteOp j (gen d b a)) +
          ((d : ℂ)⁻¹) • (1 : Matrix (Cfg d nA nB) (Cfg d nA nB) ℂ) := by
  constructor
  · ext ⟨x1, x2⟩ ⟨y1, y2⟩
    simp only [Matrix.add_apply, Matrix.sum_apply, kroneckerMap_apply, Matrix.smul_apply,
      Matrix.one_apply, smul_eq_mul]
    rw [gen_key d hd]
    simp only [flip, Matrix.of_apply, Prod.mk.injEq]
    by_cases h1 : x1 = y1 <;> by_cases h2 : x2 = y2 <;> simp [h1, h2]
  · intro nA nB i j
    ext ⟨x, y⟩ ⟨x', y'⟩
    have hmul : ∀ a b, (siteOp i (gen d a b) ⊗ₖ (1 : Matrix (Fin nB → Fin d) (Fin nB → Fin d) ℂ)) *
        ((1 : Matrix (Fin nA → Fin d) (Fin nA → Fin d) ℂ) ⊗ₖ siteOp j (gen d b a)) =
        siteOp i (gen d a b) ⊗ₖ siteOp j (gen d b a) := by
      intro a b
      rw [← Matrix.mul_kronecker_mul, Matrix.mul_one, Matrix.one_mul]
    simp only [hmul]
    simp only [Matrix.add_apply, Matrix.sum_apply, kroneckerMap_apply, Matrix.smul_apply,
      Matrix.one_apply, smul_eq_mul, siteOp, Matrix.of_apply]
    have hsum : ∑ a : Fin d, ∑ b : Fin d,
        gen d a b (x i) (x' i) * (if ∀ k, k ≠ i → x k = x' k then (1 : ℂ) else 0) *
          (gen d b a (y j) (y' j) * (if ∀ k, k ≠ j → y k = y' k then 1 else 0)) =
        (∑ a : Fin d, ∑ b : Fin d, gen d a b (x i) (x' i) * gen d b a (y j) (y' j)) *
          ((if ∀ k, k ≠ i → x k = x' k then (1 : ℂ) else 0) *
            (if ∀ k, k ≠ j → y k = y' k then 1 else 0)) := by
      rw [Finset.sum_mul]; congr 1; ext a; rw [Finset.sum_mul]; congr 1; ext b; ring
    rw [hsum, gen_key d hd]
    simp only [flipAB, swapCfg, Matrix.of_apply, Prod.mk.injEq]
    have e1 := agree_iff i x x' (y' j)
    have e2 := agree_iff j y y' (x' i)
    have e3 := agree_iff i x x' (x' i)
    have e4 := agree_iff j y y' (y' j)
    simp only [Function.update_eq_self] at e3 e4
    by_cases hx : ∀ k, k ≠ i → x k = x' k <;> by_cases hy : ∀ k, k ≠ j → y k = y' k
    · have f1 : x = Function.update x' i (y' j) ↔ x i = y' j := ⟨fun h => (e1.mpr h).2, fun h => e1.mp ⟨hx, h⟩⟩
      have f2 : y = Function.update y' j (x' i) ↔ y j = x' i := ⟨fun h => (e2.mpr h).2, fun h => e2.mp ⟨hy, h⟩⟩
      have f3 : x = x' ↔ x i = x' i := ⟨fun h => (e3.mpr h).2, fun h => e3.mp ⟨hx, h⟩⟩
      have f4 : y = y' ↔ y j = y' j := ⟨fun h => (e4.mpr h).2, fun h => e4.mp ⟨hy, h⟩⟩
      simp only [f1, f2, f3, f4, if_pos hx, if_pos hy, mul_one]
      split_ifs <;> simp_all
    · have : ¬ y = Function.update y' j (x' i) := fun h => hy (e2.mpr h).1
      have : ¬ y = y' := fun h => hy (e4.mpr h).1
      simp_all
    · have : ¬ x = Function.update x' i (y' j) := fun h => hx (e1.mpr h).1
      have : ¬ x = x' := fun h => hx (e3.mpr h).1
      simp_all
    · have : ¬ x = Function.update x' i (y' j) := fun h => hx (e1.mpr h).1
      have : ¬ x = x' := fun h => hx (e3.mpr h).1
      simp_all

end WernerExt.TwoSided


-- Platform entry point: restates the target verbatim.
namespace WernerExt.TwoSided

open Matrix
open scoped Kronecker ComplexOrder

/-- SM Eq. (6), SM p. 1: the flip in terms of the `su(d)` generators,
`F_ij = ∑_{α,β} S^{αβ}_i S^{βα}_j + 𝟙/d`, (a) on two `d`-level sites and (b) for Alice's site
`i` and Bob's site `j` of the joint system. -/
theorem _root_.solution (d : ℕ) (hd : 2 ≤ d) :
    flip d = ∑ a : Fin d, ∑ b : Fin d, (gen d a b ⊗ₖ gen d b a) +
        ((d : ℂ)⁻¹) • (1 : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) ∧
      ∀ (nA nB : ℕ) (i : Fin nA) (j : Fin nB),
        flipAB (d := d) i j =
          ∑ a : Fin d, ∑ b : Fin d,
            (siteOp i (gen d a b) ⊗ₖ (1 : Matrix (Fin nB → Fin d) (Fin nB → Fin d) ℂ)) *
              ((1 : Matrix (Fin nA → Fin d) (Fin nA → Fin d) ℂ) ⊗ₖ siteOp j (gen d b a)) +
          ((d : ℂ)⁻¹) • (1 : Matrix (Cfg d nA nB) (Cfg d nA nB) ℂ) := by
  apply @WernerExt.TwoSided.flip_generators <;> assumption

end WernerExt.TwoSided
