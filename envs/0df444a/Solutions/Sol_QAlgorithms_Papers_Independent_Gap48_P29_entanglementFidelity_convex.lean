-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Gap48.P29.entanglementFidelity_convex
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T20:42:11.706187+00:00
-- url     : https://prove2.me/submissions/056e75c2-5d06-48ff-b1a2-1a8c4239d121

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P29

noncomputable section

namespace QAlgorithms.Papers.Independent.Gap48.P29

open QAlgorithms Filter
open scoped Matrix ComplexConjugate ComplexOrder Topology

/-- complex sesquilinear form underlying `fe` -/
def X7U_B {I : Type*} [Fintype I] [DecidableEq I]
    (X : Matrix I I ℂ) (A : Superop I I) : ℂ :=
  ∑ i, ∑ j, ∑ k, ∑ l, X j i * conj (X l k) * A (Matrix.single j l 1) i k

lemma X7U_fe_eq {I : Type*} [Fintype I] [DecidableEq I]
    (X : Matrix I I ℂ) (A : Superop I I) : fe X A = (X7U_B X A).re := rfl

lemma X7U_B_nonneg {I : Type*} [Fintype I] [DecidableEq I]
    (D : Matrix I I ℂ) (A : Superop I I) (hA : FiniteCPMap A) : 0 ≤ (X7U_B D A).re := by
  obtain ⟨L, hL, hCP⟩ := hA
  set r := Fintype.card I
  let e : I ≃ Fin r := Fintype.equivFin I
  let v : Fin r × I → ℂ := fun p => if p.1 = e p.2 then 1 else 0
  have hX : (Matrix.vecMulVec v (star v)).PosSemidef := Matrix.posSemidef_vecMulVec_self_star v
  have hM := hCP r _ hX
  let w : Fin r × I → ℂ := fun p => star (D (e.symm p.1) p.2)
  have h := hM.dotProduct_mulVec_nonneg w
  have hblock : ∀ a b : Fin r, (Matrix.of fun i i' =>
      Matrix.vecMulVec v (star v) (a, i) (b, i')) = Matrix.single (e.symm a) (e.symm b) 1 := by
    intro a b
    ext i i'
    simp only [Matrix.of_apply, Matrix.vecMulVec_apply, v, Pi.star_apply, Matrix.single_apply,
      Equiv.symm_apply_eq]
    split_ifs <;> simp_all
  have key : star w ⬝ᵥ ((QAlgorithms.idTensorSuperop L (Matrix.vecMulVec v (star v))) *ᵥ w)
      = X7U_B D A := by
    simp only [dotProduct, Matrix.mulVec, QAlgorithms.idTensorSuperop, Matrix.of_apply, hblock,
      hL, w, Pi.star_apply, star_star, Fintype.sum_prod_type, Finset.mul_sum]
    have hs : ∀ f : I → ℂ, ∑ a : Fin r, f (e.symm a) = ∑ j, f j := fun f => e.symm.sum_comp f
    rw [hs (fun j => ∑ x_1, ∑ x_2 : Fin r, ∑ x_3,
      D j x_1 * (A (Matrix.single j (e.symm x_2) 1) x_1 x_3 * star (D (e.symm x_2) x_3)))]
    unfold X7U_B
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hs (fun l => D j i * (A (Matrix.single j l 1) i k * star (D l k)))]
    refine Finset.sum_congr rfl fun l _ => ?_
    simp only [Equiv.symm_apply_apply, RCLike.star_def]
    ring
  rw [key] at h
  exact (Complex.nonneg_iff.1 h).1

lemma X7U_fe_nonneg {I : Type*} [Fintype I] [DecidableEq I]
    (D : Matrix I I ℂ) (A : Superop I I) (hA : FiniteCPMap A) : 0 ≤ fe D A :=
  X7U_B_nonneg D A hA

lemma X7U_B_convex_identity {I : Type*} [Fintype I] [DecidableEq I]
    (x y : Matrix I I ℂ) (A : Superop I I) (lam : ℝ) :
    (lam : ℂ) * X7U_B x A + ((1 - lam : ℝ) : ℂ) * X7U_B y A
      - X7U_B ((lam : ℂ) • x + ((1 - lam : ℝ) : ℂ) • y) A
      = ((lam * (1 - lam) : ℝ) : ℂ) * X7U_B (x - y) A := by
  unfold X7U_B
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  refine Finset.sum_congr rfl fun j _ => ?_
  refine Finset.sum_congr rfl fun k _ => ?_
  refine Finset.sum_congr rfl fun l _ => ?_
  simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul, map_add,
    map_mul, map_sub, Complex.conj_ofReal]
  push_cast
  ring

end QAlgorithms.Papers.Independent.Gap48.P29

end

noncomputable section

open QAlgorithms Filter
open scoped Matrix ComplexConjugate ComplexOrder Topology
open QAlgorithms.Papers.Independent.Information100.P07 (IsProjection)
open QAlgorithms.Papers.Independent.Information100.P67 (squaredFidelity)

open QAlgorithms.Papers.Independent.Gap48.P29 in
theorem solution {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]
    (rho sigma : Matrix I I ℂ) (hrho : IsDensityMatrix rho) (hsigma : IsDensityMatrix sigma)
    (E : Superop I I) (hE : TraceNonincreasingCPMap E) (lam : ℝ) (hlam0 : 0 ≤ lam) (hlam1 : lam ≤ 1) :
    fe ((lam : ℂ) • rho + ((1 - lam : ℝ) : ℂ) • sigma) E ≤
      lam * fe rho E + (1 - lam) * fe sigma E := by
  have hid := congrArg Complex.re (X7U_B_convex_identity rho sigma E lam)
  have hnn := X7U_B_nonneg (rho - sigma) E hE.1
  simp only [Complex.sub_re, Complex.add_re, Complex.re_ofReal_mul] at hid
  rw [X7U_fe_eq, X7U_fe_eq, X7U_fe_eq]
  have : 0 ≤ lam * (1 - lam) * (X7U_B (rho - sigma) E).re :=
    mul_nonneg (mul_nonneg hlam0 (by linarith)) hnn
  linarith

end
