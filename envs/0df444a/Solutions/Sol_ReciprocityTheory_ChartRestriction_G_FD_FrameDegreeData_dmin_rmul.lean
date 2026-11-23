-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.dmin_rmul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:44:52.08784+00:00
-- url     : https://prove2.me/submissions/6b931ccd-98d1-49bd-a8a3-ac70e04c560e

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_ProdCastLESucc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_MajPos
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FlowMatMulVec
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_OrthonormalFlagTranslateHolds
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_FrameDegreeData_upper_of_bor
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace ReciprocityTheory.ChartRestriction.G.FD
open NumberField Complex Matrix
open scoped ComplexConjugate
variable {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
namespace FrameDegreeData
noncomputable section
variable {r : ℕ} (X : Data E r)
private theorem sum_eq_sum_castLE_of_eq_zero {n m : ℕ} (h : m ≤ n) (f : Fin n → ℂ)
    (hf : ∀ j : Fin n, m ≤ j.val → f j = 0) :
    ∑ j, f j = ∑ j : Fin m, f (Fin.castLE h j) := by
  refine Eq.trans ?_ (Finset.sum_map (Finset.univ : Finset (Fin m)) ⟨Fin.castLE h, Fin.castLE_injective h⟩ f)
  refine (Finset.sum_subset (Finset.subset_univ _) fun j _ hj => hf j ?_).symm
  by_contra hlt
  push_neg at hlt
  exact hj (Finset.mem_map.2 ⟨⟨j.val, hlt⟩, Finset.mem_univ _, Fin.ext rfl⟩)
private theorem gram_eq_lemma {r : ℕ} (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E)
    (M : Matrix (Fin r) (Fin r) ℂ) :
    gram τ G M = Mᵀ * G.map τ * M.map (starRingEnd ℂ) := by
  ext a c
  simp only [gram, Matrix.of_apply, hermC, col, Matrix.mul_apply, Matrix.transpose_apply,
    Matrix.map_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
end
end FrameDegreeData
end ReciprocityTheory.ChartRestriction.G.FD
end

set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open NumberField Complex Matrix
open scoped ComplexConjugate
variable {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
open ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData
noncomputable section
variable {r : ℕ} (X : Data E r)
namespace ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData
theorem _root_.solution (x : Frame X.Ψ r) {b : Frame X.Ψ r} (hb : b ∈ Bor X.Ψ r) (τ : X.Ψ) (i : Fin (r + 1)) :
    dmin X.Gm (rmul x b) τ i =
      (∏ j : Fin i, mat b τ (Fin.castLE (Nat.le_of_lt_succ i.isLt) j) (Fin.castLE (Nat.le_of_lt_succ i.isLt) j)) *
        dmin X.Gm x τ i *
        conj (∏ j : Fin i, mat b τ (Fin.castLE (Nat.le_of_lt_succ i.isLt) j) (Fin.castLE (Nat.le_of_lt_succ i.isLt) j)) := by
  have hB := upper_of_bor X hb τ
  have hmat : mat (rmul x b) τ = mat x τ * mat b τ := rfl
  unfold dmin lminor
  rw [hmat, gram_eq_lemma, gram_eq_lemma τ.1 X.Gm (mat x τ), Matrix.transpose_mul, Matrix.map_mul]
  have hre : (mat b τ)ᵀ * (mat x τ)ᵀ * X.Gm.map τ.1 *
      ((mat x τ).map (starRingEnd ℂ) * (mat b τ).map (starRingEnd ℂ)) =
      (mat b τ)ᵀ * ((mat x τ)ᵀ * X.Gm.map τ.1 * (mat x τ).map (starRingEnd ℂ)) *
        (mat b τ).map (starRingEnd ℂ) := by
    simp only [Matrix.mul_assoc]
  rw [hre]
  set A := (mat x τ)ᵀ * X.Gm.map τ.1 * (mat x τ).map (starRingEnd ℂ) with hA
  set B := mat b τ with hBdef
  set e : Fin i → Fin r := Fin.castLE (Nat.le_of_lt_succ i.isLt) with he
  have hlt : ∀ (a : Fin i) (j : Fin r), (i : ℕ) ≤ j.val → e a < j := by
    intro a j hj
    rw [Fin.lt_iff_val_lt_val, he, Fin.coe_castLE]
    have := a.isLt
    omega
  have hsub : (Bᵀ * A * B.map (starRingEnd ℂ)).submatrix e e =
      (B.submatrix e e)ᵀ * A.submatrix e e * (B.submatrix e e).map (starRingEnd ℂ) := by
    ext a c
    simp only [Matrix.submatrix_apply, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply]
    rw [sum_eq_sum_castLE_of_eq_zero (Nat.le_of_lt_succ i.isLt) _ (fun k hk => by
      have h0 : B k (e c) = 0 := hB (hlt c k hk)
      rw [h0, map_zero, mul_zero])]
    refine Finset.sum_congr rfl fun k _ => ?_
    congr 1
    exact sum_eq_sum_castLE_of_eq_zero (Nat.le_of_lt_succ i.isLt) _ (fun j hj => by
      have h0 : B j (e a) = 0 := hB (hlt a j hj)
      rw [h0, zero_mul])
  have hBe : (B.submatrix e e).BlockTriangular id := by
    intro j k hjk
    apply hB
    show e k < e j
    rw [Fin.lt_iff_val_lt_val, he, Fin.coe_castLE, Fin.coe_castLE]
    exact hjk
  rw [hsub, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose,
    show ((B.submatrix e e).map (starRingEnd ℂ)).det = starRingEnd ℂ (B.submatrix e e).det from
      (RingHom.map_det _ _).symm,
    Matrix.det_of_upperTriangular hBe]
  rfl
end ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData
