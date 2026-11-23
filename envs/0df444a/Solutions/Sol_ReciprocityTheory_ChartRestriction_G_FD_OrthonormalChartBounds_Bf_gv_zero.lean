-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.OrthonormalChartBounds.Bf_gv_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:17:52.977402+00:00
-- url     : https://prove2.me/submissions/c19e9773-785b-4d9c-8001-11f363324858

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_SignTypeCancelIdentity
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_BfSubRight
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace ReciprocityTheory.ChartRestriction.G.FD.OrthonormalChartBounds
open NumberField Complex Matrix ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData
open scoped ComplexConjugate
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
private lemma sum_eq_add_sum_castLE_of_vanish_above {n : ℕ} (k : Fin n) (f : Fin n → ℂ) (hf : ∀ j : Fin n, k < j → f j = 0) :
    ∑ j, f j = f k + ∑ c : Fin k, f (Fin.castLE k.isLt.le c) := by
  let e : Fin k ↪ Fin n := ⟨Fin.castLE k.isLt.le, Fin.castLE_injective _⟩
  have hk : k ∉ Finset.univ.map e := by
    intro h
    obtain ⟨c, _, hc⟩ := Finset.mem_map.mp h
    have h1 := congrArg Fin.val hc
    have h2 := c.isLt
    simp only [e, Function.Embedding.coeFn_mk, Fin.coe_castLE] at h1
    omega
  calc ∑ j, f j = ∑ j ∈ insert k (Finset.univ.map e), f j := by
        refine (Finset.sum_subset (Finset.subset_univ _) fun j _ hj => hf j ?_).symm
        by_contra hle
        push_neg at hle
        rcases lt_or_eq_of_le hle with hlt | heq
        · exact hj (Finset.mem_insert_of_mem
            (Finset.mem_map.mpr ⟨⟨(j : ℕ), hlt⟩, Finset.mem_univ _, Fin.ext rfl⟩))
        · exact hj (by rw [heq]; exact Finset.mem_insert_self _ _)
    _ = f k + ∑ j ∈ Finset.univ.map e, f j := Finset.sum_insert hk
    _ = f k + ∑ c, f (e c) := by rw [Finset.sum_map]
    _ = f k + ∑ c : Fin k, f (Fin.castLE k.isLt.le c) := rfl
end
end ReciprocityTheory.ChartRestriction.G.FD.OrthonormalChartBounds
end

set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.OrthonormalChartBounds
open NumberField Complex Matrix ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData
open scoped ComplexConjugate
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
namespace ReciprocityTheory.ChartRestriction.G.FD.OrthonormalChartBounds
theorem _root_.solution (Z : X.Coord) (τ : X.Ψ) (hdet : ∀ c : Fin r, (blk (Gp X Z τ) c).det ≠ 0) (k : Fin r)
    (t : Fin r → ℂ) (ht : ∀ b, k ≤ b → t b = 0) :
    Bf X Z τ (fun a => uMat (Gp X Z τ) a k) t = 0 := by
  have hB : IsUnit (blk (Gp X Z τ) k).det := isUnit_iff_ne_zero.mpr (hdet k)
  have hw : Matrix.vecMul (Matrix.vecMul (rowc (Gp X Z τ) k) (blk (Gp X Z τ) k)⁻¹)
      (blk (Gp X Z τ) k) = rowc (Gp X Z τ) k := by
    rw [Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul _ hB, Matrix.vecMul_one]
  show ∑ a, ∑ b, uMat (Gp X Z τ) a k * Gp X Z τ a b * conj (t b) = 0
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro b _
  by_cases hb : k ≤ b
  · simp [ht b hb]
  · push_neg at hb
    rw [← Finset.sum_mul]
    have hcol : ∑ c : Fin k, (Matrix.vecMul (rowc (Gp X Z τ) k) (blk (Gp X Z τ) k)⁻¹) c *
        Gp X Z τ (Fin.castLE k.isLt.le c) b = Gp X Z τ k b := congrFun hw ⟨(b : ℕ), hb⟩
    have hu : ∀ c : Fin k, uMat (Gp X Z τ) (Fin.castLE k.isLt.le c) k =
        -(Matrix.vecMul (rowc (Gp X Z τ) k) (blk (Gp X Z τ) k)⁻¹) c := by
      intro c
      have hne : Fin.castLE k.isLt.le c ≠ k := by
        intro h
        have h1 := congrArg Fin.val h
        have h2 := c.isLt
        simp only [Fin.coe_castLE] at h1
        omega
      have hlt : Fin.castLE k.isLt.le c < k := Fin.lt_iff_val_lt_val.mpr (by simp)
      simp only [uMat, Matrix.of_apply, if_neg hne, dif_pos hlt]
      try rfl
    have hsum : ∑ a, uMat (Gp X Z τ) a k * Gp X Z τ a b = 0 := by
      rw [sum_eq_add_sum_castLE_of_vanish_above k]
      · rw [show uMat (Gp X Z τ) k k = 1 by simp [uMat]]
        simp only [hu, neg_mul, Finset.sum_neg_distrib]
        rw [hcol]
        ring
      · intro j hj
        simp only [uMat, Matrix.of_apply, if_neg (ne_of_gt hj), dif_neg (not_lt.mpr hj.le), zero_mul]
    rw [hsum, zero_mul]
end ReciprocityTheory.ChartRestriction.G.FD.OrthonormalChartBounds
