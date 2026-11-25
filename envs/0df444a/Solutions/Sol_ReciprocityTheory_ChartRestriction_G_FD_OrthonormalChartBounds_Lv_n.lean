-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.OrthonormalChartBounds.Lv_n
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:57:57.406848+00:00
-- url     : https://prove2.me/submissions/e72ec88f-86b1-46ed-beb5-2d15d72eeaba

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
private lemma sum_eq_sum_castLE_p0_of_vanish_above (f : Fin r → ℂ) (hf : ∀ j : Fin r, X.p0 ≤ (j : ℕ) → f j = 0) :
    ∑ j, f j = ∑ c : Fin X.p0, f (Fin.castLE X.p0_le c) := by
  let e : Fin X.p0 ↪ Fin r := ⟨Fin.castLE X.p0_le, Fin.castLE_injective X.p0_le⟩
  calc ∑ j, f j = ∑ j ∈ Finset.univ.map e, f j := by
        refine (Finset.sum_subset (Finset.subset_univ _) fun j _ hj => hf j ?_).symm
        by_contra hlt
        exact hj (Finset.mem_map.mpr ⟨⟨j, by omega⟩, Finset.mem_univ _, Fin.ext rfl⟩)
    _ = ∑ c, f (e c) := Finset.sum_map _ _ _
    _ = ∑ c : Fin X.p0, f (Fin.castLE X.p0_le c) := rfl
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
theorem _root_.solution (Z : X.Coord) (τ : X.Ψ) (v : Fin r → ℂ) (m : Fin (r - X.p0)) :
    ∑ j, X.lowBlock Z τ (nI X m) j * v j = Nv X Z τ v m := by
  have hL : ∀ j : Fin r, X.lowBlock Z τ (nI X m) j =
      (if nI X m = j then 1 else 0) + (if h : (j : ℕ) < X.p0 then Z τ m ⟨j, h⟩ else 0) := by
    intro j
    simp only [Data.lowBlock, Matrix.of_apply]
    congr 1
    by_cases h : (j : ℕ) < X.p0
    · rw [dif_pos ⟨(by simp [nI] : X.p0 ≤ ((nI X m : Fin r) : ℕ)), h⟩, dif_pos h]
      exact congrFun (congrArg (Z τ) (Fin.ext (by simp [nI]))) _
    · rw [dif_neg (fun hh => h hh.2), dif_neg h]
  simp only [hL, add_mul, Finset.sum_add_distrib, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq,
    Finset.mem_univ, if_true]
  simp only [Nv]
  congr 1
  rw [sum_eq_sum_castLE_p0_of_vanish_above X]
  · refine Finset.sum_congr rfl fun c _ => ?_
    rw [dif_pos (by simp)]
    first | rfl | (congr 2) | simp
  · intro j hj
    rw [dif_neg (not_lt.mpr hj), zero_mul]
end ReciprocityTheory.ChartRestriction.G.FD.OrthonormalChartBounds
