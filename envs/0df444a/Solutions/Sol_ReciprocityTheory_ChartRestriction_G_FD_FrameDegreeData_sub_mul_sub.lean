-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.sub_mul_sub
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:48:56.627588+00:00
-- url     : https://prove2.me/submissions/e3e02c4f-cbd5-4363-bfdf-19126f5f1c43

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_IsotropicCoefficientSplitting
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_DetSubUpper

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData
open NumberField Complex Matrix
open scoped ComplexConjugate
noncomputable section
variable {n : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData
theorem _root_.solution {i : ℕ} (h : i ≤ n) (M N : Matrix (Fin n) (Fin n) ℂ)
    (hz : ∀ (a c : Fin i) (k : Fin n), i ≤ (k : ℕ) → M (Fin.castLE h a) k * N k (Fin.castLE h c) = 0) :
    (M * N).submatrix (Fin.castLE h) (Fin.castLE h) =
      M.submatrix (Fin.castLE h) (Fin.castLE h) * N.submatrix (Fin.castLE h) (Fin.castLE h) := by
  ext a c
  simp only [Matrix.submatrix_apply, Matrix.mul_apply]
  symm
  refine Fintype.sum_of_injective (Fin.castLE h) (Fin.castLE_injective h) _ _ (fun k hk => ?_) (fun k => rfl)
  apply hz a c k
  by_contra hlt
  exact hk ⟨⟨k, by omega⟩, Fin.ext rfl⟩
end ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData
