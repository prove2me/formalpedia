-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.prod_castLE_succ
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:36:38.642795+00:00
-- url     : https://prove2.me/submissions/ab95c763-3a24-4750-93fd-139bb22045c3

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_UMatUpper
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_LminorSubmatrixCastSucc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_ProdCastLESucc

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData
open NumberField Complex Matrix ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexConjugate
noncomputable section
variable {n : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData
theorem _root_.solution {k : ℕ} (h : k + 1 ≤ n) (f : Fin n → ℂ) :
    ∏ j : Fin (k + 1), f (Fin.castLE h j) = (∏ j : Fin k, f (Fin.castLE (Nat.le_of_succ_le h) j)) * f ⟨k, h⟩ := by
  rw [Fin.prod_univ_castSucc]
  rfl
end ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData
