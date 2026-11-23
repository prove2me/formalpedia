-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.PositiveSpanMatrices.sum_split
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:53:40.708725+00:00
-- url     : https://prove2.me/submissions/f096a539-30ff-47c0-8c7b-ca0243a730cc

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_ExistsUnitaryBasisSameFlag
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_UnitaryComplementMoveOfIsotropic
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_LminorSubmatrixCastSucc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_PositiveSpanMatrices

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.PositiveSpanMatrices
open NumberField Complex Matrix ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexConjugate
noncomputable section
namespace ReciprocityTheory.ChartRestriction.G.FD.PositiveSpanMatrices
theorem _root_.solution {M : Type*} [AddCommMonoid M] {n p : ℕ} (hp : p ≤ n) (F : Fin n → M) :
    ∑ c : Fin n, F c = ∑ b : Fin p, F (Fin.castLE hp b) + ∑ a : Fin (n - p), F (kap hp a) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hp
  have hm : p + m - p = m := by omega
  rw [Fin.sum_univ_add]
  refine congrArg₂ (· + ·) (Finset.sum_congr rfl (fun b _ => congrArg F (Fin.ext rfl))) ?_
  refine Fintype.sum_equiv (finCongr hm.symm) _ _ (fun i => ?_)
  exact congrArg F (Fin.ext (by simp [kap]))
end ReciprocityTheory.ChartRestriction.G.FD.PositiveSpanMatrices
