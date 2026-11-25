-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.relIndex_ne_zero_of_mul_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T15:05:49.815202+00:00
-- url     : https://prove2.me/submissions/2e0dd4a5-6232-4339-9342-1c57e844ed2a

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_ExistsMPrimeFiltration
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_ABridgeSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_ChooseLePowDivFactorial
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_RelIndexNeZeroOfMulMem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial Module
variable {Ω : Type} [Field Ω] [CharZero Ω]
namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
theorem _root_.solution {H K : Submodule ℤ Ω} (hK : K.FG) {M : ℕ} (hM0 : 0 < M)
    (hM : ∀ u ∈ K, (M : Ω) * u ∈ H) : H.toAddSubgroup.relIndex K.toAddSubgroup ≠ 0 := by
  have hfg : AddGroup.FG K.toAddSubgroup :=
    (AddGroup.fg_iff_addSubgroup_fg _).mpr ((Submodule.fg_iff_addSubgroup_fg K).mp hK)
  have htor : IsAddTorsion (K.toAddSubgroup ⧸ H.toAddSubgroup.addSubgroupOf K.toAddSubgroup) := by
    intro q
    refine QuotientAddGroup.induction_on q fun u => ?_
    refine isOfFinAddOrder_iff_nsmul_eq_zero.mpr ⟨M, hM0, ?_⟩
    rw [← QuotientAddGroup.mk_nsmul, QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf]
    simpa [nsmul_eq_mul] using hM u u.2
  have := AddCommGroup.finite_of_fg_isAddTorsion _ htor
  exact AddSubgroup.index_ne_zero_of_finite
end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
