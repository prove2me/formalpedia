-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Sh.ptNs_lin
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T13:48:07.829719+00:00
-- url     : https://prove2.me/submissions/b47959ce-58de-41fe-acc6-6d478c667f5a

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_VEqZeroOfPowEqOne
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_WeightedSumBounds_PtSolveMapFixedIff
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_WeightedSumBounds_NsmulCoprimeBijectiveCurves
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Sh_ptNs_const
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Sh_ptNs_hasSubst
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Sh_pt_F_lin
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Sh_pt_coeff_single_X
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Sh_pt_coeff_single_subst


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Sh
open MvPowerSeries ReciprocityTheory.PGsh
open Classical
noncomputable section
variable {C : Type} [Field C] {v : AddValuation C (WithTop ℝ)} {d : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.Sh
theorem _root_.solution (G : LogFGL v d) : ∀ (n : ℕ) (a s : Fin d),
    coeff (Finsupp.single s 1) (ptNs G n a) = if s = a then (n : C) else 0
  | 0, a, s => by simp [ptNs]
  | n + 1, a, s => by
    have h0 : ∀ i, constantCoeff (Sum.elim (fun b => (X b : MvPowerSeries (Fin d) C))
        (ptNs G n) i) = 0 := by
      rintro (i | i)
      · simp
      · exact ptNs_const G n i
    show coeff (Finsupp.single s 1) (subst _ (G.F a)) = _
    rw [pt_coeff_single_subst (ptNs_hasSubst G n) h0 (G.F_const a) s, Fintype.sum_sum_type]
    simp only [pt_F_lin, Sum.elim_inl, Sum.elim_inr, pt_coeff_single_X, solution G n,
      Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq, if_false, add_zero, zero_add,
      ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    split_ifs <;> push_cast <;> ring
end ReciprocityTheory.ChartRestriction.G.Sh
