-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Sh.ptAdd_lin
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T13:48:29.07672+00:00
-- url     : https://prove2.me/submissions/754b4da2-769d-4a74-9fdf-634e3d67dce9

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_VEqZeroOfPowEqOne
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_WeightedSumBounds_PtSolveMapFixedIff
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_WeightedSumBounds_PtRescaleGood
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Sh_ptc_elim_const
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Sh_pt_F_lin
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
theorem _root_.solution (G : LogFGL v d) {τ : Type*} {x y : Fin d → MvPowerSeries τ C}
    (hx : ∀ a, constantCoeff (x a) = 0) (hy : ∀ a, constantCoeff (y a) = 0) (a : Fin d)
    (t : τ) :
    coeff (Finsupp.single t 1) (ptAdd G x y a) =
      coeff (Finsupp.single t 1) (x a) + coeff (Finsupp.single t 1) (y a) := by
  have h0 := ptc_elim_const hx hy
  have hs : HasSubst (Sum.elim x y) := hasSubst_of_constantCoeff_zero h0
  show coeff (Finsupp.single t 1) (subst (Sum.elim x y) (G.F a)) = _
  rw [pt_coeff_single_subst hs h0 (G.F_const a) t, Fintype.sum_sum_type]
  simp only [pt_F_lin, Sum.elim_inl, Sum.elim_inr, Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq,
    if_false, add_zero, zero_add, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq',
    Finset.mem_univ, if_true]
end ReciprocityTheory.ChartRestriction.G.Sh
