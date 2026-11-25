-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Sh.pt_F_lin
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T13:41:20.067002+00:00
-- url     : https://prove2.me/submissions/0c8ca9a7-16f6-4712-8faf-fefe9cc25690

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_VEqZeroOfPowEqOne
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_WeightedSumBounds_PtOrderProdSub
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_WeightedSumBounds_PtCoeffSingleSubst
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Sh_pt_coeff_single_subst
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Sh_pt_coeff_single_X

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
theorem _root_.solution (G : LogFGL v d) (a : Fin d) (i : Fin d ⊕ Fin d) :
    coeff (Finsupp.single i 1) (G.F a) =
      (if i = Sum.inl a then 1 else 0) + (if i = Sum.inr a then 1 else 0) := by
  have hF : HasSubst G.F := by
    first
    | exact HasSubst.of_constantCoeff_zero G.F_const
    | exact hasSubst_of_constantCoeff_zero G.F_const
  have hX : ∀ e : Fin d → Fin d ⊕ Fin d,
      HasSubst (fun b => (X (e b) : MvPowerSeries (Fin d ⊕ Fin d) C)) := by
    intro e
    first
    | exact HasSubst.of_constantCoeff_zero fun b => constantCoeff_X _
    | exact hasSubst_of_constantCoeff_zero fun b => constantCoeff_X _
  have key := congrArg (coeff (Finsupp.single i 1)) (G.lg_F a)
  rw [map_add, pt_coeff_single_subst hF G.F_const (G.lg_const a),
    pt_coeff_single_subst (hX Sum.inl) (fun b => constantCoeff_X _) (G.lg_const a),
    pt_coeff_single_subst (hX Sum.inr) (fun b => constantCoeff_X _) (G.lg_const a)] at key
  simp only [G.lg_lin, pt_coeff_single_X, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq,
    Finset.sum_ite_eq', Finset.mem_univ, if_true] at key
  convert key
end ReciprocityTheory.ChartRestriction.G.Sh
