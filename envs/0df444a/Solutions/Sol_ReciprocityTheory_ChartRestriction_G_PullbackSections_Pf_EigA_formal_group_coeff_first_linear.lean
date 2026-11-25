-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.EigA.formal_group_coeff_first_linear
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:40:51.188138+00:00
-- url     : https://prove2.me/submissions/6e245718-6a3a-4e20-b985-218d1448dc20

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_HStable
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_EigenLift
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_ActLin
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_DofComm
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_FormalGroupCoeffSecondLinear
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_Pf_EigA_coeff_lin_ev
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_Pf_EigA_coeff_X_single
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_Pf_EigA_formal_group_coeff_second_linear
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_CZ_pt


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.PullbackSections ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.EigA
variable {R : Type} [CommRing R] {d : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.EigA
theorem _root_.solution (G : FGLaw R d) (i l : Fin d) :
    coeff (Finsupp.single ((0 : Fin 2), l) 1) (G.F i) = if l = i then 1 else 0 := by
  classical
  have e := congrArg (coeff (Finsupp.single ((0 : Fin 2), l) 1)) (G.comm i)
  rw [coeff_lin_ev _ (by
      intro j i'
      fin_cases j <;> simp [pt])] at e
  rw [Fintype.sum_prod_type, Fin.sum_univ_two] at e
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, pt, coeff_X_single] at e
  simp only [Prod.mk.injEq, Fin.zero_eq_one_iff, Fin.one_eq_zero_iff, false_and, if_false, mul_zero,
    Finset.sum_const_zero, zero_add, true_and, mul_ite, mul_one, Finset.sum_ite_eq, Finset.mem_univ, if_true,
    OfNat.ofNat_ne_one, one_ne_zero, zero_ne_one] at e
  rw [← e, formal_group_coeff_second_linear]
end ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.EigA
