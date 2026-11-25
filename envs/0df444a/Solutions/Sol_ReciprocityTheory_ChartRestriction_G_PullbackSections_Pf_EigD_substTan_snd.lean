-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.EigD.substTan_snd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T14:26:10.145587+00:00
-- url     : https://prove2.me/submissions/d1560fb2-5694-4b68-b456-ffa7f58467f9

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_SingleMemDegLE
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_SubstTanSnd
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_Pf_EigD_jetTan_mk
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_Pf_EigD_aeval_tan
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_Pf_EigD_coeff_psTrunc
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_Pf_EigD_single_mem_degLE


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
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.PullbackSections ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.EigD
open MvPolynomial CategoryTheory Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G
attribute [local instance] Over.cartesianMonoidalCategory
variable {V : Type} [CommRing V] {d : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.EigD
theorem _root_.solution (f : Fin d → MvPowerSeries (Fin 1 × Fin d) V) (j m : Fin d) :
    ((jetTan (R := V) (m := 0) ((0 : Fin 1), j)).comp
      (jetSubstP 1 fun p : Fin 1 × Fin d => psTrunc 1 (f p.2)) (zk m)).snd =
      MvPowerSeries.coeff (Finsupp.single ((0 : Fin 1), j) 1) (f m) := by
  rw [AlgHom.comp_apply]
  show (jetTan (R := V) (m := 0) ((0 : Fin 1), j) (Ideal.Quotient.mk _ (aeval _ (X ((0 : Fin 1), m))))).snd = _
  rw [aeval_X, jetTan_mk, aeval_tan]
  have hne : Finsupp.single ((0 : Fin 1), j) 1 ≠ 0 := Finsupp.single_ne_zero.2 one_ne_zero
  simp [MvPolynomial.coeff_C, hne.symm, coeff_psTrunc 1 _ _ (single_mem_degLE _)]
end ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.EigD
