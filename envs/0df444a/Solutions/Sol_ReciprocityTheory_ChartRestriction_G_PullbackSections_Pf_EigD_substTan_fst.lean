-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.EigD.substTan_fst
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T14:36:22.122085+00:00
-- url     : https://prove2.me/submissions/59ad1ac3-e53b-4dcb-858c-fe277e332757

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_SingleMemDegLE
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_SubstTanSnd
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_Pf_EigD_fst_jetTan
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_Pf_EigD_jetAug_mk

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
theorem _root_.solution (f : Fin d → MvPowerSeries (Fin 1 × Fin d) V) (j : Fin d) (w : Jet V (Fin 1 × Fin d) 1) :
    ((jetTan (R := V) (m := 0) ((0 : Fin 1), j)).comp
      (jetSubstP 1 fun p : Fin 1 × Fin d => psTrunc 1 (f p.2)) w).fst = jetAug w := by
  rw [AlgHom.comp_apply, fst_jetTan]
  obtain ⟨q, rfl⟩ := Ideal.Quotient.mk_surjective w
  have h : (jetAug : Jet V (Fin 1 × Fin d) 1 →ₐ[V] V).comp
      (jetSubstP 1 fun p : Fin 1 × Fin d => psTrunc 1 (f p.2)) = jetAug := by
    apply Ideal.Quotient.algHom_ext
    apply MvPolynomial.algHom_ext
    intro i
    simp only [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk]
    show jetAug (Ideal.Quotient.mk _ (aeval _ (X i))) = _
    rw [aeval_X, jetAug_mk, jetAug_mk]
    simp
  exact (AlgHom.comp_apply _ _ _).symm.trans (DFunLike.congr_fun h _)
end ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.EigD
