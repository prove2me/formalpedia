-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.TB.SCPf.nabla_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T13:53:00.471649+00:00
-- url     : https://prove2.me/submissions/c5b35975-110b-477e-b61a-58b53ddaaf5d

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_GermSC
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_DiscriminantEstimates_DiscriminantTheorems_WickFormula
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_LiftXHasSubst
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_SCPf_liftX_add
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_SCPf_Dof_add

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
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.SCPf
variable {R : Type} [CommRing R] {d : ℕ} {O : Type} [CommRing O] [StarRing O]
variable {k : Type} [CommRing k] [Algebra ℚ k] [Algebra R k]
namespace ReciprocityTheory.ChartRestriction.G.TB.SCPf
theorem _root_.solution (B : FB R d O) (h : PS k 2 d) (m : ℕ) (u u' φ φ' : Fin d → k) (G : AA k d) :
    nabla k B h m (u + u') (φ + φ') G = nabla k B h m u φ G + nabla k B h m u' φ' G := by
  first
  | (unfold nabla Dx
     simp only [Pi.add_apply, Prod.fst_add, Prod.snd_add, map_add, add_mul, mul_add, Finset.sum_add_distrib, Dof_add,
       liftX_add, smul_add, add_smul]
     ring)
  | (unfold nabla
     revert G u u' φ φ' m h B
     done)
end ReciprocityTheory.ChartRestriction.G.TB.SCPf
