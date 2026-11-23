-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.HermitianLatticeMaps.phi_phi
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:41:28.6378+00:00
-- url     : https://prove2.me/submissions/fdbb6495-7ea9-4c2c-ac1c-470f30bda591

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_RealPlaceEmbeddings
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_HermitianLatticeMaps
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_RealPlaceEmbeddings_qb_apply


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open ReciprocityTheory.ChartRestriction.G.FD.HermitianLatticeMaps
open Matrix NumberField Module
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable (f f' : Basis ι ℤ X.Λ)
namespace ReciprocityTheory.ChartRestriction.G.FD.HermitianLatticeMaps
theorem _root_.solution (x : Fin r → E) : phi X f' f (phi X f f' x) = x := by
  have e : (phi X f' f).comp (phi X f f') = LinearMap.id := by
    refine (RealPlaceEmbeddings.qb X f).ext fun i => ?_
    rw [LinearMap.comp_apply, RealPlaceEmbeddings.qb_apply, phi_f, phi_f, LinearMap.id_apply]
  exact LinearMap.congr_fun e x
end ReciprocityTheory.ChartRestriction.G.FD.HermitianLatticeMaps
