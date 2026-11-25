-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.HermitianLatticeMaps.phi_herm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:54:23.050607+00:00
-- url     : https://prove2.me/submissions/e8d23637-b9f4-425a-ba6f-26987f5d66e5

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
variable {f f'}
namespace ReciprocityTheory.ChartRestriction.G.FD.HermitianLatticeMaps
theorem _root_.solution (h : ty X f = ty X f') (x y : Fin r → E) :
    herm X.Gm (phi X f f' x) (phi X f f' y) = herm X.Gm x y := by
  have h1 := congrArg Prod.fst h
  have hb : ∀ i j, herm X.Gm (f' i : Fin r → E) (f' j) = herm X.Gm (f i : Fin r → E) (f j) :=
    fun i j => (congrFun (congrFun h1 i) j).symm
  have s1 : ∀ i y, herm X.Gm (phi X f f' (f i)) (phi X f f' y) =
      herm X.Gm (f i : Fin r → E) y := by
    intro i y
    have e : (hR X (phi X f f' (f i))).comp (phi X f f') = hR X (f i) := by
      refine (RealPlaceEmbeddings.qb X f).ext fun j => ?_
      rw [LinearMap.comp_apply, RealPlaceEmbeddings.qb_apply, phi_f, phi_f]
      exact hb i j
    exact LinearMap.congr_fun e y
  have e2 : (hL X (phi X f f' y)).comp (phi X f f') = hL X y := by
    refine (RealPlaceEmbeddings.qb X f).ext fun i => ?_
    rw [LinearMap.comp_apply, RealPlaceEmbeddings.qb_apply]
    exact s1 i y
  exact LinearMap.congr_fun e2 x
end ReciprocityTheory.ChartRestriction.G.FD.HermitianLatticeMaps
