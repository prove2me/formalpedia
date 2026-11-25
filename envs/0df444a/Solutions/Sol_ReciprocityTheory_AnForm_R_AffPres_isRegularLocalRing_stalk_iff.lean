-- Prove2me | solution 1 for ReciprocityTheory.AnForm.R.AffPres.isRegularLocalRing_stalk_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:33:22.238103+00:00
-- url     : https://prove2.me/submissions/17307882-c1a1-4171-94cd-9aebd957fc78

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_JacChart
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_FinalTheorems
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_StalkLocA
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_StalkLocB
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_StalkLoc
import Theorems.Thm_ReciprocityTheory_CA_DepthGE_of_ringEquiv
import Theorems.Thm_ReciprocityTheory_CA_IsCM_of_ringEquiv


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory MvPolynomial
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.R
noncomputable section
variable {W : Scheme.{0}} {s : W ⟶ Spec (.of ℂ)}
open ReciprocityTheory.AnForm.R.AffPres
variable (P : AffPres s)
namespace ReciprocityTheory.AnForm.R.AffPres
theorem _root_.solution (x : W) (hx : x ∈ P.V) (hc : IsClosed {x}) :
    IsRegularLocalRing (W.presheaf.stalk x) ↔ IsRegularLocalRing (locRing P.K (P.coord x hx)) := by
  constructor
  · intro h
    haveI := h
    first
    | exact IsRegularLocalRing.of_ringEquiv (P.stalkEquiv x hx hc)
    | exact IsRegularLocalRing.of_ringEquiv (e := P.stalkEquiv x hx hc)
  · intro h
    haveI := h
    first
    | exact IsRegularLocalRing.of_ringEquiv (P.stalkEquiv x hx hc).symm
    | exact IsRegularLocalRing.of_ringEquiv (e := (P.stalkEquiv x hx hc).symm)
end ReciprocityTheory.AnForm.R.AffPres
