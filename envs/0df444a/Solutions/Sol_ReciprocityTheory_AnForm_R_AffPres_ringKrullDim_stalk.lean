-- Prove2me | solution 1 for ReciprocityTheory.AnForm.R.AffPres.ringKrullDim_stalk
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:32:56.072941+00:00
-- url     : https://prove2.me/submissions/6f9278ec-699e-409b-bbe6-9d704d6843fe

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_JacChart
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_FinalTheorems
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_StalkLocA
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_StalkLocB
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_StalkLoc

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
    ringKrullDim (W.presheaf.stalk x) = ringKrullDim (locRing P.K (P.coord x hx)) := by
  exact ringKrullDim_eq_of_ringEquiv (P.stalkEquiv x hx hc)
end ReciprocityTheory.AnForm.R.AffPres
