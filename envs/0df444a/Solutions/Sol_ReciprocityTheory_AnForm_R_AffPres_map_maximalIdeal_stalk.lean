-- Prove2me | solution 1 for ReciprocityTheory.AnForm.R.AffPres.map_maximalIdeal_stalk
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:35:34.276715+00:00
-- url     : https://prove2.me/submissions/f81b5cfd-0d5b-49bc-83f3-9c4da7ff0068

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_JacChart
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_FinalTheorems
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_StalkLocA
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_StalkLocB
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_StalkLoc
import Theorems.Thm_ReciprocityTheory_AnForm_R_isLocalRing_locRing
import Theorems.Thm_ReciprocityTheory_AnForm_R_maximalIdeal_locRing


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
    (IsLocalRing.maximalIdeal (W.presheaf.stalk x)).map (P.stalkEquiv x hx hc) =
      Ideal.map (algebraMap _ (locRing P.K (P.coord x hx))) (ptIdeal (P.coord x hx)) := by
  have hK : P.K ≤ ptIdeal (P.coord x hx) := by
    rw [← P.ptOf_eq_ptIdeal x hx hc]
    intro h hh
    show Ideal.Quotient.mk P.K h ∈ (P.iso.hom.base ⟨x, hx⟩).asIdeal
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr hh]
    exact Ideal.zero_mem _
  haveI := isLocalRing_locRing hK
  rw [← maximalIdeal_locRing hK]
  exact IsLocalRing.eq_maximalIdeal (Ideal.map_isMaximal_of_equiv _)
end ReciprocityTheory.AnForm.R.AffPres
