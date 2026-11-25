-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.sch_of_no
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T13:45:04.934376+00:00
-- url     : https://prove2.me/submissions/90a423df-0534-482c-b63d-1fe6ac1a1fe1

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_CasimirGapAtNoncompactWeight
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_SchForm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_exists_khw_of_not_sch

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ}
variable {M : Type*} [NormedAddCommGroup M] [InnerProductSpace ℂ M] {ε : Fin n → Bool}
  {E : Fin n → Fin n → Module.End ℂ M} {V : Submodule ℂ M} {lam : Fin n → ℝ}
namespace ReciprocityTheory.ChartRestriction.DS
theorem _root_.solution (hE : IsGlRep E) (hU : IsInfUnitary ε E)
    (hV : IsKIrrHW ε E (lowK ε lam) V) (hmono : StrictAnti lam) {h : ℝ} (hh : GapAtLeast ε lam h)
    (hbig : (n : ℝ) * (pOf ε : ℝ) * (qOf ε : ℝ) + 1 < h)
    (hNo : ∀ a b : Fin n, a < b → ε a ≠ ε b → ∀ w ∈ layer ε E V 1,
      IsKHWVec ε E (lowK ε lam - root a b) w → w = 0) :
    ∀ x ∈ Wm ε E V, phi E 1 x = 0 := by
  intro x hx
  by_contra hne
  obtain ⟨a, b, hab, hε, w, hw, hw0, hkhw⟩ :=
    exists_khw_of_not_sch hE hU hV hmono hh hbig ⟨x, hx, hne⟩
  exact hw0 (hNo a b hab hε w hw hkhw)
end ReciprocityTheory.ChartRestriction.DS
