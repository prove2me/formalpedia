-- Prove2me | solution 1 for P2M_ReciprocityTheory_AnForm_A_polyMax_le__638c0d78514a
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:34:02.192426+00:00
-- url     : https://prove2.me/submissions/de49dfb3-2b6c-4b59-bd0b-3cee1bfb6698

import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_IsPshLocallyIntegrableStatement
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshMollB
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshMoll

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A
open MeasureTheory Metric Filter Topology Set
noncomputable section
variable {D : ℕ}
variable {U : Set (Fin D → ℂ)} {φ : (Fin D → ℂ) → ℝ} {z : Fin D → ℂ}
namespace ReciprocityTheory.AnForm.A
theorem _root_.solution {t c : ℝ} (ht : 0 ≤ t) (h : ∀ x ∈ closedBall z t, φ x ≤ c) :
    polyMax φ z t ≤ c :=
  csSup_le ((nonempty_closedBall.2 ht).image φ) (by rintro _ ⟨x, hx, rfl⟩; exact h x hx)
end ReciprocityTheory.AnForm.A
