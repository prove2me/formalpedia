-- Prove2me | solution 1 for ReciprocityTheory.AnForm.R.AffPres.rsp_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:44:27.504402+00:00
-- url     : https://prove2.me/submissions/9ce627c0-f864-4ec8-849c-13d4f6775c38

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_JacChart
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_FinalTheorems
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_StalkLocA
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_StalkLocB
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_StalkLoc
import Theorems.Thm_ReciprocityTheory_AnForm_R_AffPres_ringKrullDim_stalk
import Theorems.Thm_ReciprocityTheory_AnForm_R_AffPres_map_maximalIdeal_stalk

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
theorem _root_.solution (x : W) (hx : x ∈ P.V) (hc : IsClosed {x}) {e : ℕ} (r : Fin e → W.presheaf.stalk x) :
    FinalTheorems.Rsp (W.presheaf.stalk x) e r ↔
      Ideal.span (Set.range fun l => P.stalkEquiv x hx hc (r l)) =
        Ideal.map (algebraMap _ (locRing P.K (P.coord x hx))) (ptIdeal (P.coord x hx)) ∧
      (e : WithBot ℕ∞) = ringKrullDim (locRing P.K (P.coord x hx)) := by
  unfold FinalTheorems.Rsp
  rw [← P.ringKrullDim_stalk x hx hc, ← P.map_maximalIdeal_stalk x hx hc]
  have hspan : Ideal.span (Set.range fun l => P.stalkEquiv x hx hc (r l)) =
      (Ideal.span (Set.range r)).map (P.stalkEquiv x hx hc) := by
    rw [Ideal.map_span, ← Set.range_comp]
    rfl
  rw [hspan]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨by rw [h1], h2⟩
  · rintro ⟨h1, h2⟩
    refine ⟨?_, h2⟩
    have h3 := congrArg (Ideal.comap (P.stalkEquiv x hx hc)) h1
    rwa [Ideal.comap_map_of_bijective _ (P.stalkEquiv x hx hc).bijective,
      Ideal.comap_map_of_bijective _ (P.stalkEquiv x hx hc).bijective] at h3
end ReciprocityTheory.AnForm.R.AffPres
