-- Prove2me | solution 1 for ReciprocityTheory.AnForm.R.StalkLocB.germ_secH_C
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:14:52.226275+00:00
-- url     : https://prove2.me/submissions/9e9b1bf6-0219-4ac1-af07-47ce5e982743

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_JacChart
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_StalkLocB
import Theorems.Thm_ReciprocityTheory_AnForm_R_StalkLocB_secH_C

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
open ReciprocityTheory.AnForm.R.StalkLocB
variable {W : Scheme.{0}} (V : W.Opens) {n : ℕ} (K : Ideal (MvPolynomial (Fin n) ℂ))
  (iso : V.toScheme ≅ Spec (.of (MvPolynomial (Fin n) ℂ ⧸ K)))
variable {K iso}
namespace ReciprocityTheory.AnForm.R.StalkLocB
theorem _root_.solution (s : W ⟶ Spec (.of ℂ))
    (hover : iso.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap ℂ (MvPolynomial (Fin n) ℂ ⧸ K))) =
      V.ι ≫ s) (x : W) (hx : x ∈ V) (c : ℂ) :
    W.presheaf.germ V x hx (secH V K iso (C c)) =
      W.presheaf.germ ⊤ x trivial (s.appTop ((Scheme.ΓSpecIso (.of ℂ)).inv c)) := by
  rw [secH_C V s hover c, TopCat.Presheaf.germ_res_apply]
end ReciprocityTheory.AnForm.R.StalkLocB
