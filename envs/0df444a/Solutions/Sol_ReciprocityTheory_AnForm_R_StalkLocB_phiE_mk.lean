-- Prove2me | solution 1 for ReciprocityTheory.AnForm.R.StalkLocB.phiE_mk
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T05:23:40.971909+00:00
-- url     : https://prove2.me/submissions/fe1a2c37-ecd3-46d1-8a8c-55db401a6df3

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_JacChart
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_StalkLocB

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
namespace ReciprocityTheory.AnForm.R.StalkLocB
theorem _root_.solution (f : MvPolynomial (Fin n) ℂ) :
    phiE V K iso (Ideal.Quotient.mk K f) = secH V K iso f := rfl
end ReciprocityTheory.AnForm.R.StalkLocB
