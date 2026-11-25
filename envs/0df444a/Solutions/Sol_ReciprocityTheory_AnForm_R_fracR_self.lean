-- Prove2me | solution 1 for ReciprocityTheory.AnForm.R.fracR_self
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T14:05:12.750461+00:00
-- url     : https://prove2.me/submissions/93b4c0e7-7c06-4310-aa51-da3950107c74

import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_WChartsA
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_WChartsD

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.R
open MvPolynomial AlgebraicGeometry CategoryTheory
noncomputable section
namespace ReciprocityTheory.AnForm.R
theorem _root_.solution {R : Type} [CommRing R] {m : ℕ} (g : Fin m → R) (i : Fin m) : fracR g i i = 1 := by
  apply Subtype.ext
  exact IsLocalization.mk'_self' (Localization.Away (g i))
end ReciprocityTheory.AnForm.R
