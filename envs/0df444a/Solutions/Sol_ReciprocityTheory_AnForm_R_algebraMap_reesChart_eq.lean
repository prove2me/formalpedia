-- Prove2me | solution 1 for ReciprocityTheory.AnForm.R.algebraMap_reesChart_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T14:09:05.031831+00:00
-- url     : https://prove2.me/submissions/8fa746c1-82f0-4ab5-ad7b-c6802e4a59d4

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
theorem _root_.solution {R : Type} [CommRing R] {m : ℕ} (g : Fin m → R) (i k : Fin m) :
    algebraMap R (FinalTheorems.reesChart g i) (g k) = fracR g i k * algebraMap R (FinalTheorems.reesChart g i) (g i) := by
  apply Subtype.ext
  exact (IsLocalization.mk'_spec (Localization.Away (g i)) (g k)
    (⟨g i, Submonoid.mem_powers _⟩ : Submonoid.powers (g i))).symm
end ReciprocityTheory.AnForm.R
