-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.dzEntry_symm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:18:09.705946+00:00
-- url     : https://prove2.me/submissions/ee0abf4d-ee17-4eb5-9035-4b831e65d07c

import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PartsCalc
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PartsPiola
import Theorems.Thm_ReciprocityTheory_AnForm_A_hessEntry_apply


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A
open MeasureTheory ReciprocityTheory.AnForm Matrix Filter Topology
noncomputable section
namespace ReciprocityTheory.AnForm.A
theorem _root_.solution {D : ℕ} (T : (Fin D → ℂ) →L[ℝ] BilinSp D) (hT : ∀ u x, T u x = T x u)
    (j a b : Fin D) :
    (1 / 2 : ℂ) * hessEntry a b (T (Pi.single j 1)) +
        (-(Complex.I / 2)) * hessEntry a b (T (Complex.I • Pi.single j 1)) =
      (1 / 2 : ℂ) * hessEntry j b (T (Pi.single a 1)) +
        (-(Complex.I / 2)) * hessEntry j b (T (Complex.I • Pi.single a 1)) := by
  have e1 := hT (Pi.single j 1) (Pi.single a 1)
  have e2 := hT (Pi.single j 1) (Complex.I • Pi.single a 1)
  have e3 := hT (Complex.I • Pi.single j 1) (Pi.single a 1)
  have e4 := hT (Complex.I • Pi.single j 1) (Complex.I • Pi.single a 1)
  simp only [hessEntry_apply, e1, e2, e3, e4]
  push_cast
  linear_combination
    ((T (Complex.I • Pi.single a 1) (Pi.single j 1) (Complex.I • Pi.single b 1) : ℂ) -
      (T (Pi.single a 1) (Complex.I • Pi.single j 1) (Complex.I • Pi.single b 1) : ℂ)) / 8 *
      Complex.I_sq
end ReciprocityTheory.AnForm.A
