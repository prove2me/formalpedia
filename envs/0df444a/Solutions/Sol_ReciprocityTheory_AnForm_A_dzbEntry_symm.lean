-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.dzbEntry_symm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:24:56.658955+00:00
-- url     : https://prove2.me/submissions/6cf3dc19-3454-4fb6-8eee-b2186d2bfa1f

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
theorem _root_.solution {D : ℕ} (T : (Fin D → ℂ) →L[ℝ] BilinSp D)
    (hT : ∀ u x y, T u x y = T y x u) (k a b : Fin D) :
    (1 / 2 : ℂ) * hessEntry a b (T (Pi.single k 1)) +
        (Complex.I / 2) * hessEntry a b (T (Complex.I • Pi.single k 1)) =
      (1 / 2 : ℂ) * hessEntry a k (T (Pi.single b 1)) +
        (Complex.I / 2) * hessEntry a k (T (Complex.I • Pi.single b 1)) := by
  have e1 := hT (Pi.single b 1) (Pi.single a 1) (Pi.single k 1)
  have e2 := hT (Pi.single b 1) (Complex.I • Pi.single a 1) (Complex.I • Pi.single k 1)
  have e3 := hT (Pi.single b 1) (Pi.single a 1) (Complex.I • Pi.single k 1)
  have e4 := hT (Pi.single b 1) (Complex.I • Pi.single a 1) (Pi.single k 1)
  have e5 := hT (Complex.I • Pi.single b 1) (Pi.single a 1) (Pi.single k 1)
  have e6 := hT (Complex.I • Pi.single b 1) (Complex.I • Pi.single a 1)
    (Complex.I • Pi.single k 1)
  have e7 := hT (Complex.I • Pi.single b 1) (Pi.single a 1) (Complex.I • Pi.single k 1)
  have e8 := hT (Complex.I • Pi.single b 1) (Complex.I • Pi.single a 1) (Pi.single k 1)
  simp only [hessEntry_apply, e1, e2, e3, e4, e5, e6, e7, e8]
  push_cast
  linear_combination
    ((T (Pi.single k 1) (Complex.I • Pi.single a 1) (Complex.I • Pi.single b 1) : ℂ) -
      (T (Complex.I • Pi.single k 1) (Complex.I • Pi.single a 1) (Pi.single b 1) : ℂ)) / 8 *
      Complex.I_sq
end ReciprocityTheory.AnForm.A
