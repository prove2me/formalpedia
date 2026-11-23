-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.TraceConjugationCover.hessC_eq_lv
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:08:56.161867+00:00
-- url     : https://prove2.me/submissions/bac56b1e-8dc7-416d-9b4d-5da676e9f463

import Definitions.Def_ReciprocityTheory_AnalyticForms_MaIntEmpty
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_ComplexHessianIsHermitianOfContDiffAt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A ReciprocityTheory.AnForm.A.TraceConjugationCover
open Complex Filter Topology Matrix
noncomputable section
namespace ReciprocityTheory.AnForm.A.TraceConjugationCover
theorem _root_.solution {D : ℕ} (f : (Fin D → ℂ) → ℝ) (z : Fin D → ℂ) (i j : Fin D) :
    hessC f z i j = lv (fderiv ℝ (fderiv ℝ f) z) (Pi.single i 1) (Pi.single j 1) := rfl
end ReciprocityTheory.AnForm.A.TraceConjugationCover
