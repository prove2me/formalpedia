-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.SemiPt.g_fix
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T14:57:38.533919+00:00
-- url     : https://prove2.me/submissions/d012fcc6-5c56-483f-9207-3f84291c88cc

import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegF
import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegG
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_SemiPt_herm_cGP

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights ReciprocityTheory.MultiplicativeHeights.SemiPt
open Matrix NumberField ComplexConjugate
open scoped ComplexOrder
namespace ReciprocityTheory.MultiplicativeHeights.SemiPt
theorem _root_.solution {K : Type} [Field K] [NumberField K] {r : ℕ} (S : HermForm K r)
    (P : Matrix (Fin r) (Fin r) K) (m : ℕ) (g : Fin r → K)
    (hJ : (P.map S.c)ᵀ * S.G * P = wittMat r m g) (i : Fin r) (h1 : m ≤ (i : ℕ))
    (h2 : (i : ℕ) + m < r) : S.c (g i) = g i := by
  have h := herm_cGP S P i i
  rw [hJ] at h
  simpa [wittMat, Matrix.of_apply, not_lt.2 h1, h1, h2] using h
end ReciprocityTheory.MultiplicativeHeights.SemiPt
