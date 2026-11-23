-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.SemiPt.adMet_pos
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:14:25.095857+00:00
-- url     : https://prove2.me/submissions/8214eca4-cf9b-4002-b2e9-9906b5af81a0

import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegE
import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegF

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
theorem _root_.solution {K : Type} [Field K] [NumberField K] (r m : ℕ) (g : Fin r → K)
    (dd : Fin r → ℝ) (hdd : ∀ i, 0 < dd i)
    (hg : ∀ i : Fin r, m ≤ (i : ℕ) → (i : ℕ) + m < r → g i ≠ 0) (σ : K →+* ℂ) (i : Fin r) :
    0 < adMet r m g dd σ i := by
  have hi := i.isLt
  unfold adMet
  split_ifs with h1 h2
  · exact hdd i
  · exact inv_pos.mpr (hdd _)
  · exact norm_pos_iff.mpr ((map_ne_zero σ).mpr (hg i (by omega) (by omega)))
end ReciprocityTheory.MultiplicativeHeights.SemiPt
