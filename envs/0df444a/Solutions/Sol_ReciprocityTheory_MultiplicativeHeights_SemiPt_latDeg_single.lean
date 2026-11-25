-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.SemiPt.latDeg_single
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T15:22:23.929688+00:00
-- url     : https://prove2.me/submissions/0a2ad30d-389b-4d1c-bdd7-1750f5f8ba72

import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegT
import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegR
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_SemiPt_gramC_single

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
theorem _root_.solution {K : Type} [Field K] [NumberField K] {r : ℕ}
    (δ : (K →+* ℂ) → Fin r → ℝ) (C : Submodule (𝓞 K) (Fin r → K)) (i : Fin r) (x : Fin r → K)
    (hx : IsAt i x) :
    latDeg (diagMet δ) C ![x] = Real.log (spanIdx C ![x] : ℝ) -
      (1 / 2) * ∑ σ : K →+* ℂ, Real.log (‖σ (x i)‖ ^ 2 * δ σ i) := by
  unfold latDeg spanIdx
  congr 2
  exact Finset.sum_congr rfl fun σ _ => by rw [gramC_single δ σ i x hx]
end ReciprocityTheory.MultiplicativeHeights.SemiPt
