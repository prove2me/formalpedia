-- Prove2me | solution 1 for PositivityTheory.RgJS.Common0Aux.sum_lterm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:03:33.078701+00:00
-- url     : https://prove2.me/submissions/e15d6ee5-b949-40aa-824d-e19439fcc2f4

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_JacquetShalikaBounds_AbsoluteRigidity_NewtonLow
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_JacquetShalikaBounds_AbsoluteRigidity_SubtypeIteSums_CommonOfLandauEuler
import Theorems.Thm_PositivityTheory_RgJS_Common0Aux_lterm_pair

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped ComplexConjugate
open Finset
open PositivityTheory PositivityTheory.RgJS PositivityTheory.RgJS.Common0Aux
variable {W X : Type} {d : X → ℕ}
namespace PositivityTheory.RgJS.Common0Aux
theorem _root_.solution (q : W → ℕ) (hq : ∀ w, 2 ≤ q w) (A : ∀ x, W → Fin (d x) → ℂ) {ι κ : Type} [Fintype ι] [Fintype κ]
    (u : ι → X × ℝ) (v : κ → X × ℝ) (σ : ℝ) (p : W × ℕ) :
    ∑ i, ∑ j, lterm q (A (u i).1) (A (v j).1) (((σ + (u i).2 + (v j).2 : ℝ)) : ℂ) p =
      Pw q A u p.1 p.2 * conj (Pw q A v p.1 p.2) * ((q p.1 : ℂ) ^ (-(σ : ℂ))) ^ (p.2 + 1) / (p.2 + 1) := by
  simp only [lterm_pair q hq]
  unfold Pw
  rw [map_sum, Finset.sum_mul_sum]
  simp only [Finset.sum_mul, Finset.sum_div]
end PositivityTheory.RgJS.Common0Aux
