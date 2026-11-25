-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.SemiPt.gramC_single
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T15:10:09.056314+00:00
-- url     : https://prove2.me/submissions/bc928f4a-c501-43b7-bb3a-178803f255c5

import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegT
import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegR

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
theorem _root_.solution {K : Type} [Field K] [NumberField K] {r : ℕ} (δ : (K →+* ℂ) → Fin r → ℝ)
    (σ : K →+* ℂ) (i : Fin r) (x : Fin r → K) (hx : IsAt i x) :
    (gramC (diagMet δ σ) σ ![x]).det.re = ‖σ (x i)‖ ^ 2 * δ σ i := by
  rw [Matrix.det_unique]
  simp only [gramC, Matrix.of_apply, embVec, diagMet, Matrix.mulVec_diagonal, dotProduct,
    Pi.star_apply]
  rw [Finset.sum_eq_single i]
  · simp only [Fin.default_eq_zero, Matrix.cons_val_zero]
    rw [show star (σ (x i)) * (((δ σ i : ℝ) : ℂ) * σ (x i)) =
        ((δ σ i : ℝ) : ℂ) * (starRingEnd ℂ (σ (x i)) * σ (x i)) by
      rw [Complex.star_def]; ring]
    rw [Complex.conj_mul']
    simp only [Complex.re_ofReal_mul]
    norm_cast
    ring
  · intro a _ ha
    simp [Fin.default_eq_zero, hx a ha]
  · intro h
    exact absurd (Finset.mem_univ _) h
end ReciprocityTheory.MultiplicativeHeights.SemiPt
