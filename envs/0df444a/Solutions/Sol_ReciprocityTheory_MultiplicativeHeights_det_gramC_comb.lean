-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.det_gramC_comb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T15:48:06.50993+00:00
-- url     : https://prove2.me/submissions/10ba5319-8f9a-40ef-b7a9-a642192e9af6

import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegSt
import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegBA
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_gramC_comb

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights
open Matrix NumberField ComplexConjugate
open scoped ComplexOrder
namespace ReciprocityTheory.MultiplicativeHeights
theorem _root_.solution {K : Type} [Field K] [NumberField K] {r k : ℕ}
    (H : Matrix (Fin r) (Fin r) ℂ) (σ : K →+* ℂ) (b : Fin k → Fin r → K)
    (N : Matrix (Fin k) (Fin k) K) :
    (gramC H σ (fun j => ∑ i, N i j • b i)).det =
      ((Complex.normSq (σ N.det) : ℝ) : ℂ) * (gramC H σ b).det := by
  rw [gramC_comb, Matrix.det_mul, Matrix.det_mul, Matrix.det_conjTranspose]
  have h : (N.map σ).det = σ N.det := (RingHom.map_det σ N).symm
  rw [h, ← Complex.mul_conj]
  simp only [starRingEnd_apply]
  ring
end ReciprocityTheory.MultiplicativeHeights
