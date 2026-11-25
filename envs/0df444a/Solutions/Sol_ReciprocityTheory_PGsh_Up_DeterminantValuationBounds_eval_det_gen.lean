-- Prove2me | solution 1 for ReciprocityTheory.PGsh.Up.DeterminantValuationBounds.eval_det_gen
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T15:21:15.18154+00:00
-- url     : https://prove2.me/submissions/1547ebd8-b6cc-428d-adeb-6f27e8a09065

import Definitions.Def_ReciprocityTheory_DualLattices_ColengthSqBlockVandermonde
import Definitions.Def_ReciprocityTheory_DualLattices_ValuationPairwiseDifferenceProductPowLeColengthS

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open ReciprocityTheory ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up
open ReciprocityTheory.PGsh.L2
open ReciprocityTheory.PGsh.Up.DeterminantValuationBounds
variable {C : Type} [Field C] {v : Valuation C NNReal}
namespace ReciprocityTheory.PGsh.Up.DeterminantValuationBounds
theorem _root_.solution {K : Type} [CommRing K] {ι σ : Type} [Fintype ι] [DecidableEq ι] [Fintype σ]
    (A : Matrix ι σ K) (z : σ × ι → K) :
    MvPolynomial.eval z (Matrix.det (Matrix.of fun i j =>
      ∑ r, MvPolynomial.C (A i r) * (MvPolynomial.X (r, j) : MvPolynomial (σ × ι) K))) =
      Matrix.det (Matrix.of fun i j => ∑ r, A i r * z (r, j)) := by
  rw [RingHom.map_det]
  congr 1
  ext i j
  simp [map_sum]
end ReciprocityTheory.PGsh.Up.DeterminantValuationBounds
