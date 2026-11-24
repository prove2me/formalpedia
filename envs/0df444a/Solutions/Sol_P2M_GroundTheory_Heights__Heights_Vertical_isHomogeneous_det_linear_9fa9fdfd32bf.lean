-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Vertical_isHomogeneous_det_linear_9fa9fdfd32bf
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:04:35.79403+00:00
-- url     : https://prove2.me/submissions/29670516-2c24-4402-91b6-5ffb6a0c2a01

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_PNormFormEval
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_PChowSecDegree

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Vertical
open MvPolynomial
noncomputable section
namespace GroundTheory.Heights₂.Heights.Vertical
theorem _root_.solution {R : Type*} [CommRing R] {σ ι : Type*} [Fintype ι] [DecidableEq ι]
    (N : Matrix ι ι (MvPolynomial σ R)) (hN : ∀ i k, (N i k).IsHomogeneous 1) :
    N.det.IsHomogeneous (Fintype.card ι) := by
  rw [Matrix.det_apply]
  refine IsHomogeneous.sum _ _ _ fun τ _ => ?_
  have hp := IsHomogeneous.prod Finset.univ (fun i => N (τ i) i) (fun _ => 1) fun i _ => hN (τ i) i
  simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one] at hp
  rw [Units.smul_def, zsmul_eq_mul, ← map_intCast (C : R →+* MvPolynomial σ R)]
  simpa using (isHomogeneous_C σ ((τ.sign : ℤ) : R)).mul hp
end GroundTheory.Heights₂.Heights.Vertical
