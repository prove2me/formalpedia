-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ratStandard_latticeMetricAgrees_b5791eb021fc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T05:12:11.800741+00:00
-- url     : https://prove2.me/submissions/4b71819b-1c8e-4193-b7ee-f5b873e2142b

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Objects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_DualModel

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial NumberField Matrix
open scoped ComplexOrder
noncomputable section
variable {K : Type*} [Field K] [NumberField K]
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution (r : ℕ) :
    LatticeMetricAgrees (fun j : Fin (r + 1) ↦ (Pi.single j (1 : ℚ) : Fin (r + 1) → ℚ))
      (HermLattice.standard ℚ (r + 1)) (HermLine.standard (fun _ : Unit ↦ r)) := by
  intro σ w _
  change ∏ _u : Unit, l2Norm (latticePoint _ σ w ()) =
    Real.sqrt (star w ⬝ᵥ ((1 : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ) *ᵥ w)).re
  rw [Fintype.prod_unique, l2Norm, one_mulVec]
  congr 1
  have h1 : ∀ p, latticePoint (fun j : Fin (r + 1) ↦ (Pi.single j (1 : ℚ) : Fin (r + 1) → ℚ)) σ w () p =
      w p := by
    intro p
    simp [latticePoint, Pi.single_apply]
  simp only [h1]
  rw [dotProduct, Complex.re_sum]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [Pi.star_apply, Complex.star_def, Complex.conj_mul']
  norm_cast
end GroundTheory.Heights₂.Heights
