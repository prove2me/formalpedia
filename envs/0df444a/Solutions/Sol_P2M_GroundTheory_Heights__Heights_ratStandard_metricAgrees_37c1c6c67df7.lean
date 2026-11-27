-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ratStandard_metricAgrees_37c1c6c67df7
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T05:12:15.646839+00:00
-- url     : https://prove2.me/submissions/b2af4bf3-f846-4c59-b444-e92e92ea2c2a

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Objects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Examples
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ratIntegerBasis_apply_239c16315f02

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
open MvPolynomial NumberField
noncomputable section
variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable (n : ι → ℕ) (k₀ : ι)
open Matrix
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution (r : ℕ) :
    OneBlockMetricAgrees ratIntegerBasis (HermLattice.standard ℚ (r + 1))
      (HermLine.standard (oneBlockSizes 0 r)) := by
  intro σ w _
  change ∏ _u : Unit, l2Norm (oneBlockPoint ratIntegerBasis σ w ()) =
    Real.sqrt (star w ⬝ᵥ ((1 : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ) *ᵥ w)).re
  rw [Fintype.prod_unique, l2Norm, one_mulVec]
  congr 1
  have h1 : ∀ p, ‖oneBlockPoint ratIntegerBasis σ w () p‖ ^ 2 = ‖w (oneBlockIndex 0 r p).2‖ ^ 2 := by
    intro p
    simp [oneBlockPoint, ratIntegerBasis_apply]
  simp only [h1]
  rw [Fintype.sum_equiv (oneBlockIndex 0 r) _ (fun q ↦ ‖w q.2‖ ^ 2) (fun _ ↦ rfl),
    Fintype.sum_prod_type, Fin.sum_univ_one, dotProduct, Complex.re_sum]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [Pi.star_apply, Complex.star_def, Complex.conj_mul']
  norm_cast
end GroundTheory.Heights₂.Heights
