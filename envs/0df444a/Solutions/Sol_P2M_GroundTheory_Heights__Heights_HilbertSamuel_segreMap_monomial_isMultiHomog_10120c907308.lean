-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HilbertSamuel_segreMap_monomial_isMultiHomog_10120c907308
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T03:25:33.928568+00:00
-- url     : https://prove2.me/submissions/4e584a80-848e-4bc1-bfdd-31005e62d799

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsSegrePrime
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PSegrePrime

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.HilbertSamuel
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR
noncomputable section
variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} (F : Type) [Field F]
namespace GroundTheory.Heights₂.Heights.HilbertSamuel
theorem _root_.solution (d : ((_ : Unit) × ((k : K) → ι k)) →₀ ℕ) (a : F) :
    IsMultiHomog (segreMap F (monomial d a))
      (fun _ => Finsupp.weight (blockWeight (fun _ : Unit => ∀ k, ι k)) d ()) := by
  unfold IsMultiHomog
  rw [segreMap, aeval_monomial, algebraMap_eq, Finsupp.prod]
  refine IsWeightedHomogeneous.C_mul ?_ a
  have hX : ∀ v : (_ : Unit) × ((k : K) → ι k),
      IsWeightedHomogeneous (blockWeight ι) (∏ k, (X ⟨k, v.2 k⟩ : MRing ι F)) (fun _ => 1) := by
    intro v
    have := IsWeightedHomogeneous.prod (w := blockWeight ι) Finset.univ
      (fun k => (X ⟨k, v.2 k⟩ : MRing ι F)) (fun k => Pi.single k 1)
      (fun k _ => isWeightedHomogeneous_X F _ _)
    convert this using 1
    ext j
    simp [Finset.sum_apply, Pi.single_apply]
  have := IsWeightedHomogeneous.prod d.support
    (fun v => (∏ k, (X ⟨k, v.2 k⟩ : MRing ι F)) ^ d v) (fun v => d v • (fun _ : K => (1 : ℕ)))
    (fun v _ => (hX v).pow _)
  have e : (fun _ : K => Finsupp.weight (blockWeight (fun _ : Unit => ∀ k, ι k)) d ()) =
      ∑ v ∈ d.support, d v • (fun _ : K => (1 : ℕ)) := by
    ext j
    simp [Finsupp.weight_apply, Finsupp.sum, blockWeight, Finset.sum_apply]
  rw [e]
  exact this
end GroundTheory.Heights₂.Heights.HilbertSamuel
