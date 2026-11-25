-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.FFTSteps.sq_le_sum_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T11:39:20.192849+00:00
-- url     : https://prove2.me/submissions/e9e26f10-0b6e-4721-9a31-882d96fa22ea

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_GaussianPlaneIntegrals_AssemblyAlt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_GaussianPlaneIntegrals_NullTop

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory MvPolynomial Filter Topology
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.FFTSteps
variable {m n : ℕ}
namespace PositivityTheory.Rg.Sw.FFTSteps
theorem _root_.solution (x : Fin m → Fin n → ℂ) (a : Fin m) (i : Fin n) :
    ‖x a i‖ ^ 2 ≤ ∑ a, ∑ i, ‖x a i‖ ^ 2 := by
  have h1 : ‖x a i‖ ^ 2 ≤ ∑ j, ‖x a j‖ ^ 2 :=
    Finset.single_le_sum (f := fun j => ‖x a j‖ ^ 2) (fun j _ => sq_nonneg _) (Finset.mem_univ i)
  have h2 : ∑ j, ‖x a j‖ ^ 2 ≤ ∑ b, ∑ j, ‖x b j‖ ^ 2 :=
    Finset.single_le_sum (f := fun b => ∑ j, ‖x b j‖ ^ 2)
      (fun b _ => Finset.sum_nonneg (fun j _ => sq_nonneg _)) (Finset.mem_univ a)
  exact h1.trans h2
end PositivityTheory.Rg.Sw.FFTSteps
