-- Prove2me | solution 1 for PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.BlockAlgebra.isUnit_poly
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T11:30:06.366536+00:00
-- url     : https://prove2.me/submissions/d7f1d537-76f9-44d7-8f6d-abd7ea8389df

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_InfinitesimalCharacterLimits_LieSumDecompositions_PBlocksAlg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Polynomial
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.SpectralAccumulation PositivityTheory.Rg.BcB.SpectralAccumulation.Cz PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.BlockAlgebra
variable {M : Type} [AddCommGroup M] [Module ℂ M]
namespace PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.BlockAlgebra
theorem _root_.solution (n : ℕ) (a : ℕ → Module.End ℂ M) (χ : ℕ → ℂ) (hcomm : ∀ k l, Commute (a k) (a l))
    (hnil : ∀ k, IsNilpotent (a k - χ k • 1)) (w : ℂ) (hw : (∑ k ∈ Finset.range (n + 1), w ^ k * χ k) ≠ 0) :
    IsUnit (∑ k ∈ Finset.range (n + 1), w ^ k • a k) := by
  set c := ∑ k ∈ Finset.range (n + 1), w ^ k * χ k with hc
  set N := ∑ k ∈ Finset.range (n + 1), w ^ k • (a k - χ k • 1) with hN
  have hNn : IsNilpotent N := by
    refine Commute.isNilpotent_sum (fun k _ => (hnil k).smul _) fun i j _ _ => ?_
    refine ((((hcomm i j).sub_right (Commute.smul_right (Commute.one_right _) _)).sub_left
      (Commute.smul_left (Commute.one_left _) _))).smul_left _ |>.smul_right _
  have e : (∑ k ∈ Finset.range (n + 1), w ^ k • a k) = algebraMap ℂ _ c * (1 + c⁻¹ • N) := by
    rw [mul_add, mul_one, ← Algebra.smul_def, smul_smul, mul_inv_cancel₀ hw, one_smul, hN, hc, Algebra.algebraMap_eq_smul_one,
      Finset.sum_smul, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [smul_sub, smul_smul, mul_comm, add_sub_cancel]
  rw [e]
  exact ((Units.mk0 c hw).isUnit.map (algebraMap ℂ (Module.End ℂ M))).mul (IsNilpotent.isUnit_one_add (hNn.smul _))
end PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.BlockAlgebra
