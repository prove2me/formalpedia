-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.HSt.CompactCayleyBlocks.pm_unit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T11:40:58.365714+00:00
-- url     : https://prove2.me/submissions/e7601569-1f20-462d-90d2-bc4ac0b464b3

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_CayleyCosetSums_SpanUnitaryMatrix

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
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.HSt PositivityTheory.Rg.Sw.HSt.CompactCayleyBlocks
variable {n : ℕ}
namespace PositivityTheory.Rg.Sw.HSt.CompactCayleyBlocks
theorem _root_.solution (σ : Equiv.Perm (Fin n)) : (pm σ)ᴴ * pm σ = 1 := by
  ext i j
  simp only [pm, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply, Matrix.one_apply]
  rw [Finset.sum_eq_single (σ.symm i)]
  · by_cases h : i = j <;> simp [h, eq_comm, Equiv.apply_eq_iff_eq_symm_apply]
  · intro k _ hk
    have : σ k ≠ i := fun e => hk (by rw [← e]; simp)
    simp [this]
  · simp
end PositivityTheory.Rg.Sw.HSt.CompactCayleyBlocks
