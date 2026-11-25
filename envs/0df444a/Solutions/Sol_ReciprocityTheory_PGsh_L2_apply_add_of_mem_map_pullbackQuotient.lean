-- Prove2me | solution 1 for ReciprocityTheory.PGsh.L2.apply_add_of_mem_map_pullbackQuotient
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T15:14:44.485188+00:00
-- url     : https://prove2.me/submissions/521cbd65-93e3-44c7-8945-a3ba97d1c261

import Definitions.Def_ReciprocityTheory_DualLattices_ExistsFamilyValuationDetEqOne
import Definitions.Def_ReciprocityTheory_DualLattices_MemMapAugmentationIdealComapPullbackQuotient

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Finset
open ReciprocityTheory ReciprocityTheory.PGsh ReciprocityTheory.PGsh.L2
variable {C : Type} [Field C] {R : Type} [CommRing R] [Algebra R C] {v : Valuation C NNReal}
variable {N : Type} [AddCommGroup N] [Fintype N] [DecidableEq N]
namespace ReciprocityTheory.PGsh.L2
theorem _root_.solution (K : AddSubgroup N) (M : Submodule R (N ⧸ K → C)) {h : N → C}
    (hh : h ∈ M.map (pullQ (R := R) K)) (x : N) (k : K) : h (x + k) = h x := by
  obtain ⟨u, -, rfl⟩ := hh
  simp only [pullQ, LinearMap.funLeft_apply]
  rw [QuotientAddGroup.mk_add, (QuotientAddGroup.eq_zero_iff _).mpr k.2, add_zero]
end ReciprocityTheory.PGsh.L2
