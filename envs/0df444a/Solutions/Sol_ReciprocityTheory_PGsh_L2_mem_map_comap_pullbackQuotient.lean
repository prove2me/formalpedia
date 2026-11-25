-- Prove2me | solution 1 for ReciprocityTheory.PGsh.L2.mem_map_comap_pullbackQuotient
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T15:27:59.652448+00:00
-- url     : https://prove2.me/submissions/524428c8-cf6a-41c8-9c3e-bb959345625c

import Definitions.Def_ReciprocityTheory_DualLattices_ExistsFamilyValuationDetEqOne
import Definitions.Def_ReciprocityTheory_DualLattices_MemMapAugmentationIdealComapPullbackQuotient
import Theorems.Thm_ReciprocityTheory_PGsh_L2_pullbackQuotient_apply_out

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
theorem _root_.solution (AA : HopfOrder (C := C) R N) (K : AddSubgroup N) {h : N → C}
    (hh : h ∈ AA.carrier) (hinv : ∀ x (k : K), h (x + k) = h x) :
    h ∈ (AA.carrier.comap (pullQ (R := R) K)).map (pullQ (R := R) K) := by
  refine Submodule.mem_map.mpr ⟨fun q => h q.out, ?_, pullbackQuotient_apply_out (R := R) K hinv⟩
  rw [Submodule.mem_comap, pullbackQuotient_apply_out (R := R) K hinv]
  exact hh
end ReciprocityTheory.PGsh.L2
