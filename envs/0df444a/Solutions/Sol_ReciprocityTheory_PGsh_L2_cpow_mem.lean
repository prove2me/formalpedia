-- Prove2me | solution 1 for ReciprocityTheory.PGsh.L2.cpow_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T15:31:10.925484+00:00
-- url     : https://prove2.me/submissions/18ea82cf-a578-4895-848a-b96be7063a72

import Definitions.Def_ReciprocityTheory_DualLattices_ValuationDetEqOfSpanEq
import Definitions.Def_ReciprocityTheory_DualLattices_ValuationFourierLeOne
import Theorems.Thm_ReciprocityTheory_PGsh_L2_conv_mem_dualLat
import Theorems.Thm_ReciprocityTheory_PGsh_L2_single_mem_dualLat

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset Matrix
open ReciprocityTheory ReciprocityTheory.PGsh ReciprocityTheory.PGsh.L2
variable {C : Type} [Field C] {R : Type} [CommRing R] [Algebra R C]
variable {N : Type} [AddCommGroup N] [Fintype N] [DecidableEq N]
namespace ReciprocityTheory.PGsh.L2
theorem _root_.solution (AA : HopfOrder (C := C) R N) {u : N → C} (hu : u ∈ dualLat AA.carrier) :
    ∀ k, cpow u k ∈ dualLat AA.carrier
  | 0 => single_mem_dualLat AA
  | k + 1 => conv_mem_dualLat AA (solution AA hu k) hu
end ReciprocityTheory.PGsh.L2
