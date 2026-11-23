-- Prove2me | solution 1 for ReciprocityTheory.PGsh.L2.tableM_isUnit
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:31:58.404875+00:00
-- url     : https://prove2.me/submissions/352ef310-2c1c-4dde-8b8e-474c4f5e2461

import Definitions.Def_ReciprocityTheory_DualLattices_ValuationFourierLeOne
import Definitions.Def_ReciprocityTheory_DualLattices_CharTableIsUnit
import Definitions.Def_ReciprocityTheory_DualLattices_TransposeMulSelf
import Definitions.Def_ReciprocityTheory_DualLattices_MemDualLatMapFourier

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
variable {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H]
namespace ReciprocityTheory.PGsh.L2
theorem _root_.solution (e : H ≃ AddChar N C) (σ : H ≃ N) : IsUnit (tableM e σ).det := by
  unfold tableM
  exact charTable_isUnit (σ.symm.trans e)
end ReciprocityTheory.PGsh.L2
