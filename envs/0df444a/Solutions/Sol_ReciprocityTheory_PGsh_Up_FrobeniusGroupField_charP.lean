-- Prove2me | solution 1 for ReciprocityTheory.PGsh.Up.FrobeniusGroupField.charP
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:32:44.182137+00:00
-- url     : https://prove2.me/submissions/c2b677ba-5a95-4184-9f71-010fd10c06f9

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_IsUnitOfNotMem
import Theorems.Thm_ReciprocityTheory_PGsh_Up_FrobeniusGroupField_res_eq_zero

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
open ReciprocityTheory ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Up.FrobeniusGroupField
variable {C : Type} [Field C] {v : Valuation C NNReal} {R : Type} [CommRing R] [Algebra R C]
namespace ReciprocityTheory.PGsh.Up.FrobeniusGroupField
theorem _root_.solution (p : ℕ) [hp : Fact p.Prime] (hv : v.Integers R)
    (hpv : v (algebraMap R C (p : R)) < 1) : CharP (R ⧸ mI hv) p := by
  have h0 : ((p : R ⧸ mI hv)) = 0 := by
    rw [← map_natCast (res hv), res_eq_zero]; exact hpv
  exact (CharP.charP_iff_prime_eq_zero hp.out).2 h0
end ReciprocityTheory.PGsh.Up.FrobeniusGroupField
