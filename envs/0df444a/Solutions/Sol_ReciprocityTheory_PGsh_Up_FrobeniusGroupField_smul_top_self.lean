-- Prove2me | solution 1 for ReciprocityTheory.PGsh.Up.FrobeniusGroupField.smul_top_self
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T15:31:16.647421+00:00
-- url     : https://prove2.me/submissions/fbfdabe7-c677-4ded-ac35-048dde19a4e8

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_IsAdicCompleteOfBasis

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Polynomial IsLocalRing
open ReciprocityTheory ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Up.FrobeniusGroupField
variable {p : ℕ} [hp : Fact p.Prime]
namespace ReciprocityTheory.PGsh.Up.FrobeniusGroupField
theorem _root_.solution (k : ℕ) :
    ((maximalIdeal ℤ_[p]) ^ k • ⊤ : Submodule ℤ_[p] ℤ_[p]) = (maximalIdeal ℤ_[p]) ^ k := by
  rw [smul_eq_mul, Ideal.mul_top]
end ReciprocityTheory.PGsh.Up.FrobeniusGroupField
