-- Prove2me | solution 1 for ReciprocityTheory.Gal.isClosed_setOf_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T20:31:27.047804+00:00
-- url     : https://prove2.me/submissions/b025f6dd-1036-4fb1-9670-e78a3979aa6a

import Mathlib
import Definitions.Def_ReciprocityTheory_GaloisValuations_GlobalA
import Theorems.Thm_ReciprocityTheory_Gal_isOpen_setOf_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Pointwise
open ReciprocityTheory ReciprocityTheory.Gal
variable {F Ω : Type*} [Field F] [Field Ω] [Algebra F Ω] [Algebra.IsIntegral F Ω]
namespace ReciprocityTheory.Gal
theorem _root_.solution (x : Ω) (P : Ω → Prop) : IsClosed {τ : Ω ≃ₐ[F] Ω | P (τ x)} := by
  rw [← isOpen_compl_iff]
  exact isOpen_setOf_apply x (fun y => ¬ P y)
end ReciprocityTheory.Gal
