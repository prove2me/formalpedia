-- Prove2me | solution 1 for ReciprocityTheory.Neutral.Cmp.isTorsionFree_zp_Kloc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T16:49:47.244966+00:00
-- url     : https://prove2.me/submissions/f2cc5744-8b05-4a01-b272-dde3b5627186

import Definitions.Def_ReciprocityTheory_NeutralLocalFields_LocalFieldComparison_LocalFieldAutomorphisms_ModelA
import Definitions.Def_ReciprocityTheory_NeutralLocalFields_LocalFieldComparison_LocalFieldAutomorphisms_Inertia
import Definitions.Def_ReciprocityTheory_NeutralLocalFields_LocalFieldComparison_LocalFieldAutomorphisms_ModelF

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.Neutral ReciprocityTheory.Neutral.Cmp
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain ValuativeRel
variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] {p : ℕ} [Fact p.Prime]
attribute [local instance] locRel
attribute [local instance] zpAlgInteger
namespace ReciprocityTheory.Neutral.Cmp
theorem _root_.solution (ι : Ω →+* PadicAlgCl p) : Module.IsTorsionFree ℤ_[p] (Kloc F ι) := by
  refine Module.IsTorsionFree.of_smul_eq_zero fun r m h => ?_
  rw [Algebra.smul_def, mul_eq_zero] at h
  refine h.imp (fun h => ?_) id
  rw [IsScalarTower.algebraMap_apply ℤ_[p] ℚ_[p] (Kloc F ι), map_eq_zero] at h
  exact PadicInt.ext (by simpa using h)
end ReciprocityTheory.Neutral.Cmp
