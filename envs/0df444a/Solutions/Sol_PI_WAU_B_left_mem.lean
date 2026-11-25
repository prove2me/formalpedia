-- Prove2me | solution 1 for PI.WAU.B.left_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T11:05:15.247798+00:00
-- url     : https://prove2.me/submissions/c1ac7e1f-2859-42c5-89f7-ad5ff409cc4e

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_GlobAut
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicUnimodularity_ExistsNatLocal
import Definitions.Def_Lemmata_NatMulIsIntegral_ExistsNatMulIsIntegral
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicUnimodularity_ExistsNatVec

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.WAU PI.WAU.B
open NumberField IsDedekindDomain Formalism.MainNotions.S Formalism.UG Matrix
open scoped TensorProduct
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}
namespace PI.WAU.B
theorem _root_.solution (t : 𝓞 E) : ((algebraMap (𝓞 E) E t) ⊗ₜ[F] (1 : Af F)) ∈ IntAf F E :=
  Subring.subset_closure (Or.inl ⟨⟨algebraMap (𝓞 E) E t, ⟨t, rfl⟩⟩, rfl⟩)
end PI.WAU.B
