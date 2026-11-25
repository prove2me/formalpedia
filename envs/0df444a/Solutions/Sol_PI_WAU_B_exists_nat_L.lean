-- Prove2me | solution 1 for PI.WAU.B.exists_nat_L
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T11:05:01.980993+00:00
-- url     : https://prove2.me/submissions/6d1a8977-bd46-4307-9448-3fcb4578d193

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_GlobAut
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicUnimodularity_ExistsNatLocal
import Definitions.Def_Lemmata_NatMulIsIntegral_ExistsNatMulIsIntegral
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicUnimodularity_ExistsNatVec
import Theorems.Thm_Bl_NatMulIsIntegral_goal1


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
theorem _root_.solution {L : Submodule (𝓞 E) (Fin n → E)}
    {z : Fin n → E} (hz : z ∈ Submodule.span E (L : Set (Fin n → E))) :
    ∃ N : ℕ, 0 < N ∧ N • z ∈ L := by
  first | exact Bl.NatMulIsIntegral.goal1 .. | (apply Bl.NatMulIsIntegral.goal1 <;> assumption) | (intros; apply Bl.NatMulIsIntegral.goal1 <;> assumption)
end PI.WAU.B
