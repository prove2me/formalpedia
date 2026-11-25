-- Prove2me | solution 1 for PI.WAU.B.lam_sub_alt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:13:25.336095+00:00
-- url     : https://prove2.me/submissions/77842249-4e8b-4fc7-94b7-73ec5f2e0959

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_GlobAut
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicUnimodularity_ExistsNatLocal
import Definitions.Def_Lemmata_NatMulIsIntegral_ExistsNatMulIsIntegral
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicUnimodularity_ExistsNatVec
import Theorems.Thm_PI_WAU_B_T_zero
import Theorems.Thm_PI_WAU_B_T_add
import Theorems.Thm_PI_WAU_B_T_gen
import Theorems.Thm_PI_WAU_B_T_smulO

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
variable {k : ℕ} {m : Fin k → Fin n → E}
namespace PI.WAU.B
theorem _root_.solution {L : Submodule (𝓞 E) (Fin n → E)} (hm : ∀ i, m i ∈ L)
    (hgen : ∀ l ∈ L, ∃ z : Fin k → ℤ, l = ∑ i, z i • m i) {w : Fin n → E ⊗[F] Af F}
    (hw : w ∈ lamAf (F := F) L) : w ∈ Tset (F := F) m := by
  induction hw using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨⟨y, hy⟩, rfl⟩ := hx
    exact T_gen hgen hy
  | zero => exact T_zero
  | add x y _ _ hx hy => exact T_add hx hy
  | smul o x _ hx => exact T_smulO hm hgen o.2 x hx
end PI.WAU.B
