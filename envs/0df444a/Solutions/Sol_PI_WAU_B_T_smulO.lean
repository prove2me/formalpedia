-- Prove2me | solution 1 for PI.WAU.B.T_smulO
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T11:50:34.813656+00:00
-- url     : https://prove2.me/submissions/73235286-8a8f-4cdd-936a-5be4b165adc8

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_GlobAut
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicUnimodularity_ExistsNatLocal
import Definitions.Def_Lemmata_NatMulIsIntegral_ExistsNatMulIsIntegral
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicUnimodularity_ExistsNatVec
import Theorems.Thm_PI_WAU_B_T_zero
import Theorems.Thm_PI_WAU_B_T_add
import Theorems.Thm_PI_WAU_B_T_neg
import Theorems.Thm_PI_WAU_B_T_smulA
import Theorems.Thm_PI_WAU_B_T_smul_left

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
    (hgen : ∀ l ∈ L, ∃ z : Fin k → ℤ, l = ∑ i, z i • m i) {o : E ⊗[F] Af F}
    (ho : o ∈ IntAf F E) : ∀ w ∈ Tset (F := F) m, o • w ∈ Tset (F := F) m := by
  unfold IntAf tensInt at ho
  induction ho using Subring.closure_induction with
  | mem x hx =>
    rcases hx with ⟨⟨s, hs⟩, rfl⟩ | ⟨⟨a, ha⟩, rfl⟩
    · obtain ⟨t, rfl⟩ := hs
      intro w hw
      exact T_smul_left hm hgen t hw
    · intro w hw
      exact T_smulA ha hw
  | zero => intro w _; rw [zero_smul]; exact T_zero
  | one => intro w hw; rwa [one_smul]
  | add x y _ _ hx hy => intro w hw; rw [add_smul]; exact T_add (hx w hw) (hy w hw)
  | neg x _ hx => intro w hw; rw [neg_smul]; exact T_neg (hx w hw)
  | mul x y _ _ hx hy => intro w hw; rw [mul_smul]; exact hx _ (hy w hw)
end PI.WAU.B
