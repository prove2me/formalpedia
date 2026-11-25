-- Prove2me | solution 1 for PI.CharIdemW.trace_act_charIdem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T09:43:03.213557+00:00
-- url     : https://prove2.me/submissions/7aa7e56d-c3d3-4056-a49c-00cafa8d8f41

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_CharIdem
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CharacterIdempotents_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CharacterIdempotents_Scalar
import Theorems.Thm_PI_CharIdemW_act_charIdem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory
open PI PI.CharIdemW
open PI.CharIdem
variable {G : Type} [Group G] [Fintype G]
open scoped Classical
namespace PI.CharIdemW
theorem _root_.solution (V W : FDRep ℂ G) [Simple V] [Simple W] :
    LinearMap.trace ℂ W (act W (charIdem V)) =
      (Module.finrank ℂ V : ℂ) * (if Nonempty (W ≅ V) then (1 : ℂ) else 0) := by
  have : Invertible ((Nat.card G : ℂ)) := invertibleOfNonzero
    (Nat.cast_ne_zero.mpr (by rw [Nat.card_eq_fintype_card]; exact Fintype.card_ne_zero))
  have horth := FDRep.char_orthonormal W V
  rw [Nat.card_eq_fintype_card] at horth
  rw [act_charIdem, map_sum]
  simp only [map_smul, smul_eq_mul]
  have h1 : ∀ x : G, (Module.finrank ℂ V : ℂ) / (Fintype.card G : ℂ) * V.character x⁻¹ *
      LinearMap.trace ℂ W (W.ρ x) = (Module.finrank ℂ V : ℂ) *
        ((Fintype.card G : ℂ)⁻¹ * (W.character x * V.character x⁻¹)) := fun x => by
    rw [show LinearMap.trace ℂ W (W.ρ x) = W.character x from rfl]
    ring
  rw [Finset.sum_congr rfl (fun x _ => h1 x), ← Finset.mul_sum, ← Finset.mul_sum, horth]
end PI.CharIdemW
