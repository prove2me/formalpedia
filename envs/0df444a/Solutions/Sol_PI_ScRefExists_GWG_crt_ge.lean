-- Prove2me | solution 1 for PI.ScRefExists.GWG.crt_ge
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:19:51.182303+00:00
-- url     : https://prove2.me/submissions/59aa408a-4a1e-409c-b4c9-3686d8b02186

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeReferenceFrame_GlobWIff
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeReferenceFrame_HANegRight
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeReferenceFrame_GWGlue
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
noncomputable section
open NumberField Formalism.MainNotions.S IsDedekindDomain
open scoped TensorProduct
open PI PI.ScRefExists PI.ScRefExists.GWG
open PI.ScRefExists.Sk
variable (I : Formalism.MainNotions.S.AutInst)
namespace PI.ScRefExists.GWG
theorem _root_.solution {g₁ g₂ : ℕ} {A B q₁ q₂ : ℤ} (hq₁ : q₁ = g₂ * B) (hq₂ : q₂ = g₁ * A)
    {x X₁₁ X₁₂ X₂₂ : I.E} (h₁ : GE I g₁ X₁₁) (h₂ : GE I g₂ X₂₂)
    (h₁₂ : X₁₂ ∈ (algebraMap (𝓞 I.E) I.E).range)
    (hx : x = (q₁ : I.E) ^ 2 * X₁₁ + (q₁ : I.E) * (q₂ : I.E) * X₁₂ + (q₂ : I.E) ^ 2 * X₂₂) :
    GE I (g₁ * g₂) x := by
  obtain ⟨t1, ht1⟩ := h₁
  obtain ⟨t2, ht2⟩ := h₂
  obtain ⟨s, hs⟩ := h₁₂
  have hc : ∀ u : 𝓞 I.E, (u : I.E) = algebraMap (𝓞 I.E) I.E u := fun u => rfl
  refine ⟨(g₂ : 𝓞 I.E) * (B : 𝓞 I.E) ^ 2 * t1 + (B : 𝓞 I.E) * (A : 𝓞 I.E) * s +
    (g₁ : 𝓞 I.E) * (A : 𝓞 I.E) ^ 2 * t2, ?_⟩
  rw [hx, hq₁, hq₂, ht1, ht2, ← hs]
  simp only [hc, map_add, map_mul, map_pow, map_natCast, map_intCast]
  push_cast
  try ring
end PI.ScRefExists.GWG
