-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.LCG.dualL_oLat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:41:03.311902+00:00
-- url     : https://prove2.me/submissions/7d50cb96-b934-4dd0-99b0-6e7c70f3a83e

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeCountingBound_IndexDefs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeCountingBound_IndexOf
import Theorems.Thm_PI_UnitaryGroupMassFormula_LCG_mem_oLat
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
open NumberField Matrix
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.LCG
variable {E : Type} [Field E] [NumberField E]
namespace PI.UnitaryGroupMassFormula.LCG
theorem _root_.solution (k : ℕ) : dualL (oLat E k) = oLat E k := by
  ext t
  constructor
  · intro ht
    have ht' : ∀ s ∈ oLat E k, s ⬝ᵥ t ∈ (algebraMap (𝓞 E) E).range := ht
    have h1 : ∀ c, t c ∈ (algebraMap (𝓞 E) E).range := by
      intro c
      have hs : (Pi.single c 1 : Fin k → E) ∈ oLat E k := by
        rw [mem_oLat]
        exact ⟨Pi.single c 1, by funext d; by_cases h : d = c <;> simp [Pi.single_apply, h]⟩
      have := ht' _ hs
      simpa [dotProduct, Pi.single_apply] using this
    choose x hx using fun c => RingHom.mem_range.mp (h1 c)
    rw [mem_oLat]
    exact ⟨x, funext hx⟩
  · intro ht
    show ∀ s ∈ oLat E k, s ⬝ᵥ t ∈ (algebraMap (𝓞 E) E).range
    intro s hs
    obtain ⟨x, rfl⟩ := (mem_oLat t).mp ht
    obtain ⟨y, rfl⟩ := (mem_oLat s).mp hs
    refine RingHom.mem_range.mpr ⟨∑ c, y c * x c, ?_⟩
    simp [dotProduct, map_sum, map_mul]
end PI.UnitaryGroupMassFormula.LCG
