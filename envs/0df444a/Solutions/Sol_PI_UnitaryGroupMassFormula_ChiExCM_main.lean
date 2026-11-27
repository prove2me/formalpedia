-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.ChiExCM.main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T05:16:47.382916+00:00
-- url     : https://prove2.me/submissions/2ad09153-1f06-47b9-966c-6e772fbfb2da

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_ChiExCM
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_CharExtend
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_NormOneCharacters_NormOneCharacterApply
import Theorems.Thm_PI_UnitaryGroupMassFormula_ChiExCM_lam_apply
import Theorems.Thm_PI_UnitaryGroupMassFormula_ChiExCM_ker_le
import Theorems.Thm_PI_UnitaryGroupMassFormula_ChiExCM_normOne_character_apply
import Theorems.Thm_PI_character_extension_exists


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.ChiExCM
open NumberField
namespace PI.UnitaryGroupMassFormula.ChiExCM
theorem _root_.solution : PI.ChiExCM := by
  intro E _ _ c hc S _ emb hμ
  classical
  obtain ⟨ψ, hψ⟩ := PI.character_extension_exists (Submodule (𝓞 E) E)ˣ (iota c).range (chi0 c S emb (ker_le c hc S emb hμ))
  refine ⟨fun 𝔞 => if h : IsUnit 𝔞 then ((ψ h.unit : ℂˣ) : ℂ) else 0, ?_, ?_⟩
  · rintro 𝔞 𝔟 ⟨𝔞', -, h𝔞⟩ ⟨𝔟', -, h𝔟⟩
    have ha : IsUnit 𝔞 := IsUnit.of_mul_eq_one _ h𝔞
    have hb : IsUnit 𝔟 := IsUnit.of_mul_eq_one _ h𝔟
    have hab : IsUnit (𝔞 * 𝔟) := ha.mul hb
    have e : hab.unit = ha.unit * hb.unit := Units.ext rfl
    simp only [dif_pos hab, dif_pos ha, dif_pos hb, e, map_mul, Units.val_mul]
  · intro z hz
    let u : Eˣ := Units.mkOfMulEqOne z (c z) hz
    have hu : u ∈ normOne c := hz
    have hval : ((iota c ⟨u, hu⟩ : (Submodule (𝓞 E) E)ˣ) : Submodule (𝓞 E) E) = Submodule.span (𝓞 E) {z} := rfl
    have hunit : IsUnit (Submodule.span (𝓞 E) {z}) := hval ▸ (iota c ⟨u, hu⟩).isUnit
    have e : hunit.unit = iota c ⟨u, hu⟩ := Units.ext hval.symm
    simp only [dif_pos hunit, e]
    rw [hψ ⟨iota c ⟨u, hu⟩, MonoidHom.mem_range.2 ⟨⟨u, hu⟩, rfl⟩⟩, normOne_character_apply, lam_apply]
    rfl
end PI.UnitaryGroupMassFormula.ChiExCM
