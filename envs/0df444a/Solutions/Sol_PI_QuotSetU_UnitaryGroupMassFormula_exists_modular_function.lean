-- Prove2me | solution 1 for PI.QuotSetU.UnitaryGroupMassFormula.exists_modular_function
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:26:49.332159+00:00
-- url     : https://prove2.me/submissions/0c4bbf80-0570-454e-9400-83a4c0d8c01a

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryQuotientCompactness_ModCore
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryQuotientCompactness_ExistsModularFunction
import Theorems.Thm_PI_QuotSetU_UnitaryGroupMassFormula_ModW_isClosedEmbedding_val
import Theorems.Thm_PI_QuotSetU_UnitaryGroupMassFormula_ModW_modF_bdd
import Theorems.Thm_PI_QuotSetU_UnitaryGroupMassFormula_ModW_modF_conj
import Theorems.Thm_PI_QuotSetU_UnitaryGroupMassFormula_ModW_rightInv_of


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix Topology
open scoped ENNReal NNReal
noncomputable section
open PI PI.QuotSetU PI.QuotSetU.UnitaryGroupMassFormula
open PI ModW ModW.MG
namespace PI.QuotSetU.UnitaryGroupMassFormula
theorem _root_.solution : ModExists := by
  intro m G hG
  refine ⟨modFun G hG, ⟨?_, ?_, ?_, ?_⟩, ?_⟩
  ·
    intro g hg
    simp only [modFun, dif_pos hg]
    exact_mod_cast Measure.modularCharacterFun_pos (mk hG g hg)
  ·
    intro a ha b hb
    have hab : a * b ∈ G := hG.2.2.1 a ha b hb
    simp only [modFun, dif_pos ha, dif_pos hb, dif_pos hab]
    have hmk : mk hG (a * b) hab = mk hG a ha * mk hG b hb := by
      ext1
      simp only [toM_mk, toM_mul]
    rw [hmk]
    have h := (Measure.modularCharacter (G := MG G hG)).map_mul (mk hG a ha) (mk hG b hb)
    exact_mod_cast h
  ·
    intro c hc hcG g hg
    have hcg : c * g * c⁻¹ ∈ G := (hcG g).2 hg
    simp only [modFun, dif_pos hg, dif_pos hcg]
    have hmk : mk hG (c * g * c⁻¹) hcg = conjE c hc hcG (mk hG g hg) := by
      ext1
      rfl
    rw [hmk, modF_conj]
  ·
    intro V hVG hV
    have hK : IsCompact ((fun y : MtM m => Matrix.of y) ⁻¹' V) := hV
    have hW : IsCompact ((val : MG G hG → MtM m) ⁻¹' ((fun y : MtM m => Matrix.of y) ⁻¹' V)) :=
      isClosedEmbedding_val.isCompact_preimage hK
    obtain ⟨M, hM⟩ := modF_bdd _ hW
    refine ⟨M, fun v hv => ?_⟩
    have hvG : v ∈ G := hVG hv
    simp only [modFun, dif_pos hvG]
    apply hM
    show Matrix.of (mk hG v hvG).1 ∈ V
    exact hv
  ·
    intro h1 μ hμ
    refine rightInv_of (hG := hG) μ hμ (fun g => ?_)
    have hg := h1 g.toM g.toM_mem
    simp only [modFun, dif_pos g.toM_mem, mk_toM] at hg
    exact_mod_cast hg
end PI.QuotSetU.UnitaryGroupMassFormula
