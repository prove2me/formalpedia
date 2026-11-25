-- Prove2me | solution 1 for PI.ParahoricIdxZ.W.idxStep
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:18:49.632221+00:00
-- url     : https://prove2.me/submissions/9bb8d5fa-d446-449b-ba5c-5ec97116505b

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ParahoricIndexCount_ParamInjective
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ParahoricIndexCount_IdxStep
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_GLRed_ker_red
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_GLRed_red_surj
import Theorems.Thm_PI_ParahoricIdxZ_W_card_range_redJ
import Theorems.Thm_PI_ParahoricIdxZ_W_cong_blockCond
import Theorems.Thm_PI_ParahoricIdxZ_W_image_eq
import Theorems.Thm_PI_ParahoricIdxZ_W_param_injective


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Formalism.DoubleCosetMeasures.P.GLRed
open PI PI.ParahoricIdxZ PI.ParahoricIdxZ.W
namespace PI.ParahoricIdxZ.W
theorem _root_.solution : IdxStep := by
  intro F _ O ϖ hϖ hϖ0 hloc hfin a t J' hKJ hJint J hJ
  have := hfin
  set H := J.subgroupOf (Formalism.DoubleCosetMeasures.GLint O (a + t)) with hH
  have hker : (red O (a + t) ϖ hϖ).ker ≤ H := by
    rw [ker_red O ϖ hϖ hϖ0]
    intro g hg
    rw [Subgroup.mem_subgroupOf] at hg ⊢
    exact (hJ _).2 (cong_blockCond O hϖ hϖ0 hloc hKJ hg)
  have hidx := Subgroup.index_map_eq H (red_surj O (a + t) ϖ hϖ hloc) hker
  have hcm := Subgroup.card_mul_index (H.map (red O (a + t) ϖ hϖ))
  have hcard : Nat.card (H.map (red O (a + t) ϖ hϖ)) =
      Nat.card (J' ⧸ (Formalism.DoubleCosetMeasures.congSub O ϖ a).subgroupOf J') *
        (Nat.card (Formalism.DoubleCosetMeasures.kF O ϖ hϖ) ^ (a * t) * Nat.card (GL (Fin t) (Formalism.DoubleCosetMeasures.kF O ϖ hϖ))) := by
    have e1 : Nat.card (H.map (red O (a + t) ϖ hϖ)) =
        Nat.card ((fun g : GL (Fin (a + t)) (Formalism.DoubleCosetMeasures.kF O ϖ hϖ) =>
          (g : Matrix (Fin (a + t)) (Fin (a + t)) (Formalism.DoubleCosetMeasures.kF O ϖ hϖ))) ''
            ((H.map (red O (a + t) ϖ hϖ) : Subgroup _) : Set _)) :=
      (Nat.card_image_of_injective Units.val_injective _).symm
    have e2 : Nat.card (Matrix (Fin a) (Fin t) (Formalism.DoubleCosetMeasures.kF O ϖ hϖ)) =
        Nat.card (Formalism.DoubleCosetMeasures.kF O ϖ hϖ) ^ (a * t) := by
      show Nat.card (Fin a → Fin t → Formalism.DoubleCosetMeasures.kF O ϖ hϖ) = _
      rw [Nat.card_fun, Nat.card_fun, Nat.card_fin, Nat.card_fin, ← pow_mul, mul_comm]
    rw [e1, image_eq O hϖ hϖ0 hloc J' hJint J hJ,
      Nat.card_range_of_injective (param_injective (t := t) O hϖ J' hJint),
      Nat.card_prod, Nat.card_prod, card_range_redJ O ϖ hϖ hϖ0 J' hJint, e2]
  rw [← hcm, ← hidx, hcard]
  ring
end PI.ParahoricIdxZ.W
