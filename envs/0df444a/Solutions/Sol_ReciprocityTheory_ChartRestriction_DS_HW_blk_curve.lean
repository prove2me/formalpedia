-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.HW.blk_curve
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:38:51.327272+00:00
-- url     : https://prove2.me/submissions/b0f00bac-532c-4643-961e-52826dec3d6c

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_ContinuousRepresentations_DerivExistsAllPosStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_OneParam
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_ContinuousRepresentations_Blocks
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_HW_toMK_blkEmbed
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_HW_exp_blk
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_HW_onep_KG_ext


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Topology
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.HW
open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7
variable {n : ℕ}
namespace ReciprocityTheory.ChartRestriction.DS.HW
theorem _root_.solution {ε : Fin n → Bool} {X : Matrix (Fin n) (Fin n) ℂ} (hX : inK ε X)
    (γ : ℝ → KG ε) (hγ : ∀ t : ℝ, toMK (γ t) = NormedSpace.exp ((t : ℂ) • X))
    (γp : ℝ → KG (fun _ : Fin (blkP ε true) => true))
    (hp : ∀ t : ℝ, toMK (γp t) = NormedSpace.exp ((t : ℂ) • blkRes ε true X))
    (γm : ℝ → KG (fun _ : Fin (blkP ε false) => true))
    (hm : ∀ t : ℝ, toMK (γm t) = NormedSpace.exp ((t : ℂ) • blkRes ε false X)) (t : ℝ) :
    γ t = blkEmbed ε true (γp t) * blkEmbed ε false (γm t) := by
  apply onep_KG_ext
  have hX' : ((t : ℂ) • X) * Jm ε = Jm ε * ((t : ℂ) • X) := by
    rw [Matrix.smul_mul, hX.2, Matrix.mul_smul]
  show toMK (γ t) = toMK (blkEmbed ε true (γp t)) * toMK (blkEmbed ε false (γm t))
  rw [toMK_blkEmbed, toMK_blkEmbed, hγ, hp, hm, exp_blk hX', map_smul, map_smul]
end ReciprocityTheory.ChartRestriction.DS.HW
