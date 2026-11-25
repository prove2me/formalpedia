-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.S7.Ps1.continuousOn_GintD
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:20:19.131444+00:00
-- url     : https://prove2.me/submissions/bb601638-0e34-4cf9-875e-fbbf04ecf038

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_IsClosedKset
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_KFacts
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_PhiFacts
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_ContinuousOnFderivPhiP
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_Ps1_continuousOn_fderiv_phiP
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_DS_S7_Ps1_continuous_toMK__f840e4671769
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_Ps1_continuous_toMK_inv
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_Ps1_continuous_conj
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_Ps1_continuous_P
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_Ps1_GintD_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset MeasureTheory Matrix
open scoped ComplexOrder ContDiff ENNReal
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7
open ReciprocityTheory.ChartRestriction.DS
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ}
open ReciprocityTheory.ChartRestriction.DS.S7.Ps1
local notation "𝕄" => Fin n → Fin n → ℂ
variable {ε : Fin n → Bool} {Λ : Fin n → ℝ}
namespace ReciprocityTheory.ChartRestriction.DS.S7.Ps1
theorem _root_.solution (T : KType ε Λ) (μ : Fin n → ℤ) :
    ContinuousOn (fun p : Matrix (Fin n) (Fin n) ℂ × KG ε => GintD T μ p.1 p.2)
      (Uset ε ×ˢ Set.univ) := by
  refine continuousOn_clm_apply.mpr fun H => ?_
  have hmaps : Set.MapsTo (fun p : Matrix (Fin n) (Fin n) ℂ × KG ε => toMK p.2⁻¹ * p.1 * toMK p.2)
      (Uset ε ×ˢ Set.univ) (OmegaSet n) := fun p hp => hp.1 p.2
  have hA : ContinuousOn (fun p : Matrix (Fin n) (Fin n) ℂ × KG ε =>
      fderiv ℂ (PhiP μ) (toMK p.2⁻¹ * p.1 * toMK p.2)) (Uset ε ×ˢ Set.univ) :=
    (continuousOn_fderiv_phiP μ).comp continuous_conj.continuousOn hmaps
  have hB : Continuous (fun p : Matrix (Fin n) (Fin n) ℂ × KG ε =>
      toMK p.2⁻¹ * Matrix.of H * toMK p.2) :=
    ((continuous_toMK_inv.comp continuous_snd).matrix_mul continuous_const).matrix_mul
      (continuous_toMK'.comp continuous_snd)
  refine ((hA.clm_apply hB.continuousOn).smul
    ((continuous_P T).comp continuous_snd).continuousOn).congr ?_
  intro p hp
  exact GintD_apply T μ p.2 (hp.1 p.2) H
end ReciprocityTheory.ChartRestriction.DS.S7.Ps1
