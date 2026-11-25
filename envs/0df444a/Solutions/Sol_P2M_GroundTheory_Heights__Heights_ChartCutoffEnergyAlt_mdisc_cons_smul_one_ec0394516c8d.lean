-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ChartCutoffEnergyAlt_mdisc_cons_smul_one_ec0394516c8d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T02:36:38.613613+00:00
-- url     : https://prove2.me/submissions/df898f47-e0d7-4bc5-9515-63e5cdcc23ef

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_MdiscSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsChartCutoffEnergy
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PChartHessCompare
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PHermFormCompare
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PChartCutoffEnergy
import Theorems.Thm_ReciprocityTheory_AnForm_A_exists_multilinearMap_eq_mdisc
import Theorems.Thm_ReciprocityTheory_AnForm_A_mdisc_const


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.AnForm Matrix MeasureTheory Filter
open scoped ComplexOrder
noncomputable section
open GroundTheory.Heights₂.Heights.ChartCutoffEnergyAlt
open ReciprocityTheory.AnForm.A
namespace GroundTheory.Heights₂.Heights.ChartCutoffEnergyAlt
theorem _root_.solution {n : ℕ} (l m : ℂ) :
    mdisc (Fin.cons (l • (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ))
      (fun _ : Fin n => m • (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)) :
        Fin (n + 1) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) = l * m ^ n := by
  obtain ⟨f, hf⟩ := exists_multilinearMap_eq_mdisc (D := n + 1)
  have h : (Fin.cons (l • (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ))
      (fun _ : Fin n => m • (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)) :
        Fin (n + 1) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) =
      fun i => (Fin.cons l (fun _ : Fin n => m) : Fin (n + 1) → ℂ) i • (fun _ => (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)) i := by
    funext i
    refine Fin.cases ?_ (fun i => ?_) i <;> simp
  rw [h, ← hf, f.map_smul_univ, hf, mdisc_const, det_one, Fin.prod_cons]
  simp
end GroundTheory.Heights₂.Heights.ChartCutoffEnergyAlt
