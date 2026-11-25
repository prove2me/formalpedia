-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_TubeDeepRankOne_mdisc_cons_sum_a97f8b68dabd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T05:22:31.842335+00:00
-- url     : https://prove2.me/submissions/ea84b6ef-3a4c-4d52-822b-eabc07003f47

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_LintegralImageEqLintegralNormSqDetMul
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PartsAlg
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_HessCIsHermitian
import Definitions.Def_ReciprocityTheory_AnalyticForms_AnalyticCharts_Osgood
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PMaDensLeibniz
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StTubeDeepRankOne
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PTubeDeepRankOne
import Theorems.Thm_ReciprocityTheory_AnForm_A_exists_multilinearMap_eq_mdisc


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
open MvPolynomial Matrix ComplexSets ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A Filter Topology
noncomputable section
open GroundTheory.Heights₂.Heights.TubeDeepRankOne
namespace GroundTheory.Heights₂.Heights.TubeDeepRankOne
theorem _root_.solution {d n : ℕ} (A₀ : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ)
    (B : Fin n → Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ) :
    mdisc (Fin.cons A₀ (fun _ => ∑ m, B m) : Fin (d + 1) → Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ) =
      ∑ I : Fin d → Fin n,
        mdisc (Fin.cons A₀ (fun i => B (I i)) : Fin (d + 1) → Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ) := by
  obtain ⟨L, hL⟩ := exists_multilinearMap_eq_mdisc (D := d + 1)
  rw [← hL]
  have h := (L.curryLeft A₀).map_sum (fun (_ : Fin d) m => B m)
  simpa [MultilinearMap.curryLeft_apply] using h
end GroundTheory.Heights₂.Heights.TubeDeepRankOne
