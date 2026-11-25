-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_TubeDeepRankOne_mdisc_vecMulVec_be2ffc9f6b9b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T05:22:34.352163+00:00
-- url     : https://prove2.me/submissions/f1e72f73-3c6c-4d7e-b602-2655e71f62b7

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_LintegralImageEqLintegralNormSqDetMul
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PartsAlg
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_HessCIsHermitian
import Definitions.Def_ReciprocityTheory_AnalyticForms_AnalyticCharts_Osgood
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PMaDensLeibniz
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StTubeDeepRankOne
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PTubeDeepRankOne
import Theorems.Thm_ReciprocityTheory_AnForm_A_mdisc_eq_sum_perm


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
theorem _root_.solution {D : ℕ} (u : Fin D → Fin D → ℂ) :
    mdisc (fun k => vecMulVec (u k) (star (u k))) =
      (1 / (D.factorial : ℂ)) * (Complex.normSq (Matrix.of u).det : ℂ) := by
  rw [mdisc_eq_sum_perm]
  congr 1
  have hterm : ∀ σ : Equiv.Perm (Fin D),
      (Matrix.of fun i j => vecMulVec (u (σ j)) (star (u (σ j))) i j).det =
        (Matrix.of u).det * ((Equiv.Perm.sign σ : ℤ) * ∏ j, star (u (σ j) j)) := by
    intro σ
    have h1 : (Matrix.of fun i j => vecMulVec (u (σ j)) (star (u (σ j))) i j) =
        Matrix.of fun i j => (fun j => star (u (σ j) j)) j * ((Matrix.of u)ᵀ.submatrix id σ) i j := by
      ext i j
      simp [vecMulVec_apply, mul_comm]
    rw [h1, det_mul_row, det_permute', det_transpose]
    ring
  simp_rw [hterm]
  rw [← Finset.mul_sum]
  have hconj : ∑ σ : Equiv.Perm (Fin D), ((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ j, star (u (σ j) j) =
      starRingEnd ℂ (Matrix.of u).det := by
    rw [RingHom.map_det, det_apply']
    rfl
  rw [hconj, Complex.mul_conj]
end GroundTheory.Heights₂.Heights.TubeDeepRankOne
