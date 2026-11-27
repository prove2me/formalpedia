-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_DefectConstZero_proof_37389bd635ce
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T04:55:10.737938+00:00
-- url     : https://prove2.me/submissions/97929df9-44ab-497c-abf8-d120834dc1aa

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsMahler
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PDefectConstZero

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
open MvPolynomial
noncomputable section
namespace GroundTheory.Heights₂.Heights
namespace DefectConstZero
theorem _root_.solution (h1 : DefectPoint.Statement) (h2 : MahlerZeroSpec.Statement) :
    DefectConstZero.Statement := by
  intro n δ h Z f u u' data hu hu'
  obtain ⟨c, hc, g, hg, hf⟩ := data.chow
  have hK : ∀ W ∈ Z.support, ∃ K : ℝ, ∀ v : Fin n → ℂ, linForm v ∉ W →
      eval (fun ij => v ij.2) (g W) ≠ 0 ∧
        Real.log ‖eval (fun ij => v ij.2) (g W)‖ - coneIntegral h W 0 (fsLog h v) = K :=
    fun W hW => h1 n h W (g W) (data.prime W hW) (hg W hW)
  choose! K hK using hK
  have key : ∀ v : Fin n → ℂ, IsAdmissible Z v →
      mahlerDefect h 0 Z f v = Real.log ‖c‖ + ∑ W ∈ Z.support, (Z W : ℝ) * K W := by
    intro v hv
    have hne : ∀ W ∈ Z.support, eval (fun ij => v ij.2) (g W) ≠ 0 := fun W hW => (hK W hW v (hv W hW)).1
    have hm : mahler h 0 (specFirst f v) = Real.log ‖eval (fun ij => v ij.2) f‖ := h2 n h f v
    unfold mahlerDefect cycleIntegral
    rw [hm, hf, map_mul, eval_C, map_prod, norm_mul, norm_prod]
    have hc' : ‖c‖ ≠ 0 := norm_ne_zero_iff.mpr hc
    have hp : ∀ W ∈ Z.support, ‖eval (fun ij => v ij.2) (g W ^ Z W)‖ ≠ 0 := by
      intro W hW
      rw [map_pow, norm_pow]
      exact pow_ne_zero _ (norm_ne_zero_iff.mpr (hne W hW))
    rw [Real.log_mul hc' (Finset.prod_ne_zero_iff.mpr hp), Real.log_prod hp, add_sub_assoc,
      ← Finset.sum_sub_distrib]
    congr 1
    refine Finset.sum_congr rfl fun W hW => ?_
    rw [map_pow, norm_pow, Real.log_pow, ← (hK W hW v (hv W hW)).2]
    ring
  rw [key u hu, key u' hu']
end DefectConstZero
end GroundTheory.Heights₂.Heights
