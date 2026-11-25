-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_term_le_of_hessC_72071bf85ca1
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T08:40:29.97128+00:00
-- url     : https://prove2.me/submissions/93a50de1-b8fd-4b7c-9fb0-a8cd0f501047

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StCutOffGradient
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StLogLogCutHess
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PFibreBound
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_MdiscSt
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_CovLog
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PCutOffGradient
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_maDens_cons_of_hessC_eq_smul_1613fdd029d0

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
variable {n d : ℕ}
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution {D : ℕ} {X : Type*} (B : Set X) (w t : X → ℝ) (x : X)
    (hw : |w x| ≤ 1) (hwB : x ∉ B → w x = 0) (ht : 0 ≤ t x) (f g : (Fin (D + 1) → ℂ) → ℝ)
    (ψ : Fin D → (Fin (D + 1) → ℂ) → ℝ) (y : Fin (D + 1) → ℂ) {c e : ℝ}
    (h : hessC f y = (e : ℂ) • hessC g y) (he : |e| ≤ c * t x) :
    |w x * maDens (Fin.cons f ψ) y| ≤ c * |B.indicator t x * maDens (Fin.cons g ψ) y| := by
  rw [maDens_cons_of_hessC_eq_smul f g ψ y e h]
  by_cases hx : x ∈ B
  · rw [Set.indicator_of_mem hx, abs_mul, abs_mul, abs_mul, abs_of_nonneg ht]
    have hM := abs_nonneg (maDens (Fin.cons g ψ) y)
    calc |w x| * (|e| * |maDens (Fin.cons g ψ) y|) ≤ 1 * (c * t x * |maDens (Fin.cons g ψ) y|) :=
          mul_le_mul hw (mul_le_mul_of_nonneg_right he hM) (by positivity) zero_le_one
      _ = c * (t x * |maDens (Fin.cons g ψ) y|) := by ring
  · rw [hwB hx, zero_mul, abs_zero, Set.indicator_of_notMem hx, zero_mul, abs_zero, mul_zero]
end GroundTheory.Heights₂.Heights
