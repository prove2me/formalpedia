-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_CycleAverage_proof_3e1a1278ba82
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T04:54:40.975348+00:00
-- url     : https://prove2.me/submissions/c00fd537-598c-45bc-8107-160d0743ff3d

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsMahler
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_ChowDegree
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PCycleAverage
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_exists_degrees_of_chowFormCycle_5abcefad6b58


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
open MvPolynomial MeasureTheory
noncomputable section
namespace GroundTheory.Heights₂.Heights
namespace CycleAverage
theorem _root_.solution (h1 : ConeAverage.Statement) : CycleAverage.Statement := by
  intro n e δ h Z f hd
  obtain ⟨c, hc, g, hg, hf⟩ := hd.chow
  have hf0 : C c * ∏ W ∈ Z.support, g W ^ Z W ≠ 0 :=
    mul_ne_zero (C_ne_zero.mpr hc)
      (Finset.prod_ne_zero_iff.mpr fun W hW => pow_ne_zero _ (hg W hW).1)
  have hhom : IsMultiHomog δ (C c * ∏ W ∈ Z.support, g W ^ Z W) := hf ▸ hd.homog
  obtain ⟨δW, hδW, hsum⟩ :=
    exists_degrees_of_chowFormCycle (Nat.succ_pos e) Z c g hg hhom hf0
  have hW : ∀ W ∈ Z.support,
      IntegrableOn (fun v => coneIntegral h W e (fsLog h (nrmv h v))) (ballH h) ∧
        ⨍ v in ballH h, coneIntegral h W e (fsLog h (nrmv h v)) =
          -(δW W * (harmonic (n - 1) : ℝ)) / 2 :=
    fun W hm => h1 n e (δW W) h W (g W) (hd.prime W hm) (hg W hm) (hδW W hm)
  have hint : ∀ W ∈ Z.support,
      IntegrableOn (fun v => (Z W : ℝ) * coneIntegral h W e (fsLog h (nrmv h v))) (ballH h) :=
    fun W hm => (hW W hm).1.const_mul _
  unfold cycleIntegral
  refine ⟨integrable_finsetSum _ hint, ?_⟩
  rw [setAverage_eq, integral_finsetSum _ hint, Finset.smul_sum]
  have hterm : ∀ W ∈ Z.support,
      (volume.real (ballH h))⁻¹ • ∫ v in ballH h, (Z W : ℝ) * coneIntegral h W e (fsLog h (nrmv h v)) =
        (Z W : ℝ) * (-(δW W * (harmonic (n - 1) : ℝ)) / 2) := by
    intro W hm
    rw [integral_const_mul, ← (hW W hm).2, setAverage_eq, smul_eq_mul, smul_eq_mul]
    ring
  rw [Finset.sum_congr rfl hterm]
  have hδ : (δ : ℝ) = ∑ W ∈ Z.support, (Z W : ℝ) * (δW W : ℝ) := by
    rw [← hsum]; push_cast; rfl
  rw [hδ, Finset.sum_mul, ← Finset.sum_neg_distrib, Finset.sum_div]
  refine Finset.sum_congr rfl fun W _ => ?_
  ring
end CycleAverage
end GroundTheory.Heights₂.Heights
