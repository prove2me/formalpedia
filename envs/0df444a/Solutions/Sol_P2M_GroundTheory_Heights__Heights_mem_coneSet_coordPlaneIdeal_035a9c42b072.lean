-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_mem_coneSet_coordPlaneIdeal_035a9c42b072
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T08:51:25.927101+00:00
-- url     : https://prove2.me/submissions/6233ee98-56aa-4ad9-989b-8771f7fcced2

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsConeFibreAverage
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PConeIntegralMass
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LogIntPoly
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PPointLine
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PConeMassOfFibre
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_pointOf_std_30aaec238417

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
open MvPolynomial MeasureTheory Module
open scoped ENNReal
noncomputable section
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution {m k : ℕ} (y : EuclideanSpace ℂ (Fin (m + k))) :
    y ∈ coneSet (HermNorm.std (m + k)) (coordPlaneIdeal m k) ↔
      ∀ j : Fin (m + k), m ≤ (j : ℕ) → y j = 0 := by
  simp only [coneSet, Set.mem_ofPred_eq, pointOf_std]
  constructor
  · intro hy j hj
    obtain ⟨i, rfl⟩ : ∃ i : Fin k, j = Fin.natAdd m i :=
      ⟨⟨j - m, by omega⟩, by ext; simp; omega⟩
    have hX : (X (Fin.natAdd m i) : MvPolynomial (Fin (m + k)) ℂ) ∈ coordPlaneIdeal m k := by
      rw [coordPlaneIdeal, RingHom.mem_ker, aeval_X, coordPlaneSubst, Fin.append_right]
    simpa using hy _ hX
  · intro hy q hq
    rw [coordPlaneIdeal, RingHom.mem_ker] at hq
    set x : Fin m → ℂ := fun i => y (Fin.castAdd k i)
    have hyx : (fun i => y i) = fun j => eval x (coordPlaneSubst m k j) := by
      funext j
      refine Fin.addCases (fun i => ?_) (fun i => ?_) j
      · simp [coordPlaneSubst, x]
      · simp [coordPlaneSubst, hy (Fin.natAdd m i) (by simp)]
    have hev : eval (fun j => eval x (coordPlaneSubst m k j)) q =
        eval x (aeval (coordPlaneSubst m k) q) := by
      rw [← coe_aeval_eq_eval, ← coe_aeval_eq_eval, aeval_eq_bind₁]
      exact (aeval_bind₁ x (coordPlaneSubst m k) q).symm
    rw [hyx, hev, hq, map_zero]
end GroundTheory.Heights₂.Heights
