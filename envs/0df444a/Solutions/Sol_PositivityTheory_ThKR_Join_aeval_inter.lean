-- Prove2me | solution 1 for PositivityTheory.ThKR.Join.aeval_inter
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T14:10:08.31793+00:00
-- url     : https://prove2.me/submissions/6b006ba4-7237-4d63-a482-adca2104657b

import Definitions.Def_Development_WeilBound_ThetaLifts_CartanFactorisation_ExistsGreatestProperInvariantSubmoduleOfSide
import Definitions.Def_Development_WeilBound_ThetaLifts_Reductions_LocalPoly

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory.ThetaSummability.Real ReciprocityTheory.ChartRestriction.G.ThK.Real FockH1Action MvPolynomial Matrix
open scoped InnerProductSpace
open PositivityTheory PositivityTheory.ThKR PositivityTheory.ThKR.Join
open PositivityTheory.KReal PositivityTheory.ThKF.Unit
namespace PositivityTheory.ThKR.Join
theorem _root_.solution {V M : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup M] [Module ℂ M] (j : V →ₗ[ℂ] M)
    (T : Module.End ℂ V) (C : Module.End ℂ M) (h : ∀ y, j (T y) = C (j y)) (g : Polynomial ℂ) (y : V) :
    j (Polynomial.aeval T g y) = Polynomial.aeval C g (j y) := by
  have hp : ∀ (n : ℕ) y, j ((T ^ n) y) = (C ^ n) (j y) := fun n => by
    induction n with
    | zero => intro y; simp
    | succ n ih => intro y; rw [pow_succ, pow_succ, Module.End.mul_apply, Module.End.mul_apply, ih, h]
  induction g using Polynomial.induction_on' with
  | add p q hp hq => simp [hp, hq]
  | monomial n a => simp [Polynomial.aeval_monomial, hp]
end PositivityTheory.ThKR.Join
