-- Prove2me | solution 1 for PositivityTheory.KReal.schur_countable
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T05:18:56.786435+00:00
-- url     : https://prove2.me/submissions/0f2dd203-bc37-4fb0-bab5-4e93e604e203

import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_TensorIrr
import Mathlib.LinearAlgebra.PiTensorProduct.Basis
import Mathlib.RingTheory.SimpleModule.Basic
import Mathlib.RingTheory.Algebraic.LinearIndependent
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.Complex.Cardinality
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_SpectrumNonemptyOfCountableRank
import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_Tensor
import Theorems.Thm_PositivityTheory_KReal_isAlgebraic_of_rank_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PositivityTheory PositivityTheory.KReal
namespace PositivityTheory.KReal
theorem _root_.solution {B V : Type} [Ring B] [Algebra ℂ B] [AddCommGroup V] [Module ℂ V] [Module B V]
    [IsScalarTower ℂ B V] [IsSimpleModule B V] (h : Module.rank ℂ V ≤ Cardinal.aleph0) :
    Function.Surjective (algebraMap ℂ (Module.End B V)) := by
  classical
  have : Nontrivial V := IsSimpleModule.nontrivial B V
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  let ev : Module.End B V →ₗ[ℂ] V :=
    { toFun := fun T => T v
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hev : Function.Injective ev := by
    rw [injective_iff_map_eq_zero]
    intro T hT
    by_contra h0
    exact hv ((LinearMap.injective_of_ne_zero h0) (by rw [map_zero]; exact hT))
  have hr : Module.rank ℂ (Module.End B V) ≤ Cardinal.aleph0 :=
    (LinearMap.rank_le_of_injective ev hev).trans h
  have : Algebra.IsAlgebraic ℂ (Module.End B V) := ⟨isAlgebraic_of_rank_le hr⟩
  have : Algebra.IsIntegral ℂ (Module.End B V) := Algebra.IsAlgebraic.isIntegral
  exact (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := ℂ)).2
end PositivityTheory.KReal
