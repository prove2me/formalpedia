-- Prove2me | solution 1 for StochSchedPrec.InForest.lp_relaxation
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-05T16:52:48.030227+00:00
-- url     : https://prove2.me/submissions/4288d7d7-98ba-4ae0-86a5-1528436f5063
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_StochSchedPrec_InForest_Model
import Definitions.Def_StochSchedPrec_InForest_LP
import Theorems.Thm_StochSchedPrec_InForest_theorem_3_1
open MeasureTheory ProbabilityTheory

open StochSchedPrec.InForest in
theorem solution {V : Type*} [Fintype V] [DecidableEq V]
    {Ω : Type*} [MeasurableSpace Ω] {Pr : Measure Ω} [IsProbabilityMeasure Pr]
    (m : ℕ) (hm : 0 < m) (A : V → V → Prop) (hacyc : IsAcyclic A)
    (w : V → ℝ) (hw : ∀ j, 0 ≤ w j)
    (P : V → Ω → ℝ) (hP : IsStochProcTimes P Pr) (Δ : ℝ) (hCV : CVBound P Pr Δ)
    (pol : (V → ℝ) → (V → ℝ)) (hpol : IsComparator A m P Pr pol) :
    IsLPFeasible (fun j => ∫ ω, P j ω ∂Pr) A m Δ
        (fun j => ∫ ω, (pol (fun k => P k ω) j + P j ω) ∂Pr) ∧
      ∑ j, w j * ∫ ω, (pol (fun k => P k ω) j + P j ω) ∂Pr =
        ∫ ω, (∑ j, w j * (pol (fun k => P k ω) j + P j ω)) ∂Pr := by
  have hPint : ∀ j, Integrable (P j) Pr := fun j => (hCV.2.1 j).integrable (by norm_num)
  have hnn : ∀ ω, IsNonneg (fun k => P k ω) := fun ω k => hP.2.1 k ω
  have hfeas : ∀ ω, IsFeasibleSchedule A m (fun k => P k ω) (pol (fun k => P k ω)) :=
    fun ω => hpol.1.1 _ (hnn ω)
  refine ⟨⟨fun W => theorem_3_1 m hm A hacyc P hP Δ hCV pol hpol W, ?_, ?_⟩, ?_⟩
  · intro i j hij
    -- C_i + P_j ≤ C_j pointwise
    have hpt : ∀ ω, (pol (fun k => P k ω) i + P i ω) + P j ω ≤
        pol (fun k => P k ω) j + P j ω := fun ω => by
      have := (hfeas ω).2.1 i j hij
      linarith
    have h1 := integral_mono ((hpol.2 i).add (hPint j)) (hpol.2 j) hpt
    have h2 : ∫ ω, ((pol (fun k => P k ω) i + P i ω) + P j ω) ∂Pr =
        ∫ ω, (pol (fun k => P k ω) i + P i ω) ∂Pr + ∫ ω, P j ω ∂Pr :=
      integral_add (hpol.2 i) (hPint j)
    show ∫ ω, (pol (fun k => P k ω) i + P i ω) ∂Pr + ∫ ω, P j ω ∂Pr ≤
      ∫ ω, (pol (fun k => P k ω) j + P j ω) ∂Pr
    rw [← h2]
    exact h1
  · intro j
    refine integral_mono (hPint j) (hpol.2 j) fun ω => ?_
    have := (hfeas ω).1 j
    simp only
    linarith
  · rw [integral_finset_sum _ (fun j _ => (hpol.2 j).const_mul (w j))]
    exact Finset.sum_congr rfl fun j _ => (integral_const_mul _ _).symm
