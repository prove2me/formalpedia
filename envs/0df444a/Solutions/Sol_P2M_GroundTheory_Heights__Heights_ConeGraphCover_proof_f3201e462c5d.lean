-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ConeGraphCover_proof_f3201e462c5d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T04:53:14.148252+00:00
-- url     : https://prove2.me/submissions/ac9249fb-7165-48c3-855b-1b392f3b9b41

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsConeGraphCover
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsConeFiniteFibreDim
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsConeTangentDim
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsConeSmoothLocalGraph
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PNullSmaller
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PConeGraphCover
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_coneSet_hausdorff_null_of_dim_lt_8a4e1c11caea

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
open scoped ENNReal NNReal
noncomputable section
namespace GroundTheory.Heights₂.Heights
namespace ConeGraphCover
theorem _root_.solution (hDim : ConeFiniteFibreDim.Statement) (hTan : ConeTangentDim.Statement)
    (hLoc : ConeSmoothLocalGraph.Statement) : ConeGraphCover.Statement := by
  intro n m h J hJ hm hmn hfib
  have e0 : Fin n ≃ Fin m ⊕ Fin (n - m) :=
    (finCongr (Nat.add_sub_cancel' hmn).symm).trans finSumFinEquiv.symm
  rcases (hDim n m h J hJ hm hmn hfib).lt_or_eq with hlt | heq
  ·
    refine ⟨fun _ => e0, fun _ => ∅, fun _ => 0,
      fun _ => ⟨isOpen_empty, differentiableOn_empty, by simp, by simp⟩, ?_⟩
    exact measure_mono_null Set.sdiff_subset (coneSet_hausdorff_null_of_dim_lt h J m hlt)

  set S := {y | y ∈ coneSet h J ∧ finrank ℂ (coneTangent h J y) = m} with hSdef
  have hbad : Measure.hausdorffMeasure ((2 * m : ℕ) : ℝ) (coneSet h J \ S) = 0 := by
    have hae := hTan n m h J hJ hm hmn hfib
    rw [ae_iff] at hae
    refine measure_mono_null ?_ (nonpos_iff_eq_zero.1 ((Measure.le_restrict_apply _ _).trans hae.le))
    intro y hy
    exact ⟨fun h' => hy.2 ⟨hy.1, h'⟩, hy.1⟩

  have hloc := fun y (hy : y ∈ S) => hLoc n m h J hJ.isPrime heq y hy.1 hy.2
  have : Nonempty (Fin n ≃ Fin m ⊕ Fin (n - m)) := ⟨e0⟩
  choose! E Om Ph U hUo hyU hCU hΩ hΦ hG hT using hloc

  obtain ⟨T, hTS, hTc, hTU⟩ := TopologicalSpace.isOpen_biUnion_countable S U hUo
  have hScov : S ⊆ ⋃ y ∈ T, graphPt (E y) (Ph y) '' Om y := by
    intro y hy
    have hy' : y ∈ ⋃ z ∈ S, U z := Set.mem_biUnion hy (hyU y hy)
    rw [← hTU] at hy'
    obtain ⟨z, hz, hyz⟩ := Set.mem_iUnion₂.1 hy'
    exact Set.mem_biUnion hz (hCU z (hTS hz) ⟨hy.1, hyz⟩)
  rcases T.eq_empty_or_nonempty with hT0 | hTne
  ·
    refine ⟨fun _ => e0, fun _ => ∅, fun _ => 0,
      fun _ => ⟨isOpen_empty, differentiableOn_empty, by simp, by simp⟩, ?_⟩
    refine measure_mono_null ?_ hbad
    intro y hy
    refine ⟨hy.1, fun hyS => ?_⟩
    have hy' := hScov hyS
    simp [hT0] at hy'
  · obtain ⟨f, hf⟩ := hTc.exists_eq_range hTne
    have hfS : ∀ i, f i ∈ S := fun i => hTS (by rw [hf]; exact Set.mem_range_self i)
    refine ⟨fun i => E (f i), fun i => Om (f i), fun i => Ph (f i),
      fun i => ⟨hΩ _ (hfS i), hΦ _ (hfS i), hG _ (hfS i), hT _ (hfS i)⟩, ?_⟩
    refine measure_mono_null ?_ hbad
    intro y hy
    refine ⟨hy.1, fun hyS => hy.2 ?_⟩
    obtain ⟨z, hz, hyz⟩ := Set.mem_iUnion₂.1 (hScov hyS)
    rw [hf] at hz
    obtain ⟨i, rfl⟩ := hz
    exact Set.mem_iUnion.2 ⟨i, hyz⟩
end ConeGraphCover
end GroundTheory.Heights₂.Heights
