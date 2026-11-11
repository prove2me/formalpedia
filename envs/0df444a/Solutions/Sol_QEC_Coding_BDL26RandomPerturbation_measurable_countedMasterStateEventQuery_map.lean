-- Prove2me | solution 1 for QEC.Coding.BDL26RandomPerturbation.measurable_countedMasterStateEventQuery_map
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T01:34:53.553841+00:00
-- url     : https://prove2.me/submissions/d21d8989-581e-4829-bbdb-ca26dde98936

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_JointExecution
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_ActualExecutionCost
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountedCostMeasurability
import Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_measurable_listAllQuery
import Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_measurable_listAnyQuery
import Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_measurable_stateTriangleQuery_map
import Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_measurable_fullCenterQuery

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation
open BDL26FiniteTannerSquare
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open QEC.Coding.ProbabilisticConstruction.Resampling
open MeasureTheory
open scoped ENNReal
attribute [local instance] QEC.Coding.BDL26RandomPerturbation.countedLabelListMeasurable
attribute [local instance] QEC.Coding.BDL26RandomPerturbation.countedLabelListSingleton
namespace QEC.Coding.BDL26RandomPerturbation
theorem _root_.solution {Ω : Type*} [MeasurableSpace Ω]
    (P : TannerSquarePresentation) (lambda : ℝ) (K : ℕ) (e : MasterEvent P)
    (J : Ω → Vertex P → Space) (hJ : Measurable J)
    (L : List (Vertex P)) (f : Vertex P → Ω → ℕ × Space)
    (hf : ∀ u, Measurable (f u)) :
    Measurable (fun w => countedMasterStateEventQuery P (J w) lambda K e
      (L.map (fun u => (u, f u w)))) := by
  let anchor := countedMasterAnchorQuery P e
  have hc (g : Grid K) := measurable_fullCenterQuery P lambda K anchor.1 g J hJ
  have ht (g : Grid K) := measurable_listAllQuery
    (fun a : e.val => fun w => stateTriangleQuery P (J w) lambda a.val
      (L.map (fun u => (u, f u w))) (fullCenterQuery P (J w) lambda K anchor.1 g).1)
    (fun a => measurable_stateTriangleQuery_map P lambda a.val J hJ L f hf _ (hc g).fst)
    (Finset.univ.toList : List e.val)
  have hg (g : Grid K) : Measurable (fun w =>
      let center := fullCenterQuery P (J w) lambda K anchor.1 g
      let triangles := listAllQuery (fun a : e.val =>
        stateTriangleQuery P (J w) lambda a.val (L.map (fun u => (u, f u w))) center.1)
        (Finset.univ.toList : List e.val)
      (triangles.1, center.2 + triangles.2 + 8)) :=
    (ht g).fst.prodMk ((measurable_of_countable
      (fun ns : ℕ × ℕ => ns.1 + ns.2 + 8)).comp ((hc g).snd.prodMk (ht g).snd))
  have hq := measurable_listAnyQuery _ hg (gridListQuery K).1
  exact (measurable_of_countable (fun q : Bool × ℕ =>
    (q.1, (gridListQuery K).2 + anchor.2 + q.2 + 1))).comp hq
end QEC.Coding.BDL26RandomPerturbation
