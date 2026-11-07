-- Prove2me | solution 1 for QEC.Coding.ProbabilisticConstruction.Resampling.familyRead_law
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:42:05.525188+00:00
-- url     : https://prove2.me/submissions/58fe66d7-cb77-43c3-8de1-63afda926aaf

import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_Execution
import Mathlib.Probability.Independence.InfinitePi
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_TableProbability
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_advance_of_mem
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_advance_of_notMem
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_avoid_empty
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_avoid_insert
attribute [local simp] QEC.Coding.ProbabilisticConstruction.Resampling.advance_of_mem
attribute [local simp] QEC.Coding.ProbabilisticConstruction.Resampling.advance_of_notMem
attribute [local simp] QEC.Coding.ProbabilisticConstruction.avoid_empty
attribute [local simp] QEC.Coding.ProbabilisticConstruction.avoid_insert



set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ProbabilisticConstruction QEC.Coding.ProbabilisticConstruction.Resampling
open MeasureTheory ProbabilityTheory
open scoped BigOperators
variable {V A : Type*} [Fintype V] [DecidableEq V] [Fintype A]
variable {X : V → Type*} [∀ v, MeasurableSpace (X v)]
variable (ν : ∀ v, Measure (X v)) [∀ v, IsProbabilityMeasure (ν v)]
namespace QEC.Coding.ProbabilisticConstruction.Resampling
theorem _root_.solution (coords : A → Finset V) (column : ∀ a, coords a → ℕ)
    (haddress : Function.Injective
      (fun s : (a : A) × coords a => (s.2.val, column s.1 s.2))) :
    (tableLaw ν).map (familyRead (X := X) coords column) =
      Measure.pi (fun a => Measure.pi (fun v : coords a => ν v)) := by
  let key : ((a : A) × coords a) → V × ℕ := fun s => (s.2.val, column s.1 s.2)
  have hflat := Measure.map_infinitePi_infinitePi_of_inj
    (P := fun p : V × ℕ => ν p.1) (f := key) haddress
  have hcur := congrArg
    (fun m => m.map (MeasurableEquiv.piCurry (fun (a : A) (v : coords a) => X v))) hflat
  rw [Measure.map_map (by fun_prop) (by fun_prop)] at hcur
  change _ = (Measure.infinitePi (fun s : (a : A) × coords a => ν s.2.val)).map
    (MeasurableEquiv.piCurry (fun (a : A) (v : coords a) => X v)) at hcur
  rw [Measure.infinitePi_map_piCurry (fun (a : A) (v : coords a) => ν v)] at hcur
  simp only [key, Function.comp_def, MeasurableEquiv.coe_piCurry,
    Measure.infinitePi_eq_pi] at hcur
  change (Measure.infinitePi (fun p : V × ℕ => ν p.1)).map
    (fun R a v => R (v.val, column a v)) = _
  exact hcur
end QEC.Coding.ProbabilisticConstruction.Resampling
