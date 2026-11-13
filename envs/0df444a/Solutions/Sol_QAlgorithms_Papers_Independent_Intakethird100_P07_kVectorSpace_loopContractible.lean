-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Intakethird100.P07.kVectorSpace_loopContractible
-- status  : ACCEPTED   (prove)
-- author  : @Mrnaiq
-- created : 2026-11-12T23:04:52.010006+00:00
-- url     : https://prove2.me/submissions/8d9d84da-441d-421b-bfe7-dbfa588fee88

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P07
import Mathlib.CategoryTheory.Adjunction.Limits
set_option autoImplicit false

open QAlgorithms.Papers.Independent.Intakethird100.P07
noncomputable section

universe u v



open CategoryTheory Topology TopologicalSpace

/-- Example 6.1, PDF p. 25: the explicit scalar homotopy contracts a
real k-vector space. Its operations are assumed continuous on k-products;
no ordinary-product continuity or loop-contractibility hypothesis is imposed. -/
theorem solution
    (V : Type u) [TopologicalSpace V] [AddCommGroup V] [Module ℝ V]
    [UCompactlyGeneratedSpace.{u} V]
    (hadd : Continuous (fun p : KSpace (V × V) => p.1 + p.2))
    (hneg : Continuous (fun x : V => -x))
    (hsmul : Continuous (fun p : KSpace (ℝ × V) => p.1 • p.2)) :
    IsKAddLoopContraction (scalarHomotopy (V := V)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · let f : C(V × UnitTime, ℝ × V) := ⟨fun p => ((p.2 : ℝ),p.1),
      (continuous_subtype_val.comp continuous_snd).prodMk continuous_fst⟩
    exact hsmul.comp (kMap f).continuous
  · intro x; simp [scalarHomotopy,timeZero]
  · intro x; simp [scalarHomotopy,timeOne]
  · intro t x y; exact smul_add _ _ _
