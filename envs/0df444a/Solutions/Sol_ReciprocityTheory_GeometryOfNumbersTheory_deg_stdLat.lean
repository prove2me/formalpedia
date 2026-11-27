-- Prove2me | solution 1 for ReciprocityTheory.GeometryOfNumbersTheory.deg_stdLat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T05:29:01.026788+00:00
-- url     : https://prove2.me/submissions/18d08d57-9ba7-4694-96ed-2e4d820fbb6d

import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_LatticeCovolumes_ArakelovDegreeEqDegreeOfFamily
import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_LatticeCovolumes_InhabSt
import Theorems.Thm_ReciprocityTheory_GeometryOfNumbersTheory_arakelovDegree_eq_degreeOfFamily


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.GeometryOfNumbersTheory
open NumberField Module
open scoped ComplexOrder
variable (K : Type*) [Field K] [NumberField K]
namespace ReciprocityTheory.GeometryOfNumbersTheory
theorem _root_.solution (m : ℕ) : deg (stdHerm K m) (stdLat K m) = 0 := by
  classical
  have hcoe : ⇑(Pi.basisFun K (Fin m)) = fun i : Fin m => (Pi.single i 1 : Fin m → K) := by
    funext i
    simp [Pi.basisFun_apply]
  have hli : LinearIndependent K (fun i : Fin m => (Pi.single i 1 : Fin m → K)) := by
    rw [← hcoe]
    exact (Pi.basisFun K (Fin m)).linearIndependent
  have hfr : IsFrame K (stdLat K m) (fun i : Fin m => (Pi.single i 1 : Fin m → K)) := by
    refine ⟨fun i => Submodule.subset_span ⟨i, rfl⟩, hli, ?_⟩
    intro x _
    have hsp : Submodule.span K (Set.range fun i : Fin m => (Pi.single i 1 : Fin m → K)) = ⊤ := by
      rw [← hcoe]
      exact (Pi.basisFun K (Fin m)).span_eq
    rw [hsp]
    exact Submodule.mem_top
  rw [arakelovDegree_eq_degreeOfFamily (E := stdLat K m) _ (Submodule.fg_span (Set.finite_range _)) hfr]
  have hg : ∀ σ : K →+* ℂ,
      (stdHerm K m).gram σ (fun i : Fin m => (Pi.single i 1 : Fin m → K)) = 1 := by
    intro σ
    ext i j
    simp only [HermFam.gram, stdHerm, Matrix.of_apply, Matrix.one_apply]
    rw [Finset.sum_eq_single i]
    · by_cases h : i = j
      · subst h
        simp
      · simp [h, Pi.single_apply, Ne.symm h]
    · intro b _ hb
      simp [Pi.single_apply, hb]
    · simp
  unfold degreeOfFamily stdLat
  simp [hg, AddSubgroup.relIndex_self]
end ReciprocityTheory.GeometryOfNumbersTheory
