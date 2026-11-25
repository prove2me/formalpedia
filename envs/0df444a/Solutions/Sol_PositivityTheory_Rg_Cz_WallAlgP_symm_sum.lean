-- Prove2me | solution 1 for PositivityTheory.Rg.Cz.WallAlgP.symm_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T11:37:17.455996+00:00
-- url     : https://prove2.me/submissions/e38dacd9-1734-4f5a-b479-e93afe0ced35

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_LiftCommEAt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PWallAlgA
import Theorems.Thm_PositivityTheory_Rg_Cz_lift_apply
import Theorems.Thm_PositivityTheory_Rg_Cz_pm_apply
import Theorems.Thm_PositivityTheory_Rg_Cz_pm_one
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] PositivityTheory.Rg.Cz.lift_apply
attribute [local simp] PositivityTheory.Rg.Cz.pm_apply
attribute [local simp] PositivityTheory.Rg.Cz.pm_one



set_option autoImplicit false
noncomputable section
open Formalism.REAL Matrix
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Cz
open PositivityTheory.Rg.Cz.WallAlgP
variable {n : ℕ} {M : Type} [AddCommGroup M] [Module ℂ M]
namespace PositivityTheory.Rg.Cz.WallAlgP
theorem _root_.solution {m k : ℕ} {V : Type} [AddCommMonoid V] (g : Fin m → Fin m → V) (hg : ∀ i j, g i j = g j i) :
    ∑ j ∈ Finset.univ.filter (fun j : Fin m => (j : ℕ) < k),
      ∑ p ∈ Finset.univ.filter (fun p : Fin m => (p : ℕ) < k ∧ p ≠ j), g j p =
    2 • ∑ j ∈ Finset.univ.filter (fun j : Fin m => (j : ℕ) < k), ∑ i ∈ Finset.univ.filter (· < j), g i j := by
  have hsplit : ∀ j ∈ Finset.univ.filter (fun j : Fin m => (j : ℕ) < k),
      ∑ p ∈ Finset.univ.filter (fun p : Fin m => (p : ℕ) < k ∧ p ≠ j), g j p =
      ∑ i ∈ Finset.univ.filter (· < j), g i j +
        ∑ p ∈ Finset.univ.filter (fun p : Fin m => (p : ℕ) < k ∧ j < p), g j p := by
    intro j hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
    have hu : Finset.univ.filter (fun p : Fin m => (p : ℕ) < k ∧ p ≠ j) =
        Finset.univ.filter (· < j) ∪ Finset.univ.filter (fun p : Fin m => (p : ℕ) < k ∧ j < p) := by
      ext p
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union, Fin.lt_def, ne_eq, Fin.ext_iff]
      omega
    rw [hu, Finset.sum_union]
    · congr 1
      exact Finset.sum_congr rfl fun i _ => hg j i
    · rw [Finset.disjoint_filter]
      intro p _ h1 h2
      rw [Fin.lt_def] at h1 h2
      omega
  rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib, two_nsmul]
  congr 1
  refine Finset.sum_comm' fun j p => ?_
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.lt_def]
  omega
end PositivityTheory.Rg.Cz.WallAlgP
