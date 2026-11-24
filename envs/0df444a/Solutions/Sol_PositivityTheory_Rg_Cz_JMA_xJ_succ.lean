-- Prove2me | solution 1 for PositivityTheory.Rg.Cz.JMA.xJ_succ
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:50:48.833854+00:00
-- url     : https://prove2.me/submissions/0ffcf969-5894-4310-aab1-d52643d4380a

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_LiftCommEAt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PJmComm
import Theorems.Thm_PositivityTheory_Rg_Cz_JMA_pm_swap_sq
import Theorems.Thm_PositivityTheory_Rg_Cz_lift_apply
import Theorems.Thm_PositivityTheory_Rg_Cz_pm_apply
import Theorems.Thm_PositivityTheory_Rg_Cz_pm_mul
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
open PositivityTheory.Rg.Cz.JMA
variable {n : ℕ} {M : Type} [AddCommGroup M] [Module ℂ M]
namespace PositivityTheory.Rg.Cz.JMA
theorem _root_.solution (hT : TensorGl) {E : Fin n → Fin n → Module.End ℂ M} (hE : GlRel E) {m : ℕ} (i j : Fin m)
    (hij : (i : ℕ) + 1 = j) :
    xJ E j = pm (Equiv.swap i j) * xJ E i * pm (Equiv.swap i j) + pm (Equiv.swap i j) := by
  have hOm : pm (Equiv.swap i j) * Om E i * pm (Equiv.swap i j) = Om E j := by
    rw [(hT n M (Fin m) E hE (∅ : Finset (Fin m))).2.2.2, mul_assoc, pm_swap_sq, mul_one,
      Equiv.swap_apply_left]
  have hsum : ∀ l ∈ Finset.univ.filter (· < i),
      pm (Equiv.swap i j) * pm (Equiv.swap l i) * pm (Equiv.swap i j) =
        (pm (Equiv.swap l j) : Module.End ℂ (TV n M (Fin m))) := by
    intro l hl
    have hl' : (l : ℕ) < i := (Finset.mem_filter.1 hl).2
    rw [← pm_mul, ← pm_mul]
    congr 1
    refine Equiv.ext fun x => ?_
    simp only [Equiv.Perm.mul_apply, Equiv.swap_apply_def]
    split_ifs <;> simp_all [Fin.ext_iff] <;> omega
  have hset : Finset.univ.filter (· < j) = insert i (Finset.univ.filter (· < i)) := by
    ext l
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Fin.lt_iff_val_lt_val, Fin.ext_iff]
    omega
  show Om E j + ∑ l ∈ Finset.univ.filter (· < j), pm (Equiv.swap l j) =
    pm (Equiv.swap i j) * (Om E i + ∑ l ∈ Finset.univ.filter (· < i), pm (Equiv.swap l i)) *
      pm (Equiv.swap i j) + pm (Equiv.swap i j)
  rw [hset, Finset.sum_insert (by simp), mul_add, add_mul, Finset.mul_sum, Finset.sum_mul,
    Finset.sum_congr rfl hsum, hOm]
  abel
end PositivityTheory.Rg.Cz.JMA
