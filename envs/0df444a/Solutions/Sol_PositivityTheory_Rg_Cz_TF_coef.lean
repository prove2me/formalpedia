-- Prove2me | solution 1 for PositivityTheory.Rg.Cz.TF.coef
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T11:38:46.985325+00:00
-- url     : https://prove2.me/submissions/c99e374f-3881-4103-a0ea-79ac4fe40ec4

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PTransFinCK
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PTransFinA
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
open PositivityTheory.Rg.Cz.TF
namespace PositivityTheory.Rg.Cz.TF
theorem _root_.solution {Y : Type*} [AddCommGroup Y] [Module ℂ Y] (d : ℕ) (y : ℕ → Y) (S : Set ℂ) (hS : S.Infinite)
    (h : ∀ u ∈ S, ∑ i ∈ Finset.range d, u ^ i • y i = 0) : ∀ i ∈ Finset.range d, y i = 0 := by
  intro i hi
  rw [← Module.forall_dual_apply_eq_zero_iff ℂ]
  intro f
  set p : Polynomial ℂ := ∑ j ∈ Finset.range d, Polynomial.C (f (y j)) * Polynomial.X ^ j with hp
  have hroot : p = 0 := by
    apply Polynomial.eq_zero_of_infinite_isRoot
    apply hS.mono
    intro u hu
    have hfu := congrArg f (h u hu)
    simp only [map_sum, map_smul, smul_eq_mul, map_zero] at hfu
    show Polynomial.eval u p = 0
    simp only [hp, Polynomial.eval_finset_sum, Polynomial.eval_mul,
      Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
    rw [← hfu]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  have hc := congrArg (fun q => Polynomial.coeff q i) hroot
  simp only [hp, Polynomial.finset_sum_coeff, Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_zero] at hc
  rw [Finset.sum_ite_eq] at hc
  simpa [hi] using hc
end PositivityTheory.Rg.Cz.TF
