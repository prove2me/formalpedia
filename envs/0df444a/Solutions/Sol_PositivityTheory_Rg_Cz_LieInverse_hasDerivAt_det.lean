-- Prove2me | solution 1 for PositivityTheory.Rg.Cz.LieInverse.hasDerivAt_det
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T11:45:04.916242+00:00
-- url     : https://prove2.me/submissions/148599b5-a5e9-4a56-8033-88599b55d8d4

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_LiftCommEAt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PLieInv
import Theorems.Thm_PositivityTheory_Rg_Cz_LieInverse_exists_ne_of_ne_one
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
open PositivityTheory.Rg.Cz.LieInverse
namespace PositivityTheory.Rg.Cz.LieInverse
theorem _root_.solution {n : ℕ} (A : ℝ → Matrix (Fin n) (Fin n) ℂ) (Y : Matrix (Fin n) (Fin n) ℂ)
    (h0 : A 0 = 1) (hA : ∀ i j, HasDerivAt (fun t => A t i j) (Y i j) 0) :
    HasDerivAt (fun t => (A t).det) Y.trace 0 := by
  have key : ∀ σ : Equiv.Perm (Fin n), HasDerivAt (fun t => ((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ i, A t (σ i) i)
      (((Equiv.Perm.sign σ : ℤ) : ℂ) * ∑ i, (∏ j ∈ Finset.univ.erase i, A 0 (σ j) j) * Y (σ i) i) 0 := by
    intro σ
    have := (HasDerivAt.finsetProd (u := Finset.univ) (fun i _ => hA (σ i) i)).const_mul
      ((Equiv.Perm.sign σ : ℤ) : ℂ)
    refine this.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ?_)
    simp [Finset.prod_apply]
  have hs := HasDerivAt.sum (u := Finset.univ) (fun σ _ => key σ)
  refine (hs.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ?_)).congr_deriv ?_
  · simp [Matrix.det_apply', Finset.sum_apply]
  · simp only [Finset.mul_sum, smul_eq_mul]
    rw [Finset.sum_comm, Matrix.trace]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_eq_single (1 : Equiv.Perm (Fin n))]
    · simp [h0]
    · intro σ _ hσ
      obtain ⟨j, hji, hj⟩ := exists_ne_of_ne_one σ hσ i
      rw [Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hji, Finset.mem_univ j⟩) (by rw [h0]; exact Matrix.one_apply_ne hj)]
      simp
    · simp
end PositivityTheory.Rg.Cz.LieInverse
