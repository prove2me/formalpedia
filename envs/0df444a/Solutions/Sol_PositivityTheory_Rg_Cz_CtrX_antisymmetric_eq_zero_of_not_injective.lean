-- Prove2me | solution 1 for PositivityTheory.Rg.Cz.CtrX.antisymmetric_eq_zero_of_not_injective
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:06:45.9684+00:00
-- url     : https://prove2.me/submissions/3902fc5e-4c65-429a-8b10-b122e2650901

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_LiftCommEAt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PContractD
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
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Cz PositivityTheory.Rg.Cz.CtrX
open PositivityTheory.Rg.Cz
variable {n : ℕ} {M : Type} [AddCommGroup M] [Module ℂ M]
namespace PositivityTheory.Rg.Cz.CtrX
theorem _root_.solution (f : TV n M (Fin n))
    (hf : ∀ σ : Equiv.Perm (Fin n), pm σ f = ((Equiv.Perm.sign σ : ℤ) : ℂ) • f) (J : Fin n → Fin n)
    (hJ : ¬ Function.Injective J) : f J = 0 := by
  obtain ⟨i, j, hij, hne⟩ := Function.not_injective_iff.mp hJ
  have h2 : J ∘ ⇑(Equiv.swap i j) = J := by
    funext k
    simp only [Function.comp]
    rcases eq_or_ne k i with rfl | hki
    · simp [hij]
    rcases eq_or_ne k j with rfl | hkj
    · simp [hij]
    · rw [Equiv.swap_apply_of_ne_of_ne hki hkj]
  have h1 := congrFun (hf (Equiv.swap i j)) J
  have h3 : pm (Equiv.swap i j) f J = f J := by
    show f (J ∘ ⇑(Equiv.swap i j)) = f J
    rw [h2]
  rw [h3, Pi.smul_apply, Equiv.Perm.sign_swap hne] at h1
  have h4 : (2 : ℂ) • f J = 0 := by
    rw [two_smul]
    nth_rewrite 1 [h1]
    simp
  rcases smul_eq_zero.mp h4 with h | h
  · norm_num at h
  · exact h
end PositivityTheory.Rg.Cz.CtrX
