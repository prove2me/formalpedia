-- Prove2me | solution 1 for PositivityTheory.Rg.Cz.QuantumDeterminantProducts.alt_anti
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T11:34:33.478803+00:00
-- url     : https://prove2.me/submissions/7674732f-78c4-4882-8cf9-0571370524bc

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_LiftCommEAt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PPiQdet
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
open PositivityTheory.Rg.Cz.QuantumDeterminantProducts
variable {n : ℕ} {M : Type} [AddCommGroup M] [Module ℂ M]
namespace PositivityTheory.Rg.Cz.QuantumDeterminantProducts
theorem _root_.solution (f : TV n M (Fin n)) : IsAnti (alt Finset.univ f) := by
  intro σ
  funext I
  have key : ∀ J : Fin n → Fin n, alt Finset.univ f J = ∑ τ : Equiv.Perm (Fin n), sg τ • f (J ∘ ⇑τ) := by
    intro J
    simp [alt, pm, sg]
  have hp : pm σ (alt Finset.univ f) I = alt Finset.univ f (I ∘ σ) := by
    simp [pm]
  rw [hp]
  show alt Finset.univ f (I ∘ σ) = sg σ • alt Finset.univ f I
  rw [key (I ∘ σ), key I, Finset.smul_sum]
  refine Fintype.sum_equiv (Equiv.mulLeft σ) _ _ ?_
  intro τ
  have hs : sg σ * sg (σ * τ) = sg τ := by
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [sg, Equiv.Perm.sign_mul, h]
  simp only [Equiv.coe_mulLeft]
  rw [smul_smul, hs]
  rfl
end PositivityTheory.Rg.Cz.QuantumDeterminantProducts
