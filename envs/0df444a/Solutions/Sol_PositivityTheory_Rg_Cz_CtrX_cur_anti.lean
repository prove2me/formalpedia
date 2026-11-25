-- Prove2me | solution 1 for PositivityTheory.Rg.Cz.CtrX.cur_anti
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T11:30:53.274058+00:00
-- url     : https://prove2.me/submissions/80f71881-3a2e-42b4-b5f3-75b5b6629197

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_LiftCommEAt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PContractA
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
theorem _root_.solution {m : ℕ} (h : n ≤ m) (η : TV n M (Fin m))
    (hη : ∀ τ ∈ firstG m n, pm τ η = ((Equiv.Perm.sign τ : ℤ) : ℂ) • η) (σ : Equiv.Perm (Fin n)) :
    pm σ (cur (reIx (splitE m n h) η)) = ((Equiv.Perm.sign σ : ℤ) : ℂ) • cur (reIx (splitE m n h) η) := by
  funext J K
  set e := splitE m n h with he
  let S : Equiv.Perm (Fin (m - n) ⊕ Fin n) := Equiv.sumCongr (Equiv.refl _) σ
  let τ : Equiv.Perm (Fin m) := (e.trans S).trans e.symm
  have hτ : τ ∈ firstG m n := by
    simp only [firstG, Finset.mem_filter, Finset.mem_univ, true_and]
    intro j hj
    have hj' : ¬ (j : ℕ) < n := by omega
    have ha : e j = Sum.inl ⟨(j : ℕ) - n, by omega⟩ := by
      simp [he, splitE, hj']
    show e.symm (S (e j)) = j
    rw [ha]
    exact e.symm_apply_eq.2 ha.symm
  have hs : Equiv.Perm.sign τ = Equiv.Perm.sign σ := by
    show Equiv.Perm.sign ((e.symm.symm.trans S).trans e.symm) = _
    rw [Equiv.Perm.sign_symm_trans_trans]
    simp [S, Equiv.Perm.sign_sumCongr]
  have key := congrFun (hη τ hτ) (Sum.elim K J ∘ e)
  simp only [pm, LinearMap.pi_apply, LinearMap.proj_apply, Pi.smul_apply] at key
  simp only [pm, cur, reIx, LinearMap.pi_apply, LinearMap.proj_apply, Pi.smul_apply]
  rw [← hs, ← key]
  congr 1
  funext x
  simp only [Function.comp_apply, τ, Equiv.trans_apply, Equiv.apply_symm_apply]
  generalize e x = y
  cases y <;> rfl
end PositivityTheory.Rg.Cz.CtrX
