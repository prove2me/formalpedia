-- Prove2me | solution 1 for PositivityTheory.Rg.Cz.ChainP.base
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T11:51:27.67262+00:00
-- url     : https://prove2.me/submissions/ef5c54d1-7768-44a7-a60f-c69add1eb4f8

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PChainA
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PChain
import Theorems.Thm_PositivityTheory_Rg_Cz_ChainP_qdet_comp
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
open PositivityTheory.Rg.Cz.ChainP
variable {n : ℕ} {M : Type} [AddCommGroup M] [Module ℂ M]
namespace PositivityTheory.Rg.Cz.ChainP
theorem _root_.solution (E : Fin n → Fin n → Module.End ℂ M) (l : Fin n → ℂ) (hl : HasChar E l) (ℓ : M →ₗ[ℂ] ℂ)
    (hℓ : ℓ ≠ 0) (top : Fin n) (co : Fin 0 → Fin n) : Good E l ℓ top 0 co 1 := by
  refine ⟨Subalgebra.one_mem _, ?_, fun j => j.elim0, ?_⟩
  · intro h
    apply hℓ
    refine LinearMap.ext fun v => ?_
    have := LinearMap.congr_fun h (fun _ => v)
    simpa using this
  · intro u
    have hc : ∀ a b : Fin n, (LinearMap.proj (fun _ : Fin 0 => top) : TV n M (Fin 0) →ₗ[ℂ] M) ∘ₗ
        tE (Finset.univ : Finset (Fin 0)) E a b = E a b ∘ₗ LinearMap.proj (fun _ : Fin 0 => top) := by
      intro a b
      refine LinearMap.ext fun x => ?_
      simp [tE, lift]
    have hq := qdet_comp (LinearMap.proj (fun _ : Fin 0 => top) : TV n M (Fin 0) →ₗ[ℂ] M) _ E hc u
    refine LinearMap.ext fun x => ?_
    have hx := LinearMap.congr_fun hq x
    simp only [LinearMap.comp_apply, Module.End.one_apply, LinearMap.smul_apply] at hx ⊢
    rw [hx, hl u]
    simp
end PositivityTheory.Rg.Cz.ChainP
