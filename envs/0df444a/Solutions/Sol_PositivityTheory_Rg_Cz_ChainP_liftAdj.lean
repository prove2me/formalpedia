-- Prove2me | solution 1 for PositivityTheory.Rg.Cz.ChainP.liftAdj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T11:32:42.307262+00:00
-- url     : https://prove2.me/submissions/6351a0bb-f203-4d7b-bdf9-f62b4fbaad48

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PChainA
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PChain
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
theorem _root_.solution (hC : Curry) (E : Fin n → Fin n → Module.End ℂ M) (m : ℕ) :
    ∀ g ∈ Algebra.adjoin ℂ (Set.range fun j : Fin m => xJ E j), ∃ g' ∈ Algebra.adjoin ℂ
      (Set.range fun j : Fin (m + 1) => xJ E j), curF n M m 1 ∘ₗ g' =
        (lift g : Module.End ℂ (TV n (TV n M (Fin m)) (Fin 1))) ∘ₗ curF n M m 1 := by
  intro g hg
  induction hg using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    exact ⟨xJ E (Fin.castAdd 1 i), Algebra.subset_adjoin ⟨_, rfl⟩, (hC n M E m 1).2.2.1 i⟩
  | algebraMap c =>
    refine ⟨algebraMap ℂ _ c, Subalgebra.algebraMap_mem _ c, ?_⟩
    refine LinearMap.ext fun x => ?_
    funext J I
    simp [lift, curF]
  | add x y _ _ hx hy =>
    obtain ⟨x', hx', ex⟩ := hx
    obtain ⟨y', hy', ey⟩ := hy
    refine ⟨x' + y', Subalgebra.add_mem _ hx' hy', ?_⟩
    have hs : (lift (x + y) : Module.End ℂ (TV n (TV n M (Fin m)) (Fin 1))) = lift x + lift y := by
      refine LinearMap.ext fun v => ?_
      funext J
      simp [lift]
    rw [hs, LinearMap.comp_add, LinearMap.add_comp, ex, ey]
  | mul x y _ _ hx hy =>
    obtain ⟨x', hx', ex⟩ := hx
    obtain ⟨y', hy', ey⟩ := hy
    refine ⟨x' * y', Subalgebra.mul_mem _ hx' hy', ?_⟩
    have hs : (lift (x * y) : Module.End ℂ (TV n (TV n M (Fin m)) (Fin 1))) = lift x * lift y := by
      refine LinearMap.ext fun v => ?_
      funext J
      simp [lift]
    rw [hs, Module.End.mul_eq_comp, Module.End.mul_eq_comp, ← LinearMap.comp_assoc, ex,
      LinearMap.comp_assoc, ey, LinearMap.comp_assoc]
end PositivityTheory.Rg.Cz.ChainP
