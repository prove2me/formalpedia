-- Prove2me | solution 1 for PositivityTheory.Rg.Cz.Coch.cEv_perm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T11:33:41.443825+00:00
-- url     : https://prove2.me/submissions/0ad80b54-9f9e-4379-a67f-5851f2c7c7cd

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_KugaCoordinates_CochainExpansions_SumSumProd

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Complex
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Cz PositivityTheory.Rg.Cz.Coch
variable {H V : Type*} [AddCommGroup V] [Module ℂ V]
namespace PositivityTheory.Rg.Cz.Coch
theorem _root_.solution {N : ℕ} (F : (Fin N → H) → V) (σ : Equiv.Perm (Fin N)) (A B : Fin N → H) :
    cEv (fun v => F (fun i => v (σ i))) A B = cEv F (fun i => A (σ i)) (fun i => B (σ i)) := by
  unfold cEv
  refine Fintype.sum_equiv ⟨fun S => S ∘ σ, fun T => T ∘ σ.symm, fun S => by funext x; simp,
    fun T => by funext x; simp⟩ _ _ fun S => ?_
  simp only [Equiv.coe_fn_mk, Function.comp_apply]
  congr 1
  exact (Equiv.prod_comp σ (fun k => if S k then (1 : ℂ) else -I)).symm
end PositivityTheory.Rg.Cz.Coch
