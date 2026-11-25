-- Prove2me | solution 1 for PositivityTheory.Rg.Cz.young_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:13:49.360488+00:00
-- url     : https://prove2.me/submissions/5875f53e-e3fc-4a18-ac59-b2adce6a207e

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PYoungB
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PYoung
import Theorems.Thm_PositivityTheory_Rg_Cz_YoungTableau_altPair_apply
import Theorems.Thm_PositivityTheory_Rg_Cz_YoungTableau_term
import Theorems.Thm_PositivityTheory_Rg_Cz_YoungTableau_kap_pos
import Theorems.Thm_PositivityTheory_Rg_Cz_cA_apply
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
open YoungTableau
namespace PositivityTheory.Rg.Cz
theorem _root_.solution : Young := by
  intro n M _ _ ι _ Q _ _ N tl C _ col b hT h1 h2 h3 h4 ξ h
  rw [cA_apply]
  have key : altPair tl (alt (colG col) ξ) b = ((kap tl (col ∘ inF Q N) (col ∘ inS Q N) (b ∘ inF Q N)
      (b ∘ inS Q N) : ℤ) : ℂ) • alt (colG col) ξ b := by
    rw [altPair_apply, kap, Int.cast_sum, Finset.sum_smul]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [term tl col b hT h1 h2 ξ σ, smul_smul]
    push_cast
    ring_nf
  rw [h] at key
  have hk := kap_pos tl (col ∘ inF Q N) (col ∘ inS Q N) (b ∘ inF Q N) (b ∘ inS Q N) (fun k k' => h3 k k')
    (fun k k' => h4 k k') (fun k k' ht hr hc => by
      have := hT.1 (inF Q N k) (inF Q N k') ((h3 k k').mpr ⟨ht, hc⟩) hr
      simpa [inF] using this)
  exact (smul_eq_zero.mp key.symm).resolve_left (by exact_mod_cast hk.ne')
end PositivityTheory.Rg.Cz
