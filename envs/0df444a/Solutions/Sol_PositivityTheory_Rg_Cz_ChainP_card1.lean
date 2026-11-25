-- Prove2me | solution 1 for PositivityTheory.Rg.Cz.ChainP.card1
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T11:32:26.304819+00:00
-- url     : https://prove2.me/submissions/148c6299-5d7a-4fe1-a7f3-a4f6d235cd7e

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
theorem _root_.solution {m : ℕ} (co : Fin (m + 1) → Fin n) (i : Fin m) :
    (Finset.univ.filter fun p : Fin (m + 1) => p < i.castSucc ∧ co p = co i.castSucc).card =
      (Finset.univ.filter fun p : Fin m => p < i ∧ (co ∘ Fin.castSucc) p = (co ∘ Fin.castSucc) i).card := by
  symm
  apply Finset.card_bij (fun p _ => p.castSucc)
  · intro p hp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Function.comp] at hp ⊢
    refine ⟨?_, hp.2⟩
    rw [Fin.lt_def] at hp ⊢
    simpa using hp.1
  · intro a _ b _ h
    exact Fin.castSucc_injective _ h
  · intro b hb
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb
    have h1 : (b : ℕ) < i := by simpa [Fin.lt_def] using hb.1
    have h2 : (b : ℕ) < m := lt_trans h1 i.isLt
    refine ⟨⟨b, h2⟩, ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and, Function.comp]
      refine ⟨by simpa [Fin.lt_def] using h1, ?_⟩
      have hb' : (⟨b, h2⟩ : Fin m).castSucc = b := Fin.ext rfl
      rw [hb']
      exact hb.2
    · exact Fin.ext rfl
end PositivityTheory.Rg.Cz.ChainP
