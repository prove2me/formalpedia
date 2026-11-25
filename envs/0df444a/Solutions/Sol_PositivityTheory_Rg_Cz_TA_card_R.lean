-- Prove2me | solution 1 for PositivityTheory.Rg.Cz.TA.card_R
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T11:37:41.61136+00:00
-- url     : https://prove2.me/submissions/3a3cfd79-36d2-46ec-b514-38a6f92ac7a2

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PTransAllB
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PTransAllC
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
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Cz PositivityTheory.Rg.Cz.TA
variable {n : ℕ} {M : Type} [AddCommGroup M] [Module ℂ M] {P : Type} [Fintype P] [DecidableEq P]
  {ι : Type} [DecidableEq ι] (lab : P → ι) (τ₀ : ι)
omit [DecidableEq P]
namespace PositivityTheory.Rg.Cz.TA
theorem _root_.solution (τ : {τ // τ ≠ τ₀}) (co : P → Fin n) (k : Fin n) :
    (Finset.univ.filter fun p : {p // ¬ lab p = τ₀} => labR lab τ₀ p = τ ∧ co p.1 = k).card =
      (Finset.univ.filter fun p => lab p = τ.1 ∧ co p = k).card := by
  refine Finset.card_bij (fun p _ => p.1) ?_ ?_ ?_
  · intro p hp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, labR, Subtype.ext_iff] at hp ⊢
    exact hp
  · intro p _ q _ h
    exact Subtype.ext h
  · intro p hp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
    refine ⟨⟨p, fun h => τ.2 (hp.1.symm.trans h)⟩, ?_, rfl⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, labR, Subtype.ext_iff]
    exact hp
end PositivityTheory.Rg.Cz.TA
