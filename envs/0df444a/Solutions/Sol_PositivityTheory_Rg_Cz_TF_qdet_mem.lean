-- Prove2me | solution 1 for PositivityTheory.Rg.Cz.TF.qdet_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T11:38:07.806696+00:00
-- url     : https://prove2.me/submissions/fcc37383-56f7-4c27-ae0c-b04d197ff51d

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PTransFinCK
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PTransFinA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism.REAL Matrix
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Cz
open PositivityTheory.Rg.Cz.TF
namespace PositivityTheory.Rg.Cz.TF
theorem _root_.solution {A : Type*} [Ring A] [Algebra ℂ A] {n : ℕ} (F : Fin n → Fin n → A) (B : Subalgebra ℂ A)
    (hF : ∀ a b, F a b ∈ B) (u : ℂ) : qdet F u ∈ B := by
  unfold qdet qminor
  refine B.sum_mem fun σ _ => B.mul_mem ?_ (B.list_prod_mem ?_)
  · exact intCast_mem B _
  · intro z hz
    rw [List.mem_ofFn] at hz
    obtain ⟨k, rfl⟩ := hz
    unfold Tm
    refine B.add_mem ?_ (hF _ _)
    split_ifs
    · exact B.algebraMap_mem _
    · exact B.zero_mem
end PositivityTheory.Rg.Cz.TF
