-- Prove2me | solution 1 for P2M_GlobalTheory_SmGL_SwapBlocks_emb__swap_3946f0185947
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T04:51:56.418025+00:00
-- url     : https://prove2.me/submissions/bdc1334e-37de-47e3-bc03-9a560bdbc4e7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsSubquotientDetRepParInd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_LowerEquivUpperSwap
import Theorems.Thm_GlobalTheory_SmGL_IsSubquotient_trans
import Theorems.Thm_P2M_GlobalTheory_SmGL_val_emb__6050fcaf31c9


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL ValuativeRel MeasureTheory
open GlobalTheory GlobalTheory.SmGL GlobalTheory.SmGL.SwapBlocks
variable (R : Type) [CommRing R] {a b n : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
  [Fintype n] [DecidableEq n]
namespace GlobalTheory.SmGL.SwapBlocks
theorem _root_.solution (e : a ⊕ b ≃ n) (g : GL a R × GL b R) :
    emb₂ R e g = emb₂ R ((Equiv.sumComm b a).trans e) (g.2, g.1) := by
  apply Units.ext
  rw [val_emb₂, val_emb₂]
  ext i j
  obtain ⟨i, rfl⟩ := e.surjective i
  obtain ⟨j, rfl⟩ := e.surjective j
  rcases i with i | i <;> rcases j with j | j <;> simp
end GlobalTheory.SmGL.SwapBlocks
