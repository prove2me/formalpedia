-- Prove2me | solution 1 for P2M_GlobalTheory_SmGL_val_emb__6050fcaf31c9
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:25:39.683838+00:00
-- url     : https://prove2.me/submissions/0f4de3ed-8b75-4676-94c6-91fabb0f273d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_LeviEmbMemNormalizerLower

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.SmGL
open Matrix
variable (R : Type) [CommRing R] {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α]
  [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n]
variable {R}
variable (R)
variable {R}
variable (R)
variable {a b : Type}
variable [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
open Matrix
variable (R : Type) [CommRing R] {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α]
  [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n]
variable {R}
variable (R)
variable {R}
variable (R)
variable {a b : Type}
variable [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
namespace GlobalTheory.SmGL
namespace _root_.GlobalTheory.SmGL
theorem _root_.solution (e : a ⊕ b ≃ n) (g : GL a R × GL b R) :
    (_root_.GlobalTheory.SmGL.emb₂ R e g : Matrix n n R) =
      Matrix.reindex e e (fromBlocks g.1.val 0 0 g.2.val) := by
  ext i j
  obtain ⟨s, rfl⟩ := e.surjective i
  obtain ⟨t, rfl⟩ := e.surjective j
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply]
  rcases s with s | s <;> rcases t with t | t
  · exact _root_.GlobalTheory.SmGL.leviEmb_apply_same R (_root_.GlobalTheory.SmGL.two e)
      (_root_.GlobalTheory.SmGL.leviTwo R a b g) false s t
  · exact _root_.GlobalTheory.SmGL.leviEmb_apply_ne R (_root_.GlobalTheory.SmGL.two e)
      (_root_.GlobalTheory.SmGL.leviTwo R a b g) (by decide : false ≠ true) s t
  · exact _root_.GlobalTheory.SmGL.leviEmb_apply_ne R (_root_.GlobalTheory.SmGL.two e)
      (_root_.GlobalTheory.SmGL.leviTwo R a b g) (by decide : true ≠ false) s t
  · exact _root_.GlobalTheory.SmGL.leviEmb_apply_same R (_root_.GlobalTheory.SmGL.two e)
      (_root_.GlobalTheory.SmGL.leviTwo R a b g) true s t
end _root_.GlobalTheory.SmGL
end GlobalTheory.SmGL
