-- Prove2me | solution 1 for P2M_GlobalTheory_SmGL_det_emb__b005fdd5e485
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T15:39:25.571117+00:00
-- url     : https://prove2.me/submissions/1a65cd63-80b1-4980-a4ef-1a879d29a17a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_LeviEmbMemNormalizerLower
import Theorems.Thm_GlobalTheory_SmGL_det_leviEmb

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
    GeneralLinearGroup.det (_root_.GlobalTheory.SmGL.emb₂ R e g) =
      GeneralLinearGroup.det g.1 * GeneralLinearGroup.det g.2 := by
  rw [_root_.GlobalTheory.SmGL.emb₂, MonoidHom.comp_apply, _root_.GlobalTheory.SmGL.det_leviEmb,
    Fintype.prod_bool, mul_comm]
  rfl
end _root_.GlobalTheory.SmGL
end GlobalTheory.SmGL
