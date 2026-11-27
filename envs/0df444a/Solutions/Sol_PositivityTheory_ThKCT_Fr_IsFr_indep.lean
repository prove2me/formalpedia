-- Prove2me | solution 1 for PositivityTheory.ThKCT.Fr.IsFr.indep
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T05:23:29.361046+00:00
-- url     : https://prove2.me/submissions/c98199d1-a109-433b-932d-c01846c0656e

import Mathlib
import Definitions.Def_Development_WeilBound_ThetaLifts_SmallCones_ColsOfMul
import Theorems.Thm_PositivityTheory_ThKCT_Fr_fr_mulVec

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option linter.unusedSectionVars false
open PositivityTheory PositivityTheory.ThKCT PositivityTheory.ThKCT.Fr
open Matrix
variable {R S : Type} [CommRing R] [CommRing S] {d e : Type} [Fintype d] [DecidableEq d] [Fintype e] [DecidableEq e]
variable {ε : R} {A' : Matrix (e ⊕ Fin 2) d R} {c : R →+* R} {J : Matrix d d R} {J₁ : Matrix e e R} {ι : Matrix d e R} {x y : d → R}
namespace PositivityTheory.ThKCT.Fr
namespace IsFr
theorem _root_.solution (h : IsFr c ε J J₁ ι x y A') {u u' : e → R} {s t s' t' : R}
    (e1 : ι *ᵥ u + s • x + t • y = ι *ᵥ u' + s' • x + t' • y) : u = u' ∧ s = s' ∧ t = t' := by
  rw [← fr_mulVec, ← fr_mulVec] at e1
  have := congrArg (A' *ᵥ ·) e1
  simp only [mulVec_mulVec, h.inv2, one_mulVec] at this
  exact ⟨funext fun j => congrFun this (Sum.inl j), congrFun this (Sum.inr 0), congrFun this (Sum.inr 1)⟩
end IsFr
end PositivityTheory.ThKCT.Fr
