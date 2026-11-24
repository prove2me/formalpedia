-- Prove2me | solution 1 for PositivityTheory.ThKF0.Chr.rel_dv
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:36:40.774633+00:00
-- url     : https://prove2.me/submissions/f58d6c49-6780-40b3-9cf8-b6c6dc65fd67

import Definitions.Def_Development_WeilBound_ThetaLifts_LeviDeterminants_CharacterAdmissibility_SchrodingerApplyZeroOfFst
import Definitions.Def_Development_WeilBound_ThetaLifts_LeviDeterminants_CharacterAdmissibility_BoxCancel

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PositivityTheory PositivityTheory.ThKF0 PositivityTheory.ThKF0.Chr
open Matrix GlobalTheory.WeilM
variable {R : Type} [CommRing R] {κ κ₁ : Type}
namespace PositivityTheory.ThKF0.Chr
theorem _root_.solution {S : V R κ ≃ₗ[R] V R κ} {j : κ₁ → κ} (hj : Function.Injective j) {w w' : V R κ} {w₁ w₁' : V R κ₁} :
    Rel (dbS S) (Sum.map j j) (dv w w') (dv w₁ w₁') ↔ Rel S j w w₁ ∧ Rel S j w' w₁' := by
  have e : ∀ a b : κ₁ → R, Function.extend (Sum.map j j) (Sum.elim a b) 0 =
      Sum.elim (Function.extend j a 0) (Function.extend j b 0) := fun a b => by
    funext k
    by_cases h : ∃ x, Sum.map j j x = k
    · obtain ⟨x, rfl⟩ := h
      rw [(hj.sumMap hj).extend_apply]
      rcases x with x | x <;> simp [hj.extend_apply]
    · rw [Function.extend_apply' _ _ _ h]
      rcases k with k | k
      · rw [Sum.elim_inl, Function.extend_apply' _ _ _ fun ⟨x, hx⟩ => h ⟨Sum.inl x, by simp [hx]⟩]; rfl
      · rw [Sum.elim_inr, Function.extend_apply' _ _ _ fun ⟨x, hx⟩ => h ⟨Sum.inr x, by simp [hx]⟩]; rfl
  rw [Rel, dbS_dv]
  simp only [Rel, dv, e, funext_iff, Sum.forall, Function.comp_apply, Sum.map_inl, Sum.map_inr, Sum.elim_inl,
    Sum.elim_inr, Pi.neg_apply, neg_inj]
  tauto
end PositivityTheory.ThKF0.Chr
