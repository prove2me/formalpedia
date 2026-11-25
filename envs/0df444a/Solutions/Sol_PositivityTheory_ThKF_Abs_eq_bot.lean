-- Prove2me | solution 1 for PositivityTheory.ThKF.Abs.eq_bot
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:06:54.657818+00:00
-- url     : https://prove2.me/submissions/c0681e01-3d8b-4fc9-b58d-0797115337cb

import Mathlib
import Definitions.Def_Development_WeilBound_ThetaLifts_CartanFactorisation_SpanOrbitStab
import Theorems.Thm_PositivityTheory_ThKF_Abs_compl
import Theorems.Thm_PositivityTheory_ThKF_Abs_simple

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PositivityTheory PositivityTheory.ThKF PositivityTheory.ThKF.Abs
open scoped InnerProductSpace
variable {U : Type} [NormedAddCommGroup U] [InnerProductSpace ℂ U]
namespace PositivityTheory.ThKF.Abs
theorem _root_.solution {St : Submodule ℂ U → Prop} (h : Proj St) (hinf : ∀ s : Set (Submodule ℂ U), (∀ S ∈ s, St S) → St (sInf s))
    (horth : ∀ S, St S → St Sᗮ) (N : Submodule ℂ U) (hN : St N)
    (hu : ∀ M, Maximal (fun P => St P ∧ P ≠ ⊤) M → N ≤ M) : N = ⊥ := by
  by_contra hne
  obtain ⟨S, hS, hSN, hS0, hs⟩ := simple h hinf horth N hN hne
  have nle : ¬ S ≤ Sᗮ := fun hle => hS0 ((Submodule.eq_bot_iff _).2 fun x hx => inner_self_eq_zero.1 (hle hx x hx))
  refine nle (hSN.trans (hu _ ⟨⟨horth S hS, fun ht => nle (ht ▸ le_top)⟩, fun P hP hle => ?_⟩))
  have hPS : St (P ⊓ S) := by
    rw [← sInf_pair]; exact hinf _ (by rintro _ (rfl | rfl); exacts [hP.1, hS])
  rcases hs _ hPS inf_le_right with hb | hb
  · intro x hx
    obtain ⟨a, ha, hxa⟩ := compl h S hS x
    have : a ∈ P ⊓ S := ⟨by simpa using P.sub_mem hx (hle hxa), ha⟩
    rw [hb, Submodule.mem_bot] at this
    simpa [this] using hxa
  · exfalso
    refine hP.2 (eq_top_iff.2 fun x _ => ?_)
    obtain ⟨a, ha, hxa⟩ := compl h S hS x
    have : a ∈ P := (by rw [hb]; exact ha : a ∈ P ⊓ S).1
    simpa using P.add_mem (hle hxa) this
end PositivityTheory.ThKF.Abs
