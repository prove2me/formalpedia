-- Prove2me | solution 1 for PositivityTheory.ThKF.Abs.simple
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T11:59:46.677888+00:00
-- url     : https://prove2.me/submissions/39484f9d-f0c5-467a-825e-7f9ad0f7eef7

import Mathlib
import Definitions.Def_Development_WeilBound_ThetaLifts_CartanFactorisation_SpanOrbitStab

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
    (horth : ∀ S, St S → St Sᗮ) (N : Submodule ℂ U) (hN : St N) (hne : N ≠ ⊥) :
    ∃ S, St S ∧ S ≤ N ∧ S ≠ ⊥ ∧ ∀ P, St P → P ≤ S → P = ⊥ ∨ P = S := by
  classical
  obtain ⟨f, hfN, hf0⟩ := (Submodule.ne_bot_iff N).1 hne
  obtain ⟨Z, Z', hZ, hf, e, hd⟩ := h f
  have ex : ∃ m, ∃ S, St S ∧ S ≤ N ∧ S ⊓ Z ≠ ⊥ ∧ Module.finrank ℂ ↥(S ⊓ Z) = m :=
    ⟨_, N, hN, le_rfl, (Submodule.ne_bot_iff _).2 ⟨f, ⟨hfN, hf⟩, hf0⟩, rfl⟩
  obtain ⟨S₀, h0, h0N, h0ne, h0r⟩ := Nat.find_spec ex
  have hmin : ∀ P, St P → P ≤ S₀ → P ⊓ Z = ⊥ ∨ P ⊓ Z = S₀ ⊓ Z := fun P hP hle => by
    by_cases hb : P ⊓ Z = ⊥
    · exact Or.inl hb
    · haveI : FiniteDimensional ℂ ↥(S₀ ⊓ Z) := Submodule.finiteDimensional_of_le (S₂ := Z) inf_le_right
      refine Or.inr (Submodule.eq_of_le_of_finrank_le (inf_le_inf_right _ hle) ?_)
      rw [h0r]
      exact Nat.find_min' ex ⟨P, hP, hle.trans h0N, hb, rfl⟩
  let S := sInf {P | St P ∧ S₀ ⊓ Z ≤ P}
  have hS : St S := hinf _ fun P hP => hP.1
  have hS0 : S ≤ S₀ := sInf_le ⟨h0, inf_le_left⟩
  have hZS : S₀ ⊓ Z ≤ S := le_sInf fun P hP => hP.2
  have inf2 : ∀ P Q, St P → St Q → St (P ⊓ Q) := fun P Q hP hQ => by
    rw [← sInf_pair]; exact hinf _ (by rintro _ (rfl | rfl) <;> assumption)
  refine ⟨S, hS, hS0.trans h0N, fun hb => h0ne (le_bot_iff.1 (hb ▸ hZS)), fun P hP hle => ?_⟩
  rcases hmin P hP (hle.trans hS0) with hb | hb
  · left
    have h2 : S₀ ⊓ Z ≤ Pᗮ := fun x hx u hu => by
      obtain ⟨y, hy, z, -, hyZ, hz, rfl⟩ := hd P hP u hu
      have y0 : y = 0 := by
        have : y ∈ P ⊓ Z := ⟨hy, hyZ⟩
        rwa [hb, Submodule.mem_bot] at this
      have hx' : x ∈ Z'ᗮ := e ▸ hx.2
      rw [y0, zero_add]
      exact hx' z hz
    have h3 : S ≤ Pᗮ := sInf_le ⟨horth P hP, h2⟩
    exact (Submodule.eq_bot_iff _).2 fun x hx => inner_self_eq_zero.1 (h3 (hle hx) x hx)
  · exact Or.inr (le_antisymm hle (sInf_le ⟨hP, hb ▸ inf_le_left⟩))
end PositivityTheory.ThKF.Abs
