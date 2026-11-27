-- Prove2me | solution 1 for UpperTheory.Top.boundedTw
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T05:33:43.381549+00:00
-- url     : https://prove2.me/submissions/4fb46d16-3dc4-4bac-9c49-1aa563b9c311

import Definitions.Def_Development_AutomorphicArithmetic_CharacterBoxes_TwistForm
import Definitions.Def_Development_AutomorphicArithmetic_CharacterBoxes_BoundedTw
import Theorems.Thm_Formalism_GaloisCohomology_scalRep_apply
import Theorems.Thm_Formalism_HC_An_induces_of
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
import Theorems.Thm_Formalism_HC_Level_mem_ofSub
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GaloisCohomology.scalRep_apply
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv


section
open Formalism.HC UpperTheory.Top
private theorem UpperTheory.Top.boundedTw_key (ψ : PChar) (φ : Frame) (H : HostRaw φ) (htw : TwistForm ψ H) (hdiv : ψ.N ∣ H.QS)
    (hpr : ∀ l : ℕ, l.Prime → l ∣ H.QS → l ∣ 2 * ψ.N) (θ : φ.Char) (hθ : θ ∈ H.Bounded (Level.cyc ψ).KEPT)
    (N : ℕ) (χ : DirichletCharacter ℂ N) (hχ : H.IsPrimOf θ χ) :
    ∃ (ξ : DirichletCharacter ℂ ψ.N) (i j : Fin 2), (i ≠ 0 ∨ j ≠ 0) ∧
      An.Induces χ (tw (fun a => ξ (a : ZMod ψ.N)) H.q H.d i j) (2 * ψ.N * H.q * H.d) := by
  have hθ' : θ ∈ φ.Xp ∧ ¬H.Kept (Level.cyc ψ).KEPT θ ∨ θ ∈ φ.Xm := hθ
  have hχ' : An.Induces χ (H.dirAt θ) H.condN := hχ
  have htriv : Frame.TrivialOnFirstFactor θ := by
    rcases hθ' with ⟨h, -⟩ | h
    · exact h.1
    · exact h.1
  obtain ⟨ξ, hξ, i, j, hiod, heq⟩ := htw θ htriv
  have hNc : ψ.N ∣ H.condN := Dvd.dvd.mul_right (Dvd.dvd.mul_right hdiv _) _
  refine ⟨ξ, i, j, ?_, hχ'.1, ?_⟩
  · by_contra hij
    push_neg at hij
    obtain ⟨rfl, rfl⟩ := hij
    rcases hθ' with ⟨-, hnk⟩ | hm
    · apply hnk
      refine ⟨PChar.of ξ, (Level.mem_ofSub _ _).2 ⟨ξ, hξ, rfl⟩, (PChar.of ξ).prim, fun a ha => ?_⟩
      have ha' : a.Coprime ψ.N := Nat.Coprime.coprime_dvd_right hNc ha
      rw [(An.induces_of ξ).2 a ha', heq a ha]
      simp [tw]
    · have h1 := hm.2
      rw [h1] at hiod
      have h2 := congrArg Units.val hiod
      norm_num at h2
  · intro a ha
    have hq : a.Coprime H.q :=
      Nat.Coprime.coprime_dvd_right (dvd_mul_of_dvd_left (dvd_mul_left _ _) _) ha
    have hd : a.Coprime H.d := Nat.Coprime.coprime_dvd_right (dvd_mul_left _ _) ha
    have hQ : a.Coprime H.QS := by
      apply Nat.coprime_of_dvd
      intro l hl hla hlQ
      have hl2 : l ∣ 2 * ψ.N * H.q * H.d :=
        dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (hpr l hl hlQ) _) _
      exact hl.not_dvd_one (ha.gcd_eq_one ▸ Nat.dvd_gcd hla hl2)
    have hc : a.Coprime H.condN := Nat.Coprime.mul_right (Nat.Coprime.mul_right hQ hq) hd
    rw [hχ'.2 a hc, heq a hc]
end

set_option autoImplicit false
open Formalism.HC UpperTheory.Top
namespace UpperTheory.Top
theorem _root_.solution :
    ∀ (ψ : PChar) (φ : Frame) (H : HostRaw φ) (eps Y x : ℝ), 0 < eps → 1 ≤ x → Y ≤ x → TwistForm ψ H → ψ.N ∣ H.QS →
      (∀ l : ℕ, l.Prime → l ∣ H.QS → l ∣ 2 * ψ.N) → PairGood ψ.N eps Y x H.q H.d →
      H.BoundedCharsPointwise (Level.cyc ψ).KEPT x eps ∧
        ∀ θ ∈ H.Bounded (Level.cyc ψ).KEPT, ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), H.IsPrimOf θ χ → ‖An.logDerivativeAtOne χ‖ ≤ 4 * Real.log x := by
  intro ψ φ H eps Y x he hx hY htw hdiv hpr hg
  refine ⟨fun θ hθ N _ χ hχ => ?_, fun θ hθ N _ χ hχ => ?_⟩
  · obtain ⟨ξ, i, j, hij, hI⟩ := UpperTheory.Top.boundedTw_key ψ φ H htw hdiv hpr θ hθ N χ hχ
    exact (hg.bounds ξ i j hij N χ hI x hY le_rfl).1.trans
      (Real.rpow_le_rpow_of_exponent_le hx (by linarith))
  · obtain ⟨ξ, i, j, hij, hI⟩ := UpperTheory.Top.boundedTw_key ψ φ H htw hdiv hpr θ hθ N χ hχ
    exact (hg.bounds ξ i j hij N χ hI x hY le_rfl).2
end UpperTheory.Top
