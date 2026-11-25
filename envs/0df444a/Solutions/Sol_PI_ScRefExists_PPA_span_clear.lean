-- Prove2me | solution 1 for PI.ScRefExists.PPA.span_clear
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:38:08.357519+00:00
-- url     : https://prove2.me/submissions/45a68a72-46ae-4795-b88c-e1f456fd5772

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeReferenceFrame_PPAssemble
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeReferenceFrame_NatCastSmulMemL
import Theorems.Thm_PI_ScRefExists_PPA_oE_smul
import Theorems.Thm_PI_ScRefExists_PPA_natE_smul
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv


section
noncomputable section
open NumberField Formalism.MainNotions.S IsDedekindDomain
namespace PI.ScRefExists.PPA
open PI.ScRefExists.Sk
variable (I : Formalism.MainNotions.S.AutInst)
private theorem mem_Ap_lemma (p : ℕ) (x : I.E) :
    x ∈ Ap I p ↔ ∃ s : ℕ, Nat.Coprime s p ∧ ∃ a : 𝓞 I.E, (s : I.E) * x = (a : I.E) :=
  Iff.rfl
end PI.ScRefExists.PPA
end
end

set_option autoImplicit false
noncomputable section
open NumberField Formalism.MainNotions.S IsDedekindDomain
open PI PI.ScRefExists PI.ScRefExists.PPA
open PI.ScRefExists.Sk
variable (I : Formalism.MainNotions.S.AutInst)
namespace PI.ScRefExists.PPA
theorem _root_.solution (p : ℕ) (S : Set (Fin I.n → I.E)) {y : Fin I.n → I.E}
    (hy : y ∈ Submodule.span (Ap I p) S) :
    ∃ s : ℕ, Nat.Coprime s p ∧ (s : I.E) • y ∈ Submodule.span (𝓞 I.E) S := by
  have key : ∀ (a : 𝓞 I.E) {z : Fin I.n → I.E}, z ∈ Submodule.span (𝓞 I.E) S →
      (a : I.E) • z ∈ Submodule.span (𝓞 I.E) S := fun a z hz => by
    rw [← oE_smul]
    exact Submodule.smul_mem _ a hz
  have keyN : ∀ (t : ℕ) {z : Fin I.n → I.E}, z ∈ Submodule.span (𝓞 I.E) S →
      (t : I.E) • z ∈ Submodule.span (𝓞 I.E) S := fun t z hz => by
    rw [natE_smul]
    exact Submodule.smul_mem _ _ hz
  induction hy using Submodule.span_induction with
  | mem x hx => exact ⟨1, Nat.coprime_one_left p, by simpa using Submodule.subset_span hx⟩
  | zero => exact ⟨1, Nat.coprime_one_left p, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨s, hs, hsx⟩ := hx
    obtain ⟨t, ht, hty⟩ := hy
    refine ⟨s * t, Nat.Coprime.mul hs ht, ?_⟩
    have e : ((s * t : ℕ) : I.E) • (x + y) = (t : I.E) • ((s : I.E) • x) + (s : I.E) • ((t : I.E) • y) := by
      simp only [Nat.cast_mul, smul_add, smul_smul, mul_comm (t : I.E) (s : I.E)]
    rw [e]
    exact add_mem (keyN t hsx) (keyN s hty)
  | smul c x _ hx =>
    obtain ⟨s, hs, hsx⟩ := hx
    obtain ⟨s0, hs0, a, ha⟩ := (mem_Ap_lemma I p (c : I.E)).mp c.2
    refine ⟨s0 * s, Nat.Coprime.mul hs0 hs, ?_⟩
    have hc : c • x = (c : I.E) • x := rfl
    have e : ((s0 * s : ℕ) : I.E) • (c • x) = (a : I.E) • ((s : I.E) • x) := by
      rw [hc, smul_smul, smul_smul, ← ha]
      push_cast
      congr 1
      ring
    rw [e]
    exact key a hsx
end PI.ScRefExists.PPA
