-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Model_InvOpenInside_exists_of_isAffineOpen_2c89d146c622
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T04:40:56.366111+00:00
-- url     : https://prove2.me/submissions/29b67e92-174c-4351-9084-d2d666e76bd1

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_StatementsInvOpenInside
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_PInvOpenInside
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_InvOpenInside_mem_range_baseChangeMap_f272b605a89d

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Model
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite
noncomputable section
open GroundTheory.Heights₂.Heights.Model.InvOpenInside
namespace GroundTheory.Heights₂.Heights.Model.InvOpenInside
theorem _root_.solution {X : Scheme.{0}} (f : X ⟶ SpecZ) (p : Nat.Primes) (W : X.Opens)
    (hW : Set.range (baseChangeMap f (ZLoc p)) ⊆ Set.range W.ι) {U : X.Opens}
    (hU : IsAffineOpen U) :
    ∃ s ∈ (Ideal.span {((p : ℕ) : ℤ)}).primeCompl,
      ∀ x ∈ U, x ∉ W → s ∈ (f.base x).asIdeal := by
  set S := (Ideal.span {((p : ℕ) : ℤ)}).primeCompl with hS
  set T : Set (PrimeSpectrum Γ(X, U)) := hU.fromSpec.base ⁻¹' (W : Set X)ᶜ with hTdef
  have hT : IsClosed T := W.isOpen.isClosed_compl.preimage hU.fromSpec.base.hom.continuous
  have hf : ∀ P : Spec Γ(X, U),
      (f.base (hU.fromSpec.base P)).asIdeal = P.asIdeal.comap (Int.castRingHom Γ(X, U)) := by
    intro P
    have h : hU.fromSpec ≫ f = Spec.map (CommRingCat.ofHom (Int.castRingHom Γ(X, U))) :=
      specZIsTerminal.hom_ext _ _
    rw [← Scheme.Hom.comp_apply, h]
    rfl
  have hW' : ∀ x : X, Disjoint (S : Set ℤ) (f.base x).asIdeal → x ∈ W := by
    intro x hx
    have := hW (mem_range_baseChangeMap f p x hx)
    rwa [Scheme.Opens.range_ι] at this
  have hI : ¬ Disjoint (PrimeSpectrum.vanishingIdeal T : Set Γ(X, U))
      (S.map (Int.castRingHom Γ(X, U)) : Set Γ(X, U)) := by
    intro hd
    obtain ⟨P, hP, hIP, hPS⟩ := Ideal.exists_le_prime_disjoint _ _ hd
    obtain ⟨Q, rfl⟩ : ∃ Q : Spec Γ(X, U), Q.asIdeal = P := ⟨⟨P, hP⟩, rfl⟩
    have hQ : hU.fromSpec Q ∉ W := by
      change Q ∈ T
      rw [← hT.closure_eq, ← PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure]
      exact hIP
    apply hQ
    apply hW'
    rw [hf Q]
    refine Set.disjoint_left.mpr fun s hs hsP => ?_
    exact Set.disjoint_left.mp hPS hsP ⟨s, hs, rfl⟩
  obtain ⟨a, haI, ⟨s, hs, rfl⟩⟩ := Set.not_disjoint_iff.mp hI
  refine ⟨s, hs, fun x hxU hxW => ?_⟩
  have hxU' : x ∈ Set.range hU.fromSpec := by rw [hU.range_fromSpec]; exact hxU
  obtain ⟨Q, rfl⟩ := hxU'
  rw [hf]
  exact (PrimeSpectrum.mem_vanishingIdeal _ _).mp haI Q hxW
end GroundTheory.Heights₂.Heights.Model.InvOpenInside
