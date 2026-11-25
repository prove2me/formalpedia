-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_HilbertSamuel_card_eq_length_of_filtration_eb2ffd839cfb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T05:28:47.039159+00:00
-- url     : https://prove2.me/submissions/0d139afb-3b88-4e66-b67c-455775b31003

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsHilbert
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_ProjectiveSpaceIncrementHyp
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_WeightedHomogeneousSubmoduleBlockWeightIntEqRing
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_LengthLocalizedQuotientEqZero
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_HilbertSamuel_telescope_enat_094d3f3ee57a
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_HilbertSamuel_length_localized_quotient_eq_zero_506f8fa2ab32
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_HilbertSamuel_length_localized_quotient_self_c414b06e8dcf
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_HilbertSamuel_length_localized_step_9c3b7002c156

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HilbertSamuel
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR
noncomputable section
universe u
variable {R : Type*} [CommRing R]
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HilbertSamuel
theorem _root_.solution {M : Type*} [AddCommGroup M] [Module R M] {n : ℕ}
    (N : Fin (n + 1) → Submodule R M) (x : Fin n → M) (q : Fin n → Ideal R)
    (hN0 : N 0 = ⊥) (hNl : N (Fin.last n) = ⊤)
    (hsucc : ∀ j : Fin n, N j.succ = N j.castSucc ⊔ Submodule.span R {x j})
    (hprime : ∀ j, (q j).IsPrime) (hann : ∀ j (s : R), s • x j ∈ N j.castSucc ↔ s ∈ q j)
    (W : Ideal R) (hW : W ∈ (Module.annihilator R M).minimalPrimes) [W.IsPrime]
    [DecidablePred fun j => q j = W] :
    (((Finset.univ.filter fun j => q j = W).card : ℕ) : ℕ∞) =
      Module.length (Localization.AtPrime W) (LocalizedModule W.primeCompl M) := by
  let L : Fin (n + 1) → ℕ∞ := fun k =>
    Module.length (Localization.AtPrime W) (LocalizedModule W.primeCompl (M ⧸ N k))
  have hstep : ∀ j : Fin n, L j.castSucc = (if q j = W then 1 else 0) + L j.succ := by
    intro j
    simp only [L]
    rw [length_localized_step W (N j.castSucc) (N j.succ) (x j) (q j) (hsucc j) (hann j)]
    congr 1
    split_ifs with h
    · rw [h]
      exact length_localized_quotient_self W
    · apply length_localized_quotient_eq_zero
      intro hle
      apply h
      have hannq : Module.annihilator R M ≤ q j := by
        intro s hs
        rw [← hann j, Module.mem_annihilator.mp hs (x j)]
        exact zero_mem _
      exact le_antisymm hle (hW.2 ⟨hprime j, hannq⟩ hle)
  have h0 : L 0 = Module.length (Localization.AtPrime W) (LocalizedModule W.primeCompl M) := by
    simp only [L]
    rw [hN0]
    exact (IsLocalizedModule.mapEquiv W.primeCompl (LocalizedModule.mkLinearMap W.primeCompl _)
      (LocalizedModule.mkLinearMap W.primeCompl M) (Localization.AtPrime W)
      (Submodule.quotEquivOfEqBot ⊥ rfl)).length_eq
  have hl : L (Fin.last n) = 0 := by
    simp only [L]
    rw [hNl]
    have key : ∀ y : LocalizedModule W.primeCompl (M ⧸ (⊤ : Submodule R M)), y = 0 := by
      intro y
      induction y using LocalizedModule.induction_on with
      | h m s =>
        obtain ⟨m, rfl⟩ := Submodule.Quotient.mk_surjective _ m
        rw [(Submodule.Quotient.mk_eq_zero _).mpr Submodule.mem_top, LocalizedModule.zero_mk]
    have : Subsingleton (LocalizedModule W.primeCompl (M ⧸ (⊤ : Submodule R M))) :=
      ⟨fun a b => by rw [key a, key b]⟩
    exact Module.length_eq_zero
  rw [← h0, telescope_enat n L _ hstep, hl, add_zero, Finset.sum_boole]
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HilbertSamuel
