-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_EffectiveHS_EffectiveHilbertSamuelJetLemmas_exists_unit_dd50c86e45ea
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T08:08:00.749832+00:00
-- url     : https://prove2.me/submissions/9590b844-d29d-44d7-b6f0-7e0b073c6c59

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_EffectiveHilbertSamuel_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_EffectiveHilbertSamuel_SymbolExtensionProperty
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_EffectiveHilbertSamuel_MemSectionsOfHolLineBundleEquiv
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_EffectiveHilbertSamuel_JetOfMonomialSumStatement
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_EffectiveHilbertSamuel_AnalyticAtOfHoloOn

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.EffectiveHS
open ReciprocityTheory.AnForm.M
noncomputable section
open GroundTheory.Heights₂.Heights.EffectiveHS.EffectiveHilbertSamuelJetLemmas
variable {D : ℕ} {U : Type} [TopologicalSpace U]
namespace GroundTheory.Heights₂.Heights.EffectiveHS.EffectiveHilbertSamuelJetLemmas
theorem _root_.solution {N : ℕ} (A : FinHolAtlas D U) (e : Fin N → Fin A.n → U → ℂ)
    (he : NoCommonZero A e) {S : Set U} (hS : S.Finite) :
    ∃ c : Fin N → ℂ, ∀ x ∈ S, lin e c (chartIdx A x) x ≠ 0 := by
  classical
  let φ : U → (Fin N → ℂ) →ₗ[ℂ] ℂ := fun x =>
    ∑ k, e k (chartIdx A x) x • (LinearMap.proj k : (Fin N → ℂ) →ₗ[ℂ] ℂ)
  have hφ : ∀ x c, φ x c = lin e c (chartIdx A x) x := by
    intro x c
    simp [φ, lin, Finset.sum_apply, mul_comm]
  have hne : ∀ x, LinearMap.ker (φ x) ≠ ⊤ := by
    intro x htop
    obtain ⟨k, hk⟩ := he x
    have h0 : Pi.single k 1 ∈ LinearMap.ker (φ x) := htop ▸ Submodule.mem_top
    rw [LinearMap.mem_ker, hφ] at h0
    have hl : lin e (Pi.single k 1) = e k := by simp [lin, Pi.single_apply]
    rw [hl] at h0
    exact hk h0
  have hss := Submodule.iUnion_ssubset_of_forall_ne_top_of_card_lt hS.toFinset
    (fun x => LinearMap.ker (φ x)) hne (by rw [ENat.card_eq_top_of_infinite]; exact ENat.natCast_lt_top _)
  obtain ⟨c, -, hc⟩ := Set.exists_of_ssubset hss
  refine ⟨c, fun x hx h0 => hc ?_⟩
  rw [Set.mem_iUnion₂]
  exact ⟨x, hS.mem_toFinset.2 hx, by rw [SetLike.mem_coe, LinearMap.mem_ker, hφ]; exact h0⟩
end GroundTheory.Heights₂.Heights.EffectiveHS.EffectiveHilbertSamuelJetLemmas
