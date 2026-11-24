-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_Cech_Transport_proof_0f907ba81f5e
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:34:01.488013+00:00
-- url     : https://prove2.me/submissions/bae90f68-2188-4816-83e5-bf86eae4e528

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsSerrePoly
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PCechTransport

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman
noncomputable section
universe u v w
open GroundTheory.Heights₂.Heights.Kleiman.Cech
namespace GroundTheory.Heights₂.Heights.Kleiman.Cech
namespace Transport
theorem _root_.solution : Transport.Statement.{u, v, w} := by
  intro n U R _ G _ _ G' _ _ ρ ρ' deg deg' φ hφ hdeg hinj hmap i

  have minj : ∀ i, Function.Injective (mapC (G := G) (G' := G') φ i) :=
    fun i s t h => funext fun I => hinj I.1 (congrFun h I)

  have lift : ∀ (i : ℕ) (w' : Cochain G' i), w' ∈ Cdeg G' deg' i →
      ∃ w ∈ Cdeg G deg i, mapC φ i w = w' := by
    intro i w' hw'
    have h : ∀ I : Idx U i, ∃ x ∈ deg I.1, φ I.1 x = w' I := fun I => by
      have hI : w' I ∈ deg' I.1 := hw' I (Set.mem_univ _)
      rw [← hmap I.1] at hI
      exact Submodule.mem_map.mp hI
    choose w hw hφw using h
    exact ⟨w, fun I _ => hw I, funext fun I => hφw I⟩

  have bdry : ∀ (i : ℕ) (z : Cochain G i), mapC φ i z ∈ bdryDeg G' deg' ρ' i → z ∈ bdryDeg G deg ρ i := by
    intro i z h
    cases i with
    | zero =>
      change mapC φ 0 z ∈ (⊥ : Submodule R _) at h
      change z ∈ (⊥ : Submodule R _)
      rw [Submodule.mem_bot] at h ⊢
      exact minj 0 (h.trans (map_zero _).symm)
    | succ i =>
      change mapC φ (i + 1) z ∈ (Cdeg G' deg' i).map (d G' ρ' i) at h
      change z ∈ (Cdeg G deg i).map (d G ρ i)
      obtain ⟨w', hw', hd⟩ := Submodule.mem_map.mp h
      obtain ⟨w, hw, rfl⟩ := lift i w' hw'
      refine Submodule.mem_map.mpr ⟨w, hw, minj (i + 1) ?_⟩
      rw [mapC_d φ hφ]
      exact hd
  constructor
  · rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    change Submodule.Quotient.mk _ = 0 at hx
    have hx' := (Submodule.Quotient.mk_eq_zero _).mp hx
    exact (Submodule.Quotient.mk_eq_zero _).mpr (bdry i z hx')
  · intro y
    obtain ⟨z', rfl⟩ := Submodule.Quotient.mk_surjective _ y
    obtain ⟨w, hw, hwz⟩ := lift i z' z'.2.2
    have hdw : d G ρ i w = 0 := by
      apply minj (i + 1)
      rw [mapC_d φ hφ, hwz, map_zero]
      exact z'.2.1
    refine ⟨Submodule.Quotient.mk ⟨w, hdw, hw⟩, ?_⟩
    change Submodule.Quotient.mk _ = _
    congr 1
    exact Subtype.ext hwz
end Transport
end GroundTheory.Heights₂.Heights.Kleiman.Cech
