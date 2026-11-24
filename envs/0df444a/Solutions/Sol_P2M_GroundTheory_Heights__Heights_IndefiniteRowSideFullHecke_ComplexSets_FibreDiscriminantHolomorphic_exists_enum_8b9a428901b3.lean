-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_FibreDiscriminantHolomorphic_exists_enum_8b9a428901b3
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:27:58.695001+00:00
-- url     : https://prove2.me/submissions/3c6660ff-c1c0-48b2-8d4a-a34b3a066634

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StFibreDiscriminantHolomorphic
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PRiemannExtensionAnalytic
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PFibreDiscriminantHolomorphic

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
open Topology Filter Metric Set
noncomputable section
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.FibreDiscriminantHolomorphic
variable {σ : Type} [Fintype σ]
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.FibreDiscriminantHolomorphic
theorem _root_.solution {α : Type*} {S : Set α} {N : ℕ} (h : S.encard = N) :
    ∃ p : Fin N → α, Function.Injective p ∧ range p = S := by
  have hfin := Set.finite_of_encard_eq_coe h
  have hc : hfin.toFinset.card = N := by
    have := hfin.encard_eq_coe_toFinset_card
    rw [h] at this
    exact_mod_cast this.symm
  let e := hfin.toFinset.equivFin
  refine ⟨fun i => (e.symm (Fin.cast hc.symm i)).1, ?_, ?_⟩
  · intro i j hij
    exact Fin.cast_injective _ (e.symm.injective (Subtype.ext hij))
  · ext x
    constructor
    · rintro ⟨i, rfl⟩
      exact hfin.mem_toFinset.1 (e.symm _).2
    · intro hx
      refine ⟨Fin.cast hc (e ⟨x, hfin.mem_toFinset.2 hx⟩), ?_⟩
      simp
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.FibreDiscriminantHolomorphic
