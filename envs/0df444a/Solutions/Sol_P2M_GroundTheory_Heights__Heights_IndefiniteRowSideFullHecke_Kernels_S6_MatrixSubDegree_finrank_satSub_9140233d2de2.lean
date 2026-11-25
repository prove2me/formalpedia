-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Kernels_S6_MatrixSubDegree_finrank_satSub_9140233d2de2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:52:01.542813+00:00
-- url     : https://prove2.me/submissions/d0940277-170b-4a8a-872f-1579547edc79

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_ImportsMore
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_LinearIndependentSumElimOfExact
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_AssemblyLines
import Definitions.Def_GroundTheory_PowerSubgroups_CountableNeighbourhoods_ExistsSmulMemFamilyOfSpanEqTop
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_CardQuotientEqGenIndex

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kernels
open NumberField NumberField.ComplexEmbedding Matrix GroundTheory.Heights₂.Heights TensorProduct
open scoped nonZeroDivisors ComplexOrder
noncomputable section
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kernels
namespace S6.MatrixSubDegree
theorem _root_.solution {K : Type} [Field K] [NumberField K] {N : ℕ}
    (M : Submodule (𝓞 K) (Fin N → K)) [Module.Finite (𝓞 K) M] {r : ℕ} (u : Fin r → Fin N → K)
    (hu : LinearIndependent K u) (s : Fin r → satSub M u) (hs : LinearIndependent (𝓞 K) s) :
    Module.finrank (𝓞 K) (satSub M u) = r := by
  set W := Submodule.span K (Set.range u)
  let L : satSub M u →ₗ[𝓞 K] (Fin N → K) := M.subtype ∘ₗ (satSub M u).subtype
  have hLi : Function.Injective L := by
    intro x y h
    exact Subtype.ext (Subtype.ext h)
  apply le_antisymm
  · apply Module.finrank_le_of_rank_le
    apply rank_le
    intro T hT
    have h0 := hT.map_injOn L hLi.injOn
    have h1 : LinearIndependent K (L ∘ fun i : T => (i : satSub M u)) :=
      (LinearIndependent.iff_fractionRing (𝓞 K) K).mp h0
    have hmem : ∀ i : T, L i ∈ W := fun i => (i : satSub M u).2
    have h2 : LinearIndependent K (fun i : T => (⟨L i, hmem i⟩ : W)) :=
      LinearIndependent.of_comp W.subtype h1
    have := h2.fintype_card_le_finrank
    rw [finrank_span_eq_card hu, Fintype.card_fin, Fintype.card_coe] at this
    exact this
  · have := hs.fintype_card_le_finrank
    simpa using this
end S6.MatrixSubDegree
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kernels
