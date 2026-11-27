-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_RelAlgClosureFinite_proof_6a52e7199be1
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T05:02:23.304201+00:00
-- url     : https://prove2.me/submissions/ab9adeec-f790-4556-89cf-9fbedfcdaa82

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StRelAlgClosureFinite
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PRelAlgClosureFinite
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_RelAlgClosureFinite_linearIndependent_adjoin_bb5beed916b1

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open MvPolynomial IntermediateField.algebraAdjoinAdjoin
namespace GroundTheory.Heights₂.Heights.Inter
namespace RelAlgClosureFinite
theorem _root_.solution : RelAlgClosureFinite.Statement := by
  intro K L _ _ _ S hS
  obtain ⟨t, ht⟩ := exists_isTranscendenceBasis K L
  set M := algebraicClosure K L
  have hM : AlgebraicIndependent M ((↑) : t → L) := ht.1.algebraicClosure
  set E := IntermediateField.adjoin K (Set.range ((↑) : t → L))
  have halg : Algebra.IsAlgebraic E L := ht.isAlgebraic_field
  have htop : IntermediateField.adjoin E (S : Set L) = ⊤ := by
    rw [eq_top_iff]
    intro z _
    have hz : z ∈ IntermediateField.adjoin K (S : Set L) := hS ▸ IntermediateField.mem_top
    have hle : IntermediateField.adjoin K (S : Set L) ≤
        (IntermediateField.adjoin E (S : Set L)).restrictScalars K :=
      IntermediateField.adjoin_le_iff.2 fun y hy => IntermediateField.subset_adjoin E _ hy
    exact hle hz
  have hfin : FiniteDimensional E L := by
    have h := IntermediateField.finiteDimensional_adjoin (K := E) (S := (S : Set L))
      fun y _ => (halg.isAlgebraic y).isIntegral
    rw [htop] at h
    exact (IntermediateField.topEquiv (F := E) (E := L)).toLinearEquiv.finiteDimensional
  let b := Module.Basis.ofVectorSpace K M
  have hli : LinearIndependent E (fun i => ((b i : M) : L)) :=
    (LinearIndependent.iff_fractionRing (Algebra.adjoin K (Set.range ((↑) : t → L))) E).1
      (RelAlgClosureFinite.linearIndependent_adjoin M hM b.linearIndependent)
  have : Finite (Module.Basis.ofVectorSpaceIndex K M) := hli.finite
  exact Module.Finite.of_basis b
end RelAlgClosureFinite
end GroundTheory.Heights₂.Heights.Inter
