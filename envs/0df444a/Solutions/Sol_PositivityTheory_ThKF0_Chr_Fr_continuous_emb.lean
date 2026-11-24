-- Prove2me | solution 1 for PositivityTheory.ThKF0.Chr.Fr.continuous_emb
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:59:59.034004+00:00
-- url     : https://prove2.me/submissions/ca0f8b1f-0071-44fd-b4d2-0be5ce9d135a

import Definitions.Def_Development_WeilBound_CoreStatements_CompactAveragingSplitting_EigenvectorLifting_SiegelTransportAlg
import Definitions.Def_Development_WeilBound_ThetaLifts_LeviDeterminants_CharacterAdmissibility_DoublingGramFromBlocks

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PositivityTheory PositivityTheory.ThKF0 PositivityTheory.ThKF0.Chr
open Matrix GlobalTheory.WeilM PositivityTheory.ThK.SiegelT
variable {R : Type} [CommRing R] {E : Type} [CommRing E] [Algebra R E] {c : E →ₐ[R] E}
  {β β₁ μ ν : Type} [Fintype β] [DecidableEq β] [Fintype β₁] [DecidableEq β₁] [Fintype μ] [DecidableEq μ]
  [Fintype ν] [DecidableEq ν]
variable {J : Matrix β β E} {J₁ : Matrix β₁ β₁ E} {H : Matrix μ μ E} {ι : Matrix β β₁ E} {Z : Matrix β μ E}
  {π : Matrix β₁ β E} {ρ : Matrix μ β E}
namespace PositivityTheory.ThKF0.Chr
namespace Fr
theorem _root_.solution [TopologicalSpace E] [IsTopologicalRing E] (h : Fr c J J₁ H ι Z π ρ) :
    Continuous fun g : UG c J₁ => h.emb (g, 1) := by
  refine Continuous.subtype_mk (Units.continuous_iff.2 ⟨?_, ?_⟩) _
  · exact ((continuous_const.matrix_mul (Units.continuous_val.comp continuous_subtype_val)).matrix_mul
      continuous_const).add (continuous_const (y := Z * (1 : Matrix μ μ E) * ρ))
  · exact ((continuous_const.matrix_mul (Units.continuous_coe_inv.comp continuous_subtype_val)).matrix_mul
      continuous_const).add (continuous_const (y := Z * (1 : Matrix μ μ E) * ρ))
end Fr
end PositivityTheory.ThKF0.Chr
