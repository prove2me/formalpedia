-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_IrreducibleGermRegularConnected_proof_cd19fd2f7eb1
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T05:03:13.644365+00:00
-- url     : https://prove2.me/submissions/251aca35-c4af-4487-9cb6-396a1bc260a1

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StIrreducibleGermRegularConnected
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StLocalParametrisation
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StParametrisationSheetsConnected
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PIrreducibleGermRegularConnected
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_regLocus_subset_369db4101cd9


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
open Topology
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
namespace IrreducibleGermRegularConnected
theorem _root_.solution (hpar : LocalParametrisation.Statement)
    (hsheets : ParametrisationSheetsConnected.Statement) :
    IrreducibleGermRegularConnected.Statement := by
  intro σ _ X w hX hirr U hU
  obtain ⟨d, A, B, D, δ, N, hBU, hP⟩ := hpar σ X w hX hirr U hU
  have hS := hsheets σ X w B d A D δ N hP hirr
  obtain ⟨hBo, hwXB, -, -, -, -, -, -, -, -, hchart, hdense⟩ := hP

  have hSreg : {x | x ∈ X ∩ B ∧ δ (A x) ≠ 0} ⊆ regLocus (X ∩ B) := by
    rintro x ⟨hxXB, hx⟩
    obtain ⟨O, V, g, hO, hV, hxV, hg, hAg, hXV⟩ := hchart x hxXB hx
    exact ⟨hxXB, d, A, O, V, g, hO, hV, hxV, hg, hAg, hXV⟩
  exact ⟨B, hBo, hwXB.2, hBU, hS.subset_closure hSreg ((regLocus_subset _).trans hdense)⟩
end IrreducibleGermRegularConnected
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
