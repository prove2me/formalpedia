-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_LinesLatticeBasis_proof_e1dc639893aa
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:20:34.813988+00:00
-- url     : https://prove2.me/submissions/922d7d39-9de5-42b1-ba80-08f1ba2d92de

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsLines
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PLinesLatticeBasis

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
namespace GroundTheory.Heights₂.Heights
namespace LinesLatticeBasis
theorem _root_.solution : LinesLatticeBasis.Statement := by
  intro V _ _ _ ι _ hcard M hM
  let b0 := Module.Free.chooseBasis ℤ M
  let B : Module.Basis (Module.Free.ChooseBasisIndex ℤ M) ℚ V := b0.extendOfIsLattice ℚ
  have hc : Fintype.card (Module.Free.ChooseBasisIndex ℤ M) = Fintype.card ι := by
    rw [hcard, Module.finrank_eq_card_basis B]
  let e := Fintype.equivOfCardEq hc
  refine ⟨B.reindex e, ?_⟩
  rw [Module.Basis.range_reindex]
  have hB : Set.range B = M.subtype '' Set.range b0 := by
    rw [← Set.range_comp]
    ext x
    simp [B, Module.Basis.extendOfIsLattice_apply]
  rw [hB, ← Submodule.map_span, b0.span_eq, Submodule.map_top, Submodule.range_subtype]
end LinesLatticeBasis
end GroundTheory.Heights₂.Heights
