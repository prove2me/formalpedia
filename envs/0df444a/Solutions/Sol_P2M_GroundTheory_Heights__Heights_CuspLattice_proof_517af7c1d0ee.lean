-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_CuspLattice_proof_517af7c1d0ee
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T04:55:24.124628+00:00
-- url     : https://prove2.me/submissions/6dde533e-57a9-450c-a296-1e77f1b53039

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_StatementsCusp
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_TransposeEqOfPosSemidef
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_PCuspLattice

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
open Matrix
noncomputable section
namespace GroundTheory.Heights₂.Heights
namespace CuspLattice
theorem _root_.solution (h1 : CuspShortVectors.Statement) (h2 : CuspLeadingMinima.Statement)
    (h3 : CuspCovolume.Statement) : CuspLattice.Statement := by
  intro D T
  obtain ⟨c₁, hc₁, H1⟩ := h1 D T
  obtain ⟨c₂, hc₂, H3⟩ := h3 D T
  exact ⟨c₁, c₂, hc₁, hc₂, fun p hp hu ℓ hℓ =>
    ⟨H1 p hp hu ℓ hℓ, h2 D T p hp hu ℓ hℓ, fun k v hv hli => H3 p hp hu ℓ hℓ k v hv hli⟩⟩
end CuspLattice
end GroundTheory.Heights₂.Heights
