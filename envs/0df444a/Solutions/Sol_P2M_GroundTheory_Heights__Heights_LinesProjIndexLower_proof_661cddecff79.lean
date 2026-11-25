-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_LinesProjIndexLower_proof_661cddecff79
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T04:37:37.746399+00:00
-- url     : https://prove2.me/submissions/731f99ab-fc2c-4440-8ae9-79c78ce58d49

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsLines
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PLinesProjIndexLower
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_KLinesProjIndexLower_stdLattice_fg_bd02f800584d
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_KLinesProjIndexLower_stdLattice_span_7d21086f80d2

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
open NumberField
noncomputable section
open KLinesProjIndexLower
namespace GroundTheory.Heights₂.Heights
namespace LinesProjIndexLower
theorem _root_.solution (h1 : LinesProjLattice.Statement)
    (h2 : LinesIdealLatticeFG.Statement) (h3 : LinesIsLattice.Statement)
    (h4 : LinesGenIndexMono.Statement) (h5 : LinesIdealStdIndex.Statement) :
    LinesProjIndexLower.Statement := by
  intro K _ _ n m k a B τ ha hB hτ
  obtain ⟨hPfg, hPspan, hle⟩ := h1 K n m k a B τ ha hB hτ
  obtain ⟨hAfg, hAspan⟩ := h2 K k (fun j => a (τ j)) (fun j => ha (τ j))
  have hA := h3 K (Fin k) _ hAfg.restrictScalars hAspan
  have hP := h3 K (Fin k) _ hPfg hPspan
  have hS := h3 K (Fin k) _ (stdLattice_fg K k) (stdLattice_span K k)
  have key := h4 (Fin k → K) _ _ _ hA hP hS (Submodule.restrictScalars_mono ℤ hle)
  rw [← h5 K k (fun j => a (τ j))]
  exact key
end LinesProjIndexLower
end GroundTheory.Heights₂.Heights
