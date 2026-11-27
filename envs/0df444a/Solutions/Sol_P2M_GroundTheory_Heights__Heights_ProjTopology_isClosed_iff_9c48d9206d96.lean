-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ProjTopology_isClosed_iff_9c48d9206d96
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-26T22:19:11.050325+00:00
-- url     : https://prove2.me/submissions/d2a10ff1-e74e-4ee1-abaa-a0de27394326

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ProjTopology
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
open scoped LinearAlgebra.Projectivization
variable {K V : Type*} [DivisionRing K] [AddCommGroup V] [Module K V] [TopologicalSpace V]
open GroundTheory.Heights₂.Heights.ProjTopology
theorem _root_.solution {s : Set (ℙ K V)} :
    IsClosed s ↔ IsClosed ((Projectivization.mk' K) ⁻¹' s : Set {v : V // v ≠ 0}) := by
  first
  | exact isQuotientMap_quotient_mk'.isClosed_preimage.symm
  | exact (isQuotientMap_quot_mk.isClosed_preimage).symm
  | (rw [← isOpen_compl_iff, ← isOpen_compl_iff]; exact Iff.rfl)



