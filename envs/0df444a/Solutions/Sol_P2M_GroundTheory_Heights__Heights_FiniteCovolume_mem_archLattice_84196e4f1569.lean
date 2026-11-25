-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FiniteCovolume_mem_archLattice_84196e4f1569
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T04:12:06.067834+00:00
-- url     : https://prove2.me/submissions/dadb9d14-1f43-47e5-a9f8-37a1cb006af0

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_SecondCountableTopologyArchUnitary
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StArchCovolumeBound

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FiniteCovolume
open NumberField GroundTheory.Automorphic Module Matrix Topology MeasureTheory
noncomputable section
variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [IsTotallyComplex E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]
omit [IsTotallyComplex E] [Fintype ι] [DecidableEq ι]
namespace GroundTheory.Heights₂.Heights.FiniteCovolume
theorem _root_.solution {v : Basis ι E W} {La : AddSubgroup W} {y : InfinitePlace E → ι → ℂ} :
    y ∈ archLattice v La ↔ ∃ x ∈ La, vecAt v x = y := by
  change y ∈ La.map (vecAtHom v) ↔ _
  rw [AddSubgroup.mem_map]
  rfl
end GroundTheory.Heights₂.Heights.FiniteCovolume
