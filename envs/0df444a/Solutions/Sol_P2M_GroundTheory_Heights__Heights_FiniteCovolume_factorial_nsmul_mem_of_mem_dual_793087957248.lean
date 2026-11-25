-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FiniteCovolume_factorial_nsmul_mem_of_mem_dual_793087957248
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T05:13:37.620115+00:00
-- url     : https://prove2.me/submissions/3f5170c6-7f6b-4cb5-9b61-a26aa41f6b47

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StComplementLattice
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PLinePairOrbitsFinite
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PComplementLattice

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FiniteCovolume
open NumberField GroundTheory.Automorphic Module
noncomputable section
variable {F E : Type*} [Field F] [Field E] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E]
variable {W : Type*} [AddCommGroup W] [Module E W]
omit [NumberField E]
namespace GroundTheory.Heights₂.Heights.FiniteCovolume
theorem _root_.solution {h : HermitianForm F E W} {D : ℕ} {La : AddSubgroup W}
    (hLa : IsDIntegral h D La) {y : W} (hy : y ∈ dualLattice h La) : D.factorial • y ∈ La := by
  have hk : La.relIndex (dualLattice h La) • y ∈ La := by
    have := AddSubgroup.nsmul_index_mem (La.addSubgroupOf (dualLattice h La)) ⟨y, hy⟩
    exact AddSubgroup.mem_addSubgroupOf.1 this
  obtain ⟨c, hc⟩ := Nat.dvd_factorial (Nat.pos_of_ne_zero hLa.index_ne_zero) hLa.index_le
  rw [hc, mul_comm, ← smul_smul]
  exact La.nsmul_mem hk c
end GroundTheory.Heights₂.Heights.FiniteCovolume
