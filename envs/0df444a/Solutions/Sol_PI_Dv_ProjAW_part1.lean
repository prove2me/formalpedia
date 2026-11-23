-- Prove2me | solution 1 for PI.Dv.ProjAW.part1
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:03:12.281709+00:00
-- url     : https://prove2.me/submissions/7a8c9afe-aa15-4aff-a2b2-b585310b433c

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_DivisionRowsRationalLattice
import Definitions.Def_Formalism_PeriodIntegrals_IdxCalc
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LengthIndex_LenAtEqZero
import Theorems.Thm_PI_Dv_ProjAW_mem_cutE
import Theorems.Thm_PI_Dv_ProjAW_mem_imgE

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.Dv PI.Dv.ProjAW
open NumberField IsDedekindDomain Formalism.BasicNotions
variable {K : Type} [Field K] [NumberField K] [StarRing K]
variable (A : HLat K)
namespace PI.Dv.ProjAW
theorem _root_.solution {f : Module.End K A.V} {n : ℕ} (hn : ∀ x ∈ A.L, ((n : ℕ) : 𝓞 K) • f x ∈ A.L) :
    ∀ x ∈ imgE A f A.L, ((n : ℕ) : 𝓞 K) • x ∈ cutE A f A.L := by
  intro x hx
  obtain ⟨y, hy, rfl⟩ := (mem_imgE A f A.L x).1 hx
  refine (mem_cutE A f A.L _).2 ⟨hn y hy, ((n : ℕ) : 𝓞 K) • y, ?_⟩
  exact LinearMap.map_smul_of_tower f _ y
end PI.Dv.ProjAW
