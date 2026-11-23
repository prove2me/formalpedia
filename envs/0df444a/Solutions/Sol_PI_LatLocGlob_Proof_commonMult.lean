-- Prove2me | solution 1 for PI.LatLocGlob.Proof.commonMult
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:34:04.764502+00:00
-- url     : https://prove2.me/submissions/603b3c7f-562c-4734-ad2e-765530bfe4c5

import Definitions.Def_Formalism_PeriodIntegrals_LatLocGlob
import Definitions.Def_Lemmata_GeneralBFactThirdBisAlt_Imports
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalGlobalLattice_ExistsSmulMemOfLocal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.LatLocGlob PI.LatLocGlob.Proof
open PI.LatLocGlob
namespace PI.LatLocGlob.Proof
theorem _root_.solution {R ι : Type} [CommRing R] [IsDomain R] (P : ι → R → Prop)
    (hP : ∀ i c d, P i c → P i (d * c)) (T : Finset ι)
    (hT : ∀ i ∈ T, ∃ c : R, c ≠ 0 ∧ P i c) : ∃ c : R, c ≠ 0 ∧ ∀ i ∈ T, P i c := by
  classical
  induction T using Finset.induction_on with
  | empty => exact ⟨1, one_ne_zero, by simp⟩
  | insert a T ha ih =>
    obtain ⟨c, hc, hPc⟩ := ih (fun i hi => hT i (Finset.mem_insert_of_mem hi))
    obtain ⟨ca, hca, hPa⟩ := hT a (Finset.mem_insert_self a T)
    refine ⟨c * ca, mul_ne_zero hc hca, ?_⟩
    intro i hi
    rcases Finset.mem_insert.1 hi with rfl | hi
    · exact hP _ _ _ hPa
    · rw [mul_comm]; exact hP _ _ _ (hPc i hi)
end PI.LatLocGlob.Proof
