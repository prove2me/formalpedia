-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_FinGradedSub_cocycle_eq_coneSingle_d0d23a2f80fd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T09:40:11.437365+00:00
-- url     : https://prove2.me/submissions/0d8102a8-8eea-4a57-aaf3-1338617c0b75

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsTildeTail
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PTildeTailLoc
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PTildeTail
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_FinGradedSub_cellCone_of_subset_d748224c1d3f
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_FinGradedSub_cellCone_cocycle_9cb775dde1c6
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_locCone_degLoc_5fdd4721a38b


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman
open MvPolynomial
noncomputable section
universe u w
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω} (M : FinGradedSub (S := S) (x := x) Ω)
namespace GroundTheory.Heights₂.Heights.Kleiman
namespace FinGradedSub
theorem _root_.solution {c : ℤ} {z : Cech.Cochain (locSys S N M.coneSub) 0}
    (hz : z ∈ Cech.cocyDeg (locSys S N M.coneSub) (degLoc M.coneGraded c) locResS 0)
    (K : Cech.Idx (Finset.univ : Finset (Fin (N + 1))) 0) (hK : K.1.1 ⊆ support x) :
    ∃ v ∈ (M.tildeSys c).secs, M.cellCone K.1 (z K) = coneSingle S x c v := by
  obtain ⟨v, -, hzv⟩ := locCone_degLoc M c K.1 hK (hz.2 K (Set.mem_univ _))
  rw [← M.cellCone_of_subset hK] at hzv
  refine ⟨v, ?_, hzv⟩
  rw [SubSystem.secs, Submodule.mem_iInf]
  intro J
  obtain ⟨i, hi⟩ := J.2.1
  let Ki : Cech.Idx (Finset.univ : Finset (Fin (N + 1))) 0 :=
    ⟨⟨{i}, Finset.singleton_nonempty i, Finset.subset_univ _⟩, Finset.card_singleton i⟩
  have hKi : Ki.1.1 ⊆ support x := Finset.singleton_subset_iff.mpr (J.2.2 hi)
  obtain ⟨v', hv', hzv'⟩ := locCone_degLoc M c Ki.1 hKi (hz.2 Ki (Set.mem_univ _))
  rw [← M.cellCone_of_subset hKi, ← M.cellCone_cocycle (LinearMap.mem_ker.mp hz.1) K Ki hK hKi, hzv] at hzv'
  have hvv : v = v' := by
    have := congrArg (coeffAt S x c) hzv'
    rwa [coeffAt_coneSingle_same, coeffAt_coneSingle_same] at this
  rw [hvv]
  exact (M.tildeSys c).mono _ J (Finset.singleton_subset_iff.mpr hi) v' hv'
end FinGradedSub
end GroundTheory.Heights₂.Heights.Kleiman
