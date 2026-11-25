-- Prove2me | solution 1 for PI.KoszulExact.ofList_take_ofFn
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T09:48:39.895804+00:00
-- url     : https://prove2.me/submissions/b9d1256d-12e7-40ac-817f-6b4648646081

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_KoszulExactness_Ii
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_KoszulExactness_OfListTakeOfFn

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
universe u
open PI PI.KoszulExact
open RingTheory.Sequence
namespace PI.KoszulExact
theorem _root_.solution {R : Type u} [CommRing R] {D : ℕ} (s : Fin D → R) (i : ℕ) :
    Ideal.ofList ((List.ofFn s).take i) = Ii s i := by
  unfold Ideal.ofList Ii
  congr 1
  ext r
  simp only [Set.mem_setOf_eq, Set.mem_image]
  rw [List.mem_iff_getElem]
  constructor
  · rintro ⟨j, hj, rfl⟩
    simp only [List.length_take, List.length_ofFn] at hj
    exact ⟨⟨j, by omega⟩, by simp only; omega, by simp⟩
  · rintro ⟨j, hj, rfl⟩
    have := j.isLt
    exact ⟨j, by simp only [List.length_take, List.length_ofFn]; omega, by simp⟩
end PI.KoszulExact
