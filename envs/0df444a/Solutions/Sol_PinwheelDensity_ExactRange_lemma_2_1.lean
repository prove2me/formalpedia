-- Prove2me | solution 1 for PinwheelDensity.ExactRange.lemma_2_1
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T07:50:00.861603+00:00
-- url     : https://prove2.me/submissions/ac0f2128-3065-4215-8d30-7555f4a82aa3

import Mathlib
import Definitions.Def_PinwheelDensity_ExactRange_Schedulable

section
set_option autoImplicit false

namespace PinwheelDensity.ExactRange

theorem chk_lemma_2_1 (P : List ℕ) (hP : ∀ a ∈ P, 1 ≤ a) (hfree : NoScheduleWithFreeDay P)
    (x : ℕ) (hx : 1 ≤ x) : ¬ ZSchedulable (P ++ [x]) := by
  rintro ⟨σ⟩
  have hlen : (P ++ [x]).length = P.length + 1 := by simp
  let emb : Fin P.length → Fin (P ++ [x]).length := fun i => ⟨i.1, by omega⟩
  let last : Fin (P ++ [x]).length := ⟨P.length, by omega⟩
  let σ' : ZSchedule P :=
    { days := fun i => σ.days (emb i)
      disjoint := by
        intro i j hij
        exact σ.disjoint (fun h => hij (Fin.ext (by simpa [emb] using congrArg Fin.val h)))
      hits := by
        intro i t
        have := σ.hits (emb i) t
        have e : (P ++ [x]).get (emb i) = P.get i := by
          simp only [List.get_eq_getElem, emb]
          exact List.getElem_append_left i.2
        rw [e] at this
        exact this }
  obtain ⟨d, hd⟩ := σ.hits last 0
  have hd1 : d ∈ σ.days last := hd.1
  refine hfree σ' d ?_
  intro i hi
  have hne : emb i ≠ last := by
    intro h; have := congrArg Fin.val h; simp [emb, last] at this; have := i.2; omega
  exact (Set.disjoint_left.mp (σ.disjoint hne)) hi hd1

end PinwheelDensity.ExactRange
end

theorem solution : type_of% @PinwheelDensity.ExactRange.chk_lemma_2_1 := @PinwheelDensity.ExactRange.chk_lemma_2_1
