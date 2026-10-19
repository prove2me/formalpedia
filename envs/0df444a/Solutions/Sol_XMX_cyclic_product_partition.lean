-- Prove2me | solution 1 for XMX.cyclic_product_partition
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T14:22:27.911115+00:00
-- url     : https://prove2.me/submissions/11161bfd-59e0-4913-bb9d-ecd9bfdee034

import Definitions.Def_XMX_CyclicPartition

open XMX

theorem solution (N d : ℕ) (_hN : 0 < N) :
    Function.Bijective (fun p : ZMod N × (Fin d → ZMod N) => cyclicTuple N d p.1 p.2) ∧
    ∀ (offset : Fin d → ZMod N) (t : Fin (d + 1)),
      Function.Bijective (fun anchor => cyclicTuple N d anchor offset t) := by
  constructor
  · constructor
    · rintro ⟨a, u⟩ ⟨b, v⟩ h
      have hab : a = b := congrFun h 0
      apply Prod.ext hab
      funext j
      have hj := congrFun h j.succ
      simpa [cyclicTuple, hab] using hj
    · intro x
      refine ⟨(x 0, fun j => x j.succ - x 0), ?_⟩
      funext t
      refine Fin.cases ?_ (fun j => ?_) t
      · rfl
      · simp [cyclicTuple]
  · intro offset t
    refine Fin.cases ?_ (fun j => ?_) t
    · change Function.Bijective (id : ZMod N → ZMod N)
      exact Function.bijective_id
    · constructor
      · intro a b h
        exact add_right_cancel (show a + offset j = b + offset j from h)
      · intro y
        exact ⟨y - offset j, by simp [cyclicTuple]⟩
