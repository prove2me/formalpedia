-- Prove2me | solution 1 for P7ThreeColor.Seed.connected_p3free_complete
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T10:10:12.015019+00:00
-- url     : https://prove2.me/submissions/148f482f-5fa0-4b56-bfab-c0fc1eceaa50

import Mathlib
import Definitions.Def_P7ThreeColor_Seed_Basic

set_option autoImplicit false
open P7ThreeColor.Seed

theorem ind_p3 {W : Type*} (H : SimpleGraph W) (u v w : W) (huv : H.Adj u v) (hvw : H.Adj v w)
    (huw : u ≠ w) (hn : ¬ H.Adj u w) : (SimpleGraph.pathGraph 3).IsIndContained H := by
  have h1 : u ≠ v := huv.ne
  have h2 : v ≠ w := hvw.ne
  refine ⟨⟨⟨![u, v, w], ?_⟩, ?_⟩⟩
  · intro a b hab
    fin_cases a <;> fin_cases b <;> simp_all [eq_comm]
  · intro a b
    fin_cases a <;> fin_cases b <;> simp [SimpleGraph.pathGraph_adj] <;>
      first | exact huv | exact hvw | exact hn | exact huv.symm | exact hvw.symm | exact fun h => hn h.symm | skip

theorem solution {W : Type*} (H : SimpleGraph W)
    (hH : H.Connected) (h3 : PFree 3 H) :
    ∀ u v : W, u ≠ v → H.Adj u v := by
  intro u v huv
  have key : ∀ x y, H.Adj x y → (x = u ∨ H.Adj u x) → (y = u ∨ H.Adj u y) := by
    intro x y hxy hx
    rcases hx with rfl | hx
    · exact Or.inr hxy
    · by_cases hyu : y = u
      · exact Or.inl hyu
      · by_cases hy : H.Adj u y
        · exact Or.inr hy
        · exact absurd (ind_p3 H u x y hx hxy (Ne.symm hyu) hy) h3
  have hreach : ∀ x z (p : H.Walk x z), (x = u ∨ H.Adj u x) → (z = u ∨ H.Adj u z) := by
    intro x z p
    induction p with
    | nil => exact id
    | cons h p ih => exact fun hx => ih (key _ _ h hx)
  obtain ⟨p⟩ := hH.preconnected u v
  rcases hreach u v p (Or.inl rfl) with h | h
  · exact absurd h.symm huv
  · exact h
