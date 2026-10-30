-- Prove2me | solution 1 for WilliamsonShmoys.three_vertex_successor_is_other_outgoing_dart__p2m_551112cf_8b4c_4517_8603_726684976d71_a4
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-10-29T22:45:06.59746+00:00
-- url     : https://prove2.me/submissions/2a1ef2e0-27e5-4dd0-a46f-6eb352055de6

import Mathlib.Combinatorics.SimpleGraph.Dart

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (F : Type) [Fintype F]
    (corner : F → Fin 3 → V)
    (dart : (F × Fin 3) ≃ H.Dart)
    (hTail : ∀ f i, (dart (f, i)).fst = corner f i)
    (hHead : ∀ f i, (dart (f, i)).snd = corner f (i + 1))
    (hInjective : ∀ f, Function.Injective (corner f)) :
    let succ : H.Dart → H.Dart :=
      fun a => dart ((dart.symm a.symm).1, (dart.symm a.symm).2 + 1)
    ∀ d : H.Dart, (succ d).fst = d.fst ∧ succ d ≠ d := by
  dsimp only
  intro d
  let p := dart.symm d.symm
  have hp : dart p = d.symm := dart.apply_symm_apply d.symm
  have htail : (dart (p.1, p.2 + 1)).fst = d.fst := by
    rw [hTail, ← hHead p.1 p.2]
    simpa [p] using congrArg (fun a : H.Dart => a.snd) hp
  have hdistinct : dart (p.1, p.2 + 1) ≠ d := by
    intro heq
    have hcorner : corner p.1 ((p.2 + 1) + 1) = corner p.1 p.2 := by
      calc
        corner p.1 ((p.2 + 1) + 1) = (dart (p.1, p.2 + 1)).snd := (hHead _ _).symm
        _ = d.snd := congrArg (fun a : H.Dart => a.snd) heq
        _ = (dart (p.1, p.2)).fst := by
          simpa [p] using (congrArg (fun a : H.Dart => a.fst) hp).symm
        _ = corner p.1 p.2 := hTail _ _
    have hidx : (p.2 + 1) + 1 = p.2 := (hInjective p.1) hcorner
    have hcycle : ∀ i : Fin 3, i + 1 + 1 ≠ i := by decide
    exact hcycle p.2 hidx
  exact ⟨htail, hdistinct⟩
