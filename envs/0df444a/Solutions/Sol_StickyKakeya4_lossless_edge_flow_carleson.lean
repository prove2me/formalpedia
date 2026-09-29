-- Prove2me | solution 1 for StickyKakeya4.lossless_edge_flow_carleson
-- status  : ACCEPTED   (prove)
-- author  : @sensei
-- created : 2026-09-26T04:30:56.980771+00:00
-- url     : https://prove2.me/submissions/96d9b7fb-b9fa-4dd7-b697-d4c5bbbfb74f

import Definitions.Def_sticky_kakeya4_core

open StickyKakeya4

theorem solution
    {n : ℕ} (T : NestedCarrierTree n)
    (incoming : Fin n → ENNReal)
    (paid : Fin n → ENNReal)
    (leafMass : Fin n → ENNReal)
    (hconserve : ∀ i,
      incoming i = paid i + leafMass i +
        Finset.univ.sum (fun j : Fin n =>
          if T.parent j = some i then incoming j else 0)) :
    Finset.univ.sum (fun i : Fin n => paid i + leafMass i) ≤
      Finset.univ.sum (fun i : Fin n =>
        if T.parent i = none then incoming i else 0) := by
  classical
  let roots : ENNReal := Finset.univ.sum (fun i : Fin n =>
    if T.parent i = none then incoming i else 0)
  let nonroots : ENNReal := Finset.univ.sum (fun i : Fin n =>
    if T.parent i = none then 0 else incoming i)
  let payments : ENNReal := Finset.univ.sum (fun i : Fin n => paid i + leafMass i)
  by_cases hroots : roots = ⊤
  · simpa [roots, hroots]
  have hincoming_ne_top : ∀ i, incoming i ≠ ⊤ := by
    intro i
    induction hlevel : T.level i using Nat.strong_induction_on generalizing i with
    | h k ih =>
        cases hp : T.parent i with
        | none =>
            have hle : incoming i ≤ roots := by
              calc
                incoming i = (if T.parent i = none then incoming i else 0) := by simp [hp]
                _ ≤ roots := by
                  dsimp [roots]
                  exact Finset.single_le_sum (s := Finset.univ)
                    (f := fun j : Fin n =>
                      if T.parent j = none then incoming j else 0)
                    (fun j hj => bot_le) (Finset.mem_univ i)
            intro hitop
            apply hroots
            apply top_unique
            simpa [hitop] using hle
        | some p =>
            have hpfinite : incoming p ≠ ⊤ :=
              ih (T.level p) (by simpa [hlevel] using T.parent_level hp) p rfl
            have hchild : incoming i ≤ incoming p := by
              calc
                incoming i =
                    (if T.parent i = some p then incoming i else 0) := by simp [hp]
                _ ≤ Finset.univ.sum (fun j : Fin n =>
                    if T.parent j = some p then incoming j else 0) := by
                  exact Finset.single_le_sum (s := Finset.univ)
                    (f := fun j : Fin n =>
                      if T.parent j = some p then incoming j else 0)
                    (fun j hj => bot_le) (Finset.mem_univ i)
                _ ≤ paid p + leafMass p +
                    Finset.univ.sum (fun j : Fin n =>
                      if T.parent j = some p then incoming j else 0) := by
                  simpa using add_le_add_right
                    (show (0 : ENNReal) ≤ paid p + leafMass p from bot_le)
                    (Finset.univ.sum (fun j : Fin n =>
                      if T.parent j = some p then incoming j else 0))
                _ = incoming p := by simpa only [hconserve p]
            intro hitop
            apply hpfinite
            apply top_unique
            simpa [hitop] using hchild
  have hnonroots : nonroots ≠ ⊤ := by
    dsimp [nonroots]
    apply ENNReal.sum_ne_top.mpr
    intro i hi
    by_cases hp : T.parent i = none
    · simp [hp]
    · simp [hp, hincoming_ne_top i]
  have hdouble :
      Finset.univ.sum (fun i : Fin n =>
        Finset.univ.sum (fun j : Fin n =>
          if T.parent j = some i then incoming j else 0)) = nonroots := by
    rw [Finset.sum_comm]
    dsimp [nonroots]
    apply Finset.sum_congr rfl
    intro j hj
    cases hp : T.parent j with
    | none => simp [hp]
    | some p => simp [hp]
  have hsplit : Finset.univ.sum incoming = roots + nonroots := by
    calc
      Finset.univ.sum incoming = Finset.univ.sum (fun i : Fin n =>
          (if T.parent i = none then incoming i else 0) +
          (if T.parent i = none then 0 else incoming i)) := by
        apply Finset.sum_congr rfl
        intro i hi
        cases hp : T.parent i <;> simp [hp]
      _ = roots + nonroots := by
        rw [Finset.sum_add_distrib]
  have hbalance : roots + nonroots = payments + nonroots := by
    calc
      roots + nonroots = Finset.univ.sum incoming := by simpa only [hsplit]
      _ = Finset.univ.sum (fun i : Fin n =>
            paid i + leafMass i +
              Finset.univ.sum (fun j : Fin n =>
                if T.parent j = some i then incoming j else 0)) := by
          apply Finset.sum_congr rfl
          intro i hi
          exact hconserve i
      _ = payments + nonroots := by
          rw [Finset.sum_add_distrib, hdouble]
  change payments ≤ roots
  apply (ENNReal.add_le_add_iff_right hnonroots).mp
  exact hbalance.ge
