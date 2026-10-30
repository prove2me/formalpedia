-- Prove2me | solution 1 for SkipFreeFluct.MBI.theorem_5_4
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-29T10:30:06.174407+00:00
-- url     : https://prove2.me/submissions/026f386d-a5d2-4c8b-8b15-eabf5d67880e
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_SkipFreeFluct_MBI_Chain
import Definitions.Def_SkipFreeFluct_MBI_Model
import Theorems.Thm_SkipFreeFluct_MBI_theorem_5_4_gf
import Theorems.Thm_SkipFreeFluct_MBI_theorem_5_4_calH_mbp
import Theorems.Thm_SkipFreeFluct_MBI_theorem_5_4_1
import Theorems.Thm_SkipFreeFluct_MBI_theorem_5_4_2
import Theorems.Thm_SkipFreeFluct_MBI_theorem_5_4_3
open scoped ENNReal Topology
open Filter MeasureTheory

open SkipFreeFluct.MBI in
theorem solution (P : MBIParams) (hP : P.Valid) :
    (∀ x : ℕ, ∀ s ∈ Set.Ico 0 (s0 P),
      HasSum (fun y : ℕ => calH P y x * s ^ y)
        (∫ v in (0 : ℝ)..s,
          v ^ x / psi P v * Real.exp (∫ u in v..s, phiImm P u / psi P u))) ∧
    (IsMBP P → ∀ x y : ℕ, calH P y x = Wz P ((y : ℤ) - x - 1) / y) ∧
    (AllTransient (Set.Ici 0) (mbiQ P) → ∀ x y : ℕ,
      IntI P x ≠ ⊤ ∧ resolvent (Set.Ici 0) (mbiQ P) x y ≠ ⊤ ∧
      (resolvent (Set.Ici 0) (mbiQ P) x y).toReal = piSeq P y * (IntI P x).toReal - calH P y x) ∧
    (IsMBP P → ∀ x y : ℕ, 1 ≤ y →
      resolvent (Set.Ici 0) (mbiQ P) x y ≠ ⊤ ∧
      (resolvent (Set.Ici 0) (mbiQ P) x y).toReal =
        1 / y * (s0 P ^ x * W P (y - 1) - Wz P ((y : ℤ) - x - 1))) ∧
    (AllTransient (Set.Ici 0) (mbiQ P) → ∀ x y : ℕ,
      (hitProb (Set.Ici 0) (mbiQ P) {(y : ℤ)} x).toReal =
        (piSeq P y * (IntI P x).toReal - calH P y x) / (piSeq P y * (IntI P y).toReal)) ∧
    (IsMBP P → ∀ x y : ℕ,
      (hitProb (Set.Ici 0) (mbiQ P) {(y : ℤ)} x).toReal =
        if 1 ≤ y then
          (s0 P ^ x * W P (y - 1) - Wz P ((y : ℤ) - x - 1)) / (s0 P ^ y * W P (y - 1))
        else s0 P ^ x) ∧
    (AllRecurrent (Set.Ici 0) (mbiQ P) → ∀ x y : ℕ,
      hitProb (Set.Ici 0) (mbiQ P) {(y : ℤ)} x = 1) ∧
    (∀ a x b : ℕ, a ≤ x → x + 1 ≤ b →
      (hitBeforeProb (Set.Ici 0) (mbiQ P) {(a : ℤ)} (Set.Ici (b : ℤ)) x).toReal =
          calH P b x / calH P b a ∧
      (hitProb (Set.Ici 0) (mbiQ P) (Set.Ioo (a : ℤ) b)ᶜ x).toReal =
          1 - ∑ z ∈ Finset.Ioo a b,
            (P.p * z + P.q) * (calH P b x / calH P b a * calH P z a - calH P z x) ∧
      (hitProb (Set.Ici 0) (mbiQ P) (Set.Ici (b : ℤ)) x).toReal =
          if 0 < P.beta + P.q then
            1 - ∑ z ∈ Finset.range b,
              (P.p * z + P.q) * (piSeq P z / piSeq P b * calH P b x - calH P z x)
          else
            1 + P.p * (∑ z ∈ Finset.range (b - x - 1), W P z) -
              W P (b - x - 1) / W P (b - 1) * (1 + P.p * ∑ z ∈ Finset.range (b - 1), W P z)) :=
  ⟨theorem_5_4_gf P hP, theorem_5_4_calH_mbp P, (theorem_5_4_1 P hP).1, (theorem_5_4_1 P hP).2,
    (theorem_5_4_2 P hP).1, (theorem_5_4_2 P hP).2.1, (theorem_5_4_2 P hP).2.2,
    theorem_5_4_3 P hP⟩
