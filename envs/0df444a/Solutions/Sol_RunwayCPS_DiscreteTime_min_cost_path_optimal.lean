-- Prove2me | solution 1 for RunwayCPS.DiscreteTime.min_cost_path_optimal
-- status  : ACCEPTED   (disprove)
-- author  : @Nickrobbins95
-- created : 2026-10-21T14:37:29.242601+00:00
-- url     : https://prove2.me/submissions/6b638d61-b871-49a3-b0ad-cdecc290c80c

import Mathlib
import Definitions.Def_RunwayCPS_DiscreteTime_ModifiedNetwork

set_option autoImplicit false

namespace RunwayCPS.DiscreteTime.Cex2f7af8f5

open RunwayCPS.DiscreteTime

/-- One aircraft, `k = 1`, zero separations, window `[0, 0]`, unit costs, and the
self-precedence pair `(0, 0)`. No schedule respects `(0, 0)` (it needs `p < p`), but the
pruning rule of `G` never detects a self-pair, so the modified network still has a path. -/
def I0 : Instance 1 where
  k := 1
  δ := fun _ _ => 0
  e := fun _ => 0
  l := fun _ => 0
  prec := {((0 : Fin 1), (0 : Fin 1))}
  c := fun _ _ => 1

theorem poly0 : PolygonIneq I0.δ := by
  intro m _ x _
  exact Nat.zero_le _

theorem cost_pos0 : ∀ a t, 0 < I0.c a t := by
  intro a t
  show (0 : ℝ) < 1
  norm_num

theorem gnode0 : IsGNode I0 1 [(0 : Fin 1)] := by
  decide

theorem path0 : ∃ P : ℕ → MNode 1, IsMPath I0 P := by
  refine ⟨fun _ => ⟨[(0 : Fin 1)], 0, 0⟩, ?_, ?_⟩
  · intro p hp1 hpn
    have hp : p = 1 := by omega
    subst hp
    refine ⟨gnode0, ?_, fun _ => rfl, fun h => absurd h (by omega)⟩
    show (0 : ℕ) ∈ Finset.Icc (I0.e _) (I0.l _)
    simp [I0]
  · intro p hp1 hpn
    omega

theorem no_sched0 : ¬ ∃ (σ : Fin 1 → Fin 1) (t : Fin 1 → ℕ), IsFeasible I0 σ t := by
  rintro ⟨σ, t, hf⟩
  have h := hf.2.2.2 ((0 : Fin 1), (0 : Fin 1)) (by simp [I0]) 0 0
    (Subsingleton.elim _ _) (Subsingleton.elim _ _)
  exact (lt_irrefl _ h)

theorem cex :
    ¬ (∀ {n : ℕ} [NeZero n] (I : Instance n) (hk : 1 ≤ I.k)
      (hpoly : PolygonIneq I.δ) (hc : ∀ a t, 0 < I.c a t),
      ((∃ (σ : Fin n → Fin n) (t : Fin n → ℕ), IsFeasible I σ t) ↔
          ∃ P : ℕ → MNode n, IsMPath I P) ∧
        (∀ C : ℝ, IsLeast (scheduleCosts I) C ↔ IsLeast (pathCosts I) C) ∧
        (∀ P : ℕ → MNode n, IsMPath I P → IsLeast (pathCosts I) (pathCost I P) →
          IsFeasible I (mSeq P) (mTimes P) ∧
            IsLeast (scheduleCosts I) (cost I (mSeq P) (mTimes P)))) := by
  intro h
  have h1 := (h (n := 1) I0 (le_refl _) poly0 cost_pos0).1
  exact no_sched0 (h1.mpr path0)

end RunwayCPS.DiscreteTime.Cex2f7af8f5

open RunwayCPS.DiscreteTime in
theorem solution :
    ¬ (∀ {n : ℕ} [NeZero n] (I : Instance n) (hk : 1 ≤ I.k)
      (hpoly : PolygonIneq I.δ) (hc : ∀ a t, 0 < I.c a t),
      ((∃ (σ : Fin n → Fin n) (t : Fin n → ℕ), IsFeasible I σ t) ↔
          ∃ P : ℕ → MNode n, IsMPath I P) ∧
        (∀ C : ℝ, IsLeast (scheduleCosts I) C ↔ IsLeast (pathCosts I) C) ∧
        (∀ P : ℕ → MNode n, IsMPath I P → IsLeast (pathCosts I) (pathCost I P) →
          IsFeasible I (mSeq P) (mTimes P) ∧
            IsLeast (scheduleCosts I) (cost I (mSeq P) (mTimes P)))) := by
  exact RunwayCPS.DiscreteTime.Cex2f7af8f5.cex

