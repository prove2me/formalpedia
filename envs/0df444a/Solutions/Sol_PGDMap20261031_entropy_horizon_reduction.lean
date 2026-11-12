-- Prove2me | solution 1 for PGDMap20261031.entropy_horizon_reduction
-- status  : ACCEPTED   (prove)
-- author  : @Somehow
-- created : 2026-10-31T13:44:21.83557+00:00
-- url     : https://prove2.me/submissions/c5296117-d2b0-4b09-bc74-89a0d3d74d0a

import Mathlib.Tactic
import Definitions.Def_PGDMap20261031_Entropy

open PGDMap20261031

private lemma set_nonempty_of_isLUB {s : Set ℝ} {a : ℝ} (ha : IsLUB s a) : s.Nonempty := by
  by_contra hempty
  have : a ≤ a - 1 := ha.2 (by
    intro v hv
    exact (hempty ⟨v, hv⟩).elim)
  linarith

theorem solution : ExactEntropyPerformanceClaim → ErrorProfileLUBClaim →
    UniqueLocatedOptimumClaim → CommonFiniteHorizonClaim := by
  intro hexact hlub huniq M N hN z hz
  have nonneg (u : ℝ × ℝ) (hu : validGeometry u) : 0 ≤ contraction M u.1 u.2 := by
    apply le_trans (abs_nonneg (curvatureError M u.1 u.2 0))
    exact (hlub M u.1 u.2 hu).1 ⟨0, ⟨by norm_num, by norm_num⟩, rfl⟩
  have exactValue (u : ℝ × ℝ) (hu : validGeometry u) :
      omega M u.1 u.2 N = contraction M u.1 u.2 ^ (2 * N) := by
    exact (hexact M u.1 u.2 N hu hN).csSup_eq
      (set_nonempty_of_isLUB (hexact M u.1 u.2 N hu hN))
  constructor
  · intro u hu
    rw [exactValue z hz.1, exactValue u hu]
    exact pow_le_pow_left₀ (nonneg z hz.1) (hz.2 u hu) (2 * N)
  · intro u hu heq
    rw [exactValue u hu, exactValue z hz.1] at heq
    have heqr : contraction M u.1 u.2 = contraction M z.1 z.2 :=
      (pow_left_inj₀ (nonneg u hu) (nonneg z hz.1) (by omega : 2 * N ≠ 0)).mp heq
    have huo : IsGeometryOptimum M u := ⟨hu, by
      intro v hv
      rw [heqr]
      exact hz.2 v hv⟩
    obtain ⟨w, _, hw⟩ := (huniq M).1
    exact (hw u huo).trans (hw z hz).symm
