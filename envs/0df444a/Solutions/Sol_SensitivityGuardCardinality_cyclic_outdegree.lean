-- Prove2me | solution 1 for SensitivityGuardCardinality.cyclic_outdegree
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-11-24T20:21:25.183733+00:00
-- url     : https://prove2.me/submissions/f36b75ab-3394-4f36-af97-cf02ae53725c

import Definitions.Def_Sensitivity214439_PairedSemantic_Solutions_TournamentRegularDegrees
import Definitions.Def_Sensitivity214439_PairedSemantic_Solutions_TournamentSocketGuards
import Definitions.Def_Sensitivity214439_Phase0_Solutions_TournamentRegularDegrees
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Defs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace SensitivityGuardCardinality
end SensitivityGuardCardinality
namespace SensitivityRankMapCheckpoint
end SensitivityRankMapCheckpoint
namespace SensitivityRankedConstruction
end SensitivityRankedConstruction


/-! Regular degrees of the literal circulant and Paley guard graphs. -/
open SensitivityGuardCardinality
open SensitivityRankedConstruction SensitivityRankMapCheckpoint
open scoped Fin.CommRing

theorem solution {n : ℕ} [NeZero n] (v : Fin n) :
    (outNeighbors cyclicArc v).card = (cyclicSupport n).card := by
  classical
  let e : Fin n ≃ Fin n := {
    toFun := fun w => w - v
    invFun := fun d => d + v
    left_inv := by intro w; simp
    right_inv := by intro d; simp }
  apply Finset.card_equiv e
  intro w
  have hd : (w - v).val = (w.val + n - v.val) % n := by
    rw [Fin.val_sub]
    congr 1
    have hv := v.isLt
    omega
  simp only [outNeighbors, cyclicSupport, Finset.mem_filter, Finset.mem_univ, true_and]
  change (w ≠ v ∧ cyclicArc v w) ↔
    ((w - v).val ≠ 0 ∧ 0 < (w - v).val ∧ (w - v).val ≤ n / 2)
  simp only [ne_eq, Fin.val_eq_zero_iff, sub_eq_zero]
  rw [hd]
  rfl
