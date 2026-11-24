-- Prove2me | solution 1 for SensitivityGuardCardinality.paired_guard_socket_count
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-11-24T20:19:59.886349+00:00
-- url     : https://prove2.me/submissions/ce419f3d-24a2-467c-9c67-c732730f67e2

import Definitions.Def_Sensitivity214439_PairedSemantic_Solutions_HighHeadGuardBridge
import Definitions.Def_Sensitivity214439_PairedSemantic_Solutions_TournamentSocketGuards
import Definitions.Def_Sensitivity214439_Phase0_Solutions_HighHeadGuardBridge
import Definitions.Def_Sensitivity214439_Phase0_Solutions_SocketGateConstruction
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
namespace SensitivityHighHeadGuardBridge
end SensitivityHighHeadGuardBridge
namespace SensitivityRankMapCheckpoint
end SensitivityRankMapCheckpoint
namespace SensitivityRankedConstruction
end SensitivityRankedConstruction

section


/-! Exact physical socket totals for every row of each checkpoint phase. -/

namespace SensitivityGuardCardinality

noncomputable section
open scoped Classical

open SensitivityRankedConstruction SensitivityHighHeadGuardBridge
open SensitivityRankMapCheckpoint
open scoped BigOperators

theorem checks_eq_image {V S : Type} [Fintype V]
    {guards : GuardFamily V S} {arc : V → V → Prop} (idx : GuardIndexing guards arc) (v : V) :
    guards v = (Finset.univ.filter (arc v)).image (idx.check v) := by
  classical
  ext check
  constructor
  · intro hc
    obtain ⟨w, hw, rfl⟩ := idx.complete v check hc
    exact Finset.mem_image.mpr ⟨w, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hw⟩, rfl⟩
  · intro hc
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hc
    exact idx.member v w (Finset.mem_filter.mp hw).2

theorem sum_guard_cards {V S : Type} [Fintype V]
    {guards : GuardFamily V S} {arc : V → V → Prop} (idx : GuardIndexing guards arc) (v : V) :
    ∑ check ∈ guards v, check.card =
      ∑ w ∈ Finset.univ.filter (arc v), (idx.check v w).card := by
  classical
  rw [checks_eq_image idx v]
  apply Finset.sum_image
  intro w hw z hz heq
  obtain ⟨socket, hs⟩ := idx.nonempty v w (Finset.mem_filter.mp hw).2
  have hsz : socket ∈ idx.check v z := heq ▸ hs
  exact (idx.destination v w socket hs).symm.trans (idx.destination v z socket hsz)









theorem pairedCheck_card {M B : Type} (label : M → M → Bool) (v w : M × B) :
    (pairedCheck label v w).card = if w.1 = v.1 then 2 else 1 := by
  classical
  unfold pairedCheck
  split <;> simp
































end
end SensitivityGuardCardinality

end

/-! Exact physical socket totals for every row of each checkpoint phase. -/
open SensitivityGuardCardinality
open scoped Classical
open SensitivityRankedConstruction SensitivityHighHeadGuardBridge
open SensitivityRankMapCheckpoint
open scoped BigOperators

theorem solution {M B : Type} [Fintype M] [Fintype B]
    (macroArc : M → M → Prop) (label : M → M → Bool) (internalArc : B → B → Prop)
    (v : M × B) :
    ∑ check ∈ pairedTournamentGuards macroArc label internalArc v, check.card =
      Fintype.card B * (outNeighbors macroArc v.1).card +
        2 * (outNeighbors internalArc v.2).card := by
  classical
  rw [sum_guard_cards (pairedIndexing macroArc label internalArc) v]
  let external := (outNeighbors macroArc v.1) ×ˢ (Finset.univ : Finset B)
  let internal := ({v.1} : Finset M) ×ˢ outNeighbors internalArc v.2
  have hsplit : Finset.univ.filter (pairedArc macroArc internalArc v) = external ∪ internal := by
    ext w
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union,
      external, internal, Finset.mem_product, Finset.mem_singleton,
      outNeighbors, and_true, pairedArc]
  have hdisj : Disjoint external internal := by
    apply Finset.disjoint_left.mpr
    intro w hw hi
    have hwm := Finset.mem_filter.mp (Finset.mem_product.mp hw).1
    have hiw := Finset.mem_singleton.mp (Finset.mem_product.mp hi).1
    exact hwm.2.1 hiw
  rw [hsplit, Finset.sum_union hdisj]
  have hext : (∑ w ∈ external, ((pairedIndexing macroArc label internalArc).check v w).card) =
      external.card := by
    calc
      _ = ∑ _ ∈ external, (1 : ℕ) := by
        apply Finset.sum_congr rfl
        intro w hw
        have hwm := Finset.mem_filter.mp (Finset.mem_product.mp hw).1
        exact (pairedCheck_card label v w).trans (if_neg hwm.2.1)
      _ = _ := by simp
  have hint : (∑ w ∈ internal, ((pairedIndexing macroArc label internalArc).check v w).card) =
      2 * internal.card := by
    calc
      _ = ∑ _ ∈ internal, (2 : ℕ) := by
        apply Finset.sum_congr rfl
        intro w hw
        have hwm := Finset.mem_singleton.mp (Finset.mem_product.mp hw).1
        exact (pairedCheck_card label v w).trans (if_pos hwm)
      _ = _ := by simp [Nat.mul_comm]
  rw [hext, hint]
  simp only [external, internal, Finset.card_product, Finset.card_univ,
    Finset.card_singleton, Nat.one_mul]
  ac_rfl
