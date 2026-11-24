-- Prove2me | solution 1 for SensitivityGuardCardinality.paired_checks_card
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-11-24T20:19:55.940637+00:00
-- url     : https://prove2.me/submissions/de2e0888-fa4f-4992-b29a-330462657b1d

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



theorem checks_card {V S : Type} [Fintype V]
    {guards : GuardFamily V S} {arc : V → V → Prop} (idx : GuardIndexing guards arc) (v : V) :
    (guards v).card = (Finset.univ.filter (arc v)).card := by
  rw [checks_eq_image idx v]
  apply Finset.card_image_iff.mpr
  intro w hw z hz heq
  obtain ⟨socket, hs⟩ := idx.nonempty v w (Finset.mem_filter.mp hw).2
  have hsz : socket ∈ idx.check v z := heq ▸ hs
  exact (idx.destination v w socket hs).symm.trans (idx.destination v z socket hsz)








































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
    (v : M × B) : (pairedTournamentGuards macroArc label internalArc v).card =
      Fintype.card B * (outNeighbors macroArc v.1).card + (outNeighbors internalArc v.2).card := by
  rw [checks_card (pairedIndexing macroArc label internalArc) v]
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
  rw [hsplit, Finset.card_union_of_disjoint hdisj]
  simp only [external, internal, Finset.card_product, Finset.card_univ,
    Finset.card_singleton, Nat.one_mul]
  ac_rfl
