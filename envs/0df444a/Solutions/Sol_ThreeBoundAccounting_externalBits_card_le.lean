-- Prove2me | solution 1 for ThreeBoundAccounting.externalBits_card_le
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-25T22:44:36.947759+00:00
-- url     : https://prove2.me/submissions/de0f9af0-1f7e-4cdc-ae21-074fe827e7f8

import Definitions.Def_SensitivityCampaign
import Definitions.Def_SensitivitySeparation
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Combinatorics.Hall.Finite
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Finset.Union
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.Sort
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Definitions.Def_Sensitivity213303_CandidateCoherence
import Definitions.Def_Sensitivity213303_GlobalAccounting
import Definitions.Def_Sensitivity213303_GradedPositiveBoundary
import Definitions.Def_Sensitivity213303_GuardAugmentation
import Definitions.Def_Sensitivity213303_ProfileClosures
import Definitions.Def_Sensitivity213303_Q2CandidateTypes
import Definitions.Def_Sensitivity213303_Q2Enumeration
import Definitions.Def_Sensitivity213303_RecursiveLowerBounds
import Definitions.Def_Sensitivity213303_ResidualCaps
import Definitions.Def_Sensitivity213303_TournamentHighRows
import Definitions.Def_Sensitivity213303_WitnessLifting

namespace OAI.Paper320
end OAI.Paper320
namespace ThreeBoundPositive
end ThreeBoundPositive
namespace ThreeBoundProfiles
end ThreeBoundProfiles
namespace ThreeBoundWitness
end ThreeBoundWitness
namespace OAI.Paper320
end OAI.Paper320
namespace ThreeBoundProfiles
end ThreeBoundProfiles
namespace ThreeBoundWitness
end ThreeBoundWitness
section
/-
Actual positive-boundary transfer for equal-target graded rows.
Every guard count and bit flip below uses the concrete guarded construction.
This is one part of the upper transfer, not a complete seed proof.
-/


set_option autoImplicit false
set_option maxHeartbeats 2500000
set_option linter.unusedSectionVars false

namespace ThreeBoundPositive
open OAI.Paper320 ThreeBoundWitness ThreeBoundProfiles
open scoped BigOperators Classical
noncomputable section

variable {L I V : Type} [Preorder L] [Fintype I] [Fintype V]





















@[simp] theorem card_liftBits (v : V) (c : Bool) (s : Finset I) :
    (liftBits v c s).card = s.card := Finset.card_map _

























end
end ThreeBoundPositive






end

section
/- Actual coordinate accounting: incoming arcs are deduplicated to child
positions, external arcs have residual multiplicity, and histograms are
derived identities. -/


set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option linter.unusedSectionVars false

namespace ThreeBoundAccounting
open OAI.Paper320 ThreeBoundWitness ThreeBoundProfiles ThreeBoundPositive
open scoped Classical BigOperators
noncomputable section
variable {V I K : Type} [Fintype V] [Fintype I] [Fintype K]































variable {L : Type} [Preorder L]



theorem failed_inter_high (S : Stage L I V) (F : L → (I → Bool) → Bool) (j : L)
    (x : ((V × Bool) × I) → Bool) (H : Finset V)
    (hH : ∀ w ∈ H, ∀ c : Bool, F (S.guard j) (child x w c) = true) (v : V) :
    failed S F j x v ∩ H = H.filter (S.Adj v) := by
  ext w
  simp only [Finset.mem_inter,failed,Finset.mem_filter,Finset.mem_univ,true_and]
  constructor
  · exact fun h => ⟨h.2,h.1.1⟩
  · exact fun h => ⟨⟨h.2,hH w h.1 (S.label v w)⟩,h.1⟩

theorem externalHeads_card (S : Stage L I V) (F : L → (I → Bool) → Bool) (j : L)
    (x : ((V × Bool) × I) → Bool) (H : Finset V)
    (hH : ∀ w ∈ H, ∀ c : Bool, F (S.guard j) (child x w c) = true) (v : V) :
    (externalHeads S F j x H v).card =
      (failed S F j x v).card-(H.filter (S.Adj v)).card := by
  unfold externalHeads
  have hh := Finset.card_sdiff_add_card_inter (failed S F j x v) H
  rw [failed_inter_high S F j x H hH v] at hh
  omega







end
end ThreeBoundAccounting




end

section
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option linter.unusedSectionVars false
namespace ThreeBoundAccounting
end ThreeBoundAccounting
open ThreeBoundAccounting
open OAI.Paper320 ThreeBoundWitness ThreeBoundProfiles ThreeBoundPositive
open scoped Classical BigOperators
variable {V I K : Type} [Fintype V] [Fintype I] [Fintype K]
variable {L : Type} [Preorder L]

theorem solution (S : Stage L I V) (F : L → (I → Bool) → Bool)
    (i j : L) (x : ((V × Bool) × I) → Bool) (G H : Finset V)
    (hH : ∀ w ∈ H, ∀ c : Bool, F (S.guard j) (child x w c) = true)
    (hweak : ∀ v ∈ G, ∀ w ∈ failed S F j x v,
      F (S.guard i) (child x w (S.label v w)) = true)
    (s : ℕ) (hs : BBound F (S.guard j) (S.guard i) s) :
    (externalBits S F j x G H).card ≤
      (∑ v ∈ G, ((failed S F j x v).card-(H.filter (S.Adj v)).card))*s := by
  unfold externalBits
  calc
    _ ≤ ∑ v ∈ G, ((externalHeads S F j x H v).biUnion fun w =>
        liftBits w (S.label v w)
          (flipsTo (F (S.guard j)) false (child x w (S.label v w)))).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ v ∈ G, (externalHeads S F j x H v).card*s := by
      apply Finset.sum_le_sum
      intro v hv
      calc
        _ ≤ ∑ w ∈ externalHeads S F j x H v,
            (liftBits w (S.label v w)
              (flipsTo (F (S.guard j)) false (child x w (S.label v w)))).card :=
          Finset.card_biUnion_le
        _ ≤ ∑ _w ∈ externalHeads S F j x H v, s := by
          apply Finset.sum_le_sum
          intro w hw
          rw [card_liftBits]
          exact hs _ (hweak v hv w (Finset.mem_sdiff.mp hw).1)
        _ = _ := by simp [Finset.sum_const,nsmul_eq_mul]
    _ = _ := by simp only [externalHeads_card S F j x H hH,Finset.sum_mul]
end
