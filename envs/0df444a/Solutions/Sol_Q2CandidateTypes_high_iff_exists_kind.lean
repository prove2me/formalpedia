-- Prove2me | solution 1 for Q2CandidateTypes.high_iff_exists_kind
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-25T22:40:05.517757+00:00
-- url     : https://prove2.me/submissions/b9235058-f76b-4259-9dfa-e4455b1c09a6

import Definitions.Def_SensitivityCampaign
import Definitions.Def_SensitivitySeparation
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Combinatorics.Hall.Finite
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Sort
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.Sort
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Definitions.Def_Sensitivity213303_CandidateCoherence
import Definitions.Def_Sensitivity213303_GuardAugmentation
import Definitions.Def_Sensitivity213303_Q2CandidateTypes
import Definitions.Def_Sensitivity213303_Q2Enumeration
import Definitions.Def_Sensitivity213303_TournamentHighRows

namespace TournamentHighRows
end TournamentHighRows
section
/-
Exact eight-type decomposition for equal-target graded rows through tolerance 2.

The predicates below refer to the actual child truth values and actual failed
guard count. The classification does not assume a sensitivity bound. It can be
instantiated with target b z := F (threshold b) z, and guard := F g.
-/


set_option autoImplicit false
set_option maxHeartbeats 3000000

namespace Q2CandidateTypes
open scoped Classical
open TournamentHighRows

variable {X V : Type}





















theorem ofKind_high (guard : X → Prop) (target : ℕ → X → Prop)
    (Q d : ℕ) (x y : X) (k : Fin 8)
    (hk : OfKind guard target Q d x y k) : High guard target Q d x y := by
  fin_cases k <;> simp only [OfKind] at hk
  · exact Or.inl ⟨0,hk⟩
  · exact Or.inl ⟨1,hk.1⟩
  · exact Or.inl ⟨2,hk.1⟩
  · exact Or.inr ⟨0,hk.1⟩
  · exact Or.inr ⟨1,hk.1⟩
  · exact Or.inr ⟨2,hk⟩
  · exact Or.inl ⟨1,hk.1⟩
  · exact Or.inl ⟨2,hk.1⟩















section ActualRows
variable [Fintype V]











end ActualRows
end Q2CandidateTypes









end

section
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace Q2CandidateTypes
end Q2CandidateTypes
open Q2CandidateTypes
open scoped Classical
open TournamentHighRows
variable {X V : Type}

/-- These eight mutually exclusive types exhaust the actual high candidates. -/
theorem solution (guard : X → Prop) (target : ℕ → X → Prop)
    (Q d : ℕ) (hQ : Q ≤ 2) (x y : X) :
    High guard target Q d x y ↔ ∃ k : Fin 8, OfKind guard target Q d x y k := by
  classical
  constructor
  · rintro (⟨b,hb⟩ | ⟨b,hb⟩)
    · have hbQ : b ≤ Q := hb.1.1
      have hb012 : b = 0 ∨ b = 1 ∨ b = 2 := by omega
      rcases hb012 with rfl | rfl | rfl
      · exact ⟨0,hb⟩
      · by_cases hg : GuardCandidate target Q d 0 x y
        · exact ⟨6,hb,hg⟩
        · exact ⟨1,hb,hg⟩
      · by_cases hg : GuardCandidate target Q d 1 x y
        · exact ⟨7,hb,hg⟩
        · exact ⟨2,hb,hg⟩
    · have hbQ : b ≤ Q := hb.1
      have hb012 : b = 0 ∨ b = 1 ∨ b = 2 := by omega
      rcases hb012 with rfl | rfl | rfl
      · by_cases hp : PositiveCandidate guard target Q d 1 x y
        · exact ⟨6,hp,hb⟩
        · exact ⟨3,hb,hp⟩
      · by_cases hp : PositiveCandidate guard target Q d 2 x y
        · exact ⟨7,hp,hb⟩
        · exact ⟨4,hb,hp⟩
      · exact ⟨5,hb⟩
  · rintro ⟨k,hk⟩
    exact ofKind_high guard target Q d x y k hk
end
