-- Prove2me | solution 1 for ResidualCaps.cleaned_marked_zero
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-25T22:42:10.621095+00:00
-- url     : https://prove2.me/submissions/d2845503-3556-46a8-8935-b163d4ed6be4

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
import Definitions.Def_Sensitivity213303_ResidualCaps
import Definitions.Def_Sensitivity213303_TournamentHighRows

namespace MinmaxLocal
end MinmaxLocal
namespace TournamentHighRows
end TournamentHighRows
namespace CandidateCoherence
end CandidateCoherence
namespace MinmaxLocal
end MinmaxLocal
namespace TournamentHighRows
end TournamentHighRows
namespace CandidateCoherence
end CandidateCoherence
namespace GuardAugmentation
end GuardAugmentation
namespace TournamentHighRows
end TournamentHighRows

section
/-
Semantic high-row bounds for the graded q2/q3 transfer.

The finite high set is connected to actual guard failure sets: every arc to
a high head selects a guard-true child and therefore consumes a failure of
its tail. The tournament edge double count is proved here, not assumed.
-/


set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace TournamentHighRows
open scoped Classical BigOperators

variable {V X : Type}

























section GuardSemantics
variable [Fintype V]



/-- Every edge into a high head consumes an actual failed guard. -/
theorem out_high_subset_failures (R : V → V → Prop) (ell : V → V → Bool)
    (P : X → Prop) (children : V → Bool → X) (H : Finset V)
    (hhigh : ∀ w ∈ H, ∀ c : Bool, P (children w c)) (v : V) :
    outNeighbors R H v ⊆ guardFailures R ell P children v := by
  classical
  intro w hw
  rcases Finset.mem_filter.mp hw with ⟨hwH,hvw⟩
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ w, hvw, hhigh w hwH (ell v w)⟩











end GuardSemantics
end TournamentHighRows








end

section
/-
The graded-target to labeling-exclusion bridge.

Targets at different rows may use different lower thresholds. A geometric
one-child candidate has an accepted partner; coloring its row by the other
position makes every label mismatch an actual guard failure. This argument
is independent of fixed versus graded targets and applies to min/max targets.
-/


set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace CandidateCoherence
open scoped Classical
open MinmaxLocal TournamentHighRows

variable {N : ℕ} {V X : Type}























section ActualGuards
variable [Fintype V]

/-- Each label mismatch enters the actual selected-child failure set. -/
theorem mismatch_subset_failures (R : V → V → Prop) (ell : V → V → Bool)
    (P : X → Prop) (children : V → Bool → X)
    (T : Finset V) (color : V → Bool)
    (hpartner : ∀ w ∈ T, ∀ b : Bool, b ≠ color w → P (children w b)) (v : V) :
    mismatch R ell T color v ⊆ guardFailures R ell P children v := by
  classical
  intro w hw
  rcases Finset.mem_filter.mp hw with ⟨hwT,hvw,hlabel⟩
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ w,hvw,hpartner w hwT (ell v w) hlabel⟩









end ActualGuards
end CandidateCoherence







end

section
/-
Actual guard augmentation for graded-target candidates.

The optional matching and near-coloring argument is adapted from the accepted
CompactTournament.augment_by_guards proof in the attached Paley11987 source
(prove2.me submission 7f5aa99d-5bc6-4815-915f-ef258368885d). This module specializes
its abstract combinatorics to the actual Boolean selected-child guard sets in
TournamentHighRows and the graded target colors in CandidateCoherence.
-/


set_option autoImplicit false
set_option maxHeartbeats 3000000

namespace GuardAugmentation
open scoped Classical
open Finset MinmaxLocal TournamentHighRows CandidateCoherence
noncomputable section

variable {V X : Type} [Fintype V] [DecidableEq V]











/-- Every abstract augmentation charge is an actual guard failure. The
    disjointness of candidates and high rows prevents double-counting. -/
theorem charges_card_le_actual_failures (R : V → V → Prop)
    (ell : V → V → Bool) (P : X → Prop) (children : V → Bool → X)
    (C G : Finset V) (hdis : Disjoint C G) (base : V → Bool)
    (hpartner : ∀ w ∈ C, ∀ b : Bool, b ≠ base w → P (children w b))
    (hhigh : ∀ w ∈ G, ∀ b : Bool, P (children w b)) (v : V) :
    (mismatch R ell C base v).card + (outNeighbors R G v).card ≤
      (guardFailures R ell P children v).card := by
  have hd : Disjoint (mismatch R ell C base v) (outNeighbors R G v) := by
    apply Finset.disjoint_left.mpr
    intro w hwC hwG
    exact Finset.disjoint_left.mp hdis
      (Finset.mem_filter.mp hwC).1 (Finset.mem_filter.mp hwG).1
  rw [← Finset.card_union_of_disjoint hd]
  apply Finset.card_le_card
  apply Finset.union_subset
  · exact mismatch_subset_failures R ell P children C base hpartner v
  · exact out_high_subset_failures R ell P children G hhigh v



end
end GuardAugmentation







end

section
/-
Source, double-dominator, and zero-mismatch residual caps for actual graded
target candidates. The residuals are actual failed guards left after all arcs
inside the full high-row tournament have been charged.
-/


set_option autoImplicit false
set_option maxHeartbeats 3000000

namespace ResidualCaps
open scoped Classical BigOperators
open Finset TournamentHighRows CandidateCoherence GuardAugmentation
noncomputable section

variable {V X : Type} [Fintype V] [DecidableEq V]

















theorem cleanedHeads_subset (R : V → V → Prop) (ell : V → V → Bool)
    (A M : Finset V) (color : V → Bool) : cleanedHeads R ell A M color ⊆ A :=
  Finset.sdiff_subset



theorem marker_clean_mismatch_empty (R : V → V → Prop) (ell : V → V → Bool)
    (A M : Finset V) (color : V → Bool) (v : V) (hv : v ∈ M) :
    mismatch R ell (cleanedHeads R ell A M color) color v = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro w hw
  obtain ⟨hwC,hvw,hcolor⟩ := Finset.mem_filter.mp hw
  obtain ⟨hwA,hwD⟩ := Finset.mem_sdiff.mp hwC
  exact hwD (Finset.mem_biUnion.mpr
    ⟨v,hv,Finset.mem_filter.mpr ⟨hwA,hvw,hcolor⟩⟩)







theorem outNeighbors_card_le_pred (R : V → V → Prop) (hR : IsTournament R)
    (M : Finset V) (v : V) (hv : v ∈ M) : (outNeighbors R M v).card ≤ M.card-1 := by
  have hsub : outNeighbors R M v ⊆ M.erase v := by
    intro w hw
    obtain ⟨hwM,hvw⟩ := Finset.mem_filter.mp hw
    apply Finset.mem_erase.mpr
    refine ⟨?_,hwM⟩
    intro he
    subst w
    exact hR.loopless v hvw
  have h := Finset.card_le_card hsub
  rwa [Finset.card_erase_of_mem hv] at h





end
end ResidualCaps







end

section
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace ResidualCaps
end ResidualCaps
open ResidualCaps
open scoped Classical BigOperators
open Finset TournamentHighRows CandidateCoherence GuardAugmentation
variable {V X : Type} [Fintype V] [DecidableEq V]

/-- Zeroing all selected-marker mismatches gives a marked configuration even
    when the original markers have larger global guard budgets. Only the
    number of selected markers matters for their internal outdegrees. -/
theorem solution (R : V → V → Prop) (hR : IsTournament R)
    (ell : V → V → Bool) (guard : X → Prop) (children : V → Bool → X)
    (A H M : Finset V) (hdis : Disjoint A H) (hMH : M ⊆ H)
    (color : V → Bool) (q : ℕ) (hsize : M.card ≤ q+2)
    (hpartner : ∀ w ∈ A, ∀ c : Bool, c ≠ color w → guard (children w c))
    (hhigh : ∀ w ∈ H, ∀ c : Bool, guard (children w c))
    (hbudget : ∀ v ∈ A, (guardFailures R ell guard children v).card ≤ q) :
    MarkedGood R ell (cleanedHeads R ell A M color) M q 0 color := by
  let C := cleanedHeads R ell A M color
  have hCA : C ⊆ A := cleanedHeads_subset R ell A M color
  have hzero : ∀ v ∈ M, (mismatch R ell C color v).card = 0 := by
    intro v hv
    rw [marker_clean_mismatch_empty R ell A M color v hv]
    rfl
  refine ⟨?_,?_,?_⟩
  · intro v hv
    exact (charges_card_le_actual_failures R ell guard children C M (hdis.mono hCA hMH)
      color (fun w hw => hpartner w (hCA hw)) (fun w hw => hhigh w (hMH hw)) v).trans
      (hbudget v (hCA hv))
  · intro v hv
    rw [hzero v hv, Nat.add_zero]
    have h := outNeighbors_card_le_pred R hR M v hv
    omega
  · have hz : (∑ v ∈ M, (mismatch R ell C color v).card) = 0 :=
      Finset.sum_eq_zero (fun v hv => hzero v hv)
    exact hz.le
end
