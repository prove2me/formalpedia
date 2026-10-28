-- Prove2me | solution 1 for ThreeBoundOrdinaryArchive.SensitivityOrdinaryGuard.tournament_outside_budget
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-25T22:45:19.89599+00:00
-- url     : https://prove2.me/submissions/21806878-6b5c-4292-b248-be05c79c022f

import Definitions.Def_SensitivityCampaign
import Definitions.Def_SensitivitySeparation
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.GroupWithZero.Units.Equiv
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Combinatorics.Digraph.Basic
import Mathlib.Combinatorics.Hall.Finite
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Union
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.NumberTheory.JacobiSum.Basic
import Mathlib.NumberTheory.LegendreSymbol.Basic
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Definitions.Def_Sensitivity213303_ArchivedOrdinaryDefinitions
import Theorems.Thm_ThreeBoundOrdinaryArchive_OAI_Paper320_Tournament_card_internalEdges

namespace OAI.Paper320
end OAI.Paper320
namespace ThreeBoundOrdinaryArchive.OAI.Paper320
end ThreeBoundOrdinaryArchive.OAI.Paper320
namespace ThreeBoundOrdinaryArchive.Sensitivity205
end ThreeBoundOrdinaryArchive.Sensitivity205
namespace ThreeBoundOrdinaryArchive.Sensitivity2075
end ThreeBoundOrdinaryArchive.Sensitivity2075
namespace ThreeBoundOrdinaryArchive.SensitivityQ
end ThreeBoundOrdinaryArchive.SensitivityQ
namespace ThreeBoundOrdinaryArchive.ZL
end ThreeBoundOrdinaryArchive.ZL
namespace ThreeBoundOrdinaryArchive.ZP
end ThreeBoundOrdinaryArchive.ZP
namespace OAI.Paper320
end OAI.Paper320
namespace ThreeBoundOrdinaryArchive.OAI.Paper320
end ThreeBoundOrdinaryArchive.OAI.Paper320
namespace ThreeBoundOrdinaryArchive.Sensitivity205
end ThreeBoundOrdinaryArchive.Sensitivity205
namespace ThreeBoundOrdinaryArchive.Sensitivity2075
end ThreeBoundOrdinaryArchive.Sensitivity2075
namespace ThreeBoundOrdinaryArchive.SensitivityOrdinaryGuard
end ThreeBoundOrdinaryArchive.SensitivityOrdinaryGuard
namespace ThreeBoundOrdinaryArchive.SensitivityQ
end ThreeBoundOrdinaryArchive.SensitivityQ
namespace ThreeBoundOrdinaryArchive.ZL
end ThreeBoundOrdinaryArchive.ZL
namespace ThreeBoundOrdinaryArchive.ZP
end ThreeBoundOrdinaryArchive.ZP
section
/- Adapted complete accepted Apache-2.0 Prove2me proofs by @yousofy. See ordinary_provenance.json. -/


open OAI.Paper320
namespace ThreeBoundOrdinaryArchive

/- Sol_Paley11987Verified_CompactBooleanTransfer_candidateTotalCap_bound.lean -/
set_option autoImplicit false
set_option Elab.async false
section z8

section

set_option maxHeartbeats 6000000
open scoped Classical BigOperators

namespace ZL
noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]



















































end
end ZL
end
end z8

section z29

set_option maxHeartbeats 3000000
set_option maxRecDepth 20000
noncomputable section
open scoped Classical BigOperators
namespace OAI.Paper320













namespace Tournament
variable {k : ℕ} (T : Tournament k)









end Tournament



















end OAI.Paper320
namespace Sensitivity205
open OAI.Paper320







end Sensitivity205
namespace Sensitivity2075
open OAI.Paper320 Sensitivity205













section Flips
variable {n k r : ℕ} {I : Type} (T : Tournament k)
  (label : Fin k → Fin k → Fin r) (F : Fin n → (I → Bool) → Bool)
  (G : Fin n) (x : ((Fin k × Fin r) × I) → Bool)
  (i j : Fin k) (c : Fin r) (a : I)

















end Flips

section RowFlips
variable {n k r : ℕ} {I : Type} (T : Tournament k)
  (label : Fin k → Fin k → Fin r) (F : Fin n → (I → Bool) → Bool)
  (A G : Fin n) (q : ℕ) (x : ((Fin k × Fin r) × I) → Bool)
  (i j : Fin k) (c : Fin r) (a : I)





end RowFlips

section Nesting
variable {n k r : ℕ} {I : Type} (T : Tournament k)
  (label : Fin k → Fin k → Fin r) (F : Fin n → (I → Bool) → Bool)
  (hF : NestedFamily F)





end Nesting











section JointCandidates








end JointCandidates





end Sensitivity2075
end
end z29

section z32
set_option maxHeartbeats 3000000
noncomputable section
open OAI.Paper320 Sensitivity205 Sensitivity2075
open scoped Classical BigOperators
namespace OAI.Paper320.Tournament
variable {k : ℕ} (T : Tournament k)





theorem sum_outdegree_eq (I : Finset (Fin k)) :
    ∑ i ∈ I, (I.filter (T.Adj i)).card = (T.internalEdges I).card := by
  simp only [internalEdges, Finset.card_eq_sum_ones, Finset.sum_filter, Finset.sum_product]

end OAI.Paper320.Tournament
namespace SensitivityQ



















end SensitivityQ
namespace SensitivitySourceZero






















end SensitivitySourceZero
end
end z32

section z38

set_option maxHeartbeats 3000000
open scoped Classical BigOperators
noncomputable section

namespace CompactTournament
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]













end CompactTournament
end
end z38

section z39

set_option maxHeartbeats 3000000
open scoped Classical BigOperators
noncomputable section

namespace CompactTournament
open Finset ZL
variable {V : Type*} [Fintype V] [DecidableEq V]



end CompactTournament
end
end z39

section z40

set_option maxHeartbeats 3000000
noncomputable section
open OAI.Paper320 Sensitivity205 Sensitivity2075
open scoped Classical BigOperators

namespace ZT
variable {n k : ℕ} {I : Type}

















end ZT
end
end z40

section z43

set_option maxHeartbeats 8000000
noncomputable section
open scoped Classical BigOperators
open OAI.Paper320 Sensitivity2075 SensitivityQ ZL
namespace ZT
variable {n k : ℕ} {I : Type} [Fintype I]



















end ZT
end
end z43

section z45

set_option maxHeartbeats 8000000
noncomputable section
open scoped Classical BigOperators
open OAI.Paper320 Sensitivity2075 SensitivityQ
open ZP
namespace ZT
variable {n k : ℕ} {I : Type} [Fintype I]









end ZT
end
end z45

end ThreeBoundOrdinaryArchive

end

section
open OAI.Paper320
namespace ThreeBoundOrdinaryArchive
end ThreeBoundOrdinaryArchive
open ThreeBoundOrdinaryArchive
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 5000000
open scoped Classical BigOperators
open OAI.Paper320 Sensitivity2075 SensitivityQ
namespace ThreeBoundOrdinaryArchive.SensitivityOrdinaryGuard
end ThreeBoundOrdinaryArchive.SensitivityOrdinaryGuard
open ThreeBoundOrdinaryArchive.SensitivityOrdinaryGuard

theorem solution {k : ℕ} (T : Tournament k)
    (P R : Finset (Fin k)) (B O : Fin k → Finset (Fin k)) (q : ℕ)
    (hdis : Disjoint P R)
    (hinside : ∀ i, (P ∪ R).filter (T.Adj i) ⊆ B i)
    (hP : ∀ i ∈ P, (B i).card ≤ q)
    (hR : ∀ i ∈ R, (B i).card = q+1)
    (hOB : ∀ i, O i ⊆ B i)
    (hOR : ∀ i, ∀ j ∈ O i, j ∉ R) :
    (∑ i ∈ R, ((O i).filter fun j => j ∉ P).card)+
      (P.card+R.card).choose 2 ≤ q*P.card+(q+1)*R.card := by
  let S := P ∪ R
  let W := ∑ i ∈ R, ((O i).filter fun j => j ∉ P).card
  have hlocalP : ∀ i ∈ P, (S.filter (T.Adj i)).card ≤ q := by
    intro i hi
    exact (Finset.card_le_card (hinside i)).trans (hP i hi)
  have hlocalR : ∀ i ∈ R,
      ((O i).filter fun j => j ∉ P).card+
        (S.filter (T.Adj i)).card ≤ q+1 := by
    intro i hi
    have hd : Disjoint ((O i).filter fun j => j ∉ P) (S.filter (T.Adj i)) := by
      apply Finset.disjoint_left.mpr
      intro j hjO hjS
      obtain ⟨hjO, hjnotP⟩ := Finset.mem_filter.mp hjO
      obtain ⟨hjS, _⟩ := Finset.mem_filter.mp hjS
      rcases Finset.mem_union.mp hjS with hjP | hjR
      · exact hjnotP hjP
      · exact hOR i j hjO hjR
    calc
      _ = (((O i).filter fun j => j ∉ P) ∪ S.filter (T.Adj i)).card :=
        (Finset.card_union_of_disjoint hd).symm
      _ ≤ (B i).card := Finset.card_le_card (Finset.union_subset
        ((Finset.filter_subset _ _).trans (hOB i)) (hinside i))
      _ = q+1 := hR i hi
  have hs : (P.card+R.card).choose 2 =
      (∑ i ∈ P, (S.filter (T.Adj i)).card)+
        ∑ i ∈ R, (S.filter (T.Adj i)).card := by
    calc
      _ = S.card.choose 2 := by
        rw [show S.card = P.card+R.card from Finset.card_union_of_disjoint hdis]
      _ = ∑ i ∈ S, (S.filter (T.Adj i)).card := by
        rw [T.sum_outdegree_eq, T.card_internalEdges]
      _ = _ := Finset.sum_union hdis
  have hp : (∑ i ∈ P, (S.filter (T.Adj i)).card) ≤ P.card*q := by
    simpa using Finset.sum_le_sum hlocalP
  have hr : W+(∑ i ∈ R, (S.filter (T.Adj i)).card) ≤ R.card*(q+1) := by
    calc
      _ = ∑ i ∈ R, (((O i).filter fun j => j ∉ P).card+
          (S.filter (T.Adj i)).card) := by rw [Finset.sum_add_distrib]
      _ ≤ ∑ _i ∈ R, (q+1) := Finset.sum_le_sum hlocalR
      _ = _ := by simp
  change W+(P.card+R.card).choose 2 ≤ _
  rw [hs]
  have hh := Nat.add_le_add hp hr
  simpa only [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm,
    Nat.mul_comm] using hh
end
