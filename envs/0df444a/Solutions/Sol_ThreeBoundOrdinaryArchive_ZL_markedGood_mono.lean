-- Prove2me | solution 1 for ThreeBoundOrdinaryArchive.ZL.markedGood_mono
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-25T22:38:18.481982+00:00
-- url     : https://prove2.me/submissions/2d8614c1-6300-46ad-b0da-d441e74a1d67

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





















theorem mismatch_mono (R : V → V → Prop) (ell : V × V → Fin 2)
    (A B : Finset V) (h : A ⊆ B) (color : V → Fin 2) (x : V) :
    mismatch R ell A color x ⊆ mismatch R ell B color x := by
  intro y hy
  exact Finset.mem_filter.mpr ⟨h (Finset.mem_filter.mp hy).1,
    (Finset.mem_filter.mp hy).2⟩





























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
set_option maxHeartbeats 6000000
open scoped Classical BigOperators
namespace ThreeBoundOrdinaryArchive.ZL
end ThreeBoundOrdinaryArchive.ZL
open ThreeBoundOrdinaryArchive.ZL
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem solution (R : V → V → Prop) (ell : V × V → Fin 2)
    (A A' M P P' : Finset V) (hA : A' ⊆ A) (hP : P' ⊆ P)
    (q B B' : ℕ) (hB : B ≤ B') (color : V → Fin 2)
    (hg : MarkedGood R ell A M P q B color) :
    MarkedGood R ell A' M P' q B' color := by
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    exact (Nat.add_le_add_right
      (Finset.card_le_card (mismatch_mono R ell A' A hA color x)) _).trans
      (hg.1 x (hA hx))
  · intro y hy
    have hm := Finset.card_le_card (mismatch_mono R ell A' A hA color y)
    have ho := hg.2.1 y hy
    by_cases hyP : y ∈ P'
    · simpa only [if_pos hyP, if_pos (hP hyP), Nat.add_zero] using
        (Nat.add_le_add_left hm (outOn R M y).card).trans ho
    · simp only [if_neg hyP]
      by_cases hyold : y ∈ P
      · simp only [if_pos hyold] at ho
        omega
      · simp only [if_neg hyold] at ho
        omega
  · calc
      ∑ y ∈ M, (mismatch R ell A' color y).card ≤
          ∑ y ∈ M, (mismatch R ell A color y).card :=
        Finset.sum_le_sum fun y _ => Finset.card_le_card
          (mismatch_mono R ell A' A hA color y)
      _ ≤ B' := hg.2.2.trans hB
end
