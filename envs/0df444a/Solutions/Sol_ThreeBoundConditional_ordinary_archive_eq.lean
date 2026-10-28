-- Prove2me | solution 1 for ThreeBoundConditional.ordinary_archive_eq
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-25T22:47:43.698694+00:00
-- url     : https://prove2.me/submissions/b5dc73a5-d9cc-429b-a028-14f2da3e99c5

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
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Finset.Union
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.Sort
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
import Definitions.Def_Sensitivity213303_CandidateCoherence
import Definitions.Def_Sensitivity213303_ConditionalOrdinary
import Definitions.Def_Sensitivity213303_Endpoint40Recipes
import Definitions.Def_Sensitivity213303_GradedPositiveBoundary
import Definitions.Def_Sensitivity213303_GuardAugmentation
import Definitions.Def_Sensitivity213303_LabelCard
import Definitions.Def_Sensitivity213303_LabelDefinitions
import Definitions.Def_Sensitivity213303_LabelExists
import Definitions.Def_Sensitivity213303_LabelLoads
import Definitions.Def_Sensitivity213303_LabelMarked
import Definitions.Def_Sensitivity213303_LabelOrdinary
import Definitions.Def_Sensitivity213303_MinMaxNesting
import Definitions.Def_Sensitivity213303_OrdinaryParentBridge
import Definitions.Def_Sensitivity213303_Paley10007
import Definitions.Def_Sensitivity213303_ProfileClosures
import Definitions.Def_Sensitivity213303_Q2CandidateTypes
import Definitions.Def_Sensitivity213303_Q2Enumeration
import Definitions.Def_Sensitivity213303_RecursiveLowerBounds
import Definitions.Def_Sensitivity213303_ResidualCaps
import Definitions.Def_Sensitivity213303_Selected10007
import Definitions.Def_Sensitivity213303_SelectedBoolCaps
import Definitions.Def_Sensitivity213303_SelectedOrdinaryCaps
import Definitions.Def_Sensitivity213303_StrictPositive
import Definitions.Def_Sensitivity213303_StrictUnion
import Definitions.Def_Sensitivity213303_TournamentHighRows
import Definitions.Def_Sensitivity213303_WitnessLifting

namespace OAI.Paper320
end OAI.Paper320
namespace ThreeBoundOrdinaryArchive.CompactAtomicLLL
end ThreeBoundOrdinaryArchive.CompactAtomicLLL
namespace ThreeBoundOrdinaryArchive.OAI.Paper320
end ThreeBoundOrdinaryArchive.OAI.Paper320
namespace ThreeBoundOrdinaryArchive.Sensitivity205
end ThreeBoundOrdinaryArchive.Sensitivity205
namespace ThreeBoundOrdinaryArchive.Sensitivity2075
end ThreeBoundOrdinaryArchive.Sensitivity2075
namespace ThreeBoundOrdinaryArchive.SensitivityLabelCache12607.SensitivityLLL
end ThreeBoundOrdinaryArchive.SensitivityLabelCache12607.SensitivityLLL
namespace ThreeBoundOrdinaryArchive.SensitivityQ
end ThreeBoundOrdinaryArchive.SensitivityQ
namespace ThreeBoundOrdinaryArchive.ZL
end ThreeBoundOrdinaryArchive.ZL
namespace ThreeBoundOrdinaryArchive.ZL.RowCounting
end ThreeBoundOrdinaryArchive.ZL.RowCounting
namespace ThreeBoundOrdinaryArchive.ZP
end ThreeBoundOrdinaryArchive.ZP
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
namespace ThreeBoundPositive
end ThreeBoundPositive
namespace ThreeBoundProfiles
end ThreeBoundProfiles
namespace ThreeBoundWitness
end ThreeBoundWitness
namespace OAI.Paper320
end OAI.Paper320
section
/- Adapted complete accepted Apache-2.0 Prove2me proofs by @yousofy. See ordinary_provenance.json. -/


open OAI.Paper320
namespace ThreeBoundOrdinaryArchive

/- Def_Paley11987Support_000.lean -/
set_option autoImplicit false
set_option Elab.async false
section z0

section

set_option maxHeartbeats 6000000
open scoped Classical BigOperators

namespace ZL

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

































end
end ZL
end
end z0



/- Def_Paley11987Support_001.lean -/
set_option autoImplicit false
set_option Elab.async false
section z1

section

set_option maxHeartbeats 6000000
open scoped Classical BigOperators

namespace ZL.RowCounting
noncomputable section

variable {Ω ι : Type*} [Fintype Ω] [Fintype ι] [DecidableEq Ω]



















end
end ZL.RowCounting
end
end z1



/- Def_Paley11987Support_002.lean -/
set_option autoImplicit false
set_option Elab.async false
section z2

section

namespace SensitivityLabelCache12607

set_option maxHeartbeats 8000000
open scoped BigOperators

namespace SensitivityLLL

variable {ι : Type*} [DecidableEq ι]







noncomputable section
open scoped Classical

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]















end
end SensitivityLLL

end SensitivityLabelCache12607
end
end z2



/- Def_Paley11987Support_003.lean -/
set_option autoImplicit false
set_option Elab.async false
section z3

section

set_option maxHeartbeats 4000000
open scoped Classical BigOperators

namespace CompactAtomicLLL

noncomputable section

open SensitivityLabelCache12607.SensitivityLLL

variable {V E : Type*} [Fintype V] [DecidableEq V]























end

end CompactAtomicLLL
end
end z3



/- Def_Paley11987Support_004.lean -/
set_option autoImplicit false
set_option Elab.async false
section z4

section

set_option maxHeartbeats 4000000
open scoped Classical BigOperators

namespace CompactAtomicLLL

noncomputable section

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]









end

end CompactAtomicLLL
end
end z4



/- Def_Paley11987Support_005.lean -/
set_option autoImplicit false
set_option Elab.async false
section z7

section

set_option maxHeartbeats 8000000
open scoped Classical BigOperators

namespace ZL
noncomputable section

open CompactAtomicLLL

variable {V D : Type*} [Fintype V] [DecidableEq V] [Fintype D] [DecidableEq D]



namespace SupportedFamily

variable (F : SupportedFamily V D)









































end SupportedFamily
end
end ZL
end
end z7



/- Def_Paley11987Support_006.lean -/
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



/- Def_Paley11987Support_007.lean -/
set_option autoImplicit false
set_option Elab.async false
section z9

section

set_option maxHeartbeats 8000000
open scoped Classical BigOperators

namespace ZL
noncomputable section

namespace SupportedFamily
variable {V D : Type*} [Fintype V] [DecidableEq V] [Fintype D] [DecidableEq D]
variable (F : SupportedFamily V D)










end SupportedFamily

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (R : V → V → Prop)

open RowCounting

















end
end ZL
end
end z9



/- Def_Paley11987Support_008.lean -/
set_option autoImplicit false
set_option Elab.async false
section z10

section

set_option maxHeartbeats 6000000
open scoped Classical BigOperators

namespace ZL
noncomputable section

variable {V : Type*} [DecidableEq V]













end
end ZL
end
end z10



/- Def_Paley11987Support_009.lean -/
set_option autoImplicit false
set_option Elab.async false
section z11

section

set_option maxHeartbeats 8000000
open scoped Classical BigOperators

namespace ZL
noncomputable section
open RowCounting

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (R : V → V → Prop)

















end
end ZL
end
end z11



/- Def_Paley11987Support_010.lean -/
set_option autoImplicit false
set_option Elab.async false
section z13

section

set_option maxHeartbeats 8000000
open scoped Classical BigOperators

namespace ZL
noncomputable section
open RowCounting
variable {V D : Type*} [Fintype V] [DecidableEq V] [Fintype D] [DecidableEq D]















end
end ZL
end
end z13



/- Def_Paley11987Support_011.lean -/
set_option autoImplicit false
set_option Elab.async false
section z15

section

set_option maxHeartbeats 8000000
open scoped Classical BigOperators

namespace ZL
noncomputable section
open RowCounting
variable {V D : Type*} [Fintype V] [DecidableEq V] [Fintype D] [DecidableEq D]

















end
end ZL
end
end z15



/- Def_Paley11987Support_012.lean -/
set_option autoImplicit false
set_option Elab.async false
section z16

section
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 12000000
set_option maxRecDepth 200000
set_option exponentiation.threshold 32768
open scoped Classical BigOperators

namespace CompactLabeling11987
open ZL ZL.RowCounting




















































































































































end CompactLabeling11987
end
end z16



/- Def_Paley11987Support_013.lean -/
set_option autoImplicit false
set_option Elab.async false
section z17

section

set_option maxHeartbeats 6000000
open scoped Classical BigOperators

namespace ZL
noncomputable section
variable {V : Type*} [Fintype V] [DecidableEq V]














































end
end ZL
end
end z17



/- Def_Paley11987Support_014.lean -/
set_option autoImplicit false
set_option Elab.async false
section z20

section

set_option maxHeartbeats 8000000
open scoped Classical BigOperators

namespace ZL
noncomputable section
variable {V : Type*} [Fintype V] [DecidableEq V]







end
end ZL
end
end z20



/- Def_Paley11987Support_015.lean -/
set_option autoImplicit false
set_option Elab.async false
section z23

set_option maxHeartbeats 200000
open scoped Classical BigOperators
noncomputable section

namespace ZL
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]







end ZL
end
end z23



/- Def_Paley11987Support_016.lean -/
set_option autoImplicit false
set_option Elab.async false
section z24

set_option maxHeartbeats 3000000
open scoped Classical BigOperators
noncomputable section

namespace ZL
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]















end ZL
end
end z24



/- Def_Paley11987Support_017.lean -/
set_option autoImplicit false
set_option Elab.async false
section z27

section

set_option maxHeartbeats 6000000
open scoped Classical BigOperators

namespace ZL.SupportedFamily
noncomputable section
variable {V T : Type*} [Fintype V] [DecidableEq V] [Fintype T]
variable {D : T → Type*} [∀ t, Fintype (D t)]







end
end ZL.SupportedFamily
end
end z27



/- Def_Paley11987Support_018.lean -/
set_option autoImplicit false
set_option Elab.async false
section z28

set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
open scoped Classical BigOperators
noncomputable section

namespace CompactLabeling11987
open ZL ZL.RowCounting

variable {V : Type*} [Fintype V] [DecidableEq V]



































end CompactLabeling11987
end
end z28



/- Def_Paley11987Support_019.lean -/
set_option autoImplicit false
set_option Elab.async false
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



















theorem tolerantRow_true {n k r : ℕ} {I : Type} (T : Tournament k)
    (label : Fin k → Fin k → Fin r) (F : Fin n → (I → Bool) → Bool)
    (A G : Fin n) (q : ℕ) (x : ((Fin k × Fin r) × I) → Bool) (i : Fin k) :
    tolerantRow T label F A G q x i = true ↔
      (∀ c, F A (recursiveChild x i c) = true) ∧
      (failedGuards T label F G x i).card ≤ q := by
  simp only [tolerantRow, decide_eq_true_eq]

theorem tolerantFamily_true {n k r : ℕ} {I : Type} (T : Tournament k)
    (label : Fin k → Fin k → Fin r) (F : Fin n → (I → Bool) → Bool)
    (A G : Fin n) (q : ℕ) (x : ((Fin k × Fin r) × I) → Bool) :
    tolerantFamily T label F A G q x = true ↔
      ∃ i, tolerantRow T label F A G q x i = true := by
  simp only [tolerantFamily, decide_eq_true_eq]



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



/- Def_Paley11987Support_020.lean -/
set_option autoImplicit false
set_option Elab.async false
section z30

set_option maxHeartbeats 3000000
noncomputable section
open scoped Classical BigOperators
open OAI.Paper320 Sensitivity205 Sensitivity2075

namespace ZT

variable {I : Type} [Fintype I]



























end ZT
end
end z30



/- Def_Paley11987Support_021.lean -/
set_option autoImplicit false
set_option Elab.async false
section z31

set_option maxHeartbeats 3000000
noncomputable section
open scoped Classical BigOperators
open OAI.Paper320 Sensitivity2075
namespace ZT

variable {n k r : ℕ} {I : Type} [Fintype I]























end ZT
end
end z31



/- Def_Paley11987Support_022.lean -/
set_option autoImplicit false
set_option Elab.async false
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
variable {n k r : ℕ} {I : Type}





















end SensitivitySourceZero
end
end z32



/- Def_Paley11987Support_023.lean -/
set_option autoImplicit false
set_option Elab.async false
section z33

set_option maxHeartbeats 5000000
noncomputable section
open scoped Classical BigOperators
open OAI.Paper320 Sensitivity2075 SensitivityQ
namespace ZT
variable {n k : ℕ} {I : Type} [Fintype I]















end ZT
end
end z33



/- Def_Paley11987Support_024.lean -/
set_option autoImplicit false
set_option Elab.async false
section z34

set_option maxHeartbeats 8000000
noncomputable section
open scoped Classical BigOperators
open OAI.Paper320 Sensitivity2075 SensitivityQ
namespace ZT
variable {n k : ℕ} {I : Type} [Fintype I]





















end ZT
end
end z34



/- Def_Paley11987Support_025.lean -/
set_option autoImplicit false
set_option Elab.async false
section z37

set_option maxHeartbeats 8000000
noncomputable section
open scoped Classical BigOperators
open OAI.Paper320 Sensitivity2075 SensitivityQ
namespace ZT
variable {n k : ℕ} {I : Type} [Fintype I]















end ZT
end
end z37



/- Def_Paley11987Support_026.lean -/
set_option autoImplicit false
set_option Elab.async false
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



/- Def_Paley11987Support_027.lean -/
set_option autoImplicit false
set_option Elab.async false
section z41

set_option maxHeartbeats 8000000
noncomputable section
open scoped Classical BigOperators
open OAI.Paper320 Sensitivity2075 SensitivityQ
namespace ZT
variable {n k : ℕ} {I : Type} [Fintype I]

















end ZT
end
end z41



/- Def_Paley11987Support_028.lean -/
set_option autoImplicit false
set_option Elab.async false
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



/- Def_Paley11987Support_029.lean -/
set_option autoImplicit false
set_option Elab.async false
section z44

namespace ZP


























































end ZP
end z44



/- Def_Paley11987Support_030.lean -/
set_option autoImplicit false
set_option Elab.async false
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



/- Def_Paley11987Support_038.lean -/
set_option autoImplicit false
set_option Elab.async false
section z59

set_option maxHeartbeats 5000000
namespace ZT









end ZT
end z59



/- Def_Paley11987Support_039.lean -/
set_option autoImplicit false
set_option Elab.async false
section z60

set_option maxHeartbeats 8000000
noncomputable section
open scoped Classical BigOperators
open OAI.Paper320 Sensitivity2075 SensitivityQ
namespace ZT
variable {n k : ℕ} {I : Type} [Fintype I]











end ZT
end
end z60



/- Def_Paley11987Support_040.lean -/
set_option autoImplicit false
set_option Elab.async false
section z61

set_option maxHeartbeats 8000000
noncomputable section
open scoped Classical BigOperators
open OAI.Paper320 Sensitivity2075 SensitivityQ
open ZP
namespace ZT
variable {n k : ℕ} {I : Type} [Fintype I]













end ZT
end
end z61



/- Def_Paley11987Support_041.lean -/
set_option autoImplicit false
set_option Elab.async false
section z62

set_option maxHeartbeats 5000000
namespace ZT









end ZT
end z62



end ThreeBoundOrdinaryArchive

end

section
/-
Common block and positive-sensitivity witnesses for a broad two-child
guarded construction. These are lower-bound witnesses; no upper sensitivity
transfer theorem is asserted here.
-/


set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace ThreeBoundWitness
open OAI.Paper320

variable {L I V : Type}









theorem parent_true_iff [Fintype V] (S : Stage L I V)
    (F : L → (I → Bool) → Bool) (l : L)
    (x : ((V × Bool) × I) → Bool) :
    parent S F l x = true ↔ ∃ v : V,
      (failed S F l x v).card ≤ S.tolerance l ∧
      S.target l (failed S F l x v).card (child x v false) (child x v true) = true := by
  classical
  simp [parent]















































/- Reindexing lemmas follow the accepted Apache-2.0 source by @yousofy:
   Sol_Paley11987Verified_CompactFiniteProfile11987_actual_seeds_of_label_and_certificate,
   together with Definitions.Def_Paley11987Support_053. -/










end ThreeBoundWitness








end

section
/-
Ordinary-component conditional transfers for the actual guarded Boolean family.
This development uses the shared campaign bit-flip definitions throughout.
-/


set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedSectionVars false

namespace ThreeBoundConditional
open OAI.Paper320 ThreeBoundWitness ThreeBoundProfiles ThreeBoundPositive
open scoped BigOperators Classical
noncomputable section

variable {L I V : Type} [LinearOrder L] [Fintype I] [Fintype V]









@[simp] theorem ordinary_failed (S : Stage L I V) (F : L → (I → Bool) → Bool)
    (t g l : L) (q : ℕ) (x : ((V × Bool) × I) → Bool) (v : V) :
    failed (ordinaryStage S F t g q) F l x v = guardFailures S F g x v := rfl

@[simp] theorem ordinary_parent_true (S : Stage L I V) (F : L → (I → Bool) → Bool)
    (t g : L) (q : ℕ) (x : ((V × Bool) × I) → Bool) :
    ordinaryParent S F t g q x = true ↔ ∃ v, ordinaryRow S F t g q x v := by
  simp only [ordinaryParent, parent_true_iff, ordinary_failed, ordinaryStage,
    Bool.and_eq_true, ordinaryRow]
  constructor
  · rintro ⟨v,hc,hf,ht⟩
    exact ⟨v, fun c => by cases c <;> assumption, hc⟩
  · rintro ⟨v,ht,hc⟩
    exact ⟨v,hc,ht false,ht true⟩































































end
end ThreeBoundConditional




end

section
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 10000
set_option linter.unusedSectionVars false
namespace ThreeBoundConditional
end ThreeBoundConditional
open ThreeBoundConditional
open OAI.Paper320 ThreeBoundWitness ThreeBoundProfiles ThreeBoundPositive
open scoped Classical
variable {I J : Type} [Fintype I] [Fintype J]
variable {n k : ℕ}

theorem solution (S : Stage (Fin n) I (Fin k))
    (T : ThreeBoundOrdinaryArchive.OAI.Paper320.Tournament k)
    (ell : Fin k → Fin k → Fin 2)
    (hAdj : ∀ v w, T.Adj v w ↔ S.Adj v w)
    (hLabel : ∀ v w, finTwoEquiv (ell v w)=S.label v w)
    (F : Fin n → (I → Bool) → Bool) (t g : Fin n) (q : ℕ) :
    reindex (ordinaryCoordEquiv (I:=I))
      (ThreeBoundOrdinaryArchive.Sensitivity2075.tolerantFamily T ell F t g q) =
      ordinaryParent S F t g q := by
  funext x
  let xx : ((Fin k × Fin 2) × I) → Bool := fun a => x (ordinaryCoordEquiv a)
  have hchild (v : Fin k) (c : Fin 2) :
      ThreeBoundOrdinaryArchive.OAI.Paper320.recursiveChild xx v c = child x v (finTwoEquiv c) := rfl
  have hfailed (v : Fin k) :
      ThreeBoundOrdinaryArchive.Sensitivity2075.failedGuards T ell F g xx v = guardFailures S F g x v := by
    ext w
    simp only [ThreeBoundOrdinaryArchive.Sensitivity2075.failedGuards,guardFailures,
      Finset.mem_filter,Finset.mem_univ,true_and,hchild,hAdj,hLabel]
  have hiff : ThreeBoundOrdinaryArchive.Sensitivity2075.tolerantFamily T ell F t g q xx=true ↔
      ordinaryParent S F t g q x=true := by
    rw [ThreeBoundOrdinaryArchive.Sensitivity2075.tolerantFamily_true,ordinary_parent_true]
    apply exists_congr
    intro v
    rw [ThreeBoundOrdinaryArchive.Sensitivity2075.tolerantRow_true,hfailed]
    apply and_congr
    · constructor
      · intro h c
        have hh := h (finTwoEquiv.symm c)
        simpa only [hchild,Equiv.apply_symm_apply] using hh
      · intro h c
        simpa only [hchild] using h (finTwoEquiv c)
    · rfl
  change ThreeBoundOrdinaryArchive.Sensitivity2075.tolerantFamily T ell F t g q xx =
    ordinaryParent S F t g q x
  cases h₁ : ThreeBoundOrdinaryArchive.Sensitivity2075.tolerantFamily T ell F t g q xx <;>
    cases h₂ : ordinaryParent S F t g q x <;> simp_all
end
