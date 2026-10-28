-- Prove2me | solution 1 for Sensitivity213981Formal.ThreeBoundOrdinary5591.ordinary_positive_of_cases
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T01:36:41.498461+00:00
-- url     : https://prove2.me/submissions/40fb325d-ee93-4ccb-8c06-3f0dabf24a0c

import Definitions.Def_Sensitivity213981Formal_Namespaces
import Definitions.Def_Sensitivity213981Formal_NamespacesComplete
import Definitions.Def_Sensitivity213981Formal_Ordinary5591Caps
import Definitions.Def_Sensitivity213981Formal_Supplement_ArchivedOrdinaryDefinitions
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
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
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
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.List.FinRange
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
import Theorems.Thm_Sensitivity213981Formal_ThreeBoundOrdinary5591_candidateTotalCap_bound
import Theorems.Thm_Sensitivity213981Formal_ThreeBoundOrdinaryArchive_Sensitivity2075_tolerant_target_weak_false
import Theorems.Thm_Sensitivity213981Formal_ThreeBoundOrdinaryArchive_SensitivityQ_guards_card
import Theorems.Thm_Sensitivity213981Formal_ThreeBoundOrdinaryArchive_SensitivityQ_positiveTargets_card
import Theorems.Thm_Sensitivity213981Formal_ThreeBoundOrdinaryArchive_SensitivityQ_positiveTargets_guards_coupling
import Theorems.Thm_Sensitivity213981Formal_ThreeBoundOrdinaryArchive_ZT_candidates_markedGood
import Theorems.Thm_Sensitivity213981Formal_ThreeBoundOrdinaryArchive_ZT_crossedTargetHeads_budget
import Theorems.Thm_Sensitivity213981Formal_ThreeBoundOrdinaryArchive_ZT_ordinary_zero_candidate_cost


namespace Sensitivity213981Formal
section
/- Adapted complete accepted Apache-2.0 Prove2me proofs by @yousofy. See ordinary_provenance.json. -/


open _root_.OAI.Paper320 _root_.Sensitivity213981Formal.OAI.Paper320
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
attribute [local irreducible] N degree common lam
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
open _root_.Sensitivity213981Formal.ThreeBoundOrdinaryArchive.OAI.Paper320







end Sensitivity205
namespace Sensitivity2075
open _root_.Sensitivity213981Formal.ThreeBoundOrdinaryArchive.OAI.Paper320 Sensitivity205



















theorem tolerantRow_true {n k r : ℕ} {I : Type} (T : Tournament k)
    (label : Fin k → Fin k → Fin r) (F : Fin n → (I → Bool) → Bool)
    (A G : Fin n) (q : ℕ) (x : ((Fin k × Fin r) × I) → Bool) (i : Fin k) :
    tolerantRow T label F A G q x i = true ↔
      (∀ c, F A (recursiveChild x i c) = true) ∧
      (failedGuards T label F G x i).card ≤  q := by
  simp only [tolerantRow, decide_eq_true_eq]

theorem tolerantFamily_true {n k r : ℕ} {I : Type} (T : Tournament k)
    (label : Fin k → Fin k → Fin r) (F : Fin n → (I → Bool) → Bool)
    (A G : Fin n) (q : ℕ) (x : ((Fin k × Fin r) × I) → Bool) :
    tolerantFamily T label F A G q x = true ↔
      ∃ i, tolerantRow T label F A G q x i = true := by
  simp only [tolerantFamily, decide_eq_true_eq]

theorem tolerantFamily_false {n k r : ℕ} {I : Type} (T : Tournament k)
    (label : Fin k → Fin k → Fin r) (F : Fin n → (I → Bool) → Bool)
    (A G : Fin n) (q : ℕ) (x : ((Fin k × Fin r) × I) → Bool) :
    tolerantFamily T label F A G q x = false ↔
      ∀ i, tolerantRow T label F A G q x i = false := by
  simp [tolerantFamily]

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
open _root_.Sensitivity213981Formal.ThreeBoundOrdinaryArchive.OAI.Paper320 Sensitivity205 Sensitivity2075

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
open _root_.Sensitivity213981Formal.ThreeBoundOrdinaryArchive.OAI.Paper320 Sensitivity2075
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
open _root_.Sensitivity213981Formal.ThreeBoundOrdinaryArchive.OAI.Paper320 Sensitivity205 Sensitivity2075
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
open _root_.Sensitivity213981Formal.ThreeBoundOrdinaryArchive.OAI.Paper320 Sensitivity2075 SensitivityQ
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
open _root_.Sensitivity213981Formal.ThreeBoundOrdinaryArchive.OAI.Paper320 Sensitivity2075 SensitivityQ
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
open _root_.Sensitivity213981Formal.ThreeBoundOrdinaryArchive.OAI.Paper320 Sensitivity2075 SensitivityQ
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
open _root_.Sensitivity213981Formal.ThreeBoundOrdinaryArchive.OAI.Paper320 Sensitivity2075 SensitivityQ
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
open _root_.Sensitivity213981Formal.ThreeBoundOrdinaryArchive.OAI.Paper320 Sensitivity2075 SensitivityQ ZL
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
open _root_.Sensitivity213981Formal.ThreeBoundOrdinaryArchive.OAI.Paper320 Sensitivity2075 SensitivityQ
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
open _root_.Sensitivity213981Formal.ThreeBoundOrdinaryArchive.OAI.Paper320 Sensitivity2075 SensitivityQ
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
open _root_.Sensitivity213981Formal.ThreeBoundOrdinaryArchive.OAI.Paper320 Sensitivity2075 SensitivityQ
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
end Sensitivity213981Formal

namespace Sensitivity213981Formal
section
/- Adapted complete accepted Apache-2.0 Prove2me proofs by @yousofy. See ordinary_provenance.json. -/


open _root_.OAI.Paper320 _root_.Sensitivity213981Formal.OAI.Paper320
namespace ThreeBoundOrdinaryArchive

/- Sol_Paley11987Verified_Sensitivity2075_tolerant_repair_cases.lean -/
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
open _root_.Sensitivity213981Formal.ThreeBoundOrdinaryArchive.OAI.Paper320







end Sensitivity205
namespace Sensitivity2075
open _root_.Sensitivity213981Formal.ThreeBoundOrdinaryArchive.OAI.Paper320 Sensitivity205













@[simp] theorem mem_missingTargets {n k r : ℕ} {I : Type}
    (F : Fin n → (I → Bool) → Bool) (A : Fin n)
    (x : ((Fin k × Fin r) × I) → Bool) (i : Fin k) (c : Fin r) :
    c ∈ missingTargets F A x i ↔ F A (recursiveChild x i c) = false := by
  simp [missingTargets]

@[simp] theorem mem_failedGuards {n k r : ℕ} {I : Type} (T : Tournament k)
    (label : Fin k → Fin k → Fin r) (F : Fin n → (I → Bool) → Bool)
    (G : Fin n) (x : ((Fin k × Fin r) × I) → Bool) (i j : Fin k) :
    j ∈ failedGuards T label F G x i ↔
      T.Adj i j ∧ F G (recursiveChild x j (label i j)) = true := by
  simp [failedGuards]

theorem missingTargets_empty {n k r : ℕ} {I : Type}
    (F : Fin n → (I → Bool) → Bool) (A : Fin n)
    (x : ((Fin k × Fin r) × I) → Bool) (i : Fin k) :
    missingTargets F A x i = ∅ ↔ ∀ c, F A (recursiveChild x i c) = true := by
  simp [missingTargets, Finset.filter_eq_empty_iff]







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






end Nesting











section JointCandidates








end JointCandidates





end Sensitivity2075
end
end z29

end ThreeBoundOrdinaryArchive

end
end Sensitivity213981Formal

namespace Sensitivity213981Formal
section
/- Adapted complete accepted Apache-2.0 Prove2me proofs by @yousofy. See ordinary_provenance.json. -/


open _root_.OAI.Paper320 _root_.Sensitivity213981Formal.OAI.Paper320
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
open _root_.Sensitivity213981Formal.ThreeBoundOrdinaryArchive.OAI.Paper320







end Sensitivity205
namespace Sensitivity2075
open _root_.Sensitivity213981Formal.ThreeBoundOrdinaryArchive.OAI.Paper320 Sensitivity205













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



theorem missing_singleton {n k r : ℕ} {I : Type}
    (F : Fin n → (I → Bool) → Bool) (A : Fin n)
    (x : ((Fin k × Fin r) × I) → Bool) (hr : 0 <  r) (i : Fin k)
    (hi : (missingTargets F A x i).card = 1) :
    missingTargets F A x i = {missingWitness F A x hr i} := by
  obtain ⟨c, hc⟩ := Finset.card_eq_one.mp hi
  have hne : (missingTargets F A x i).Nonempty := hc ▸ Finset.singleton_nonempty c
  have hm : missingWitness F A x hr i ∈ missingTargets F A x i := by
    simp only [missingWitness, dif_pos hne]
    exact hne.choose_spec
  rw [hc, Finset.mem_singleton] at hm
  simpa only [hm] using hc



theorem missingWitness_unique {n k r : ℕ} {I : Type}
    (F : Fin n → (I → Bool) → Bool) (A : Fin n)
    (x : ((Fin k × Fin r) × I) → Bool) (hr : 0 <  r) (i : Fin k)
    (hi : (missingTargets F A x i).card = 1) (c : Fin r)
    (hc : F A (recursiveChild x i c) = false) : c = missingWitness F A x hr i := by
  have hm := (mem_missingTargets F A x i c).mpr hc
  rwa [missing_singleton F A x hr i hi, Finset.mem_singleton] at hm

theorem missingWitness_other_true {n k r : ℕ} {I : Type}
    (F : Fin n → (I → Bool) → Bool) (A : Fin n)
    (x : ((Fin k × Fin r) × I) → Bool) (hr : 0 <  r) (i : Fin k)
    (hi : (missingTargets F A x i).card = 1) (c : Fin r)
    (hc : c ≠ missingWitness F A x hr i) : F A (recursiveChild x i c) = true := by
  cases hh : F A (recursiveChild x i c)
  · exact False.elim (hc (missingWitness_unique F A x hr i hi c hh))
  · rfl

section JointCandidates








end JointCandidates





end Sensitivity2075
end
end z29

section z32
set_option maxHeartbeats 3000000
noncomputable section
open _root_.Sensitivity213981Formal.ThreeBoundOrdinaryArchive.OAI.Paper320 Sensitivity205 Sensitivity2075
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
open _root_.Sensitivity213981Formal.ThreeBoundOrdinaryArchive.OAI.Paper320 Sensitivity205 Sensitivity2075
open scoped Classical BigOperators

namespace ZT
variable {n k : ℕ} {I : Type}

theorem target_guard_disjoint (T : Tournament k)
    (label : Fin k → Fin k → Fin 2) (F : Fin n → (I → Bool) → Bool)
    (t g : Fin n) (q : ℕ) (x : ((Fin k × Fin 2) × I) → Bool) :
    Disjoint (tolerantTargets T label F t g q x)
      (tolerantGuards T label F t g q x) := by
  apply Finset.disjoint_left.mpr
  intro i hi hj
  have hone := (Finset.mem_filter.mp hi).2.1
  have hempty := (Finset.mem_filter.mp hj).2.1
  simp only [hempty, Finset.card_empty] at hone
  omega



theorem target_mismatch_failed (T : Tournament k)
    (label : Fin k → Fin k → Fin 2) (F : Fin n → (I → Bool) → Bool)
    (hF : NestedFamily F) (t g : Fin n) (hgt : g ≤  t)
    (q : ℕ) (x : ((Fin k × Fin 2) × I) → Bool)
    (A : Finset (Fin k)) (hA : A ⊆ tolerantTargets T label F t g q x)
    (i : Fin k) :
    ZL.mismatch T.Adj (fun e => label e.1 e.2) A
      (missingWitness F t x (by decide)) i ⊆ failedGuards T label F g x i := by
  intro j hj
  obtain ⟨hjA,hij,hl⟩ := Finset.mem_filter.mp hj
  exact (mem_failedGuards T label F g x i j).mpr ⟨hij,
    hF.accepts_of_le hgt (missingWitness_other_true F t x (by decide) j
      (Finset.mem_filter.mp (hA hjA)).2.1 _ hl)⟩

theorem targets_ordinaryGood (T : Tournament k)
    (label : Fin k → Fin k → Fin 2) (F : Fin n → (I → Bool) → Bool)
    (hF : NestedFamily F) (t g : Fin n) (hgt : g ≤  t)
    (q : ℕ) (x : ((Fin k × Fin 2) × I) → Bool) :
    ZL.OrdinaryGood T.Adj (fun e => label e.1 e.2)
      (tolerantTargets T label F t g q x) q (missingWitness F t x (by decide)) := by
  intro i hi
  exact (Finset.card_le_card
    (target_mismatch_failed T label F hF t g hgt q x _ (fun _ h => h) i)).trans
    (Finset.mem_filter.mp hi).2.2





theorem targets_card_of_exclusion (T : Tournament k)
    (label : Fin k → Fin k → Fin 2) (F : Fin n → (I → Bool) → Bool)
    (hF : NestedFamily F) (t g : Fin n) (hgt : g ≤  t)
    (q w : ℕ) (hd : SensitivityQ.DefectBound T label q w)
    (x : ((Fin k × Fin 2) × I) → Bool) :
    (tolerantTargets T label F t g q x).card <  w := by
  exact hd _ _ (targets_ordinaryGood T label F hF t g hgt q x)



end ZT
end
end z40

section z43

set_option maxHeartbeats 8000000
noncomputable section
open scoped Classical BigOperators
open _root_.Sensitivity213981Formal.ThreeBoundOrdinaryArchive.OAI.Paper320 Sensitivity2075 SensitivityQ ZL
namespace ZT
variable {n k : ℕ} {I : Type} [Fintype I]



















end ZT
end
end z43

section z45

set_option maxHeartbeats 8000000
noncomputable section
open scoped Classical BigOperators
open _root_.Sensitivity213981Formal.ThreeBoundOrdinaryArchive.OAI.Paper320 Sensitivity2075 SensitivityQ
open ZP
namespace ZT
variable {n k : ℕ} {I : Type} [Fintype I]









end ZT
end
end z45

end ThreeBoundOrdinaryArchive

end
end Sensitivity213981Formal

namespace Sensitivity213981Formal
section
/- Adapted complete accepted Apache-2.0 Prove2me proofs by @yousofy. See ordinary_provenance.json. -/


open _root_.OAI.Paper320 _root_.Sensitivity213981Formal.OAI.Paper320
namespace ThreeBoundOrdinaryArchive

/- Sol_Paley11987Verified_CompactBooleanTransfer_ordinary_positive_of_cases.lean -/
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
open _root_.Sensitivity213981Formal.ThreeBoundOrdinaryArchive.OAI.Paper320







end Sensitivity205
namespace Sensitivity2075
open _root_.Sensitivity213981Formal.ThreeBoundOrdinaryArchive.OAI.Paper320 Sensitivity205













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

include hF in
theorem failedGuards_subset {Gi Gj : Fin n} (hG : Gj ≤  Gi)
    (x : ((Fin k × Fin r) × I) → Bool) (i : Fin k) :
    failedGuards T label F Gi x i ⊆ failedGuards T label F Gj x i := by
  intro j hj
  obtain ⟨hij, hon⟩ := (mem_failedGuards T label F Gi x i j).mp hj
  exact (mem_failedGuards T label F Gj x i j).mpr ⟨hij, hF.accepts_of_le hG hon⟩

include hF in
theorem tolerantRow_nested {Ai Aj Gi Gj : Fin n} {qi qj : ℕ}
    (hA : Ai ≤  Aj) (hG : Gj ≤  Gi) (hq : qj ≤  qi)
    (x : ((Fin k × Fin r) × I) → Bool) (i : Fin k)
    (hi : tolerantRow T label F Aj Gj qj x i = true) :
    tolerantRow T label F Ai Gi qi x i = true := by
  obtain ⟨ht, hg⟩ := (tolerantRow_true T label F Aj Gj qj x i).mp hi
  exact (tolerantRow_true T label F Ai Gi qi x i).mpr
    ⟨fun c => hF.accepts_of_le hA (ht c),
      (Finset.card_le_card (failedGuards_subset T label F hF hG x i)).trans (hg.trans hq)⟩

end Nesting



section JointCandidates
variable {n k r : ℕ} {I : Type} (T : Tournament k)
  (label : Fin k → Fin k → Fin r) (F : Fin n → (I → Bool) → Bool)
  (hF : NestedFamily F) (Ai Aj Gi Gj : Fin n)
  (hA : Ai ≤  Aj) (hG : Gj ≤  Gi)
  (x : ((Fin k × Fin r) × I) → Bool)





include hF hA hG in

theorem no_guard_candidate_of_strict {qi qj : ℕ} (hq : qj <  qi)
    (hx : tolerantFamily T label F Ai Gi qi x = false) {i : Fin k}
    (hi : i ∈ tolerantGuards T label F Aj Gj qj x) : False := by
  obtain ⟨hmiss, hguards⟩ := (Finset.mem_filter.mp hi).2
  have hrow : tolerantRow T label F Ai Gi qi x i = true := by
    apply (tolerantRow_true T label F Ai Gi qi x i).mpr
    refine ⟨fun c => hF.accepts_of_le hA ((missingTargets_empty F Aj x i).mp hmiss c), ?_⟩
    have hh := Finset.card_le_card (failedGuards_subset T label F hF hG x i)
    omega
  have hoff := (tolerantFamily_false T label F Ai Gi qi x).mp hx i
  simp [hoff] at hrow

end JointCandidates





end Sensitivity2075
end
end z29

section z30

set_option maxHeartbeats 3000000
noncomputable section
open scoped Classical BigOperators
open _root_.Sensitivity213981Formal.ThreeBoundOrdinaryArchive.OAI.Paper320 Sensitivity205 Sensitivity2075

namespace ZT

variable {I : Type} [Fintype I]























theorem family_nested {n k r : ℕ} {J : Type}
    (T : Tournament k) (label : Fin k → Fin k → Fin r)
    (F : Fin n → (J → Bool) → Bool) (hF : NestedFamily F)
    {Ai Aj Gi Gj : Fin n} {qi qj : ℕ}
    (hA : Ai ≤  Aj) (hG : Gj ≤  Gi) (hq : qj ≤  qi)
    (x : ((Fin k × Fin r) × J) → Bool)
    (hx : tolerantFamily T label F Aj Gj qj x = true) :
    tolerantFamily T label F Ai Gi qi x = true := by
  obtain ⟨v, hv⟩ := (tolerantFamily_true T label F Aj Gj qj x).mp hx
  exact (tolerantFamily_true T label F Ai Gi qi x).mpr
    ⟨v, tolerantRow_nested T label F hF hA hG hq x v hv⟩



end ZT
end
end z30

section z31

set_option maxHeartbeats 3000000
noncomputable section
open scoped Classical BigOperators
open _root_.Sensitivity213981Formal.ThreeBoundOrdinaryArchive.OAI.Paper320 Sensitivity2075
namespace ZT

variable {n k r : ℕ} {I : Type} [Fintype I]























end ZT
end
end z31

section z32
set_option maxHeartbeats 3000000
noncomputable section
open _root_.Sensitivity213981Formal.ThreeBoundOrdinaryArchive.OAI.Paper320 Sensitivity205 Sensitivity2075
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

section z33

set_option maxHeartbeats 5000000
noncomputable section
open scoped Classical BigOperators
open _root_.Sensitivity213981Formal.ThreeBoundOrdinaryArchive.OAI.Paper320 Sensitivity2075 SensitivityQ
namespace ZT
variable {n k : ℕ} {I : Type} [Fintype I]













theorem positiveTargets_empty_of_gate_eq (T : Tournament k) (label : Fin k → Fin k → Fin 2)
    (F : Fin n → (I → Bool) → Bool) (hF : NestedFamily F)
    (ta tb ga gb : Fin n) (ht : ta ≤  tb) (hg : gb ≤  ga) (heq : gb = ta)
    (qa q : ℕ) (hq : q ≤  qa)
    (x : ((Fin k × Fin 2) × I) → Bool)
    (hx : tolerantFamily T label F ta ga qa x = false) :
    positiveTargets T label F tb gb q x (by decide) = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro v hv
  obtain ⟨hT,htrue⟩ := Finset.mem_filter.mp hv
  have hfalse := tolerant_target_weak_false T label F hF ta tb ga gb ht hg x hq
    (by decide) hx hT
  rw [heq,hfalse] at htrue
  contradiction

end ZT
end
end z33

section z34

set_option maxHeartbeats 8000000
noncomputable section
open scoped Classical BigOperators
open _root_.Sensitivity213981Formal.ThreeBoundOrdinaryArchive.OAI.Paper320 Sensitivity2075 SensitivityQ
namespace ZT
variable {n k : ℕ} {I : Type} [Fintype I]









@[simp] theorem mem_guardArcs (T : Tournament k) (label : Fin k → Fin k → Fin 2)
    (F : Fin n → (I → Bool) → Bool) (t g : Fin n) (q : ℕ)
    (x : ((Fin k × Fin 2) × I) → Bool) (e : Fin k × Fin k) :
    e ∈ guardArcs T label F t g q x ↔
      e.1 ∈ tolerantGuards T label F t g q x ∧ e.2 ∈ failedGuards T label F g x e.1 := by
  simp [guardArcs]











end ZT
end
end z34

section z35

set_option maxHeartbeats 5000000
noncomputable section
open scoped Classical BigOperators
namespace ZT









end ZT
end
end z35

section z36
set_option maxHeartbeats 5000000
noncomputable section
open scoped Classical BigOperators
open _root_.Sensitivity213981Formal.ThreeBoundOrdinaryArchive.OAI.Paper320 Sensitivity2075 SensitivityQ
namespace SensitivityOrdinaryGuard










end SensitivityOrdinaryGuard
end
end z36

section z37

set_option maxHeartbeats 8000000
noncomputable section
open scoped Classical BigOperators
open _root_.Sensitivity213981Formal.ThreeBoundOrdinaryArchive.OAI.Paper320 Sensitivity2075 SensitivityQ
namespace ZT
variable {n k : ℕ} {I : Type} [Fintype I]















end ZT
end
end z37

section z40

set_option maxHeartbeats 3000000
noncomputable section
open _root_.Sensitivity213981Formal.ThreeBoundOrdinaryArchive.OAI.Paper320 Sensitivity205 Sensitivity2075
open scoped Classical BigOperators

namespace ZT
variable {n k : ℕ} {I : Type}

end ZT
end
end z40

section z41

set_option maxHeartbeats 8000000
noncomputable section
open scoped Classical BigOperators
open _root_.Sensitivity213981Formal.ThreeBoundOrdinaryArchive.OAI.Paper320 Sensitivity2075 SensitivityQ
namespace ZT
variable {n k : ℕ} {I : Type} [Fintype I]



theorem crossedTargetHeads_subset (T : Tournament k) (label : Fin k → Fin k → Fin 2)
    (F : Fin n → (I → Bool) → Bool) (t g : Fin n) (q : ℕ)
    (x : ((Fin k × Fin 2) × I) → Bool) :
    crossedTargetHeads T label F t g q x ⊆
      tolerantTargets T label F t g q x \ positiveTargets T label F t g q x (by decide) := by
  intro v hv
  obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hv
  exact Finset.mem_sdiff.mpr (Finset.mem_filter.mp hz).2

theorem crossedTargetHeads_of_failed (T : Tournament k) (label : Fin k → Fin k → Fin 2)
    (F : Fin n → (I → Bool) → Bool) (t g : Fin n) (q : ℕ)
    (x : ((Fin k × Fin 2) × I) → Bool) (v w : Fin k)
    (hv : v ∈ tolerantGuards T label F t g q x)
    (hw : w ∈ tolerantTargets T label F t g q x)
    (hP : w ∉ positiveTargets T label F t g q x (by decide))
    (hfailed : w ∈ failedGuards T label F g x v) :
    w ∈ crossedTargetHeads T label F t g q x := by
  have hwG : w ∉ tolerantGuards T label F t g q x := by
    exact Finset.disjoint_left.mp (target_guard_disjoint T label F t g q x) hw
  have hext : (v,w) ∈ externalGuardArcs T label F t g q x :=
    Finset.mem_filter.mpr ⟨(mem_guardArcs _ _ _ _ _ _ _ _).mpr ⟨hv,hfailed⟩,hwG⟩
  exact Finset.mem_image.mpr ⟨(w,label v w),Finset.mem_filter.mpr
    ⟨Finset.mem_image.mpr ⟨(v,w),hext,rfl⟩,hw,hP⟩,rfl⟩

theorem remaining_targets_subset (T : Tournament k) (label : Fin k → Fin k → Fin 2)
    (F : Fin n → (I → Bool) → Bool) (t g : Fin n) (q : ℕ)
    (x : ((Fin k × Fin 2) × I) → Bool) :
    remainingOrdinaryTargets T label F t g q x ⊆ tolerantTargets T label F t g q x := by
  intro v hv
  exact (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp hv).1).1

theorem remaining_targets_card (T : Tournament k) (label : Fin k → Fin k → Fin 2)
    (F : Fin n → (I → Bool) → Bool) (t g : Fin n) (q : ℕ)
    (x : ((Fin k × Fin 2) × I) → Bool) :
    (remainingOrdinaryTargets T label F t g q x).card+
      (crossedTargetHeads T label F t g q x).card+
      (positiveTargets T label F t g q x (by decide)).card =
      (tolerantTargets T label F t g q x).card := by
  have hC := Finset.card_sdiff_add_card_eq_card (crossedTargetHeads_subset T label F t g q x)
  have hP := Finset.card_sdiff_add_card_eq_card
    (show positiveTargets T label F t g q x (by decide) ⊆ tolerantTargets T label F t g q x from
      Finset.filter_subset _ _)
  change (remainingOrdinaryTargets T label F t g q x).card+_=_ at hC
  omega

theorem remaining_targets_guard_mismatch_empty (T : Tournament k) (label : Fin k → Fin k → Fin 2)
    (F : Fin n → (I → Bool) → Bool) (hF : NestedFamily F)
    (t g : Fin n) (hgt : g ≤  t) (q : ℕ)
    (x : ((Fin k × Fin 2) × I) → Bool) (v : Fin k)
    (hv : v ∈ tolerantGuards T label F t g q x) :
    ZL.mismatch T.Adj (fun e => label e.1 e.2)
      (remainingOrdinaryTargets T label F t g q x) (missingWitness F t x (by decide)) v = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro w hw
  have hfailed := target_mismatch_failed T label F hF t g hgt q x
    (remainingOrdinaryTargets T label F t g q x) (remaining_targets_subset T label F t g q x) v hw
  have hrem := (Finset.mem_filter.mp hw).1
  obtain ⟨hord,hnotC⟩ := Finset.mem_sdiff.mp hrem
  obtain ⟨hT,hnotP⟩ := Finset.mem_sdiff.mp hord
  exact hnotC (crossedTargetHeads_of_failed T label F t g q x v w hv hT hnotP hfailed)

theorem remaining_targets_marked_zero (T : Tournament k) (label : Fin k → Fin k → Fin 2)
    (F : Fin n → (I → Bool) → Bool) (hF : NestedFamily F)
    (t g : Fin n) (hgt : g ≤  t) (q : ℕ)
    (x : ((Fin k × Fin 2) × I) → Bool) (M : Finset (Fin k))
    (hM : M ⊆ tolerantGuards T label F t g q x) :
    ZL.MarkedGood T.Adj (fun e => label e.1 e.2)
      (remainingOrdinaryTargets T label F t g q x) M ∅ q 0
      (missingWitness F t x (by decide)) := by
  apply candidates_markedGood T label F hF t g hgt q 0 x
    (remainingOrdinaryTargets T label F t g q x) M ∅
    (remaining_targets_subset T label F t g q x)
    (fun v hv => Finset.mem_union_right _ (hM hv)) (Finset.empty_subset _)
  · apply (target_guard_disjoint T label F t g q x).mono
      (remaining_targets_subset T label F t g q x) hM
  · have he : (∑ v ∈ M, (ZL.mismatch T.Adj (fun e => label e.1 e.2)
        (remainingOrdinaryTargets T label F t g q x) (missingWitness F t x (by decide)) v).card) = 0 := by
      apply Finset.sum_eq_zero
      intro v hv
      rw [remaining_targets_guard_mismatch_empty T label F hF t g hgt q x v (hM hv)]
      rfl
    exact he.le



end ZT
end
end z41

section z43

set_option maxHeartbeats 8000000
noncomputable section
open scoped Classical BigOperators
open _root_.Sensitivity213981Formal.ThreeBoundOrdinaryArchive.OAI.Paper320 Sensitivity2075 SensitivityQ ZL
namespace ZT
variable {n k : ℕ} {I : Type} [Fintype I]













theorem remaining_card_guard_marked (T : Tournament k) (label : Fin k → Fin k → Fin 2)
    (F : Fin n → (I → Bool) → Bool) (hF : NestedFamily F)
    (t g : Fin n) (hgt : g ≤  t) (q r w : ℕ)
    (hcap : MarkedCardBound T label q r 0 0 w)
    (x : ((Fin k × Fin 2) × I) → Bool)
    (hr : r ≤  (tolerantGuards T label F t g q x).card) :
    (remainingOrdinaryTargets T label F t g q x).card <  w := by
  obtain ⟨M,hM,hcard⟩ := Finset.exists_subset_card_eq hr
  have hdis := (target_guard_disjoint T label F t g q x).mono
    (remaining_targets_subset T label F t g q x) hM
  exact hcap _ M ∅ _ hdis (Finset.empty_subset _) hcard rfl
    (remaining_targets_marked_zero T label F hF t g hgt q x M hM)





end ZT
end
end z43

section z45

set_option maxHeartbeats 8000000
noncomputable section
open scoped Classical BigOperators
open _root_.Sensitivity213981Formal.ThreeBoundOrdinaryArchive.OAI.Paper320 Sensitivity2075 SensitivityQ
open ZP
namespace ZT
variable {n k : ℕ} {I : Type} [Fintype I]









end ZT
end
end z45

section z58

set_option maxHeartbeats 8000000
noncomputable section
open scoped Classical BigOperators
open _root_.Sensitivity213981Formal.ThreeBoundOrdinaryArchive.OAI.Paper320 Sensitivity2075 SensitivityQ SensitivityOrdinaryGuard
namespace ZT
variable {n k : ℕ} {I : Type} [Fintype I]



end ZT
end
end z58

section z59

set_option maxHeartbeats 5000000
namespace ZT



theorem deletion_affine_endpoints (K ext intr e δ B S J : ℕ)
    (hδ : δ ≤  e) (he : e ≤  ext) :
    (K+δ)*B+(ext-δ)*S+(intr+δ)*J ≤ 
      max (K*B+ext*S+intr*J) ((K+e)*B+(ext-e)*S+(intr+e)*J) := by
  have hδext : δ ≤  ext := hδ.trans he
  have hδsum : (ext-δ)+δ=ext := Nat.sub_add_cancel hδext
  by_cases hc : B+J ≤  S
  · apply le_trans _ (le_max_left _ _)
    have hm := Nat.mul_le_mul_left δ hc
    nlinarith
  · apply le_trans _ (le_max_right _ _)
    have hcs : S ≤  B+J := by omega
    have hm := Nat.mul_le_mul_left (e-δ) hcs
    have hesum : (ext-e)+e=ext := Nat.sub_add_cancel he
    have hsub : (e-δ)+δ=e := Nat.sub_add_cancel hδ
    nlinarith

theorem deletion_cost_dominate (n K ext intr δ δ' B S J : ℕ)
    (hJS : J ≤  S) (hδ' : δ' ≤  δ) (hδ : δ ≤  ext) (hn : n ≤  K+δ') :
    n*B+(ext-δ)*S+(intr+δ)*J ≤ 
      (K+δ')*B+(ext-δ')*S+(intr+δ')*J := by
  have hb := Nat.mul_le_mul_right B hn
  have hm := Nat.mul_le_mul_left (δ-δ') hJS
  have hsub : (δ-δ')+δ'=δ := Nat.sub_add_cancel hδ'
  have he : (ext-δ)+δ=ext := Nat.sub_add_cancel hδ
  have he' : (ext-δ')+δ'=ext := Nat.sub_add_cancel (hδ'.trans hδ)
  nlinarith

theorem deletion_cost_bound (n K t ext intr budget δ B S J : ℕ)
    (hJS : J ≤  S) (hn : n ≤  t) (hnK : n ≤  K+δ)
    (hδ : δ ≤  budget) (hbudget : budget ≤  ext) :
    n*B+(ext-δ)*S+(intr+δ)*J ≤  deletionCost K t ext intr budget B S J := by
  let k := min K t
  let e := min t (k+budget)-k
  let δ' := min δ e
  have hk : k ≤  t := min_le_right _ _
  have he : e ≤  budget := by dsimp [e]; omega
  have hδe : δ' ≤  e := min_le_right _ _
  have hδδ : δ' ≤  δ := min_le_left _ _
  have hn' : n ≤  k+δ' := by dsimp [δ',e,k]; omega
  have hcost := deletion_cost_dominate n k ext intr δ δ' B S J hJS hδδ
    (hδ.trans hbudget) hn'
  exact hcost.trans (deletion_affine_endpoints k ext intr e δ' B S J hδe (he.trans hbudget))

end ZT
end z59

section z60

set_option maxHeartbeats 8000000
noncomputable section
open scoped Classical BigOperators
open _root_.Sensitivity213981Formal.ThreeBoundOrdinaryArchive.OAI.Paper320 Sensitivity2075 SensitivityQ
namespace ZT
variable {n k : ℕ} {I : Type} [Fintype I]









theorem candidateCost_le_deletionCost (q t u m δ a b s j K tt : ℕ)
    (hjs : j ≤  s) (ht : t ≤  tt) (hK : t-u ≤  K+δ)
    (hδ : δ+((u*m+u.choose 2)-q*u) ≤  m*(q+1)-m.choose 2) :
    candidateCost q t u m δ a b s j ≤ 
      u*a+deletionCost K (tt-u)
        ((m*(q+1)-m.choose 2)-(((u*m+u.choose 2)-q*u)-u))
        (min (m.choose 2) (2*m)+min u (((u*m+u.choose 2)-q*u)-u))
        ((m*(q+1)-m.choose 2)-((u*m+u.choose 2)-q*u)) b s j := by
  let E := m*(q+1)-m.choose 2
  let L := (u*m+u.choose 2)-q*u
  let save := L-u
  let intr := min (m.choose 2) (2*m)
  have hδ' : δ ≤  E-L := by change δ+L ≤  E at hδ; omega
  have hbudget : E-L ≤  E-save := by dsimp [save]; omega
  have hh := deletion_cost_bound (t-u) K (tt-u) (E-save) (intr+min u save)
    (E-L) δ b s j hjs (Nat.sub_le_sub_right ht u) hK hδ' hbudget
  have hh' := Nat.add_le_add_left hh (u*a)
  simpa only [candidateCost,Nat.add_assoc] using hh'

end ZT
end
end z60

section z61

set_option maxHeartbeats 8000000
noncomputable section
open scoped Classical BigOperators
open _root_.Sensitivity213981Formal.ThreeBoundOrdinaryArchive.OAI.Paper320 Sensitivity2075 SensitivityQ
open ZP
namespace ZT
variable {n k : ℕ} {I : Type} [Fintype I]













end ZT
end
end z61

end ThreeBoundOrdinaryArchive

end
end Sensitivity213981Formal

namespace Sensitivity213981Formal
section
/- The exact ordinary caps needed for the third endpoint.  The actual flip
accounting below reuses the proved ordinary transfer argument; only the
exclusion constants change.  Small-tolerance branches are not used here. -/


set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 30000

namespace ThreeBoundOrdinary5591
open ThreeBoundOrdinaryArchive
open ThreeBoundOrdinaryArchive.OAI.Paper320
open ThreeBoundOrdinaryArchive.Sensitivity2075
open ThreeBoundOrdinaryArchive.SensitivityQ
open ThreeBoundOrdinaryArchive.ZT
open scoped Classical BigOperators
noncomputable section













variable {n k : ℕ} {I : Type} [Fintype I]





theorem markedDeletionCap_bound (T : Tournament k) (label : Fin k → Fin k → Fin 2)
    (hCaps : LabelCaps T label) (F : Fin n → (I → Bool) → Bool) (hF : NestedFamily F)
    (t g : Fin n) (hgt : g ≤  t) (q : ℕ) (hq : 4 ≤  q) (hq8 : q ≤  8)
    (x : ((Fin k × Fin 2) × I) → Bool) :
    (tolerantTargets T label F t g q x).card-
      (positiveTargets T label F t g q x (by decide)).card ≤ 
      markedCap q (tolerantGuards T label F t g q x).card+
        (crossedTargetHeads T label F t g q x).card := by
  let C := tolerantTargets T label F t g q x
  let G := tolerantGuards T label F t g q x
  let P := positiveTargets T label F t g q x (by decide)
  let A := remainingOrdinaryTargets T label F t g q x
  let δ := (crossedTargetHeads T label F t g q x).card
  have hpart : A.card+δ+P.card=C.card := remaining_targets_card T label F t g q x
  have hrem : A.card ≤  markedCap q G.card := by
    unfold markedCap
    split_ifs with he
    · obtain ⟨rfl,hm⟩ := he
      have hh := remaining_card_guard_marked T label F hF t g hgt 4 6 31 hCaps.zero_four_six x
        (by simpa only [G] using hm.ge)
      change A.card <  31 at hh
      omega
    · have hc := targets_card_of_exclusion T label F hF t g hgt q (cutoff q)
        (hCaps.ordinary q hq hq8) x
      change C.card <  cutoff q at hc
      have hn : cutoff q ≤  68 := by interval_cases q <;> decide
      omega
  change C.card-P.card ≤  markedCap q G.card+δ
  omega

theorem ordinary_positive_of_cases (T : Tournament k) (label : Fin k → Fin k → Fin 2)
    (hCaps : LabelCaps T label) (F : Fin n → (I → Bool) → Bool) (hF : NestedFamily F)
    (ta tb ga gb : Fin n) (ht : ta ≤  tb) (hg : gb ≤  ga) (hga : ga ≤  ta)
    (qa q : ℕ) (hq : q ≤  qa) (hlarge : 4 ≤  q) (hq8 : q ≤  8)
    (a b s j z : ℕ) (hjs : j ≤  s)
    (ha : PBound F gb ta tb a) (hb : ABound F gb tb b)
    (hs : BBound F gb ga s) (hj : BBound F gb tb j)
    (hcases : ∀ m u, m ≤  (if qa=q then 2*q+3 else 0) → u ≤  2*q+1 →
      (u+m).choose 2 ≤  q*u+(q+1)*m → u ≤  candidateTotalCap q m u →
      (0 <  u → gb ≠ ta) → positiveCaseCost q m u a b s j ≤  z)
    (x : ((Fin k × Fin 2) × I) → Bool)
    (hx : tolerantFamily T label F ta ga qa x = false) :
    (flipsTo (tolerantFamily T label F tb gb q) true x).card ≤  z := by
  let C := tolerantTargets T label F tb gb q x
  let G := tolerantGuards T label F tb gb q x
  let P := positiveTargets T label F tb gb q x (by decide)
  let δ := (crossedTargetHeads T label F tb gb q x).card
  have hgt : gb ≤  tb := hg.trans (hga.trans ht)
  have hxq : tolerantFamily T label F ta ga q x = false := by
    cases hh : tolerantFamily T label F ta ga q x
    · rfl
    · have hw := family_nested T label F hF (le_refl ta) (le_refl ga) hq x hh
      simp [hx] at hw
  have hm : G.card ≤  if qa=q then 2*q+3 else 0 := by
    split_ifs with he
    · exact guards_card T label F hF tb gb hgt q x
    · have hstrict : q <  qa := by omega
      have hempty : G=∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro v hv
        exact no_guard_candidate_of_strict T label F hF ta tb ga gb ht hg x hstrict hx hv
      simp [hempty]
  have hu : P.card ≤  2*q+1 := positiveTargets_card T label F hF tb gb hgt q x (by decide)
  have hc : (P.card+G.card).choose 2 ≤  q*P.card+(q+1)*G.card :=
    positiveTargets_guards_coupling T label F hF tb gb hgt q x (by decide)
  have htt : C.card ≤  candidateTotalCap q G.card P.card :=
    candidateTotalCap_bound T label hCaps F hF tb gb hgt q hlarge hq8 x
  have huC : P.card ≤  C.card := Finset.card_le_card (Finset.filter_subset _ _)
  have hskip : 0 <  P.card → gb ≠ ta := by
    intro hn he
    have hempty := positiveTargets_empty_of_gate_eq T label F hF ta tb ga gb ht hg he qa q hq x hx
    have hh : P.card=0 := by simp only [P,hempty,Finset.card_empty]
    omega
  have hK := markedDeletionCap_bound T label hCaps F hF tb gb hgt q hlarge hq8 x
  have hδ := crossedTargetHeads_budget T label F hF tb gb hgt q x
  have hraw := ordinary_zero_candidate_cost T label F hF ta tb ga gb ht hg hga q a b s j
    hjs ha hb hs hj x hxq
  have hcost := candidateCost_le_deletionCost q C.card P.card G.card δ a b s j
    (markedCap q G.card) (candidateTotalCap q G.card P.card) hjs htt hK hδ
  exact hraw.trans (hcost.trans (hcases G.card P.card hm hu hc (huC.trans htt) hskip))

end
end ThreeBoundOrdinary5591



end
end Sensitivity213981Formal

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem solution :
∀ {n k : Nat} {I : Type} [inst : Fintype.{0} I]
  (T : Sensitivity213981Formal.ThreeBoundOrdinaryArchive.OAI.Paper320.Tournament k)
  (label : Fin k → Fin k → Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
  (hCaps : @Sensitivity213981Formal.ThreeBoundOrdinary5591.LabelCaps k T label) (F : Fin n → (I → Bool) → Bool)
  (hF : @Sensitivity213981Formal.ThreeBoundOrdinaryArchive.OAI.Paper320.NestedFamily n I F) (ta tb ga gb : Fin n)
  (ht : @LE.le.{0} (Fin n) (@instLEFin n) ta tb) (hg : @LE.le.{0} (Fin n) (@instLEFin n) gb ga)
  (hga : @LE.le.{0} (Fin n) (@instLEFin n) ga ta) (qa q : Nat) (hq : @LE.le.{0} Nat instLENat q qa)
  (hlarge : @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) q)
  (hq8 : @LE.le.{0} Nat instLENat q (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))) (a b s j z : Nat)
  (hjs : @LE.le.{0} Nat instLENat j s)
  (ha : @Sensitivity213981Formal.ThreeBoundOrdinaryArchive.ZT.PBound I inst n F gb ta tb a)
  (hb : @Sensitivity213981Formal.ThreeBoundOrdinaryArchive.ZT.ABound I inst n F gb tb b)
  (hs : @Sensitivity213981Formal.ThreeBoundOrdinaryArchive.ZT.BBound I inst n F gb ga s)
  (hj : @Sensitivity213981Formal.ThreeBoundOrdinaryArchive.ZT.BBound I inst n F gb tb j)
  (hcases :
    ∀ (m u : Nat),
      @LE.le.{0} Nat instLENat m
          (@ite.{1} Nat (@Eq.{1} Nat qa q) (instDecidableEqNat qa q)
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) q)
              (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
            (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) →
        @LE.le.{0} Nat instLENat u
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) q)
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) →
          @LE.le.{0} Nat instLENat
              (Nat.choose (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) u m)
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) q u)
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) q
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                  m)) →
            @LE.le.{0} Nat instLENat u (Sensitivity213981Formal.ThreeBoundOrdinary5591.candidateTotalCap q m u) →
              (@LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) u →
                  @Ne.{1} (Fin n) gb ta) →
                @LE.le.{0} Nat instLENat (Sensitivity213981Formal.ThreeBoundOrdinary5591.positiveCaseCost q m u a b s j)
                  z)
  (x : Prod.{0, 0} (Prod.{0, 0} (Fin k) (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))) I → Bool)
  (hx :
    @Eq.{1} Bool
      (@Sensitivity213981Formal.ThreeBoundOrdinaryArchive.Sensitivity2075.tolerantFamily n k
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) I T label F ta ga qa x)
      Bool.false),
  @LE.le.{0} Nat instLENat
    (@Finset.card.{0}
      (Prod.{0, 0} (Prod.{0, 0} (Fin k) (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))) I)
      (@Sensitivity213981Formal.ThreeBoundOrdinaryArchive.ZT.flipsTo
        (Prod.{0, 0} (Prod.{0, 0} (Fin k) (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))) I)
        (@instFintypeProd.{0, 0}
          (Prod.{0, 0} (Fin k) (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))) I
          (@instFintypeProd.{0, 0} (Fin k) (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
            (Fin.fintype k) (Fin.fintype (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
          inst)
        (@Sensitivity213981Formal.ThreeBoundOrdinaryArchive.Sensitivity2075.tolerantFamily n k
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) I T label F tb gb q)
        Bool.true x))
    z := @Sensitivity213981Formal.ThreeBoundOrdinary5591.ordinary_positive_of_cases
