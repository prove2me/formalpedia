-- Prove2me | solution 1 for Sensitivity213981Formal.ThreeBoundOrdinaryArchive.ZT.ordinary_zero_candidate_cost
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-26T19:29:02.591983+00:00
-- url     : https://prove2.me/submissions/97e9de8e-f9f6-40e8-a8ad-16613c13feb1

import Definitions.Def_Sensitivity213981Formal_Namespaces
import Definitions.Def_Sensitivity213981Formal_NamespacesComplete
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
import Theorems.Thm_Sensitivity213981Formal_ThreeBoundOrdinaryArchive_Paley11987Verified_Sensitivity2075_tolerant_repair_cases
import Theorems.Thm_Sensitivity213981Formal_ThreeBoundOrdinaryArchive_Sensitivity2075_tolerant_target_weak_false
import Theorems.Thm_Sensitivity213981Formal_ThreeBoundOrdinaryArchive_ZT_external_outside_positive_budget
import Theorems.Thm_Sensitivity213981Formal_ThreeBoundOrdinaryArchive_ZT_guardArcs_card
import Theorems.Thm_Sensitivity213981Formal_ThreeBoundOrdinaryArchive_ZT_positive_union_charge
import Theorems.Thm_Sensitivity213981Formal_ThreeBoundOrdinaryArchive_ZT_sum_binary_weights


namespace Sensitivity213981Formal
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
open OAI.Paper320







end Sensitivity205
namespace Sensitivity2075
open OAI.Paper320 Sensitivity205



















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
end Sensitivity213981Formal

namespace Sensitivity213981Formal
section
/- Adapted complete accepted Apache-2.0 Prove2me proofs by @yousofy. See ordinary_provenance.json. -/


open OAI.Paper320
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
open OAI.Paper320







end Sensitivity205
namespace Sensitivity2075
open OAI.Paper320 Sensitivity205













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
end Sensitivity213981Formal

namespace Sensitivity213981Formal
section
/- Adapted complete accepted Apache-2.0 Prove2me proofs by @yousofy. See ordinary_provenance.json. -/


open OAI.Paper320
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









@[simp] theorem mem_childLift {J I : Type} (j : J) (A : Finset I) (p : J × I) :
    p ∈ childLift j A ↔ p.1 = j ∧ p.2 ∈ A := by
  rcases p with ⟨k, a⟩
  unfold childLift
  rw [Finset.mem_map]
  constructor
  · rintro ⟨b, hb, hp⟩
    change (j, b) = (k, a) at hp
    cases hp
    exact ⟨rfl, hb⟩
  · rintro ⟨rfl, ha⟩
    exact ⟨a, ha, rfl⟩

@[simp] theorem childLift_card {J I : Type} (j : J) (A : Finset I) :
    (childLift j A).card = A.card := Finset.card_map _







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

theorem tolerant_guard_sets_eq (q : ℕ)
    (hx : tolerantFamily T label F Ai Gi q x = false) {i : Fin k}
    (hi : i ∈ tolerantGuards T label F Aj Gj q x) :
    failedGuards T label F Gi x i = failedGuards T label F Gj x i := by
  obtain ⟨hmiss, hguards⟩ := (Finset.mem_filter.mp hi).2
  have htargets : ∀ c, F Ai (recursiveChild x i c) = true :=
    fun c => hF.accepts_of_le hA ((missingTargets_empty F Aj x i).mp hmiss c)
  have hcount : q <  (failedGuards T label F Gi x i).card := by
    by_contra hn
    have hrow := (tolerantRow_true T label F Ai Gi q x i).mpr ⟨htargets, by omega⟩
    have hoff := (tolerantFamily_false T label F Ai Gi q x).mp hx i
    simp [hoff] at hrow
  exact Finset.eq_of_subset_of_card_le (failedGuards_subset T label F hF hG x i) (by omega)



end JointCandidates





end Sensitivity2075
end
end z29

section z30

set_option maxHeartbeats 3000000
noncomputable section
open scoped Classical BigOperators
open OAI.Paper320 Sensitivity205 Sensitivity2075

namespace ZT

variable {I : Type} [Fintype I]



@[simp] theorem mem_flipsTo (f : (I → Bool) → Bool) (b : Bool) (x : I → Bool)
    (a : I) : a ∈ flipsTo f b x ↔ f (_root_.OAI.Paper320.flip x {a}) = b := by
  simp [flipsTo]



















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
open OAI.Paper320 Sensitivity2075
namespace ZT

variable {n k r : ℕ} {I : Type} [Fintype I]



@[simp] theorem childFlipsTo_card (F : Fin n → (I → Bool) → Bool) (a : Fin n) (b : Bool)
    (x : ((Fin k × Fin r) × I) → Bool) (v : Fin k) (c : Fin r) :
    (childFlipsTo F a b x v c).card = (flipsTo (F a) b (recursiveChild x v c)).card := by
  simp [childFlipsTo]

@[simp] theorem mem_childFlipsTo_same (F : Fin n → (I → Bool) → Bool) (a : Fin n) (b : Bool)
    (x : ((Fin k × Fin r) × I) → Bool) (v : Fin k) (c : Fin r) (z : I) :
    ((v,c),z) ∈ childFlipsTo F a b x v c ↔
      F a (_root_.OAI.Paper320.flip (recursiveChild x v c) {z}) = b := by
  simp [childFlipsTo]

















end ZT
end
end z31

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

section z33

set_option maxHeartbeats 5000000
noncomputable section
open scoped Classical BigOperators
open OAI.Paper320 Sensitivity2075 SensitivityQ
namespace ZT
variable {n k : ℕ} {I : Type} [Fintype I]





theorem up_subset_repairs (T : Tournament k) (label : Fin k → Fin k → Fin 2)
    (F : Fin n → (I → Bool) → Bool) (t g : Fin n) (q : ℕ)
    (x : ((Fin k × Fin 2) × I) → Bool)
    (hx : tolerantFamily T label F t g q x = false) :
    flipsTo (tolerantFamily T label F t g q) true x ⊆
      targetRepairs T label F t g q x ∪ guardRepairs T label F t g q x := by
  rintro ⟨⟨w,c⟩,a⟩ hp
  obtain ⟨v,hv⟩ := (tolerantFamily_true T label F t g q _).mp
    ((mem_flipsTo _ _ _ _).mp hp)
  have hoff := (tolerantFamily_false T label F t g q x).mp hx v
  rcases _root_.Sensitivity213981Formal.ThreeBoundOrdinaryArchive.Paley11987Verified.Sensitivity2075.tolerant_repair_cases T label F t g q x v w c a hoff hv with
    ⟨hT, hw, hfalse, htrue⟩ | ⟨hG, hadj, hc, htrue, hfalse⟩
  · subst w
    have hc := missingWitness_unique F t x (by decide) v
      (Finset.mem_filter.mp hT).2.1 c hfalse
    apply Finset.mem_union_left
    apply Finset.mem_biUnion.mpr
    refine ⟨v,hT,?_⟩
    rw [← hc]
    exact (mem_childFlipsTo_same _ _ _ _ _ _ _).mpr htrue
  · subst c
    apply Finset.mem_union_right
    apply Finset.mem_biUnion.mpr
    refine ⟨v,hG,Finset.mem_biUnion.mpr ⟨w,?_,?_⟩⟩
    · exact (mem_failedGuards T label F g x v w).mpr ⟨hadj,htrue⟩
    · exact (mem_childFlipsTo_same _ _ _ _ _ _ _).mpr hfalse



theorem targetRepairs_card (T : Tournament k) (label : Fin k → Fin k → Fin 2)
    (F : Fin n → (I → Bool) → Bool) (hF : NestedFamily F)
    (ta tb ga gb : Fin n) (ht : ta ≤  tb) (hg : gb ≤  ga)
    (qa q : ℕ) (hq : q ≤  qa) (a b : ℕ)
    (ha : PBound F gb ta tb a) (hb : ABound F gb tb b)
    (x : ((Fin k × Fin 2) × I) → Bool)
    (hx : tolerantFamily T label F ta ga qa x = false) :
    (targetRepairs T label F tb gb q x).card ≤ 
      (positiveTargets T label F tb gb q x (by decide)).card*a+
      ((tolerantTargets T label F tb gb q x).card-
        (positiveTargets T label F tb gb q x (by decide)).card)*b := by
  let S := tolerantTargets T label F tb gb q x
  let tw := missingWitness F tb x (by decide)
  let p := fun v => F gb (recursiveChild x v (tw v)) = true
  have hsum : (targetRepairs T label F tb gb q x).card ≤ 
      ∑ v ∈ S, if p v then a else b := by
    apply Finset.card_biUnion_le.trans
    apply Finset.sum_le_sum
    intro v hv
    have hta := tolerant_target_weak_false T label F hF ta tb ga gb ht hg x hq
      (by decide) hx hv
    by_cases hp : p v
    · simpa only [if_pos hp, childFlipsTo_card] using ha _ hp hta
    · have hfalse : F gb (recursiveChild x v (tw v)) = false := by
        simpa only [p, Bool.not_eq_true] using hp
      simpa only [if_neg hp, childFlipsTo_card] using hb _ hfalse
  rw [sum_binary_weights] at hsum
  exact hsum





end ZT
end
end z33

section z34

set_option maxHeartbeats 8000000
noncomputable section
open scoped Classical BigOperators
open OAI.Paper320 Sensitivity2075 SensitivityQ
namespace ZT
variable {n k : ℕ} {I : Type} [Fintype I]









@[simp] theorem mem_guardArcs (T : Tournament k) (label : Fin k → Fin k → Fin 2)
    (F : Fin n → (I → Bool) → Bool) (t g : Fin n) (q : ℕ)
    (x : ((Fin k × Fin 2) × I) → Bool) (e : Fin k × Fin k) :
    e ∈ guardArcs T label F t g q x ↔
      e.1 ∈ tolerantGuards T label F t g q x ∧ e.2 ∈ failedGuards T label F g x e.1 := by
  simp [guardArcs]



theorem guardRepairs_subset_coordinates (T : Tournament k) (label : Fin k → Fin k → Fin 2)
    (F : Fin n → (I → Bool) → Bool) (t g : Fin n) (q : ℕ)
    (x : ((Fin k × Fin 2) × I) → Bool) :
    guardRepairs T label F t g q x ⊆
      ((externalGuardArcs T label F t g q x).image (arcCoordinate label)).biUnion
        (fun z => childFlipsTo F g false x z.1 z.2) ∪
      ((internalGuardArcs T label F t g q x).image (arcCoordinate label)).biUnion
        (fun z => childFlipsTo F g false x z.1 z.2) := by
  intro p hp
  obtain ⟨v,hv,hp⟩ := Finset.mem_biUnion.mp hp
  obtain ⟨w,hw,hp⟩ := Finset.mem_biUnion.mp hp
  have harc : (v,w) ∈ guardArcs T label F t g q x := (mem_guardArcs _ _ _ _ _ _ _ _).mpr ⟨hv,hw⟩
  by_cases hin : w ∈ tolerantGuards T label F t g q x
  · apply Finset.mem_union_right
    exact Finset.mem_biUnion.mpr ⟨(w,label v w),Finset.mem_image.mpr
      ⟨(v,w),Finset.mem_filter.mpr ⟨harc,hin⟩,rfl⟩,hp⟩
  · apply Finset.mem_union_left
    exact Finset.mem_biUnion.mpr ⟨(w,label v w),Finset.mem_image.mpr
      ⟨(v,w),Finset.mem_filter.mpr ⟨harc,hin⟩,rfl⟩,hp⟩

theorem filter_image_card_le {A B : Type} [DecidableEq A] [DecidableEq B]
    (S : Finset A) (f : A → B) (p : B → Prop) [DecidablePred p] :
    ((S.image f).filter p).card ≤  (S.filter fun a => p (f a)).card := by
  have hsub : (S.image f).filter p ⊆ (S.filter fun a => p (f a)).image f := by
    intro b hb
    obtain ⟨hb,hp⟩ := Finset.mem_filter.mp hb
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hb
    exact Finset.mem_image.mpr ⟨a,Finset.mem_filter.mpr ⟨ha,hp⟩,rfl⟩
  exact (Finset.card_le_card hsub).trans (Finset.card_image_le)

theorem positive_costly_coordinates_card (T : Tournament k) (label : Fin k → Fin k → Fin 2)
    (F : Fin n → (I → Bool) → Bool) (t g : Fin n) (q : ℕ)
    (x : ((Fin k × Fin 2) × I) → Bool) (Z : Finset (Fin k × Fin 2)) :
    (Z.filter fun z => z.1 ∈ positiveTargets T label F t g q x (by decide) ∧
      F t (recursiveChild x z.1 z.2) = false).card ≤ 
      (positiveTargets T label F t g q x (by decide)).card := by
  let S := Z.filter fun z => z.1 ∈ positiveTargets T label F t g q x (by decide) ∧
    F t (recursiveChild x z.1 z.2) = false
  have hinj : Set.InjOn Prod.fst (↑S : Set (Fin k × Fin 2)) := by
    intro z hz w hw he
    have hz' := (Finset.mem_filter.mp hz).2
    have hw' := (Finset.mem_filter.mp hw).2
    have hzt := (Finset.mem_filter.mp hz'.1).1
    have hwt := (Finset.mem_filter.mp hw'.1).1
    have hzc := missingWitness_unique F t x (by decide) z.1
      (Finset.mem_filter.mp hzt).2.1 z.2 hz'.2
    have hwc := missingWitness_unique F t x (by decide) w.1
      (Finset.mem_filter.mp hwt).2.1 w.2 hw'.2
    apply Prod.ext he
    rw [hzc,hwc,he]
  have hcard : (S.image Prod.fst).card = S.card := Finset.card_image_iff.mpr hinj
  have hsub : S.image Prod.fst ⊆ positiveTargets T label F t g q x (by decide) := by
    intro v hv
    obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hv
    exact (Finset.mem_filter.mp hz).2.1
  change S.card ≤  _
  rw [← hcard]
  exact Finset.card_le_card hsub

theorem positive_coordinates_card (P : Finset (Fin k)) (Z : Finset (Fin k × Fin 2)) :
    (Z.filter fun z => z.1 ∈ P).card ≤  2*P.card := by
  have hs : Z.filter (fun z => z.1 ∈ P) ⊆ P ×ˢ Finset.univ := by
    intro z hz
    exact Finset.mem_product.mpr ⟨(Finset.mem_filter.mp hz).2,Finset.mem_univ _⟩
  simpa [Nat.mul_comm] using Finset.card_le_card hs

end ZT
end
end z34

section z35

set_option maxHeartbeats 5000000
noncomputable section
open scoped Classical BigOperators
namespace ZT







theorem by_head_child_card {H α : Type} [DecidableEq H] [DecidableEq α]
    (S : Finset H) (Z : Finset (H × Fin 2)) (D : H × Fin 2 → Finset α) (j : ℕ)
    (hZS : ∀ z ∈ Z, z.1 ∈ S) (hD : ∀ z ∈ Z, (D z).card ≤  j) :
    (Z.biUnion D).card ≤  (2*S.card)*j := by
  have hcard : Z.card ≤  2*S.card := by
    have hsub : Z ⊆ S ×ˢ Finset.univ := by
      intro z hz
      exact Finset.mem_product.mpr ⟨hZS z hz,Finset.mem_univ _⟩
    simpa [Nat.mul_comm] using Finset.card_le_card hsub
  calc
    (Z.biUnion D).card ≤  ∑ z ∈ Z, (D z).card := Finset.card_biUnion_le
    _ ≤  ∑ _z ∈ Z, j := Finset.sum_le_sum hD
    _ = Z.card*j := by simp
    _ ≤  (2*S.card)*j := Nat.mul_le_mul_right j hcard

end ZT
end
end z35

section z36
set_option maxHeartbeats 5000000
noncomputable section
open scoped Classical BigOperators
open OAI.Paper320 Sensitivity2075 SensitivityQ
namespace SensitivityOrdinaryGuard










end SensitivityOrdinaryGuard
end
end z36

section z37

set_option maxHeartbeats 8000000
noncomputable section
open scoped Classical BigOperators
open OAI.Paper320 Sensitivity2075 SensitivityQ
namespace ZT
variable {n k : ℕ} {I : Type} [Fintype I]





theorem ordinary_failed_target_true (T : Tournament k) (label : Fin k → Fin k → Fin 2)
    (F : Fin n → (I → Bool) → Bool) (t g : Fin n) (q : ℕ)
    (x : ((Fin k × Fin 2) × I) → Bool) (z : Fin k × Fin 2)
    (hz : z ∈ externalGuardCoordinates T label F t g q x)
    (hT : z.1 ∈ tolerantTargets T label F t g q x)
    (hU : z.1 ∉ positiveTargets T label F t g q x (by decide)) :
    F t (recursiveChild x z.1 z.2) = true := by
  obtain ⟨e,he,rfl⟩ := Finset.mem_image.mp hz
  have harc := (mem_guardArcs T label F t g q x e).mp (Finset.mem_filter.mp he).1
  have hgate := ((mem_failedGuards T label F g x e.1 e.2).mp harc.2).2
  cases ht : F t (recursiveChild x e.2 (label e.1 e.2))
  · have hsel := missingWitness_unique F t x (by decide) e.2
      (Finset.mem_filter.mp hT).2.1 (label e.1 e.2) ht
    apply False.elim
    apply hU
    apply Finset.mem_filter.mpr
    refine ⟨hT,?_⟩
    simpa only [arcCoordinate,←hsel] using hgate
  · exact ht

theorem crossedTargetHeads_cheap_card (T : Tournament k) (label : Fin k → Fin k → Fin 2)
    (F : Fin n → (I → Bool) → Bool) (t g : Fin n) (q : ℕ)
    (x : ((Fin k × Fin 2) × I) → Bool) :
    (crossedTargetHeads T label F t g q x).card ≤ 
      ((externalGuardCoordinates T label F t g q x).filter fun z =>
        z.1 ∉ positiveTargets T label F t g q x (by decide) ∧
          ¬ F t (recursiveChild x z.1 z.2) = false).card := by
  apply Finset.card_image_le.trans
  apply Finset.card_le_card
  intro z hz
  obtain ⟨hz,hT,hU⟩ := Finset.mem_filter.mp hz
  refine Finset.mem_filter.mpr ⟨hz,hU,?_⟩
  have hon := ordinary_failed_target_true T label F t g q x z hz hT hU
  simp [hon]

theorem selected_guard_weak_true (T : Tournament k) (label : Fin k → Fin k → Fin 2)
    (F : Fin n → (I → Bool) → Bool) (hF : NestedFamily F)
    (ta tb ga gb : Fin n) (ht : ta ≤  tb) (hg : gb ≤  ga) (q : ℕ)
    (x : ((Fin k × Fin 2) × I) → Bool)
    (hx : tolerantFamily T label F ta ga q x = false)
    (e : Fin k × Fin k) (he : e ∈ guardArcs T label F tb gb q x) :
    F ga (recursiveChild x e.2 (label e.1 e.2)) = true := by
  have he' := (mem_guardArcs T label F tb gb q x e).mp he
  have hh := tolerant_guard_sets_eq T label F hF ta tb ga gb ht hg x q hx he'.1
  have hmem : e.2 ∈ failedGuards T label F ga x e.1 := by rw [hh]; exact he'.2
  exact ((mem_failedGuards T label F ga x e.1 e.2).mp hmem).2

theorem internal_guard_cost (T : Tournament k) (label : Fin k → Fin k → Fin 2)
    (F : Fin n → (I → Bool) → Bool) (hF : NestedFamily F)
    (t g : Fin n) (hgt : g ≤  t) (q : ℕ) (j : ℕ) (hj : BBound F g t j)
    (x : ((Fin k × Fin 2) × I) → Bool) :
    (((internalGuardArcs T label F t g q x).image (arcCoordinate label)).biUnion
      (fun z => childFlipsTo F g false x z.1 z.2)).card ≤ 
      min ((tolerantGuards T label F t g q x).card.choose 2)
        (2*(tolerantGuards T label F t g q x).card)*j := by
  let R := tolerantGuards T label F t g q x
  let S := internalGuardArcs T label F t g q x
  let Z := S.image (arcCoordinate label)
  let D := fun z : Fin k × Fin 2 => childFlipsTo F g false x z.1 z.2
  have hhead : ∀ z ∈ Z, z.1 ∈ R := by
    intro z hz
    obtain ⟨e,he,rfl⟩ := Finset.mem_image.mp hz
    exact (Finset.mem_filter.mp he).2
  have hD : ∀ z ∈ Z, (D z).card ≤  j := by
    intro z hz
    have hon := (missingTargets_empty F t x z.1).mp (Finset.mem_filter.mp (hhead z hz)).2.1 z.2
    simpa only [D,childFlipsTo_card] using hj _ hon
  have hbyarc : (Z.biUnion D).card ≤  R.card.choose 2*j := by
    calc
      (Z.biUnion D).card ≤  ∑ z ∈ Z, (D z).card := Finset.card_biUnion_le
      _ ≤  ∑ _z ∈ Z, j := Finset.sum_le_sum hD
      _ = Z.card*j := by simp
      _ ≤  S.card*j := Nat.mul_le_mul_right j Finset.card_image_le
      _ = R.card.choose 2*j := by rw [(guardArcs_card T label F hF t g hgt q x).2]
  have hbyhead : (Z.biUnion D).card ≤  (2*R.card)*j :=
    by_head_child_card R Z D j hhead hD
  rw [min_mul]
  exact le_min hbyarc hbyhead

theorem external_guard_cost (T : Tournament k) (label : Fin k → Fin k → Fin 2)
    (F : Fin n → (I → Bool) → Bool) (hF : NestedFamily F)
    (ta tb ga gb : Fin n) (ht : ta ≤  tb) (hg : gb ≤  ga) (hgbtb : gb ≤  tb)
    (q s j L : ℕ) (hjs : j ≤  s) (hs : BBound F gb ga s) (hj : BBound F gb tb j)
    (x : ((Fin k × Fin 2) × I) → Bool)
    (hx : tolerantFamily T label F ta ga q x = false)
    (hL : ((externalGuardArcs T label F tb gb q x).filter fun e =>
        e.2 ∉ positiveTargets T label F tb gb q x (by decide)).card+L ≤ 
      (externalGuardArcs T label F tb gb q x).card) :
    ((externalGuardCoordinates T label F tb gb q x).biUnion
      (fun z => childFlipsTo F gb false x z.1 z.2)).card ≤ 
      ((externalGuardArcs T label F tb gb q x).card-
        (L-(positiveTargets T label F tb gb q x (by decide)).card)-
        (crossedTargetHeads T label F tb gb q x).card)*s+
      (min (positiveTargets T label F tb gb q x (by decide)).card
        (L-(positiveTargets T label F tb gb q x (by decide)).card)+
        (crossedTargetHeads T label F tb gb q x).card)*j := by
  let Z := externalGuardCoordinates T label F tb gb q x
  let S := externalGuardArcs T label F tb gb q x
  let P := positiveTargets T label F tb gb q x (by decide)
  let D := fun z : Fin k × Fin 2 => childFlipsTo F gb false x z.1 z.2
  apply positive_union_charge Z (fun z => z.1 ∈ P)
    (fun z => F tb (recursiveChild x z.1 z.2) = false) D
    S.card ((S.filter fun e => e.2 ∉ P).card) L P.card
    (crossedTargetHeads T label F tb gb q x).card s j hjs
  · exact Finset.card_image_le
  · exact filter_image_card_le S (arcCoordinate label) (fun z => z.1 ∉ P)
  · exact hL
  · exact positive_coordinates_card P Z
  · exact positive_costly_coordinates_card T label F tb gb q x Z
  · exact crossedTargetHeads_cheap_card T label F tb gb q x
  · intro z hz
    obtain ⟨e,he,rfl⟩ := Finset.mem_image.mp hz
    have hweak := selected_guard_weak_true T label F hF ta tb ga gb ht hg q x hx e
      (Finset.mem_filter.mp he).1
    by_cases hc : F tb (recursiveChild x e.2 (label e.1 e.2)) = false
    · simpa [D,arcCoordinate,hc] using hs _ hweak
    · have hon : F tb (recursiveChild x e.2 (label e.1 e.2)) = true := by
        simpa only [Bool.not_eq_false] using hc
      simpa [D,arcCoordinate,hc] using hj _ hon

end ZT
end
end z37

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

section z58

set_option maxHeartbeats 8000000
noncomputable section
open scoped Classical BigOperators
open OAI.Paper320 Sensitivity2075 SensitivityQ SensitivityOrdinaryGuard
namespace ZT
variable {n k : ℕ} {I : Type} [Fintype I]



end ZT
end
end z58

section z59

set_option maxHeartbeats 5000000
namespace ZT









end ZT
end z59

section z60

set_option maxHeartbeats 8000000
noncomputable section
open scoped Classical BigOperators
open OAI.Paper320 Sensitivity2075 SensitivityQ
namespace ZT
variable {n k : ℕ} {I : Type} [Fintype I]





theorem ordinary_zero_candidate_cost (T : Tournament k) (label : Fin k → Fin k → Fin 2)
    (F : Fin n → (I → Bool) → Bool) (hF : NestedFamily F)
    (ta tb ga gb : Fin n) (ht : ta ≤  tb) (hg : gb ≤  ga) (hga : ga ≤  ta)
    (q a b s j : ℕ) (hjs : j ≤  s)
    (ha : PBound F gb ta tb a) (hb : ABound F gb tb b)
    (hs : BBound F gb ga s) (hj : BBound F gb tb j)
    (x : ((Fin k × Fin 2) × I) → Bool)
    (hx : tolerantFamily T label F ta ga q x = false) :
    (flipsTo (tolerantFamily T label F tb gb q) true x).card ≤ 
      candidateCost q (tolerantTargets T label F tb gb q x).card
        (positiveTargets T label F tb gb q x (by decide)).card
        (tolerantGuards T label F tb gb q x).card
        (crossedTargetHeads T label F tb gb q x).card a b s j := by
  let TC := tolerantTargets T label F tb gb q x
  let P := positiveTargets T label F tb gb q x (by decide)
  let G := tolerantGuards T label F tb gb q x
  let δ := (crossedTargetHeads T label F tb gb q x).card
  let E := G.card*(q+1)-G.card.choose 2
  let L := (P.card*G.card+P.card.choose 2)-q*P.card
  let intr := min (G.card.choose 2) (2*G.card)
  let X := (externalGuardCoordinates T label F tb gb q x).biUnion
    (fun z => childFlipsTo F gb false x z.1 z.2)
  let Y := ((internalGuardArcs T label F tb gb q x).image (arcCoordinate label)).biUnion
    (fun z => childFlipsTo F gb false x z.1 z.2)
  have hgt : gb ≤  tb := hg.trans (hga.trans ht)
  have hX : X.card ≤  (E-(L-P.card)-δ)*s+(min P.card (L-P.card)+δ)*j := by
    have hh := external_guard_cost T label F hF ta tb ga gb ht hg hgt q s j L
      hjs hs hj x hx (external_outside_positive_budget T label F hF tb gb hgt q x)
    rw [(guardArcs_card T label F hF tb gb hgt q x).1] at hh
    exact hh
  have hY : Y.card ≤  intr*j := internal_guard_cost T label F hF tb gb hgt q j hj x
  have hG : (guardRepairs T label F tb gb q x).card ≤ 
      (E-(L-P.card)-δ)*s+(intr+min P.card (L-P.card)+δ)*j := by
    have hh := (Finset.card_le_card (guardRepairs_subset_coordinates T label F tb gb q x)).trans
      ((Finset.card_union_le _ _).trans (Nat.add_le_add hX hY))
    simpa only [Nat.add_mul,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using hh
  have hT := targetRepairs_card T label F hF ta tb ga gb ht hg q q (le_refl q) a b ha hb x hx
  have hoff : tolerantFamily T label F tb gb q x = false := by
    cases hh : tolerantFamily T label F tb gb q x
    · rfl
    · have hw := family_nested T label F hF ht hg (le_refl q) x hh
      simp [hx] at hw
  have hh := (Finset.card_le_card (up_subset_repairs T label F tb gb q x hoff)).trans
    ((Finset.card_union_le _ _).trans (Nat.add_le_add hT hG))
  simpa only [candidateCost,Nat.add_assoc] using hh





end ZT
end
end z60

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

end ThreeBoundOrdinaryArchive

end
end Sensitivity213981Formal

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem solution :
∀ {n k : Nat} {I : Type} [inst : Fintype.{0} I]
  (T : Sensitivity213981Formal.ThreeBoundOrdinaryArchive.OAI.Paper320.Tournament k)
  (label : Fin k → Fin k → Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
  (F : Fin n → (I → Bool) → Bool)
  (hF : @Sensitivity213981Formal.ThreeBoundOrdinaryArchive.OAI.Paper320.NestedFamily n I F) (ta tb ga gb : Fin n)
  (ht : @LE.le.{0} (Fin n) (@instLEFin n) ta tb) (hg : @LE.le.{0} (Fin n) (@instLEFin n) gb ga)
  (hga : @LE.le.{0} (Fin n) (@instLEFin n) ga ta) (q a b s j : Nat) (hjs : @LE.le.{0} Nat instLENat j s)
  (ha : @Sensitivity213981Formal.ThreeBoundOrdinaryArchive.ZT.PBound I inst n F gb ta tb a)
  (hb : @Sensitivity213981Formal.ThreeBoundOrdinaryArchive.ZT.ABound I inst n F gb tb b)
  (hs : @Sensitivity213981Formal.ThreeBoundOrdinaryArchive.ZT.BBound I inst n F gb ga s)
  (hj : @Sensitivity213981Formal.ThreeBoundOrdinaryArchive.ZT.BBound I inst n F gb tb j)
  (x : Prod.{0, 0} (Prod.{0, 0} (Fin k) (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))) I → Bool)
  (hx :
    @Eq.{1} Bool
      (@Sensitivity213981Formal.ThreeBoundOrdinaryArchive.Sensitivity2075.tolerantFamily n k
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) I T label F ta ga q x)
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
    (Sensitivity213981Formal.ThreeBoundOrdinaryArchive.ZT.candidateCost q
      (@Finset.card.{0} (Fin k)
        (@Sensitivity213981Formal.ThreeBoundOrdinaryArchive.Sensitivity2075.tolerantTargets n k
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) I T label F tb gb q x))
      (@Finset.card.{0} (Fin k)
        (@Sensitivity213981Formal.ThreeBoundOrdinaryArchive.SensitivityQ.positiveTargets n k
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) I T label F tb gb q x
          (@of_decide_eq_true
            (@LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
            (Nat.decLt (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
            (@id.{0}
              (@Eq.{1} Bool
                (@Decidable.decide
                  (@LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                  (Nat.decLt (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                Bool.true)
              (@Eq.refl.{1} Bool Bool.true)))))
      (@Finset.card.{0} (Fin k)
        (@Sensitivity213981Formal.ThreeBoundOrdinaryArchive.Sensitivity2075.tolerantGuards n k
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) I T label F tb gb q x))
      (@Finset.card.{0} (Fin k)
        (@Sensitivity213981Formal.ThreeBoundOrdinaryArchive.ZT.crossedTargetHeads n k I T label F tb gb q x))
      a b s j) := @Sensitivity213981Formal.ThreeBoundOrdinaryArchive.ZT.ordinary_zero_candidate_cost
