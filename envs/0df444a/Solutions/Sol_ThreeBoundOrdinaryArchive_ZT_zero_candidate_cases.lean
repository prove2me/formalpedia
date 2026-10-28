-- Prove2me | solution 1 for ThreeBoundOrdinaryArchive.ZT.zero_candidate_cases
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-25T22:38:09.788252+00:00
-- url     : https://prove2.me/submissions/7b474381-b7f7-46a6-9538-f9f0f86ff264

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
namespace ThreeBoundOrdinaryArchive.SensitivityOrdinaryGuard
end ThreeBoundOrdinaryArchive.SensitivityOrdinaryGuard
namespace ThreeBoundOrdinaryArchive.SensitivityQ
end ThreeBoundOrdinaryArchive.SensitivityQ
namespace ThreeBoundOrdinaryArchive.SensitivitySourceZero
end ThreeBoundOrdinaryArchive.SensitivitySourceZero
namespace ThreeBoundOrdinaryArchive.ZL
end ThreeBoundOrdinaryArchive.ZL
section
/- Adapted complete accepted Apache-2.0 Prove2me proofs by @yousofy. See ordinary_provenance.json. -/


open OAI.Paper320
namespace ThreeBoundOrdinaryArchive

/- Sol_Paley11987Verified_CompactBooleanTransfer_ordinary_zero_tolerance.lean -/
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
variable {n k r : ℕ} {I : Type} (T : Tournament k)
  (label : Fin k → Fin k → Fin r) (F : Fin n → (I → Bool) → Bool)
  (hF : NestedFamily F) (Ai Aj Gi Gj : Fin n)
  (hA : Ai ≤ Aj) (hG : Gj ≤ Gi)
  (x : ((Fin k × Fin r) × I) → Bool)



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
variable {n k r : ℕ} {I : Type}





















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

section z42

set_option maxHeartbeats 3000000
noncomputable section
open scoped Classical BigOperators
open OAI.Paper320 ZL

namespace ZT
variable {k : ℕ}









end ZT
end
end z42

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

section z62

set_option maxHeartbeats 5000000
namespace ZT



theorem zeroCost_lower (a b s j d : ℕ) :
    22*b ≤ zeroCost a b s j d ∧ a+19*b ≤ zeroCost a b s j d ∧
    17*b+max (min (a+s) d) (a+j) ≤ zeroCost a b s j d ∧
    19*b+s ≤ zeroCost a b s j d ∧ 20*b+j ≤ zeroCost a b s j d ∧
    17*b+s+j ≤ zeroCost a b s j d ∧ 18*b+2*j ≤ zeroCost a b s j d ∧
    17*b+3*j ≤ zeroCost a b s j d := by unfold zeroCost; omega





end ZT
end z62

section z63

set_option maxHeartbeats 8000000
noncomputable section
open scoped Classical BigOperators
open OAI.Paper320 Sensitivity2075 SensitivityQ SensitivitySourceZero
namespace ZT
variable {n k : ℕ} {I : Type} [Fintype I]





end ZT
end
end z63

section z64

set_option maxHeartbeats 8000000
noncomputable section
open scoped Classical BigOperators
open OAI.Paper320 Sensitivity2075 SensitivityQ
namespace ZT
variable {n k : ℕ} {I : Type} [Fintype I]





end ZT
end
end z64

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
namespace ThreeBoundOrdinaryArchive.ZT
end ThreeBoundOrdinaryArchive.ZT
open ThreeBoundOrdinaryArchive.ZT

theorem solution (z t u m δ a b s j d : ℕ)
    (hu : u ≤ 1) (hm : m ≤ 3) (hc : (u+m).choose 2 ≤ m)
    (ht : t ≤ 22)
    (hδ : δ+((u*m+u.choose 2)-0*u) ≤ m*(0+1)-m.choose 2)
    (hsource : 1 ≤ u+m → t-u ≤ 19+δ)
    (hdouble : 2 ≤ u+m → t-u ≤ 17+δ)
    (hraw : z ≤ candidateCost 0 t u m δ a b s j)
    (hshared : u=1 → m=1 → z ≤ (t-1)*b+max (min (a+s) d) (a+j)) :
    z ≤ zeroCost a b s j d := by
  obtain ⟨h0,h1,h2,h3,h4,h5,h6,h7⟩ := zeroCost_lower a b s j d
  interval_cases u
  · interval_cases m
    · have hd : δ=0 := by norm_num at hδ; omega
      subst δ
      norm_num [candidateCost] at hraw
      exact (hraw.trans (Nat.mul_le_mul_right b ht)).trans h0
    · have hd : δ ≤ 1 := by norm_num at hδ; exact hδ
      have hs := hsource (by decide)
      norm_num at hs
      interval_cases δ
      · norm_num [candidateCost] at hraw
        have hb := Nat.mul_le_mul_right b hs
        exact (by omega : z ≤ 19*b+s).trans h3
      · norm_num [candidateCost] at hraw
        have hb := Nat.mul_le_mul_right b hs
        exact (by omega : z ≤ 20*b+j).trans h4
    · have hd : δ ≤ 1 := by norm_num at hδ; exact hδ
      have hs := hdouble (by decide)
      norm_num at hs
      interval_cases δ
      · norm_num [candidateCost] at hraw
        have hb := Nat.mul_le_mul_right b hs
        exact (by omega : z ≤ 17*b+s+j).trans h5
      · norm_num [candidateCost] at hraw
        have hb := Nat.mul_le_mul_right b hs
        exact (by omega : z ≤ 18*b+2*j).trans h6
    · have hd : δ=0 := by norm_num at hδ; omega
      subst δ
      have hs := hdouble (by decide)
      norm_num at hs
      norm_num [candidateCost] at hraw
      have hb := Nat.mul_le_mul_right b hs
      exact (by omega : z ≤ 17*b+3*j).trans h7
  · interval_cases m
    · have hd : δ=0 := by norm_num at hδ; omega
      subst δ
      have hs : t-1 ≤ 19 := by simpa only [Nat.add_zero] using hsource (by decide)
      norm_num [candidateCost] at hraw
      have hb := Nat.mul_le_mul_right b hs
      exact (by omega : z ≤ a+19*b).trans h1
    · have hd : δ=0 := by norm_num at hδ; omega
      subst δ
      have hs : t-1 ≤ 17 := by simpa only [Nat.add_zero] using hdouble (by decide)
      have hr := hshared rfl rfl
      have hb := Nat.mul_le_mul_right b hs
      exact (by omega : z ≤ 17*b+max (min (a+s) d) (a+j)).trans h2
    · norm_num [Nat.choose] at hc
    · norm_num [Nat.choose] at hc
end
