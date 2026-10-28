-- Prove2me | solution 1 for ThreeBoundOrdinaryArchive.Paley11987Verified.CompactBooleanTransfer.candidateTotalCap_bound
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-25T22:45:58.780861+00:00
-- url     : https://prove2.me/submissions/facbd213-91eb-4573-a4bd-74030d21dd41

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
import Theorems.Thm_ThreeBoundOrdinaryArchive_CompactTournament_augment_by_guards
import Theorems.Thm_ThreeBoundOrdinaryArchive_OAI_Paper320_Tournament_card_internalEdges
import Theorems.Thm_ThreeBoundOrdinaryArchive_ZL_markedGood_mono
import Theorems.Thm_ThreeBoundOrdinaryArchive_ZT_candidates_markedGood

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





theorem adj_or_reverse {i j : Fin k} (h : i ≠ j) : T.Adj i j ∨ T.Adj j i := by
  by_cases hh : T.Adj j i
  · exact Or.inr hh
  · exact Or.inl ((T.edge_compl h).mpr hh)



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
    (x : ((Fin k × Fin r) × I) → Bool) (hr : 0 < r) (i : Fin k)
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
    (x : ((Fin k × Fin r) × I) → Bool) (hr : 0 < r) (i : Fin k)
    (hi : (missingTargets F A x i).card = 1) (c : Fin r)
    (hc : F A (recursiveChild x i c) = false) : c = missingWitness F A x hr i := by
  have hm := (mem_missingTargets F A x i c).mpr hc
  rwa [missing_singleton F A x hr i hi, Finset.mem_singleton] at hm

theorem missingWitness_other_true {n k r : ℕ} {I : Type}
    (F : Fin n → (I → Bool) → Bool) (A : Fin n)
    (x : ((Fin k × Fin r) × I) → Bool) (hr : 0 < r) (i : Fin k)
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

theorem positive_or_guard_full (T : Tournament k)
    (label : Fin k → Fin k → Fin 2) (F : Fin n → (I → Bool) → Bool)
    (hF : NestedFamily F) (t g : Fin n) (hgt : g ≤ t)
    (q : ℕ) (x : ((Fin k × Fin 2) × I) → Bool)
    (j : Fin k)
    (hj : j ∈ SensitivityQ.positiveTargets T label F t g q x (by decide) ∪
      tolerantGuards T label F t g q x) :
    ∀ c, F g (recursiveChild x j c) = true := by
  intro c
  rcases Finset.mem_union.mp hj with hp | hg
  · obtain ⟨hjt,hgate⟩ := Finset.mem_filter.mp hp
    by_cases hc : c = missingWitness F t x (by decide) j
    · simpa only [hc] using hgate
    · exact hF.accepts_of_le hgt
        (missingWitness_other_true F t x (by decide) j
          (Finset.mem_filter.mp hjt).2.1 c hc)
  · exact hF.accepts_of_le hgt
      ((missingTargets_empty F t x j).mp (Finset.mem_filter.mp hg).2.1 c)

theorem target_mismatch_failed (T : Tournament k)
    (label : Fin k → Fin k → Fin 2) (F : Fin n → (I → Bool) → Bool)
    (hF : NestedFamily F) (t g : Fin n) (hgt : g ≤ t)
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
    (hF : NestedFamily F) (t g : Fin n) (hgt : g ≤ t)
    (q : ℕ) (x : ((Fin k × Fin 2) × I) → Bool) :
    ZL.OrdinaryGood T.Adj (fun e => label e.1 e.2)
      (tolerantTargets T label F t g q x) q (missingWitness F t x (by decide)) := by
  intro i hi
  exact (Finset.card_le_card
    (target_mismatch_failed T label F hF t g hgt q x _ (fun _ h => h) i)).trans
    (Finset.mem_filter.mp hi).2.2

theorem candidate_local_charge (T : Tournament k)
    (label : Fin k → Fin k → Fin 2) (F : Fin n → (I → Bool) → Bool)
    (hF : NestedFamily F) (t g : Fin n) (hgt : g ≤ t)
    (q : ℕ) (x : ((Fin k × Fin 2) × I) → Bool)
    (A M : Finset (Fin k)) (hA : A ⊆ tolerantTargets T label F t g q x)
    (hM : M ⊆ SensitivityQ.positiveTargets T label F t g q x (by decide) ∪
      tolerantGuards T label F t g q x) (hdis : Disjoint A M) (i : Fin k) :
    (ZL.mismatch T.Adj (fun e => label e.1 e.2) A
      (missingWitness F t x (by decide)) i).card +
      (ZL.outOn T.Adj M i).card ≤ (failedGuards T label F g x i).card := by
  let D := ZL.mismatch T.Adj (fun e => label e.1 e.2) A
    (missingWitness F t x (by decide)) i
  let O := ZL.outOn T.Adj M i
  have hD : D ⊆ failedGuards T label F g x i :=
    target_mismatch_failed T label F hF t g hgt q x A hA i
  have hO : O ⊆ failedGuards T label F g x i := by
    intro j hj
    obtain ⟨hjM,hij⟩ := Finset.mem_filter.mp hj
    exact (mem_failedGuards T label F g x i j).mpr
      ⟨hij, positive_or_guard_full T label F hF t g hgt q x j (hM hjM) _⟩
  have hd : Disjoint D O := by
    apply Finset.disjoint_left.mpr
    intro j hjD hjO
    exact Finset.disjoint_left.mp hdis
      (Finset.mem_filter.mp hjD).1 (Finset.mem_filter.mp hjO).1
  calc
    D.card + O.card = (D ∪ O).card := (Finset.card_union_of_disjoint hd).symm
    _ ≤ (failedGuards T label F g x i).card :=
      Finset.card_le_card (Finset.union_subset hD hO)



theorem targets_card_of_exclusion (T : Tournament k)
    (label : Fin k → Fin k → Fin 2) (F : Fin n → (I → Bool) → Bool)
    (hF : NestedFamily F) (t g : Fin n) (hgt : g ≤ t)
    (q w : ℕ) (hd : SensitivityQ.DefectBound T label q w)
    (x : ((Fin k × Fin 2) × I) → Bool) :
    (tolerantTargets T label F t g q x).card < w := by
  exact hd _ _ (targets_ordinaryGood T label F hF t g hgt q x)

theorem targets_guards_card_of_exclusion (T : Tournament k)
    (label : Fin k → Fin k → Fin 2) (F : Fin n → (I → Bool) → Bool)
    (hF : NestedFamily F) (t g : Fin n) (hgt : g ≤ t)
    (q w : ℕ) (hd : SensitivityQ.DefectBound T label q w)
    (x : ((Fin k × Fin 2) × I) → Bool) :
    (tolerantTargets T label F t g q x).card +
      (tolerantGuards T label F t g q x).card ≤ w := by
  let C := tolerantTargets T label F t g q x
  let G := tolerantGuards T label F t g q x
  have hdis : Disjoint C G := target_guard_disjoint T label F t g q x
  have hcharge (i : Fin k) := candidate_local_charge T label F hF t g hgt q x C G
    (fun _ h => h) (fun _ h => Finset.mem_union_right _ h) hdis i
  obtain ⟨S,color,hcard,hgood⟩ := CompactTournament.augment_by_guards T.Adj
    (fun _ _ h => T.adj_or_reverse h) (fun e => label e.1 e.2) C G hdis q
    (missingWitness F t x (by decide))
    (fun i hi => (hcharge i).trans (Finset.mem_filter.mp hi).2.2)
    (fun i hi => (hcharge i).trans (Nat.le_of_eq (Finset.mem_filter.mp hi).2.2))
  have hs := hd S color hgood
  change C.card + G.card ≤ w
  omega

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





theorem candidate_marked_unrestricted (T : Tournament k) (label : Fin k → Fin k → Fin 2)
    (F : Fin n → (I → Bool) → Bool) (hF : NestedFamily F)
    (t g : Fin n) (hgt : g ≤ t) (q : ℕ)
    (x : ((Fin k × Fin 2) × I) → Bool) (A M P : Finset (Fin k))
    (hA : A ⊆ tolerantTargets T label F t g q x)
    (hM : M ⊆ positiveTargets T label F t g q x (by decide) ∪ tolerantGuards T label F t g q x)
    (hP : P ⊆ positiveTargets T label F t g q x (by decide)) (hdis : Disjoint A M) :
    MarkedGood T.Adj (fun e => label e.1 e.2) A M P q (M.card*(q+1))
      (missingWitness F t x (by decide)) := by
  apply candidates_markedGood T label F hF t g hgt q (M.card*(q+1)) x A M P hA hM hP hdis
  calc
    _ ≤ ∑ _v ∈ M, (q+1) := by
      apply Finset.sum_le_sum
      intro v hv
      have hsub := Finset.card_le_card (target_mismatch_failed T label F hF t g hgt q x A hA v)
      rcases Finset.mem_union.mp (hM hv) with hp | hg
      · have hh := (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).2.2
        omega
      · have hh := (Finset.mem_filter.mp hg).2.2
        omega
    _ = _ := by simp

theorem targets_card_guard_marked (T : Tournament k) (label : Fin k → Fin k → Fin 2)
    (F : Fin n → (I → Bool) → Bool) (hF : NestedFamily F)
    (t g : Fin n) (hgt : g ≤ t) (q r w : ℕ)
    (hcap : MarkedCardBound T label q r 0 (r*(q+1)) w)
    (x : ((Fin k × Fin 2) × I) → Bool)
    (hr : r ≤ (tolerantGuards T label F t g q x).card) :
    (tolerantTargets T label F t g q x).card < w := by
  obtain ⟨M,hM,hcard⟩ := Finset.exists_subset_card_eq hr
  let A := tolerantTargets T label F t g q x
  have hdis : Disjoint A M := (target_guard_disjoint T label F t g q x).mono_right hM
  have hg := candidate_marked_unrestricted T label F hF t g hgt q x A M ∅
    (Finset.Subset.refl _) (fun v hv => Finset.mem_union_right _ (hM hv)) (Finset.empty_subset _) hdis
  rw [hcard] at hg
  exact hcap A M ∅ _ hdis (Finset.empty_subset _) hcard rfl hg

theorem targets_card_positive_marked (T : Tournament k) (label : Fin k → Fin k → Fin 2)
    (F : Fin n → (I → Bool) → Bool) (hF : NestedFamily F)
    (t g : Fin n) (hgt : g ≤ t) (q r w : ℕ)
    (hcap : MarkedCardBound T label q r 0 (r*(q+1)) w)
    (x : ((Fin k × Fin 2) × I) → Bool)
    (hr : r ≤ (positiveTargets T label F t g q x (by decide)).card) :
    (tolerantTargets T label F t g q x).card < w+r := by
  obtain ⟨M,hM,hcard⟩ := Finset.exists_subset_card_eq hr
  let TC := tolerantTargets T label F t g q x
  let A := TC \ M
  have hMT : M ⊆ TC := hM.trans (Finset.filter_subset _ _)
  have hdis : Disjoint A M := Finset.sdiff_disjoint
  have hg := candidate_marked_unrestricted T label F hF t g hgt q x A M ∅
    Finset.sdiff_subset (fun v hv => Finset.mem_union_left _ (hM hv)) (Finset.empty_subset _) hdis
  rw [hcard] at hg
  have hc := hcap A M ∅ _ hdis (Finset.empty_subset _) hcard rfl hg
  have hs := Finset.card_sdiff_add_card_eq_card hMT
  change A.card+M.card=TC.card at hs
  change TC.card < _
  omega

theorem targets_card_three_positive_one (T : Tournament k) (label : Fin k → Fin k → Fin 2)
    (F : Fin n → (I → Bool) → Bool) (hF : NestedFamily F)
    (t g : Fin n) (hgt : g ≤ t) (w : ℕ)
    (hcap : MarkedCardBound T label 1 3 0 0 w)
    (x : ((Fin k × Fin 2) × I) → Bool)
    (hr : 3 ≤ (positiveTargets T label F t g 1 x (by decide)).card) :
    (tolerantTargets T label F t g 1 x).card < w+3 := by
  obtain ⟨M,hM,hcard⟩ := Finset.exists_subset_card_eq hr
  let TC := tolerantTargets T label F t g 1 x
  let A := TC \ M
  let color := missingWitness F t x (by decide)
  have hMT : M ⊆ TC := hM.trans (Finset.filter_subset _ _)
  have hdis : Disjoint A M := Finset.sdiff_disjoint
  have hg := candidate_marked_unrestricted T label F hF t g hgt 1 x A M M
    Finset.sdiff_subset (fun v hv => Finset.mem_union_left _ (hM hv)) hM hdis
  have hsum : (∑ y ∈ M, (outOn T.Adj M y).card)+
      (∑ y ∈ M, (mismatch T.Adj (fun e => label e.1 e.2) A color y).card) ≤ M.card := by
    rw [←Finset.sum_add_distrib]
    calc
      _ ≤ ∑ _y ∈ M, 1 := by
        apply Finset.sum_le_sum
        intro y hy
        simpa only [if_pos hy,Nat.add_zero] using hg.2.1 y hy
      _ = M.card := by simp
  have hi : (∑ y ∈ M, (outOn T.Adj M y).card) = 3 := by
    change (∑ y ∈ M, (M.filter (T.Adj y)).card)=3
    rw [T.sum_outdegree_eq,T.card_internalEdges,hcard]
    decide
  have hcross : (∑ y ∈ M, (mismatch T.Adj (fun e => label e.1 e.2) A color y).card) ≤ 0 := by
    rw [hi,hcard] at hsum
    omega
  have hg0 : MarkedGood T.Adj (fun e => label e.1 e.2) A M M 1 0 color :=
    ⟨hg.1,hg.2.1,hcross⟩
  have hgloose := markedGood_mono T.Adj (fun e => label e.1 e.2)
    A A M M ∅ (Finset.Subset.refl _) (Finset.empty_subset _) 1 0 0 (le_refl 0) color hg0
  have hc := hcap A M ∅ color hdis (Finset.empty_subset _) hcard rfl hgloose
  have hs := Finset.card_sdiff_add_card_eq_card hMT
  change A.card+M.card=TC.card at hs
  change TC.card < _
  omega







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
set_option maxHeartbeats 8000000
open scoped Classical BigOperators
open OAI.Paper320 Sensitivity2075 SensitivityQ
open ZP
namespace ThreeBoundOrdinaryArchive.ZT
end ThreeBoundOrdinaryArchive.ZT
open ThreeBoundOrdinaryArchive.ZT
variable {n k : ℕ} {I : Type} [Fintype I]

theorem solution (T : Tournament k) (label : Fin k → Fin k → Fin 2)
    (hCaps : LabelCaps T label) (F : Fin n → (I → Bool) → Bool) (hF : NestedFamily F)
    (t g : Fin n) (hgt : g ≤ t) (q : ℕ) (hq : 0 < q) (hq8 : q ≤ 8)
    (x : ((Fin k × Fin 2) × I) → Bool) :
    (tolerantTargets T label F t g q x).card ≤
      candidateTotalCap q (tolerantGuards T label F t g q x).card
        (positiveTargets T label F t g q x (by decide)).card := by
  let C := tolerantTargets T label F t g q x
  let G := tolerantGuards T label F t g q x
  let P := positiveTargets T label F t g q x (by decide)
  have hordinary := targets_card_of_exclusion T label F hF t g hgt q (cutoff q) (hCaps.ordinary q hq8) x
  change C.card < cutoff q at hordinary
  have hord : C.card ≤ cutoff q-1 := by omega
  have hg : C.card+G.card ≤ cutoff q := targets_guards_card_of_exclusion
    T label F hF t g hgt q (cutoff q) (hCaps.ordinary q hq8) x
  have hguard : 0 < G.card → C.card ≤ guardCap q := by
    intro hgn
    by_cases hq4 : q ≤ 4
    · have hc := targets_card_guard_marked T label F hF t g hgt q 1 (guardCap q+1)
        (by simpa using hCaps.one q hq hq4) x hgn
      change C.card < guardCap q+1 at hc
      omega
    · have hq5 : 5 ≤ q := by omega
      have he : guardCap q = cutoff q-1 := by interval_cases q <;> decide
      rw [he]
      exact hord
  have hpositive : 0 < P.card → C.card ≤ targetCap q := by
    intro hpn
    by_cases hq4 : q ≤ 4
    · have hc := targets_card_positive_marked T label F hF t g hgt q 1 (guardCap q+1)
        (by simpa using hCaps.one q hq hq4) x hpn
      change C.card < (guardCap q+1)+1 at hc
      have he : targetCap q = guardCap q+1 := by interval_cases q <;> decide
      rw [he]
      omega
    · have hq5 : 5 ≤ q := by omega
      have he : targetCap q = cutoff q-1 := by interval_cases q <;> decide
      rw [he]
      exact hord
  have hu2 : q=1 ∧ 2 ≤ P.card → C.card ≤ 28 := by
    rintro ⟨rfl,hp⟩
    have hc := targets_card_positive_marked T label F hF t g hgt 1 2 27 hCaps.two_one x hp
    change C.card < 27+2 at hc
    omega
  have hu3 : q=1 ∧ 3 ≤ P.card → C.card ≤ 26 := by
    rintro ⟨rfl,hp⟩
    have hc := targets_card_three_positive_one T label F hF t g hgt 24 hCaps.zero_one_three x hp
    change C.card < 24+3 at hc
    omega
  have hg2 : q=1 ∧ 2 ≤ G.card → C.card ≤ 26 := by
    rintro ⟨rfl,hg⟩
    have hc := targets_card_guard_marked T label F hF t g hgt 1 2 27 hCaps.two_one x hg
    change C.card < 27 at hc
    omega
  have hg22 : q=2 ∧ 2 ≤ G.card → C.card ≤ 33 := by
    rintro ⟨rfl,hg⟩
    have hc := targets_card_guard_marked T label F hF t g hgt 2 2 34 hCaps.two_two x hg
    change C.card < 34 at hc
    omega
  let base := if G.card > 0 then min (cutoff q-G.card) (guardCap q) else cutoff q-1
  have hb : C.card ≤ base := by
    dsimp [base]
    split_ifs with hgn
    · exact le_min (by omega) (hguard hgn)
    · exact hord
  let pp := if P.card > 0 then min base (targetCap q) else base
  have hp : C.card ≤ pp := by
    dsimp [pp]
    split_ifs with hpn
    · exact le_min hb (hpositive hpn)
    · exact hb
  let pp2 := if q=1 ∧ P.card≥2 then min pp 28 else pp
  have hp2 : C.card ≤ pp2 := by
    dsimp [pp2]
    split_ifs with h
    · exact le_min hp (hu2 h)
    · exact hp
  let pp3 := if q=1 ∧ P.card≥3 then min pp2 26 else pp2
  have hp3 : C.card ≤ pp3 := by
    dsimp [pp3]
    split_ifs with h
    · exact le_min hp2 (hu3 h)
    · exact hp2
  let gg2 := if q=1 ∧ G.card≥2 then min pp3 26 else pp3
  have hgg2 : C.card ≤ gg2 := by
    dsimp [gg2]
    split_ifs with h
    · exact le_min hp3 (hg2 h)
    · exact hp3
  change C.card ≤ if q=2 ∧ G.card≥2 then min gg2 33 else gg2
  split_ifs with h
  · exact le_min hgg2 (hg22 h)
  · exact hgg2
end
