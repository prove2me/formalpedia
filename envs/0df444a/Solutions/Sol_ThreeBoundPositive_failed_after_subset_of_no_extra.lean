-- Prove2me | solution 1 for ThreeBoundPositive.failed_after_subset_of_no_extra
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-25T22:40:14.29475+00:00
-- url     : https://prove2.me/submissions/35df01e3-2539-4944-b4c9-b10365eb62a5

import Definitions.Def_SensitivityCampaign
import Definitions.Def_SensitivitySeparation
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Union
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Prod
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Definitions.Def_Sensitivity213303_GradedPositiveBoundary
import Definitions.Def_Sensitivity213303_ProfileClosures
import Definitions.Def_Sensitivity213303_RecursiveLowerBounds
import Definitions.Def_Sensitivity213303_WitnessLifting

namespace OAI.Paper320
end OAI.Paper320
namespace ThreeBoundProfiles
end ThreeBoundProfiles
namespace ThreeBoundWitness
end ThreeBoundWitness
namespace OAI.Paper320
end OAI.Paper320
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





























theorem child_flip_same (x : ((V × Bool) × I) → Bool) (v : V) (c : Bool) (i : I) :
    child (flip x {((v,c),i)}) v c = flip (child x v c) {i} := by
  classical
  funext a
  simp [child, OAI.Paper320.flip]

theorem child_flip_other (x : ((V × Bool) × I) → Bool)
    (v w : V) (c e : Bool) (i : I) (h : (w,e) ≠ (v,c)) :
    child (flip x {((v,c),i)}) w e = child x w e := by
  classical
  funext a
  have hh : ((w,e),a) ≠ ((v,c),i) := by
    intro he
    exact h (congrArg Prod.fst he)
  simp [child, OAI.Paper320.flip, hh]

























/- Reindexing lemmas follow the accepted Apache-2.0 source by @yousofy:
   Sol_Paley11987Verified_CompactFiniteProfile11987_actual_seeds_of_label_and_certificate,
   together with Definitions.Def_Paley11987Support_053. -/










end ThreeBoundWitness








end

section
set_option autoImplicit false
set_option maxHeartbeats 2500000
set_option linter.unusedSectionVars false
namespace ThreeBoundPositive
end ThreeBoundPositive
open ThreeBoundPositive
open OAI.Paper320 ThreeBoundWitness ThreeBoundProfiles
open scoped BigOperators Classical
variable {L I V : Type} [Preorder L] [Fintype I] [Fintype V]

/-- If no previously passing guard is activated, the old strong count suffices. -/
theorem solution (S : Stage L I V) (F : L → (I → Bool) → Bool)
    (hF : Nested F) (i j : L) (hg : S.guard j ≤ S.guard i)
    (x : ((V × Bool) × I) → Bool) (v w : V) (c : Bool) (a : I)
    (he : ¬ ExtraFailure S F i j x v w c a) :
    failed S F i (flip x {((w,c),a)}) v ⊆ failed S F j x v := by
  classical
  intro z hz
  rcases Finset.mem_filter.mp hz with ⟨_, hR, hf⟩
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, hR, ?_⟩
  by_cases hp : (z, S.label v z) = (w,c)
  · have hzw : z = w := congrArg Prod.fst hp
    have hl : S.label v z = c := congrArg Prod.snd hp
    subst z
    rw [hl, child_flip_same] at hf
    cases hb : F (S.guard j) (child x w c) with
    | true => simpa only [hl] using hb
    | false => exact False.elim (he ⟨hR, hl, hb, hf⟩)
  · rw [child_flip_other x w z c (S.label v z) a hp] at hf
    exact hF _ _ hg _ hf
end
