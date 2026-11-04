-- Prove2me | solution 1 for ThreeSum.RawIncidences.dense_early_yes_w3sum_ac885d1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:47:44.41878+00:00
-- url     : https://prove2.me/submissions/5360e45f-6afb-4959-bad9-213e66a06844

import Definitions.Def_Submission_ThreeSum_GlobalEncoding
import Definitions.Def_Submission_ThreeSum_Arithmetic
import Definitions.Def_Submission_ThreeSum_Histograms
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Tactic.FinCases
import Definitions.Def_Submission_ThreeSum_RawIncidences
import Theorems.Thm_ThreeSum_RawIncidences_mem_rawOn
import Theorems.Thm_ThreeSum_RawIncidences_raw_sound
import Theorems.Thm_ThreeSum_RawIncidences_raw_owner_weight_bound
import Definitions.Def_WeightedCache3SUM_Alias_695584d03436af82
import Theorems.Thm_ThreeSum_Arithmetic_falseCount_le_weightedFalseCount
import Theorems.Thm_ThreeSum_Arithmetic_missWeight_zero
import Theorems.Thm_ThreeSum_HashFamily_hashMap_apply
import Theorems.Thm_ThreeSum_LayerCounts_mem_edgeSet
import Theorems.Thm_ThreeSum_LayerCounts_mem_vertices
attribute [local simp] ThreeSum.Arithmetic.missWeight_zero
attribute [local simp] ThreeSum.HashFamily.hashMap_apply
attribute [local simp] ThreeSum.LayerCounts.mem_edgeSet
attribute [local simp] ThreeSum.LayerCounts.mem_vertices



set_option autoImplicit false
open ThreeSum ThreeSum.RawIncidences
set_option maxRecDepth 8000
open Finset
open scoped BigOperators
open GlobalEncoding LocalCoverBounds
variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]
namespace ThreeSum.RawIncidences
theorem _root_.solution {h J : ℕ} {P d : ℤ} (T : Finset (Original α β γ))
    (a : α → ℤ) (b : β → ℤ) (c : γ → ℤ) (aux : Finset ℤ)
    (hP : 0 < P) (hguard : 4 * P ≤ globalModulus h J)
    (hsep : ∀ t ∈ T, difference a b c t ≠ 0 → ∃ l ∈ aux, ¬l ∣ difference a b c t)
    (hlarge : representationCap h J * Arithmetic.weightedFalseCount T (difference a b c) aux P <
      rawMass h J P d T a b c) :
    ∃ t ∈ T, difference a b c t = 0 := by
  let good : Original α β γ → Prop :=
    fun t => t ∉ T ∨ ¬P ∣ difference a b c t ∨ difference a b c t = 0
  have hset : (Finset.univ.filter fun t : Original α β γ => ¬good t) =
      T.filter (fun t => P ∣ difference a b c t ∧ difference a b c t ≠ 0) := by
    ext t
    simp [good]
  have hcount : (Finset.univ.filter fun t : Original α β γ => ¬good t).card ≤
      Arithmetic.weightedFalseCount T (difference a b c) aux P := by
    rw [hset, Finset.card_eq_sum_ones, Finset.sum_filter]
    exact Arithmetic.falseCount_le_weightedFalseCount T (difference a b c) aux P hsep
  have hmass : representationCap h J * Arithmetic.weightedFalseCount T (difference a b c) aux P <
      ∑ _r ∈ rawOn h J P d T a b c, (1 : ℕ) := by
    simpa only [Finset.sum_const, smul_eq_mul, mul_one, rawMass] using hlarge
  obtain ⟨r, hr, _, hg⟩ := Arithmetic.early_yes
    (rawOn h J P d T a b c) Sigma.fst (fun _ => 1) good
    (representationCap h J) (Arithmetic.weightedFalseCount T (difference a b c) aux P)
    (fun t _ => raw_owner_weight_bound T a b c hP hguard t) hcount hmass
  have ht := (mem_rawOn.mp hr).1
  have hd := raw_sound hP hguard hr
  refine ⟨r.1, ht, ?_⟩
  rcases hg with hnot | hnot | hz
  · exact False.elim (hnot ht)
  · exact False.elim (hnot hd)
  · exact hz
end ThreeSum.RawIncidences
