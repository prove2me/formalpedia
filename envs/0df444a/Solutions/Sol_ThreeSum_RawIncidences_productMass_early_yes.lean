-- Prove2me | solution 1 for ThreeSum.RawIncidences.productMass_early_yes
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:25:20.049448+00:00
-- url     : https://prove2.me/submissions/edbf115c-b167-4420-8a67-a49325f122b0

import Definitions.Def_Submission_ThreeSum_GlobalEncoding
import Definitions.Def_Submission_ThreeSum_Arithmetic
import Definitions.Def_Submission_ThreeSum_Histograms
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Tactic.FinCases
import Definitions.Def_Submission_ThreeSum_RawIncidences
import Theorems.Thm_ThreeSum_RawIncidences_rawMass_eq_productMass
import Definitions.Def_WeightedCache3SUM_Alias_77565573dc2a8798
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
theorem _root_.solution {h J : ℕ} {P d : ℤ}
    (A : Finset α) (B : Finset β) (C : Finset γ)
    (a : α → ℤ) (b : β → ℤ) (c : γ → ℤ) (aux : Finset ℤ)
    (hP : 0 < P) (hguard : 4 * P ≤ globalModulus h J)
    (hsep : ∀ t ∈ A ×ˢ (B ×ˢ C), difference a b c t ≠ 0 →
      ∃ l ∈ aux, ¬l ∣ difference a b c t)
    (hlarge : representationCap h J *
      Arithmetic.weightedFalseCount (A ×ˢ (B ×ˢ C)) (difference a b c) aux P <
        productMass h J P d A B C a b c) :
    ∃ i ∈ A, ∃ j ∈ B, ∃ k ∈ C, a i + b j = c k := by
  have hm : representationCap h J *
      Arithmetic.weightedFalseCount (A ×ˢ (B ×ˢ C)) (difference a b c) aux P <
        rawMass h J P d (A ×ˢ (B ×ˢ C)) a b c := by
    simpa only [rawMass_eq_productMass] using hlarge
  obtain ⟨t, ht, he⟩ := dense_early_yes (A ×ˢ (B ×ˢ C)) a b c aux hP hguard hsep hm
  obtain ⟨ha, hb, hc⟩ := by simpa only [Finset.mem_product] using ht
  refine ⟨t.1, ha, t.2.1, hb, t.2.2, hc, ?_⟩
  unfold difference at he
  omega
end ThreeSum.RawIncidences
