-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Independent1.P05.clusterSeparation
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T21:05:09.384529+00:00
-- url     : https://prove2.me/submissions/fb002ab9-ffe3-4746-999c-7babd34131b9

import Mathlib
import Definitions.Def_QAlgorithms_Defs_NLTSPreparationCircuits
import Definitions.Def_QAlgorithms_Defs_Measurement
import Definitions.Def_QAlgorithms_Papers_Independent_Independent1_P05_Model
set_option autoImplicit false

/-! Statements from Anshu--Breuckmann--Nirkhe, arXiv:2206.13228v4.
Theorem 5 and three construction-specific expansion claims are deferred in HARD.md.
All new definitions are specific to this paper. -/

noncomputable section

open scoped Matrix ComplexOrder

attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

open QAlgorithms QAlgorithms.Papers QAlgorithms.Papers.Independent QAlgorithms.Papers.Independent.Independent1 QAlgorithms.Papers.Independent.Independent1.P05
open PresentedCSS

/-- Section 2, PDF p.4: computed equivalence classes partition the approximate words
and are separated. Strict 2*eps1<delta0 is the actual Property-1 domain on p.2. -/
theorem gk_hn_add {n : ℕ} (x y : Fin n → ZMod 2) :
    hammingNorm (x + y) ≤ hammingNorm x + hammingNorm y := by
  unfold hammingNorm
  calc (Finset.univ.filter fun i => (x + y) i ≠ 0).card
      ≤ ((Finset.univ.filter fun i => x i ≠ 0) ∪ (Finset.univ.filter fun i => y i ≠ 0)).card := by
        apply Finset.card_le_card
        intro i hi
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union,
          Pi.add_apply] at hi ⊢
        by_contra h
        push_neg at h
        rw [h.1, h.2, add_zero] at hi
        exact hi rfl
    _ ≤ _ := Finset.card_union_le _ _

theorem gk_red_spec {n : ℕ} (S : Submodule (ZMod 2) (Fin n → ZMod 2)) (a : Fin n → ZMod 2) :
    ∃ s ∈ S, NLTS.reducedHammingWeight S a = hammingNorm (a + s) := by
  unfold NLTS.reducedHammingWeight
  obtain ⟨s, _, hs⟩ := Finset.exists_mem_eq_inf' (Finset.univ_nonempty_iff.mpr ⟨(0 : S)⟩)
    (fun s : S => hammingNorm (a + (s : Fin n → ZMod 2)))
  exact ⟨s, s.2, hs⟩

theorem gk_red_le {n : ℕ} (S : Submodule (ZMod 2) (Fin n → ZMod 2)) (a s : Fin n → ZMod 2)
    (hs : s ∈ S) : NLTS.reducedHammingWeight S a ≤ hammingNorm (a + s) := by
  unfold NLTS.reducedHammingWeight
  exact Finset.inf'_le (fun s : S => hammingNorm (a + (s : Fin n → ZMod 2)))
    (Finset.mem_univ (⟨s, hs⟩ : S))

theorem gk_red_add {n : ℕ} (S : Submodule (ZMod 2) (Fin n → ZMod 2)) (a b : Fin n → ZMod 2) :
    NLTS.reducedHammingWeight S (a + b) ≤
      NLTS.reducedHammingWeight S a + NLTS.reducedHammingWeight S b := by
  obtain ⟨s1, h1, e1⟩ := gk_red_spec S a
  obtain ⟨s2, h2, e2⟩ := gk_red_spec S b
  calc NLTS.reducedHammingWeight S (a + b) ≤ hammingNorm (a + b + (s1 + s2)) :=
        gk_red_le S _ _ (S.add_mem h1 h2)
    _ = hammingNorm ((a + s1) + (b + s2)) := by congr 1; abel
    _ ≤ _ := by rw [e1, e2]; exact gk_hn_add _ _

theorem gk_red_n {n : ℕ} (S : Submodule (ZMod 2) (Fin n → ZMod 2)) (a : Fin n → ZMod 2) :
    NLTS.reducedHammingWeight S a ≤ n := by
  have := gk_red_le S a 0 S.zero_mem
  rw [add_zero] at this
  have h2 : hammingNorm a ≤ Fintype.card (Fin n) := hammingNorm_le_card_fintype
  simp at h2
  omega

theorem solution {n mx mz : ℕ} (C : CheckPresentation n mx mz)
    (c1 c2 delta0 eps1 : ℝ) (hcluster : NLTS.ClustersApproximateCodewords C c1 c2 delta0)
    (heps : 0 ≤ eps1) (hdomain : 2*eps1 < delta0) (hsmall : 4*c1*eps1 < c2) :
    ∀ had : Bool,
      Equivalence (fun x y : {y : NLTSWord n // y ∈ nltsApprox C had eps1} =>
        nltsRelated C c1 eps1 had x.val y.val) ∧
      nltsClusterUnion (nltsClasses C c1 eps1 had) = nltsApprox C had eps1 ∧
      (∀ B ∈ nltsClasses C c1 eps1 had, B.Nonempty) ∧
      ∀ B ∈ nltsClasses C c1 eps1 had, ∀ B2 ∈ nltsClasses C c1 eps1 had, B ≠ B2 →
        Disjoint B B2 ∧ ∀ x ∈ B, ∀ y ∈ B2, c2*n ≤ (hammingDist x y : ℝ) := by
  obtain ⟨hc1, hc2, hd0, hcl⟩ := hcluster
  intro had
  have hdich : ∀ x y, x ∈ nltsApprox C had eps1 → y ∈ nltsApprox C had eps1 →
      (NLTS.reducedHammingWeight (nltsOppositeDual C had) (x+y) : ℝ) ≤ 2*c1*eps1*n ∨
      c2*n ≤ (NLTS.reducedHammingWeight (nltsOppositeDual C had) (x+y) : ℝ) := by
    intro x y hx hy
    have h2 : (0:ℝ) ≤ 2*eps1 := by linarith
    cases had
    · simp only [nltsApprox, Bool.false_eq_true, if_false, Finset.mem_filter,
        Finset.mem_univ, true_and] at hx hy
      have hm : (x + y) ∈ NLTS.approximateCodewords C.HZ (2*eps1) h2 := by
        show (hammingNorm (C.HZ.mulVec (x+y)) : ℝ) ≤ 2*eps1*mz
        rw [Matrix.mulVec_add]
        have := gk_hn_add (C.HZ.mulVec x) (C.HZ.mulVec y)
        have : (hammingNorm (C.HZ.mulVec x + C.HZ.mulVec y) : ℝ) ≤
          hammingNorm (C.HZ.mulVec x) + hammingNorm (C.HZ.mulVec y) := by exact_mod_cast this
        linarith
      have := ((hcl (2*eps1) h2 hdomain (x+y)).1 hm)
      show (NLTS.reducedHammingWeight (codeDual C.Cx) (x+y) : ℝ) ≤ 2*c1*eps1*n ∨ _
      rcases this with h | h
      · left; linarith
      · right; exact h
    · simp only [nltsApprox, if_true, Finset.mem_filter,
        Finset.mem_univ, true_and] at hx hy
      have hm : (x + y) ∈ NLTS.approximateCodewords C.HX (2*eps1) h2 := by
        show (hammingNorm (C.HX.mulVec (x+y)) : ℝ) ≤ 2*eps1*mx
        rw [Matrix.mulVec_add]
        have := gk_hn_add (C.HX.mulVec x) (C.HX.mulVec y)
        have : (hammingNorm (C.HX.mulVec x + C.HX.mulVec y) : ℝ) ≤
          hammingNorm (C.HX.mulVec x) + hammingNorm (C.HX.mulVec y) := by exact_mod_cast this
        linarith
      have := ((hcl (2*eps1) h2 hdomain (x+y)).2 hm)
      show (NLTS.reducedHammingWeight (codeDual C.Cz) (x+y) : ℝ) ≤ 2*c1*eps1*n ∨ _
      rcases this with h | h
      · left; linarith
      · right; exact h
  set S := nltsOppositeDual C had with hS
  have hrefl : ∀ x, nltsRelated C c1 eps1 had x x := by
    intro x
    show (NLTS.reducedHammingWeight S (x+x) : ℝ) ≤ 2*c1*eps1*n
    have : x + x = 0 := by ext i; simp [ZModModule.add_self]
    rw [this]
    have := gk_red_le S 0 0 S.zero_mem
    simp only [add_zero, hammingNorm_zero, nonpos_iff_eq_zero] at this
    rw [this]; simp only [Nat.cast_zero]; positivity
  have hsymm : ∀ x y, nltsRelated C c1 eps1 had x y → nltsRelated C c1 eps1 had y x := by
    intro x y h
    show (NLTS.reducedHammingWeight S (y+x) : ℝ) ≤ 2*c1*eps1*n
    rw [add_comm]; exact h
  have htrans : ∀ x y z, x ∈ nltsApprox C had eps1 → z ∈ nltsApprox C had eps1 →
      nltsRelated C c1 eps1 had x y → nltsRelated C c1 eps1 had y z →
      nltsRelated C c1 eps1 had x z := by
    intro x y z hx hz h1 h2
    unfold nltsRelated at h1 h2 ⊢
    have e : x + z = (x + y) + (y + z) := by
      have : y + y = 0 := by ext i; simp [ZModModule.add_self]
      calc x + z = x + (y + y) + z := by rw [this, add_zero]
        _ = _ := by abel
    have ht := gk_red_add S (x+y) (y+z)
    rw [← e] at ht
    have ht' : (NLTS.reducedHammingWeight S (x+z) : ℝ) ≤ 4*c1*eps1*n := by
      have : (NLTS.reducedHammingWeight S (x+z) : ℝ) ≤
        NLTS.reducedHammingWeight S (x+y) + NLTS.reducedHammingWeight S (y+z) := by
        exact_mod_cast ht
      linarith
    rcases hdich x z hx hz with h | h
    · exact h
    · have hn : (n:ℝ) = 0 := by
        have : (c2 - 4*c1*eps1) * n ≤ 0 := by linarith
        have hn0 : (0:ℝ) ≤ n := by positivity
        nlinarith
      have := gk_red_n S (x+z)
      have : (NLTS.reducedHammingWeight S (x+z) : ℝ) ≤ n := by exact_mod_cast this
      rw [hn] at this ⊢; simpa using this
  have hmem : ∀ x y, y ∈ nltsClass C c1 eps1 had x ↔
      y ∈ nltsApprox C had eps1 ∧ nltsRelated C c1 eps1 had x y := by
    intro x y; simp [nltsClass]
  have hceq : ∀ x y, x ∈ nltsApprox C had eps1 → y ∈ nltsApprox C had eps1 →
      nltsRelated C c1 eps1 had x y → nltsClass C c1 eps1 had x = nltsClass C c1 eps1 had y := by
    intro x y hx hy h
    ext z
    rw [hmem, hmem]
    constructor
    · rintro ⟨hz, h2⟩; exact ⟨hz, htrans y x z hy hz (hsymm x y h) h2⟩
    · rintro ⟨hz, h2⟩; exact ⟨hz, htrans x y z hx hz h h2⟩
  refine ⟨⟨fun x => hrefl x.val, fun h => hsymm _ _ h,
    fun {x y z} h1 h2 => htrans x.val y.val z.val x.2 z.2 h1 h2⟩, ?_, ?_, ?_⟩
  · ext z
    simp only [nltsClusterUnion, nltsClasses, Finset.mem_biUnion, Finset.mem_image, id]
    constructor
    · rintro ⟨B, ⟨x, hx, rfl⟩, hz⟩
      exact ((hmem x z).1 hz).1
    · intro hz
      exact ⟨_, ⟨z, hz, rfl⟩, (hmem z z).2 ⟨hz, hrefl z⟩⟩
  · intro B hB
    simp only [nltsClasses, Finset.mem_image] at hB
    obtain ⟨x, hx, rfl⟩ := hB
    exact ⟨x, (hmem x x).2 ⟨hx, hrefl x⟩⟩
  · intro B hB B2 hB2 hne
    simp only [nltsClasses, Finset.mem_image] at hB hB2
    obtain ⟨x, hx, rfl⟩ := hB
    obtain ⟨y, hy, rfl⟩ := hB2
    have hnr : ¬ nltsRelated C c1 eps1 had x y := fun h => hne (hceq x y hx hy h)
    refine ⟨?_, ?_⟩
    · rw [Finset.disjoint_left]
      intro z hz1 hz2
      rw [hmem] at hz1 hz2
      exact hnr (htrans x z y hx hy hz1.2 (hsymm _ _ hz2.2))
    · intro u hu v hv
      rw [hmem] at hu hv
      have huv : ¬ nltsRelated C c1 eps1 had u v := by
        intro h
        exact hnr (htrans x u y hx hy hu.2 (htrans u v y hu.1 hy h (hsymm _ _ hv.2)))
      rcases hdich u v hu.1 hv.1 with h | h
      · exact absurd h huv
      · have h1 := gk_red_le S (u+v) 0 S.zero_mem
        rw [add_zero] at h1
        have h2 : hammingDist u v = hammingNorm (u + v) := by
          rw [hammingDist_eq_hammingNorm]
          congr 1
          ext i; simp [sub_eq_add_neg, ZModModule.neg_eq_self]
        rw [h2]
        have : (NLTS.reducedHammingWeight S (u+v) : ℝ) ≤ hammingNorm (u+v) := by
          exact_mod_cast h1
        linarith

