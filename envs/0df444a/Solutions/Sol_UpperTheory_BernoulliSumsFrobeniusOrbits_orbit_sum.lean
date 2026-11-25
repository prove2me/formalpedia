-- Prove2me | solution 1 for UpperTheory.BernoulliSumsFrobeniusOrbits.orbit_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T15:46:47.237776+00:00
-- url     : https://prove2.me/submissions/61d36ca0-3f6e-44ea-abd3-2f92bc888383

import Definitions.Def_Development_AutomorphicArithmetic_ThickFrames_MarkedLow
import Definitions.Def_Development_AutomorphicArithmetic_ThickFrames_orbitSum
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Finset UpperTheory.BernoulliSumsFrobeniusOrbits Formalism.G0
namespace UpperTheory.BernoulliSumsFrobeniusOrbits
private lemma fibre_sum {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    (p : α → ℝ) (f : β → α) (hf : Function.Injective f) (S : Finset β) :
    ∑ T : Finset α, (if univ.filter (fun i => f i ∈ T) = S then pw p T else 0) =
      pw (fun i => p (f i)) S := by
  classical
  set g : α → ℝ := fun a => if a ∈ (univ \ S).image f then 0 else p a with hg
  set h : α → ℝ := fun a => if a ∈ S.image f then 0 else 1 - p a with hh
  have h1 := Finset.prod_add g h (univ : Finset α)
  rw [powerset_univ] at h1
  have h2 : ∏ a, (g a + h a) = pw (fun i => p (f i)) S := by
    rw [← Finset.prod_subset (subset_univ ((univ : Finset β).image f)), prod_image hf.injOn]
    · rw [pw, ← prod_sdiff (subset_univ S), mul_comm]
      congr 1
      · refine prod_congr rfl fun i hi => ?_
        simp [hg, hh, hf.eq_iff, hi]
      · refine prod_congr rfl fun i hi => ?_
        have hi' : i ∉ S := (mem_sdiff.mp hi).2
        simp [hg, hh, hf.eq_iff, hi']
    · intro a _ ha
      have ha1 : a ∉ (univ \ S).image f := fun h' => ha (image_subset_image (subset_univ _) h')
      have ha2 : a ∉ S.image f := fun h' => ha (image_subset_image (subset_univ _) h')
      simp only [hg, hh, if_neg ha1, if_neg ha2]
      ring
  rw [← h2, h1]
  refine sum_congr rfl fun T _ => ?_
  split_ifs with hT
  · rw [pw]
    congr 1
    · refine prod_congr rfl fun a ha => ?_
      have : a ∉ (univ \ S).image f := by
        intro h'
        obtain ⟨i, hi, rfl⟩ := mem_image.mp h'
        exact (mem_sdiff.mp hi).2 (hT ▸ mem_filter.mpr ⟨mem_univ _, ha⟩)
      simp only [hg, if_neg this]
    · refine prod_congr rfl fun a ha => ?_
      have : a ∉ S.image f := by
        intro h'
        obtain ⟨i, hi, rfl⟩ := mem_image.mp h'
        rw [← hT] at hi
        exact (mem_sdiff.mp ha).2 (mem_filter.mp hi).2
      simp only [hh, if_neg this]
  · have : ∃ i, ¬ (f i ∈ T ↔ i ∈ S) := by
      by_contra hc
      push Not at hc
      exact hT (by ext i; simp [hc i])
    obtain ⟨i, hi⟩ := this
    by_cases hiS : i ∈ S
    · have hT' : f i ∉ T := fun h' => hi ⟨fun _ => hiS, fun _ => h'⟩
      rw [prod_eq_zero (s := univ \ T) (i := f i) (by simp [hT']), mul_zero]
      simp only [hh, if_pos (mem_image_of_mem f hiS)]
    · have hT' : f i ∈ T := by
        by_contra h'
        exact hi ⟨fun h'' => absurd h'' h', fun h'' => absurd h'' hiS⟩
      rw [prod_eq_zero (s := T) (i := f i) hT', zero_mul]
      simp only [hg, if_pos (mem_image_of_mem f (mem_sdiff.mpr ⟨mem_univ i, hiS⟩))]
private lemma marginal {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    (p : α → ℝ) (f : β → α) (hf : Function.Injective f) (F : Finset β → ℝ) :
    ∑ T : Finset α, pw p T * F (univ.filter (fun i => f i ∈ T)) =
      ∑ S : Finset β, pw (fun i => p (f i)) S * F S := by
  calc ∑ T : Finset α, pw p T * F (univ.filter (fun i => f i ∈ T))
      = ∑ T : Finset α, ∑ S : Finset β,
          (if univ.filter (fun i => f i ∈ T) = S then pw p T else 0) * F S := by
        refine sum_congr rfl fun T _ => ?_
        simp only [ite_mul, zero_mul]
        rw [Finset.sum_ite_eq]
        simp
    _ = _ := by
        rw [sum_comm]
        refine sum_congr rfl fun S _ => ?_
        rw [← sum_mul, fibre_sum p f hf S]
private lemma fin_sum_eq (n : ℕ) (q : ℕ → ℝ) (F : Finset ℕ → ℝ) :
    (∑ S : Finset (Fin n), pw (fun i : Fin n => q i) S * F (S.map Fin.valEmbedding)) =
      exP q (range n) F := by
  unfold exP
  refine Finset.sum_bij (fun S _ => S.map Fin.valEmbedding) ?_ ?_ ?_ ?_
  · intro S _
    rw [mem_powerset]
    intro x hx
    obtain ⟨i, _, rfl⟩ := mem_map.mp hx
    simp
  · intro S _ S' _ h
    exact Finset.map_injective _ h
  · intro T hT
    refine ⟨univ.filter (fun i : Fin n => (i : ℕ) ∈ T), mem_univ _, ?_⟩
    ext x
    simp only [mem_map, mem_filter, mem_univ, true_and, Fin.valEmbedding_apply]
    constructor
    · rintro ⟨i, hi, rfl⟩; exact hi
    · intro hx
      exact ⟨⟨x, mem_range.mp (mem_powerset.mp hT hx)⟩, hx, rfl⟩
  · intro S _
    have e : range n \ S.map Fin.valEmbedding = (univ \ S).map Fin.valEmbedding := by
      ext x
      simp only [mem_sdiff, mem_range, mem_map, mem_univ, true_and, Fin.valEmbedding_apply]
      constructor
      · rintro ⟨hx, hx'⟩
        exact ⟨⟨x, hx⟩, fun h => hx' ⟨_, h, rfl⟩, rfl⟩
      · rintro ⟨i, hi, rfl⟩
        refine ⟨i.2, ?_⟩
        rintro ⟨j, hj, hji⟩
        exact hi (Fin.ext hji ▸ hj)
    rw [e, prod_map, prod_map]
    rfl
private lemma bernoulliExpectation_mem_and (q : ℕ → ℝ) {S : Finset ℕ} {i₀ : ℕ} (hm : i₀ ∈ S) (A : Finset ℕ → Prop) :
    exP q S (fun T => ind (i₀ ∈ T ∧ A T)) =
      q i₀ * exP q (S.erase i₀) (fun U => ind (A (insert i₀ U))) := by
  unfold exP
  conv_lhs => rw [← Finset.insert_erase hm]
  rw [Finset.sum_powerset_insert (Finset.notMem_erase _ _), Finset.sum_eq_zero, zero_add, mul_sum]
  · refine Finset.sum_congr rfl fun T hT => ?_
    have hT' : i₀ ∉ T := fun h => Finset.notMem_erase _ _ (Finset.mem_powerset.1 hT h)
    have e : insert i₀ (S.erase i₀) \ insert i₀ T = S.erase i₀ \ T := by
      ext x
      simp only [mem_sdiff, mem_insert, mem_erase]
      tauto
    rw [e, prod_insert hT']
    simp only [mem_insert_self, true_and]
    ring
  · intro T hT
    have hT' : i₀ ∉ T := fun h => Finset.notMem_erase _ _ (Finset.mem_powerset.1 hT h)
    simp [ind, hT']
end UpperTheory.BernoulliSumsFrobeniusOrbits
end

set_option autoImplicit false
open Finset UpperTheory.BernoulliSumsFrobeniusOrbits Formalism.G0
namespace UpperTheory.BernoulliSumsFrobeniusOrbits
theorem _root_.solution :
    ∀ (α : Type) [Fintype α] [DecidableEq α] [AddCommGroup α] (p : α → ℝ) (b h t : α), (∃ i : ℕ, b + i • h = t) →
      ∀ A : Finset ℕ → Prop, ∃ i₀ < addOrderOf h, b + i₀ • h = t ∧
        ∑ T : Finset α, pw p T * ind (t ∈ T ∧ A ((univ.filter (fun i : Fin (addOrderOf h) => b + (i : ℕ) • h ∈ T)).map Fin.valEmbedding)) =
          p t * exP (fun i => p (b + i • h)) ((range (addOrderOf h)).erase i₀) (fun U => ind (A (insert i₀ U))) := by
  intro α _ _ _ p b h t ht A
  obtain ⟨i, hi⟩ := ht
  have hpos : 0 < addOrderOf h := addOrderOf_pos h
  have hlt : i % addOrderOf h < addOrderOf h := Nat.mod_lt _ hpos
  have ht : b + (i % addOrderOf h) • h = t := by rw [mod_addOrderOf_nsmul, hi]
  refine ⟨i % addOrderOf h, hlt, ht, ?_⟩
  have hinj : Function.Injective (fun j : Fin (addOrderOf h) => b + (j : ℕ) • h) := by
    intro j k hjk
    have := add_left_cancel hjk
    exact Fin.ext (nsmul_injOn_Iio_addOrderOf j.2 k.2 this)
  have h1 := bernoulliExpectation_mem_and (fun i => p (b + i • h)) (mem_range.2 hlt) A
  rw [ht] at h1
  rw [← h1, ← fin_sum_eq, ← marginal p _ hinj
    (fun S => ind (i % addOrderOf h ∈ S.map Fin.valEmbedding ∧ A (S.map Fin.valEmbedding)))]
  refine sum_congr rfl fun T _ => ?_
  have : t ∈ T ↔ i % addOrderOf h ∈ (univ.filter
      (fun i : Fin (addOrderOf h) => b + (i : ℕ) • h ∈ T)).map Fin.valEmbedding := by
    rw [show i % addOrderOf h = Fin.valEmbedding (⟨_, hlt⟩ : Fin (addOrderOf h)) from rfl,
      Finset.mem_map']
    simp [hi]
  simp only [this]
end UpperTheory.BernoulliSumsFrobeniusOrbits
