-- Prove2me | solution 1 for VapnikChervonenkis.Entropy.lemma1_shattered_subsample
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T04:47:17.439881+00:00
-- url     : https://prove2.me/submissions/685d33df-7730-412b-b89f-b23219056ad0

import Mathlib
import Definitions.Def_VapnikChervonenkis_Shared_Phi
import Definitions.Def_VapnikChervonenkis_Shared_index

open MeasureTheory Filter Topology

namespace VapnikChervonenkis.Entropy

theorem aux_l1ss_Phi_eq : ∀ (r n : ℕ),
    Shared.Phi n r = ∑ k ∈ Finset.range (n + 1), r.choose k := by
  intro r
  induction r with
  | zero =>
    intro n
    cases n with
    | zero => simp [Shared.Phi]
    | succ n =>
      rw [Finset.sum_range_succ']
      simp [Shared.Phi, Nat.choose_zero_succ]
  | succ r ih =>
    intro n
    cases n with
    | zero => simp [Shared.Phi]
    | succ n =>
      rw [Shared.Phi, ih (n + 1), ih n]
      rw [Finset.sum_range_succ' (fun k => (r + 1).choose k)]
      simp only [Nat.choose_succ_succ']
      rw [Finset.sum_add_distrib, Finset.sum_range_succ' (fun k => r.choose k)]
      simp
      ring

end VapnikChervonenkis.Entropy

open VapnikChervonenkis VapnikChervonenkis.Entropy
open MeasureTheory Filter Topology

theorem solution {X : Type*} (S : Set (Set X)) (i n : ℕ) (x : Fin i → X)
    (hn1 : 1 ≤ n) (hni : n ≤ i) (hΔ : Shared.Phi n i ≤ Shared.index S x) :
    ∃ e : Fin n → Fin i, StrictMono e ∧ Shared.index S (x ∘ e) = 2 ^ n := by
  classical
  set 𝒜 : Finset (Finset (Fin i)) :=
    Finset.univ.filter (fun t : Finset (Fin i) => ∃ A ∈ S, ∀ j, j ∈ t ↔ x j ∈ A) with h𝒜
  have hidx : Shared.index S x = 𝒜.card := by
    unfold Shared.index
    rw [h𝒜]
  -- VC dimension at least n
  have hvc : n ≤ 𝒜.vcDim := by
    by_contra hlt
    rw [not_le] at hlt
    have h1 := Finset.card_le_card_shatterer 𝒜
    have h2 := Finset.card_shatterer_le_sum_vcDim (𝒜 := 𝒜)
    rw [Fintype.card_fin] at h2
    have h3 : ∑ k ∈ Finset.Iic 𝒜.vcDim, i.choose k ≤ ∑ k ∈ Finset.range n, i.choose k := by
      apply Finset.sum_le_sum_of_subset
      intro k hk
      simp only [Finset.mem_Iic] at hk
      simp only [Finset.mem_range]
      omega
    have h4 : Shared.Phi n i = ∑ k ∈ Finset.range n, i.choose k + i.choose n := by
      rw [aux_l1ss_Phi_eq, Finset.sum_range_succ]
    have h5 : 0 < i.choose n := Nat.choose_pos hni
    omega
  have hbot : (⊥ : ℕ) < n := by simp; omega
  obtain ⟨s, hs, hns⟩ := (Finset.le_sup_iff hbot).1 hvc
  rw [Finset.mem_shatterer] at hs
  obtain ⟨s', hs's, hcard⟩ := Finset.exists_subset_card_eq hns
  have hsh : 𝒜.Shatters s' := hs.mono_right hs's
  let f := s'.orderEmbOfFin hcard
  refine ⟨fun k => f k, f.strictMono, ?_⟩
  unfold Shared.index
  have hall : (Finset.univ.filter (fun t : Finset (Fin n) =>
      ∃ A ∈ S, ∀ k, k ∈ t ↔ (x ∘ fun k => f k) k ∈ A)) = Finset.univ := by
    apply Finset.filter_true_of_mem
    intro u _
    have hsub : u.map f.toEmbedding ⊆ s' := by
      intro j hj
      rw [Finset.mem_map] at hj
      obtain ⟨k, _, rfl⟩ := hj
      exact s'.orderEmbOfFin_mem hcard k
    obtain ⟨t, ht, hst⟩ := hsh hsub
    rw [h𝒜, Finset.mem_filter] at ht
    obtain ⟨_, A, hA, htA⟩ := ht
    refine ⟨A, hA, fun k => ?_⟩
    simp only [Function.comp_apply]
    rw [← htA]
    have hk : f k ∈ s' := s'.orderEmbOfFin_mem hcard k
    constructor
    · intro hku
      have : f k ∈ u.map f.toEmbedding := Finset.mem_map_of_mem _ hku
      rw [← hst] at this
      exact (Finset.mem_inter.1 this).2
    · intro hkt
      have : f k ∈ s' ∩ t := Finset.mem_inter.2 ⟨hk, hkt⟩
      rw [hst, Finset.mem_map] at this
      obtain ⟨k', hk', hkk⟩ := this
      have : k' = k := f.injective hkk
      rw [← this]; exact hk'
  convert congrArg Finset.card hall using 1
  rw [Finset.card_univ, Fintype.card_finset, Fintype.card_fin]
