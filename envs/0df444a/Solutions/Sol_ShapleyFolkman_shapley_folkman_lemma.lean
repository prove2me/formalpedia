-- Prove2me | solution 1 for ShapleyFolkman.shapley_folkman_lemma
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T16:33:55.555006+00:00
-- url     : https://prove2.me/submissions/3fda5d13-3d31-48a1-8e9b-efebee271feb

import Mathlib
open scoped Pointwise

set_option autoImplicit false

namespace SFAux

open Finset

lemma card_bad_le {ι : Type*} [Fintype ι] {m : ℕ} (idx : ι → Fin m)
    (hpos : ∀ i, 1 ≤ (univ.filter (fun k => idx k = i)).card)
    (B : Finset (Fin m)) (hB : ∀ i ∈ B, 2 ≤ (univ.filter (fun k => idx k = i)).card) :
    m + B.card ≤ Fintype.card ι := by
  classical
  have h1 : ∑ i : Fin m, (univ.filter (fun k => idx k = i)).card = Fintype.card ι := by
    have := Finset.sum_fiberwise (univ : Finset ι) idx (fun _ => (1 : ℕ))
    simpa using this
  have h2 : ∑ i : Fin m, (1 + if i ∈ B then 1 else 0) ≤
      ∑ i : Fin m, (univ.filter (fun k => idx k = i)).card := by
    apply Finset.sum_le_sum
    intro i _
    split_ifs with h
    · exact hB i h
    · simpa using hpos i
  rw [Finset.sum_add_distrib, Finset.sum_boole] at h2
  simp at h2
  omega

theorem main {E : Type*} [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]
    (m : ℕ) (S : Fin m → Set E)
    (x : E) (hx : x ∈ convexHull ℝ (∑ i, S i)) :
    ∃ y : Fin m → E,
      (∀ i, y i ∈ convexHull ℝ (S i)) ∧ ∑ i, y i = x ∧
        {i | y i ∉ S i}.ncard ≤ Module.finrank ℝ E := by
  classical
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm
    refine ⟨fun i => i.elim0, fun i => i.elim0, ?_, ?_⟩
    · simp at hx; simp [hx]
    · rw [Set.eq_empty_of_isEmpty {i : Fin 0 | _}]; simp
  rw [convexHull_sum, Set.mem_fintype_sum] at hx
  obtain ⟨y0, hy0, hsum⟩ := hx
  let T : Set (E × (Fin m → ℝ)) := ⋃ i, (fun s => (s, Pi.single i (1 : ℝ))) '' S i
  let g : Fin m → E →ᵃ[ℝ] (E × (Fin m → ℝ)) := fun i =>
    { toFun := fun s => (s, Pi.single i 1)
      linear := LinearMap.inl ℝ E (Fin m → ℝ)
      map_vadd' := by intro p v; ext <;> simp }
  have hg : ∀ i, convexHull ℝ (S i) ⊆ g i ⁻¹' convexHull ℝ T := fun i =>
    convexHull_min (fun s hs => subset_convexHull ℝ T (Set.mem_iUnion.2 ⟨i, s, hs, rfl⟩))
      ((convex_convexHull ℝ T).affine_preimage (g i))
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  set q : (E × (Fin m → ℝ)) := ((m : ℝ)⁻¹ • x, fun _ => (m : ℝ)⁻¹) with hqdef
  have hgv : ∀ i s, g i s = (s, Pi.single i (1 : ℝ)) := fun _ _ => rfl
  have hq : q ∈ convexHull ℝ T := by
    have h := (convex_convexHull ℝ T).sum_mem (t := (univ : Finset (Fin m)))
      (w := fun _ => (m : ℝ)⁻¹) (z := fun i => g i (y0 i))
      (fun _ _ => by positivity) (by simp; field_simp) (fun i _ => hg i (hy0 i))
    convert h using 1
    simp only [hgv]
    ext1
    · rw [Prod.fst_sum]
      simp only [Prod.smul_fst]
      rw [← Finset.smul_sum, hsum]
    · rw [Prod.snd_sum]
      funext j
      rw [Finset.sum_apply]
      simp [q, Pi.single_apply]
  obtain ⟨ι, _, z, w, hzT, hind, hw0, hw1, hwz⟩ := eq_pos_convex_span_of_mem_convexHull hq
  have hmem : ∀ k, ∃ i, ∃ s ∈ S i, (s, Pi.single i (1 : ℝ)) = z k := by
    intro k
    rcases Set.mem_iUnion.1 (hzT (Set.mem_range_self k)) with ⟨i, s, hs, he⟩
    exact ⟨i, s, hs, he⟩
  choose idx pt hpt hz using hmem
  -- dimension bound
  let f : (E × (Fin m → ℝ)) →ₗ[ℝ] ℝ :=
    { toFun := fun v => ∑ i, v.2 i
      map_add' := by
        intro a b
        show ∑ i, (a + b).2 i = ∑ i, a.2 i + ∑ i, b.2 i
        rw [← Finset.sum_add_distrib]; rfl
      map_smul' := by
        intro c a
        show ∑ i, (c • a).2 i = c • ∑ i, a.2 i
        rw [smul_eq_mul, Finset.mul_sum]; rfl }
  have hfz : ∀ k, f (z k) = 1 := by
    intro k
    rw [← hz k]
    simp [f, Pi.single_apply]
  have hspan : vectorSpan ℝ (Set.range z) ≤ LinearMap.ker f := by
    rw [vectorSpan_def, Submodule.span_le]
    rintro _ ⟨a, ⟨k1, rfl⟩, b, ⟨k2, rfl⟩, rfl⟩
    simp [hfz]
  have hker : LinearMap.ker f ≠ ⊤ := by
    intro h
    have : ((0 : E), Pi.single (⟨0, hm⟩ : Fin m) (1 : ℝ)) ∈ LinearMap.ker f := by
      rw [h]; exact Submodule.mem_top
    simp [f] at this
  have hfin : Module.finrank ℝ (E × (Fin m → ℝ)) = Module.finrank ℝ E + m := by
    simp [Module.finrank_prod]
  have hcard : Fintype.card ι ≤ Module.finrank ℝ E + m := by
    have h1 : Fintype.card ι ≤ Module.finrank ℝ (vectorSpan ℝ (Set.range z)) + 1 :=
      hind.card_le_finrank_succ
    have h2 : Module.finrank ℝ (vectorSpan ℝ (Set.range z)) ≤
        Module.finrank ℝ (LinearMap.ker f) := Submodule.finrank_mono hspan
    have h3 : Module.finrank ℝ (LinearMap.ker f) < Module.finrank ℝ (E × (Fin m → ℝ)) :=
      Submodule.finrank_lt hker
    omega
  -- coordinates
  simp_rw [← hz] at hwz
  have hfst : ∑ k, w k • pt k = (m : ℝ)⁻¹ • x := by
    have := congrArg Prod.fst hwz
    rw [Prod.fst_sum] at this
    simpa [q] using this
  have hsnd : ∀ i, ∑ k ∈ univ.filter (fun k => idx k = i), w k = (m : ℝ)⁻¹ := by
    intro i
    have := congrFun (congrArg Prod.snd hwz) i
    rw [Prod.snd_sum, Finset.sum_apply] at this
    simp only [Prod.smul_snd, Pi.smul_apply, Pi.single_apply, smul_eq_mul, mul_ite, mul_one,
      mul_zero] at this
    have hq2 : q.2 i = (m : ℝ)⁻¹ := rfl
    rw [Finset.sum_filter, ← hq2, ← this]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    by_cases h : idx k = i
    · simp [h]
    · simp [h, Ne.symm h]
  refine ⟨fun i => ∑ k ∈ univ.filter (fun k => idx k = i), ((m : ℝ) * w k) • pt k, ?_, ?_, ?_⟩
  · intro i
    refine (convex_convexHull ℝ _).sum_mem (fun k _ => by have := hw0 k; positivity) ?_ ?_
    · rw [← Finset.mul_sum, hsnd i]; field_simp
    · intro k hk
      apply subset_convexHull
      have := (Finset.mem_filter.1 hk).2
      rw [← this]; exact hpt k
  · rw [Finset.sum_fiberwise univ idx (fun k => ((m : ℝ) * w k) • pt k)]
    simp_rw [mul_smul]
    rw [← Finset.smul_sum, hfst, smul_smul, mul_inv_cancel₀ hmR.ne', one_smul]
  · set y : Fin m → E := fun i =>
      ∑ k ∈ univ.filter (fun k => idx k = i), ((m : ℝ) * w k) • pt k with hy
    have hpos : ∀ i, 1 ≤ (univ.filter (fun k => idx k = i)).card := by
      intro i
      apply Finset.card_pos.2
      apply Finset.nonempty_of_sum_ne_zero (f := w)
      rw [hsnd i]; positivity
    let B : Finset (Fin m) := univ.filter (fun i => y i ∉ S i)
    have hB : ∀ i ∈ B, 2 ≤ (univ.filter (fun k => idx k = i)).card := by
      intro i hi
      have hiS : y i ∉ S i := (Finset.mem_filter.1 hi).2
      by_contra hlt
      have h1 : (univ.filter (fun k => idx k = i)).card = 1 := by
        have := hpos i; omega
      obtain ⟨k, hk⟩ := Finset.card_eq_one.1 h1
      have hki : idx k = i := by
        have : k ∈ univ.filter (fun k => idx k = i) := by rw [hk]; simp
        exact (Finset.mem_filter.1 this).2
      have hwk : w k = (m : ℝ)⁻¹ := by
        have := hsnd i; rw [hk] at this; simpa using this
      apply hiS
      have : y i = pt k := by
        simp only [hy]
        rw [hk, Finset.sum_singleton, hwk, mul_inv_cancel₀ hmR.ne', one_smul]
      rw [this, ← hki]; exact hpt k
    have hc := card_bad_le idx hpos B hB
    have hset : {i | y i ∉ S i} = (B : Set (Fin m)) := by
      ext i; simp [B]
    rw [hset, Set.ncard_coe_finset]
    omega

end SFAux

open scoped Pointwise in
theorem solution (N m : ℕ) (S : Fin m → Set (EuclideanSpace ℝ (Fin N)))
    (x : EuclideanSpace ℝ (Fin N)) (hx : x ∈ convexHull ℝ (∑ i, S i)) :
    ∃ y : Fin m → EuclideanSpace ℝ (Fin N),
      (∀ i, y i ∈ convexHull ℝ (S i)) ∧ ∑ i, y i = x ∧
        {i | y i ∉ S i}.ncard ≤ N := by
  simpa [finrank_euclideanSpace_fin] using SFAux.main m S x hx
