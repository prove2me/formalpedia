-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Information100.P62.sequential_converse
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T09:03:18.301195+00:00
-- url     : https://prove2.me/submissions/158c854d-00ba-485d-8365-26341a12a1f8

import Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P62_kraus_geometric_converse

set_option autoImplicit false
noncomputable section
open scoped Matrix ComplexConjugate ComplexOrder
open QAlgorithms QAlgorithms.Papers.Independent.Information100.P62
open Finset

private lemma rank_image {I O : Type} [Fintype I] [Fintype O]
    [DecidableEq I] [DecidableEq O] (M : Matrix O I ℂ) :
    M.rank = Module.finrank ℂ (imageSpace M) := by
  rw [Matrix.rank_eq_finrank_range_toLin M
    (EuclideanSpace.basisFun O ℂ).toBasis (EuclideanSpace.basisFun I ℂ).toBasis]
  rfl

private lemma projection_linear {I : Type} [Fintype I] [DecidableEq I]
    (C : Submodule ℂ (EuclideanSpace ℂ I)) :
    Matrix.toEuclideanLin (projection C) = C.starProjection.toLinearMap := by
  apply (EuclideanSpace.basisFun I ℂ).toBasis.ext
  intro i
  ext j
  simp [projection, Matrix.toLpLin_apply,
    EuclideanSpace.basisFun_apply, QAlgorithms.ket]

private lemma mapped_image {I O J : Type} [Fintype I] [Fintype O] [Fintype J]
    [DecidableEq I] [DecidableEq O] [DecidableEq J]
    (A : Matrix O I ℂ) (B : Matrix J O ℂ) :
    (imageSpace A).map (Matrix.toEuclideanLin B) = imageSpace (B * A) := by
  unfold imageSpace
  rw [← LinearMap.range_comp, ← Matrix.toLpLin_mul_same]

private lemma selected_singleton {I O : Type} [Fintype I] [Fintype O]
    [DecidableEq I] [DecidableEq O] {r : ℕ} (E : Fin r → Matrix O I ℂ)
    {A : Shape} (f : Block A → Fin r) (k : Block A) :
    selectedSpan E f {k} = imageSpace (E (f k)) := by
  classical
  apply le_antisymm
  · apply iSup_le
    intro a
    have ha : a.val = k := mem_singleton.mp a.property
    simpa only [ha] using (le_refl (imageSpace (E (f k))))
  · exact le_iSup_of_le ⟨k,mem_singleton_self k⟩ le_rfl

private lemma overlap_rank {I O : Type} [Fintype I] [Fintype O]
    [DecidableEq I] [DecidableEq O] (A B : Matrix O I ℂ) :
    (Aᴴ * B).rank = (projection (imageSpace A) * B).rank := by
  have hk : LinearMap.ker (Matrix.toEuclideanLin (Aᴴ * B)) =
      LinearMap.ker (Matrix.toEuclideanLin (projection (imageSpace A) * B)) := by
    ext x
    simp only [Matrix.toLpLin_mul_same, LinearMap.mem_ker, LinearMap.comp_apply,
      Matrix.toEuclideanLin_conjTranspose_eq_adjoint, projection_linear,
      ContinuousLinearMap.coe_coe]
    rw [Submodule.starProjection_apply_eq_zero_iff]
    change (Matrix.toEuclideanLin A).adjoint (Matrix.toEuclideanLin B x) = 0 ↔
      Matrix.toEuclideanLin B x ∈ (LinearMap.range (Matrix.toEuclideanLin A))ᗮ
    rw [LinearMap.orthogonal_range]
    rfl
  have h₁ := (Matrix.toEuclideanLin (Aᴴ * B)).finrank_range_add_finrank_ker
  have h₂ := (Matrix.toEuclideanLin (projection (imageSpace A) * B)).finrank_range_add_finrank_ker
  rw [hk] at h₁
  rw [rank_image,rank_image]
  exact Nat.add_right_cancel (h₁.trans h₂.symm)

private lemma overlap_self_rank {I O : Type} [Fintype I] [Fintype O]
    [DecidableEq I] [DecidableEq O] (A : Matrix O I ℂ) :
    (Aᴴ * A).rank = A.rank := Matrix.rank_conjTranspose_mul_self A

private lemma two_blocks (d e : ℕ) :
    ∃ a b : Block (quantum d + quantum e), a ≠ b ∧
      blockSize (quantum d + quantum e) a = d ∧
      blockSize (quantum d + quantum e) b = e := by
  classical
  let A := quantum d + quantum e
  have hl : A.toList.length = 2 := by simp [A,quantum]
  obtain ⟨x,y,hxy⟩ := List.length_eq_two.mp hl
  let a : Block A := ⟨0,by omega⟩
  let b : Block A := ⟨1,by omega⟩
  have hab : a ≠ b := by intro h; have := congrArg Fin.val h; simp [a,b] at this
  have ha : blockSize A a = x := by simp [blockSize,hxy,a]
  have hb : blockSize A b = y := by simp [blockSize,hxy,b]
  have hm : ({x,y} : Multiset ℕ) = {d,e} := by
    calc
      ({x,y} : Multiset ℕ) = (A.toList : Multiset ℕ) := by rw [hxy]; rfl
      _ = {d,e} := by rw [Multiset.coe_toList]; rfl
  have hp : x = d ∧ y = e ∨ x = e ∧ y = d := by
    have hx : x = d ∨ x = e := by
      have hh : x ∈ ({d,e} : Multiset ℕ) := hm ▸ (by simp)
      simpa using hh
    rcases hx with rfl | rfl
    · exact Or.inl ⟨rfl, by simpa using hm⟩
    · refine Or.inr ⟨rfl, ?_⟩
      have hm' := hm.trans (Multiset.cons_swap d x 0)
      simpa using hm' 
  rcases hp with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · exact ⟨a,b,hab,ha,hb⟩
  · exact ⟨b,a,Ne.symm hab,hb,ha⟩

theorem solution {I O : Type} [Fintype I] [Fintype O]
    [DecidableEq I] [DecidableEq O] [Nonempty I] [Nonempty O]
    {r : ℕ} (E : Fin r → Matrix O I ℂ) (hE : IsKrausFamily E) :
    (∀ A : Shape, Transmits (krausApply E) A → ∃ f : Block A → Fin r,
      ∀ k : Block A,
        (blockSize A k : ℤ) + max 0
          (((projection (selectedSpan E f (univ.filter (fun j => j < k))) * E (f k)).rank : ℤ) -
            Module.finrank ℂ (selectedSpan E f (univ.filter (fun j => j < k))) +
            ∑ j ∈ univ.filter (fun j => j < k), (blockSize A j : ℤ)) ≤ (E (f k)).rank) ∧
    (∀ d e : ℕ, 0 < e → e ≤ d → Transmits (krausApply E) (quantum d + quantum e) →
      ∃ i j : Fin r, d ≤ (E i).rank ∧
        (e : ℤ) + max 0 (((E i)ᴴ * E j).rank - ((E i).rank : ℤ) + d) ≤ (E j).rank ∧
        (i = j → d + e ≤ (E i).rank) ∧
        (((E i).rank = d) → e + ((E i)ᴴ * E j).rank ≤ (E j).rank) ∧
        ((E i)ᴴ * E j).rank = (projection (imageSpace (E i)) * E j).rank) := by
  classical
  constructor
  · intro A hA
    obtain ⟨f,hf⟩ := (kraus_geometric_converse E hE A hA).1
    refine ⟨f,?_⟩
    intro k
    have hdis : Disjoint (univ.filter (fun j : Block A => j < k)) {k} := by simp
    have hh := hf (univ.filter (fun j : Block A => j < k)) {k} hdis
    rw [selected_singleton, mapped_image, ← rank_image, ← rank_image] at hh
    simpa only [sum_singleton] using hh
  · intro d e he hed hA
    obtain ⟨a,b,hab,ha,hb⟩ := two_blocks d e
    obtain ⟨f,hf⟩ := (kraus_geometric_converse E hE _ hA).1
    have hfirst := hf ∅ {a} (by simp)
    rw [selected_singleton, ← rank_image] at hfirst
    simp only [sum_singleton,ha,sum_empty] at hfirst
    have hd : d ≤ (E (f a)).rank := by omega
    have hdis : Disjoint ({a} : Finset (Block (quantum d + quantum e))) {b} := by
      simpa using hab
    have hsecond := hf {a} {b} hdis
    rw [selected_singleton, selected_singleton, mapped_image,
      ← rank_image, ← rank_image, ← rank_image, ← overlap_rank] at hsecond
    simp only [sum_singleton,ha,hb] at hsecond
    refine ⟨f a,f b,hd,hsecond,?_,?_,overlap_rank _ _⟩
    · intro hij
      rw [← hij, overlap_self_rank] at hsecond
      omega
    · intro hr
      rw [hr] at hsecond
      omega

#print axioms solution
