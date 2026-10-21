-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Renew46.P26.proposition_3_2
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T00:04:41.284376+00:00
-- url     : https://prove2.me/submissions/032655bf-30fb-44aa-b09e-13dd7a4150d8

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P26
noncomputable section

open scoped BigOperators

open QAlgorithms.Papers.Independent.Renew46.P26

attribute [local instance] Classical.propDecidable

theorem g64f_single_mul_swap {n : ℕ} (s : Equiv.Perm (Fin n)) (a b : Fin n) :
    s * Equiv.swap a b = Equiv.swap (s a) (s b) * s := by
  rw [Equiv.swap_apply_apply]; group

theorem g64f_yjm_eq {n : ℕ} (j : Fin n) :
    yjm j = ∑ k ∈ Finset.univ.filter (fun k : Fin n => k < j),
      MonoidAlgebra.single (Equiv.swap k j) (1 : ℂ) := rfl

theorem g64f_comm_fix {n : ℕ} (g : Equiv.Perm (Fin n)) (j : Fin n) (hgg : g * g = 1)
    (hj : g j = j) (hk : ∀ k, k < j → g k < j) :
    MonoidAlgebra.single g (1 : ℂ) * yjm j = yjm j * MonoidAlgebra.single g 1 := by
  simp only [g64f_yjm_eq, Finset.mul_sum, Finset.sum_mul,
    MonoidAlgebra.single_mul_single, one_mul]
  refine Finset.sum_nbij' (fun k => g k) (fun k => g k) ?_ ?_ ?_ ?_ ?_
  · intro k hk'
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk' ⊢
    exact hk k hk'
  · intro k hk'
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk' ⊢
    exact hk k hk'
  · intro k _; rw [← Equiv.Perm.mul_apply, hgg, Equiv.Perm.one_apply]
  · intro k _; rw [← Equiv.Perm.mul_apply, hgg, Equiv.Perm.one_apply]
  · intro k _
    rw [g64f_single_mul_swap, hj]
theorem g64f_local_rel {n : ℕ} (i : Adjacent n) :
    (∀ j : Fin n, j ≠ i.val → j ≠ nextPosition i →
      adjacentElement i * yjm j = yjm j * adjacentElement i) ∧
    adjacentElement i * yjm i.val + 1 = yjm (nextPosition i) * adjacentElement i := by
  set s := adjacentPerm i with hs
  have hsi : s i.val = nextPosition i := by simp [hs, adjacentPerm]
  have hsn : s (nextPosition i) = i.val := by simp [hs, adjacentPerm]
  have hss : s * s = 1 := by simp [hs, adjacentPerm, Equiv.swap_mul_self]
  have hlt : i.val < nextPosition i := by
    rw [Fin.lt_def]; simp [nextPosition]
  have hadj : ∀ k : Fin n, k < nextPosition i → k ≠ i.val → k < i.val := by
    intro k hk hne
    rw [Fin.lt_def] at hk ⊢
    simp [nextPosition] at hk
    have : k.val ≠ i.val.val := fun h => hne (Fin.ext h)
    omega
  constructor
  · intro j hj1 hj2
    have hsj : s j = j := by
      simp only [hs, adjacentPerm]; exact Equiv.swap_apply_of_ne_of_ne hj1 hj2
    simp only [adjacentElement, g64f_yjm_eq, Finset.mul_sum, Finset.sum_mul,
      MonoidAlgebra.single_mul_single, one_mul]
    refine Finset.sum_nbij' (fun k => s k) (fun k => s k) ?_ ?_ ?_ ?_ ?_
    · intro k hk
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk ⊢
      by_cases h1 : k = i.val
      · subst h1; rw [hsi]
        rcases lt_or_gt_of_ne hj2 with h | h
        · exact absurd (hadj j h hj1) (by intro h'; exact absurd (lt_trans h' hk) (lt_irrefl _))
        · exact h
      by_cases h2 : k = nextPosition i
      · subst h2; rw [hsn]; exact lt_trans hlt hk
      · have : s k = k := by
          simp only [hs, adjacentPerm]; exact Equiv.swap_apply_of_ne_of_ne h1 h2
        rw [this]; exact hk
    · intro k hk
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk ⊢
      by_cases h1 : k = i.val
      · subst h1; rw [hsi]
        rcases lt_or_gt_of_ne hj2 with h | h
        · exact absurd (hadj j h hj1) (by intro h'; exact absurd (lt_trans h' hk) (lt_irrefl _))
        · exact h
      by_cases h2 : k = nextPosition i
      · subst h2; rw [hsn]; exact lt_trans hlt hk
      · have : s k = k := by
          simp only [hs, adjacentPerm]; exact Equiv.swap_apply_of_ne_of_ne h1 h2
        rw [this]; exact hk
    · intro k _; rw [← Equiv.Perm.mul_apply, hss, Equiv.Perm.one_apply]
    · intro k _; rw [← Equiv.Perm.mul_apply, hss, Equiv.Perm.one_apply]
    · intro k _
      rw [g64f_single_mul_swap, hsj]
  · have hset : Finset.univ.filter (fun k : Fin n => k < nextPosition i) =
        insert i.val (Finset.univ.filter (fun k : Fin n => k < i.val)) := by
      ext k
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
      constructor
      · intro hk; by_cases h : k = i.val
        · exact Or.inl h
        · exact Or.inr (hadj k hk h)
      · rintro (h | h)
        · rw [h]; exact hlt
        · exact lt_trans h hlt
    simp only [adjacentElement, g64f_yjm_eq, Finset.mul_sum, Finset.sum_mul,
      MonoidAlgebra.single_mul_single, one_mul]
    rw [hset, Finset.sum_insert (by simp), add_comm]
    congr 1
    · rw [show Equiv.swap i.val (nextPosition i) = s from rfl, hss]; rfl
    · refine Finset.sum_congr rfl (fun k hk => ?_)
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk
      rw [g64f_single_mul_swap]
      have hk1 : k ≠ i.val := ne_of_lt hk
      have hk2 : k ≠ nextPosition i := ne_of_lt (lt_trans hk hlt)
      have : s k = k := by
        simp only [hs, adjacentPerm]; exact Equiv.swap_apply_of_ne_of_ne hk1 hk2
      rw [this, hsi]

theorem g64f_single_mem_prefix (n : ℕ) (h : Equiv.Perm (Fin (n + 1))) :
    MonoidAlgebra.single (h.viaEmbedding (prefixEmbedding (by omega : n + 1 ≤ n + 2))) (1 : ℂ) ∈
      prefixAlgebra (by omega : n + 1 ≤ n + 2) := by
  refine ⟨MonoidAlgebra.single h 1, ?_⟩
  simp [prefixInclusion, MonoidAlgebra.mapDomainAlgHom_apply, MonoidAlgebra.mapDomain_single]
  rfl

theorem g64f_adj_via (n : ℕ) (i : Fin (n + 1)) (hi : i.val < n) :
    Equiv.swap (Fin.castSucc i) (Fin.succ i) =
      (Equiv.swap (⟨i.val, by omega⟩ : Fin (n + 1)) ⟨i.val + 1, by omega⟩).viaEmbedding
        (prefixEmbedding (by omega : n + 1 ≤ n + 2)) := by
  ext x : 1
  by_cases hx : x.val < n + 1
  · have : x = prefixEmbedding (by omega : n + 1 ≤ n + 2) ⟨x.val, hx⟩ := Fin.ext rfl
    have e1 : Fin.castSucc i = prefixEmbedding (by omega : n + 1 ≤ n + 2) ⟨i.val, by omega⟩ :=
      Fin.ext rfl
    have e2 : Fin.succ i = prefixEmbedding (by omega : n + 1 ≤ n + 2) ⟨i.val + 1, by omega⟩ :=
      Fin.ext (by simp only [Fin.val_succ]; rfl)
    rw [this, Equiv.Perm.viaEmbedding_apply, e1, e2, ← Function.Embedding.swap_apply]
  · rw [Equiv.Perm.viaEmbedding_apply_of_notMem]
    · rw [Equiv.swap_apply_of_ne_of_ne]
      · intro h; have := congrArg Fin.val h; simp at this; omega
      · intro h; have := congrArg Fin.val h; simp at this; omega
    · rintro ⟨y, hy⟩
      have := congrArg Fin.val hy
      have h2 : ((prefixEmbedding (by omega : n + 1 ≤ n + 2)) y).val = y.val := rfl
      rw [h2] at this; have := y.isLt; omega

theorem g64f_yjm_comm {m : ℕ} (a b : Fin m) (hab : a < b) : yjm a * yjm b = yjm b * yjm a := by
  have key : ∀ k ∈ Finset.univ.filter (fun k : Fin m => k < a),
      MonoidAlgebra.single (Equiv.swap k a) (1 : ℂ) * yjm b =
        yjm b * MonoidAlgebra.single (Equiv.swap k a) (1 : ℂ) := by
    intro k hk
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk
    refine g64f_comm_fix _ b (Equiv.swap_mul_self _ _) ?_ ?_
    · exact Equiv.swap_apply_of_ne_of_ne (ne_of_lt (lt_trans hk hab)).symm (ne_of_lt hab).symm
    · intro x hm
      rcases eq_or_ne x k with rfl | h1
      · rw [Equiv.swap_apply_left]; exact hab
      rcases eq_or_ne x a with rfl | h2
      · rw [Equiv.swap_apply_right]; exact lt_trans hk hab
      rw [Equiv.swap_apply_of_ne_of_ne h1 h2]; exact hm
  rw [g64f_yjm_eq a, Finset.sum_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl key

theorem solution (n : ℕ) :
    ∃ f : Hecke 2 →ₐ[ℂ] SymmetricAlgebra (n + 2),
      f (heckeY (0 : Fin 2)) = yjm ⟨n, by omega⟩ ∧
      f (heckeY (1 : Fin 2)) = yjm ⟨n + 1, by omega⟩ ∧
      f (heckeS (⟨0, by decide⟩ : Adjacent 2)) =
        swapAlgebraElement (⟨n, by omega⟩ : Fin (n + 2)) ⟨n + 1, by omega⟩ ∧
      Algebra.adjoin ℂ ((prefixAlgebra (by omega : n + 1 ≤ n + 2) :
        Set (SymmetricAlgebra (n + 2))) ∪ (f.range : Set (SymmetricAlgebra (n + 2)))) = ⊤ := by
  set a : Fin (n + 2) := ⟨n, by omega⟩ with ha
  set b : Fin (n + 2) := ⟨n + 1, by omega⟩ with hb
  let gen : Sum (Fin 2) (Adjacent 2) → SymmetricAlgebra (n + 2) :=
    Sum.elim (fun i : Fin 2 => if i.val = 0 then yjm a else yjm b) (fun _ => swapAlgebraElement a b)
  let F := FreeAlgebra.lift ℂ gen
  have hFY : ∀ i : Fin 2, F (freeY i) = if i.val = 0 then yjm a else yjm b := by
    intro i; simp [F, freeY, gen]
  have hFS : ∀ i : Adjacent 2, F (freeS i) = swapAlgebraElement a b := by
    intro i; simp [F, freeS, gen]
  have hab : a < b := by simp [ha, hb, Fin.lt_def]
  have hcomm : yjm a * yjm b = yjm b * yjm a := g64f_yjm_comm a b hab
  let ia : Adjacent (n + 2) := ⟨a, by simp [ha]⟩
  have hloc : swapAlgebraElement a b * yjm a + 1 = yjm b * swapAlgebraElement a b :=
    (g64f_local_rel ia).2
  have hss : swapAlgebraElement a b * swapAlgebraElement a b = 1 := by
    simp [swapAlgebraElement, MonoidAlgebra.single_mul_single, Equiv.swap_mul_self,
      MonoidAlgebra.one_def]
  have hA : ∀ i : Adjacent 2, i.val.val = 0 := by
    intro i; have := i.property; omega
  have w : ∀ ⦃x y : HeckeFree 2⦄, HeckeRelations 2 x y → F x = F y := by
    rintro x y (⟨i, j, rfl, rfl⟩ | ⟨i, rfl, rfl⟩ | ⟨i, j, hij, rfl, rfl⟩ |
      ⟨i, j, hij, rfl, rfl⟩ | ⟨i, j, h1, h2, rfl, rfl⟩ | ⟨i, rfl, rfl⟩)
    · simp only [map_mul, hFY]
      fin_cases i <;> fin_cases j <;> simp [hcomm]
    · simp only [map_mul, hFS, map_one, hss]
    · have := hA i; have := hA j; omega
    · have := hA i; have := hA j; omega
    · exfalso
      have hi := hA i
      fin_cases j
      · exact h1 (Fin.ext (by simp [hi]))
      · exact h2 (Fin.ext (by simp [nextPosition, hi]))
    · simp only [map_mul, map_add, map_one, hFY, hFS, hA i]
      have : (nextPosition i).val = 1 := by simp [nextPosition, hA i]
      simp only [this, if_true, one_ne_zero, if_false]
      exact hloc
  refine ⟨RingQuot.liftAlgHom ℂ ⟨F, w⟩, ?_, ?_, ?_, ?_⟩
  · simp [heckeY, hFY]
  · simp [heckeY, hFY]
  · simp [heckeS, hFS]
  · set S := Algebra.adjoin ℂ ((prefixAlgebra (by omega : n + 1 ≤ n + 2) :
        Set (SymmetricAlgebra (n + 2))) ∪
          ((RingQuot.liftAlgHom ℂ ⟨F, w⟩).range : Set (SymmetricAlgebra (n + 2)))) with hS
    have hsing : ∀ g : Equiv.Perm (Fin (n + 2)), MonoidAlgebra.single g (1 : ℂ) ∈ S := by
      let M : Submonoid (Equiv.Perm (Fin (n + 2))) :=
        { carrier := {g | MonoidAlgebra.single g (1 : ℂ) ∈ S}
          one_mem' := by
            show MonoidAlgebra.single 1 (1 : ℂ) ∈ S
            rw [← MonoidAlgebra.one_def]; exact S.one_mem
          mul_mem' := by
            intro g h hg hh
            show MonoidAlgebra.single (g * h) (1 : ℂ) ∈ S
            have := S.mul_mem hg hh
            rwa [MonoidAlgebra.single_mul_single, one_mul] at this }
      have hgen : Set.range (fun i : Fin (n + 1) => Equiv.swap i.castSucc i.succ) ⊆ M := by
        rintro _ ⟨i, rfl⟩
        show MonoidAlgebra.single (Equiv.swap i.castSucc i.succ) (1 : ℂ) ∈ S
        by_cases hi : i.val < n
        · rw [g64f_adj_via n i hi]
          exact Algebra.subset_adjoin (Or.inl (g64f_single_mem_prefix n _))
        · have hi' : i.val = n := by have := i.isLt; omega
          have e1 : Fin.castSucc i = a := Fin.ext (by simp [ha, hi'])
          have e2 : Fin.succ i = b := Fin.ext (by simp [hb, hi'])
          rw [e1, e2]
          refine Algebra.subset_adjoin (Or.inr ⟨heckeS (⟨0, by decide⟩ : Adjacent 2), ?_⟩)
          simp [heckeS, hFS, swapAlgebraElement]
      have := (Submonoid.closure_le.mpr hgen)
      rw [Equiv.Perm.mclosure_swap_castSucc_succ] at this
      intro g; exact this (Submonoid.mem_top g)
    rw [eq_top_iff]
    rintro x -
    induction x using MonoidAlgebra.induction_linear with
    | zero => exact S.zero_mem
    | add x y hx hy => exact S.add_mem hx hy
    | single g r =>
      have : MonoidAlgebra.single g r = r • MonoidAlgebra.single g (1 : ℂ) := by
        simp [MonoidAlgebra.smul_single]
      rw [this]; exact S.smul_mem (hsing g) r
