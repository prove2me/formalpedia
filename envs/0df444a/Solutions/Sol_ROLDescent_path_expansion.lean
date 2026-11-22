-- Prove2me | solution 1 for ROLDescent.path_expansion
-- status  : ACCEPTED   (prove)
-- author  : @I am wealthy
-- created : 2026-11-21T16:12:17.192923+00:00
-- url     : https://prove2.me/submissions/4d8af0f6-42fb-48e0-9b1e-418c63f32961

import Mathlib
import Definitions.Def_ROLDescent_WeightedComplex
import Definitions.Def_HDXConc_linkWeight
import Definitions.Def_ROLDescent_prefixFace
import Definitions.Def_ROLDescent_rootPaths

set_option autoImplicit false

namespace ROLDescent.PathProof

variable {V : Type*} [Fintype V] [DecidableEq V]

@[simp] theorem prefix_zero {j : ℕ} (p : Fin j → V) : prefixFace p 0 = ∅ := by
  simp [prefixFace]

@[simp] theorem prefix_full {j : ℕ} (p : Fin j → V) :
    prefixFace p j = Finset.univ.image p := by
  simp [prefixFace]

theorem prefix_card {j k : ℕ} (p : Fin j → V) (hp : Function.Injective p)
    (hk : k ≤ j) : (prefixFace p k).card = k := by
  rw [prefixFace, Finset.card_image_of_injective _ hp]
  simpa [Nat.min_eq_right hk] using (Fin.card_filter_val_lt (n := j) (m := k))

theorem prefix_snoc_le {j k : ℕ} (p : Fin j → V) (v : V) (hk : k ≤ j) :
    prefixFace (Fin.snoc p v) k = prefixFace p k := by
  ext x
  simp only [prefixFace, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨m, hm, hx⟩
    rcases Fin.eq_castSucc_or_eq_last m with ⟨m, rfl⟩ | rfl
    · exact ⟨m, hm, by simpa only [Fin.snoc_castSucc] using hx⟩
    · have : j < k := hm
      omega
  · rintro ⟨m, hm, hx⟩
    exact ⟨m.castSucc, hm, by simpa only [Fin.snoc_castSucc] using hx⟩

theorem prefix_snoc_full {j : ℕ} (p : Fin j → V) (v : V) :
    prefixFace (Fin.snoc p v) (j + 1) = insert v (prefixFace p j) := by
  ext x
  simp only [prefix_full, Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_insert]
  constructor
  · rintro ⟨m, hx⟩
    rcases Fin.eq_castSucc_or_eq_last m with ⟨m, rfl⟩ | rfl
    · exact Or.inr ⟨m, by simpa only [Fin.snoc_castSucc] using hx⟩
    · exact Or.inl (by simpa only [Fin.snoc_last] using hx.symm)
  · rintro (rfl | ⟨m, hx⟩)
    · exact ⟨Fin.last j, by simp only [Fin.snoc_last]⟩
    · exact ⟨m.castSucc, by simpa only [Fin.snoc_castSucc] using hx⟩

theorem empty_mem {X : Finset (Finset V)} {d : ℕ} {w : Finset V → ℝ}
    (hX : WeightedComplex X d w) : ∅ ∈ X := by
  obtain ⟨F, hF⟩ := hX.1
  exact hX.2.1.1 F hF ∅ (Finset.empty_subset _)

theorem link_nonempty {X : Finset (Finset V)} {d : ℕ} {w : Finset V → ℝ}
    (hX : WeightedComplex X d w) {τ : Finset V} (hτ : τ ∈ X)
    (hcard : τ.card < d) : (HDXConc.linkVerts X τ).Nonempty := by
  let candidates := X.filter (fun F => τ ⊆ F)
  obtain ⟨F, hF, hmax⟩ := Finset.exists_max_image candidates Finset.card
    ⟨τ, Finset.mem_filter.mpr ⟨hτ, le_rfl⟩⟩
  obtain ⟨hFX, hτF⟩ := Finset.mem_filter.mp hF
  have hFd : F.card = d := hX.2.1.2 F hFX (by
    intro G hG hFG
    have hG' : G ∈ candidates := Finset.mem_filter.mpr ⟨hG, hτF.trans hFG⟩
    exact (Finset.eq_of_subset_of_card_le hFG (hmax G hG')).symm)
  have hnot : ¬ F ⊆ τ := by
    intro hFτ
    have := Finset.card_le_card hFτ
    omega
  obtain ⟨v, hvF, hvτ⟩ := Finset.not_subset.mp hnot
  refine ⟨v, ?_⟩
  simp only [HDXConc.linkVerts, Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨hvτ, hX.2.1.1 F hFX _ (Finset.insert_subset_iff.mpr ⟨hvF, hτF⟩)⟩

theorem mem_snoc_iff {X : Finset (Finset V)} {j : ℕ} (p : Fin j → V) (v : V) :
    Fin.snoc p v ∈ rootPaths X (j + 1) ↔
      p ∈ rootPaths X j ∧ v ∈ HDXConc.linkVerts X (prefixFace p j) := by
  simp only [rootPaths, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨hp, hfaces⟩
    obtain ⟨hpinj, hvrange⟩ := Fin.snoc_injective_iff.mp hp
    refine ⟨⟨hpinj, fun k hk => ?_⟩, ?_⟩
    · rw [← prefix_snoc_le p v hk]
      exact hfaces k (by omega)
    · simp only [HDXConc.linkVerts, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · simpa only [prefix_full, Finset.mem_image, Finset.mem_univ, true_and,
          Set.mem_range] using hvrange
      · rw [← prefix_snoc_full]
        exact hfaces (j + 1) le_rfl
  · rintro ⟨⟨hpinj, hfaces⟩, hv⟩
    have hv' : v ∉ prefixFace p j ∧ insert v (prefixFace p j) ∈ X := by
      simpa only [HDXConc.linkVerts, Finset.mem_filter, Finset.mem_univ, true_and] using hv
    refine ⟨Fin.snoc_injective_of_injective hpinj ?_, ?_⟩
    · simpa only [prefix_full, Finset.mem_image, Finset.mem_univ, true_and,
        Set.mem_range] using hv'.1
    · intro k hk
      by_cases hkj : k ≤ j
      · rw [prefix_snoc_le p v hkj]
        exact hfaces k hkj
      · have hk' : k = j + 1 := by omega
        rw [hk', prefix_snoc_full]
        exact hv'.2

def pathCost (θbar δ : Finset V → ℝ) {j : ℕ} (p : Fin j → V) : ℝ :=
  δ (prefixFace p j) * ∏ k ∈ Finset.range j, (1 - θbar (prefixFace p k))

theorem pathCost_snoc (θbar δ : Finset V → ℝ) {j : ℕ} (p : Fin j → V) (v : V) :
    pathCost θbar δ (Fin.snoc p v) =
      ((1 - θbar (prefixFace p j)) * δ (insert v (prefixFace p j))) *
        ∏ k ∈ Finset.range j, (1 - θbar (prefixFace p k)) := by
  unfold pathCost
  rw [prefix_snoc_full, Finset.prod_range_succ]
  have hprod : (∏ k ∈ Finset.range j, (1 - θbar (prefixFace (Fin.snoc p v) k))) =
      ∏ k ∈ Finset.range j, (1 - θbar (prefixFace p k)) := by
    apply Finset.prod_congr rfl
    intro k hk
    rw [prefix_snoc_le p v (Finset.mem_range.mp hk).le]
  rw [hprod, prefix_snoc_le p v le_rfl]
  ring

theorem retention_prod_nonneg {X : Finset (Finset V)} {d : ℕ}
    (θbar : Finset V → ℝ)
    (hθ : ∀ τ ∈ X, τ.card + 2 ≤ d → θbar τ < 1)
    {j : ℕ} (hj : j ≤ d - 1) (p : Fin j → V) (hp : p ∈ rootPaths X j) :
    0 ≤ ∏ k ∈ Finset.range j, (1 - θbar (prefixFace p k)) := by
  obtain ⟨hpinj, hfaces⟩ := (Finset.mem_filter.mp hp).2
  apply Finset.prod_nonneg
  intro k hk
  have hkj := Finset.mem_range.mp hk
  have hcard := prefix_card p hpinj hkj.le
  exact sub_nonneg.mpr (hθ _ (hfaces k hkj.le) (by omega)).le

theorem path_bounds_and_attainment {X : Finset (Finset V)} {d : ℕ}
    {w : Finset V → ℝ} (hX : WeightedComplex X d w)
    (θbar δ : Finset V → ℝ)
    (hθ : ∀ τ ∈ X, τ.card + 2 ≤ d → θbar τ < 1)
    (h83 : ∀ τ ∈ X, τ.card + 2 ≤ d →
      δ τ = (1 - θbar τ) * ⨅ i : HDXConc.linkVerts X τ, δ (insert (i : V) τ)) :
    ∀ j ≤ d - 1,
      (∀ p ∈ rootPaths X j, δ ∅ ≤ pathCost θbar δ p) ∧
        ∃ p ∈ rootPaths X j, pathCost θbar δ p = δ ∅ := by
  intro j
  induction j with
  | zero =>
    intro _
    refine ⟨fun p _ => ?_, Fin.elim0, ?_, ?_⟩
    · simp [pathCost]
    · simp only [rootPaths, Finset.mem_filter, Finset.mem_univ, true_and]
      refine ⟨Function.injective_of_subsingleton _, fun k hk => ?_⟩
      have hk0 : k = 0 := by omega
      simpa [hk0] using empty_mem hX
    · simp [pathCost]
  | succ j ih =>
    intro hj
    have hj' : j ≤ d - 1 := by omega
    obtain ⟨hbound, q, hq, hqcost⟩ := ih hj'
    have hface_card (p : Fin j → V) (hp : p ∈ rootPaths X j) :
        prefixFace p j ∈ X ∧ (prefixFace p j).card + 2 ≤ d := by
      obtain ⟨hpinj, hfaces⟩ := (Finset.mem_filter.mp hp).2
      refine ⟨hfaces j le_rfl, ?_⟩
      rw [prefix_card p hpinj le_rfl]
      have hd := hX.2.2.1
      omega
    refine ⟨?_, ?_⟩
    · intro p hp
      let p' := Fin.init p
      let v := p (Fin.last j)
      have hpsnoc : Fin.snoc p' v = p := Fin.snoc_init_self p
      obtain ⟨hp', hv⟩ := (mem_snoc_iff p' v).mp (hpsnoc.symm ▸ hp)
      obtain ⟨hτ, hτd⟩ := hface_card p' hp'
      have hr : 0 ≤ 1 - θbar (prefixFace p' j) := (sub_pos.mpr (hθ _ hτ hτd)).le
      have hδ : δ (prefixFace p' j) ≤
          (1 - θbar (prefixFace p' j)) * δ (insert v (prefixFace p' j)) := by
        rw [h83 _ hτ hτd]
        exact mul_le_mul_of_nonneg_left
          (ciInf_le (Finite.bddBelow_range
            (fun i : HDXConc.linkVerts X (prefixFace p' j) =>
              δ (insert (i : V) (prefixFace p' j)))) ⟨v, hv⟩) hr
      calc
        δ ∅ ≤ pathCost θbar δ p' := hbound p' hp'
        _ ≤ pathCost θbar δ (Fin.snoc p' v) := by
          rw [pathCost_snoc]
          exact mul_le_mul_of_nonneg_right hδ (retention_prod_nonneg θbar hθ hj' p' hp')
        _ = pathCost θbar δ p := congrArg _ hpsnoc
    · obtain ⟨hτ, hτd⟩ := hface_card q hq
      obtain ⟨v, hv, hmin⟩ := Finset.exists_min_image
        (HDXConc.linkVerts X (prefixFace q j)) (fun v => δ (insert v (prefixFace q j)))
        (link_nonempty hX hτ (by omega))
      letI : Nonempty (HDXConc.linkVerts X (prefixFace q j)) := ⟨⟨v, hv⟩⟩
      have hmin_eq : (⨅ i : HDXConc.linkVerts X (prefixFace q j),
          δ (insert (i : V) (prefixFace q j))) = δ (insert v (prefixFace q j)) := by
        apply le_antisymm (ciInf_le (Finite.bddBelow_range
          (fun i : HDXConc.linkVerts X (prefixFace q j) =>
            δ (insert (i : V) (prefixFace q j)))) ⟨v, hv⟩)
        exact le_ciInf fun i => hmin i i.2
      refine ⟨Fin.snoc q v, (mem_snoc_iff q v).mpr ⟨hq, hv⟩, ?_⟩
      rw [pathCost_snoc, ← hmin_eq, ← h83 _ hτ hτd]
      exact hqcost

end ROLDescent.PathProof

namespace ROLDescent

theorem path_expansion_proof {V : Type*} [Fintype V] [DecidableEq V]
    (X : Finset (Finset V)) (d : ℕ) (w : Finset V → ℝ) (hX : WeightedComplex X d w)
    (θbar δ : Finset V → ℝ)
    (hθ : ∀ τ ∈ X, τ.card + 2 ≤ d → θbar τ < 1)
    (h83 : ∀ τ ∈ X, τ.card + 2 ≤ d →
      δ τ = (1 - θbar τ) * ⨅ i : HDXConc.linkVerts X τ, δ (insert (i : V) τ)) :
    ∀ j ≤ d - 1, δ ∅ = ⨅ p : rootPaths X j,
      δ (prefixFace p.1 j) * ∏ k ∈ Finset.range j, (1 - θbar (prefixFace p.1 k)) := by
  intro j hj
  obtain ⟨hbound, p, hp, hattain⟩ :=
    PathProof.path_bounds_and_attainment hX θbar δ hθ h83 j hj
  letI : Nonempty (rootPaths X j) := ⟨⟨p, hp⟩⟩
  exact le_antisymm (le_ciInf fun p => hbound p p.2)
    (ciInf_le_of_le (Finite.bddBelow_range _) ⟨p, hp⟩ hattain.le)

end ROLDescent



open ROLDescent

theorem solution {V : Type*} [Fintype V] [DecidableEq V]
    (X : Finset (Finset V)) (d : ℕ) (w : Finset V → ℝ) (hX : WeightedComplex X d w)
    (θbar δ : Finset V → ℝ)
    (hθ : ∀ τ ∈ X, τ.card + 2 ≤ d → θbar τ < 1)
    (h83 : ∀ τ ∈ X, τ.card + 2 ≤ d →
      δ τ = (1 - θbar τ) * ⨅ i : HDXConc.linkVerts X τ, δ (insert (i : V) τ)) :
    ∀ j ≤ d - 1, δ ∅ = ⨅ p : rootPaths X j,
      δ (prefixFace p.1 j) * ∏ k ∈ Finset.range j, (1 - θbar (prefixFace p.1 k)) := by
  exact ROLDescent.path_expansion_proof X d w hX θbar δ hθ h83

#print axioms solution
