-- Prove2me | solution 1 for PerfectGraph.gasparian
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T10:39:19.121575+00:00
-- url     : https://prove2.me/submissions/5111f967-85aa-44a8-923d-bcd6fd0dfd23

module
public import Mathlib
public import Definitions.Def_PerfectLib_Gasparian
public import Theorems.Thm_PerfectGraph_card_le_cliqueNum_induce
public import Theorems.Thm_PerfectGraph_exists_clique_card_eq_cliqueNum_induce
public import Theorems.Thm_PerfectGraph_card_le_indepNum_induce
public import Theorems.Thm_PerfectGraph_exists_indepSet_card_eq_indepNum_induce
public import Theorems.Thm_PerfectGraph_cliqueNum_induce_mono
public import Theorems.Thm_PerfectGraph_card_inter_le_one
public import Theorems.Thm_PerfectGraph_sum_indicator_eq_card

set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph Finset
open PerfectGraph
variable {V : Type*} (G : SimpleGraph V)
namespace PerfectGraph
theorem _root_.solution [Finite V] {S : Finset V}
    (hnot : ¬ IsColOn G S (G.induce (S : Set V)).cliqueNum)
    (hmin : ∀ T ⊂ S, IsColOn G T (G.induce (T : Set V)).cliqueNum) :
    (G.induce (S : Set V)).indepNum * (G.induce (S : Set V)).cliqueNum + 1 ≤ S.card := by
  classical
  set ω := (G.induce (S : Set V)).cliqueNum with hω
  set α := (G.induce (S : Set V)).indepNum with hα
  have hSne : S.Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty] at h
    subst h
    exact hnot ⟨fun _ => 0, by simp, by simp⟩
  obtain ⟨v0, hv0⟩ := hSne
  have hω1 : 1 ≤ ω := by
    have := card_le_cliqueNum_induce G (Finset.singleton_subset_iff.2 hv0) (by simp)
    simpa using this
  have hα1 : 1 ≤ α := by
    have := card_le_indepNum_induce G (Finset.singleton_subset_iff.2 hv0) (by simp)
    simpa using this
  -- (b): every independent set misses some maximum clique
  have hb : ∀ A ⊆ S, G.IsIndepSet (A : Set V) →
      ∃ C ⊆ S, G.IsClique (C : Set V) ∧ C.card = ω ∧ Disjoint C A := by
    intro A hAS hA
    by_cases hA0 : A = ∅
    · subst hA0
      obtain ⟨K, hKS, hK, hc⟩ := exists_clique_card_eq_cliqueNum_induce G S
      exact ⟨K, hKS, hK, hc, Finset.disjoint_empty_right _⟩
    · have hT : S \ A ⊂ S := Finset.sdiff_ssubset hAS (Finset.nonempty_iff_ne_empty.2 hA0)
      obtain ⟨c, hc, hcv⟩ := hmin _ hT
      have hge : ω ≤ (G.induce ((S \ A : Finset V) : Set V)).cliqueNum := by
        by_contra hlt
        push Not at hlt
        apply hnot
        refine ⟨fun v => if v ∈ A then ω - 1 else c v, ?_, ?_⟩
        · intro v hv
          beta_reduce
          split_ifs with h
          · omega
          · have := hc v (Finset.mem_sdiff.2 ⟨hv, h⟩)
            omega
        · intro u hu v hv huv
          beta_reduce
          split_ifs with h1 h2 h2
          · exact absurd huv (hA h1 h2 (G.ne_of_adj huv))
          · have := hc v (Finset.mem_sdiff.2 ⟨hv, h2⟩)
            omega
          · have := hc u (Finset.mem_sdiff.2 ⟨hu, h1⟩)
            omega
          · exact hcv u (Finset.mem_sdiff.2 ⟨hu, h1⟩) v (Finset.mem_sdiff.2 ⟨hv, h2⟩) huv
      obtain ⟨K, hKT, hK, hcK⟩ := exists_clique_card_eq_cliqueNum_induce G (S \ A)
      have hle := cliqueNum_induce_mono G (Finset.sdiff_subset : S \ A ⊆ S)
      exact ⟨K, hKT.trans Finset.sdiff_subset, hK, by omega,
        Finset.disjoint_of_subset_left hKT Finset.sdiff_disjoint⟩
  -- (a): colourings of `S - v` with `ω` colours
  have ha : ∀ v ∈ S, ∃ c : V → ℕ, (∀ u ∈ S.erase v, c u < ω) ∧
      ∀ u ∈ S.erase v, ∀ w ∈ S.erase v, G.Adj u w → c u ≠ c w := by
    intro v hv
    obtain ⟨c, hc, hcv⟩ := hmin _ (Finset.erase_ssubset hv)
    exact ⟨c, fun u hu => (hc u hu).trans_le
      (cliqueNum_induce_mono G (Finset.erase_subset _ _)), hcv⟩
  choose col hcol hcolv using ha
  obtain ⟨A0, hA0S, hA0, hA0c⟩ := exists_indepSet_card_eq_indepNum_induce G S
  let Aset : Option (A0 × Fin ω) → Finset V := fun j => j.elim A0
    (fun p => (S.erase p.1).filter (fun u => col p.1 (hA0S p.1.2) u = p.2))
  have hAS : ∀ j, Aset j ⊆ S := by
    rintro (_ | ⟨v, k⟩)
    · exact hA0S
    · exact (Finset.filter_subset _ _).trans (Finset.erase_subset _ _)
  have hAind : ∀ j, G.IsIndepSet (Aset j : Set V) := by
    rintro (_ | ⟨v, k⟩)
    · exact hA0
    · intro u hu w hw _ huw
      simp only [Aset, Option.elim, Finset.coe_filter, Set.mem_ofPred_eq] at hu hw
      exact hcolv v (hA0S v.2) u hu.1 w hw.1 huw (hu.2.trans hw.2.symm)
  choose C hCS hC hCc hCd using fun j => hb (Aset j) (hAS j) (hAind j)
  -- (d): counting
  have hsum : ∀ K ⊆ S, G.IsClique (K : Set V) → K.card = ω →
      ∑ j, (K ∩ Aset j).card = α * ω := by
    intro K hKS hK hKc
    rw [Fintype.sum_option, Fintype.sum_prod_type]
    have h1 : ∀ v : A0, ∑ k : Fin ω, (K ∩ Aset (some (v, k))).card = (K.erase v).card := by
      intro v
      change ∑ k : Fin ω, (K ∩ (S.erase v).filter (fun u => col v (hA0S v.2) u = k)).card = _
      rw [Fin.sum_univ_eq_sum_range (fun k => (K ∩ (S.erase v).filter
        (fun u => col v (hA0S v.2) u = k)).card) ω]
      rw [Finset.card_eq_sum_card_fiberwise (f := col v (hA0S v.2)) (s := K.erase v)
        (t := Finset.range ω)]
      · apply Finset.sum_congr rfl
        intro k _
        congr 1
        ext u
        simp only [Finset.mem_inter, Finset.mem_filter, Finset.mem_erase]
        constructor
        · rintro ⟨huK, ⟨huv, -⟩, hk⟩
          exact ⟨⟨huv, huK⟩, hk⟩
        · rintro ⟨⟨huv, huK⟩, hk⟩
          exact ⟨huK, ⟨huv, hKS huK⟩, hk⟩
      · intro u hu
        exact Finset.mem_range.2 (hcol v (hA0S v.2) u (Finset.erase_subset_erase _ hKS hu))
    simp only [h1]
    have h2 : ∀ v : A0, (K.erase v).card + (if (v : V) ∈ K then 1 else 0) = ω := by
      intro v
      split_ifs with h
      · rw [Finset.card_erase_add_one h, hKc]
      · rw [Finset.erase_eq_of_notMem h, hKc, add_zero]
    have h3 : (K ∩ Aset none).card = ∑ v : A0, (if (v : V) ∈ K then 1 else 0) := by
      rw [Finset.sum_coe_sort A0 (fun v => if v ∈ K then 1 else 0), Finset.sum_boole,
        Finset.filter_mem_eq_inter, Finset.inter_comm]
      simp [Aset]
    rw [h3, add_comm, ← Finset.sum_add_distrib, Finset.sum_congr rfl (fun v _ => h2 v),
      Finset.sum_const, Finset.card_univ, Fintype.card_coe, hA0c, smul_eq_mul]
  have hcardι : Fintype.card (Option (A0 × Fin ω)) = α * ω + 1 := by
    rw [Fintype.card_option, Fintype.card_prod, Fintype.card_coe, Fintype.card_fin, hA0c]
  have hone : ∀ j i, i ≠ j → (C j ∩ Aset i).card = 1 := by
    intro j i hij
    have hs := hsum (C j) (hCS j) (hC j) (hCc j)
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j),
      Finset.disjoint_iff_inter_eq_empty.1 (hCd j), Finset.card_empty, zero_add] at hs
    by_contra hne
    have hlt : ∑ x ∈ Finset.univ.erase j, (C j ∩ Aset x).card <
        ∑ x ∈ Finset.univ.erase j, 1 := by
      apply Finset.sum_lt_sum
      · intro x _
        exact card_inter_le_one G (hC j) (hAind x)
      · refine ⟨i, Finset.mem_erase.2 ⟨hij, Finset.mem_univ _⟩, ?_⟩
        have := card_inter_le_one G (hC j) (hAind i)
        omega
    rw [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
      hcardι, smul_eq_mul, mul_one] at hlt
    omega
  -- (e): linear algebra
  let M : Matrix (Option (A0 × Fin ω)) S ℚ := Matrix.of fun i u => if (u : V) ∈ Aset i then 1 else 0
  let N : Matrix S (Option (A0 × Fin ω)) ℚ := Matrix.of fun u j => if (u : V) ∈ C j then 1 else 0
  let J : Matrix (Option (A0 × Fin ω)) (Option (A0 × Fin ω)) ℚ := Matrix.of fun _ _ => 1
  have hMN : M * N = J - 1 := by
    ext i j
    simp only [Matrix.mul_apply, M, N, J, Matrix.of_apply, Matrix.sub_apply, Matrix.one_apply,
      mul_ite, mul_one, mul_zero, ← ite_and]
    have : ∀ u : S, ((u : V) ∈ C j ∧ (u : V) ∈ Aset i) ↔ (u : V) ∈ Aset i ∩ C j := by
      intro u
      rw [Finset.mem_inter, and_comm]
    simp only [this]
    rw [sum_indicator_eq_card (Finset.inter_subset_left.trans (hAS i))]
    split_ifs with h
    · subst h
      rw [Finset.inter_comm, Finset.disjoint_iff_inter_eq_empty.1 (hCd i)]
      simp
    · rw [Finset.inter_comm, hone j i h]
      simp
  set m : ℚ := (Fintype.card (Option (A0 × Fin ω)) : ℚ) with hm
  have hJJ : J * J = m • J := by
    ext i j
    simp [J, Matrix.mul_apply, hm]
  have hm1 : m - 1 ≠ 0 := by
    rw [hm, hcardι]
    have : (1 : ℚ) ≤ α * ω := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (by positivity)
    push_cast
    intro h
    nlinarith
  have hinv : (J - 1) * ((m - 1)⁻¹ • J - 1) = 1 := by
    have hc : (m - 1)⁻¹ * m = 1 + (m - 1)⁻¹ := by
      field_simp
      ring
    rw [sub_mul, mul_sub, mul_sub, Matrix.mul_smul, hJJ, smul_smul, hc, add_smul, one_smul,
      mul_one, one_mul, one_mul]
    abel
  have hrank : Fintype.card (Option (A0 × Fin ω)) ≤ Fintype.card S := by
    calc Fintype.card (Option (A0 × Fin ω))
        = (1 : Matrix (Option (A0 × Fin ω)) (Option (A0 × Fin ω)) ℚ).rank :=
          (Matrix.rank_one).symm
      _ = (M * N * ((m - 1)⁻¹ • J - 1)).rank := by rw [hMN, hinv]
      _ ≤ (M * N).rank := Matrix.rank_mul_le_left _ _
      _ ≤ M.rank := Matrix.rank_mul_le_left _ _
      _ ≤ Fintype.card S := Matrix.rank_le_card_width _
  rw [hcardι, Fintype.card_coe] at hrank
  exact hrank
end PerfectGraph
