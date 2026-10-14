-- Prove2me | solution 1 for SingleMachinePrec.VariableCost.heavy_subgraph_iso
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-13T03:10:14.560329+00:00
-- url     : https://prove2.me/submissions/4c4c4f32-72cb-4220-a257-fab790fee2ad

import Mathlib
import Definitions.Def_SingleMachinePrec_VariableCost_AdjacencyInstance
open scoped NNReal


namespace SingleMachinePrec.VariableCost

open Classical

lemma e51_weight_cases {n : ℕ} (G : SimpleGraph (Fin n)) (k : ℝ≥0)
    (u : IncPair (adjacencyInstance G k).P) :
    vertexWeight (adjacencyInstance G k) u = 0 ∨
      ∃ i j : Fin n, u.1 = (Sum.inl i, Sum.inr j) ∧ j ≤ i ∧
        vertexWeight (adjacencyInstance G k) u = (k : ℝ) ^ ((j : ℕ) + 1) / (k : ℝ) ^ ((i : ℕ) + 1) := by
  obtain ⟨⟨x, y⟩, h⟩ := u
  rcases x with i | i <;> rcases y with j | j
  · left; simp [vertexWeight, adjacencyInstance]
  · right
    refine ⟨i, j, rfl, ?_, ?_⟩
    · by_contra hji
      apply h.1
      show adjPrec G (Sum.inl i) (Sum.inr j)
      exact Or.inr ⟨i, j, rfl, rfl, Or.inr (not_le.mp hji)⟩
    · simp [vertexWeight, adjacencyInstance, div_eq_inv_mul]
  · left; simp [vertexWeight, adjacencyInstance]
  · left; simp [vertexWeight, adjacencyInstance]

lemma e51_vw_nonneg {n : ℕ} (G : SimpleGraph (Fin n)) (k : ℝ≥0)
    (u : IncPair (adjacencyInstance G k).P) : 0 ≤ vertexWeight (adjacencyInstance G k) u :=
  mul_nonneg ((adjacencyInstance G k).p_nonneg _) ((adjacencyInstance G k).w_nonneg _)

lemma e51_heavy_inj {n : ℕ} (G : SimpleGraph (Fin n)) (k : ℝ≥0) {i j : Fin n} :
    heavy G k i = heavy G k j ↔ i = j := by
  constructor
  · intro h
    have := congrArg (fun u : IncPair (adjacencyInstance G k).P => u.1.1) h
    simpa [heavy] using this
  · rintro rfl; rfl

lemma e51_heavy_weight {n : ℕ} (G : SimpleGraph (Fin n)) (k : ℝ≥0) (hk : 1 ≤ k) (i : Fin n) :
    vertexWeight (adjacencyInstance G k) (heavy G k i) = 1 := by
  have hk0 : (k : ℝ) ≠ 0 := by
    have : (1 : ℝ) ≤ k := by exact_mod_cast hk
    linarith
  simp [vertexWeight, heavy, adjacencyInstance]
  field_simp

lemma e51_light_le {n : ℕ} (G : SimpleGraph (Fin n)) (k : ℝ≥0) (hk : 1 ≤ k)
    (u : IncPair (adjacencyInstance G k).P) (hu : ∀ i : Fin n, u ≠ heavy G k i) :
    vertexWeight (adjacencyInstance G k) u ≤ 1 / (k : ℝ) := by
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hk0 : (0 : ℝ) < k := by linarith
  rcases e51_weight_cases G k u with h0 | ⟨i, j, hu1, hji, hv⟩
  · rw [h0]; positivity
  · have hne : j ≠ i := by
      rintro rfl
      apply hu j
      apply Subtype.ext
      simp [heavy, hu1]
    have hlt : j < i := lt_of_le_of_ne hji hne
    rw [hv, div_le_div_iff₀ (by positivity) hk0]
    have h2 : (k : ℝ) ^ ((j : ℕ) + 1) * k ≤ 1 * (k : ℝ) ^ ((i : ℕ) + 1) := by
      rw [← pow_succ, one_mul]
      exact pow_le_pow_right₀ hk1 (by have := Fin.lt_def.mp hlt; omega)
    exact h2

lemma e51_light_weight {n : ℕ} (G : SimpleGraph (Fin n)) (k : ℝ≥0) (hk : 1 ≤ k) :
    weight (adjacencyInstance G k)
        (Finset.univ.filter (fun u => ∀ i : Fin n, u ≠ heavy G k i)) ≤
      (n : ℝ) ^ 2 / (k : ℝ) := by
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hk0 : (0 : ℝ) < k := by linarith
  unfold weight
  set T := Finset.univ.filter (fun u : IncPair (adjacencyInstance G k).P => ∀ i : Fin n, u ≠ heavy G k i) with hT
  have h1 : ∑ u ∈ T, vertexWeight (adjacencyInstance G k) u =
      ∑ u ∈ T.filter (fun u => vertexWeight (adjacencyInstance G k) u ≠ 0),
        vertexWeight (adjacencyInstance G k) u := by
    rw [Finset.sum_filter_ne_zero]
  rw [h1]
  set T' := T.filter (fun u => vertexWeight (adjacencyInstance G k) u ≠ 0) with hT'
  have hcard : T'.card ≤ n ^ 2 := by
    have := Finset.card_le_card_of_injOn
      (s := T') (t := (Finset.univ : Finset (Fin n × Fin n)))
      (fun u : IncPair (adjacencyInstance G k).P => (Sum.elim id id u.1.1, Sum.elim id id u.1.2))
      (fun _ _ => Finset.mem_univ _) ?_
    · simpa [sq] using this
    · intro u hu v hv huv
      have hu' := (Finset.mem_filter.mp hu).2
      have hv' := (Finset.mem_filter.mp hv).2
      rcases e51_weight_cases G k u with h0 | ⟨i, j, hu1, -, -⟩
      · exact absurd h0 hu'
      rcases e51_weight_cases G k v with h0 | ⟨i', j', hv1, -, -⟩
      · exact absurd h0 hv'
      apply Subtype.ext
      simp only [hu1, hv1, Sum.elim_inl, Sum.elim_inr, id, Prod.mk.injEq] at huv
      obtain ⟨rfl, rfl⟩ := huv
      rw [hu1, hv1]
  calc ∑ u ∈ T', vertexWeight (adjacencyInstance G k) u
      ≤ ∑ u ∈ T', 1 / (k : ℝ) := by
        apply Finset.sum_le_sum
        intro u hu
        exact e51_light_le G k hk u (Finset.mem_filter.mp (Finset.mem_filter.mp hu).1).2
    _ = (T'.card : ℝ) * (1 / (k : ℝ)) := by simp
    _ ≤ ((n ^ 2 : ℕ) : ℝ) * (1 / (k : ℝ)) := by
        apply mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) (by positivity)
    _ = (n : ℝ) ^ 2 / (k : ℝ) := by push_cast; ring

theorem e51_light_core {n : ℕ} (G : SimpleGraph (Fin n)) (k : ℝ≥0) (hk : 1 ≤ k) :
    (∀ i : Fin n, vertexWeight (adjacencyInstance G k) (heavy G k i) = 1) ∧
    (∀ u : IncPair (adjacencyInstance G k).P, (∀ i : Fin n, u ≠ heavy G k i) →
      vertexWeight (adjacencyInstance G k) u ≤ 1 / (k : ℝ)) ∧
    weight (adjacencyInstance G k)
        (Finset.univ.filter (fun u => ∀ i : Fin n, u ≠ heavy G k i)) ≤
      (n : ℝ) ^ 2 / (k : ℝ) :=
  ⟨e51_heavy_weight G k hk, e51_light_le G k hk, e51_light_weight G k hk⟩

lemma e51_heavy_csRule {n : ℕ} (G : SimpleGraph (Fin n)) (k : ℝ≥0) (i j : Fin n) :
    csRule (adjacencyInstance G k).P (heavy G k i) (heavy G k j) ↔ G.Adj i j := by
  constructor
  · rintro (⟨h, _⟩ | ⟨h, _⟩ | ⟨h1, h2⟩)
    · exact absurd h (by simp [heavy])
    · exact absurd h (by simp [heavy])
    · have h1' : adjPrec G (Sum.inl i) (Sum.inr j) := h1
      have h2' : adjPrec G (Sum.inl j) (Sum.inr i) := h2
      rcases h1' with h | ⟨a, b, ha, hb, hh⟩
      · exact absurd h (by simp)
      rcases h2' with h' | ⟨a', b', ha', hb', hh'⟩
      · exact absurd h' (by simp)
      cases ha; cases hb; cases ha'; cases hb'
      rcases hh with hh | hh
      · exact hh
      rcases hh' with hh' | hh'
      · exact hh'.symm
      · exact absurd hh (not_lt.mpr hh'.le)
  · intro h
    right; right
    exact ⟨Or.inr ⟨i, j, rfl, rfl, Or.inl h⟩, Or.inr ⟨j, i, rfl, rfl, Or.inl h.symm⟩⟩

lemma e51_heavy_adj {n : ℕ} (G : SimpleGraph (Fin n)) (k : ℝ≥0) (i j : Fin n) :
    (vertexCoverGraph (adjacencyInstance G k).P).Adj (heavy G k i) (heavy G k j) ↔ G.Adj i j := by
  constructor
  · rintro ⟨_, h | h⟩
    · exact (e51_heavy_csRule G k i j).1 h
    · exact ((e51_heavy_csRule G k j i).1 h).symm
  · intro h
    refine ⟨?_, Or.inl ((e51_heavy_csRule G k i j).2 h)⟩
    intro heq
    exact G.ne_of_adj h ((e51_heavy_inj G k).1 heq)

lemma e51_eq_heavy {n : ℕ} (G : SimpleGraph (Fin n)) (k : ℝ≥0) (hk : 1 < k)
    (u : IncPair (adjacencyInstance G k).P) (hu : vertexWeight (adjacencyInstance G k) u = 1) :
    ∃ i, u = heavy G k i := by
  have hk' : (1 : ℝ) < k := by exact_mod_cast hk
  have hk0 : (0 : ℝ) < k := by linarith
  rcases e51_weight_cases G k u with h0 | ⟨i, j, hu1, hji, hv⟩
  · rw [h0] at hu; exact absurd hu zero_ne_one
  · have hpow : (k : ℝ) ^ ((j : ℕ) + 1) = (k : ℝ) ^ ((i : ℕ) + 1) := by
      rw [hv, div_eq_one_iff_eq (by positivity)] at hu
      exact hu
    have := (pow_right_inj₀ hk0 hk'.ne').1 hpow
    have hji' : j = i := Fin.ext (by omega)
    subst hji'
    refine ⟨j, Subtype.ext ?_⟩
    simp [heavy, hu1]

theorem e51_iso_core {n : ℕ} (G : SimpleGraph (Fin n)) (k : ℝ≥0) :
    (∀ i j : Fin n,
      (vertexCoverGraph (adjacencyInstance G k).P).Adj (heavy G k i) (heavy G k j) ↔
        G.Adj i j) ∧
    (1 < k →
      ∃ f : (vertexCoverGraph (adjacencyInstance G k).P).induce
          {u | vertexWeight (adjacencyInstance G k) u = 1} ≃g G,
        ∀ (i : Fin n) (h : heavy G k i ∈ {u | vertexWeight (adjacencyInstance G k) u = 1}),
          f ⟨heavy G k i, h⟩ = i) := by
  refine ⟨fun i j => e51_heavy_adj G k i j, fun hk => ?_⟩
  have hmem : ∀ i, heavy G k i ∈ {u | vertexWeight (adjacencyInstance G k) u = 1} :=
    fun i => e51_heavy_weight G k hk.le i
  let g : Fin n → ({u | vertexWeight (adjacencyInstance G k) u = 1} :
      Set (IncPair (adjacencyInstance G k).P)) := fun i => ⟨heavy G k i, hmem i⟩
  have hbij : Function.Bijective g := by
    refine ⟨fun a b h => (e51_heavy_inj G k).1 (congrArg Subtype.val h), ?_⟩
    rintro ⟨u, hu⟩
    obtain ⟨i, rfl⟩ := e51_eq_heavy G k hk u hu
    exact ⟨i, rfl⟩
  let e := Equiv.ofBijective g hbij
  let iso : G ≃g (vertexCoverGraph (adjacencyInstance G k).P).induce
      {u | vertexWeight (adjacencyInstance G k) u = 1} :=
    ⟨e, by
      intro a b
      show (vertexCoverGraph (adjacencyInstance G k).P).Adj (heavy G k a) (heavy G k b) ↔ G.Adj a b
      exact e51_heavy_adj G k a b⟩
  refine ⟨iso.symm, fun i h => ?_⟩
  exact (Equiv.symm_apply_eq e).2 rfl

lemma e51_exists_cover {n : ℕ} (G : SimpleGraph (Fin n)) :
    ∃ D : Finset (Fin n), G.IsVertexCover (D : Set (Fin n)) ∧
      (D.card : ℝ) = (G.vertexCoverNum.toNat : ℝ) := by
  obtain ⟨s, hs1, hs2⟩ := SimpleGraph.vertexCoverNum_exists G
  refine ⟨s.toFinset, by simpa using hs2, ?_⟩
  have : (s.toFinset.card : ℕ) = G.vertexCoverNum.toNat := by
    rw [← hs1, ← Set.ncard_eq_toFinset_card', Set.ncard_def]
  exact_mod_cast this

lemma e51_min_le {n : ℕ} (G : SimpleGraph (Fin n)) (k : ℝ≥0) (hk : 1 ≤ k) :
    minCoverWeight (adjacencyInstance G k) ≤
      (G.vertexCoverNum.toNat : ℝ) + (n : ℝ) ^ 2 / (k : ℝ) := by
  obtain ⟨D, hD, hDc⟩ := e51_exists_cover G
  set L := Finset.univ.filter (fun u : IncPair (adjacencyInstance G k).P => ∀ i : Fin n, u ≠ heavy G k i)
    with hL
  set C' := D.image (heavy G k) ∪ L with hC'
  have hcov : (vertexCoverGraph (adjacencyInstance G k).P).IsVertexCover (C' : Set _) := by
    intro u v huv
    by_cases hu : ∀ i, u ≠ heavy G k i
    · left; simp [hC', hL, hu]
    by_cases hv : ∀ i, v ≠ heavy G k i
    · right; simp [hC', hL, hv]
    push_neg at hu hv
    obtain ⟨i, rfl⟩ := hu
    obtain ⟨j, rfl⟩ := hv
    have hadj := (e51_heavy_adj G k i j).1 huv
    rcases hD hadj with h | h
    · left; simp only [hC', Finset.coe_union, Finset.coe_image, Set.mem_union, Set.mem_image,
        Finset.mem_coe]
      exact Or.inl ⟨i, by simpa using h, rfl⟩
    · right; simp only [hC', Finset.coe_union, Finset.coe_image, Set.mem_union, Set.mem_image,
        Finset.mem_coe]
      exact Or.inl ⟨j, by simpa using h, rfl⟩
  have hdisj : Disjoint (D.image (heavy G k)) L := by
    rw [Finset.disjoint_left]
    intro u hu hu2
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hu
    exact (Finset.mem_filter.mp hu2).2 i rfl
  have hw : weight (adjacencyInstance G k) C' =
      (D.card : ℝ) + weight (adjacencyInstance G k) L := by
    unfold weight
    rw [hC', Finset.sum_union hdisj, Finset.sum_image (fun a _ b _ h => (e51_heavy_inj G k).1 h)]
    simp [e51_heavy_weight G k hk]
  calc minCoverWeight (adjacencyInstance G k) ≤ weight (adjacencyInstance G k) C' := by
        unfold minCoverWeight
        apply Finset.inf'_le
        simpa using hcov
    _ = _ := hw
    _ ≤ _ := by
        rw [hDc]
        exact add_le_add le_rfl (e51_light_weight G k hk)

theorem e51_goal_core {n : ℕ} (G : SimpleGraph (Fin n)) (r ε : ℝ) (k : ℝ≥0)
    (hr : 1 ≤ r) (hε : 0 < ε) (hk1 : 1 ≤ k) (hk : (n : ℝ) ^ 2 * r / ε < (k : ℝ))
    (C : Finset (IncPair (adjacencyInstance G k).P))
    (hC : (vertexCoverGraph (adjacencyInstance G k).P).IsVertexCover (C : Set _))
    (hCr : weight (adjacencyInstance G k) C ≤ r * minCoverWeight (adjacencyInstance G k)) :
    G.IsVertexCover {i | heavy G k i ∈ C} ∧
    ((Finset.univ.filter (fun i => heavy G k i ∈ C)).card : ℝ) ≤
      r * ((G.vertexCoverNum.toNat : ℝ) + (n : ℝ) ^ 2 / (k : ℝ)) ∧
    (G.edgeSet.Nonempty →
      ((Finset.univ.filter (fun i => heavy G k i ∈ C)).card : ℝ) ≤
          r * (1 + (n : ℝ) ^ 2 / (k : ℝ)) * (G.vertexCoverNum.toNat : ℝ) ∧
        r * (1 + (n : ℝ) ^ 2 / (k : ℝ)) * (G.vertexCoverNum.toNat : ℝ) <
          (r + ε) * (G.vertexCoverNum.toNat : ℝ)) := by
  have hr0 : 0 ≤ r := by linarith
  have hk0 : (0 : ℝ) < k := by
    have : 0 ≤ (n : ℝ) ^ 2 * r / ε := by positivity
    linarith
  have hq : 0 ≤ (n : ℝ) ^ 2 / (k : ℝ) := by positivity
  have hcover : G.IsVertexCover {i | heavy G k i ∈ C} := by
    intro i j hij
    have := hC ((e51_heavy_adj G k i j).2 hij)
    simpa using this
  have hcard : ((Finset.univ.filter (fun i => heavy G k i ∈ C)).card : ℝ) ≤
      weight (adjacencyInstance G k) C := by
    set F := Finset.univ.filter (fun i => heavy G k i ∈ C) with hF
    have h1 : ∑ u ∈ F.image (heavy G k), vertexWeight (adjacencyInstance G k) u = (F.card : ℝ) := by
      rw [Finset.sum_image (fun a _ b _ h => (e51_heavy_inj G k).1 h)]
      simp [e51_heavy_weight G k hk1]
    rw [← h1]
    unfold weight
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro u hu
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hu
      simpa [hF] using hi
    · intro u _ _
      exact e51_vw_nonneg G k u
  have h2 : ((Finset.univ.filter (fun i => heavy G k i ∈ C)).card : ℝ) ≤
      r * ((G.vertexCoverNum.toNat : ℝ) + (n : ℝ) ^ 2 / (k : ℝ)) :=
    hcard.trans (hCr.trans (mul_le_mul_of_nonneg_left (e51_min_le G k hk1) hr0))
  refine ⟨hcover, h2, fun hne => ?_⟩
  obtain ⟨D, hD, hDc⟩ := e51_exists_cover G
  have hτ : (1 : ℝ) ≤ (G.vertexCoverNum.toNat : ℝ) := by
    rw [← hDc]
    obtain ⟨e, he⟩ := hne
    induction e using Sym2.ind with
    | _ a b =>
      have hab : G.Adj a b := by simpa using he
      have : a ∈ D ∨ b ∈ D := by simpa using hD hab
      have hpos : 0 < D.card := by
        rcases this with h | h
        · exact Finset.card_pos.mpr ⟨a, h⟩
        · exact Finset.card_pos.mpr ⟨b, h⟩
      exact_mod_cast hpos
  set τ := (G.vertexCoverNum.toNat : ℝ) with hτdef
  set q := (n : ℝ) ^ 2 / (k : ℝ) with hqdef
  refine ⟨h2.trans ?_, ?_⟩
  · have : 0 ≤ r * q * (τ - 1) := mul_nonneg (mul_nonneg hr0 hq) (by linarith)
    nlinarith
  · have hrq : r * q < ε := by
      rw [hqdef, ← mul_div_assoc, div_lt_iff₀ hk0]
      rw [div_lt_iff₀ hε] at hk
      linarith
    have : r * q * τ < ε * τ := mul_lt_mul_of_pos_right hrq (by linarith)
    nlinarith

end SingleMachinePrec.VariableCost

open SingleMachinePrec.VariableCost


theorem solution {n : ℕ} (G : SimpleGraph (Fin n)) (k : ℝ≥0) :
    (∀ i j : Fin n,
      (vertexCoverGraph (adjacencyInstance G k).P).Adj (heavy G k i) (heavy G k j) ↔
        G.Adj i j) ∧
    (1 < k →
      ∃ f : (vertexCoverGraph (adjacencyInstance G k).P).induce
          {u | vertexWeight (adjacencyInstance G k) u = 1} ≃g G,
        ∀ (i : Fin n) (h : heavy G k i ∈ {u | vertexWeight (adjacencyInstance G k) u = 1}),
          f ⟨heavy G k i, h⟩ = i) := by
  exact e51_iso_core G k
