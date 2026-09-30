-- Prove2me | solution 1 for SupplyChainTheory.mst_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-25T20:42:32.661773+00:00
-- url     : https://prove2.me/submissions/6fdd2d12-e62f-472c-a2c5-08097568d600

import Mathlib
import Definitions.Def_SupplyChainTheory_tsp

open Classical SupplyChainTheory

/-! ### The Hamiltonian path `τ 0 – τ 1 – ⋯ – τ m` of a tour on `Fin (m + 1)` -/

private lemma rot_castSucc {m : ℕ} (i : Fin m) : finRotate (m + 1) i.castSucc = i.succ :=
  finRotate_of_lt i.isLt

/-- The tour `τ` with its closing edge `{τ m, τ 0}` removed. -/
private def pathG {m : ℕ} (τ : Equiv.Perm (Fin (m + 1))) : SimpleGraph (Fin (m + 1)) where
  Adj u v := ∃ i : Fin m, (u = τ i.castSucc ∧ v = τ i.succ) ∨ (v = τ i.castSucc ∧ u = τ i.succ)
  symm := ⟨fun _ _ ⟨i, h⟩ => ⟨i, h.symm⟩⟩
  loopless := ⟨by
    rintro u ⟨i, ⟨h1, h2⟩ | ⟨h1, h2⟩⟩ <;>
    · have := τ.injective (h1.symm.trans h2)
      exact absurd this Fin.castSucc_lt_succ.ne⟩

private lemma pathG_adj {m : ℕ} (τ : Equiv.Perm (Fin (m + 1))) (u v : Fin (m + 1)) :
    (pathG τ).Adj u v ↔
      ∃ i : Fin m, (u = τ i.castSucc ∧ v = τ i.succ) ∨ (v = τ i.castSucc ∧ u = τ i.succ) :=
  Iff.rfl

private lemma pathEdge_injective {m : ℕ} (τ : Equiv.Perm (Fin (m + 1))) :
    Function.Injective (fun i : Fin m => s(τ i.castSucc, τ i.succ)) := by
  intro a b h
  simp only [Sym2.eq_iff] at h
  rcases h with ⟨h1, _⟩ | ⟨h1, h2⟩
  · exact Fin.castSucc_injective _ (τ.injective h1)
  · have e1 := congrArg Fin.val (τ.injective h1)
    have e2 := congrArg Fin.val (τ.injective h2)
    simp only [Fin.val_castSucc, Fin.val_succ] at e1 e2
    omega

private lemma pathG_edgeFinset {m : ℕ} (τ : Equiv.Perm (Fin (m + 1))) [Fintype (pathG τ).edgeSet] :
    (pathG τ).edgeFinset = Finset.univ.image (fun i : Fin m => s(τ i.castSucc, τ i.succ)) := by
  ext e
  induction e using Sym2.ind with
  | h u v =>
    simp only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet, pathG_adj, Finset.mem_image,
      Finset.mem_univ, true_and, Sym2.eq_iff]
    constructor <;> rintro ⟨i, h⟩ <;> refine ⟨i, ?_⟩ <;>
      rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp

private lemma pathG_isTree {m : ℕ} (τ : Equiv.Perm (Fin (m + 1))) : (pathG τ).IsTree := by
  rw [SimpleGraph.isTree_iff_connected_and_card]
  constructor
  · -- Every node `τ j` is reachable from `τ 0` along the path.
    have hreach : ∀ (j : ℕ) (hj : j < m + 1), (pathG τ).Reachable (τ 0) (τ ⟨j, hj⟩) := by
      intro j
      induction j with
      | zero => intro _; rfl
      | succ j ih =>
        intro hj
        refine (ih (by omega)).trans (SimpleGraph.Adj.reachable ?_)
        exact (pathG_adj τ _ _).mpr ⟨⟨j, by omega⟩, Or.inl ⟨rfl, rfl⟩⟩
    refine SimpleGraph.Connected.mk (fun u v => ?_)
    have hu := hreach (τ.symm u).val (τ.symm u).isLt
    have hv := hreach (τ.symm v).val (τ.symm v).isLt
    simp only [Fin.eta, Equiv.apply_symm_apply] at hu hv
    exact hu.symm.trans hv
  · classical
    rw [Nat.card_eq_fintype_card, ← SimpleGraph.edgeFinset_card, pathG_edgeFinset,
      Finset.card_image_of_injective _ (pathEdge_injective τ)]
    simp

/-- Under symmetric distances, the path weighs `∑ᵢ c(τ i, τ (i+1))`. -/
private lemma pathG_weight {m : ℕ} (c : Fin (m + 1) → Fin (m + 1) → ℝ) (hsymm : ∀ i j, c i j = c j i)
    (τ : Equiv.Perm (Fin (m + 1))) :
    graphWeight c (pathG τ) = ∑ i : Fin m, c (τ i.castSucc) (τ i.succ) := by
  rw [graphWeight, pathG_edgeFinset, Finset.sum_image (fun a _ b _ h => pathEdge_injective τ h)]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  simp only [edgeCost, Sym2.lift_mk]
  rw [hsymm (τ i.succ)]; ring

/-- A tour is its Hamiltonian path plus the closing edge. -/
private lemma tourLength_eq_path {m : ℕ} (c : Fin (m + 1) → Fin (m + 1) → ℝ)
    (τ : Equiv.Perm (Fin (m + 1))) :
    tourLength c τ = ∑ i : Fin m, c (τ i.castSucc) (τ i.succ) + c (τ (Fin.last m)) (τ 0) := by
  rw [tourLength, Fin.sum_univ_castSucc, finRotate_last]
  congr 1
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [rot_castSucc]

/-- `z*` is the length of some tour. -/
private lemma exists_opt_tour {n : ℕ} (c : Fin n → Fin n → ℝ) :
    ∃ τ : Equiv.Perm (Fin n), tourLength c τ = optTourLength c := by
  have := (Set.range_nonempty (tourLength c)).csInf_mem (Set.finite_range _)
  obtain ⟨τ, hτ⟩ := this
  exact ⟨τ, hτ⟩

theorem solution {n : ℕ} (c : Fin n → Fin n → ℝ) (hc : IsMetric c) (hn : 1 ≤ n)
    (T : SimpleGraph (Fin n)) (hT : IsMST c T) : graphWeight c T ≤ optTourLength c := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  obtain ⟨τ, hτ⟩ := exists_opt_tour c
  rw [← hτ]
  -- Deleting the closing edge of an optimal tour leaves a spanning path, hence a spanning tree.
  calc graphWeight c T ≤ graphWeight c (pathG τ) := hT.2 _ (pathG_isTree τ)
    _ = ∑ i : Fin m, c (τ i.castSucc) (τ i.succ) := pathG_weight c hc.symm τ
    _ ≤ tourLength c τ := by
        rw [tourLength_eq_path]
        linarith [hc.nonneg (τ (Fin.last m)) (τ 0)]
