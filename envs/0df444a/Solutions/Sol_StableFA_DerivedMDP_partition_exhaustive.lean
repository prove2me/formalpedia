-- Prove2me | solution 1 for StableFA.DerivedMDP.partition_exhaustive
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T16:30:47.502784+00:00
-- url     : https://prove2.me/submissions/6e84df35-f293-48d4-8e7f-65f0c4a4f2b2

import Mathlib
import Definitions.Def_BertsekasSSPModel
import Definitions.Def_StableFA_DerivedMDP_Setting

set_option autoImplicit false

open StableFA.DerivedMDP Filter Topology

theorem solution {n : ℕ} {C : Type} [Fintype C]
    (M : BertsekasSSPModel n C)
    (hproper : ∀ μ : Fin n → C, (∀ i, μ i ∈ M.U i) → IsProper M μ) :
    ∀ i : Fin n, ∃ k : ℕ, some i ∈ layer M k := by
  classical
  by_contra hcon
  push_neg at hcon
  -- hcon : ∃ i, ∀ k, some i ∉ layer M k
  obtain ⟨i0, hi0⟩ := hcon
  let Wset : Set (Option (Fin n)) := ⋃ k, layer M k
  -- a uniform bound
  have hex : ∀ y : Option (Fin n), ∃ j : ℕ, y ∈ Wset → y ∈ layer M j := by
    intro y
    by_cases hy : y ∈ Wset
    · obtain ⟨j, hj⟩ := Set.mem_iUnion.1 hy
      exact ⟨j, fun _ => hj⟩
    · exact ⟨0, fun h => absurd h hy⟩
  choose f hf using hex
  let K : ℕ := Finset.univ.sup f + 3
  have hK : ∀ y ∈ Wset, y ∈ ⋃ j < K + 0, layer M j := by
    intro y hy
    refine Set.mem_iUnion₂.2 ⟨f y, ?_, hf y hy⟩
    have : f y ≤ Finset.univ.sup f := Finset.le_sup (f := f) (Finset.mem_univ y)
    omega
  have hK2 : ∃ k, K = k + 2 := ⟨Finset.univ.sup f + 1, by show Finset.univ.sup f + 3 = _; omega⟩
  obtain ⟨k, hkK⟩ := hK2
  -- for every i not in W, there's an action with no mass to W
  have hact : ∀ i : Fin n, ∃ u ∈ M.U i, some i ∉ Wset → ∀ y ∈ Wset, ¬ 0 < stepProb M i u y := by
    intro i
    by_cases hi : some i ∈ Wset
    · obtain ⟨u, hu⟩ := M.hU i
      exact ⟨u, hu, fun h => absurd hi h⟩
    · have hnot : some i ∉ layer M (k + 2) := fun h => hi (Set.mem_iUnion.2 ⟨_, h⟩)
      rw [mem_layer_iff] at hnot
      have hnot' : ¬ (∃ i', some i = some i' ∧ ∀ u ∈ M.U i', ∃ y ∈ (⋃ j < k + 2, layer M j),
          0 < stepProb M i' u y) := by
        intro h
        exact hnot ⟨fun hmem => hi (by
          obtain ⟨j, _, hj⟩ := Set.mem_iUnion₂.1 hmem
          exact Set.mem_iUnion.2 ⟨j, hj⟩), h⟩
      push_neg at hnot'
      obtain ⟨u, hu, hu2⟩ := hnot' i rfl
      refine ⟨u, hu, fun _ y hy => ?_⟩
      have := hu2 y
      rw [← hkK] at this
      exact not_lt.2 (this (hK y hy))
  choose μ hμU hμ using hact
  have hprop := hproper μ hμU i0
  -- survival stays 1 outside W
  have hsurv : ∀ t, ∀ j : Fin n, some j ∉ Wset →
      BertsekasSSPSurvival M (fun _ => μ) t j = 1 := by
    intro t
    induction t with
    | zero => intro j _; simp [BertsekasSSPSurvival]
    | succ t ih =>
      intro j hj
      have h1 := hμ j hj
      have hsum := M.hp_sum j (μ j) (hμU j)
      have hnone : ¬ 0 < stepProb M j (μ j) none := fun h =>
        h1 none (by
          -- none lies in layer 1
          exact Set.mem_iUnion.2 ⟨1, rfl⟩) h
      simp only [stepProb, not_lt] at hnone
      have hsum1 : ∑ l, M.p j (μ j) l = 1 := le_antisymm hsum (by linarith)
      simp only [BertsekasSSPSurvival]
      calc ∑ l, M.p j (μ j) l * BertsekasSSPSurvival M (fun _ => μ) t l
          = ∑ l, M.p j (μ j) l := by
            refine Finset.sum_congr rfl fun l _ => ?_
            by_cases hl : some l ∈ Wset
            · have : ¬ 0 < M.p j (μ j) l := h1 _ hl
              have h0 : M.p j (μ j) l = 0 :=
                le_antisymm (not_lt.1 this) (M.hp_nonneg _ _ _)
              simp [h0]
            · rw [ih l hl, mul_one]
        _ = 1 := hsum1
  have hconst : Tendsto (fun t => BertsekasSSPSurvival M (fun _ => μ) t i0) atTop (𝓝 1) := by
    have : (fun t => BertsekasSSPSurvival M (fun _ => μ) t i0) = fun _ => 1 :=
      funext fun t => hsurv t i0 (fun h => by
        obtain ⟨j, hj⟩ := Set.mem_iUnion.1 h
        exact hi0 j hj)
    rw [this]; exact tendsto_const_nhds
  have := tendsto_nhds_unique hprop hconst
  norm_num at this
