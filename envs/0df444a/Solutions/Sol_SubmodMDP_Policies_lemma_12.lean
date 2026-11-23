-- Prove2me | solution 1 for SubmodMDP.Policies.lemma_12
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-23T04:30:14.658519+00:00
-- url     : https://prove2.me/submissions/a772726d-1fb9-4755-a3ad-8b69216a3808

import Definitions.Def_SubmodMDP_Policies_GraphMDP

open SubmodMDP.Policies

namespace Lemma12Aux

lemma alg4K_subset_range (d r ℓ : ℕ) (hd : 2 ≤ d) (hℓ : ℓ < d ^ r) :
    alg4K d ℓ ⊆ (Finset.range r).image (fun j => (ℓ / d ^ j) * d ^ j) := by
  intro k hk
  simp only [alg4K, Finset.mem_erase, Finset.mem_image, Finset.mem_range] at hk ⊢
  rcases hk with ⟨hk0, j, _, rfl⟩
  refine ⟨j, ?_, rfl⟩
  by_contra hj
  have hj' : r ≤ j := Nat.le_of_not_lt hj
  have hpow : d ^ r ≤ d ^ j := Nat.pow_le_pow_right (by omega) hj'
  have hdiv : ℓ / d ^ j = 0 := Nat.div_eq_of_lt (lt_of_lt_of_le hℓ hpow)
  simp [hdiv] at hk0

lemma card_alg4I_le {N : ℕ} (d r : ℕ) (traj : List (Fin N)) (hd : 2 ≤ d)
    (hℓ : traj.length < d ^ r) : (alg4I d traj).card ≤ r := by
  calc
    (alg4I d traj).card
      ≤ ∑ i ∈ alg4K d traj.length, (traj[i - 1]?).toFinset.card := Finset.card_biUnion_le
    _ ≤ ∑ _i ∈ alg4K d traj.length, 1 := by
      refine Finset.sum_le_sum fun i _ => ?_
      cases traj[i - 1]? <;> simp
    _ = (alg4K d traj.length).card := by simp
    _ ≤ ((Finset.range r).image (fun j => (traj.length / d ^ j) * d ^ j)).card :=
      Finset.card_le_card (alg4K_subset_range d r traj.length hd hℓ)
    _ ≤ (Finset.range r).card := Finset.card_image_le
    _ = r := Finset.card_range r

lemma mem_alg4K_pos_le (d ℓ i : ℕ) (hi : i ∈ alg4K d ℓ) : 1 ≤ i ∧ i ≤ ℓ := by
  simp only [alg4K, Finset.mem_erase, Finset.mem_image, Finset.mem_range] at hi
  rcases hi with ⟨hi0, j, _, rfl⟩
  exact ⟨Nat.pos_of_ne_zero hi0, Nat.div_mul_le_self ℓ (d ^ j)⟩

lemma alg4K_succ_subset (d k : ℕ) (hd : 2 ≤ d) :
    alg4K d (k + 1) ⊆ insert (k + 1) (alg4K d k) := by
  intro m hm
  simp only [alg4K, Finset.mem_erase, Finset.mem_image, Finset.mem_range] at hm
  rcases hm with ⟨hm0, j, _, rfl⟩
  set D := d ^ j
  have hDpos : 0 < D := Nat.pow_pos (by omega)
  have hrem_lt : k % D < D := Nat.mod_lt k hDpos
  by_cases hrem : k % D + 1 = D
  · have hk1 : k + 1 = D * (k / D + 1) := by
      have hdivmod := Nat.div_add_mod k D
      calc
        k + 1 = D * (k / D) + (k % D + 1) := by omega
        _ = D * (k / D) + D := by rw [hrem]
        _ = D * (k / D + 1) := by ring
    have hdiv : (k + 1) / D = k / D + 1 := by
      rw [hk1, Nat.mul_div_right _ hDpos]
    have hm_eq : (k + 1) / D * D = k + 1 := by
      rw [hdiv]
      linarith [hk1]
    rw [hm_eq]
    exact Finset.mem_insert_self _ _
  · have hrem_lt' : k % D + 1 < D := by omega
    have hk1 : k + 1 = (k % D + 1) + D * (k / D) := by
      have hdivmod := Nat.div_add_mod k D
      omega
    have hdiv : (k + 1) / D = k / D := by
      rw [hk1, Nat.add_mul_div_left _ _ hDpos, Nat.div_eq_of_lt hrem_lt', zero_add]
    rw [hdiv] at hm0 ⊢
    apply Finset.mem_insert_of_mem
    simp only [alg4K, Finset.mem_erase, Finset.mem_image, Finset.mem_range]
    refine ⟨hm0, j, ?_, rfl⟩
    have hDk : D ≤ k := by
      by_contra hlt
      have h0 : k / D = 0 := Nat.div_eq_of_lt (Nat.lt_of_not_le hlt)
      simp [h0] at hm0
    have hjD : j < D := Nat.lt_pow_self (by omega)
    omega

lemma alg4I_append_subset {N : ℕ} (d : ℕ) (hd : 2 ≤ d) (τ : List (Fin N)) (u : Fin N) :
    alg4I d (τ ++ [u]) ⊆ insert u (alg4I d τ) := by
  intro v hv
  simp only [alg4I, List.length_append, List.length_singleton, Finset.mem_biUnion,
    Option.mem_toFinset, Option.mem_def] at hv
  rcases hv with ⟨i, hiK, hvi⟩
  have hi' := alg4K_succ_subset d τ.length hd hiK
  rcases Finset.mem_insert.mp hi' with rfl | hiK0
  · simp only [Nat.add_sub_cancel, List.getElem?_append_right (le_refl τ.length),
      Nat.sub_self, List.getElem?_cons_zero] at hvi
    cases hvi
    exact Finset.mem_insert_self u _
  · obtain ⟨hi1, hi2⟩ := mem_alg4K_pos_le d τ.length i hiK0
    have hilt : i - 1 < τ.length := by omega
    rw [List.getElem?_append_left hilt] at hvi
    apply Finset.mem_insert_of_mem
    simp only [alg4I, Finset.mem_biUnion, Option.mem_toFinset, Option.mem_def]
    exact ⟨i, hiK0, hvi⟩

lemma inQ_antimono (G : LGraph) (r : ℕ) (x : Finset (Fin G.N) → ℝ) (hx : InQ G r x) :
    ∀ {A B : Finset (Fin G.N)}, A ⊆ B → B.card ≤ r + 1 → x B ≤ x A := by
  suffices h : ∀ (s : Finset (Fin G.N)) (A : Finset (Fin G.N)),
      Disjoint A s → (A ∪ s).card ≤ r + 1 → x (A ∪ s) ≤ x A by
    intro A B hAB hB
    have hdisj : Disjoint A (B \ A) := disjoint_sdiff_self_right
    have hunion : A ∪ (B \ A) = B := Finset.union_sdiff_of_subset hAB
    simpa [hunion] using h (B \ A) A hdisj (by simpa [hunion] using hB)
  intro s
  induction s using Finset.induction_on with
  | empty =>
    intro A _ _
    simp
  | @insert v s hvs ih =>
    intro A hdisj hcard
    rw [Finset.disjoint_insert_right] at hdisj
    rcases hdisj with ⟨hvA, hdisj'⟩
    have hvAs : v ∉ A ∪ s := by
      simp [hvA, hvs]
    have hunion_eq : A ∪ insert v s = insert v (A ∪ s) := Finset.union_insert v A s
    rw [hunion_eq] at hcard ⊢
    have hcard_ins : (insert v (A ∪ s)).card = (A ∪ s).card + 1 :=
      Finset.card_insert_of_notMem hvAs
    have hcard_le_r : (A ∪ s).card ≤ r := by omega
    calc
      x (insert v (A ∪ s)) ≤ x (A ∪ s) := hx.2.2.1 v (A ∪ s) hcard_le_r
      _ ≤ x A := ih A hdisj' (by omega)

lemma mdpPrefix_length_and_pos (M : GMDP) (d r : ℕ) (hd : 2 ≤ d) (hH : M.G.H = d ^ r)
    (x : Finset (Fin M.G.N) → ℝ) (hx : InQ M.G r x) :
    ∀ k ≤ M.G.H, ∀ τ : List (Fin M.G.N), some τ ∈ (mdpPrefix M d x k).support →
      τ.length = k ∧ (k < M.G.H → 0 < x (alg4I d τ)) := by
  intro k
  induction k with
  | zero =>
    intro _ τ hτ
    simp only [mdpPrefix, PMF.support_pure, Set.mem_singleton_iff, Option.some.injEq] at hτ
    subst hτ
    refine ⟨rfl, fun _ => ?_⟩
    have hI0 : alg4I d ([] : List (Fin M.G.N)) = ∅ := by
      simp [alg4I, alg4K]
    rw [hI0, hx.2.2.2.1]
    exact zero_lt_one
  | succ k ih =>
    intro hk1 τ' hτ'
    simp only [mdpPrefix, PMF.mem_support_bind_iff] at hτ'
    rcases hτ' with ⟨o, ho, hstep⟩
    cases o with
    | none =>
      simp at hstep
    | some τ =>
      obtain ⟨hlen, hpos_prev⟩ := ih (by omega) τ ho
      have hxI_pos : 0 < x (alg4I d τ) := hpos_prev (by omega)
      cases halg : alg4 M d x τ with
      | none =>
        simp [halg] at hstep
      | some q =>
        cases hnd : nextDist q with
        | none =>
          simp [halg, hnd] at hstep
        | some μ =>
          simp only [halg, hnd, PMF.mem_support_map_iff, Option.some.injEq] at hstep
          rcases hstep with ⟨u, hu, rfl⟩
          refine ⟨by simp [hlen], fun hk1_lt => ?_⟩
          unfold nextDist at hnd
          split_ifs at hnd with hprob
          cases hnd
          simp only [PMF.mem_support_iff, PMF.ofFintype_apply, ne_eq, ENNReal.ofReal_eq_zero,
            not_le] at hu
          simp only [alg4, hxI_pos.ne', ↓reduceIte, Option.some.injEq] at halg
          subst halg
          dsimp only at hu
          split_ifs at hu with hlay
          · have hxu_pos : 0 < x (insert u (alg4I d τ)) := by
              by_contra hnp
              have hle : x (insert u (alg4I d τ)) ≤ 0 := le_of_not_gt hnp
              have hdiv : x (insert u (alg4I d τ)) / x (alg4I d τ) ≤ 0 :=
                div_nonpos_of_nonpos_of_nonneg hle hxI_pos.le
              linarith
            have hk_lt_dr : τ.length < d ^ r := by omega
            have hcardI : (alg4I d τ).card ≤ r := card_alg4I_le d r τ hd hk_lt_dr
            have hcardB : (insert u (alg4I d τ)).card ≤ r + 1 := by
              have := Finset.card_insert_le u (alg4I d τ)
              omega
            have hsub : alg4I d (τ ++ [u]) ⊆ insert u (alg4I d τ) :=
              alg4I_append_subset d hd τ u
            have hle_x : x (insert u (alg4I d τ)) ≤ x (alg4I d (τ ++ [u])) :=
              inQ_antimono M.G r x hx hsub hcardB
            linarith
          · linarith

end Lemma12Aux

set_option linter.unusedVariables false in
theorem solution (M : GMDP) (hM : M.WF) (d r : ℕ) (hd : 2 ≤ d) (hr : 1 ≤ r)
    (hH : M.G.H = d ^ r) (x : Finset (Fin M.G.N) → ℝ) (hx : InQ M.G r x) (h7 : Sat7 M r x) :
    ∀ k < M.G.H, ∀ τ : List (Fin M.G.N), some τ ∈ (mdpPrefix M d x k).support →
      alg4 M d x τ ≠ none := by
  intro k hk τ hτ
  have hpos := (Lemma12Aux.mdpPrefix_length_and_pos M d r hd hH x hx k hk.le τ hτ).2 hk
  simp [alg4, hpos.ne']
