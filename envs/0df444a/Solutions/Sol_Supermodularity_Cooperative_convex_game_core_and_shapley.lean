-- Prove2me | solution 1 for Supermodularity.Cooperative.convex_game_core_and_shapley
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-26T14:18:12.043301+00:00
-- url     : https://prove2.me/submissions/83408bb8-3593-4b0a-bb51-e91df761283b

import Mathlib
import Definitions.Def_Supermodularity_Cooperative_IsConvexGame
import Definitions.Def_Supermodularity_Cooperative_Core
import Definitions.Def_Supermodularity_Cooperative_GreedyPayoff
import Definitions.Def_Supermodularity_Cooperative_ShapleyValue

set_option autoImplicit false

open Supermodularity.Cooperative in
lemma smc_IC_succ {n : ℕ} (σ : Equiv.Perm (Fin n)) (k : Fin n) :
    InitialCoalition σ ((σ.symm k : ℕ) + 1) = insert k (InitialCoalition σ (σ.symm k : ℕ)) := by
  ext m
  simp only [InitialCoalition, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
  constructor
  · intro h
    rcases Nat.lt_succ_iff_lt_or_eq.mp h with h' | h'
    · right; exact h'
    · left; exact σ.symm.injective (Fin.ext h')
  · rintro (rfl | h)
    · omega
    · omega

open Supermodularity.Cooperative in
lemma smc_not_mem_IC {n : ℕ} (σ : Equiv.Perm (Fin n)) (k : Fin n) :
    k ∉ InitialCoalition σ (σ.symm k : ℕ) := by
  simp [InitialCoalition]

open Supermodularity.Cooperative in
lemma smc_telescope {n : ℕ} (σ : Equiv.Perm (Fin n)) (F : Finset (Fin n) → ℝ) :
    ∑ k : Fin n, (F (InitialCoalition σ ((σ.symm k : ℕ) + 1)) -
      F (InitialCoalition σ (σ.symm k : ℕ))) = F Finset.univ - F ∅ := by
  have h1 : ∑ k : Fin n, (F (InitialCoalition σ ((σ.symm k : ℕ) + 1)) -
      F (InitialCoalition σ (σ.symm k : ℕ))) =
      ∑ j : Fin n, (F (InitialCoalition σ ((j : ℕ) + 1)) - F (InitialCoalition σ (j : ℕ))) :=
    Equiv.sum_comp σ.symm
      (fun j : Fin n => F (InitialCoalition σ ((j : ℕ) + 1)) - F (InitialCoalition σ (j : ℕ)))
  rw [h1, Fin.sum_univ_eq_sum_range (fun j => F (InitialCoalition σ (j + 1)) -
    F (InitialCoalition σ j)) n, Finset.sum_range_sub (fun j => F (InitialCoalition σ j)) n]
  have h0 : InitialCoalition σ 0 = ∅ := by
    ext k; simp [InitialCoalition]
  have hn : InitialCoalition σ n = Finset.univ := by
    ext k
    simp only [InitialCoalition, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
    exact (σ.symm k).isLt
  rw [h0, hn]

open Supermodularity.Cooperative in
lemma smc_greedy_core {n : ℕ} (f : Finset (Fin n) → ℝ) (hf0 : f ∅ = 0)
    (hsup : ∀ A B : Finset (Fin n), f A + f B ≤ f (A ∪ B) + f (A ∩ B))
    (σ : Equiv.Perm (Fin n)) :
    (∑ i ∈ Finset.univ, GreedyPayoff σ f i = f Finset.univ) ∧
    ∀ S ⊆ Finset.univ, f S ≤ ∑ i ∈ S, GreedyPayoff σ f i := by
  classical
  refine ⟨?_, fun S _ => ?_⟩
  · show ∑ k : Fin n, (f (InitialCoalition σ ((σ.symm k : ℕ) + 1)) -
      f (InitialCoalition σ (σ.symm k : ℕ))) = f Finset.univ
    rw [smc_telescope, hf0, sub_zero]
  · have ht := smc_telescope σ (fun A => f (S ∩ A))
    simp only [Finset.inter_empty, Finset.inter_univ, hf0, sub_zero] at ht
    have e : ∑ i ∈ S, GreedyPayoff σ f i =
        ∑ k : Fin n, (if k ∈ S then GreedyPayoff σ f k else 0) := by
      rw [← Finset.sum_filter]
      congr 1
      ext k
      simp
    rw [e, ← ht]
    apply Finset.sum_le_sum
    intro k _
    have hkA := smc_not_mem_IC σ k
    split_ifs with hk
    · show _ ≤ f (InitialCoalition σ ((σ.symm k : ℕ) + 1)) -
        f (InitialCoalition σ (σ.symm k : ℕ))
      rw [smc_IC_succ]
      set A := InitialCoalition σ (σ.symm k : ℕ) with hA
      have e1 : S ∩ insert k A ∪ A = insert k A := by
        ext m
        simp only [Finset.mem_union, Finset.mem_inter, Finset.mem_insert]
        constructor
        · rintro (⟨-, h⟩ | h)
          · exact h
          · exact Or.inr h
        · rintro (rfl | h)
          · exact Or.inl ⟨hk, Or.inl rfl⟩
          · exact Or.inr h
      have e2 : S ∩ insert k A ∩ A = S ∩ A := by
        ext m
        simp only [Finset.mem_inter, Finset.mem_insert]
        constructor
        · rintro ⟨⟨h1, -⟩, h2⟩; exact ⟨h1, h2⟩
        · rintro ⟨h1, h2⟩; exact ⟨⟨h1, Or.inr h2⟩, h2⟩
      have := hsup (S ∩ insert k A) A
      rw [e1, e2] at this
      linarith
    · rw [smc_IC_succ, Finset.inter_insert_of_notMem hk, sub_self]

open Supermodularity.Cooperative in
lemma smc_pred_subset {n : ℕ} (σ : Equiv.Perm (Fin n)) (i : Fin n) :
    InitialCoalition σ (σ.symm i : ℕ) ⊆ Finset.univ.erase i := by
  intro k hk
  rw [Finset.mem_erase]
  refine ⟨?_, Finset.mem_univ _⟩
  rintro rfl
  exact smc_not_mem_IC σ k hk

open Supermodularity.Cooperative in
lemma smc_fiber_card {n : ℕ} (i : Fin n) (S : Finset (Fin n)) (hiS : i ∉ S) :
    (Finset.univ.filter (fun σ : Equiv.Perm (Fin n) =>
      InitialCoalition σ (σ.symm i : ℕ) = S)).card =
      S.card.factorial * (n - S.card - 1).factorial := by
  classical
  have hsn : S.card < n := by
    have hsub : S ⊆ Finset.univ.erase i := fun k hk =>
      Finset.mem_erase.mpr ⟨fun h => hiS (h ▸ hk), Finset.mem_univ _⟩
    have h1 := Finset.card_le_card hsub
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin] at h1
    have : 0 < n := Fin.pos i
    omega
  obtain ⟨M, hM⟩ : ∃ M : Fin n → Fin 3,
      ∀ k, M k = if k ∈ S then 0 else if k = i then 1 else 2 := ⟨_, fun k => rfl⟩
  obtain ⟨L, hL⟩ : ∃ L : Fin n → Fin 3,
      ∀ j, L j = if (j : ℕ) < S.card then 0 else if (j : ℕ) = S.card then 1 else 2 :=
    ⟨_, fun j => rfl⟩
  have lit : ∀ c : Fin 3, c = 0 ∨ c = 1 ∨ c = 2 := by decide
  -- claim: fiber condition
  have hclaim : ∀ σ : Equiv.Perm (Fin n),
      InitialCoalition σ (σ.symm i : ℕ) = S ↔ ∀ k, L (σ.symm k) = M k := by
    intro σ
    constructor
    · intro h
      have hmem : ∀ k, k ∈ S ↔ (σ.symm k : ℕ) < σ.symm i := by
        intro k; rw [← h]; simp [InitialCoalition]
      have hpos : ((σ.symm i : Fin n) : ℕ) = S.card := by
        rw [← h]
        unfold InitialCoalition
        rw [Finset.card_equiv σ.symm
          (t := Finset.univ.filter (fun j : Fin n => (j : ℕ) < σ.symm i)) (fun k => by simp),
          Fin.card_filter_val_lt]
        exact (min_eq_right (le_of_lt (σ.symm i).isLt)).symm
      intro k
      rw [hL, hM]
      by_cases hkS : k ∈ S
      · have := (hmem k).mp hkS
        rw [if_pos hkS, if_pos (by omega)]
      · have hlt : ¬ (σ.symm k : ℕ) < σ.symm i := fun h' => hkS ((hmem k).mpr h')
        rw [if_neg hkS]
        by_cases hki : k = i
        · subst hki
          rw [if_pos rfl, if_neg (by omega), if_pos hpos]
        · have hne : (σ.symm k : ℕ) ≠ σ.symm i := fun h' =>
            hki (σ.symm.injective (Fin.ext h'))
          rw [if_neg hki, if_neg (by omega), if_neg (by omega)]
    · intro h
      have hi1 := h i
      rw [hL, hM, if_neg hiS, if_pos rfl] at hi1
      have hpos : ((σ.symm i : Fin n) : ℕ) = S.card := by
        split_ifs at hi1 with h1 h2
        · exact absurd hi1 (by decide)
        · exact h2
        · exact absurd hi1 (by decide)
      ext k
      simp only [InitialCoalition, Finset.mem_filter, Finset.mem_univ, true_and]
      rw [hpos]
      have key : (σ.symm k : ℕ) < S.card ↔ L (σ.symm k) = 0 := by
        rw [hL]; split_ifs with h1 h2
        · simp [h1]
        · simp only [h1, false_iff]; decide
        · simp only [h1, false_iff]; decide
      have key2 : k ∈ S ↔ M k = 0 := by
        rw [hM]; split_ifs with h1 h2
        · simp [h1]
        · simp only [h1, false_iff]; decide
        · simp only [h1, false_iff]; decide
      rw [key, key2, h k]
  have hclaim' : ∀ σ : Equiv.Perm (Fin n),
      InitialCoalition σ (σ.symm i : ℕ) = S ↔ M ∘ σ = L := by
    intro σ
    rw [hclaim σ]
    constructor
    · intro h; funext j
      have := h (σ j)
      simp only [Equiv.symm_apply_apply] at this
      rw [Function.comp_apply, this]
    · intro h k
      have := congrFun h (σ.symm k)
      simp only [Function.comp_apply, Equiv.apply_symm_apply] at this
      rw [this]
  -- fiber cardinalities
  have tot : ∀ F : Fin n → Fin 3,
      (Finset.univ.filter (fun k => F k = 0)).card + (Finset.univ.filter (fun k => F k = 1)).card
        + (Finset.univ.filter (fun k => F k = 2)).card = n := by
    intro F
    have := Finset.card_eq_sum_card_fiberwise (s := Finset.univ) (t := Finset.univ) (f := F)
      (by intro x _; simp)
    rw [Fin.sum_univ_three, Finset.card_univ, Fintype.card_fin] at this
    omega
  have cM0 : (Finset.univ.filter (fun k => M k = 0)).card = S.card := by
    congr 1
    ext k
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [hM]
    split_ifs with h1 h2
    · simp [h1]
    · simp only [h1, iff_false]; decide
    · simp only [h1, iff_false]; decide
  have cM1 : (Finset.univ.filter (fun k => M k = 1)).card = 1 := by
    rw [Finset.card_eq_one]
    refine ⟨i, ?_⟩
    ext k
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    rw [hM]
    split_ifs with h1 h2
    · have : k ≠ i := fun h => hiS (h ▸ h1)
      simp only [this, iff_false]; decide
    · simp [h2]
    · simp only [h2, iff_false]; decide
  have cL0 : (Finset.univ.filter (fun j => L j = 0)).card = S.card := by
    have : Finset.univ.filter (fun j => L j = 0) =
        Finset.univ.filter (fun j : Fin n => (j : ℕ) < S.card) := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rw [hL]
      split_ifs with h1 h2
      · simp [h1]
      · simp only [h1, iff_false]; decide
      · simp only [h1, iff_false]; decide
    rw [this, Fin.card_filter_val_lt]
    omega
  have cL1 : (Finset.univ.filter (fun j => L j = 1)).card = 1 := by
    rw [Finset.card_eq_one]
    refine ⟨⟨S.card, hsn⟩, ?_⟩
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    rw [hL]
    split_ifs with h1 h2
    · have hne : j ≠ ⟨S.card, hsn⟩ := fun h => by rw [h] at h1; exact lt_irrefl _ h1
      simp only [hne, iff_false]; decide
    · simp only [true_iff]; exact Fin.ext h2
    · have hne : j ≠ ⟨S.card, hsn⟩ := fun h => h2 (by rw [h])
      simp only [hne, iff_false]; decide
  have cM2 : (Finset.univ.filter (fun k => M k = 2)).card = n - S.card - 1 := by
    have := tot M; omega
  have cL2 : (Finset.univ.filter (fun j => L j = 2)).card = n - S.card - 1 := by
    have := tot L; omega
  have hcard : ∀ c : Fin 3, Fintype.card {j // L j = c} = Fintype.card {k // M k = c} := by
    intro c
    rw [Fintype.card_subtype, Fintype.card_subtype]
    rcases lit c with rfl | rfl | rfl
    · rw [cL0, cM0]
    · rw [cL1, cM1]
    · rw [cL2, cM2]
  obtain ⟨ρ₀, hρ₀⟩ : ∃ ρ₀ : Equiv.Perm (Fin n), ∀ j, M (ρ₀ j) = L j :=
    ⟨Equiv.ofFiberEquiv (fun c => Fintype.equivOfCardEq (hcard c)),
      fun j => Equiv.ofFiberEquiv_map _ j⟩
  have hcond : ∀ σ : Equiv.Perm (Fin n),
      M ∘ σ = L ↔ M ∘ ⇑((Equiv.mulRight ρ₀⁻¹) σ) = M := by
    intro σ
    rw [Equiv.coe_mulRight]
    constructor
    · intro h; funext x
      simp only [Function.comp_apply, Equiv.Perm.mul_apply, Equiv.Perm.inv_def]
      rw [show M (σ (ρ₀.symm x)) = L (ρ₀.symm x) from congrFun h _, ← hρ₀ (ρ₀.symm x),
        Equiv.apply_symm_apply]
    · intro h; funext j
      have := congrFun h (ρ₀ j)
      simp only [Function.comp_apply, Equiv.Perm.mul_apply, Equiv.Perm.inv_def,
        Equiv.symm_apply_apply] at this
      rw [Function.comp_apply, this, hρ₀]
  rw [← Fintype.card_subtype, Fintype.card_congr (Equiv.subtypeEquivRight hclaim'),
    Fintype.card_congr (Equiv.subtypeEquiv
      (q := fun g : Equiv.Perm (Fin n) => M ∘ ⇑g = M) (Equiv.mulRight ρ₀⁻¹) hcond),
    DomMulAct.stabilizer_card, Fin.prod_univ_three, Fintype.card_subtype,
    Fintype.card_subtype, Fintype.card_subtype, cM0, cM1, cM2]
  simp

open Supermodularity.Cooperative in
lemma smc_sum_greedy {n : ℕ} (f : Finset (Fin n) → ℝ) (i : Fin n) :
    ∑ σ : Equiv.Perm (Fin n), GreedyPayoff σ f i = (n.factorial : ℝ) * ShapleyValue f i := by
  classical
  calc ∑ σ : Equiv.Perm (Fin n), GreedyPayoff σ f i
      = ∑ σ : Equiv.Perm (Fin n), (f (insert i (InitialCoalition σ (σ.symm i : ℕ))) -
          f (InitialCoalition σ (σ.symm i : ℕ))) := by
        apply Finset.sum_congr rfl
        intro σ _
        simp only [GreedyPayoff]
        rw [smc_IC_succ]
    _ = ∑ S ∈ (Finset.univ.erase i).powerset,
          ∑ σ ∈ Finset.univ.filter (fun σ : Equiv.Perm (Fin n) =>
            InitialCoalition σ (σ.symm i : ℕ) = S),
          (f (insert i (InitialCoalition σ (σ.symm i : ℕ))) -
            f (InitialCoalition σ (σ.symm i : ℕ))) :=
        (Finset.sum_fiberwise_of_maps_to
          (fun σ _ => Finset.mem_powerset.mpr (smc_pred_subset σ i)) _).symm
    _ = ∑ S ∈ (Finset.univ.erase i).powerset,
          ((S.card.factorial * (n - S.card - 1).factorial : ℕ) : ℝ) *
            (f (insert i S) - f S) := by
        apply Finset.sum_congr rfl
        intro S hS
        have hiS : i ∉ S := by
          intro h
          have := Finset.mem_powerset.mp hS h
          simp at this
        have hc : ∀ σ ∈ Finset.univ.filter (fun σ : Equiv.Perm (Fin n) =>
            InitialCoalition σ (σ.symm i : ℕ) = S),
            (f (insert i (InitialCoalition σ (σ.symm i : ℕ))) -
              f (InitialCoalition σ (σ.symm i : ℕ))) = f (insert i S) - f S := by
          intro σ hσ
          rw [(Finset.mem_filter.mp hσ).2]
        rw [Finset.sum_congr rfl hc, Finset.sum_const, nsmul_eq_mul, smc_fiber_card i S hiS]
    _ = (n.factorial : ℝ) * ShapleyValue f i := by
        unfold ShapleyValue
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro S _
        have hn : (n.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
        push_cast
        field_simp

open Supermodularity.Cooperative in
theorem solution {n : ℕ} (f : Finset (Fin n) → ℝ)
    (hf : IsConvexGame f) :
    (∀ σ : Equiv.Perm (Fin n), GreedyPayoff σ f ∈ Core Finset.univ f) ∧
    (Core Finset.univ f).Nonempty ∧
    ShapleyValue f ∈ Core Finset.univ f := by
  classical
  obtain ⟨hf0, hsm⟩ := hf
  unfold Supermodularity.Monotonicity.SupermodularOn at hsm
  have hsup : ∀ A B : Finset (Fin n), f A + f B ≤ f (A ∪ B) + f (A ∩ B) :=
    fun A B => hsm (Set.mem_univ A) (Set.mem_univ B)
  have hc : ∀ σ : Equiv.Perm (Fin n), GreedyPayoff σ f ∈ Core Finset.univ f := by
    intro σ
    simp only [Core, Set.mem_setOf_eq]
    exact smc_greedy_core f hf0 hsup σ
  refine ⟨hc, ⟨_, hc 1⟩, ?_⟩
  have hnf : (0 : ℝ) < n.factorial := by exact_mod_cast Nat.factorial_pos n
  have hsh : ∀ i, ShapleyValue f i =
      (∑ σ : Equiv.Perm (Fin n), GreedyPayoff σ f i) / n.factorial := by
    intro i
    rw [smc_sum_greedy]
    field_simp
  have hcard : (Finset.univ : Finset (Equiv.Perm (Fin n))).card = n.factorial := by
    rw [Finset.card_univ, Fintype.card_perm, Fintype.card_fin]
  simp only [Core, Set.mem_setOf_eq]
  constructor
  · simp_rw [hsh]
    rw [← Finset.sum_div, Finset.sum_comm,
      Finset.sum_congr rfl (fun σ _ => (smc_greedy_core f hf0 hsup σ).1),
      Finset.sum_const, hcard, nsmul_eq_mul]
    field_simp
  · intro S _
    simp_rw [hsh]
    rw [← Finset.sum_div, Finset.sum_comm, le_div_iff₀ hnf]
    calc f S * n.factorial = ∑ σ : Equiv.Perm (Fin n), f S := by
          rw [Finset.sum_const, hcard, nsmul_eq_mul]; ring
      _ ≤ ∑ σ : Equiv.Perm (Fin n), ∑ i ∈ S, GreedyPayoff σ f i :=
          Finset.sum_le_sum (fun σ _ => (smc_greedy_core f hf0 hsup σ).2 S (Finset.subset_univ S))
