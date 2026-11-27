-- Prove2me | solution 1 for PigeonholeDesign.Upper.Supplement.theorem_5
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:35:38.438331+00:00
-- url     : https://prove2.me/submissions/19e4d3be-5a6e-4c00-ae96-2b590d8f400c

import Mathlib
import Definitions.Def_PigeonholeDesign_MultiDim_Setting
import Definitions.Def_PigeonholeDesign_Upper_Supplement_MatchedPair

open PigeonholeDesign
open PigeonholeDesign.Upper
open PigeonholeDesign.Upper.Supplement

theorem solution (q : ℕ) (S : Fin q → Finset ℝ) (hS : ∀ i, (S i : Set ℝ) ⊆ Set.Icc 0 1)
    (hne : ∀ i, (S i).Nonempty) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∃ T₀ : ℕ, ∀ T : ℕ, T₀ ≤ T → Even T →
      (∀ x : Fin T → MultiDim.Cov q 1, MultiDim.Admissible S x →
          PigeonholeDesign.Upper.crdExp x ≤ C * Real.sqrt T) ∧
      (∃ x : Fin T → MultiDim.Cov q 1, MultiDim.Admissible S x ∧
          c * Real.sqrt T ≤ PigeonholeDesign.Upper.crdExp x) := by
            open Finset in
            focus
              have G1 : ∀ (n : ℕ) (x : Fin (n+n) → MultiDim.Cov q 1) (V : Finset (Fin (n+n))), V.card = n →
                  ∀ (φ : Fin (n+n) → ℝ), (∀ s t, |φ s - φ t| ≤ dist (x s) (x t)) →
                  |∑ t ∈ V, φ t - ∑ t ∈ Vᶜ, φ t| ≤ PigeonholeDesign.Upper.discrepancy x (fun t => decide (t ∉ V)) := by
                intro n x V hV φ hφ
                unfold PigeonholeDesign.Upper.discrepancy
                have hA : ∀ t, t ∈ V ↔ decide (t ∉ V) = false := by intro t; simp
                have hB : ∀ t, t ∈ Vᶜ ↔ decide (t ∉ V) = true := by intro t; simp
                have : Nonempty ({t // decide (t ∉ V) = false} ≃ {t // decide (t ∉ V) = true}) := by
                  rw [← Fintype.card_eq, Fintype.card_subtype, Fintype.card_subtype]
                  have h1 : (univ.filter fun t => decide (t ∉ V) = false) = V := by ext t; simp
                  have h2 : (univ.filter fun t => decide (t ∉ V) = true) = Vᶜ := by ext t; simp
                  rw [h1, h2, card_compl, hV, Fintype.card_fin]; omega
                apply le_ciInf
                intro e
                rw [Finset.sum_subtype V hA φ, Finset.sum_subtype Vᶜ hB φ]
                rw [← Equiv.sum_comp e (fun b => φ b), ← Finset.sum_sub_distrib]
                refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
                exact Finset.sum_le_sum fun a _ => hφ _ _
              have B1 : ∀ r : ℕ, 16 ^ r ≤ (Nat.centralBinom r) ^ 2 * (4 * r + 1) := by
                intro r
                induction r with
                | zero => simp
                | succ r ih =>
                  have h := Nat.succ_mul_centralBinom_succ r
                  have hc : ((r+1:ℕ):ℝ) * (Nat.centralBinom (r+1) : ℝ) = 2 * (2 * r + 1) * Nat.centralBinom r := by
                    exact_mod_cast h
                  have ih' : (16:ℝ) ^ r ≤ (Nat.centralBinom r : ℝ) ^ 2 * (4 * r + 1) := by exact_mod_cast ih
                  suffices (16:ℝ) ^ (r+1) ≤ (Nat.centralBinom (r+1) : ℝ) ^ 2 * (4 * (r+1:ℕ) + 1) by exact_mod_cast this
                  push_cast at hc ⊢
                  have hr : (0:ℝ) < r + 1 := by positivity
                  have key : ((r+1:ℝ))^2 * ((Nat.centralBinom (r+1) : ℝ) ^ 2 * (4 * (r+1) + 1))
                      ≥ ((r+1:ℝ))^2 * 16 ^ (r+1) := by
                    have e1 : ((r+1:ℝ))^2 * (Nat.centralBinom (r+1) : ℝ) ^ 2 = (2 * (2 * r + 1) * Nat.centralBinom r)^2 := by
                      rw [← hc]; ring
                    rw [← mul_assoc, e1, pow_succ (16:ℝ) r]
                    have hp : (0:ℝ) ≤ 16 * (r+1)^2 := by positivity
                    have h0 : (0:ℝ) ≤ (Nat.centralBinom r : ℝ)^2 := by positivity
                    nlinarith [mul_le_mul_of_nonneg_left ih' hp]
                  exact le_of_mul_le_mul_left key (by positivity)
              have B2 : ∀ r : ℕ, (Nat.centralBinom r) ^ 2 * (3 * r + 1) ≤ 16 ^ r := by
                intro r
                induction r with
                | zero => simp
                | succ r ih =>
                  have h := Nat.succ_mul_centralBinom_succ r
                  have hc : ((r+1:ℕ):ℝ) * (Nat.centralBinom (r+1) : ℝ) = 2 * (2 * r + 1) * Nat.centralBinom r := by
                    exact_mod_cast h
                  have ih' : (Nat.centralBinom r : ℝ) ^ 2 * (3 * r + 1) ≤ (16:ℝ) ^ r := by exact_mod_cast ih
                  suffices (Nat.centralBinom (r+1) : ℝ) ^ 2 * (3 * (r+1:ℕ) + 1) ≤ (16:ℝ) ^ (r+1) by exact_mod_cast this
                  push_cast at hc ⊢
                  have key : ((r+1:ℝ))^2 * ((Nat.centralBinom (r+1) : ℝ) ^ 2 * (3 * (r+1) + 1))
                      ≤ ((r+1:ℝ))^2 * 16 ^ (r+1) := by
                    have e1 : ((r+1:ℝ))^2 * (Nat.centralBinom (r+1) : ℝ) ^ 2 = (2 * (2 * r + 1) * Nat.centralBinom r)^2 := by
                      rw [← hc]; ring
                    rw [← mul_assoc, e1, pow_succ (16:ℝ) r]
                    have hp : (0:ℝ) ≤ 16 * (r+1)^2 := by positivity
                    have h0 : (0:ℝ) ≤ (Nat.centralBinom r : ℝ)^2 := by positivity
                    nlinarith [mul_le_mul_of_nonneg_left ih' hp, mul_nonneg h0 (Nat.cast_nonneg r : (0:ℝ) ≤ r)]
                  exact le_of_mul_le_mul_left key (by positivity)
              have B3 : ∀ m : ℕ, (4:ℝ) ^ m ≤ (Nat.choose m (m/2) : ℝ) ^ 2 * (2 * m + 3) := by
                intro m
                obtain ⟨r, rfl | rfl⟩ := Nat.even_or_odd' m
                · have h1 : 2 * r / 2 = r := by omega
                  rw [h1, ← Nat.centralBinom_eq_two_mul_choose]
                  have := B1 r
                  have h' : (16:ℝ) ^ r ≤ (Nat.centralBinom r : ℝ) ^ 2 * (4 * r + 1) := by exact_mod_cast this
                  have h4 : (4:ℝ) ^ (2*r) = 16 ^ r := by rw [pow_mul]; norm_num
                  rw [h4]; push_cast
                  nlinarith [sq_nonneg (Nat.centralBinom r : ℝ)]
                · have h1 : (2 * r + 1) / 2 = r := by omega
                  rw [h1]
                  have hs : Nat.centralBinom (r+1) = 2 * Nat.choose (2*r+1) r := by
                    rw [Nat.centralBinom_eq_two_mul_choose, show 2 * (r+1) = (2*r+1)+1 by ring,
                      Nat.choose_succ_succ, Nat.choose_symm_half]; ring
                  have := B1 (r+1)
                  rw [hs] at this
                  have h' : (16:ℝ) ^ (r+1) ≤ (2 * Nat.choose (2*r+1) r : ℝ) ^ 2 * (4 * (r+1:ℕ) + 1) := by exact_mod_cast this
                  have h4 : (4:ℝ) ^ (2*r+1) = 16 ^ r * 4 := by rw [pow_succ, pow_mul]; norm_num
                  rw [h4]; push_cast at h' ⊢
                  rw [pow_succ] at h'
                  nlinarith [sq_nonneg (Nat.choose (2*r+1) r : ℝ)]
              have T1 : ∀ n : ℕ, 1 ≤ n → ∀ K : ℕ, K + 1 ≤ n →
                  ∑ j ∈ Finset.range (K+1), ((n:ℝ) - 2 * j) * (Nat.choose n j : ℝ) ^ 2
                    = n * (Nat.choose (n-1) K : ℝ) ^ 2 := by
                intro n hn K
                obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n-1, by omega⟩
                simp only [Nat.add_sub_cancel]
                induction K with
                | zero => intro _; simp
                | succ K ih =>
                  intro hK
                  rw [Finset.sum_range_succ, ih (by omega)]
                  have e1 : ((m+1 : ℕ) : ℝ) * Nat.choose m K = Nat.choose (m+1) (K+1) * (K+1) := by
                    exact_mod_cast Nat.add_one_mul_choose_eq m K
                  have e2 : (Nat.choose m (K+1) : ℝ) * (m+1) = Nat.choose (m+1) (K+1) * ((m+1 - (K+1) : ℕ) : ℝ) := by
                    exact_mod_cast Nat.choose_mul_succ_eq m (K+1)
                  have e3 : (Nat.choose (m+1) (K+1) : ℝ) = Nat.choose m K + Nat.choose m (K+1) := by
                    exact_mod_cast Nat.choose_succ_succ m K
                  rw [Nat.cast_sub (by omega)] at e2
                  push_cast at e1 e2 ⊢
                  nlinarith [e1, e2, e3]
              have C1 : ∀ n j : ℕ, (((univ : Finset (Fin (n+n))).powersetCard n).filter
                  (fun V => (V.filter (fun t => t.val < n)).card = j)).card = n.choose j * n.choose (n - j) := by
                intro n j
                set p : Fin (n+n) → Prop := fun t => t.val < n
                have hL : (univ.filter p).card = n := by
                  simp only [p]; rw [Fin.card_filter_val_lt]; omega
                have hR : (univ.filter (fun t => ¬ p t)).card = n := by
                  have := card_filter_add_card_filter_not (s := (univ : Finset (Fin (n+n)))) p
                  rw [hL, card_univ, Fintype.card_fin] at this; omega
                have key : ∀ ab : Finset (Fin (n+n)) × Finset (Fin (n+n)), ab.1 ⊆ univ.filter p →
                    ab.2 ⊆ univ.filter (fun t => ¬ p t) →
                    (ab.1 ∪ ab.2).filter p = ab.1 ∧ (ab.1 ∪ ab.2).filter (fun t => ¬ p t) = ab.2 ∧
                    Disjoint ab.1 ab.2 := by
                  intro ab h1 h3
                  refine ⟨?_, ?_, ?_⟩
                  · ext t; simp only [mem_filter, mem_union]
                    constructor
                    · rintro ⟨h | h, hp⟩
                      · exact h
                      · exact absurd hp (mem_filter.1 (h3 h)).2
                    · intro h; exact ⟨Or.inl h, (mem_filter.1 (h1 h)).2⟩
                  · ext t; simp only [mem_filter, mem_union]
                    constructor
                    · rintro ⟨h | h, hp⟩
                      · exact absurd (mem_filter.1 (h1 h)).2 hp
                      · exact h
                    · intro h; exact ⟨Or.inr h, (mem_filter.1 (h3 h)).2⟩
                  · rw [disjoint_left]; intro a ha hb
                    exact (mem_filter.1 (h3 hb)).2 (mem_filter.1 (h1 ha)).2
                rw [show n.choose j * n.choose (n-j) = (powersetCard j (univ.filter p) ×ˢ powersetCard (n-j) (univ.filter (fun t => ¬ p t))).card by rw [card_product, card_powersetCard, card_powersetCard, hL, hR]]
                apply card_nbij' (fun V => (V.filter p, V.filter (fun t => ¬ p t))) (fun ab => ab.1 ∪ ab.2)
                · intro V hV
                  simp only [coe_filter, mem_powersetCard, mem_univ, subset_univ, true_and, Set.mem_setOf_eq] at hV
                  simp only [coe_product, Set.mem_prod, Set.mem_setOf_eq, mem_coe, mem_powersetCard]
                  refine ⟨⟨filter_subset_filter _ (subset_univ _), hV.2⟩, filter_subset_filter _ (subset_univ _), ?_⟩
                  have := card_filter_add_card_filter_not (s := V) p
                  obtain ⟨hV1, hV2⟩ := hV
                  simp only [p] at this ⊢; omega
                · intro ab hab
                  simp only [coe_product, Set.mem_prod, Set.mem_setOf_eq, mem_coe,
                    mem_powersetCard] at hab
                  obtain ⟨⟨h1, h2⟩, h3, h4⟩ := hab
                  obtain ⟨k1, _, kd⟩ := key ab h1 h3
                  have hjn : ab.1.card ≤ n := by have := card_le_card h1; omega
                  simp only [coe_filter, mem_powersetCard, mem_univ, subset_univ, true_and, Set.mem_setOf_eq]
                  refine ⟨?_, ?_⟩
                  · rw [card_union_of_disjoint kd]; omega
                  · rw [k1, h2]
                · intro V _; ext t; simp only [mem_union, mem_filter]; tauto
                · intro ab hab
                  simp only [coe_product, Set.mem_prod, Set.mem_setOf_eq, mem_coe,
                    mem_powersetCard] at hab
                  obtain ⟨⟨h1, h2⟩, h3, h4⟩ := hab
                  obtain ⟨k1, k2, _⟩ := key ab h1 h3
                  simp only [k1, k2]
              obtain ⟨C, hC, hup⟩ : ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n → ∀ x : Fin (n+n) → MultiDim.Cov q 1,
                  MultiDim.Admissible S x → PigeonholeDesign.Upper.crdExp x ≤ C * Real.sqrt ((n+n : ℕ) : ℝ) := by
                have ML : ∀ (N K : ℕ) (ℓ : Fin N → ℕ) (m : ℕ) (A B : Finset (Fin N)), A.card = m → B.card = m →
                    (∀ t ∈ A, ℓ t ≤ K) → (∀ t ∈ B, ℓ t ≤ K) → ∃ f : Fin N → Fin N, Set.BijOn f A B ∧
                    ∑ a ∈ A, |(ℓ a : ℝ) - ℓ (f a)| ≤ ∑ k ∈ range K, |(∑ t ∈ A, if ℓ t ≤ k then (1:ℝ) else 0)
                        - ∑ t ∈ B, if ℓ t ≤ k then (1:ℝ) else 0| := by
                  intro N K ℓ m
                  induction m with
                  | zero =>
                    intro A B hA hB _ _
                    rw [card_eq_zero] at hA hB
                    subst hA hB
                    exact ⟨id, by simp, by simp⟩
                  | succ m ih =>
                    intro A B hA hB hAK hBK
                    obtain ⟨a, haA, ha⟩ := exists_min_image A ℓ (card_pos.1 (by omega))
                    obtain ⟨b, hbB, hb⟩ := exists_min_image B ℓ (card_pos.1 (by omega))
                    obtain ⟨f', hf', hsum⟩ := ih (A.erase a) (B.erase b) (by rw [card_erase_of_mem haA]; omega)
                      (by rw [card_erase_of_mem hbB]; omega) (fun t ht => hAK t (mem_of_mem_erase ht))
                      (fun t ht => hBK t (mem_of_mem_erase ht))
                    refine ⟨Function.update f' a b, ?_, ?_⟩
                    · have h1 : Set.BijOn (Function.update f' a b) (A.erase a : Set (Fin N)) (B.erase b) := by
                        refine hf'.congr ?_
                        intro t ht
                        have : t ≠ a := by simpa using (mem_erase.1 ht).1
                        simp [Function.update_of_ne this]
                      have h2 := h1.insert (a := a) (by simp)
                      rw [Function.update_self] at h2
                      convert h2 using 1
                      · rw [coe_erase, Set.insert_sdiff_singleton, Set.insert_eq_of_mem (by simpa using haA)]
                      · rw [coe_erase, Set.insert_sdiff_singleton, Set.insert_eq_of_mem (by simpa using hbB)]
                    · rw [← add_sum_erase A _ haA, Function.update_self]
                      have e1 : ∑ x ∈ A.erase a, |(ℓ x : ℝ) - ℓ (Function.update f' a b x)|
                          = ∑ x ∈ A.erase a, |(ℓ x : ℝ) - ℓ (f' x)| := by
                        apply sum_congr rfl; intro t ht
                        rw [Function.update_of_ne (mem_erase.1 ht).1]
                      rw [e1]
                      have hpt : ∀ k ∈ range K, |(∑ t ∈ A, if ℓ t ≤ k then (1:ℝ) else 0)
                          - ∑ t ∈ B, if ℓ t ≤ k then (1:ℝ) else 0| =
                          |(∑ t ∈ A.erase a, if ℓ t ≤ k then (1:ℝ) else 0)
                          - ∑ t ∈ B.erase b, if ℓ t ≤ k then (1:ℝ) else 0| +
                          (if min (ℓ a) (ℓ b) ≤ k ∧ k < max (ℓ a) (ℓ b) then 1 else 0) := by
                        intro k _
                        rw [← add_sum_erase A _ haA, ← add_sum_erase B _ hbB]
                        have hα : 0 ≤ ∑ t ∈ A.erase a, if ℓ t ≤ k then (1:ℝ) else 0 :=
                          sum_nonneg fun _ _ => by split_ifs <;> norm_num
                        have hβ : 0 ≤ ∑ t ∈ B.erase b, if ℓ t ≤ k then (1:ℝ) else 0 :=
                          sum_nonneg fun _ _ => by split_ifs <;> norm_num
                        rcases le_total (ℓ a) (ℓ b) with hab | hab
                        · rw [min_eq_left hab, max_eq_right hab]
                          by_cases h1 : ℓ a ≤ k
                          · by_cases h2 : ℓ b ≤ k
                            · simp only [h1, h2, true_and, not_lt.2 h2, if_true, if_false]; ring_nf
                            · have h0 : ∑ t ∈ B.erase b, (if ℓ t ≤ k then (1:ℝ) else 0) = 0 := by
                                apply sum_eq_zero; intro t ht
                                have := hb t (mem_of_mem_erase ht)
                                rw [if_neg (by omega)]
                              simp only [h1, h2, true_and, not_le.1 h2, if_true, if_false, h0]
                              rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]; ring
                          · have h2 : ¬ ℓ b ≤ k := by omega
                            simp only [h1, h2, false_and, if_false]; ring_nf
                        · rw [min_eq_right hab, max_eq_left hab]
                          by_cases h1 : ℓ b ≤ k
                          · by_cases h2 : ℓ a ≤ k
                            · simp only [h1, h2, true_and, not_lt.2 h2, if_true, if_false]; ring_nf
                            · have h0 : ∑ t ∈ A.erase a, (if ℓ t ≤ k then (1:ℝ) else 0) = 0 := by
                                apply sum_eq_zero; intro t ht
                                have := ha t (mem_of_mem_erase ht)
                                rw [if_neg (by omega)]
                              simp only [h1, h2, true_and, not_le.1 h2, if_true, if_false, h0]
                              rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]; ring
                          · have h2 : ¬ ℓ a ≤ k := by omega
                            simp only [h1, h2, false_and, if_false]; ring_nf
                      rw [sum_congr rfl hpt, sum_add_distrib, sum_boole]
                      have hK : (range K).filter (fun k => min (ℓ a) (ℓ b) ≤ k ∧ k < max (ℓ a) (ℓ b))
                          = Ico (min (ℓ a) (ℓ b)) (max (ℓ a) (ℓ b)) := by
                        ext k; simp only [mem_filter, mem_range, mem_Ico]
                        have := hAK a haA; have := hBK b hbB; omega
                      rw [hK, Nat.card_Ico]
                      have : |(ℓ a : ℝ) - ℓ b| = ((max (ℓ a) (ℓ b) - min (ℓ a) (ℓ b) : ℕ) : ℝ) := by
                        rcases le_total (ℓ a) (ℓ b) with hab | hab
                        · rw [max_eq_right hab, min_eq_left hab, Nat.cast_sub hab, abs_sub_comm,
                            abs_of_nonneg (sub_nonneg.2 (by exact_mod_cast hab))]
                        · rw [max_eq_left hab, min_eq_right hab, Nat.cast_sub hab,
                            abs_of_nonneg (sub_nonneg.2 (by exact_mod_cast hab))]
                      rw [this]; linarith
                have VC : ∀ n : ℕ, 1 ≤ n → ∀ g : Fin (n+n) → ℝ, (∀ t, 0 ≤ g t ∧ g t ≤ 1) →
                    ∑ V ∈ (univ : Finset (Fin (n+n))).powersetCard n,
                      |∑ t, g t * (if t ∈ V then (1:ℝ) else -1)|
                      ≤ ((univ : Finset (Fin (n+n))).powersetCard n).card * Real.sqrt ((n+n : ℕ) : ℝ) := by
                  intro n hn g hg
                  set P := (univ : Finset (Fin (n+n))).powersetCard n with hP
                  set ε : Finset (Fin (n+n)) → Fin (n+n) → ℝ := fun V t => if t ∈ V then (1:ℝ) else -1 with hε
                  set F : Fin (n+n) → Fin (n+n) → ℝ := fun s t => ∑ V ∈ P, ε V s * ε V t with hF
                  have hsq : ∀ V u, ε V u * ε V u = 1 := by intro V u; simp only [ε]; split_ifs <;> norm_num
                  have hdiag : ∀ s, F s s = P.card := by
                    intro s; simp only [F, hsq, sum_const, nsmul_eq_mul, mul_one]
                  have hrow : ∀ s, ∑ t, F s t = 0 := by
                    intro s; simp only [F]; rw [sum_comm]
                    apply sum_eq_zero; intro V hV
                    rw [← mul_sum]
                    have hc := (mem_powersetCard.1 hV).2
                    have : ∑ t, ε V t = 0 := by
                      have e : ∀ t, ε V t = 2 * (if t ∈ V then (1:ℝ) else 0) - 1 := by
                        intro t; simp only [ε]; split_ifs <;> norm_num
                      simp only [e, sum_sub_distrib, ← mul_sum, sum_boole, filter_mem_eq_inter, univ_inter, hc,
                        sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
                      push_cast; ring
                    rw [this, mul_zero]
                  have hinv : ∀ s t t', t ≠ s → t' ≠ s → F s t = F s t' := by
                    intro s t t' hts hts'
                    set σ := Equiv.swap t t'
                    simp only [F]
                    apply sum_nbij' (fun V => V.map σ.toEmbedding) (fun V => V.map σ.toEmbedding)
                    · intro V hV
                      simp only [P, mem_coe, mem_powersetCard] at hV ⊢
                      exact ⟨subset_univ _, by rw [card_map]; exact hV.2⟩
                    · intro V hV
                      simp only [P, mem_coe, mem_powersetCard] at hV ⊢
                      exact ⟨subset_univ _, by rw [card_map]; exact hV.2⟩
                    · intro V _; ext u; rw [mem_map_equiv, mem_map_equiv]; simp [σ, Equiv.swap_apply_self]
                    · intro V _; ext u; rw [mem_map_equiv, mem_map_equiv]; simp [σ, Equiv.swap_apply_self]
                    · intro V _
                      simp only [ε, mem_map_equiv, σ, Equiv.symm_swap]
                      rw [Equiv.swap_apply_of_ne_of_ne hts.symm hts'.symm, Equiv.swap_apply_right]
                  have hoff : ∀ s t, t ≠ s → F s t ≤ 0 := by
                    intro s t hts
                    have h := hrow s
                    rw [← add_sum_erase _ _ (mem_univ s), hdiag] at h
                    have h2 : ∑ u ∈ univ.erase s, F s u = ((n+n:ℕ) - 1 : ℝ) * F s t := by
                      rw [sum_congr rfl (fun u hu => hinv s u t (mem_erase.1 hu).1 hts), sum_const,
                        card_erase_of_mem (mem_univ _), card_univ, Fintype.card_fin, nsmul_eq_mul,
                        Nat.cast_sub (by omega)]
                      simp
                    rw [h2] at h
                    have hP0 : (0:ℝ) ≤ P.card := by positivity
                    have hN : (1:ℝ) ≤ ((n+n:ℕ):ℝ) - 1 := by
                      push_cast; linarith [(by exact_mod_cast hn : (1:ℝ) ≤ n)]
                    by_contra hc; push_neg at hc
                    nlinarith [mul_pos (by linarith : (0:ℝ) < ((n+n:ℕ):ℝ) - 1) hc]
                  have hS2 : ∑ V ∈ P, (∑ t, g t * ε V t) ^ 2 ≤ P.card * (n+n : ℕ) := by
                    have e : ∑ V ∈ P, (∑ t, g t * ε V t) ^ 2 = ∑ s, ∑ t, g s * g t * F s t := by
                      calc _ = ∑ V ∈ P, ∑ s, ∑ t, g s * g t * (ε V s * ε V t) := by
                            apply sum_congr rfl; intro V _; rw [sq, sum_mul_sum]; apply sum_congr rfl
                            intro s _; apply sum_congr rfl; intro t _; ring
                        _ = ∑ s, ∑ V ∈ P, ∑ t, g s * g t * (ε V s * ε V t) := sum_comm
                        _ = ∑ s, ∑ t, ∑ V ∈ P, g s * g t * (ε V s * ε V t) := by
                            apply sum_congr rfl; intro s _; exact sum_comm
                        _ = _ := by simp only [F, mul_sum]
                    rw [e]
                    have hrow2 : ∀ s, ∑ t, g s * g t * F s t ≤ P.card := by
                      intro s
                      rw [← add_sum_erase _ _ (mem_univ s), hdiag]
                      have h1 : ∑ t ∈ univ.erase s, g s * g t * F s t ≤ 0 := by
                        apply sum_nonpos; intro t ht
                        exact mul_nonpos_of_nonneg_of_nonpos (mul_nonneg (hg s).1 (hg t).1) (hoff s t (mem_erase.1 ht).1)
                      have h2 : g s * g s * P.card ≤ P.card := by
                        have : g s * g s ≤ 1 := by nlinarith [hg s]
                        have hP0 : (0:ℝ) ≤ P.card := by positivity
                        nlinarith
                      linarith
                    calc ∑ s, ∑ t, g s * g t * F s t ≤ ∑ s : Fin (n+n), (P.card : ℝ) := sum_le_sum fun s _ => hrow2 s
                      _ = _ := by rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]; ring
                  have hCS := sq_sum_le_card_mul_sum_sq (s := P) (f := fun V => |∑ t, g t * ε V t|)
                  simp only [sq_abs] at hCS
                  have h3 : (∑ V ∈ P, |∑ t, g t * ε V t|) ^ 2 ≤ ((P.card : ℝ) * Real.sqrt ((n+n:ℕ):ℝ)) ^ 2 := by
                    rw [mul_pow, Real.sq_sqrt (by positivity)]
                    have hP0 : (0:ℝ) ≤ P.card := by positivity
                    calc _ ≤ _ := hCS
                      _ ≤ (P.card : ℝ) * (P.card * (n+n:ℕ)) := mul_le_mul_of_nonneg_left hS2 hP0
                      _ = _ := by ring
                  have h0 : 0 ≤ (P.card:ℝ) * Real.sqrt ((n+n:ℕ):ℝ) := by positivity
                  exact le_of_pow_le_pow_left₀ two_ne_zero h0 h3
                set Pr := Fintype.piFinset S with hPr
                set M := Pr.card with hM
                set Bd : ℝ := ∑ i, ∑ v ∈ S i, |v| + 1 with hBd
                set R : ℕ := ⌈2 * Bd⌉₊ + 1 with hR
                refine ⟨M * R + 2, by positivity, ?_⟩
                intro n hn x hx
                let idx : (Fin q → ℝ) → ℕ := fun z => if h : z ∈ Pr then (Pr.equivFin ⟨z, h⟩ : ℕ) else 0
                let prof : Fin (n+n) → (Fin q → ℝ) := fun t i => x t (Sum.inl i)
                have hprof : ∀ t, prof t ∈ Pr := by
                  intro t; rw [hPr, Fintype.mem_piFinset]; intro i; exact hx.1 t i
                have hidx : ∀ t, idx (prof t) < M := by
                  intro t; simp only [idx, dif_pos (hprof t)]; exact (Pr.equivFin _).isLt
                have hinj : ∀ a b, idx (prof a) = idx (prof b) → prof a = prof b := by
                  intro a b h
                  simp only [idx, dif_pos (hprof a), dif_pos (hprof b)] at h
                  have := (Pr.equivFin).injective (Fin.ext h)
                  exact congrArg Subtype.val this
                set s : ℕ := ⌈Real.sqrt ((n+n) : ℝ)⌉₊ with hsdef
                have hsq : Real.sqrt ((n+n):ℝ) ≤ s := Nat.le_ceil _
                have hN1 : (1:ℝ) ≤ (n+n) := by push_cast; linarith [(by exact_mod_cast hn : (1:ℝ) ≤ n)]
                have hs1 : (1:ℝ) ≤ s := le_trans (by rw [Real.one_le_sqrt]; exact hN1) hsq
                let c : Fin (n+n) → ℝ := fun t => x t (Sum.inr 0)
                have hc : ∀ t, 0 ≤ c t ∧ c t ≤ 1 := fun t => hx.2 t 0
                let ℓ : Fin (n+n) → ℕ := fun t => idx (prof t) * (s * R) + ⌈c t * s⌉₊
                have hce : ∀ t, c t * s ≤ ⌈c t * s⌉₊ ∧ (⌈c t * s⌉₊ : ℝ) < c t * s + 1 ∧ (⌈c t * s⌉₊ : ℝ) ≤ s := by
                  intro t
                  refine ⟨Nat.le_ceil _, Nat.ceil_lt_add_one (by nlinarith [hc t]), ?_⟩
                  have : ⌈c t * s⌉₊ ≤ s := Nat.ceil_le.2 (by nlinarith [hc t])
                  exact_mod_cast this
                set K := M * s * R + s with hK
                have hℓK : ∀ t, ℓ t ≤ K := by
                  intro t
                  have h1 := hidx t
                  have h2 : ⌈c t * s⌉₊ ≤ s := by exact_mod_cast (hce t).2.2
                  have h3 : idx (prof t) * (s * R) ≤ (M - 1) * (s * R) := Nat.mul_le_mul_right _ (by omega)
                  have h4 : (M - 1) * (s * R) + s * R = M * s * R := by
                    rw [← Nat.succ_mul]; rw [Nat.succ_eq_add_one, Nat.sub_add_cancel (by omega)]; ring
                  simp only [ℓ, hK]; omega
                have hnorm : ∀ t, ‖x t‖ ≤ Bd := by
                  intro t
                  rw [EuclideanSpace.norm_eq]
                  have h1 : Real.sqrt (∑ j, ‖x t j‖ ^ 2) ≤ ∑ j, ‖x t j‖ := by
                    rw [Real.sqrt_le_left (sum_nonneg fun _ _ => norm_nonneg _)]
                    exact sum_sq_le_sq_sum_of_nonneg fun _ _ => norm_nonneg _
                  refine h1.trans ?_
                  rw [Fintype.sum_sum_type]
                  have h2 : ∀ i, ‖x t (Sum.inl i)‖ ≤ ∑ v ∈ S i, |v| := by
                    intro i
                    exact single_le_sum (f := fun v => |v|) (fun _ _ => abs_nonneg _) (hx.1 t i)
                  have h3 : ∑ j : Fin 1, ‖x t (Sum.inr j)‖ ≤ 1 := by
                    simp only [Fin.sum_univ_one, Real.norm_eq_abs]
                    rw [abs_of_nonneg (hx.2 t 0).1]; exact (hx.2 t 0).2
                  have := sum_le_sum fun i (_ : i ∈ univ) => h2 i
                  simp only [hBd]; linarith
                have hRB : 2 * Bd ≤ (R:ℝ) - 1 := by
                  simp only [hR]; push_cast; linarith [Nat.le_ceil (2 * Bd)]
                have hd : ∀ a b, (s:ℝ) * dist (x a) (x b) ≤ |(ℓ a:ℝ) - ℓ b| + 1 := by
                  intro a b
                  have ha := hce a; have hb := hce b
                  by_cases hp : prof a = prof b
                  · have hdist : dist (x a) (x b) = |c a - c b| := by
                      rw [EuclideanSpace.dist_eq, Fintype.sum_sum_type]
                      have : ∀ i, dist (x a (Sum.inl i)) (x b (Sum.inl i)) = 0 := by
                        intro i; rw [show x a (Sum.inl i) = x b (Sum.inl i) from congrFun hp i, dist_self]
                      simp only [this, Fin.sum_univ_one]
                      simp [Real.dist_eq, c, Real.sqrt_sq_eq_abs]
                    have hl : (ℓ a : ℝ) - ℓ b = (⌈c a * s⌉₊ : ℝ) - ⌈c b * s⌉₊ := by
                      simp only [ℓ, hp]; push_cast; ring
                    rw [hdist, hl, ← abs_of_pos (by linarith : (0:ℝ) < s), ← abs_mul, abs_of_pos (by linarith : (0:ℝ) < s)]
                    have e1 := le_abs_self ((⌈c a * s⌉₊ : ℝ) - ⌈c b * s⌉₊)
                    have e2 := neg_abs_le ((⌈c a * s⌉₊ : ℝ) - ⌈c b * s⌉₊)
                    rw [abs_le]; constructor <;> linarith [ha.1, ha.2.1, hb.1, hb.2.1, e1, e2]
                  · have hi : idx (prof a) ≠ idx (prof b) := fun h => hp (hinj a b h)
                    have hdist : dist (x a) (x b) ≤ (R:ℝ) - 1 := by
                      have := dist_le_norm_add_norm (x a) (x b)
                      linarith [hnorm a, hnorm b]
                    have hR1 : (1:ℝ) ≤ R := by simp only [hR]; push_cast; linarith [Nat.cast_nonneg (α := ℝ) ⌈2*Bd⌉₊]
                    have hlow : (s:ℝ) * R - s ≤ |(ℓ a:ℝ) - ℓ b| := by
                      simp only [ℓ]; push_cast
                      rcases Nat.lt_or_gt_of_ne hi with h | h
                      · have h' : (idx (prof a) : ℝ) + 1 ≤ idx (prof b) := by exact_mod_cast h
                        rw [abs_sub_comm]
                        refine le_trans ?_ (le_abs_self _)
                        have : 0 ≤ ((idx (prof b) : ℝ) - idx (prof a) - 1) * (s * R) := by
                          exact mul_nonneg (by linarith) (mul_nonneg (by linarith) (by linarith))
                        linarith [(hce a).2.2, Nat.cast_nonneg (α := ℝ) ⌈c b * s⌉₊]
                      · have h' : (idx (prof b) : ℝ) + 1 ≤ idx (prof a) := by exact_mod_cast h
                        refine le_trans ?_ (le_abs_self _)
                        have : 0 ≤ ((idx (prof a) : ℝ) - idx (prof b) - 1) * (s * R) := by
                          exact mul_nonneg (by linarith) (mul_nonneg (by linarith) (by linarith))
                        linarith [(hce b).2.2, Nat.cast_nonneg (α := ℝ) ⌈c a * s⌉₊]
                    have := mul_le_mul_of_nonneg_left hdist (by linarith : (0:ℝ) ≤ s)
                    linarith
                -- discrepancy bound per V
                set P := (univ : Finset (Fin (n+n))).powersetCard n with hP
                have hPpos : (0:ℝ) < P.card := by
                  rw [hP, card_powersetCard, card_univ, Fintype.card_fin]; exact_mod_cast Nat.choose_pos (by omega)
                have DB : ∀ V : Finset (Fin (n+n)), V ∈ P → PigeonholeDesign.Upper.discrepancy x (fun t => decide (t ∉ V))
                    ≤ (∑ k ∈ range K, |∑ t, (if ℓ t ≤ k then (1:ℝ) else 0) * (if t ∈ V then (1:ℝ) else -1)| + n) / s := by
                  intro V hV
                  have hVc : V.card = n := (mem_powersetCard.1 hV).2
                  have hVcc : Vᶜ.card = n := by rw [card_compl, Fintype.card_fin, hVc]; omega
                  obtain ⟨f, hf, hfs⟩ := ML (n+n) K ℓ n V Vᶜ hVc hVcc (fun t _ => hℓK t) (fun t _ => hℓK t)
                  have hA : ∀ t, t ∈ V ↔ decide (t ∉ V) = false := by intro t; simp
                  have step1 : PigeonholeDesign.Upper.discrepancy x (fun t => decide (t ∉ V))
                      ≤ ∑ t ∈ V, dist (x t) (x (f t)) := by
                    unfold PigeonholeDesign.Upper.discrepancy
                    let e : {t // decide (t ∉ V) = false} ≃ {t // decide (t ∉ V) = true} :=
                      (Equiv.subtypeEquivRight (fun t => by simp : ∀ t, decide (t ∉ V) = false ↔ t ∈ (V : Set (Fin (n+n))))).trans
                        ((hf.equiv f).trans (Equiv.subtypeEquivRight (fun t => by simp : ∀ t, t ∈ ((Vᶜ : Finset (Fin (n+n))) : Set (Fin (n+n))) ↔ decide (t ∉ V) = true)))
                    refine (ciInf_le ⟨0, by rintro _ ⟨e, rfl⟩; exact sum_nonneg fun _ _ => dist_nonneg⟩ e).trans ?_
                    rw [Finset.sum_subtype V hA (fun t => dist (x t) (x (f t)))]
                    apply le_of_eq; rfl
                  have hgε : ∀ k, ∑ t, (if ℓ t ≤ k then (1:ℝ) else 0) * (if t ∈ V then (1:ℝ) else -1)
                      = (∑ t ∈ V, if ℓ t ≤ k then (1:ℝ) else 0) - ∑ t ∈ Vᶜ, if ℓ t ≤ k then (1:ℝ) else 0 := by
                    intro k
                    rw [← sum_add_sum_compl V]
                    have e1 : ∑ t ∈ V, (if ℓ t ≤ k then (1:ℝ) else 0) * (if t ∈ V then (1:ℝ) else -1)
                        = ∑ t ∈ V, if ℓ t ≤ k then (1:ℝ) else 0 :=
                      sum_congr rfl fun t ht => by rw [if_pos ht, mul_one]
                    have e2 : ∑ t ∈ Vᶜ, (if ℓ t ≤ k then (1:ℝ) else 0) * (if t ∈ V then (1:ℝ) else -1)
                        = -∑ t ∈ Vᶜ, if ℓ t ≤ k then (1:ℝ) else 0 := by
                      rw [← sum_neg_distrib]
                      exact sum_congr rfl fun t ht => by rw [if_neg (mem_compl.1 ht)]; ring
                    rw [e1, e2]; ring
                  simp only [hgε]
                  refine step1.trans ?_
                  rw [le_div_iff₀ (by linarith), sum_mul]
                  calc ∑ t ∈ V, dist (x t) (x (f t)) * s ≤ ∑ t ∈ V, (|(ℓ t:ℝ) - ℓ (f t)| + 1) :=
                        sum_le_sum fun t _ => by rw [mul_comm]; exact hd t (f t)
                    _ = ∑ t ∈ V, |(ℓ t:ℝ) - ℓ (f t)| + n := by rw [sum_add_distrib, sum_const, hVc]; simp
                    _ ≤ _ := add_le_add hfs le_rfl
                have hN2 : (n+n) / 2 = n := by omega
                have hch : (n+n).choose n = P.card := by rw [hP, card_powersetCard, card_univ, Fintype.card_fin]
                unfold PigeonholeDesign.Upper.crdExp
                rw [hN2, ← hP, hch, div_le_iff₀ hPpos]
                have hsum1 := sum_le_sum DB
                rw [← sum_div, sum_add_distrib, sum_comm, sum_const, nsmul_eq_mul] at hsum1
                have hVCk : ∀ k ∈ range K, ∑ V ∈ P, |∑ t, (if ℓ t ≤ k then (1:ℝ) else 0) * (if t ∈ V then (1:ℝ) else -1)|
                    ≤ P.card * Real.sqrt ((n+n:ℕ):ℝ) :=
                  fun k _ => VC n hn _ (fun t => by split_ifs <;> norm_num)
                have hsum2 := sum_le_sum hVCk
                rw [sum_const, card_range, nsmul_eq_mul] at hsum2
                have hs0 : (0:ℝ) < s := by linarith
                have hKs : (K:ℝ) = (M * R + 1) * s := by simp only [hK]; push_cast; ring
                have hsqN : Real.sqrt ((n+n:ℕ):ℝ) * Real.sqrt ((n+n:ℕ):ℝ) = (n+n:ℕ) := Real.mul_self_sqrt (by positivity)
                have hNn : ((n+n:ℕ):ℝ) = 2 * n := by push_cast; ring
                have hn_le : (n:ℝ) ≤ s * Real.sqrt ((n+n:ℕ):ℝ) := by
                  have h0 := Real.sqrt_nonneg ((n+n:ℕ):ℝ)
                  have hsq' : Real.sqrt ((n+n:ℕ):ℝ) ≤ s := by push_cast; exact hsq
                  linarith [mul_le_mul_of_nonneg_right hsq' h0, Nat.cast_nonneg (α := ℝ) n]
                rw [le_div_iff₀ hs0] at hsum1
                rw [hKs] at hsum2
                have hfin : (∑ V ∈ P, PigeonholeDesign.Upper.discrepancy x (fun t => decide (t ∉ V))) * s
                    ≤ (((M:ℝ) * R + 2) * Real.sqrt ((n+n:ℕ):ℝ) * P.card) * s := by
                  linarith [mul_le_mul_of_nonneg_left hn_le hPpos.le]
                have := le_of_mul_le_mul_right hfin hs0
                push_cast at this ⊢
                linarith
              refine ⟨1/12, C, by norm_num, hC, 2, ?_⟩
              intro T hT hTe
              obtain ⟨n, rfl⟩ := hTe
              have hn2 : (n+n)/2 = n := by omega
              have hn1 : 1 ≤ n := by omega
              refine ⟨fun x hx => hup n hn1 x hx, ?_⟩
              let s0 : Fin q → ℝ := fun i => (hne i).choose
              let x0 : Fin (n+n) → MultiDim.Cov q 1 :=
                fun t => WithLp.toLp 2 (Sum.elim s0 (fun _ => if t.val < n then (1:ℝ) else 0))
              refine ⟨x0, ⟨?_, ?_⟩, ?_⟩
              · intro t i; exact (hne i).choose_spec
              · intro t j; simp only [x0, PiLp.toLp_apply, Sum.elim_inr]; split_ifs <;> norm_num
              set φ : Fin (n+n) → ℝ := fun t => if t.val < n then 1 else 0 with hφdef
              have hφ : ∀ s t, |φ s - φ t| ≤ dist (x0 s) (x0 t) := by
                intro s t
                have := PiLp.dist_apply_le (x0 s) (x0 t) (Sum.inr 0)
                simpa [x0, φ, Real.dist_eq] using this
              set jf : Finset (Fin (n+n)) → ℕ := fun V => (V.filter (fun t => t.val < n)).card with hjf
              have hsum : ∀ V : Finset (Fin (n+n)), ∑ t ∈ V, φ t - ∑ t ∈ Vᶜ, φ t = 2 * (jf V : ℝ) - n := by
                intro V
                have h1 : ∀ W : Finset (Fin (n+n)), ∑ t ∈ W, φ t = ((W.filter (fun t => t.val < n)).card : ℝ) := by
                  intro W; simp only [φ]; rw [Finset.sum_boole]
                have h2 := Finset.sum_add_sum_compl V φ
                rw [h1 univ, h1 V, h1 Vᶜ, Fin.card_filter_val_lt] at h2
                rw [h1 V, h1 Vᶜ]
                have : min (n+n) n = n := by omega
                rw [this] at h2
                simp only [jf]; linarith
              set P := (univ : Finset (Fin (n+n))).powersetCard n with hP
              set K := (n-1)/2 with hK
              have hKn : K + 1 ≤ n := by omega
              have hlow1 : (n : ℝ) * (Nat.choose (n-1) K : ℝ) ^ 2 ≤
                  ∑ V ∈ P, PigeonholeDesign.Upper.discrepancy x0 (fun t => decide (t ∉ V)) := by
                calc (n : ℝ) * (Nat.choose (n-1) K : ℝ) ^ 2
                    = ∑ k ∈ range (K+1), ((n:ℝ) - 2 * k) * (Nat.choose n k : ℝ) ^ 2 := (T1 n hn1 K hKn).symm
                  _ = ∑ k ∈ range (K+1), ∑ V ∈ P with jf V = k, |2 * (jf V : ℝ) - n| := by
                    apply sum_congr rfl
                    intro k hk
                    rw [mem_range] at hk
                    have e : ∀ V ∈ P.filter (fun V => jf V = k), |2 * (jf V : ℝ) - n| = (n:ℝ) - 2 * k := by
                      intro V hV
                      rw [(mem_filter.1 hV).2, abs_of_nonpos (by
                        have : (2 * k : ℝ) ≤ n := by exact_mod_cast (by omega : 2 * k ≤ n)
                        linarith)]
                      ring
                    rw [sum_congr rfl e, sum_const, nsmul_eq_mul]
                    have := C1 n k
                    simp only [jf] at this ⊢
                    rw [this, Nat.choose_symm (by omega)]
                    push_cast; ring
                  _ ≤ ∑ k ∈ range (n+1), ∑ V ∈ P with jf V = k, |2 * (jf V : ℝ) - n| := by
                    apply sum_le_sum_of_subset_of_nonneg
                    · intro k; simp only [mem_range]; omega
                    · intro _ _ _; exact sum_nonneg fun _ _ => abs_nonneg _
                  _ = ∑ V ∈ P, |2 * (jf V : ℝ) - n| := by
                    refine sum_fiberwise_of_maps_to (fun V hV => ?_) _
                    rw [mem_range]
                    have h1 := card_filter_le V (fun t : Fin (n+n) => t.val < n)
                    have h2 := (mem_powersetCard.1 hV).2
                    simp only [jf]; omega
                  _ ≤ _ := by
                    apply sum_le_sum
                    intro V hV
                    rw [← hsum V]
                    exact G1 n x0 V (mem_powersetCard.1 hV).2 φ hφ
              unfold PigeonholeDesign.Upper.crdExp
              rw [hn2]
              have hNc : (n+n).choose n = Nat.centralBinom n := by rw [Nat.centralBinom_eq_two_mul_choose, two_mul]
              rw [hNc]
              set N : ℝ := (Nat.centralBinom n : ℝ) with hN
              have hNpos : 0 < N := by rw [hN]; exact_mod_cast Nat.centralBinom_pos n
              set c2 : ℝ := (Nat.choose (n-1) K : ℝ) ^ 2 with hc2
              have hc2n : 0 ≤ c2 := by positivity
              have hb2 : N ^ 2 * (3 * n + 1) ≤ 16 ^ n := by
                have := B2 n; rw [hN]; exact_mod_cast this
              have hb3 : (4:ℝ) ^ (n-1) ≤ c2 * (2 * n + 1) := by
                have := B3 (n-1)
                have e : ((n-1 : ℕ) : ℝ) = n - 1 := by rw [Nat.cast_sub hn1]; simp
                rw [e] at this
                rw [hc2, hK]; nlinarith [this]
              set u : ℝ := (4:ℝ) ^ (n-1) with hu
              have hu0 : 0 < u := by positivity
              have h16 : (16:ℝ) ^ n = 16 * u ^ 2 := by
                rw [hu, ← pow_mul, show (16:ℝ) = 4 ^ 2 by norm_num, ← pow_mul]
                rw [show (4:ℝ)^2 = 16 by norm_num]
                obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n-1, by omega⟩
                simp only [Nat.add_sub_cancel]
                rw [show 2 * (m+1) = (m*2) + 2 by ring, pow_add]; norm_num; ring
              have hnr : (1:ℝ) ≤ n := by exact_mod_cast hn1
              have hu2 : u ^ 2 ≤ (c2 * (2 * n + 1)) ^ 2 := by
                exact pow_le_pow_left₀ hu0.le hb3 2
              have hsq : 2 * n * N ^ 2 ≤ 144 * ((n:ℝ) * c2) ^ 2 := by
                have h1 : N ^ 2 * (3 * n + 1) ≤ 16 * (c2 * (2 * n + 1)) ^ 2 := by linarith only [hb2, h16, hu2]
                have hn0 : (0:ℝ) ≤ n := by linarith only [hnr]
                have h3 : (2 * n * N ^ 2) * (3 * n + 1) ≤ (144 * ((n:ℝ) * c2) ^ 2) * (3 * n + 1) := by
                  have hnn : (1:ℝ) ≤ n * n := by nlinarith only [hnr]
                  have : 32 * (2 * (n:ℝ) + 1) ^ 2 ≤ 144 * n * (3 * n + 1) := by linarith only [hnn, hnr]
                  linarith only [mul_le_mul_of_nonneg_left h1 (by linarith only [hnr] : (0:ℝ) ≤ 2 * n),
                    mul_le_mul_of_nonneg_left this (mul_nonneg hn0 (sq_nonneg c2))]
                exact le_of_mul_le_mul_right h3 (by linarith only [hnr])
              have hsqrt : Real.sqrt ((n+n : ℕ) : ℝ) * N ≤ 12 * ((n:ℝ) * c2) := by
                have h0 : 0 ≤ 12 * ((n:ℝ) * c2) :=
                  mul_nonneg (by norm_num) (mul_nonneg (by linarith only [hnr]) hc2n)
                have hss : Real.sqrt ((n+n : ℕ) : ℝ) ^ 2 = 2 * n := by
                  rw [Real.sq_sqrt (Nat.cast_nonneg _)]; push_cast; ring
                exact le_of_pow_le_pow_left₀ two_ne_zero h0 (by rw [mul_pow, hss]; linarith only [hsq])
              rw [le_div_iff₀ hNpos]
              linarith only [hlow1, hsqrt]
