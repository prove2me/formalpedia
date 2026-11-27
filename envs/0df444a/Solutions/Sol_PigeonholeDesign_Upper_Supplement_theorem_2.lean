-- Prove2me | solution 1 for PigeonholeDesign.Upper.Supplement.theorem_2
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:34:57.47983+00:00
-- url     : https://prove2.me/submissions/f28f213d-162e-4a4f-9673-16dd03c79715

import Mathlib
import Definitions.Def_PigeonholeDesign_MultiDim_Setting
import Definitions.Def_PigeonholeDesign_Upper_Supplement_MatchedPair

open PigeonholeDesign
open PigeonholeDesign.Upper
open PigeonholeDesign.Upper.Supplement

theorem solution (q : ℕ) (hq : 1 ≤ q) (S : Fin q → Finset ℝ) (hS : ∀ i, (S i : Set ℝ) ⊆ Set.Icc 0 1)
    (hne : ∀ i, (S i).Nonempty)
    (h2 : ∃ i, 2 ≤ (S i).card) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∃ T₀ : ℕ, ∀ T : ℕ, T₀ ≤ T → Even T →
      (∀ x : Fin T → MultiDim.Cov q 0, MultiDim.Admissible S x →
          PigeonholeDesign.Upper.crdExp x ≤ C * Real.sqrt T) ∧
      (∃ x : Fin T → MultiDim.Cov q 0, MultiDim.Admissible S x ∧
          c * Real.sqrt T ≤ PigeonholeDesign.Upper.crdExp x) := by
            classical
            obtain ⟨i₀, hi₀⟩ := h2
            obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp hi₀
            choose z hz using hne
            let u : MultiDim.Cov q 0 := WithLp.toLp 2 (Sum.elim (Function.update z i₀ a) (fun j => j.elim0))
            let v : MultiDim.Cov q 0 := WithLp.toLp 2 (Sum.elim (Function.update z i₀ b) (fun j => j.elim0))
            have hu : ∀ i, u (Sum.inl i) ∈ S i := by
              intro i
              by_cases h : i = i₀
              · subst h; simpa [u] using ha
              · simpa [u, Function.update_of_ne h] using hz i
            have hv : ∀ i, v (Sum.inl i) ∈ S i := by
              intro i
              by_cases h : i = i₀
              · subst h; simpa [v] using hb
              · simpa [v, Function.update_of_ne h] using hz i
            have huv : u ≠ v := by
              intro h
              have := congrArg (fun y : MultiDim.Cov q 0 => y (Sum.inl i₀)) h
              simp [u, v] at this
              exact hab this
            have hduv : 0 < dist u v := dist_pos.mpr huv
            -- upper bound (hypergeometric second moment + type-wise matching)
            have hub : ∃ C : ℝ, 0 < C ∧ ∃ T₀ : ℕ, ∀ T : ℕ, T₀ ≤ T → Even T →
                ∀ x : Fin T → MultiDim.Cov q 0, MultiDim.Admissible S x →
                    PigeonholeDesign.Upper.crdExp x ≤ C * Real.sqrt T := by
              let Afin : Finset (MultiDim.Cov q 0) := (Fintype.piFinset S).image
                (fun f => WithLp.toLp 2 (Sum.elim f (fun j : Fin 0 => j.elim0)))
              obtain ⟨D', hD'⟩ := Metric.isBounded_iff.mp (Afin.finite_toSet.isBounded)
              set D : ℝ := max D' 0 with hDdef
              have hD0 : 0 ≤ D := le_max_right _ _
              set K : ℕ := Afin.card with hKdef
              have hK : Afin.card ≤ K := le_rfl
              have hAx : ∀ (T : ℕ) (x : Fin T → MultiDim.Cov q 0), MultiDim.Admissible S x → ∀ t, x t ∈ Afin := by
                intro T x hx t
                refine Finset.mem_image.mpr ⟨fun i => x t (Sum.inl i), Fintype.mem_piFinset.mpr (fun i => hx.1 t i), ?_⟩
                ext k
                cases k with
                | inl i => rfl
                | inr j => exact j.elim0
              have hdist : ∀ y ∈ Afin, ∀ y' ∈ Afin, dist y y' ≤ D := fun y hy y' hy' =>
                (hD' (Finset.mem_coe.mpr hy) (Finset.mem_coe.mpr hy')).trans (le_max_left _ _)
              -- type-wise matching: controls and treated at the same point are matched at cost 0
              have U1 : ∀ (T : ℕ) (x : Fin T → MultiDim.Cov q 0), MultiDim.Admissible S x → Even T →
                  ∀ V : Finset (Fin T), V.card = T / 2 →
                  PigeonholeDesign.Upper.discrepancy x (fun t => decide (t ∉ V)) ≤
                    D * ∑ y ∈ Afin, |(2 * ((V.filter (fun t => x t = y)).card : ℝ) -
                      ((Finset.univ.filter (fun t => x t = y)).card : ℝ))| := by
                clear * - hAx hdist hD0
                open Finset in
                focus
                  classical
                  intro T x hx hev V hV
                  have hxA := hAx T x hx
                  have M : ∀ n : ℕ, ∀ A B : Finset (Fin T), A.card = n → B.card = n →
                      ∃ f : Fin T → Fin T, Set.MapsTo f A B ∧ Set.InjOn f A ∧
                        ∑ a ∈ A, dist (x a) (x (f a)) ≤ D * ∑ y ∈ Afin,
                          |((A.filter (fun t => x t = y)).card : ℝ) - ((B.filter (fun t => x t = y)).card : ℝ)| := by
                    intro n
                    induction n with
                    | zero =>
                      intro A B hA hB
                      rw [card_eq_zero] at hA hB
                      subst hA; subst hB
                      refine ⟨id, by simp, by simp, ?_⟩
                      simp
                    | succ n ih =>
                      intro A B hA hB
                      have hcnt : ∀ (C : Finset (Fin T)) (c : Fin T), c ∈ C → ∀ y,
                          (((C.erase c).filter (fun t => x t = y)).card : ℝ) + (if x c = y then 1 else 0) =
                            ((C.filter (fun t => x t = y)).card : ℝ) := by
                        intro C c hc y
                        rw [filter_erase]
                        split_ifs with h
                        · exact_mod_cast card_erase_add_one (mem_filter.mpr ⟨hc, h⟩)
                        · rw [erase_eq_of_notMem (by simp [h])]; simp
                      obtain ⟨a, ha, b, hb, hcase⟩ : ∃ a ∈ A, ∃ b ∈ B,
                          (x a = x b ∨ ¬ ∃ a ∈ A, ∃ b ∈ B, x a = x b) := by
                        by_cases hp : ∃ a ∈ A, ∃ b ∈ B, x a = x b
                        · obtain ⟨a, ha, b, hb, h⟩ := hp; exact ⟨a, ha, b, hb, Or.inl h⟩
                        · obtain ⟨a, ha⟩ := card_pos.mp (by omega : 0 < A.card)
                          obtain ⟨b, hb⟩ := card_pos.mp (by omega : 0 < B.card)
                          exact ⟨a, ha, b, hb, Or.inr hp⟩
                      obtain ⟨f, hmap, hinj, hsum⟩ := ih (A.erase a) (B.erase b)
                        (by rw [card_erase_of_mem ha, hA]; rfl) (by rw [card_erase_of_mem hb, hB]; rfl)
                      refine ⟨Function.update f a b, ?_, ?_, ?_⟩
                      · intro a' ha'
                        by_cases h : a' = a
                        · subst h; simpa using hb
                        · rw [Function.update_of_ne h]
                          exact mem_of_mem_erase (hmap (mem_erase.mpr ⟨h, ha'⟩))
                      · intro a1 h1 a2 h2 heq
                        by_cases e1 : a1 = a <;> by_cases e2 : a2 = a
                        · rw [e1, e2]
                        · exfalso
                          rw [e1, Function.update_self, Function.update_of_ne e2] at heq
                          have := hmap (show a2 ∈ A.erase a from mem_erase.mpr ⟨e2, h2⟩)
                          exact (ne_of_mem_erase this) heq.symm
                        · exfalso
                          rw [e2, Function.update_self, Function.update_of_ne e1] at heq
                          have := hmap (show a1 ∈ A.erase a from mem_erase.mpr ⟨e1, h1⟩)
                          exact (ne_of_mem_erase this) heq
                        · rw [Function.update_of_ne e1, Function.update_of_ne e2] at heq
                          exact hinj (mem_erase.mpr ⟨e1, h1⟩) (mem_erase.mpr ⟨e2, h2⟩) heq
                      · rw [← add_sum_erase A _ ha, Function.update_self]
                        rw [sum_congr rfl (fun a' ha' => by rw [Function.update_of_ne (ne_of_mem_erase ha')])]
                        rcases hcase with hxe | hno
                        · have hterm : ∀ y ∈ Afin,
                              |((((A.erase a).filter (fun t => x t = y)).card : ℝ)) -
                                  (((B.erase b).filter (fun t => x t = y)).card : ℝ)| =
                              |((A.filter (fun t => x t = y)).card : ℝ) - ((B.filter (fun t => x t = y)).card : ℝ)| := by
                            intro y _
                            have e1 := hcnt A a ha y
                            have e2 := hcnt B b hb y
                            rw [← hxe] at e2
                            congr 1; linarith
                          rw [← sum_congr rfl hterm, hxe, dist_self, zero_add]
                          exact hsum
                        · have hterm : ∀ y ∈ Afin,
                              |((((A.erase a).filter (fun t => x t = y)).card : ℝ)) -
                                  (((B.erase b).filter (fun t => x t = y)).card : ℝ)| + (if x a = y then 1 else 0) ≤
                              |((A.filter (fun t => x t = y)).card : ℝ) - ((B.filter (fun t => x t = y)).card : ℝ)| := by
                            intro y _
                            have e1 := hcnt A a ha y
                            have e2 := hcnt B b hb y
                            have n1 : (0 : ℝ) ≤ (((A.erase a).filter (fun t => x t = y)).card : ℝ) := by positivity
                            have n2 : (0 : ℝ) ≤ (((B.erase b).filter (fun t => x t = y)).card : ℝ) := by positivity
                            by_cases h1 : x a = y <;> by_cases h2 : x b = y
                            · exact absurd ⟨a, ha, b, hb, h1.trans h2.symm⟩ hno
                            · have hB0 : ((B.filter (fun t => x t = y)).card : ℝ) = 0 := by
                                rw [Nat.cast_eq_zero, card_eq_zero, filter_eq_empty_iff]
                                intro b' hb' h; exact hno ⟨a, ha, b', hb', h1.trans h.symm⟩
                              rw [if_pos h1] at e1 ⊢; rw [if_neg h2] at e2
                              rw [hB0, ← e1]; rw [hB0] at e2
                              rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]; linarith
                            · have hA0 : ((A.filter (fun t => x t = y)).card : ℝ) = 0 := by
                                rw [Nat.cast_eq_zero, card_eq_zero, filter_eq_empty_iff]
                                intro a' ha' h; exact hno ⟨a', ha', b, hb, h.trans h2.symm⟩
                              rw [if_neg h1] at e1 ⊢; rw [if_pos h2] at e2
                              rw [hA0, ← e2]; rw [hA0] at e1
                              rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]; linarith
                            · rw [if_neg h1] at e1 ⊢; rw [if_neg h2] at e2
                              rw [← e1, ← e2]; simp
                          have hs := sum_le_sum hterm
                          rw [sum_add_distrib, sum_ite_eq, if_pos (hxA a)] at hs
                          have hd := hdist _ (hxA a) _ (hxA b)
                          nlinarith [mul_le_mul_of_nonneg_left hs hD0]
                  -- apply to V and its complement
                  set w : Fin T → Bool := fun t => decide (t ∉ V) with hw
                  have hA : ∀ t, t ∈ V ↔ w t = false := by intro t; simp [hw]
                  have hcV : Vᶜ.card = T / 2 := by
                    rw [card_compl, Fintype.card_fin, hV]; obtain ⟨r, rfl⟩ := hev; omega
                  obtain ⟨f, hmap, hinj, hsum⟩ := M (T / 2) V Vᶜ hV hcV
                  let g : {t // w t = false} → {t // w t = true} := fun a =>
                    ⟨f a.1, by
                      have := hmap ((hA a.1).mpr a.2)
                      simpa [hw] using this⟩
                  have ginj : Function.Injective g := fun a1 a2 h =>
                    Subtype.ext (hinj ((hA a1.1).mpr a1.2) ((hA a2.1).mpr a2.2) (congrArg Subtype.val h))
                  have hcard : Fintype.card {t // w t = false} = Fintype.card {t // w t = true} := by
                    rw [Fintype.card_subtype, Fintype.card_subtype]
                    have h1 : (univ.filter fun t => w t = false) = V := by ext t; simp [hw]
                    have h2 : (univ.filter fun t => w t = true) = Vᶜ := by ext t; simp [hw]
                    rw [h1, h2, hV, hcV]
                  let e := Equiv.ofBijective g ((Fintype.bijective_iff_injective_and_card g).mpr ⟨ginj, hcard⟩)
                  unfold PigeonholeDesign.Upper.discrepancy
                  refine (ciInf_le ⟨0, ?_⟩ e).trans ?_
                  · rintro _ ⟨e', rfl⟩; exact sum_nonneg (fun _ _ => dist_nonneg)
                  have hse : ∑ a : {t // w t = false}, dist (x a) (x (e a)) = ∑ t ∈ V, dist (x t) (x (f t)) :=
                    (Finset.sum_subtype V hA (fun t => dist (x t) (x (f t)))).symm
                  rw [hse]
                  refine hsum.trans (le_of_eq ?_)
                  congr 1
                  apply sum_congr rfl
                  intro y _
                  have hsplit := card_filter_add_card_filter_not (s := univ.filter (fun t => x t = y)) (fun t => t ∈ V)
                  have k1 : (univ.filter (fun t => x t = y)).filter (fun t => t ∈ V) = V.filter (fun t => x t = y) := by
                    ext t; simp [and_comm]
                  have k2 : (univ.filter (fun t => x t = y)).filter (fun t => t ∉ V) = Vᶜ.filter (fun t => x t = y) := by
                    ext t; simp [and_comm]
                  rw [k1, k2] at hsplit
                  have : ((Vᶜ.filter (fun t => x t = y)).card : ℝ) = ((univ.filter (fun t => x t = y)).card : ℝ) -
                      ((V.filter (fun t => x t = y)).card : ℝ) := by
                    rw [← hsplit]; push_cast; ring
                  rw [this]; congr 1; ring
              -- hypergeometric second moment: Var ≤ T/4 for the count of a fixed set in a random half
              have U2 : ∀ (T : ℕ), Even T → 4 ≤ T → ∀ P : Finset (Fin T),
                  ∑ V ∈ (Finset.univ : Finset (Fin T)).powersetCard (T / 2),
                    (2 * ((V.filter (fun t => t ∈ P)).card : ℝ) - (P.card : ℝ)) ^ 2 ≤
                    T * ((T.choose (T / 2) : ℕ) : ℝ) := by
                clear * -
                open Finset in
                focus
                  classical
                  intro T hev h4 P
                  have cnt : ∀ (k : ℕ) (R : Finset (Fin T)), R.card ≤ k →
                      (((univ : Finset (Fin T)).powersetCard k).filter (fun V => R ⊆ V)).card =
                        (T - R.card).choose (k - R.card) := by
                    intro k R hR
                    have e1 : (T - R.card).choose (k - R.card) = (powersetCard (k - R.card) (univ \ R)).card := by
                      rw [card_powersetCard, card_sdiff_of_subset (subset_univ _), card_univ, Fintype.card_fin]
                    rw [e1]
                    apply card_nbij' (fun V => V \ R) (fun W => W ∪ R)
                    · intro V hV
                      simp only [coe_filter, mem_powersetCard, subset_univ, true_and, Set.mem_setOf_eq] at hV
                      simp only [mem_coe, mem_powersetCard]
                      refine ⟨sdiff_subset_sdiff (subset_univ _) le_rfl, ?_⟩
                      rw [card_sdiff_of_subset hV.2, hV.1]
                    · intro W hW
                      simp only [mem_coe, mem_powersetCard] at hW
                      simp only [coe_filter, mem_powersetCard, subset_univ, true_and, Set.mem_setOf_eq]
                      have hd : Disjoint W R := by
                        rw [disjoint_left]; intro t ht htR; exact (mem_sdiff.1 (hW.1 ht)).2 htR
                      refine ⟨?_, subset_union_right⟩
                      rw [card_union_of_disjoint hd, hW.2]; omega
                    · intro V hV
                      simp only [coe_filter, mem_powersetCard, subset_univ, true_and, Set.mem_setOf_eq] at hV
                      exact sdiff_union_of_subset hV.2
                    · intro W hW
                      simp only [mem_coe, mem_powersetCard] at hW
                      have hd : Disjoint W R := by
                        rw [disjoint_left]; intro t ht htR; exact (mem_sdiff.1 (hW.1 ht)).2 htR
                      exact union_sdiff_cancel_right hd
                  obtain ⟨k, rfl⟩ := hev
                  obtain ⟨j, rfl⟩ : ∃ j, k = j + 2 := ⟨k - 2, by omega⟩
                  have hk : (j + 2 + (j + 2)) / 2 = j + 2 := by omega
                  rw [hk]
                  set Wd := (univ : Finset (Fin (j + 2 + (j + 2)))).powersetCard (j + 2) with hWd
                  set a : ℝ := (((2 * j + 3).choose (j + 1) : ℕ) : ℝ) with ha
                  set b : ℝ := (((2 * j + 2).choose j : ℕ) : ℝ) with hb
                  set N : ℝ := (((j + 2 + (j + 2)).choose (j + 2) : ℕ) : ℝ) with hN
                  have hNa : N = 2 * a := by
                    rw [hN, ha, show j + 2 + (j + 2) = (2 * j + 3) + 1 by ring, show j + 2 = (j + 1) + 1 by ring,
                      Nat.choose_succ_succ, Nat.choose_symm_of_eq_add (show 2 * j + 3 = (j + 1 + 1) + (j + 1) by ring)]
                    push_cast; ring
                  have hab : 2 * b ≤ a := by
                    have e : (2 * j + 3).choose (j + 1) = (2 * j + 2).choose j + (2 * j + 2).choose (j + 1) := by
                      rw [show 2 * j + 3 = (2 * j + 2) + 1 by ring, Nat.choose_succ_succ]
                    have m := Nat.choose_le_middle j (2 * j + 2)
                    rw [show (2 * j + 2) / 2 = j + 1 by omega] at m
                    rw [ha, hb, e]; push_cast
                    have : ((2 * j + 2).choose j : ℝ) ≤ ((2 * j + 2).choose (j + 1) : ℝ) := by exact_mod_cast m
                    linarith
                  have hcard1 : ∀ t : Fin (j + 2 + (j + 2)),
                      ∑ V ∈ Wd, (if t ∈ V then (1 : ℝ) else 0) = a := by
                    intro t
                    rw [sum_boole]
                    have := cnt (j + 2) {t} (by simp)
                    simp only [singleton_subset_iff, card_singleton] at this
                    rw [this, ha]; congr 2 <;> omega
                  have hcard2 : ∀ t t' : Fin (j + 2 + (j + 2)), t ≠ t' →
                      ∑ V ∈ Wd, (if t ∈ V then (1 : ℝ) else 0) * (if t' ∈ V then (1 : ℝ) else 0) = b := by
                    intro t t' htt
                    have e : ∀ V : Finset (Fin (j + 2 + (j + 2))), (if t ∈ V then (1 : ℝ) else 0) * (if t' ∈ V then (1 : ℝ) else 0)
                        = if ({t, t'} : Finset _) ⊆ V then 1 else 0 := by
                      intro V; by_cases h1 : t ∈ V <;> by_cases h2 : t' ∈ V <;> simp [h1, h2, insert_subset_iff]
                    rw [sum_congr rfl (fun V _ => e V), sum_boole]
                    have hc : ({t, t'} : Finset _).card = 2 := card_pair htt
                    have := cnt (j + 2) {t, t'} (by rw [hc]; omega)
                    rw [this, hc, hb]; congr 2 <;> omega
                  have hX : ∀ V : Finset (Fin (j + 2 + (j + 2))),
                      ((V.filter (fun t => t ∈ P)).card : ℝ) = ∑ t ∈ P, (if t ∈ V then (1 : ℝ) else 0) := by
                    intro V; rw [sum_boole]; congr 2; ext t; simp [and_comm]
                  set p : ℝ := (P.card : ℝ) with hp
                  have S1 : ∑ V ∈ Wd, ((V.filter (fun t => t ∈ P)).card : ℝ) = p * a := by
                    simp_rw [hX]; rw [sum_comm]; rw [sum_congr rfl (fun t _ => hcard1 t), sum_const, nsmul_eq_mul]
                  have S2 : ∑ V ∈ Wd, ((V.filter (fun t => t ∈ P)).card : ℝ) ^ 2 = p * (a + (p - 1) * b) := by
                    simp_rw [hX, sq, sum_mul_sum]
                    rw [sum_comm]
                    have inner : ∀ t ∈ P, ∑ V ∈ Wd, ∑ t' ∈ P, (if t ∈ V then (1 : ℝ) else 0) * (if t' ∈ V then (1 : ℝ) else 0)
                        = a + (p - 1) * b := by
                      intro t ht
                      rw [sum_comm, ← add_sum_erase P _ ht]
                      have e0 : ∑ V ∈ Wd, (if t ∈ V then (1 : ℝ) else 0) * (if t ∈ V then (1 : ℝ) else 0) = a := by
                        rw [← hcard1 t]; apply sum_congr rfl; intro V _; split_ifs <;> simp
                      rw [e0, sum_congr rfl (fun t' ht' => hcard2 t t' (ne_of_mem_erase ht').symm), sum_const,
                        nsmul_eq_mul]
                      have := card_erase_add_one ht
                      have : ((P.erase t).card : ℝ) = p - 1 := by rw [hp, ← this]; push_cast; ring
                      rw [this]
                    rw [sum_congr rfl inner, sum_const, nsmul_eq_mul]
                  have hWc : (Wd.card : ℝ) = N := by
                    rw [hWd, card_powersetCard, card_univ, Fintype.card_fin]
                  have expand : ∑ V ∈ Wd, (2 * ((V.filter (fun t => t ∈ P)).card : ℝ) - p) ^ 2 =
                      4 * ∑ V ∈ Wd, ((V.filter (fun t => t ∈ P)).card : ℝ) ^ 2
                        - 4 * p * ∑ V ∈ Wd, ((V.filter (fun t => t ∈ P)).card : ℝ) + p ^ 2 * Wd.card := by
                    rw [mul_sum, mul_sum, ← sum_sub_distrib]
                    rw [show (p ^ 2 * (Wd.card : ℝ)) = ∑ V ∈ Wd, p ^ 2 by rw [sum_const, nsmul_eq_mul]; ring,
                      ← sum_add_distrib]
                    apply sum_congr rfl; intro V _; ring
                  rw [expand, S1, S2, hWc]
                  have hpT : p ≤ ((j + 2 + (j + 2) : ℕ) : ℝ) := by
                    rw [hp]; exact_mod_cast (card_le_univ P).trans (by simp)
                  have hp0 : 0 ≤ p * (p - 1) := by
                    rcases Nat.eq_zero_or_pos P.card with h | h
                    · rw [hp, h]; simp
                    · have : (1 : ℝ) ≤ p := by rw [hp]; exact_mod_cast h
                      exact mul_nonneg (by linarith only [this]) (by linarith only [this])
                  have ha0 : 0 ≤ a := by rw [ha]; positivity
                  have hp00 : 0 ≤ p := by rw [hp]; positivity
                  rw [hNa]
                  have k1 : p * (p - 1) * (2 * b) ≤ p * (p - 1) * a := mul_le_mul_of_nonneg_left hab hp0
                  have k2 : p * a ≤ ((j + 2 + (j + 2) : ℕ) : ℝ) * a := mul_le_mul_of_nonneg_right hpT ha0
                  calc 4 * (p * (a + (p - 1) * b)) - 4 * p * (p * a) + p ^ 2 * (2 * a)
                      = 4 * p * a + 2 * (p * (p - 1) * (2 * b)) - 2 * p ^ 2 * a := by ring
                    _ ≤ 4 * p * a + 2 * (p * (p - 1) * a) - 2 * p ^ 2 * a := by linarith only [k1]
                    _ = 2 * (p * a) := by ring
                    _ ≤ 2 * (((j + 2 + (j + 2) : ℕ) : ℝ) * a) := by linarith only [k2]
                    _ = ((j + 2 + (j + 2) : ℕ) : ℝ) * (2 * a) := by ring
              refine ⟨D * K + 1, by positivity, 4, fun T hT4 hev x hx => ?_⟩
              set N : ℝ := ((T.choose (T / 2) : ℕ) : ℝ) with hN
              have hNpos : 0 < N := by rw [hN]; exact_mod_cast Nat.choose_pos (Nat.div_le_self _ _)
              set W := (Finset.univ : Finset (Fin T)).powersetCard (T / 2) with hW
              have hWc : (W.card : ℝ) = N := by rw [hW, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]
              -- each type
              have hy : ∀ y : MultiDim.Cov q 0,
                  ∑ V ∈ W, |(2 * ((V.filter (fun t => x t = y)).card : ℝ) -
                      ((Finset.univ.filter (fun t => x t = y)).card : ℝ))| ≤ N * Real.sqrt T := by
                intro y
                set P := Finset.univ.filter (fun t => x t = y)
                have h2 := U2 T hev hT4 P
                have hfilt : ∀ V : Finset (Fin T), V.filter (fun t => x t = y) = V.filter (fun t => t ∈ P) := by
                  intro V; ext t; simp [P]
                simp_rw [hfilt]
                set g : Finset (Fin T) → ℝ := fun V => |(2 * ((V.filter (fun t => t ∈ P)).card : ℝ) - (P.card : ℝ))|
                have cs := Finset.sum_mul_sq_le_sq_mul_sq W (fun _ => (1 : ℝ)) g
                simp only [one_mul, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one, g, sq_abs] at cs
                rw [hWc] at cs
                have hnn : 0 ≤ ∑ V ∈ W, g V := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
                have : (∑ V ∈ W, g V) ^ 2 ≤ (N * Real.sqrt T) ^ 2 := by
                  rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
                  calc _ ≤ N * _ := cs
                    _ ≤ N * (T * N) := mul_le_mul_of_nonneg_left h2 hNpos.le
                    _ = _ := by ring
                exact (pow_le_pow_iff_left₀ hnn (by positivity) two_ne_zero).mp this
              have hsum : ∑ V ∈ W, PigeonholeDesign.Upper.discrepancy x (fun t => decide (t ∉ V)) ≤
                  D * ∑ y ∈ Afin, N * Real.sqrt T := by
                calc ∑ V ∈ W, PigeonholeDesign.Upper.discrepancy x (fun t => decide (t ∉ V))
                    ≤ ∑ V ∈ W, D * ∑ y ∈ Afin, |(2 * ((V.filter (fun t => x t = y)).card : ℝ) -
                      ((Finset.univ.filter (fun t => x t = y)).card : ℝ))| := by
                      apply Finset.sum_le_sum
                      intro V hV
                      exact U1 T x hx hev V (Finset.mem_powersetCard.mp hV).2
                  _ = D * ∑ y ∈ Afin, ∑ V ∈ W, |(2 * ((V.filter (fun t => x t = y)).card : ℝ) -
                      ((Finset.univ.filter (fun t => x t = y)).card : ℝ))| := by
                      rw [← Finset.mul_sum, Finset.sum_comm]
                  _ ≤ _ := by
                      apply mul_le_mul_of_nonneg_left _ hD0
                      exact Finset.sum_le_sum (fun y _ => hy y)
              unfold PigeonholeDesign.Upper.crdExp
              rw [div_le_iff₀ hNpos]
              try rw [← hW]
              calc _ ≤ _ := hsum
                _ = D * Afin.card * (N * Real.sqrt T) := by rw [Finset.sum_const, nsmul_eq_mul]; ring
                _ ≤ D * K * (N * Real.sqrt T) := by
                    apply mul_le_mul_of_nonneg_right _ (by positivity)
                    exact mul_le_mul_of_nonneg_left (by exact_mod_cast hK) hD0
                _ ≤ (D * K + 1) * Real.sqrt T * N := by nlinarith [Real.sqrt_nonneg (T : ℝ)]
            have hper : ∀ (m : ℕ) (V : Finset (Fin (m + m))), V.card = m →
                dist u v * |(2 * ((V.filter (fun t : Fin (m + m) => (t : ℕ) < m)).card : ℝ) - m)| ≤
                PigeonholeDesign.Upper.discrepancy (fun t : Fin (m + m) => if (t : ℕ) < m then u else v)
                  (fun t => decide (t ∉ V)) := by
              intro m V hV
              set x : Fin (m + m) → MultiDim.Cov q 0 := fun t => if (t : ℕ) < m then u else v with hx
              set w : Fin (m + m) → Bool := fun t => decide (t ∉ V) with hw
              set P : Finset (Fin (m + m)) := Finset.univ.filter (fun t : Fin (m + m) => (t : ℕ) < m) with hP
              set k := (V.filter (fun t : Fin (m + m) => (t : ℕ) < m)).card with hk
              have hcP : P.card = m := by
                have : P = (Finset.univ : Finset (Fin m)).map (Fin.castAddEmb m) := by
                  ext t; simp only [hP, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map]
                  constructor
                  · intro h; exact ⟨⟨t, h⟩, by ext; simp⟩
                  · rintro ⟨s, -, rfl⟩; simp
                rw [this, Finset.card_map, Finset.card_univ, Fintype.card_fin]
              have hkm : k ≤ m := by
                have := Finset.card_le_card (Finset.filter_subset (fun t : Fin (m+m) => (t : ℕ) < m) V)
                omega
              have hF : Fintype.card {t // w t = false} = m := by
                rw [Fintype.card_subtype]; convert hV using 2; ext t; simp [hw]
              have hT : Fintype.card {t // w t = true} = m := by
                have h1 : Fintype.card {t // w t = true} = Fintype.card {t // ¬ w t = false} := by
                  apply Fintype.card_congr; exact Equiv.subtypeEquivRight (fun t => by simp)
                rw [h1, Fintype.card_subtype_compl, Fintype.card_fin, Fintype.card_subtype]
                have : (Finset.univ.filter (fun t => w t = false)) = V := by ext t; simp [hw]
                rw [this, hV]; omega
              -- counts
              have c1 : Fintype.card {a : {t // w t = false} // (a.1 : ℕ) < m} = k := by
                rw [Fintype.card_subtype, hk]
                refine Finset.card_bij (fun a _ => a.1) ?_ ?_ ?_
                · intro a ha; simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha
                  have := a.2; simp only [hw, decide_eq_false_iff_not, not_not] at this
                  simp [this, ha]
                · intro a _ b _ h; exact Subtype.ext h
                · intro t ht; simp only [Finset.mem_filter] at ht
                  exact ⟨⟨t, by simp [hw, ht.1]⟩, by simp [ht.2], rfl⟩
              have c2 : Fintype.card {a : {t // w t = true} // (a.1 : ℕ) < m} = m - k := by
                rw [Fintype.card_subtype]
                have : (Finset.univ.filter (fun a : {t // w t = true} => (a.1 : ℕ) < m)).card =
                    (P \ V.filter (fun t : Fin (m + m) => (t : ℕ) < m)).card := by
                  refine Finset.card_bij (fun a _ => a.1) ?_ ?_ ?_
                  · intro a ha; simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha
                    have := a.2; simp only [hw, decide_eq_true_eq] at this
                    simp [hP, this, ha]
                  · intro a _ b _ h; exact Subtype.ext h
                  · intro t ht
                    simp only [hP, Finset.mem_sdiff, Finset.mem_filter, Finset.mem_univ, true_and] at ht
                    refine ⟨⟨t, by simp only [hw, decide_eq_true_eq]; tauto⟩, by simp [ht.1], rfl⟩
                rw [this, Finset.card_sdiff_of_subset, hcP]
                intro t; simp only [hP, Finset.mem_filter, Finset.mem_univ, true_and]; exact fun h => h.2
              have c3 : Fintype.card {a : {t // w t = false} // ¬ (a.1 : ℕ) < m} = m - k := by
                rw [Fintype.card_subtype_compl, c1, hF]
              have c4 : Fintype.card {a : {t // w t = true} // ¬ (a.1 : ℕ) < m} = k := by
                rw [Fintype.card_subtype_compl, c2, hT]; omega
              have key : ∀ (r : Fin (m + m) → Prop) [DecidablePred r],
                  (∀ t t', r t → ¬ r t' → dist (x t) (x t') = dist u v) →
                  ∀ e : {t // w t = false} ≃ {t // w t = true},
                  dist u v * ((Fintype.card {a : {t // w t = false} // r a.1} : ℝ) -
                    Fintype.card {b : {t // w t = true} // r b.1}) ≤
                    ∑ a : {t // w t = false}, dist (x a) (x (e a)) := by
                intro r _ hr e
                set bad := (Finset.univ : Finset {t // w t = false}).filter (fun a => r a.1 ∧ ¬ r (e a).1)
                set good := (Finset.univ : Finset {t // w t = false}).filter (fun a => r a.1 ∧ r (e a).1)
                have h1 : Fintype.card {a : {t // w t = false} // r a.1} ≤ bad.card + good.card := by
                  rw [Fintype.card_subtype]
                  refine le_trans (Finset.card_le_card ?_) (Finset.card_union_le _ _)
                  intro a ha
                  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha
                  by_cases h : r (e a).1
                  · exact Finset.mem_union_right _ (by simp [good, ha, h])
                  · exact Finset.mem_union_left _ (by simp [bad, ha, h])
                have h2 : good.card ≤ Fintype.card {b : {t // w t = true} // r b.1} := by
                  rw [Fintype.card_subtype]
                  refine Finset.card_le_card_of_injOn e ?_ ?_
                  · intro a ha
                    simp only [good, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at ha
                    simp [ha.2]
                  · intro a _ b _ h; exact e.injective h
                have h3 : dist u v * (bad.card : ℝ) ≤ ∑ a : {t // w t = false}, dist (x a) (x (e a)) := by
                  calc dist u v * (bad.card : ℝ) = ∑ a ∈ bad, dist u v := by
                        rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
                    _ = ∑ a ∈ bad, dist (x a) (x (e a)) := by
                        refine Finset.sum_congr rfl (fun a ha => ?_)
                        simp only [bad, Finset.mem_filter, Finset.mem_univ, true_and] at ha
                        exact (hr _ _ ha.1 ha.2).symm
                    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
                          (fun _ _ _ => dist_nonneg)
                have h4 : ((Fintype.card {a : {t // w t = false} // r a.1} : ℝ) -
                    Fintype.card {b : {t // w t = true} // r b.1}) ≤ bad.card := by
                  have : (Fintype.card {a : {t // w t = false} // r a.1} : ℝ) ≤ bad.card + good.card := by
                    exact_mod_cast h1
                  have : (good.card : ℝ) ≤ Fintype.card {b : {t // w t = true} // r b.1} := by
                    exact_mod_cast h2
                  linarith only [this, ‹(Fintype.card {a : {t // w t = false} // r a.1} : ℝ) ≤ bad.card + good.card›]
                calc _ ≤ dist u v * (bad.card : ℝ) := mul_le_mul_of_nonneg_left h4 dist_nonneg
                  _ ≤ _ := h3
              have hne' : Nonempty ({t // w t = false} ≃ {t // w t = true}) :=
                Fintype.card_eq.mp (hF.trans hT.symm)
              refine le_ciInf (fun e => ?_)
              have k1 := key (fun t => (t : ℕ) < m) (by
                intro t t' h h'; simp only [hx, if_pos h, if_neg h']) e
              have k2 := key (fun t => ¬ (t : ℕ) < m) (by
                intro t t' h h'; simp only [not_not] at h'; simp only [hx, if_pos h', if_neg h]
                exact dist_comm _ _) e
              rw [c1, c2] at k1
              rw [c3, c4] at k2
              push_cast [hkm] at k1 k2
              rcases le_total 0 (2 * (k : ℝ) - m) with h | h
              · rw [abs_of_nonneg h]; linarith
              · rw [abs_of_nonpos h]; linarith
            have hcore : ∃ c : ℝ, 0 < c ∧ ∃ M : ℕ, ∀ m : ℕ, M ≤ m →
                c * Real.sqrt ((m + m : ℕ) : ℝ) * ((m + m).choose m : ℝ) ≤
                  ∑ V ∈ (Finset.univ : Finset (Fin (m + m))).powersetCard m,
                    |(2 * ((V.filter (fun t : Fin (m + m) => (t : ℕ) < m)).card : ℝ) - m)| := by
              clear * -
              open Finset in
              focus
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
                    linear_combination ((Nat.choose m K : ℝ) + Nat.choose m (K+1)) * e1 - ((Nat.choose m K : ℝ) + Nat.choose m (K+1)) * e2 - (Nat.choose (m+1) (K+1) : ℝ) * (2 * (K:ℝ) + 1 - m) * e3
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
                refine ⟨1/12, by norm_num, 1, ?_⟩
                intro n hn1
                set jf : Finset (Fin (n+n)) → ℕ := fun V => (V.filter (fun t => t.val < n)).card with hjf
                set P := (univ : Finset (Fin (n+n))).powersetCard n with hP
                set K := (n-1)/2 with hK
                have hKn : K + 1 ≤ n := by omega
                have hlow1 : (n : ℝ) * (Nat.choose (n-1) K : ℝ) ^ 2 ≤
                    ∑ V ∈ P, |2 * (jf V : ℝ) - n| := by
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
                show _ ≤ ∑ V ∈ P, |2 * (jf V : ℝ) - n|
                have hNc : (n+n).choose n = Nat.centralBinom n := by rw [Nat.centralBinom_eq_two_mul_choose, two_mul]
                rw [hNc]
                set N : ℝ := (Nat.centralBinom n : ℝ) with hN
                have hN0 : 0 ≤ N := Nat.cast_nonneg _
                set c2 : ℝ := (Nat.choose (n-1) K : ℝ) ^ 2 with hc2
                have hc2n : 0 ≤ c2 := sq_nonneg _
                have hb2 : N ^ 2 * (3 * n + 1) ≤ 16 ^ n := by
                  have := B2 n; rw [hN]; exact_mod_cast this
                have hb3 : (4:ℝ) ^ (n-1) ≤ c2 * (2 * n + 1) := by
                  have := B3 (n-1)
                  have e : ((n-1 : ℕ) : ℝ) = n - 1 := by rw [Nat.cast_sub hn1]; simp
                  rw [e] at this
                  rw [hc2, hK]
                  calc _ ≤ _ := this
                    _ = _ := by ring
                set u : ℝ := (4:ℝ) ^ (n-1) with hu
                have hu0 : 0 < u := pow_pos (by norm_num) _
                have h16 : (16:ℝ) ^ n = 16 * u ^ 2 := by
                  rw [hu, ← pow_mul, show (16:ℝ) = 4 ^ 2 by norm_num, ← pow_mul]
                  rw [show (4:ℝ)^2 = 16 by norm_num]
                  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n-1, by omega⟩
                  simp only [Nat.add_sub_cancel]
                  rw [show 2 * (m+1) = (m*2) + 2 by ring, pow_add]; norm_num; ring
                have hnr : (1:ℝ) ≤ n := by exact_mod_cast hn1
                have hu2 : u ^ 2 ≤ (c2 * (2 * n + 1)) ^ 2 := pow_le_pow_left₀ hu0.le hb3 2
                have h1 : N ^ 2 * (3 * n + 1) ≤ 16 * (c2 * (2 * n + 1)) ^ 2 := by
                  linarith only [hb2, h16, hu2]
                have hn0 : (0:ℝ) ≤ n := by linarith only [hnr]
                have k1 : (2 * (n:ℝ)) * (N ^ 2 * (3 * n + 1)) ≤ (2 * (n:ℝ)) * (16 * (c2 * (2 * n + 1)) ^ 2) :=
                  mul_le_mul_of_nonneg_left h1 (by linarith only [hn0])
                have k2 : 32 * (2 * (n:ℝ) + 1) ^ 2 ≤ 144 * n * (3 * n + 1) := by
                  nlinarith only [mul_le_mul hnr hnr zero_le_one hn0, hnr]
                have k3 : ((n:ℝ) * c2 ^ 2) * (32 * (2 * (n:ℝ) + 1) ^ 2) ≤ ((n:ℝ) * c2 ^ 2) * (144 * n * (3 * n + 1)) :=
                  mul_le_mul_of_nonneg_left k2 (mul_nonneg hn0 (sq_nonneg _))
                have k4 : (((n + n : ℕ) : ℝ) * N ^ 2) * (3 * n + 1) ≤ (12 * ((n:ℝ) * c2)) ^ 2 * (3 * n + 1) := by
                  push_cast
                  have e1 : ((n:ℝ) + n) * N ^ 2 * (3 * n + 1) = (2 * (n:ℝ)) * (N ^ 2 * (3 * n + 1)) := by ring
                  have e2 : (2 * (n:ℝ)) * (16 * (c2 * (2 * n + 1)) ^ 2) = ((n:ℝ) * c2 ^ 2) * (32 * (2 * (n:ℝ) + 1) ^ 2) := by ring
                  have e3 : ((n:ℝ) * c2 ^ 2) * (144 * n * (3 * n + 1)) = (12 * ((n:ℝ) * c2)) ^ 2 * (3 * n + 1) := by ring
                  rw [e1, ← e3]; rw [e2] at k1; exact k1.trans k3
                have k5 : ((n + n : ℕ) : ℝ) * N ^ 2 ≤ (12 * ((n:ℝ) * c2)) ^ 2 :=
                  le_of_mul_le_mul_right k4 (by linarith only [hn0])
                have hsqrt : Real.sqrt ((n+n : ℕ) : ℝ) * N ≤ 12 * ((n:ℝ) * c2) := by
                  have h0 : 0 ≤ 12 * ((n:ℝ) * c2) := mul_nonneg (by norm_num) (mul_nonneg hn0 hc2n)
                  rw [← Real.sqrt_sq hN0, ← Real.sqrt_mul (Nat.cast_nonneg _), ← Real.sqrt_sq h0]
                  exact Real.sqrt_le_sqrt k5
                rw [mul_assoc]
                linarith only [hsqrt, hlow1]
            have hlb : ∃ c : ℝ, 0 < c ∧ ∃ T₀ : ℕ, ∀ T : ℕ, T₀ ≤ T → Even T →
                c * Real.sqrt T ≤ PigeonholeDesign.Upper.crdExp
                  (fun t : Fin T => if (t : ℕ) < T / 2 then u else v) := by
              obtain ⟨c, hc, M, hM⟩ := hcore
              refine ⟨dist u v * c, mul_pos hduv hc, M + M, ?_⟩
              rintro T hT ⟨m, rfl⟩
              have hm2 : (m + m) / 2 = m := by omega
              have hMm : M ≤ m := by omega
              unfold PigeonholeDesign.Upper.crdExp
              rw [hm2]
              have hpos : (0 : ℝ) < ((m + m).choose m : ℝ) := by
                exact_mod_cast Nat.choose_pos (by omega)
              rw [le_div_iff₀ hpos]
              calc dist u v * c * Real.sqrt ((m + m : ℕ) : ℝ) * ((m + m).choose m : ℝ)
                  = dist u v * (c * Real.sqrt ((m + m : ℕ) : ℝ) * ((m + m).choose m : ℝ)) := by ring
                _ ≤ dist u v * ∑ V ∈ (Finset.univ : Finset (Fin (m + m))).powersetCard m,
                    |(2 * ((V.filter (fun t : Fin (m + m) => (t : ℕ) < m)).card : ℝ) - m)| :=
                    mul_le_mul_of_nonneg_left (hM m hMm) dist_nonneg
                _ = ∑ V ∈ (Finset.univ : Finset (Fin (m + m))).powersetCard m, dist u v *
                    |(2 * ((V.filter (fun t : Fin (m + m) => (t : ℕ) < m)).card : ℝ) - m)| := by
                    rw [Finset.mul_sum]
                _ ≤ _ := by
                    apply Finset.sum_le_sum
                    intro V hV
                    exact hper m V (Finset.mem_powersetCard.mp hV).2
            obtain ⟨C, hC, T₁, hT₁⟩ := hub
            obtain ⟨c, hc, T₂, hT₂⟩ := hlb
            refine ⟨c, C, hc, hC, max T₁ T₂, fun T hT hev => ⟨hT₁ T (le_of_max_le_left hT) hev, ?_⟩⟩
            refine ⟨fun t : Fin T => if (t : ℕ) < T / 2 then u else v, ⟨?_, ?_⟩,
              hT₂ T (le_of_max_le_right hT) hev⟩
            · intro t i
              dsimp only
              split_ifs
              · exact hu i
              · exact hv i
            · intro t j; exact j.elim0
