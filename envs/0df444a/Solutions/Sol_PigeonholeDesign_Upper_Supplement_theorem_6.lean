-- Prove2me | solution 1 for PigeonholeDesign.Upper.Supplement.theorem_6
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:36:00.55757+00:00
-- url     : https://prove2.me/submissions/98fb4cc2-bd9d-4b13-9bee-6f3f683144c0

import Mathlib
import Definitions.Def_PigeonholeDesign_MultiDim_Setting
import Definitions.Def_PigeonholeDesign_Upper_Supplement_MatchedPair

open PigeonholeDesign
open PigeonholeDesign.Upper
open PigeonholeDesign.Upper.Supplement

theorem solution (q : ℕ) (S : Fin q → Finset ℝ) (hS : ∀ i, (S i : Set ℝ) ⊆ Set.Icc 0 1)
    (hne : ∀ i, (S i).Nonempty) :
    (∃ C : ℝ, 0 < C ∧ ∃ T₀ : ℕ, ∀ T : ℕ, T₀ ≤ T → Even T →
      ∀ x : Fin T → MultiDim.Cov q 1, MultiDim.Admissible S x →
        PigeonholeDesign.Upper.phdExp
            (MultiDim.gridHole (q := q) (p := 1) ⌈(T : ℝ) ^ ((1 : ℝ) / 2)⌉₊) x
          ≤ C * ((T : ℝ) ^ ((1 : ℝ) / 4) * Real.sqrt (Real.log T))) ∧
    (∃ c : ℝ, 0 < c ∧ ∃ T₀ : ℕ, ∀ T : ℕ, T₀ ≤ T → Even T →
      ∀ (K : ℕ) (hole : MultiDim.Cov q 1 → Fin K),
        ∃ x : Fin T → MultiDim.Cov q 1, MultiDim.Admissible S x ∧
          c * (T : ℝ) ^ ((1 : ℝ) / 4) ≤ PigeonholeDesign.Upper.phdExp hole x) := by
            obtain ⟨sg, ht, hf⟩ : ∃ sg : Bool → ℝ, sg true = 1 ∧ sg false = -1 :=
              ⟨fun b => if b then 1 else -1, by simp, by simp⟩
            classical
            have absrep : ∀ (B a b : ℕ), a ≤ B → b ≤ B → |(a : ℝ) - b| = ∑ j ∈ Finset.range B,
                |(if a ≤ j then (1:ℝ) else 0) - (if b ≤ j then 1 else 0)| := by
              clear * -  sg
              as_aux_lemma =>
                have cnt : ∀ (B a : ℕ), a ≤ B → ∑ j ∈ Finset.range B, (if a ≤ j then (1:ℝ) else 0) = B - a := by
                  intro B a h
                  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]
                  have : (Finset.range B).filter (fun j => a ≤ j) = Finset.Ico a B := by
                    ext j; simp [and_comm]
                  rw [this, Nat.card_Ico, Nat.cast_sub h]
                have main : ∀ (B a b : ℕ), a ≤ B → b ≤ B → a ≤ b → |(a : ℝ) - b| = ∑ j ∈ Finset.range B,
                  |(if a ≤ j then (1:ℝ) else 0) - (if b ≤ j then 1 else 0)| := by
                  intro B a b ha hb hab
                  have : ∀ j ∈ Finset.range B, |(if a ≤ j then (1:ℝ) else 0) - (if b ≤ j then 1 else 0)|
                      = (if a ≤ j then (1:ℝ) else 0) - (if b ≤ j then 1 else 0) := by
                    intro j _
                    apply abs_of_nonneg
                    split_ifs <;> first | omega | norm_num
                  rw [Finset.sum_congr rfl this, Finset.sum_sub_distrib, cnt B a ha, cnt B b hb, abs_sub_comm, abs_of_nonneg]
                  · ring
                  · rw [sub_nonneg]; exact_mod_cast hab
                intro B a b ha hb
                rcases le_total a b with h | h
                · exact main B a b ha hb h
                · rw [abs_sub_comm, main B b a hb ha h]
                  exact Finset.sum_congr rfl fun j _ => abs_sub_comm _ _
            have sgsplit : ∀ (T : ℕ) (w : Fin T → Bool) (φ : Fin T → ℝ), ∑ t, φ t * sg (w t)
                = ∑ b : {t // w t = true}, φ b - ∑ a : {t // w t = false}, φ a := by
              clear * - ht hf sg
              as_aux_lemma =>
                intro T w φ
                rw [← Finset.sum_subtype (Finset.univ.filter (fun t => w t = true)) (by simp) φ,
                  ← Finset.sum_subtype (Finset.univ.filter (fun t => w t = false)) (by simp) φ,
                  Finset.sum_filter, Finset.sum_filter, ← Finset.sum_sub_distrib]
                refine Finset.sum_congr rfl fun t _ => ?_
                cases h : w t <;> simp [ht, hf]
            have matchLow : ∀ (T : ℕ) (y : Fin T → ℕ) (B : ℕ) (w : Fin T → Bool) (e : {t // w t = false} ≃ {t // w t = true}),
                (∀ t, y t ≤ B) → ∑ j ∈ Finset.range B, |∑ t, (if y t ≤ j then (1:ℝ) else 0) * sg (w t)|
                  ≤ ∑ a : {t // w t = false}, |(y a : ℝ) - y (e a)| := by
              clear * - absrep sgsplit sg
              as_aux_lemma =>
                intro T y B w e hy
                have h1 : ∀ a : {t // w t = false}, |(y a : ℝ) - y (e a)| = _ := fun a => absrep B (y a) (y (e a)) (hy _) (hy _)
                rw [Finset.sum_congr rfl fun a _ => h1 a, Finset.sum_comm]
                refine Finset.sum_le_sum fun j _ => ?_
                rw [sgsplit T w (fun t => if y t ≤ j then (1:ℝ) else 0), abs_sub_comm,
                  ← Equiv.sum_comp e, ← Finset.sum_sub_distrib]
                exact Finset.abs_sum_le_sum_abs _ _
            have matchUp : ∀ (T : ℕ) (y : Fin T → ℕ) (B : ℕ) (w : Fin T → Bool),
                Nonempty ({t // w t = false} ≃ {t // w t = true}) →
                (∀ t, y t ≤ B) → ∃ e : {t // w t = false} ≃ {t // w t = true}, 
                  ∑ a : {t // w t = false}, |(y a : ℝ) - y (e a)| ≤
                  ∑ j ∈ Finset.range B, |∑ t, (if y t ≤ j then (1:ℝ) else 0) * sg (w t)| := by
              clear * - absrep sgsplit sg
              as_aux_lemma =>
                intro T y B w hE hy
                have sorted : ∀ (α : Type) [Fintype α] (f : α → ℕ) (n : ℕ), Fintype.card α = n →
                    ∃ E : Fin n ≃ α, Monotone (fun i => f (E i)) := by
                  intro α _ f n hn
                  have e0 := Fintype.equivFinOfCardEq hn
                  exact ⟨(Tuple.sort (fun i => f (e0.symm i))).trans e0.symm, Tuple.monotone_sort (fun i => f (e0.symm i))⟩
                obtain ⟨e1⟩ := hE
                obtain ⟨EA, hA⟩ := sorted {t // w t = false} (fun a => y a) _ rfl
                obtain ⟨EB, hB⟩ := sorted {t // w t = true} (fun a => y a) (Fintype.card {t // w t = false})
                  (Fintype.card_congr e1).symm
                refine ⟨EA.symm.trans EB, ?_⟩
                rw [← Equiv.sum_comp EA]
                simp only [Equiv.trans_apply, Equiv.symm_apply_apply]
                rw [Finset.sum_congr rfl fun i _ => absrep B (y (EA i)) (y (EB i)) (hy _) (hy _), Finset.sum_comm]
                refine Finset.sum_le_sum fun j _ => ?_
                rw [sgsplit T w (fun t => if y t ≤ j then (1:ℝ) else 0), abs_sub_comm,
                  ← Equiv.sum_comp EA, ← Equiv.sum_comp EB, ← Finset.sum_sub_distrib]
                have hA' : ∀ i i', i ≤ i' → y (EA i) ≤ y (EA i') := fun i i' h => hA h
                have hB' : ∀ i i', i ≤ i' → y (EB i) ≤ y (EB i') := fun i i' h => hB h
                by_cases hc : ∀ i, y (EB i) ≤ j → y (EA i) ≤ j
                · refine (le_of_eq ?_).trans (le_abs_self _)
                  refine Finset.sum_congr rfl fun i _ => abs_of_nonneg ?_
                  have := hc i
                  split_ifs <;> first | omega | norm_num
                · push Not at hc
                  obtain ⟨i0, h1, h2⟩ := hc
                  refine (le_of_eq ?_).trans (neg_le_abs _)
                  rw [← Finset.sum_neg_distrib]
                  refine Finset.sum_congr rfl fun i _ => abs_of_nonpos ?_
                  rcases le_total i i0 with h | h
                  · have := hB' _ _ h
                    rw [if_pos (by omega : y (EB i) ≤ j)]
                    split_ifs <;> norm_num
                  · have := hA' _ _ h
                    rw [if_neg (by omega : ¬ y (EA i) ≤ j)]
                    split_ifs <;> norm_num
            have khin : ∀ (T : ℕ) (A : Finset ℕ) , (∀ a ∈ A, a < T) →
                2 ^ T * (1/4 * Real.sqrt (A.card)) ≤ ∑ coin : Fin T → Bool, |∑ a ∈ A, sg (PigeonholeDesign.Upper.coinOf coin a)| := by
              clear * - ht hf sg
              as_aux_lemma =>
                intro T A hA
                have hsq : ∀ b, sg b ^ 2 = 1 := by intro b; cases b <;> simp [ht, hf]
                have hcard : ∑ coin : Fin T → Bool, (1:ℝ) = 2 ^ T := by simp
                -- flip
                have flip : ∀ (s : ℕ) (B : Finset ℕ) (g : ℝ → ℝ), s < T → s ∉ B →
                    ∑ coin : Fin T → Bool, sg (PigeonholeDesign.Upper.coinOf coin s) * g (∑ a ∈ B, sg (PigeonholeDesign.Upper.coinOf coin a)) = 0 := by
                  intro s B g hs hB
                  obtain ⟨fl, hfl⟩ : ∃ fl : (Fin T → Bool) → (Fin T → Bool), fl = fun coin => Function.update coin ⟨s, hs⟩ (!coin ⟨s, hs⟩) := ⟨_, rfl⟩
                  have hinv : Function.Involutive fl := by
                    intro coin
                    rw [hfl]; simp
                  have h1 : ∀ coin, sg (PigeonholeDesign.Upper.coinOf (fl coin) s) = - sg (PigeonholeDesign.Upper.coinOf coin s) := by
                    intro coin
                    rw [hfl]
                    simp only [PigeonholeDesign.Upper.coinOf, dif_pos hs, Function.update_self]
                    cases coin ⟨s, hs⟩ <;> simp [ht, hf]
                  have h2 : ∀ coin, ∑ a ∈ B, sg (PigeonholeDesign.Upper.coinOf (fl coin) a) = ∑ a ∈ B, sg (PigeonholeDesign.Upper.coinOf coin a) := by
                    intro coin
                    refine Finset.sum_congr rfl fun a ha => ?_
                    have has : a ≠ s := by rintro rfl; exact hB ha
                    rw [hfl]
                    simp only [PigeonholeDesign.Upper.coinOf]
                    split_ifs with h
                    · rw [Function.update_of_ne]
                      intro hh; exact has (congrArg Fin.val hh)
                    · rfl
                  have h3 := Equiv.sum_comp hinv.toPerm (fun coin => sg (PigeonholeDesign.Upper.coinOf coin s) * g (∑ a ∈ B, sg (PigeonholeDesign.Upper.coinOf coin a)))
                  simp only [Function.Involutive.coe_toPerm, h1, h2, neg_mul, Finset.sum_neg_distrib] at h3
                  linarith
                have mom : ∀ A : Finset ℕ, (∀ a ∈ A, a < T) →
                    (∑ coin : Fin T → Bool, (∑ a ∈ A, sg (PigeonholeDesign.Upper.coinOf coin a)) ^ 2 = 2 ^ T * A.card) ∧
                    (∑ coin : Fin T → Bool, (∑ a ∈ A, sg (PigeonholeDesign.Upper.coinOf coin a)) ^ 4 ≤ 2 ^ T * (3 * (A.card : ℝ) ^ 2)) := by
                  intro A
                  induction A using Finset.induction_on with
                  | empty => intro _; simp
                  | insert s B hs ih =>
                    intro hA
                    obtain ⟨i1, i2⟩ := ih (fun a ha => hA a (Finset.mem_insert_of_mem ha))
                    have hsT := hA s (Finset.mem_insert_self _ _)
                    have f1 := flip s B (fun z => z) hsT hs
                    have f3 := flip s B (fun z => z ^ 3) hsT hs
                    simp only [Finset.sum_insert hs, Finset.card_insert_of_notMem hs]
                    have e2 : ∀ coin : Fin T → Bool, (sg (PigeonholeDesign.Upper.coinOf coin s) + ∑ a ∈ B, sg (PigeonholeDesign.Upper.coinOf coin a)) ^ 2
                        = 1 + 2 * (sg (PigeonholeDesign.Upper.coinOf coin s) * (∑ a ∈ B, sg (PigeonholeDesign.Upper.coinOf coin a))) + (∑ a ∈ B, sg (PigeonholeDesign.Upper.coinOf coin a)) ^ 2 := by
                      intro coin
                      have := hsq (PigeonholeDesign.Upper.coinOf coin s)
                      linear_combination this
                    have e4 : ∀ coin : Fin T → Bool, (sg (PigeonholeDesign.Upper.coinOf coin s) + ∑ a ∈ B, sg (PigeonholeDesign.Upper.coinOf coin a)) ^ 4
                        = 1 + 4 * (sg (PigeonholeDesign.Upper.coinOf coin s) * (∑ a ∈ B, sg (PigeonholeDesign.Upper.coinOf coin a))) + 6 * (∑ a ∈ B, sg (PigeonholeDesign.Upper.coinOf coin a)) ^ 2
                        + 4 * (sg (PigeonholeDesign.Upper.coinOf coin s) * (∑ a ∈ B, sg (PigeonholeDesign.Upper.coinOf coin a)) ^ 3) + (∑ a ∈ B, sg (PigeonholeDesign.Upper.coinOf coin a)) ^ 4 := by
                      intro coin
                      have := hsq (PigeonholeDesign.Upper.coinOf coin s)
                      generalize sg (PigeonholeDesign.Upper.coinOf coin s) = z at *
                      generalize ∑ a ∈ B, sg (PigeonholeDesign.Upper.coinOf coin a) = S at *
                      linear_combination (z ^ 2 + 1 + 4 * z * S + 6 * S ^ 2) * this
                    constructor
                    · simp only [e2, Finset.sum_add_distrib, ← Finset.mul_sum, f1, i1, hcard]
                      push_cast; ring
                    · simp only [e4, Finset.sum_add_distrib, ← Finset.mul_sum, f1, f3, i1, hcard]
                      push_cast
                      have : (0:ℝ) < 2 ^ T := by positivity
                      linarith
                obtain ⟨m2, m4⟩ := mom A hA
                rcases Nat.eq_zero_or_pos A.card with h0 | hpos
                · rw [h0]; simp
                  exact Finset.sum_nonneg fun _ _ => abs_nonneg _
                have hn : (0:ℝ) < A.card := by exact_mod_cast hpos
                obtain ⟨r, hr⟩ : ∃ r, r = Real.sqrt A.card := ⟨_, rfl⟩
                have hrpos : 0 < r := by rw [hr]; exact Real.sqrt_pos.2 hn
                have hr2 : (A.card : ℝ) = r ^ 2 := by rw [hr, Real.sq_sqrt hn.le]
                rw [← hr]
                -- pointwise: |y| ≥ a (y²/a² - y⁴/(4a⁴)) with a = 2 r
                have hpt : ∀ y : ℝ, y ^ 2 * (1 / (2 * r)) - y ^ 4 * (1 / (32 * r ^ 3)) ≤ |y| := by
                  intro y
                  have h1 : ∀ u : ℝ, 0 ≤ u → u ^ 2 - u ^ 4 / 4 ≤ u := by
                    intro u hu
                    have : 0 ≤ u * (1 - u + u ^ 3 / 4) := by
                      apply mul_nonneg hu
                      have := mul_nonneg (sq_nonneg (u - 6/5)) (by linarith : 0 ≤ u + 12/5)
                      linarith
                    linarith
                  have h2 := h1 (|y| / (2 * r)) (by positivity)
                  have h3 : |y| ^ 2 = y ^ 2 := sq_abs y
                  have h4 : |y| ^ 4 = y ^ 4 := by
                    rw [show |y| ^ 4 = (|y| ^ 2) ^ 2 by ring, h3]; ring
                  have h5 := mul_le_mul_of_nonneg_left h2 (by positivity : 0 ≤ 2 * r)
                  rw [div_pow, div_pow, h3, h4] at h5
                  have e1 : 2 * r * (y ^ 2 / (2 * r) ^ 2 - y ^ 4 / (2 * r) ^ 4 / 4) = y ^ 2 * (1 / (2 * r)) - y ^ 4 * (1 / (32 * r ^ 3)) := by
                    field_simp; ring
                  have e2 : 2 * r * (|y| / (2 * r)) = |y| := by field_simp
                  rw [e1, e2] at h5
                  exact h5
                refine le_trans ?_ (Finset.sum_le_sum fun coin _ => hpt _)
                rw [Finset.sum_sub_distrib, ← Finset.sum_mul, ← Finset.sum_mul, m2]
                have h6 := mul_le_mul_of_nonneg_right m4 (by positivity : 0 ≤ 1 / (32 * r ^ 3))
                rw [hr2] at h6 ⊢
                have e1 : (2:ℝ) ^ T * r ^ 2 * (1 / (2 * r)) = 2 ^ T * r * (1/2) := by field_simp
                have e2 : (2:ℝ) ^ T * (3 * (r ^ 2) ^ 2) * (1 / (32 * r ^ 3)) = 2 ^ T * r * (3/32) := by field_simp
                rw [e2] at h6
                rw [e1]
                have : 0 < (2:ℝ) ^ T * r := by positivity
                linarith
            have struct : ∀ (ι : Type) [DecidableEq ι] (T : ℕ) (cell : ℕ → ι) (coin : ℕ → Bool),
                ∃ v : ℕ → Bool, (∀ n, PigeonholeDesign.Upper.prefixAssign T cell coin n
                    = (List.range n).map v) ∧
                  ∀ n, (((Finset.range n).filter (fun t => v t = false)).card = T / 2 → v n = true) ∧
                    (((Finset.range n).filter (fun t => v t = false)).card ≠ T / 2 →
                      ((Finset.range n).filter (fun t => v t = true)).card = T / 2 → v n = false) ∧
                    (((Finset.range n).filter (fun t => v t = false)).card ≠ T / 2 →
                      ((Finset.range n).filter (fun t => v t = true)).card ≠ T / 2 →
                      ((∑ t ∈ Finset.range n, (if cell t = cell n then sg (v t) else 0) = 0 → v n = coin n) ∧
                       (0 < ∑ t ∈ Finset.range n, (if cell t = cell n then sg (v t) else 0) → v n = false) ∧
                       (∑ t ∈ Finset.range n, (if cell t = cell n then sg (v t) else 0) < 0 → v n = true))) := by
              clear * - ht hf sg
              as_aux_lemma =>
                intro ι _ T cell coin
                have hlen : ∀ n, (PigeonholeDesign.Upper.prefixAssign T cell coin n).length = n := by
                  intro n
                  induction n with
                  | zero => simp [PigeonholeDesign.Upper.prefixAssign]
                  | succ n ih => simp [PigeonholeDesign.Upper.prefixAssign, ih]
                obtain ⟨v, hv⟩ : ∃ v : ℕ → Bool, v = fun t =>
                  (PigeonholeDesign.Upper.prefixAssign T cell coin (t+1)).getD t false := ⟨_, rfl⟩
                have hmap : ∀ n, PigeonholeDesign.Upper.prefixAssign T cell coin n
                      = (List.range n).map v := by
                  intro n
                  induction n with
                  | zero => simp [PigeonholeDesign.Upper.prefixAssign]
                  | succ n ih =>
                    rw [List.range_succ, List.map_append, ← ih]
                    have h1 : v n = (PigeonholeDesign.Upper.prefixAssign T cell coin (n+1)).getD n false := by
                      rw [hv]
                    simp only [PigeonholeDesign.Upper.prefixAssign] at h1 ⊢
                    rw [List.getD_append_right _ _ _ _ (by rw [hlen])] at h1
                    simp only [hlen, Nat.sub_self, List.getD_cons_zero] at h1
                    simp only [List.map_cons, List.map_nil, h1]
                have hcnt : ∀ n (b : Bool), ((List.range n).map v).count b
                    = ((Finset.range n).filter (fun t => v t = b)).card := by
                  intro n b
                  induction n with
                  | zero => simp
                  | succ n ih =>
                    rw [List.range_succ, List.map_append, List.count_append, ih, Finset.range_add_one,
                      Finset.filter_insert]
                    by_cases h : v n = b <;> simp [h]
                have hcnt2 : ∀ n (c : ι) (b : Bool), ((List.range n).zip ((List.range n).map v)).countP
                      (fun sb => cell sb.1 = c ∧ sb.2 = b)
                    = ((Finset.range n).filter (fun t => cell t = c ∧ v t = b)).card := by
                  intro n c b
                  induction n with
                  | zero => simp
                  | succ n ih =>
                    rw [List.range_succ, List.map_append, List.zip_append (by simp), List.countP_append, ih,
                      Finset.range_add_one, Finset.filter_insert]
                    by_cases h : cell n = c ∧ v n = b <;> simp [h]
                have himb : ∀ n (c : ι), ∑ t ∈ Finset.range n, (if cell t = c then sg (v t) else 0)
                    = (((Finset.range n).filter (fun t => cell t = c ∧ v t = true)).card : ℝ)
                      - ((Finset.range n).filter (fun t => cell t = c ∧ v t = false)).card := by
                  intro n c
                  rw [Finset.card_filter, Finset.card_filter]
                  push_cast
                  rw [← Finset.sum_sub_distrib]
                  refine Finset.sum_congr rfl fun t _ => ?_
                  by_cases h : cell t = c <;> cases h2 : v t <;> simp [h, ht, hf]
                refine ⟨v, hmap, fun n => ?_⟩
                have h1 : v n = (PigeonholeDesign.Upper.prefixAssign T cell coin (n+1)).getD n false := by
                    rw [hv]
                simp only [PigeonholeDesign.Upper.prefixAssign] at h1
                rw [List.getD_append_right _ _ _ _ (by rw [hlen])] at h1
                simp only [hlen, Nat.sub_self, List.getD_cons_zero] at h1
                simp only [hmap, hcnt, hcnt2] at h1
                rw [himb]
                refine ⟨fun h => by rw [h1, if_pos h], fun h h' => by rw [h1, if_neg h, if_pos h'],
                  fun h h' => ?_⟩
                rw [if_neg h, if_neg h'] at h1
                refine ⟨fun h2 => ?_, fun h2 => ?_, fun h2 => ?_⟩
                · rw [sub_eq_zero, Nat.cast_inj] at h2
                  rw [h1, if_neg (by omega), if_neg (by omega)]
                · rw [sub_pos, Nat.cast_lt] at h2
                  rw [h1, if_pos h2]
                · rw [sub_neg, Nat.cast_lt] at h2
                  rw [h1, if_neg (by omega), if_pos h2]
            have compare : ∀ (ι : Type) [DecidableEq ι] (T : ℕ) (cell : ℕ → ι) (coin w u : ℕ → Bool), Even T →
                (∀ n, (((Finset.range n).filter (fun t => w t = false)).card = T / 2 → w n = true) ∧
                    (((Finset.range n).filter (fun t => w t = false)).card ≠ T / 2 →
                      ((Finset.range n).filter (fun t => w t = true)).card = T / 2 → w n = false) ∧
                    (((Finset.range n).filter (fun t => w t = false)).card ≠ T / 2 →
                      ((Finset.range n).filter (fun t => w t = true)).card ≠ T / 2 →
                      ((∑ t ∈ Finset.range n, (if cell t = cell n then sg (w t) else 0) = 0 → w n = coin n) ∧
                       (0 < ∑ t ∈ Finset.range n, (if cell t = cell n then sg (w t) else 0) → w n = false) ∧
                       (∑ t ∈ Finset.range n, (if cell t = cell n then sg (w t) else 0) < 0 → w n = true)))) →
                (∀ n < T, 
                      ((∑ t ∈ Finset.range n, (if cell t = cell n then sg (u t) else 0) = 0 → u n = coin n) ∧
                       (0 < ∑ t ∈ Finset.range n, (if cell t = cell n then sg (u t) else 0) → u n = false) ∧
                       (∑ t ∈ Finset.range n, (if cell t = cell n then sg (u t) else 0) < 0 → u n = true))) →
                ((Finset.range T).filter (fun t => w t = false)).card = T / 2 ∧
                ((Finset.range T).filter (fun t => w t = true)).card = T / 2 ∧
                ∃ τ ≤ T, T / 2 ≤ τ ∧ (∀ t < τ, w t = u t) ∧ ∃ b, ∀ t, τ ≤ t → t < T → w t = b := by
              clear * -  sg
              as_aux_lemma =>
                intro ι _ T cell coin w u hT hw hu
                obtain ⟨m, hm⟩ := hT
                have hm2 : T / 2 = m := by omega
                rw [hm2] at hw ⊢
                obtain ⟨a, ha⟩ : ∃ a : ℕ → ℕ, ∀ n, a n = ((Finset.range n).filter (fun t => w t = false)).card :=
                  ⟨_, fun _ => rfl⟩
                obtain ⟨b, hb⟩ : ∃ b : ℕ → ℕ, ∀ n, b n = ((Finset.range n).filter (fun t => w t = true)).card :=
                  ⟨_, fun _ => rfl⟩
                simp only [← ha, ← hb] at hw ⊢
                have ha1 : ∀ n, a (n+1) = a n + if w n = false then 1 else 0 := by
                  intro n
                  rw [ha, ha, Finset.range_add_one, Finset.filter_insert]
                  by_cases h : w n = false <;> simp [h]
                have hb1 : ∀ n, b (n+1) = b n + if w n = true then 1 else 0 := by
                  intro n
                  rw [hb, hb, Finset.range_add_one, Finset.filter_insert]
                  by_cases h : w n = true <;> simp [h]
                have hab : ∀ n, a n + b n = n := by
                  intro n
                  induction n with
                  | zero => simp [ha, hb]
                  | succ n ih =>
                    rw [ha1, hb1]
                    cases h : w n <;> simp <;> omega
                have hinv : ∀ n ≤ T, a n ≤ m ∧ b n ≤ m ∧ ∃ τ ≤ n, (∀ t < τ, w t = u t) ∧
                    (τ = n ∨ m ≤ τ ∧ ((a n = m ∧ ∀ t, τ ≤ t → t < n → w t = true) ∨
                      (b n = m ∧ ∀ t, τ ≤ t → t < n → w t = false))) := by
                  intro n
                  induction n with
                  | zero =>
                    intro _
                    exact ⟨by simp [ha], by simp [hb], 0, le_rfl, by simp, Or.inl rfl⟩
                  | succ n ih =>
                    intro hn
                    obtain ⟨i1, i2, τ, hτ, h3, h4⟩ := ih (by omega)
                    obtain ⟨w1, w2, w3⟩ := hw n
                    have e := hab n
                    have e1 := ha1 n
                    have e2 := hb1 n
                    by_cases c1 : a n = m
                    · have hwn := w1 c1
                      simp [hwn] at e1 e2
                      refine ⟨by omega, by omega, ?_⟩
                      rcases h4 with h4 | ⟨h5, h4 | h4⟩
                      · refine ⟨n, by omega, fun t ht => h3 t (by omega), Or.inr ⟨by omega, Or.inl ⟨by omega, fun t h1 h2 => ?_⟩⟩⟩
                        obtain rfl : t = n := by omega
                        exact hwn
                      · refine ⟨τ, by omega, h3, Or.inr ⟨h5, Or.inl ⟨by omega, fun t h1 h2 => ?_⟩⟩⟩
                        rcases Nat.lt_succ_iff_lt_or_eq.1 h2 with h | h
                        · exact h4.2 t h1 h
                        · rw [h]; exact hwn
                      · omega
                    · by_cases c2 : b n = m
                      · have hwn := w2 c1 c2
                        simp [hwn] at e1 e2
                        refine ⟨by omega, by omega, ?_⟩
                        rcases h4 with h4 | ⟨h5, h4 | h4⟩
                        · refine ⟨n, by omega, fun t ht => h3 t (by omega), Or.inr ⟨by omega, Or.inr ⟨by omega, fun t h1 h2 => ?_⟩⟩⟩
                          obtain rfl : t = n := by omega
                          exact hwn
                        · omega
                        · refine ⟨τ, by omega, h3, Or.inr ⟨h5, Or.inr ⟨by omega, fun t h1 h2 => ?_⟩⟩⟩
                          rcases Nat.lt_succ_iff_lt_or_eq.1 h2 with h | h
                          · exact h4.2 t h1 h
                          · rw [h]; exact hwn
                      · refine ⟨by split_ifs at e1 <;> omega, by split_ifs at e2 <;> omega, n + 1, le_rfl, ?_, Or.inl rfl⟩
                        obtain rfl : τ = n := by
                          rcases h4 with h | ⟨-, h | h⟩
                          · exact h
                          · exact absurd h.1 c1
                          · exact absurd h.1 c2
                        intro t ht'
                        rcases Nat.lt_succ_iff_lt_or_eq.1 ht' with h | h
                        · exact h3 t h
                        · rw [h]
                          obtain ⟨r1, r2, r3⟩ := w3 c1 c2
                          obtain ⟨s1, s2, s3⟩ := hu τ (by omega)
                          have hs : ∑ t ∈ Finset.range τ, (if cell t = cell τ then sg (w t) else 0)
                              = ∑ t ∈ Finset.range τ, (if cell t = cell τ then sg (u t) else 0) := by
                            refine Finset.sum_congr rfl fun t ht => ?_
                            rw [h3 t (Finset.mem_range.1 ht)]
                          rw [hs] at r1 r2 r3
                          rcases lt_trichotomy (∑ t ∈ Finset.range τ, (if cell t = cell τ then sg (u t) else 0)) 0 with h | h | h
                          · rw [r3 h, s3 h]
                          · rw [r1 h, s1 h]
                          · rw [r2 h, s2 h]
                obtain ⟨f1, f2, τ, hτ, f3, f4⟩ := hinv T le_rfl
                have f5 := hab T
                refine ⟨by omega, by omega, τ, hτ, ?_, f3, ?_⟩
                · rcases f4 with h | h
                  · omega
                  · exact h.1
                · rcases f4 with h | ⟨-, h | h⟩
                  · exact ⟨true, fun t h1 h2 => by omega⟩
                  · exact ⟨true, h.2⟩
                  · exact ⟨false, h.2⟩
            have rad : ∀ (ι : Type) [DecidableEq ι] (M : ℕ) (cell : ℕ → ι) (u : (ℕ → Bool) → ℕ → Bool)
                (f : ℕ → ℝ) (κ : ι), (∀ t, f t = 0 ∨ f t = 1) →
                (∀ s t, cell s = cell t → cell s ≠ κ → f s = f t) →
                (∀ coin, ∀ n < M, 
                      ((∑ t ∈ Finset.range n, (if cell t = cell n then sg (u coin t) else 0) = 0 → u coin n = coin n) ∧
                       (0 < ∑ t ∈ Finset.range n, (if cell t = cell n then sg (u coin t) else 0) → u coin n = false) ∧
                       (∑ t ∈ Finset.range n, (if cell t = cell n then sg (u coin t) else 0) < 0 → u coin n = true))) →
                ∀ n ≤ M, ∃ c : ℕ → ℝ, (∀ a, |c a| ≤ 1) ∧
                  (∀ coin, ∑ t ∈ Finset.range n, f t * sg (u coin t) = ∑ a ∈ Finset.range n, c a * sg (coin a)) ∧
                  (∀ a b, a < n → b < n → c a ≠ 0 → c b ≠ 0 → cell a ≠ κ → cell a = cell b → a = b) := by
              clear * - ht hf sg
              as_aux_lemma =>
                intro ι _ M cell u f κ hf01 hfc hu
                have key : ∀ n ≤ M, ∃ c : ℕ → ℝ, (∀ a, |c a| ≤ 1) ∧
                    (∀ coin, ∑ t ∈ Finset.range n, f t * sg (u coin t) = ∑ a ∈ Finset.range n, c a * sg (coin a)) ∧
                    (∀ k, ((∀ coin, ∑ t ∈ Finset.range n, (if cell t = k then sg (u coin t) else 0) = 0) ∧
                        (k ≠ κ → ∀ a < n, cell a = k → c a = 0)) ∨
                      (∃ o < n, cell o = k ∧ c o = f o ∧ 
                        (∀ coin, ∑ t ∈ Finset.range n, (if cell t = k then sg (u coin t) else 0) = sg (coin o)) ∧
                        (k ≠ κ → ∀ a < n, cell a = k → a ≠ o → c a = 0))) := by
                  intro n
                  induction n with
                  | zero =>
                    intro _
                    exact ⟨fun _ => 0, by simp, by simp, fun k => Or.inl (by simp)⟩
                  | succ n ih =>
                    intro hn
                    obtain ⟨c, h1, h2, h3⟩ := ih (by omega)
                    rcases h3 (cell n) with ⟨h4, h5⟩ | ⟨o, ho, hok, hco, h4, h5⟩
                    · have hun : ∀ coin, u coin n = coin n := fun coin => (hu coin n (by omega)).1 (h4 coin)
                      refine ⟨Function.update c n (f n), ?_, ?_, ?_⟩
                      · intro a
                        by_cases ha : a = n
                        · subst ha; rw [Function.update_self]
                          rcases hf01 a with h | h <;> rw [h] <;> simp
                        · rw [Function.update_of_ne ha]; exact h1 a
                      · intro coin
                        rw [Finset.sum_range_succ, Finset.sum_range_succ, h2, hun, Function.update_self]
                        congr 1
                        refine Finset.sum_congr rfl fun a ha => ?_
                        rw [Function.update_of_ne (by have := Finset.mem_range.1 ha; omega)]
                      · intro k
                        by_cases hk : cell n = k
                        · right
                          refine ⟨n, by omega, hk, Function.update_self .., fun coin => ?_, fun hκ a ha hak han => ?_⟩
                          · rw [Finset.sum_range_succ, if_pos hk, hun, ← hk, h4, zero_add]
                          · rw [Function.update_of_ne han]
                            exact h5 (by rw [hk]; exact hκ) a (by omega) (by rw [hk]; exact hak)
                        · rcases h3 k with ⟨h6, h7⟩ | ⟨o, ho, hok, hco, h6, h7⟩
                          · left
                            refine ⟨fun coin => ?_, fun hκ a ha hak => ?_⟩
                            · rw [Finset.sum_range_succ, if_neg hk, h6, zero_add]
                            · have han : a ≠ n := by rintro rfl; exact hk hak
                              rw [Function.update_of_ne han]
                              exact h7 hκ a (by omega) hak
                          · right
                            refine ⟨o, by omega, hok, ?_, fun coin => ?_, fun hκ a ha hak hao => ?_⟩
                            · rw [Function.update_of_ne (by omega)]; exact hco
                            · rw [Finset.sum_range_succ, if_neg hk, h6, add_zero]
                            · have han : a ≠ n := by rintro rfl; exact hk hak
                              rw [Function.update_of_ne han]
                              exact h7 hκ a (by omega) hak hao
                    · have hun : ∀ coin, sg (u coin n) = - sg (coin o) := by
                        intro coin
                        obtain ⟨r1, r2, r3⟩ := hu coin n (by omega)
                        rw [h4 coin] at r1 r2 r3
                        cases hc : coin o
                        · rw [hc, hf] at r3
                          rw [r3 (by norm_num), ht, hf]; norm_num
                        · rw [hc, ht] at r2
                          rw [r2 (by norm_num), ht, hf]
                      have hon : o ≠ n := by omega
                      obtain ⟨c', hc'⟩ : ∃ c' : ℕ → ℝ, c' = Function.update (Function.update c n 0) o (f o - f n) := ⟨_, rfl⟩
                      have hc'o : c' o = f o - f n := by rw [hc', Function.update_self]
                      have hc'n : c' n = 0 := by rw [hc', Function.update_of_ne hon.symm, Function.update_self]
                      have hc'e : ∀ a, a ≠ o → a ≠ n → c' a = c a := by
                        intro a h1 h2
                        rw [hc', Function.update_of_ne h1, Function.update_of_ne h2]
                      refine ⟨c', ?_, ?_, ?_⟩
                      · intro a
                        by_cases ha : a = o
                        · subst ha; rw [hc'o]
                          rcases hf01 a with h | h <;> rcases hf01 n with h' | h' <;> rw [h, h'] <;> simp
                        · by_cases han : a = n
                          · subst han; rw [hc'n]; simp
                          · rw [hc'e a ha han]; exact h1 a
                      · intro coin
                        rw [Finset.sum_range_succ, Finset.sum_range_succ, h2, hun, hc'n]
                        rw [← Finset.sum_erase_add _ _ (Finset.mem_range.2 ho),
                            ← Finset.sum_erase_add (Finset.range n) (fun a => c' a * sg (coin a)) (Finset.mem_range.2 ho),
                            hc'o, hco]
                        have : ∑ a ∈ (Finset.range n).erase o, c' a * sg (coin a)
                            = ∑ a ∈ (Finset.range n).erase o, c a * sg (coin a) := by
                          refine Finset.sum_congr rfl fun a ha => ?_
                          have h7 := Finset.mem_range.1 (Finset.mem_of_mem_erase ha)
                          rw [hc'e a (Finset.ne_of_mem_erase ha) (by omega)]
                        rw [this]
                        ring
                      · intro k
                        by_cases hk : cell n = k
                        · left
                          refine ⟨fun coin => ?_, fun hκ a ha hak => ?_⟩
                          · rw [Finset.sum_range_succ, if_pos hk, hun, ← hk, h4]; ring
                          · by_cases hao : a = o
                            · rw [hao, hc'o, hfc o n hok (by rw [hok, hk]; exact hκ), sub_self]
                            · by_cases han : a = n
                              · rw [han, hc'n]
                              · rw [hc'e a hao han]
                                exact h5 (by rw [hk]; exact hκ) a (by omega) (by rw [hk]; exact hak) hao
                        · rcases h3 k with ⟨h6, h7⟩ | ⟨o', ho', hok', hco', h6, h7⟩
                          · left
                            refine ⟨fun coin => ?_, fun hκ a ha hak => ?_⟩
                            · rw [Finset.sum_range_succ, if_neg hk, h6, zero_add]
                            · have han : a ≠ n := by rintro rfl; exact hk hak
                              have hao : a ≠ o := by rintro rfl; exact hk (hok.symm.trans hak)
                              rw [hc'e a hao han]
                              exact h7 hκ a (by omega) hak
                          · right
                            have hoo : o' ≠ o := by rintro rfl; exact hk (hok.symm.trans hok')
                            refine ⟨o', by omega, hok', ?_, fun coin => ?_, fun hκ a ha hak hao' => ?_⟩
                            · rw [hc'e o' hoo (by omega)]; exact hco'
                            · rw [Finset.sum_range_succ, if_neg hk, h6, add_zero]
                            · have han : a ≠ n := by rintro rfl; exact hk hak
                              have hao : a ≠ o := by rintro rfl; exact hk (hok.symm.trans hak)
                              rw [hc'e a hao han]
                              exact h7 hκ a (by omega) hak hao'
                intro n hn
                obtain ⟨c, h1, h2, h3⟩ := key n hn
                refine ⟨c, h1, h2, fun a b ha hb hca hcb hκ hab => ?_⟩
                rcases h3 (cell a) with ⟨h4, h5⟩ | ⟨o, ho, hok, hco, h4, h5⟩
                · exact absurd (h5 hκ a ha rfl) hca
                · have e1 : a = o := by
                    by_contra h; exact hca (h5 hκ a ha rfl h)
                  have e2 : b = o := by
                    by_contra h; exact hcb (h5 hκ b hb hab.symm h)
                  rw [e1, e2]
            have mgf : ∀ (T n N : ℕ) (c : ℕ → ℝ) (l : ℝ), n ≤ T → (∀ a, |c a| ≤ 1) →
                ((Finset.range n).filter (fun a => c a ≠ 0)).card ≤ N →
                ∑ coin : Fin T → Bool, Real.exp (l * ∑ a ∈ Finset.range n, c a * sg (PigeonholeDesign.Upper.coinOf coin a))
                  ≤ 2 ^ T * Real.exp (l ^ 2 * N / 2) := by
              clear * - ht hf sg
              as_aux_lemma =>
                intro T n N c l hn hc hN
                have e1 : ∀ coin : Fin T → Bool, Real.exp (l * ∑ a ∈ Finset.range n, c a * sg (PigeonholeDesign.Upper.coinOf coin a))
                    = ∏ i : Fin T, Real.exp (if (i : ℕ) < n then l * c i * sg (coin i) else 0) := by
                  intro coin
                  rw [← Real.exp_sum]
                  congr 1
                  rw [Finset.mul_sum]
                  have : Finset.range n = (Finset.range T).filter (fun a => a < n) := by
                    ext a; simp; omega
                  rw [this, Finset.sum_filter, Finset.sum_range]
                  refine Finset.sum_congr rfl fun i _ => ?_
                  simp [PigeonholeDesign.Upper.coinOf, mul_assoc]
                simp only [e1]
                have e2 := Finset.prod_univ_sum (fun _ : Fin T => (Finset.univ : Finset Bool))
                  (fun i b => Real.exp (if (i : ℕ) < n then l * c i * sg b else 0))
                rw [Fintype.piFinset_univ] at e2
                rw [← e2]
                have e3 : ∀ i : Fin T, ∑ b : Bool, Real.exp (if (i : ℕ) < n then l * c i * sg b else 0)
                    ≤ 2 * Real.exp (if (i : ℕ) < n ∧ c i ≠ 0 then l ^ 2 / 2 else 0) := by
                  intro i
                  rw [Fintype.sum_bool, ht, hf]
                  by_cases h : (i : ℕ) < n
                  · by_cases h' : c i = 0
                    · simp [h, h']; norm_num
                    · simp only [h, h', if_true, ne_eq, not_false_eq_true, and_self]
                      have h1 := Real.cosh_le_exp_half_sq (l * c i)
                      rw [Real.cosh_eq] at h1
                      have h2 : Real.exp ((l * c i) ^ 2 / 2) ≤ Real.exp (l ^ 2 / 2) := by
                        apply Real.exp_le_exp.2
                        have h3 : (c i) ^ 2 ≤ 1 := by rw [sq_le_one_iff_abs_le_one]; exact hc i
                        rw [mul_pow]
                        nlinarith [sq_nonneg l]
                      rw [mul_one, mul_neg_one]
                      linarith
                  · simp [h]; norm_num
                refine (Finset.prod_le_prod (fun i _ => by positivity) (fun i _ => e3 i)).trans ?_
                rw [Finset.prod_mul_distrib, ← Real.exp_sum]
                simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
                refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (by positivity)
                rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
                have e4 : ((Finset.univ.filter (fun i : Fin T => (i : ℕ) < n ∧ c i ≠ 0)).card : ℝ) ≤ N := by
                  refine Nat.cast_le.2 (le_trans ?_ hN)
                  refine Finset.card_le_card_of_injOn (fun i => (i : ℕ)) ?_ (fun a _ b _ h => Fin.ext h)
                  intro i hi
                  simpa using hi
                nlinarith [sq_nonneg l]
            have maxb : ∀ (T N : ℕ) (V : (Fin T → Bool) → ℕ → ℝ) (c : ℕ → ℕ → ℝ) (τ : (Fin T → Bool) → ℕ) (l : ℝ),
                0 < l → (∀ coin, τ coin ≤ T) →
                (∀ n ≤ T, (∀ a, |c n a| ≤ 1) ∧ ((Finset.range n).filter (fun a => c n a ≠ 0)).card ≤ N ∧
                  ∀ coin, V coin n = ∑ a ∈ Finset.range n, c n a * sg (PigeonholeDesign.Upper.coinOf coin a)) →
                ∑ coin : Fin T → Bool, |V coin (τ coin)| ≤ 2 ^ T * (Real.log (2 * (T + 1)) / l + l * N / 2) := by
              clear * - mgf sg
              as_aux_lemma =>
                intro T N V c τ l hl hτ hV
                obtain ⟨B, hB⟩ : ∃ B : ℝ, B = 2 * (T + 1) * Real.exp (l ^ 2 * N / 2) := ⟨_, rfl⟩
                have hBpos : 0 < B := by rw [hB]; positivity
                have hlogB : Real.log B = Real.log (2 * (T + 1)) + l ^ 2 * N / 2 := by
                  rw [hB, Real.log_mul (by positivity) (by positivity), Real.log_exp]
                have hpt : ∀ y : ℝ, l * y ≤ Real.exp (l * y) / B + Real.log B - 1 := by
                  intro y
                  have h := Real.add_one_le_exp (l * y - Real.log B)
                  rw [Real.exp_sub, Real.exp_log hBpos] at h
                  linarith
                have h1 : ∀ coin : Fin T → Bool, l * |V coin (τ coin)| ≤
                    (∑ n ∈ Finset.range (T + 1), (Real.exp (l * V coin n) + Real.exp ((-l) * V coin n))) / B + Real.log B - 1 := by
                  intro coin
                  have hs : Real.exp (l * V coin (τ coin)) + Real.exp ((-l) * V coin (τ coin)) ≤
                      ∑ n ∈ Finset.range (T + 1), (Real.exp (l * V coin n) + Real.exp ((-l) * V coin n)) :=
                    Finset.single_le_sum (f := fun n => Real.exp (l * V coin n) + Real.exp ((-l) * V coin n))
                      (fun n _ => by positivity) (Finset.mem_range.2 (Nat.lt_succ_of_le (hτ coin)))
                  have hp1 := Real.exp_pos (l * V coin (τ coin))
                  have hp2 := Real.exp_pos ((-l) * V coin (τ coin))
                  rcases abs_cases (V coin (τ coin)) with ⟨h, -⟩ | ⟨h, -⟩
                  · rw [h]
                    have := hpt (V coin (τ coin))
                    have h3 := div_le_div_of_nonneg_right (c := B) (by linarith : Real.exp (l * V coin (τ coin)) ≤ ∑ n ∈ Finset.range (T + 1), (Real.exp (l * V coin n) + Real.exp ((-l) * V coin n))) hBpos.le
                    linarith
                  · rw [h]
                    have := hpt (-V coin (τ coin))
                    rw [show l * -V coin (τ coin) = (-l) * V coin (τ coin) by ring] at this ⊢
                    have h3 := div_le_div_of_nonneg_right (c := B) (by linarith : Real.exp ((-l) * V coin (τ coin)) ≤ ∑ n ∈ Finset.range (T + 1), (Real.exp (l * V coin n) + Real.exp ((-l) * V coin n))) hBpos.le
                    linarith
                have h2 : ∑ coin : Fin T → Bool, ∑ n ∈ Finset.range (T + 1), (Real.exp (l * V coin n) + Real.exp ((-l) * V coin n)) ≤ 2 ^ T * B := by
                  rw [Finset.sum_comm]
                  have : ∀ n ∈ Finset.range (T + 1), ∑ coin : Fin T → Bool, (Real.exp (l * V coin n) + Real.exp ((-l) * V coin n)) ≤ 2 ^ T * (2 * Real.exp (l ^ 2 * N / 2)) := by
                    intro n hn
                    have hn' : n ≤ T := by have := Finset.mem_range.1 hn; omega
                    obtain ⟨c1, c2, c3⟩ := hV n hn'
                    rw [Finset.sum_add_distrib]
                    have m1 := mgf T n N (c n) l hn' c1 c2
                    have m2 := mgf T n N (c n) (-l) hn' c1 c2
                    simp only [← c3, neg_sq] at m1 m2
                    linarith
                  refine (Finset.sum_le_sum this).trans ?_
                  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, hB]
                  push_cast
                  apply le_of_eq; ring
                have h3 := Finset.sum_le_sum (s := Finset.univ) (fun coin _ => h1 coin)
                rw [← Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.sum_div] at h3
                simp only [Finset.sum_const, Finset.card_univ, Fintype.card_pi, Fintype.card_bool, Finset.prod_const, Fintype.card_fin, nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat, mul_one] at h3
                have h4 : (∑ coin : Fin T → Bool, ∑ n ∈ Finset.range (T + 1), (Real.exp (l * V coin n) + Real.exp ((-l) * V coin n))) / B ≤ 2 ^ T := by
                  rw [div_le_iff₀ hBpos]; exact h2
                have h5 : l * ∑ coin : Fin T → Bool, |V coin (τ coin)| ≤ 2 ^ T * (Real.log (2 * (T + 1)) + l ^ 2 * N / 2) := by
                  rw [← hlogB]; linarith
                have h6 : (2:ℝ) ^ T * (Real.log (2 * (T + 1)) / l + l * N / 2) = (2 ^ T * (Real.log (2 * (T + 1)) + l ^ 2 * N / 2)) / l := by
                  field_simp
                rw [h6, le_div_iff₀ hl]
                linarith
            have expG : ∀ (ι : Type) [DecidableEq ι] (T K : ℕ) (cell : ℕ → ι) (g : ι → ℕ), Even T →
                (∀ s < T, g (cell s) < K) → (∀ s < T, ∀ t < T, g (cell s) = g (cell t) → cell s = cell t) →
                ∃ w : (Fin T → Bool) → ℕ → Bool,
                  (∀ coin n, PigeonholeDesign.Upper.prefixAssign T cell (PigeonholeDesign.Upper.coinOf coin) n
                    = (List.range n).map (w coin)) ∧
                  (∀ coin, ((Finset.range T).filter (fun t => w coin t = false)).card = T / 2 ∧
                    ((Finset.range T).filter (fun t => w coin t = true)).card = T / 2) ∧
                  (∀ coin, ∀ n < T / 2,
                      ((∑ t ∈ Finset.range n, (if cell t = cell n then sg (w coin t) else 0) = 0 →
                          w coin n = PigeonholeDesign.Upper.coinOf coin n) ∧
                       (0 < ∑ t ∈ Finset.range n, (if cell t = cell n then sg (w coin t) else 0) → w coin n = false) ∧
                       (∑ t ∈ Finset.range n, (if cell t = cell n then sg (w coin t) else 0) < 0 → w coin n = true))) ∧
                  (∀ (f : ℕ → ℝ) (κ : ι) (N : ℕ) (l : ℝ), 0 < l → (∀ t, f t = 0 ∨ f t = 1) →
                    (∀ s t, cell s = cell t → cell s ≠ κ → f s = f t) →
                    ((Finset.range T).filter (fun t => cell t = κ)).card ≤ N →
                    ∑ coin : Fin T → Bool, |∑ t ∈ Finset.range T, f t * sg (w coin t)| ≤
                      2 ^ T * (2 * (Real.log (2 * (T + 1)) / l) + l * (N + K))) := by
              clear * - ht hf struct compare rad maxb sg
              as_aux_lemma =>
                intro ι _ T K cell g hT hgK hginj
                choose w0 hw0 hwr0 using struct ι T cell
                choose u0 hu0 hur0 using struct ι (4 * T + 4) cell
                have hunf : ∀ coin, ∀ n < T, 
                        ((∑ t ∈ Finset.range n, (if cell t = cell n then sg (u0 coin t) else 0) = 0 → u0 coin n = coin n) ∧
                         (0 < ∑ t ∈ Finset.range n, (if cell t = cell n then sg (u0 coin t) else 0) → u0 coin n = false) ∧
                         (∑ t ∈ Finset.range n, (if cell t = cell n then sg (u0 coin t) else 0) < 0 → u0 coin n = true)) := by
                  intro coin n hn
                  have c1 := Finset.card_filter_le (Finset.range n) (fun t => u0 coin t = false)
                  have c2 := Finset.card_filter_le (Finset.range n) (fun t => u0 coin t = true)
                  rw [Finset.card_range] at c1 c2
                  exact (hur0 coin n).2.2 (by omega) (by omega)
                have hcmp := fun coin => compare ι T cell coin (w0 coin) (u0 coin) hT (hwr0 coin) (hunf coin)
                refine ⟨fun coin => w0 (PigeonholeDesign.Upper.coinOf coin), fun coin n => hw0 _ n,
                  fun coin => ⟨(hcmp _).1, (hcmp _).2.1⟩, ?_, ?_⟩
                · intro coin n hn
                  have c1 := Finset.card_filter_le (Finset.range n) (fun t => w0 (PigeonholeDesign.Upper.coinOf coin) t = false)
                  have c2 := Finset.card_filter_le (Finset.range n) (fun t => w0 (PigeonholeDesign.Upper.coinOf coin) t = true)
                  rw [Finset.card_range] at c1 c2
                  exact (hwr0 _ n).2.2 (by omega) (by omega)
                · intro f κ N l hl hf01 hfc hN
                  choose τ hτT _ hτu b hb using fun coin => (hcmp coin).2.2
                  -- bound for one f
                  have one : ∀ f : ℕ → ℝ, (∀ t, f t = 0 ∨ f t = 1) → (∀ s t, cell s = cell t → cell s ≠ κ → f s = f t) →
                      ∑ coin : Fin T → Bool, |∑ t ∈ Finset.range (τ (PigeonholeDesign.Upper.coinOf coin)), f t * sg (u0 (PigeonholeDesign.Upper.coinOf coin) t)|
                        ≤ 2 ^ T * (Real.log (2 * (T + 1)) / l + l * ((N + K : ℕ) : ℝ) / 2) := by
                    intro f hf01 hfc
                    have hr := rad ι T cell u0 f κ hf01 hfc hunf
                    choose! c hc1 hc2 hc3 using hr
                    refine maxb T (N + K) (fun coin n => ∑ t ∈ Finset.range n, f t * sg (u0 (PigeonholeDesign.Upper.coinOf coin) t)) c
                      (fun coin => τ (PigeonholeDesign.Upper.coinOf coin)) l hl (fun coin => hτT _) ?_
                    intro n hn
                    refine ⟨hc1 n hn, ?_, fun coin => hc2 n hn _⟩
                    have hsub : (Finset.range n).filter (fun a => c n a ≠ 0) ⊆
                        (Finset.range T).filter (fun t => cell t = κ) ∪ (Finset.range n).filter (fun a => c n a ≠ 0 ∧ cell a ≠ κ) := by
                      intro a ha
                      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_union] at ha ⊢
                      by_cases h : cell a = κ
                      · left; exact ⟨by omega, h⟩
                      · right; exact ⟨ha.1, ha.2, h⟩
                    refine (Finset.card_le_card hsub).trans ((Finset.card_union_le _ _).trans (Nat.add_le_add hN ?_))
                    have := Finset.card_le_card_of_injOn (s := (Finset.range n).filter (fun a => c n a ≠ 0 ∧ cell a ≠ κ))
                      (t := Finset.range K) (fun a => g (cell a)) (by
                        intro a ha
                        have ha := Finset.mem_filter.1 (Finset.mem_coe.1 ha)
                        have h1 := Finset.mem_range.1 ha.1
                        exact Finset.mem_coe.2 (Finset.mem_range.2 (hgK a (by omega)))) (by
                        intro a ha b' hb' hab
                        have ha := Finset.mem_filter.1 (Finset.mem_coe.1 ha)
                        have hb' := Finset.mem_filter.1 (Finset.mem_coe.1 hb')
                        have h1 := Finset.mem_range.1 ha.1
                        have h2 := Finset.mem_range.1 hb'.1
                        exact hc3 n hn a b' h1 h2 ha.2.1 hb'.2.1 ha.2.2 (hginj a (by omega) b' (by omega) hab))
                    rwa [Finset.card_range] at this
                  have b1 := one f hf01 hfc
                  have b2 := one (fun _ => 1) (fun _ => Or.inr rfl) (fun _ _ _ _ => rfl)
                  have hsplit : ∀ (coin : ℕ → Bool) (f : ℕ → ℝ), ∑ t ∈ Finset.range T, f t * sg (w0 coin t)
                      = ∑ t ∈ Finset.range (τ coin), f t * sg (u0 coin t) + sg (b coin) * ∑ t ∈ Finset.Ico (τ coin) T, f t := by
                    intro coin f
                    rw [← Finset.sum_range_add_sum_Ico _ (hτT coin)]
                    congr 1
                    · refine Finset.sum_congr rfl fun t ht' => ?_
                      rw [hτu coin t (Finset.mem_range.1 ht')]
                    · rw [Finset.mul_sum]
                      refine Finset.sum_congr rfl fun t ht' => ?_
                      rw [hb coin t (Finset.mem_Ico.1 ht').1 (Finset.mem_Ico.1 ht').2, mul_comm]
                  have hsgabs : ∀ b, |sg b| = 1 := by intro b; cases b <;> simp [ht, hf]
                  have hzero : ∀ coin, ∑ t ∈ Finset.range T, (1:ℝ) * sg (w0 coin t) = 0 := by
                    intro coin
                    have : ∀ t ∈ Finset.range T, (1:ℝ) * sg (w0 coin t) = (if w0 coin t = true then 1 else 0) - (if w0 coin t = false then 1 else 0) := by
                      intro t _
                      cases w0 coin t <;> simp [ht, hf]
                    rw [Finset.sum_congr rfl this, Finset.sum_sub_distrib, ← Finset.sum_filter, ← Finset.sum_filter,
                      Finset.sum_const, Finset.sum_const, (hcmp coin).1, (hcmp coin).2.1, sub_self]
                  have hpt : ∀ coin, |∑ t ∈ Finset.range T, f t * sg (w0 coin t)| ≤
                      |∑ t ∈ Finset.range (τ coin), f t * sg (u0 coin t)| + |∑ t ∈ Finset.range (τ coin), (1:ℝ) * sg (u0 coin t)| := by
                    intro coin
                    rw [hsplit coin f]
                    refine (abs_add_le _ _).trans (add_le_add le_rfl ?_)
                    have h0 := hzero coin
                    rw [hsplit coin (fun _ => 1)] at h0
                    have h1 : ∑ t ∈ Finset.range (τ coin), (1:ℝ) * sg (u0 coin t) = - (sg (b coin) * ∑ t ∈ Finset.Ico (τ coin) T, (1:ℝ)) := by linarith
                    rw [h1, abs_neg, abs_mul, abs_mul, hsgabs, one_mul, one_mul]
                    have hnn : ∀ t ∈ Finset.Ico (τ coin) T, 0 ≤ f t := by
                      intro t _; rcases hf01 t with h | h <;> rw [h]; norm_num
                    rw [abs_of_nonneg (Finset.sum_nonneg hnn), abs_of_nonneg (Finset.sum_nonneg (fun _ _ => zero_le_one))]
                    refine Finset.sum_le_sum fun t _ => ?_
                    rcases hf01 t with h | h <;> rw [h]; norm_num
                  refine (Finset.sum_le_sum (fun coin _ => hpt (PigeonholeDesign.Upper.coinOf coin))).trans ?_
                  rw [Finset.sum_add_distrib]
                  refine (add_le_add b1 b2).trans (le_of_eq ?_)
                  push_cast
                  ring
            have finalNum : ∀ (Q m r sl Lg : ℝ), 1 ≤ r → 1 ≤ sl → 0 ≤ Q → r ^ 2 ≤ m → m ≤ 2 * r ^ 2 → Lg ≤ 2 * sl ^ 2 →
                4 * Q * (Lg * r / sl) + (sl / r) * (r ^ 4 / m) + (sl / r) * (4 * Q ^ 2 * m) + 1 / m
                  ≤ (2 + 8 * Q + 8 * Q ^ 2) * (r * sl) := by
              clear * -  sg
              as_aux_lemma =>
                intro Q m r sl Lg hr1 hsl1 hQ0 hm1 hm2 hLgle
                have hrpos : 0 < r := by linarith
                have hslpos : 0 < sl := by linarith
                have hm1' : 1 ≤ m := (one_le_pow₀ hr1).trans hm1
                have hmpos : 0 < m := by linarith
                have t1 : Lg * r / sl ≤ 2 * (r * sl) := by
                  rw [div_le_iff₀ hslpos]
                  have := mul_le_mul_of_nonneg_right hLgle hrpos.le
                  linarith
                have t2 : (sl / r) * (r ^ 4 / m) ≤ r * sl := by
                  rw [div_mul_div_comm, div_le_iff₀ (mul_pos hrpos hmpos)]
                  have h2 : 0 ≤ sl * r ^ 2 * (m - r ^ 2) := mul_nonneg (mul_nonneg hslpos.le (sq_nonneg _)) (sub_nonneg.2 hm1)
                  linarith
                have t3 : (sl / r) * (4 * Q ^ 2 * m) ≤ 8 * Q ^ 2 * (r * sl) := by
                  rw [div_mul_eq_mul_div, div_le_iff₀ hrpos]
                  have h2 : 0 ≤ 4 * Q ^ 2 * sl * (2 * r ^ 2 - m) :=
                    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _)) hslpos.le) (sub_nonneg.2 hm2)
                  linarith
                have t4 : 1 / m ≤ r * sl := by
                  rw [div_le_iff₀ hmpos]
                  exact one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hr1 hsl1) hm1'
                have t5 := mul_le_mul_of_nonneg_left t1 (mul_nonneg (by norm_num) hQ0 : (0:ℝ) ≤ 4 * Q)
                linarith
            have finalEq : ∀ (q Q m r sl Lg T Kc : ℝ), 0 < m → 0 < r → 0 < sl → T = r ^ 4 → Kc = 2 * Q * m →
                (q + 1 : ℝ) / (m * T) * ((Kc * T) * (2 * (Lg / (sl / r))) + (sl / r) * (T * T) + (sl / r) * ((Kc * T) * Kc) + T)
                  = (q + 1) * (4 * Q * (Lg * r / sl) + (sl / r) * (r ^ 4 / m) + (sl / r) * (4 * Q ^ 2 * m) + 1 / m) := by
              clear * -  sg
              as_aux_lemma =>
                intro q Q m r sl Lg T Kc hm hr hsl hT hK
                rw [hT, hK]
                field_simp
                ring
            have numeric0 : ∀ (m r J n s : ℝ), 8 ≤ m → 0 < r → r ^ 2 ≤ 2 * m → m / 2 ≤ J → m / 8 ≤ n →
                1 / 64 * r ≤ J / (2 * m) * (1 / 4 * Real.sqrt n) := by
              clear * -  sg
              as_aux_lemma =>
                intro m r J n s hm hr hrm h1 h2
                have h3 : (1:ℝ) / 4 ≤ J / (2 * m) := by
                  rw [le_div_iff₀ (by linarith)]; linarith
                have h4 : r / 4 ≤ Real.sqrt n := by
                  apply Real.le_sqrt_of_sq_le
                  linarith
                have h5 : r / 16 ≤ 1 / 4 * Real.sqrt n := by linarith
                have h6 := mul_le_mul h3 h5 (by linarith) (by linarith)
                linarith
            have sqm : ∀ (m r : ℝ), 8 ≤ m → r ^ 4 < (m + 1) * (m + 1) → r ^ 2 ≤ 2 * m := by
              clear * -  sg
              as_aux_lemma =>
                intro m r hm h1
                have h2 : (r ^ 2) ^ 2 ≤ (2 * m) ^ 2 := by
                  have h3 : (m + 1) * (m + 1) ≤ (2 * m) * (2 * m) := mul_le_mul (by linarith) (by linarith) (by linarith) (by linarith)
                  linarith
                exact (pow_le_pow_iff_left₀ (sq_nonneg r) (by linarith) (by norm_num)).1 h2
            have floorNum : ∀ (a b c d M : ℝ), 0 < M → a * M - 1 ≤ c → c ≤ a * M → b * M - 1 ≤ d → d ≤ b * M → |a - b| * M ≤ |c - d| + 1 := by
              clear * -  sg
              as_aux_lemma =>
                intro a b c d M hM h1 h2 h3 h4
                have h5 : |a - b| * M = |a * M - b * M| := by rw [← sub_mul, abs_mul, abs_of_pos hM]
                rw [h5]
                have h6 := le_abs_self (c - d)
                have h7 := neg_le_abs (c - d)
                rw [abs_le]
                constructor <;> linarith
            clear struct compare rad mgf maxb absrep sgsplit
            have upper : ∃ C : ℝ, 0 < C ∧ ∃ T₀ : ℕ, ∀ T : ℕ, T₀ ≤ T → Even T →
                ∀ x : Fin T → MultiDim.Cov q 1, MultiDim.Admissible S x →
                  PigeonholeDesign.Upper.phdExp
                      (MultiDim.gridHole (q := q) (p := 1) ⌈(T : ℝ) ^ ((1 : ℝ) / 2)⌉₊) x
                    ≤ C * ((T : ℝ) ^ ((1 : ℝ) / 4) * Real.sqrt (Real.log T)) := by
              clear khin matchLow numeric0 sqm
              as_aux_lemma =>
                have sq1 : ∀ a b : ℝ, 0 ≤ a → a ≤ 1 → 0 ≤ b → b ≤ 1 → (a - b) ^ 2 ≤ 1 := by
                  intro a b h1 h2 h3 h4
                  rw [sq_le_one_iff_abs_le_one, abs_le]
                  constructor <;> linarith
                have sq2 : ∀ a : ℝ, 0 ≤ a → a + 1 ≤ (a + 1) ^ 2 := by
                  intro a h
                  have : 0 ≤ a ^ 2 := sq_nonneg a
                  linarith
                have sq3 : ∀ a : ℝ, 3 ≤ a → 2 * (a + 1) ≤ a ^ 2 := by
                  intro a h
                  have := mul_self_le_mul_self (by norm_num) (by linarith : (2:ℝ) ≤ a - 1)
                  linarith
                obtain ⟨D, hD⟩ : ∃ D : Finset (Fin q → ℝ), D = Fintype.piFinset S := ⟨_, rfl⟩
                obtain ⟨ρ, hρlt, hρinj⟩ : ∃ ρ : (Fin q → ℝ) → ℕ, (∀ z ∈ D, ρ z < D.card) ∧
                    (∀ z ∈ D, ∀ z' ∈ D, ρ z = ρ z' → z = z') := by
                  refine ⟨fun z => if h : z ∈ D then (D.equivFin ⟨z, h⟩ : ℕ) else 0, ?_, ?_⟩
                  · intro z hz
                    simp only [dif_pos hz]
                    exact (D.equivFin ⟨z, hz⟩).2
                  · intro z hz z' hz' h
                    simp only [dif_pos hz, dif_pos hz'] at h
                    have := D.equivFin.injective (Fin.ext h)
                    exact congrArg Subtype.val this
                obtain ⟨Q, hQ⟩ : ∃ Q : ℕ, Q = D.card := ⟨_, rfl⟩
                rw [← hQ] at hρlt
                refine ⟨(q + 1) * (2 + 8 * Q + 8 * Q ^ 2), by positivity, 3, ?_⟩
                intro T hT3 hT x hx
                have hT0 : 0 < T := by omega
                have hTR : (0:ℝ) < T := by exact_mod_cast hT0
                have hT3R : (3:ℝ) ≤ T := by exact_mod_cast hT3
                obtain ⟨m, hm⟩ : ∃ m : ℕ, m = ⌈(T : ℝ) ^ ((1 : ℝ) / 2)⌉₊ := ⟨_, rfl⟩
                rw [← hm]
                obtain ⟨r, hr⟩ : ∃ r : ℝ, r = (T : ℝ) ^ ((1 : ℝ) / 4) := ⟨_, rfl⟩
                have hr2 : (T : ℝ) ^ ((1 : ℝ) / 2) = r ^ 2 := by
                  rw [hr, ← Real.rpow_natCast, ← Real.rpow_mul hTR.le]; norm_num
                have hr4 : (T : ℝ) = r ^ 4 := by
                  rw [hr, ← Real.rpow_natCast, ← Real.rpow_mul hTR.le]; norm_num
                have hr1 : 1 ≤ r := by
                  rw [hr]; exact Real.one_le_rpow (by linarith only [hT3R]) (by norm_num)
                rw [hr2] at hm
                have hr21 : 1 ≤ r ^ 2 := one_le_pow₀ hr1
                have hm1 : r ^ 2 ≤ m := by rw [hm]; exact Nat.le_ceil _
                have hm2 : (m : ℝ) ≤ 2 * r ^ 2 := by
                  have h := Nat.ceil_lt_add_one (by positivity : 0 ≤ r ^ 2)
                  rw [← hm] at h
                  linarith only [h, hr21]
                have hm1' : (1:ℝ) ≤ m := hr21.trans hm1
                have hm0 : 0 < m := by
                  have : (0:ℝ) < m := lt_of_lt_of_le one_pos hm1'
                  exact_mod_cast this
                have hmT : 0 < m * T := Nat.mul_pos hm0 hT0
                -- discrete coordinates
                obtain ⟨z, hz⟩ : ∃ z : Fin T → (Fin q → ℝ), z = fun t i => x t (Sum.inl i) := ⟨_, rfl⟩
                obtain ⟨v, hv⟩ : ∃ v : Fin T → ℝ, v = fun t => x t (Sum.inr 0) := ⟨_, rfl⟩
                have hzD : ∀ t, z t ∈ D := by
                  intro t
                  rw [hD, Fintype.mem_piFinset, hz]
                  exact fun i => hx.1 t i
                have hv01 : ∀ t, 0 ≤ v t ∧ v t ≤ 1 := by
                  intro t
                  rw [hv]
                  exact hx.2 t 0
                obtain ⟨k, hk⟩ : ∃ k : Fin T → ℕ, k = fun t => min ⌊v t * (m * T : ℕ)⌋₊ (m * T - 1) := ⟨_, rfl⟩
                have hklt : ∀ t, k t < m * T := by
                  intro t
                  rw [hk]
                  exact lt_of_le_of_lt (min_le_right _ _) (by omega)
                have hk1 : ∀ t, (k t : ℝ) ≤ v t * (m * T : ℕ) := by
                  clear expG matchUp finalNum finalEq floorNum
                  as_aux_lemma =>
                    intro t
                    have h1 : k t ≤ ⌊v t * (m * T : ℕ)⌋₊ := by rw [hk]; exact min_le_left _ _
                    have h2 := Nat.floor_le (mul_nonneg (hv01 t).1 (Nat.cast_nonneg (m * T)))
                    exact le_trans (by exact_mod_cast h1) h2
                have hk2 : ∀ t, v t * (m * T : ℕ) ≤ k t + 1 := by
                  clear expG matchUp finalNum finalEq floorNum
                  as_aux_lemma =>
                    intro t
                    rcases le_total ⌊v t * (m * T : ℕ)⌋₊ (m * T - 1) with h | h
                    · have : k t = ⌊v t * (m * T : ℕ)⌋₊ := by rw [hk]; exact min_eq_left h
                      rw [this]
                      exact (Nat.lt_floor_add_one _).le
                    · have : k t = m * T - 1 := by rw [hk]; exact min_eq_right h
                      have h2 : k t + 1 = m * T := by omega
                      have h3 : (k t : ℝ) + 1 = (m * T : ℕ) := by exact_mod_cast h2
                      rw [h3]
                      have := (hv01 t).2
                      have h4 : (0:ℝ) ≤ (m * T : ℕ) := Nat.cast_nonneg _
                      exact mul_le_of_le_one_left h4 this
                have hkdiv : ∀ t, k t / T = min ⌊v t * m⌋₊ (m - 1) := by
                  clear expG matchUp finalNum finalEq floorNum
                  as_aux_lemma =>
                    intro t
                    have h1 : ⌊v t * m⌋₊ = ⌊v t * (m * T : ℕ)⌋₊ / T := by
                      rw [← Nat.floor_div_natCast]
                      congr 1
                      push_cast
                      field_simp
                    rw [h1]
                    have h3 : (m * T - 1) / T = m - 1 := by
                      obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
                      have : (m' + 1) * T - 1 = (T - 1) + T * m' := by
                        have : (m' + 1) * T = T * m' + T := by ring
                        omega
                      rw [this, Nat.add_mul_div_left _ _ hT0, Nat.div_eq_of_lt (by omega)]
                      simp
                    rcases le_total ⌊v t * (m * T : ℕ)⌋₊ (m * T - 1) with h | h
                    · have : k t = ⌊v t * (m * T : ℕ)⌋₊ := by rw [hk]; exact min_eq_left h
                      rw [this, min_eq_left]
                      rw [← h3]; exact Nat.div_le_div_right h
                    · have : k t = m * T - 1 := by rw [hk]; exact min_eq_right h
                      rw [this, h3, min_eq_right]
                      rw [← h3]; exact Nat.div_le_div_right h
                obtain ⟨y, hy⟩ : ∃ y : Fin T → ℕ, y = fun t => k t + T * (2 * ρ (z t) * m) := ⟨_, rfl⟩
                have hyt : ∀ t, y t = k t + T * (2 * ρ (z t) * m) := by intro t; rw [hy]
                have hydiv : ∀ t, y t / T = 2 * ρ (z t) * m + min ⌊v t * m⌋₊ (m - 1) := by
                  clear expG matchUp finalNum finalEq floorNum
                  as_aux_lemma =>
                    intro t
                    rw [hyt, Nat.add_mul_div_left _ _ hT0, hkdiv]; ring
                obtain ⟨Kc, hKc⟩ : ∃ Kc : ℕ, Kc = 2 * Q * m := ⟨_, rfl⟩
                have hydivlt : ∀ t, y t / T < Kc := by
                  clear expG matchUp finalNum finalEq floorNum
                  as_aux_lemma =>
                    intro t
                    rw [hydiv, hKc]
                    have h1 := hρlt _ (hzD t)
                    have h2 : min ⌊v t * m⌋₊ (m - 1) ≤ m - 1 := min_le_right _ _
                    have h3 : (2 * ρ (z t) + 2) * m ≤ 2 * Q * m := Nat.mul_le_mul_right _ (by omega)
                    have h4 : (2 * ρ (z t) + 2) * m = 2 * ρ (z t) * m + 2 * m := by ring
                    omega
                have hylt : ∀ t, y t ≤ Kc * T := by
                  clear expG matchUp finalNum finalEq floorNum
                  as_aux_lemma =>
                    intro t
                    have := hydivlt t
                    rw [Nat.div_lt_iff_lt_mul hT0] at this
                    exact this.le
                -- distances
                have hdist : ∀ s t, dist (x s) (x t) ≤ (q + 1) * ((|(y s : ℝ) - y t| + 1) / (m * T : ℕ)) := by
                  clear expG matchUp finalNum finalEq
                  as_aux_lemma =>
                    intro s t
                    have hmTR : (0:ℝ) < (m * T : ℕ) := by exact_mod_cast hmT
                    rw [EuclideanSpace.dist_eq, Fintype.sum_sum_type]
                    simp only [Finset.univ_unique, Finset.sum_singleton, Fin.default_eq_zero, Fin.isValue, Real.dist_eq, sq_abs]
                    have ev : ∀ t, x t (Sum.inr 0) = v t := by intro t; rw [hv]
                    have ez : ∀ t i, x t (Sum.inl i) = z t i := by intro t i; rw [hz]
                    simp only [ev, ez]
                    have e0 : (0:ℝ) ≤ (|(y s : ℝ) - y t| + 1) / (m * T : ℕ) := div_nonneg (add_nonneg (abs_nonneg _) zero_le_one) hmTR.le
                    by_cases hzz : z s = z t
                    · rw [hzz]
                      simp only [sub_self, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, Finset.sum_const_zero, zero_add, Real.sqrt_sq_eq_abs]
                      have h1 : |v s - v t| ≤ (|(y s : ℝ) - y t| + 1) / (m * T : ℕ) := by
                        rw [le_div_iff₀ hmTR]
                        have h2 : (y s : ℝ) - y t = k s - k t := by
                          rw [hyt, hyt, hzz]; push_cast; ring
                        rw [h2]
                        exact floorNum _ _ _ _ _ hmTR (sub_le_iff_le_add.2 (hk2 s)) (hk1 s) (sub_le_iff_le_add.2 (hk2 t)) (hk1 t)
                      have hq : (0:ℝ) ≤ q := Nat.cast_nonneg _
                      exact h1.trans (le_mul_of_one_le_left e0 (by linarith only [hq]))
                    · have hρne : ρ (z s) ≠ ρ (z t) := fun h => hzz (hρinj _ (hzD s) _ (hzD t) h)
                      have h1 : (1:ℝ) ≤ (|(y s : ℝ) - y t| + 1) / (m * T : ℕ) := by
                        rw [le_div_iff₀ hmTR, one_mul]
                        have h1m : (0:ℝ) ≤ (m * T : ℕ) := hmTR.le
                        have key : ∀ s t, ρ (z s) < ρ (z t) → (m * T : ℕ) ≤ |(y s : ℝ) - y t| := by
                          intro s t h
                          have h5 : y s + m * T ≤ y t := by
                            rw [hyt, hyt]
                            have h6 := hklt s
                            have h7 : T * (2 * (ρ (z s) + 1) * m) ≤ T * (2 * ρ (z t) * m) :=
                              Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ h))
                            have h8 : T * (2 * (ρ (z s) + 1) * m) = T * (2 * ρ (z s) * m) + 2 * (m * T) := by ring
                            omega
                          have h6 : (y s : ℝ) + (m * T : ℕ) ≤ y t := by exact_mod_cast h5
                          have := neg_le_abs ((y s : ℝ) - y t)
                          linarith only [this, h6]
                        rcases lt_or_gt_of_ne hρne with h | h
                        · have := key s t h; linarith only [this, h1m]
                        · have := key t s h
                          rw [abs_sub_comm] at this
                          linarith only [this, h1m]
                      have h2 : Real.sqrt (∑ i, (z s i - z t i) ^ 2 + (v s - v t) ^ 2) ≤ q + 1 := by
                        rw [Real.sqrt_le_left (add_nonneg (Nat.cast_nonneg _) zero_le_one)]
                        have : ∀ i ∈ (Finset.univ : Finset (Fin q)), (z s i - z t i) ^ 2 ≤ (1:ℝ) := by
                          intro i _
                          have h1 := hS i (hx.1 s i)
                          have h2 := hS i (hx.1 t i)
                          rw [ez] at h1 h2
                          exact sq1 _ _ h1.1 h1.2 h2.1 h2.2
                        have h3 := Finset.sum_le_sum this
                        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one] at h3
                        have b1 := hv01 s
                        have b2 := hv01 t
                        have h4 : (v s - v t) ^ 2 ≤ 1 := sq1 _ _ b1.1 b1.2 b2.1 b2.2
                        have hq := sq2 q (Nat.cast_nonneg _)
                        linarith only [hq, h3, h4]
                      refine h2.trans ?_
                      have hq : (0:ℝ) ≤ q := Nat.cast_nonneg _
                      exact le_mul_of_one_le_right (by linarith only [hq]) h1
                -- cells
                obtain ⟨cell, hcelldef⟩ : ∃ cell, cell = PigeonholeDesign.Upper.cellOf (MultiDim.gridHole (q := q) (p := 1) m) x := ⟨_, rfl⟩
                have hcell : ∀ t : Fin T, cell t = some (z t, fun _ => min ⌊v t * m⌋₊ (m - 1)) := by
                  intro t
                  rw [hcelldef, hz, hv]
                  simp only [PigeonholeDesign.Upper.cellOf, dif_pos t.2, MultiDim.gridHole, Fin.eta]
                  congr 2
                  funext j
                  rw [Subsingleton.elim j 0]
                have hcellnone : ∀ n, ¬ n < T → cell n = none := by
                  intro n hn
                  rw [hcelldef]
                  simp [PigeonholeDesign.Upper.cellOf, hn]
                have hcellinj : ∀ s t : Fin T, y s / T = y t / T → cell s = cell t := by
                  clear expG matchUp finalNum finalEq floorNum
                  as_aux_lemma =>
                    intro s t h
                    rw [hydiv, hydiv] at h
                    have c1 : min ⌊v s * m⌋₊ (m - 1) ≤ m - 1 := min_le_right _ _
                    have c2 : min ⌊v t * m⌋₊ (m - 1) ≤ m - 1 := min_le_right _ _
                    have key : ∀ (a b c d : ℕ), c ≤ m - 1 → d ≤ m - 1 → 2 * a * m + c = 2 * b * m + d → ¬ a < b := by
                      intro a b c d hc hd h hab
                      have h1 : 2 * (a + 1) * m ≤ 2 * b * m := Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hab)
                      have h2 : 2 * (a + 1) * m = 2 * a * m + 2 * m := by ring
                      omega
                    have k1 := key _ _ _ _ c1 c2 h
                    have k2 := key _ _ _ _ c2 c1 h.symm
                    have k3 : ρ (z s) = ρ (z t) := by omega
                    have k4 : z s = z t := hρinj _ (hzD s) _ (hzD t) k3
                    rw [k3] at h
                    have k5 : min ⌊v s * m⌋₊ (m - 1) = min ⌊v t * m⌋₊ (m - 1) := by omega
                    rw [hcell, hcell, k4, k5]
                obtain ⟨g, hg⟩ : ∃ g : Option ((Fin q → ℝ) × (Fin 1 → ℕ)) → ℕ, ∀ t : Fin T, g (cell t) = y t / T := by
                  refine ⟨fun o => match o with
                    | none => 0
                    | some p => 2 * ρ p.1 * m + p.2 0, fun t => ?_⟩
                  rw [hcell, hydiv]
                obtain ⟨w, hw1, hw2, -, hw4⟩ := expG _ T Kc cell g hT
                  (fun s hs => by have := hg ⟨s, hs⟩; simp only at this; rw [this]; exact hydivlt _)
                  (fun s hs t ht' h => by
                    have h1 := hg ⟨s, hs⟩
                    have h2 := hg ⟨t, ht'⟩
                    simp only at h1 h2
                    rw [h1, h2] at h
                    exact hcellinj ⟨s, hs⟩ ⟨t, ht'⟩ h)
                clear expG
                have hassign : ∀ coin, PigeonholeDesign.Upper.assign (MultiDim.gridHole (q := q) (p := 1) m) x coin
                    = fun t : Fin T => w coin t := by
                  intro coin
                  funext t
                  simp only [PigeonholeDesign.Upper.assign]
                  rw [← hcelldef, hw1]
                  simp [List.getD_eq_getElem?_getD]
                have hfin : ∀ (P : ℕ → Prop) [DecidablePred P],
                    ((Finset.univ : Finset (Fin T)).filter (fun t : Fin T => P t)).card
                      = ((Finset.range T).filter P).card := by
                  intro P _
                  rw [Finset.card_filter, Finset.card_filter, Finset.sum_range]
                have hE : ∀ coin, Nonempty ({t : Fin T // w coin t = false} ≃ {t : Fin T // w coin t = true}) := by
                  intro coin
                  rw [← Fintype.card_eq, Fintype.card_subtype, Fintype.card_subtype,
                    hfin (fun t => w coin t = false), hfin (fun t => w coin t = true), (hw2 coin).1, (hw2 coin).2]
                have hmTR : (0:ℝ) < (m * T : ℕ) := by exact_mod_cast hmT
                have hqpos : (0:ℝ) < q + 1 := by positivity
                have hdisc : ∀ coin, PigeonholeDesign.Upper.discrepancy x (PigeonholeDesign.Upper.assign (MultiDim.gridHole (q := q) (p := 1) m) x coin)
                    ≤ (q + 1) / (m * T : ℕ) * (∑ j ∈ Finset.range (Kc * T), |∑ t : Fin T, (if y t ≤ j then (1:ℝ) else 0) * sg (w coin t)| + T) := by
                  clear finalNum finalEq floorNum
                  as_aux_lemma =>
                    intro coin
                    rw [hassign]
                    obtain ⟨e, he⟩ := matchUp T y (Kc * T) (fun t : Fin T => w coin t) (hE coin) hylt
                    refine (ciInf_le (Set.finite_range _).bddBelow e).trans ?_
                    refine (Finset.sum_le_sum fun a _ => hdist _ _).trans ?_
                    rw [← Finset.mul_sum, ← Finset.sum_div, Finset.sum_add_distrib, mul_div_assoc', div_mul_eq_mul_div]
                    refine div_le_div_of_nonneg_right ?_ hmTR.le
                    refine mul_le_mul_of_nonneg_left (add_le_add he ?_) hqpos.le
                    rw [Finset.sum_const, nsmul_eq_mul, mul_one, Finset.card_univ]
                    have := Fintype.card_subtype_le (fun t : Fin T => w coin t = false)
                    rw [Fintype.card_fin] at this
                    exact_mod_cast this
                -- expected prefix imbalance
                obtain ⟨Lg, hLg⟩ : ∃ Lg : ℝ, Lg = Real.log (2 * (T + 1)) := ⟨_, rfl⟩
                have hG : ∀ l : ℝ, 0 < l → ∀ j ∈ Finset.range (Kc * T),
                    ∑ coin : Fin T → Bool, |∑ t : Fin T, (if y t ≤ j then (1:ℝ) else 0) * sg (w coin t)|
                    ≤ 2 ^ T * (2 * (Lg / l) + l * (((Finset.univ.filter (fun t : Fin T => y t / T = j / T)).card : ℝ) + Kc)) := by
                  clear finalNum finalEq floorNum matchUp
                  as_aux_lemma =>
                    intro l hl j _
                    obtain ⟨f, hf'⟩ : ∃ f : ℕ → ℝ, f = fun n => if h : n < T then (if y ⟨n, h⟩ ≤ j then (1:ℝ) else 0) else 0 := ⟨_, rfl⟩
                    have hft : ∀ t : Fin T, f t = if y t ≤ j then (1:ℝ) else 0 := by
                      intro t; rw [hf']; simp
                    have hfn : ∀ n, ¬ n < T → f n = 0 := by
                      intro n hn; rw [hf']; simp [hn]
                    have hf01 : ∀ t, f t = 0 ∨ f t = 1 := by
                      intro t
                      by_cases h : t < T
                      · rw [hft ⟨t, h⟩]; split_ifs <;> simp
                      · left; exact hfn t h
                    obtain ⟨κ, hκ⟩ : ∃ κ, ∀ t : Fin T, cell t = κ ↔ y t / T = j / T := by
                      by_cases h : ∃ t0 : Fin T, y t0 / T = j / T
                      · obtain ⟨t0, h0⟩ := h
                        refine ⟨cell t0, fun t => ⟨fun h => ?_, fun h => hcellinj t t0 (h.trans h0.symm)⟩⟩
                        rw [← hg, h, hg, h0]
                      · push Not at h
                        refine ⟨none, fun t => ⟨fun h' => ?_, fun h' => absurd h' (h t)⟩⟩
                        rw [hcell] at h'
                        exact absurd h' (by simp)
                    have h := hw4 f κ (Finset.univ.filter (fun t : Fin T => y t / T = j / T)).card l hl hf01 ?_ ?_
                    · rw [← hLg] at h
                      refine le_trans (le_of_eq ?_) h
                      refine Finset.sum_congr rfl fun coin _ => ?_
                      rw [Finset.sum_range]
                      simp only [hft]
                    · intro s t hst hsκ
                      by_cases hs : s < T
                      · by_cases ht' : t < T
                        · have h1 := hg ⟨s, hs⟩
                          have h2 := hg ⟨t, ht'⟩
                          have h3 := (not_congr (hκ ⟨s, hs⟩)).1 hsκ
                          simp only at h1 h2
                          rw [hst, h2] at h1
                          rw [hft ⟨s, hs⟩, hft ⟨t, ht'⟩]
                          rw [← h1] at h3
                          have : y ⟨s, hs⟩ ≤ j ↔ y ⟨t, ht'⟩ ≤ j := by
                            constructor
                            · intro h4
                              have h5 := Nat.div_le_div_right (c := T) h4
                              by_contra h6
                              have h7 := Nat.div_le_div_right (c := T) (le_of_lt (not_le.1 h6))
                              omega
                            · intro h4
                              have h5 := Nat.div_le_div_right (c := T) h4
                              by_contra h6
                              have h7 := Nat.div_le_div_right (c := T) (le_of_lt (not_le.1 h6))
                              omega
                          simp only [this]
                        · exfalso
                          have h1 := hcell ⟨s, hs⟩
                          simp only at h1
                          rw [hst, hcellnone t ht'] at h1
                          exact absurd h1 (by simp)
                      · by_cases ht' : t < T
                        · exfalso
                          have h1 := hcell ⟨t, ht'⟩
                          simp only at h1
                          rw [← hst, hcellnone s hs] at h1
                          exact absurd h1 (by simp)
                        · rw [hfn s hs, hfn t ht']
                    · rw [← hfin (fun t => cell t = κ)]
                      apply le_of_eq
                      congr 1
                      ext t
                      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
                      exact hκ t
                have hNsum : ∑ j ∈ Finset.range (Kc * T), ((Finset.univ.filter (fun t : Fin T => y t / T = j / T)).card : ℝ) ≤ T * T := by
                  clear finalNum finalEq floorNum matchUp
                  as_aux_lemma =>
                    have : ∑ j ∈ Finset.range (Kc * T), (Finset.univ.filter (fun t : Fin T => y t / T = j / T)).card ≤ T * T := by
                      simp only [Finset.card_filter]
                      rw [Finset.sum_comm]
                      refine (Finset.sum_le_card_nsmul _ _ T fun t _ => ?_).trans (by simp)
                      rw [← Finset.card_filter]
                      have hsub : (Finset.range (Kc * T)).filter (fun j => y t / T = j / T) ⊆ Finset.Ico (T * (y t / T)) (T * (y t / T) + T) := by
                        intro j hj
                        have hj2 := (Finset.mem_filter.1 hj).2
                        have h1 := Nat.div_add_mod j T
                        have h2 := Nat.mod_lt j hT0
                        rw [Finset.mem_Ico, hj2]
                        constructor <;> omega
                      refine (Finset.card_le_card hsub).trans ?_
                      rw [Nat.card_Ico]; omega
                    exact_mod_cast this
                have hphd : ∀ l : ℝ, 0 < l → PigeonholeDesign.Upper.phdExp (MultiDim.gridHole (q := q) (p := 1) m) x
                    ≤ (q + 1) / (m * T : ℕ) * ((Kc * T : ℕ) * (2 * (Lg / l)) + l * (T * T) + l * ((Kc * T : ℕ) * Kc) + T) := by
                  clear finalNum finalEq floorNum matchUp
                  as_aux_lemma =>
                    intro l hl
                    unfold PigeonholeDesign.Upper.phdExp
                    rw [div_le_iff₀ (pow_pos two_pos _)]
                    refine (Finset.sum_le_sum fun coin _ => hdisc coin).trans ?_
                    rw [← Finset.mul_sum, mul_assoc]
                    refine mul_le_mul_of_nonneg_left ?_ (div_nonneg hqpos.le hmTR.le)
                    rw [Finset.sum_add_distrib, Finset.sum_comm]
                    have h1 := Finset.sum_le_sum (hG l hl)
                    rw [← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_add_distrib] at h1
                    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Finset.card_univ, Fintype.card_pi, Fintype.card_bool, Finset.prod_const, Fintype.card_fin] at h1 ⊢
                    have h2 := mul_le_mul_of_nonneg_left hNsum hl.le
                    have h3 : (0:ℝ) < 2 ^ T := by positivity
                    have h4 := mul_le_mul_of_nonneg_left h2 h3.le
                    push_cast at h1 h4 ⊢
                    linarith only [h1, h4]
                obtain ⟨sl, hsl⟩ : ∃ sl : ℝ, sl = Real.sqrt (Real.log T) := ⟨_, rfl⟩
                rw [← hsl, ← hr]
                have hlog1 : 1 ≤ Real.log T := by
                  rw [Real.le_log_iff_exp_le hTR]
                  have := Real.exp_one_lt_d9
                  linarith only [this, hT3R]
                have hsl1 : 1 ≤ sl := by rw [hsl]; exact Real.one_le_sqrt.2 hlog1
                have hsl2 : Real.log T = sl ^ 2 := by rw [hsl, Real.sq_sqrt (zero_le_one.trans hlog1)]
                have hLgle : Lg ≤ 2 * sl ^ 2 := by
                  rw [hLg, ← hsl2]
                  have : 2 * Real.log T = Real.log (T ^ 2) := by rw [Real.log_pow]; norm_num
                  rw [this]
                  exact Real.log_le_log (by linarith only [hTR]) (sq3 _ hT3R)
                have hrpos : 0 < r := lt_of_lt_of_le one_pos hr1
                have hslpos : 0 < sl := lt_of_lt_of_le one_pos hsl1
                have hfinal := hphd (sl / r) (div_pos hslpos hrpos)
                refine hfinal.trans ?_
                have hKcR : (Kc : ℝ) = 2 * Q * m := by rw [hKc]; push_cast; ring
                push_cast
                rw [finalEq q Q m r sl Lg T Kc (lt_of_lt_of_le one_pos hm1') hrpos hslpos hr4 hKcR, mul_assoc ((q:ℝ) + 1)]
                exact mul_le_mul_of_nonneg_left (finalNum Q m r sl Lg hr1 hsl1 (Nat.cast_nonneg _) hm1 hm2 hLgle) hqpos.le
            have lower : ∃ c : ℝ, 0 < c ∧ ∃ T₀ : ℕ, ∀ T : ℕ, T₀ ≤ T → Even T →
                ∀ (K : ℕ) (hole : MultiDim.Cov q 1 → Fin K),
                  ∃ x : Fin T → MultiDim.Cov q 1, MultiDim.Admissible S x ∧
                    c * (T : ℝ) ^ ((1 : ℝ) / 4) ≤ PigeonholeDesign.Upper.phdExp hole x := by
              clear upper matchUp finalNum finalEq floorNum hS
              as_aux_lemma =>
                choose z0 hz0 using hne
                obtain ⟨pt, hpt1, hpt2⟩ : ∃ pt : ℕ → ℕ → MultiDim.Cov q 1, (∀ m i a, pt m i (Sum.inl a) = z0 a) ∧
                    (∀ m i b, pt m i (Sum.inr b) = (i : ℝ) / (2 * m)) :=
                  ⟨fun m i => WithLp.toLp 2 (Sum.elim z0 (fun _ => (i : ℝ) / (2 * m))), fun m i a => by simp, fun m i b => by simp⟩
                have lowgen : ∀ (K : ℕ) (hole : MultiDim.Cov q 1 → Fin K) (T m : ℕ) (g : ℕ → ℕ), Even T → 0 < m →
                    (∀ n, g n ≤ 2 * m) → ∃ x : Fin T → MultiDim.Cov q 1, MultiDim.Admissible S x ∧
                      ∃ w : (Fin T → Bool) → ℕ → Bool,
                        (∀ coin, ∀ n < T / 2,
                          ((∑ t ∈ Finset.range n, (if hole (pt m (g t)) = hole (pt m (g n)) then sg (w coin t) else 0) = 0 →
                              w coin n = PigeonholeDesign.Upper.coinOf coin n) ∧
                           (0 < ∑ t ∈ Finset.range n, (if hole (pt m (g t)) = hole (pt m (g n)) then sg (w coin t) else 0) → w coin n = false) ∧
                           (∑ t ∈ Finset.range n, (if hole (pt m (g t)) = hole (pt m (g n)) then sg (w coin t) else 0) < 0 → w coin n = true))) ∧
                        ∀ (J : Finset ℕ) (n : ℕ) (A : ℕ → Finset ℕ), J ⊆ Finset.range (2 * m) →
                          (∀ j ∈ J, (∀ a ∈ A j, a < T) ∧ n ≤ (A j).card ∧ ∀ coin,
                            ∑ t ∈ Finset.range T, (if g t ≤ j then (1:ℝ) else 0) * sg (w coin t)
                              = ∑ a ∈ A j, sg (PigeonholeDesign.Upper.coinOf coin a)) →
                          (J.card : ℝ) / (2 * m) * (1 / 4 * Real.sqrt n) ≤ PigeonholeDesign.Upper.phdExp hole x := by
                  clear numeric0 sqm
                  as_aux_lemma =>
                    intro K hole T m g hT hm hg
                    have hmR : (0:ℝ) < m := by exact_mod_cast hm
                    obtain ⟨x, hx⟩ : ∃ x : Fin T → MultiDim.Cov q 1, ∀ t : Fin T, x t = pt m (g t) := ⟨fun t => pt m (g t), fun _ => rfl⟩
                    have hcell : ∀ n, n < T → PigeonholeDesign.Upper.cellOf hole x n = some (hole (pt m (g n))) := by
                      intro n hn
                      simp [PigeonholeDesign.Upper.cellOf, hn, hx]
                    obtain ⟨w, hw1, hw2, hw3, -⟩ := expG _ T K (PigeonholeDesign.Upper.cellOf hole x)
                      (fun o => match o with
                        | none => 0
                        | some k => (k : ℕ)) hT
                      (fun s hs => by rw [hcell s hs]; exact (hole (pt m (g s))).2)
                      (fun s hs t ht' h => by
                        rw [hcell s hs, hcell t ht'] at h ⊢
                        exact congrArg some (Fin.ext h))
                    refine ⟨x, ⟨fun t i => ?_, fun t j => ?_⟩, w, ?_, ?_⟩
                    · rw [hx, hpt1]; exact hz0 i
                    · rw [hx, hpt2]
                      have h1 : (g t : ℝ) ≤ 2 * m := by exact_mod_cast hg t
                      exact ⟨by positivity, by rw [div_le_one (by positivity)]; exact h1⟩
                    · intro coin n hn
                      have h := hw3 coin n hn
                      have e : ∑ t ∈ Finset.range n, (if PigeonholeDesign.Upper.cellOf hole x t = PigeonholeDesign.Upper.cellOf hole x n then sg (w coin t) else 0)
                          = ∑ t ∈ Finset.range n, (if hole (pt m (g t)) = hole (pt m (g n)) then sg (w coin t) else 0) := by
                        refine Finset.sum_congr rfl fun t ht' => ?_
                        rw [hcell n (by omega), hcell t (by have := Finset.mem_range.1 ht'; omega)]
                        simp only [Option.some.injEq]
                      rw [e] at h
                      exact h
                    · intro J n A hJ hA
                      have hassign : ∀ coin, PigeonholeDesign.Upper.assign hole x coin = fun t : Fin T => w coin t := by
                        intro coin
                        funext t
                        simp only [PigeonholeDesign.Upper.assign]
                        rw [hw1]
                        simp [List.getD_eq_getElem?_getD]
                      have hfin : ∀ (P : ℕ → Prop) [DecidablePred P],
                          ((Finset.univ : Finset (Fin T)).filter (fun t : Fin T => P t)).card
                            = ((Finset.range T).filter P).card := by
                        intro P _
                        rw [Finset.card_filter, Finset.card_filter, Finset.sum_range]
                      have hE : ∀ coin, Nonempty ({t : Fin T // w coin t = false} ≃ {t : Fin T // w coin t = true}) := by
                        intro coin
                        rw [← Fintype.card_eq, Fintype.card_subtype, Fintype.card_subtype,
                          hfin (fun t => w coin t = false), hfin (fun t => w coin t = true), (hw2 coin).1, (hw2 coin).2]
                      have hdist : ∀ s t, |(g s : ℝ) - g t| / (2 * m) ≤ dist (pt m (g s)) (pt m (g t)) := by
                        intro s t
                        have h := PiLp.norm_apply_le (pt m (g s) - pt m (g t)) (Sum.inr 0)
                        rw [← dist_eq_norm] at h
                        refine le_trans (le_of_eq ?_) h
                        rw [PiLp.sub_apply, hpt2, hpt2, ← sub_div, Real.norm_eq_abs, abs_div, abs_of_pos (by positivity : (0:ℝ) < 2 * m)]
                      have hdisc : ∀ coin, (∑ j ∈ J, |∑ a ∈ A j, sg (PigeonholeDesign.Upper.coinOf coin a)|) / (2 * m) ≤
                          PigeonholeDesign.Upper.discrepancy x (PigeonholeDesign.Upper.assign hole x coin) := by
                        intro coin
                        rw [hassign]
                        unfold PigeonholeDesign.Upper.discrepancy
                        have := hE coin
                        refine le_ciInf fun e => ?_
                        have h1 := matchLow T (fun t => g t) (2 * m) (fun t => w coin t) e (fun t => hg t)
                        have h2 : ∑ j ∈ J, |∑ a ∈ A j, sg (PigeonholeDesign.Upper.coinOf coin a)| ≤
                            ∑ j ∈ Finset.range (2 * m), |∑ t : Fin T, (if g t ≤ j then (1:ℝ) else 0) * sg (w coin t)| := by
                          refine le_trans (le_of_eq ?_) (Finset.sum_le_sum_of_subset_of_nonneg hJ (fun _ _ _ => abs_nonneg _))
                          refine Finset.sum_congr rfl fun j hj => ?_
                          rw [← (hA j hj).2.2 coin, Finset.sum_range]
                        refine (div_le_div_of_nonneg_right (h2.trans h1) (by positivity)).trans ?_
                        rw [Finset.sum_div]
                        refine Finset.sum_le_sum fun a _ => ?_
                        rw [hx, hx]
                        exact hdist _ _
                      unfold PigeonholeDesign.Upper.phdExp
                      rw [le_div_iff₀ (by positivity)]
                      refine le_trans ?_ (Finset.sum_le_sum fun coin _ => hdisc coin)
                      rw [← Finset.sum_div, Finset.sum_comm, div_mul_eq_mul_div, div_mul_eq_mul_div]
                      refine div_le_div_of_nonneg_right ?_ (by positivity)
                      have h3 : ∀ j ∈ J, 2 ^ T * (1 / 4 * Real.sqrt n) ≤ ∑ coin : Fin T → Bool, |∑ a ∈ A j, sg (PigeonholeDesign.Upper.coinOf coin a)| := by
                        intro j hj
                        refine le_trans ?_ (khin T (A j) (hA j hj).1)
                        have h4 : Real.sqrt n ≤ Real.sqrt (A j).card := Real.sqrt_le_sqrt (by exact_mod_cast (hA j hj).2.1)
                        have h5 : (0:ℝ) < 2 ^ T := by positivity
                        have h7 := mul_le_mul_of_nonneg_left h4 h5.le
                        linarith
                      have h6 := Finset.sum_le_sum h3
                      rw [Finset.sum_const, nsmul_eq_mul] at h6
                      linarith
                clear expG matchLow khin
                refine ⟨1 / 64, by norm_num, 64, ?_⟩
                intro T hT64 hT K hole
                obtain ⟨m, hm⟩ : ∃ m : ℕ, m = Nat.sqrt T := ⟨_, rfl⟩
                have hmle : m * m ≤ T := by rw [hm]; exact Nat.sqrt_le T
                have hmlt : T < (m + 1) * (m + 1) := by rw [hm]; exact Nat.lt_succ_sqrt T
                have hm8 : 8 ≤ m := by
                  rw [hm, Nat.le_sqrt]; omega
                have hmT2 : m ≤ T / 2 := by
                  have : 8 * m ≤ m * m := Nat.mul_le_mul_right _ hm8
                  omega
                have hmR : (8:ℝ) ≤ m := by exact_mod_cast hm8
                have hTR : (0:ℝ) < T := by
                  have : 0 < T := by omega
                  exact_mod_cast this
                obtain ⟨r, hr⟩ : ∃ r : ℝ, r = (T : ℝ) ^ ((1 : ℝ) / 4) := ⟨_, rfl⟩
                have hr4 : (T : ℝ) = r ^ 4 := by
                  rw [hr, ← Real.rpow_natCast, ← Real.rpow_mul hTR.le]; norm_num
                have hr0 : 0 < r := by rw [hr]; positivity
                have hrm : r ^ 2 ≤ 2 * m := by
                  apply sqm m r hmR
                  rw [← hr4]
                  exact_mod_cast hmlt
                rw [← hr]
                have hm0 : 0 < m := by omega
                have numeric : ∀ (J : Finset ℕ) (n : ℕ), (m : ℝ) / 2 ≤ J.card → (m : ℝ) / 8 ≤ n →
                    1 / 64 * r ≤ (J.card : ℝ) / (2 * m) * (1 / 4 * Real.sqrt n) :=
                  fun J n h1 h2 => numeric0 m r J.card n 0 hmR hr0 hrm h1 h2
                clear numeric0 sqm
                obtain ⟨E, hEdef⟩ : ∃ E : Finset ℕ, E = (Finset.range m).filter (fun j => ∀ i, j < i → i < m → hole (pt m i) ≠ hole (pt m j)) := ⟨_, rfl⟩
                have hEinj : ∀ a ∈ E, ∀ b ∈ E, hole (pt m a) = hole (pt m b) → a = b := by
                  intro a ha b hb h
                  rw [hEdef, Finset.mem_filter, Finset.mem_range] at ha hb
                  rcases lt_trichotomy a b with h1 | h1 | h1
                  · exact absurd h.symm (ha.2 b h1 hb.1)
                  · exact h1
                  · exact absurd h (hb.2 a h1 ha.1)
                have hEm : ∀ a ∈ E, a < m := by
                  intro a ha
                  rw [hEdef, Finset.mem_filter, Finset.mem_range] at ha
                  exact ha.1
                have hEcard : E.card ≤ m := by
                  rw [hEdef]
                  exact (Finset.card_filter_le _ _).trans (by simp)
                by_cases hcase : m ≤ 2 * E.card
                · -- many cells
                  obtain ⟨σ, hσE, hσinj⟩ : ∃ σ : ℕ → ℕ, (∀ n < E.card, σ n ∈ E) ∧
                      (∀ a < E.card, ∀ b < E.card, σ a = σ b → a = b) := by
                    refine ⟨fun n => if h : n < E.card then (E.equivFin.symm ⟨n, h⟩ : ℕ) else 0, ?_, ?_⟩
                    · intro n hn
                      simp only [dif_pos hn]
                      exact (E.equivFin.symm ⟨n, hn⟩).2
                    · intro a ha b hb h
                      simp only [dif_pos ha, dif_pos hb] at h
                      have := E.equivFin.symm.injective (Subtype.ext h)
                      exact congrArg Fin.val this
                  obtain ⟨g, hg⟩ : ∃ g : ℕ → ℕ, g = fun n => if n < E.card then σ n else 2 * m := ⟨_, rfl⟩
                  have hg1 : ∀ n < E.card, g n = σ n := by intro n hn; rw [hg]; simp [hn]
                  have hg2 : ∀ n, ¬ n < E.card → g n = 2 * m := by intro n hn; rw [hg]; simp [hn]
                  obtain ⟨x, hx, w, hw, hlow⟩ := lowgen K hole T m g hT hm0 (by
                    intro n
                    by_cases h : n < E.card
                    · rw [hg1 n h]; have := hEm _ (hσE n h); omega
                    · rw [hg2 n h])
                  refine ⟨x, hx, ?_⟩
                  have hwc : ∀ coin, ∀ n < E.card, w coin n = PigeonholeDesign.Upper.coinOf coin n := by
                    intro coin n hn
                    refine (hw coin n (by omega)).1 (Finset.sum_eq_zero fun t ht' => ?_)
                    have htn := Finset.mem_range.1 ht'
                    rw [if_neg]
                    intro h
                    rw [hg1 t (by omega), hg1 n hn] at h
                    have h2 := hσinj t (by omega) n hn (hEinj _ (hσE t (by omega)) _ (hσE n hn) h)
                    omega
                  refine (numeric (Finset.Ico m (2 * m)) E.card ?_ ?_).trans (hlow (Finset.Ico m (2 * m)) E.card (fun _ => Finset.range E.card) ?_ ?_)
                  · rw [Nat.card_Ico]
                    have : 2 * m - m = m := by omega
                    rw [this]; linarith only [hmR]
                  · have : (m : ℝ) ≤ 2 * E.card := by exact_mod_cast hcase
                    linarith only [this, hmR]
                  · intro j hj
                    rw [Finset.mem_Ico] at hj
                    exact Finset.mem_range.2 hj.2
                  · intro j hj
                    rw [Finset.mem_Ico] at hj
                    refine ⟨fun a ha => by have := Finset.mem_range.1 ha; omega, by simp, fun coin => ?_⟩
                    have hsub : Finset.range E.card ⊆ Finset.range T := Finset.range_subset_range.2 (by omega)
                    rw [← Finset.sum_subset hsub]
                    · refine Finset.sum_congr rfl fun t ht' => ?_
                      have htn := Finset.mem_range.1 ht'
                      have h1 := hEm _ (hσE t htn)
                      rw [hg1 t htn, if_pos (by omega), one_mul, hwc coin t htn]
                    · intro t _ ht'
                      rw [Finset.mem_range] at ht'
                      rw [hg2 t ht', if_neg (by omega), zero_mul]
                · -- few cells
                  obtain ⟨L, hL⟩ : ∃ L : ℕ → ℕ, ∀ i < m, i ≤ L i ∧ L i < m ∧ hole (pt m (L i)) = hole (pt m i) ∧ (i ∉ E → i < L i) := by
                    have : ∀ i, ∃ l, i < m → i ≤ l ∧ l < m ∧ hole (pt m l) = hole (pt m i) ∧ (i ∉ E → i < l) := by
                      intro i
                      by_cases hi : i < m
                      · by_cases hiE : i ∈ E
                        · exact ⟨i, fun _ => ⟨le_rfl, hi, rfl, fun h => absurd hiE h⟩⟩
                        · have h := hiE
                          rw [hEdef, Finset.mem_filter, Finset.mem_range] at h
                          push Not at h
                          obtain ⟨l, h1, h2, h3⟩ := h hi
                          exact ⟨l, fun _ => ⟨h1.le, h2, h3, fun _ => h1⟩⟩
                      · exact ⟨0, fun h => absurd h hi⟩
                    choose L hL using this
                    exact ⟨L, hL⟩
                  obtain ⟨H, hH⟩ : ∃ H : ℕ, H = T / 4 := ⟨_, rfl⟩
                  have hH2 : 2 * H ≤ T / 2 := by omega
                  obtain ⟨g, hg⟩ : ∃ g : ℕ → ℕ, g = fun n => if n < 2 * H then (if n % 2 = 0 then (n / 2) % m else L ((n / 2) % m)) else 2 * m := ⟨_, rfl⟩
                  have hmod : ∀ s, s % m < m := fun s => Nat.mod_lt _ hm0
                  have hg0 : ∀ s < H, g (2 * s) = s % m := by
                    intro s hs
                    rw [hg]
                    simp only
                    rw [if_pos (by omega), if_pos (by omega), show 2 * s / 2 = s by omega]
                  have hg1 : ∀ s < H, g (2 * s + 1) = L (s % m) := by
                    intro s hs
                    rw [hg]
                    simp only
                    rw [if_pos (by omega), if_neg (by omega), show (2 * s + 1) / 2 = s by omega]
                  have hg2 : ∀ n, ¬ n < 2 * H → g n = 2 * m := by
                    intro n hn
                    rw [hg]
                    simp only
                    rw [if_neg hn]
                  obtain ⟨x, hx, w, hw, hlow⟩ := lowgen K hole T m g hT hm0 (by
                    intro n
                    by_cases h : n < 2 * H
                    · rcases Nat.even_or_odd' n with ⟨s, rfl | rfl⟩
                      · rw [hg0 s (by omega)]; have := hmod s; omega
                      · rw [hg1 s (by omega)]; have := (hL _ (hmod s)).2.1; omega
                    · rw [hg2 n h])
                  refine ⟨x, hx, ?_⟩
                  have hstep : ∀ coin, ∀ s < H, (∀ k, ∑ t ∈ Finset.range (2 * s), (if hole (pt m (g t)) = k then sg (w coin t) else 0) = 0) →
                      w coin (2 * s) = PigeonholeDesign.Upper.coinOf coin (2 * s) ∧
                      sg (w coin (2 * s + 1)) = - sg (PigeonholeDesign.Upper.coinOf coin (2 * s)) := by
                    clear numeric
                    as_aux_lemma =>
                      intro coin s hs hz
                      have h1 := (hw coin (2 * s) (by omega)).1 (hz _)
                      refine ⟨h1, ?_⟩
                      obtain ⟨-, r2, r3⟩ := hw coin (2 * s + 1) (by omega)
                      have hsame : hole (pt m (g (2 * s))) = hole (pt m (g (2 * s + 1))) := by
                        rw [hg0 s hs, hg1 s hs]; exact (hL _ (hmod s)).2.2.1.symm
                      rw [Finset.sum_range_succ, hz, if_pos hsame, zero_add, h1] at r2 r3
                      cases hc : PigeonholeDesign.Upper.coinOf coin (2 * s)
                      · rw [hc, hf] at r3
                        rw [r3 (by norm_num), ht, hf]; norm_num
                      · rw [hc, ht] at r2
                        rw [r2 (by norm_num), ht, hf]
                  have hbal : ∀ coin, ∀ s ≤ H, ∀ k, ∑ t ∈ Finset.range (2 * s), (if hole (pt m (g t)) = k then sg (w coin t) else 0) = 0 := by
                    clear numeric
                    as_aux_lemma =>
                      intro coin s
                      induction s with
                      | zero => intro _ k; simp
                      | succ s ih =>
                        intro hs k
                        have i1 := ih (by omega)
                        obtain ⟨h1, h2⟩ := hstep coin s (by omega) i1
                        rw [show 2 * (s + 1) = 2 * s + 1 + 1 by ring, Finset.sum_range_succ, Finset.sum_range_succ, i1 k]
                        have hsame : hole (pt m (g (2 * s))) = hole (pt m (g (2 * s + 1))) := by
                          rw [hg0 s (by omega), hg1 s (by omega)]; exact (hL _ (hmod s)).2.2.1.symm
                        rw [← hsame, h1, h2]
                        split_ifs <;> ring
                  have hpair : ∀ coin, ∀ s < H, w coin (2 * s) = PigeonholeDesign.Upper.coinOf coin (2 * s) ∧
                      sg (w coin (2 * s + 1)) = - sg (PigeonholeDesign.Upper.coinOf coin (2 * s)) :=
                    fun coin s hs => hstep coin s hs (hbal coin s hs.le)
                  have hsum2 : ∀ (φ : ℕ → ℝ) (n : ℕ), ∑ t ∈ Finset.range (2 * n), φ t = ∑ s ∈ Finset.range n, (φ (2 * s) + φ (2 * s + 1)) := by
                    intro φ n
                    induction n with
                    | zero => simp
                    | succ n ih =>
                      rw [show 2 * (n + 1) = 2 * n + 1 + 1 by ring, Finset.sum_range_succ, Finset.sum_range_succ, ih, Finset.sum_range_succ]
                      ring
                  have hJsub : ∀ j ∈ Finset.range m \ E, j < m ∧ j ∉ E := by
                    intro j hj
                    rw [Finset.mem_sdiff, Finset.mem_range] at hj
                    exact hj
                  refine (numeric (Finset.range m \ E) (H / m) ?_ ?_).trans (hlow (Finset.range m \ E) (H / m)
                    (fun j => ((Finset.range H).filter (fun s => s % m ≤ j ∧ j < L (s % m))).image (fun s => 2 * s)) ?_ ?_)
                  · have h1 := Finset.le_card_sdiff E (Finset.range m)
                    rw [Finset.card_range] at h1
                    have h2 : m ≤ 2 * (Finset.range m \ E).card := by omega
                    have h3 : (m : ℝ) ≤ 2 * ((Finset.range m \ E).card : ℝ) := by exact_mod_cast h2
                    linarith only [h3]
                  · have h1 : m / 4 ≤ H / m := by
                      rw [Nat.le_div_iff_mul_le hm0, hH, Nat.le_div_iff_mul_le (by norm_num)]
                      have h2 : m / 4 * 4 ≤ m := Nat.div_mul_le_self m 4
                      calc m / 4 * m * 4 = (m / 4 * 4) * m := by ring
                        _ ≤ m * m := Nat.mul_le_mul_right _ h2
                        _ ≤ T := hmle
                    have h2 : m ≤ 8 * (H / m) := by omega
                    have h3 : (m : ℝ) ≤ 8 * ((H / m : ℕ) : ℝ) := by exact_mod_cast h2
                    linarith only [h3]
                  · intro j hj
                    have := (hJsub j hj).1
                    rw [Finset.mem_range]; omega
                  · intro j hj
                    obtain ⟨hjm, hjE⟩ := hJsub j hj
                    refine ⟨?_, ?_, fun coin => ?_⟩
                    · intro a ha
                      obtain ⟨s, hs, rfl⟩ := Finset.mem_image.1 ha
                      have := Finset.mem_range.1 (Finset.mem_filter.1 hs).1
                      omega
                    · rw [Finset.card_image_of_injective _ (fun a b h => by simpa using h)]
                      have h1 := Finset.card_le_card_of_injOn (s := Finset.range (H / m))
                        (t := (Finset.range H).filter (fun s => s % m ≤ j ∧ j < L (s % m))) (fun k => j + m * k) (by
                          intro k hk
                          have hk := Finset.mem_range.1 (Finset.mem_coe.1 hk)
                          have h2 : (j + m * k) % m = j := by
                            rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hjm]
                          rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_range, h2]
                          refine ⟨?_, le_rfl, (hL j hjm).2.2.2 hjE⟩
                          have h3 : m * (k + 1) ≤ m * (H / m) := Nat.mul_le_mul_left _ hk
                          have h4 : m * (H / m) ≤ H := Nat.mul_div_le H m
                          have h5 : m * (k + 1) = m * k + m := by ring
                          show j + m * k < H
                          rw [h5] at h3
                          exact lt_of_lt_of_le (by rw [add_comm]; exact Nat.add_lt_add_left hjm _) (h3.trans h4)) (by
                          intro a _ b _ h
                          have h2 : m * a = m * b := by simpa using h
                          exact Nat.eq_of_mul_eq_mul_left hm0 h2)
                      rwa [Finset.card_range] at h1
                    · have hsub : Finset.range (2 * H) ⊆ Finset.range T := Finset.range_subset_range.2 (by omega)
                      rw [← Finset.sum_subset hsub]
                      · rw [hsum2, Finset.sum_image (fun a _ b _ h => by simpa using h), Finset.sum_filter]
                        refine Finset.sum_congr rfl fun s hs => ?_
                        have hs := Finset.mem_range.1 hs
                        obtain ⟨h1, h2⟩ := hpair coin s hs
                        have h3 := (hL _ (hmod s)).1
                        rw [hg0 s hs, hg1 s hs, h1, h2]
                        by_cases c1 : s % m ≤ j
                        · by_cases c2 : L (s % m) ≤ j
                          · rw [if_pos c1, if_pos c2, if_neg (by omega)]; ring
                          · rw [if_pos c1, if_neg c2, if_pos (by omega)]; ring
                        · rw [if_neg c1, if_neg (by omega), if_neg (by omega)]; ring
                      · intro t _ ht'
                        rw [Finset.mem_range] at ht'
                        rw [hg2 t ht', if_neg (by omega), zero_mul]
            exact ⟨upper, lower⟩
