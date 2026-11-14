-- Prove2me | solution 1 for RvsCert.lemma_4_hard_input
-- status  : ACCEPTED   (prove)
-- author  : @Robin Kothari
-- created : 2026-11-13T21:18:03.516207+00:00
-- url     : https://prove2.me/submissions/f1d4c92b-4d0b-4d91-8b26-461ba8f50501

import Definitions.Def_RvsCert_champion
import Definitions.Def_RvsCert_IsCertificate

open RvsCert

namespace RvsCertHard


theorem bitsVal_testBit : ∀ (w N : ℕ), N < 2 ^ w → bitsVal (fun t : Fin w => N.testBit t) = N
  | 0, N, h => by simp [bitsVal]; omega
  | w + 1, N, h => by
    have ih := bitsVal_testBit w (N / 2) (by rw [pow_succ] at h; omega)
    unfold bitsVal at ih ⊢
    rw [Fin.sum_univ_succ]
    simp only [Fin.val_zero, pow_zero, Fin.val_succ]
    have hs : ∀ t : Fin w, N.testBit ((t : ℕ) + 1) = (N / 2).testBit t := fun t =>
      Nat.testBit_succ N t
    simp only [hs]
    have : ∑ t : Fin w, (if (N / 2).testBit t then 2 ^ ((t : ℕ) + 1) else 0) =
        2 * ∑ t : Fin w, (if (N / 2).testBit t then 2 ^ (t : ℕ) else 0) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun t _ => ?_
      split_ifs <;> ring
    rw [this, ih, Nat.testBit_zero]
    have := Nat.mod_add_div N 2
    rcases Nat.mod_two_eq_zero_or_one N with h2 | h2 <;> simp [h2] <;> omega

theorem bitsVal_false (w : ℕ) : bitsVal (fun _ : Fin w => false) = 0 := by
  simp [bitsVal]


theorem raceOf_val {n : ℕ} (c : Fin (2 * n)) (j : Fin (2 * n - 1)) :
    (raceOf c j).1 = if (j : ℕ) < c then (opponent c j, c) else (c, opponent c j) := by
  unfold raceOf
  split_ifs <;> rfl

theorem raceOf_inj {n : ℕ} (c : Fin (2 * n)) (j j' : Fin (2 * n - 1))
    (h : raceOf c j = raceOf c j') : j = j' := by
  have h' := congrArg Subtype.val h
  rw [raceOf_val, raceOf_val] at h'
  apply Fin.ext
  split_ifs at h' with h1 h2 h2 <;>
    simp only [Prod.mk.injEq, Fin.ext_iff, opponent] at h' <;> split_ifs at h' <;> omega

theorem not_champion_false (n : ℕ) (hn : 0 < n) : champion n (fun _ => false) = false := by
  unfold champion
  simp only [decide_eq_false_iff_not, not_exists]
  intro a ha
  obtain ⟨-, -, h3⟩ := ha
  obtain ⟨hp, hq⟩ := h3 ⟨0, by omega⟩
  have := (hq ⟨_, hp⟩).2 rfl
  simp only [raceEntry, bitsVal_false] at this
  unfold athleteCode at this
  omega

/-- Whether bit `s` is a race bit of a race involving country `c`. -/
def involves {n : ℕ} (s : Idx n) (c : Fin (2 * n)) : Bool :=
  match s with
  | .inl z => decide (z.1.1.1 = c ∨ z.1.1.2 = c)
  | .inr _ => false

/-- The race bits of `S` in races involving country `c`. -/
def raceBitsAt {n : ℕ} (S : Finset (Idx n)) (c : Fin (2 * n)) : Finset (Idx n) :=
  S.filter fun s => involves s c = true

theorem sum_raceBitsAt_le {n : ℕ} (S : Finset (Idx n)) :
    ∑ c : Fin (2 * n), (raceBitsAt S c).card ≤ 2 * S.card := by
  unfold raceBitsAt
  simp only [Finset.card_filter]
  rw [Finset.sum_comm, Finset.card_eq_sum_ones, Finset.mul_sum]
  refine Finset.sum_le_sum fun s _ => ?_
  rcases s with z | z
  · simp only [involves, decide_eq_true_eq, mul_one]
    calc (∑ c : Fin (2 * n), if z.1.1.1 = c ∨ z.1.1.2 = c then 1 else 0)
        = (Finset.univ.filter fun c : Fin (2 * n) => z.1.1.1 = c ∨ z.1.1.2 = c).card := by
          rw [Finset.card_filter]
      _ ≤ ({z.1.1.1, z.1.1.2} : Finset (Fin (2 * n))).card := by
          apply Finset.card_le_card
          intro c hc
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc
          rcases hc with hc | hc <;> simp [hc]
      _ ≤ 2 := Finset.card_le_two
  · simp [involves]

end RvsCertHard

open RvsCertHard in
theorem solution (n : ℕ) (hn : 0 < n) :
    champion n (fun _ => false) = false ∧
    ∀ S : Finset (Idx n), IsCertificate (champion n) (fun _ => false) S →
      (n : ℝ) ^ 2 / 2 < S.card := by
  refine ⟨not_champion_false n hn, fun S hS => ?_⟩
  by_contra hcon
  have hS2 : 2 * S.card ≤ n ^ 2 := by
    have : (S.card : ℝ) ≤ (n : ℝ) ^ 2 / 2 := not_lt.mp hcon
    have : (2 * S.card : ℝ) ≤ (n : ℝ) ^ 2 := by linarith
    exact_mod_cast this
  classical
  -- athletes whose proposal card is touched by `S`
  let proj : Idx n → Fin (2 * n) × Fin n :=
    Sum.elim (fun _ => (⟨0, by omega⟩, ⟨0, hn⟩)) (fun z => z.1)
  let B1 : Finset (Fin (2 * n) × Fin n) :=
    (S.filter fun s => s.isRight = true).image proj
  have hB1 : B1.card ≤ S.card :=
    (Finset.card_image_le).trans (Finset.card_filter_le _ _)
  -- athletes from countries with at least `n` revealed race bits
  let badC : Finset (Fin (2 * n)) := Finset.univ.filter fun c => n ≤ (raceBitsAt S c).card
  let B2 : Finset (Fin (2 * n) × Fin n) := badC ×ˢ Finset.univ
  have hbadC : badC.card * n ≤ 2 * S.card := by
    calc badC.card * n = ∑ c ∈ badC, n := by rw [Finset.sum_const, smul_eq_mul]
      _ ≤ ∑ c ∈ badC, (raceBitsAt S c).card :=
          Finset.sum_le_sum fun c hc => (Finset.mem_filter.1 hc).2
      _ ≤ ∑ c : Fin (2 * n), (raceBitsAt S c).card :=
          Finset.sum_le_sum_of_subset (Finset.subset_univ _)
      _ ≤ 2 * S.card := sum_raceBitsAt_le S
  have hB2 : B2.card ≤ 2 * S.card := by
    simp only [B2, Finset.card_product, Finset.card_univ, Fintype.card_fin]
    exact hbadC
  -- a good athlete exists
  obtain ⟨a, ha⟩ : ∃ a : Fin (2 * n) × Fin n, a ∉ B1 ∪ B2 := by
    by_contra hall
    push Not at hall
    have hsub : (Finset.univ : Finset (Fin (2 * n) × Fin n)) ⊆ B1 ∪ B2 := fun a _ => hall a
    have h1 := Finset.card_le_card hsub
    have h2 := Finset.card_union_le B1 B2
    simp only [Finset.card_univ, Fintype.card_prod, Fintype.card_fin] at h1
    nlinarith
  rw [Finset.mem_union, not_or] at ha
  obtain ⟨haB1, haB2⟩ := ha
  have hcard_untouched : ∀ j t, Sum.inr (a, j, t) ∉ S := by
    intro j t hmem
    apply haB1
    exact Finset.mem_image.2 ⟨Sum.inr (a, j, t), Finset.mem_filter.2 ⟨hmem, rfl⟩, rfl⟩
  have hZ : (raceBitsAt S a.1).card < n := by
    by_contra h
    exact haB2 (Finset.mem_product.2 ⟨Finset.mem_filter.2 ⟨Finset.mem_univ _, by omega⟩,
      Finset.mem_univ _⟩)
  set c := a.1 with hc
  -- touched positions in the `j`-th race of `c`
  let T : Fin (2 * n - 1) → Finset (Fin n) := fun j =>
    Finset.univ.filter fun p => ∃ t, (Sum.inl (raceOf c j, p, t) : Idx n) ∈ S
  have hT : ∑ j, (T j).card ≤ (raceBitsAt S c).card := by
    rw [← Finset.card_sigma]
    let g : (Σ _ : Fin (2 * n - 1), Fin n) → Idx n := fun jp =>
      if h : ∃ t, (Sum.inl (raceOf c jp.1, jp.2, t) : Idx n) ∈ S then
        Sum.inl (raceOf c jp.1, jp.2, h.choose) else Sum.inr (a, ⟨0, by omega⟩, ⟨0, by
          unfold wY; omega⟩)
    refine Finset.card_le_card_of_injOn g ?_ ?_
    · intro jp hjp
      have hjp' : ∃ t, (Sum.inl (raceOf c jp.1, jp.2, t) : Idx n) ∈ S := by
        have := Finset.mem_sigma.1 hjp
        exact (Finset.mem_filter.1 this.2).2
      simp only [g, dif_pos hjp']
      refine Finset.mem_filter.2 ⟨hjp'.choose_spec, ?_⟩
      simp only [involves, decide_eq_true_eq]
      rw [raceOf_val]
      split_ifs <;> simp
    · intro jp hjp jp' hjp' heq
      have h1 : ∃ t, (Sum.inl (raceOf c jp.1, jp.2, t) : Idx n) ∈ S :=
        (Finset.mem_filter.1 (Finset.mem_sigma.1 hjp).2).2
      have h2 : ∃ t, (Sum.inl (raceOf c jp'.1, jp'.2, t) : Idx n) ∈ S :=
        (Finset.mem_filter.1 (Finset.mem_sigma.1 hjp').2).2
      simp only [g, dif_pos h1, dif_pos h2, Sum.inl.injEq, Prod.mk.injEq] at heq
      obtain ⟨hr, hp, -⟩ := heq
      have hj := raceOf_inj c _ _ hr
      obtain ⟨j, p⟩ := jp
      obtain ⟨j', p'⟩ := jp'
      simp only at hj hp
      subst hj
      subst hp
      rfl
  -- every race of `c` has an untouched position
  have hex : ∀ j : Fin (2 * n - 1),
      ∃ p : ℕ, ∃ hp : p < n, ∀ t, (Sum.inl (raceOf c j, ⟨p, hp⟩, t) : Idx n) ∉ S := by
    intro j
    by_contra hno
    push Not at hno
    have hfull : T j = Finset.univ := by
      ext p
      simp only [T, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
      exact hno p p.2
    have : n ≤ ∑ j, (T j).card := by
      calc n = (T j).card := by rw [hfull, Finset.card_univ, Fintype.card_fin]
        _ ≤ ∑ j, (T j).card := Finset.single_le_sum (f := fun j => (T j).card) (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
    omega
  let q : Fin (2 * n - 1) → ℕ := fun j => Nat.find (hex j)
  have hq_lt : ∀ j, q j < n := fun j => (Nat.find_spec (hex j)).1
  have hq_untouched : ∀ j t, (Sum.inl (raceOf c j, ⟨q j, hq_lt j⟩, t) : Idx n) ∉ S :=
    fun j => (Nat.find_spec (hex j)).2
  have hq_le : ∀ j, q j ≤ (T j).card := by
    intro j
    have hsub : (Finset.univ.filter fun p : Fin n => (p : ℕ) < q j) ⊆ T j := by
      intro p hp
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
      simp only [T, Finset.mem_filter, Finset.mem_univ, true_and]
      have hmin := Nat.find_min (hex j) hp
      push Not at hmin
      exact hmin p.2
    have hcardp : (Finset.univ.filter fun p : Fin n => (p : ℕ) < q j).card = q j := by
      have : (Finset.univ.filter fun p : Fin n => (p : ℕ) < q j) =
          (Finset.range (q j)).attachFin (fun m hm => by
            have := Finset.mem_range.1 hm; have := hq_lt j; omega) := by
        ext p; simp
      rw [this, Finset.card_attachFin, Finset.card_range]
    rw [← hcardp]
    exact Finset.card_le_card hsub
  have hsumq : ∑ j, q j < n :=
    lt_of_le_of_lt ((Finset.sum_le_sum fun j _ => hq_le j).trans hT) hZ
  -- running totals of the card
  let qN : ℕ → ℕ := fun i => if h : i < 2 * n - 1 then q ⟨i, h⟩ else 0
  let Y : ℕ → ℕ := fun j => ∑ i ∈ Finset.range (j + 1), qN i
  have hY_le : ∀ j, Y j ≤ ∑ j, q j := by
    intro j
    calc Y j = ∑ i ∈ Finset.range (j + 1), qN i := rfl
      _ ≤ ∑ i ∈ Finset.range (2 * n - 1), qN i := by
          by_cases hj : j + 1 ≤ 2 * n - 1
          · exact Finset.sum_le_sum_of_subset (Finset.range_subset_range.2 hj)
          · rw [← Finset.sum_range_add_sum_Ico _ (show 2 * n - 1 ≤ j + 1 by omega)]
            have : ∑ i ∈ Finset.Ico (2 * n - 1) (j + 1), qN i = 0 :=
              Finset.sum_eq_zero fun i hi => by
                simp only [Finset.mem_Ico] at hi
                simp only [qN]
                rw [dif_neg (by omega)]
            omega
      _ = ∑ j, q j := by
          rw [← Fin.sum_univ_eq_sum_range qN]
          refine Finset.sum_congr rfl fun i _ => ?_
          simp [qN]
  have hY_lt : ∀ j, Y j < n := fun j => lt_of_le_of_lt (hY_le j) hsumq
  have hn_lt : n < 2 ^ wY n := by unfold wY; exact Nat.lt_pow_succ_log_self (by norm_num) n
  have hcode : athleteCode n a < 2 ^ wX n := by
    have h1 : 2 * n ^ 2 + 1 ≤ 2 ^ wX n := Nat.le_pow_clog (by norm_num) _
    have h2 : athleteCode n a ≤ 2 * n ^ 2 := by
      unfold athleteCode
      have := a.1.isLt; have := a.2.isLt
      nlinarith
    omega
  -- the modified input
  let y : Idx n → Bool := Sum.elim
    (fun z => decide (∃ j, z.1 = raceOf c j ∧ (z.2.1 : ℕ) = q j ∧
      (athleteCode n a).testBit z.2.2))
    (fun z => decide (z.1 = a ∧ (Y z.2.1).testBit z.2.2))
  have hagree : ∀ s ∈ S, y s = (fun _ => false) s := by
    intro s hs
    rcases s with z | z
    · simp only [y, Sum.elim_inl, decide_eq_false_iff_not, not_exists, not_and]
      intro j hr hp _
      obtain ⟨r, p, t⟩ := z
      simp only at hr hp
      subst hr
      have : p = ⟨q j, hq_lt j⟩ := Fin.ext hp
      subst this
      exact hq_untouched j t hs
    · simp only [y, Sum.elim_inr, decide_eq_false_iff_not, not_and]
      intro ha'
      obtain ⟨a', j, t⟩ := z
      simp only at ha'
      subst ha'
      exact absurd hs (hcard_untouched j t)
  have hcardE : ∀ j : Fin (2 * n - 1), cardEntry n y a j = Y j := by
    intro j
    unfold cardEntry
    simp only [y, Sum.elim_inr, true_and, decide_eq_true_eq]
    simp only [decide_eq_true_eq] at *
    have := bitsVal_testBit (wY n) (Y j) (lt_trans (hY_lt j) hn_lt)
    convert this using 2
    simp
  have hraceE : ∀ (j : Fin (2 * n - 1)) (p : Fin n),
      raceEntry n y (raceOf c j) p = if (p : ℕ) = q j then athleteCode n a else 0 := by
    intro j p
    unfold raceEntry
    split_ifs with hp
    · rw [← bitsVal_testBit (wX n) (athleteCode n a) hcode]
      congr 1
      funext t
      simp only [y, Sum.elim_inl]
      by_cases ht : (athleteCode n a).testBit t = true
      · exact (decide_eq_true ⟨j, rfl, hp, ht⟩).trans ht.symm
      · rw [Bool.not_eq_true] at ht
        exact (decide_eq_false fun ⟨_, _, _, h⟩ => by rw [ht] at h; exact Bool.noConfusion h).trans
          ht.symm
    · rw [← bitsVal_false (wX n)]
      congr 1
      funext t
      simp only [y, Sum.elim_inl, decide_eq_false_iff_not, not_exists, not_and]
      intro j' hr hp' _
      have := raceOf_inj c _ _ hr
      subst this
      exact hp hp'
  have hchamp : IsChampion n y a := by
    refine ⟨?_, ?_, ?_⟩
    · intro j j' hjj'
      rw [hcardE, hcardE]
      exact Finset.sum_le_sum_of_subset (Finset.range_subset_range.2 (by
        have := Fin.le_def.1 hjj'; omega))
    · intro j _
      rw [hcardE]
      exact hY_lt j
    · intro j
      have hpos : claimedPos n y a j = q j := by
        unfold claimedPos
        rw [hcardE]
        by_cases h0 : (j : ℕ) = 0
        · rw [dif_pos h0]
          simp only [Y, h0, zero_add, Finset.sum_range_one, qN]
          rw [dif_pos (by omega)]
          exact congrArg q (Fin.ext h0.symm)
        · rw [dif_neg h0, hcardE]
          simp only [Y]
          have : (j : ℕ) + 1 = ((j : ℕ) - 1 + 1) + 1 := by omega
          rw [this, Finset.sum_range_succ]
          simp only [qN]
          rw [dif_pos (by omega)]
          have hj : (⟨(j : ℕ) - 1 + 1, by omega⟩ : Fin (2 * n - 1)) = j := Fin.ext (by simp; omega)
          rw [hj]
          omega
      refine ⟨by rw [hpos]; exact hq_lt j, fun p => ⟨fun hlt => ?_, fun heq => ?_⟩⟩
      · rw [← hc, hraceE, if_neg (by rw [hpos] at hlt; omega)]
      · rw [← hc, hraceE, if_pos (by rw [hpos] at heq; exact heq)]
  have hy : champion n y = true := by
    unfold champion
    exact decide_eq_true ⟨a, hchamp⟩
  have := hS y hagree
  rw [hy, not_champion_false n hn] at this
  exact Bool.noConfusion this
