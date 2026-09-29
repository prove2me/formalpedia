-- Prove2me | solution 1 for PLCMarkets.Rationality.isEquilibrium_iff_maxFlow
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T03:07:06.820843+00:00
-- url     : https://prove2.me/submissions/5116e232-5e78-415e-8a64-30093597eee0

import Mathlib
import Definitions.Def_PLCMarkets_Rationality_EquilibriumNetwork

namespace PLCMarkets.Rationality

noncomputable def aux_plc_F (L : List (ℚ × ℚ)) (t : ℚ) (x : ℝ) : ℝ :=
  plEval L x + (t : ℝ) * max (x - (((L.map Prod.snd).sum : ℚ) : ℝ)) 0

noncomputable def aux_plc_A (L : List (ℚ × ℚ)) (c : ℝ) : ℝ :=
  (L.map (fun s => if c < (s.1 : ℝ) then (s.2 : ℝ) else 0)).sum

noncomputable def aux_plc_B (L : List (ℚ × ℚ)) (c : ℝ) : ℝ :=
  (L.map (fun s => if c ≤ (s.1 : ℝ) then (s.2 : ℝ) else 0)).sum

noncomputable def aux_plc_C (L : List (ℚ × ℚ)) (c : ℝ) : ℝ :=
  (L.map (fun s => if (s.1 : ℝ) = c then (s.2 : ℝ) else 0)).sum

theorem aux_plc_B_eq (c : ℝ) : ∀ L : List (ℚ × ℚ), aux_plc_B L c = aux_plc_A L c + aux_plc_C L c
  | [] => by simp [aux_plc_A, aux_plc_B, aux_plc_C]
  | s :: L => by
    have ih := aux_plc_B_eq c L
    simp only [aux_plc_A, aux_plc_B, aux_plc_C, List.map_cons, List.sum_cons] at ih ⊢
    rw [ih]
    rcases lt_trichotomy (s.1 : ℝ) c with h | h | h
    · simp [not_le.2 h, not_lt.2 h.le, h.ne]
    · simp [h]; ring
    · simp [h.le, h, h.ne']; ring

theorem aux_plc_A_nonneg (c : ℝ) : ∀ L : List (ℚ × ℚ), (∀ s ∈ L, 0 < s.2) → 0 ≤ aux_plc_A L c
  | [] => by simp [aux_plc_A]
  | s :: L => by
    intro h
    have ih := aux_plc_A_nonneg c L (fun u hu => h u (List.mem_cons_of_mem _ hu))
    have hs : (0 : ℝ) < s.2 := by exact_mod_cast h s (List.mem_cons_self)
    simp only [aux_plc_A, List.map_cons, List.sum_cons] at ih ⊢
    split_ifs <;> linarith

theorem aux_plc_C_nonneg (c : ℝ) : ∀ L : List (ℚ × ℚ), (∀ s ∈ L, 0 < s.2) → 0 ≤ aux_plc_C L c
  | [] => by simp [aux_plc_C]
  | s :: L => by
    intro h
    have ih := aux_plc_C_nonneg c L (fun u hu => h u (List.mem_cons_of_mem _ hu))
    have hs : (0 : ℝ) < s.2 := by exact_mod_cast h s (List.mem_cons_self)
    simp only [aux_plc_C, List.map_cons, List.sum_cons] at ih ⊢
    split_ifs <;> linarith

theorem aux_plc_A_zero (c : ℝ) : ∀ L : List (ℚ × ℚ), (∀ s ∈ L, (s.1 : ℝ) ≤ c) → aux_plc_A L c = 0
  | [] => by simp [aux_plc_A]
  | s :: L => by
    intro h
    have ih := aux_plc_A_zero c L (fun u hu => h u (List.mem_cons_of_mem _ hu))
    have hs := h s (List.mem_cons_self)
    simp only [aux_plc_A, List.map_cons, List.sum_cons] at ih ⊢
    rw [ih, if_neg (not_lt.2 hs)]; simp

theorem aux_plc_B_zero (c : ℝ) : ∀ L : List (ℚ × ℚ), (∀ s ∈ L, (s.1 : ℝ) < c) → aux_plc_B L c = 0
  | [] => by simp [aux_plc_B]
  | s :: L => by
    intro h
    have ih := aux_plc_B_zero c L (fun u hu => h u (List.mem_cons_of_mem _ hu))
    have hs := h s (List.mem_cons_self)
    simp only [aux_plc_B, List.map_cons, List.sum_cons] at ih ⊢
    rw [ih, if_neg (not_le.2 hs)]; simp

theorem aux_plc_plEval_nonpos : ∀ L : List (ℚ × ℚ), (∀ s ∈ L, 0 < s.2) → ∀ w : ℝ, w ≤ 0 → plEval L w = 0
  | [] => by intros; simp [plEval]
  | s :: L => by
    intro h w hw
    have hs : (0 : ℝ) < s.2 := by exact_mod_cast h s (List.mem_cons_self)
    have ih := aux_plc_plEval_nonpos L (fun u hu => h u (List.mem_cons_of_mem _ hu)) (w - s.2) (by linarith)
    obtain ⟨c, a⟩ := s
    simp only [plEval, ih, max_eq_right hw]
    simp [min_eq_left hs.le]

theorem aux_plc_sum_nonneg : ∀ L : List (ℚ × ℚ), (∀ s ∈ L, 0 < s.2) → (0 : ℝ) ≤ (((L.map Prod.snd).sum : ℚ) : ℝ)
  | [] => by simp
  | s :: L => by
    intro h
    have hs : (0 : ℝ) < s.2 := by exact_mod_cast h s (List.mem_cons_self)
    have ih := aux_plc_sum_nonneg L (fun u hu => h u (List.mem_cons_of_mem _ hu))
    simp only [List.map_cons, List.sum_cons, Rat.cast_add] at ih ⊢
    linarith

theorem aux_plc_F_nonpos (L : List (ℚ × ℚ)) (t : ℚ) (h : ∀ s ∈ L, 0 < s.2) (w : ℝ) (hw : w ≤ 0) :
    aux_plc_F L t w = 0 := by
  have := aux_plc_sum_nonneg L h
  simp only [aux_plc_F, aux_plc_plEval_nonpos L h w hw, max_eq_right (by linarith : w - _ ≤ 0)]
  simp

theorem aux_plc_F_cons (c a : ℚ) (L : List (ℚ × ℚ)) (t : ℚ) (x : ℝ) :
    aux_plc_F ((c, a) :: L) t x = (c : ℝ) * min (max x 0) (a : ℝ) + aux_plc_F L t (x - a) := by
  simp only [aux_plc_F, plEval, List.map_cons, List.sum_cons, Rat.cast_add]
  ring_nf

theorem aux_plc_super (t : ℚ) (c : ℝ) : ∀ (L : List (ℚ × ℚ)),
    (∀ s ∈ L, 0 < s.2) → L.Pairwise (fun s u => u.1 ≤ s.1) → (∀ s ∈ L, t ≤ s.1) → (t : ℝ) ≤ c →
    ∀ x : ℝ, 0 ≤ x → aux_plc_A L c ≤ x → ((t : ℝ) < c → x ≤ aux_plc_B L c) →
    ∀ z : ℝ, 0 ≤ z →
      aux_plc_F L t z ≤ aux_plc_F L t x + c * (z - x) ∧
      (z < aux_plc_A L c → aux_plc_F L t z < aux_plc_F L t x + c * (z - x)) ∧
      ((t : ℝ) < c → aux_plc_B L c < z → aux_plc_F L t z < aux_plc_F L t x + c * (z - x))
  | [] => by
    intro _ _ _ htc x hx hA hB z hz
    simp only [aux_plc_A, aux_plc_B, aux_plc_F, plEval, List.map_nil, List.sum_nil, Rat.cast_zero,
      sub_zero, zero_add] at hA hB ⊢
    rw [max_eq_left hz, max_eq_left hx]
    rcases htc.lt_or_eq with h | h
    · have hx0 : x = 0 := le_antisymm (hB h) hx
      subst hx0
      refine ⟨by nlinarith, fun h' => absurd h' (not_lt.2 hz), fun _ h' => by nlinarith⟩
    · refine ⟨le_of_eq (by rw [← h]; ring), fun h' => absurd h' (not_lt.2 hz),
        fun h' => absurd h (ne_of_lt h')⟩
  | s :: L => by
    intro hpos hpw htl htc x hx hA hB z hz
    obtain ⟨c1, a1⟩ := s
    have ha1 : (0:ℝ) < a1 := by exact_mod_cast hpos _ List.mem_cons_self
    have hposL : ∀ u ∈ L, 0 < u.2 := fun u hu => hpos u (List.mem_cons_of_mem _ hu)
    rw [List.pairwise_cons] at hpw
    have hle1 : ∀ u ∈ L, (u.1 : ℝ) ≤ c1 := fun u hu => by exact_mod_cast hpw.1 u hu
    have htlL : ∀ u ∈ L, t ≤ u.1 := fun u hu => htl u (List.mem_cons_of_mem _ hu)
    have ht1 : (t:ℝ) ≤ c1 := by exact_mod_cast htl _ List.mem_cons_self
    have ih := aux_plc_super t c L hposL hpw.2 htlL htc
    have hAc : aux_plc_A ((c1, a1) :: L) c = (if c < (c1:ℝ) then (a1:ℝ) else 0) + aux_plc_A L c := by
      simp [aux_plc_A]
    have hBc : aux_plc_B ((c1, a1) :: L) c = (if c ≤ (c1:ℝ) then (a1:ℝ) else 0) + aux_plc_B L c := by
      simp [aux_plc_B]
    have hAL0 := aux_plc_A_nonneg c L hposL
    have hBL0 : 0 ≤ aux_plc_B L c := by rw [aux_plc_B_eq]; linarith [aux_plc_C_nonneg c L hposL]
    have hF0 : ∀ w ≤ 0, aux_plc_F L t w = 0 := aux_plc_F_nonpos L t hposL
    rw [hAc] at hA ⊢
    rw [hBc] at hB ⊢
    rcases lt_trichotomy c (c1:ℝ) with hc | hc | hc
    · -- c < c1
      rw [if_pos hc] at hA ⊢
      rw [if_pos hc.le] at hB ⊢
      have hxa : (a1:ℝ) ≤ x := by linarith
      have ihx := ih (x - a1) (by linarith) (by linarith) (fun h => by linarith [hB h])
      have e1 : aux_plc_F ((c1, a1) :: L) t x = c1 * a1 + aux_plc_F L t (x - a1) := by
        rw [aux_plc_F_cons, max_eq_left hx, min_eq_right hxa]
      obtain ⟨h0, -, -⟩ := ihx 0 le_rfl
      rw [hF0 0 le_rfl] at h0
      rw [e1]
      by_cases hza : (a1:ℝ) ≤ z
      · have e2 : aux_plc_F ((c1, a1) :: L) t z = c1 * a1 + aux_plc_F L t (z - a1) := by
          rw [aux_plc_F_cons, max_eq_left hz, min_eq_right hza]
        obtain ⟨i1, i2, i3⟩ := ihx (z - a1) (by linarith)
        rw [e2]
        refine ⟨by linarith, fun h => by linarith [i2 (by linarith)],
          fun ht h => by linarith [i3 ht (by linarith)]⟩
      · rw [not_le] at hza
        have e2 : aux_plc_F ((c1, a1) :: L) t z = c1 * z := by
          rw [aux_plc_F_cons, max_eq_left hz, min_eq_left hza.le, hF0 _ (by linarith)]; ring
        have key : (c1:ℝ) * z < c1 * a1 + aux_plc_F L t (x - a1) + c * (z - x) := by
          nlinarith [mul_pos (sub_pos.2 hc) (sub_pos.2 hza)]
        rw [e2]; exact ⟨key.le, fun _ => key, fun _ _ => key⟩
    · -- c = c1
      subst hc
      have hAL : aux_plc_A L (c1:ℝ) = 0 := aux_plc_A_zero _ L hle1
      rw [if_neg (lt_irrefl _), hAL] at hA ⊢
      rw [if_pos le_rfl] at hB ⊢
      by_cases hxa : x ≤ (a1:ℝ)
      · have e1 : aux_plc_F ((c1, a1) :: L) t x = c1 * x := by
          rw [aux_plc_F_cons, max_eq_left hx, min_eq_left hxa, hF0 _ (by linarith)]; ring
        have ih0 := ih 0 le_rfl (by rw [hAL]) (fun _ => hBL0)
        rw [e1]
        by_cases hza : (a1:ℝ) ≤ z
        · have e2 : aux_plc_F ((c1, a1) :: L) t z = c1 * a1 + aux_plc_F L t (z - a1) := by
            rw [aux_plc_F_cons, max_eq_left hz, min_eq_right hza]
          obtain ⟨i1, -, i3⟩ := ih0 (z - a1) (by linarith)
          rw [hF0 0 le_rfl] at i1 i3
          rw [e2]
          refine ⟨by linarith, fun h => by linarith, fun ht h => by linarith [i3 ht (by linarith)]⟩
        · rw [not_le] at hza
          have e2 : aux_plc_F ((c1, a1) :: L) t z = c1 * z := by
            rw [aux_plc_F_cons, max_eq_left hz, min_eq_left hza.le, hF0 _ (by linarith)]; ring
          rw [e2]
          refine ⟨le_of_eq (by ring), fun h => by linarith, fun _ h => by linarith⟩
      · rw [not_le] at hxa
        have ihx := ih (x - a1) (by linarith) (by rw [hAL]; linarith) (fun h => by linarith [hB h])
        have e1 : aux_plc_F ((c1, a1) :: L) t x = c1 * a1 + aux_plc_F L t (x - a1) := by
          rw [aux_plc_F_cons, max_eq_left hx, min_eq_right hxa.le]
        obtain ⟨h0, -, -⟩ := ihx 0 le_rfl
        rw [hF0 0 le_rfl] at h0
        rw [e1]
        by_cases hza : (a1:ℝ) ≤ z
        · have e2 : aux_plc_F ((c1, a1) :: L) t z = c1 * a1 + aux_plc_F L t (z - a1) := by
            rw [aux_plc_F_cons, max_eq_left hz, min_eq_right hza]
          obtain ⟨i1, -, i3⟩ := ihx (z - a1) (by linarith)
          rw [e2]
          refine ⟨by linarith, fun h => by linarith, fun ht h => by linarith [i3 ht (by linarith)]⟩
        · rw [not_le] at hza
          have e2 : aux_plc_F ((c1, a1) :: L) t z = c1 * z := by
            rw [aux_plc_F_cons, max_eq_left hz, min_eq_left hza.le, hF0 _ (by linarith)]; ring
          rw [e2]
          refine ⟨by linarith, fun h => by linarith, fun _ h => by linarith⟩
    · -- c1 < c
      have hAL : aux_plc_A L c = 0 := aux_plc_A_zero _ L (fun u hu => (hle1 u hu).trans hc.le)
      have hBL : aux_plc_B L c = 0 := aux_plc_B_zero _ L (fun u hu => lt_of_le_of_lt (hle1 u hu) hc)
      have htc' : (t:ℝ) < c := lt_of_le_of_lt ht1 hc
      rw [if_neg (not_lt.2 hc.le), hAL] at hA ⊢
      rw [if_neg (not_le.2 hc), hBL] at hB ⊢
      have hx0 : x = 0 := le_antisymm (by linarith [hB htc']) hx
      subst hx0
      have e1 : aux_plc_F ((c1, a1) :: L) t 0 = 0 := aux_plc_F_nonpos _ t hpos 0 le_rfl
      have ih0 := ih 0 le_rfl (by rw [hAL]) (fun _ => by rw [hBL])
      rw [e1]
      suffices hs : aux_plc_F ((c1, a1) :: L) t z ≤ 0 + c * (z - 0) ∧
          (0 < z → aux_plc_F ((c1, a1) :: L) t z < 0 + c * (z - 0)) by
        refine ⟨hs.1, fun h => by linarith, fun _ h => hs.2 (by linarith)⟩
      by_cases hza : (a1:ℝ) ≤ z
      · have e2 : aux_plc_F ((c1, a1) :: L) t z = c1 * a1 + aux_plc_F L t (z - a1) := by
          rw [aux_plc_F_cons, max_eq_left hz, min_eq_right hza]
        obtain ⟨i1, -, -⟩ := ih0 (z - a1) (by linarith)
        rw [hF0 0 le_rfl] at i1
        have hlt : (c1:ℝ) * a1 < c * a1 := mul_lt_mul_of_pos_right hc ha1
        rw [e2]
        exact ⟨by linarith, fun _ => by linarith⟩
      · rw [not_le] at hza
        have e2 : aux_plc_F ((c1, a1) :: L) t z = c1 * z := by
          rw [aux_plc_F_cons, max_eq_left hz, min_eq_left hza.le, hF0 _ (by linarith)]; ring
        rw [e2]
        exact ⟨by nlinarith [mul_le_mul_of_nonneg_right hc.le hz],
          fun hz' => by nlinarith [mul_lt_mul_of_pos_right hc hz']⟩

open FisherMarket in
theorem aux_plc_sumget (L : List (ℚ × ℚ)) (φ : ℚ × ℚ → ℝ) :
    ∑ k : Fin L.length, φ (L.get k) = (L.map φ).sum := by
  simp

section market
variable {n g : ℕ}

theorem aux_plc_forced_eq (M : FisherMarket n g) (p : Fin g → ℝ) (hp : ∀ j, 0 < p j) (i : Fin n)
    (j : Fin g) :
    M.forcedAmount p i j = aux_plc_A (M.util i j).segs (M.flexBpb p i * p j) := by
  unfold FisherMarket.forcedAmount aux_plc_A
  rw [Finset.sum_filter, ← aux_plc_sumget]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [FisherMarket.IsForcedSeg, FisherMarket.segBpb, FisherMarket.segSlope,
    FisherMarket.segAmount, lt_div_iff₀ (hp j)]

theorem aux_plc_flexCap_eq (M : FisherMarket n g) (p : Fin g → ℝ) (hp : ∀ j, 0 < p j) (i : Fin n)
    (j : Fin g) :
    M.flexCap p j i = p j * aux_plc_C (M.util i j).segs (M.flexBpb p i * p j) := by
  unfold FisherMarket.flexCap aux_plc_C
  rw [Finset.sum_filter, ← aux_plc_sumget, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [FisherMarket.IsFlexibleSeg, FisherMarket.segBpb, FisherMarket.segSlope,
    FisherMarket.segValue, FisherMarket.segAmount, div_eq_iff (hp j).ne']
  split_ifs <;> ring

theorem aux_plc_spent_eq (M : FisherMarket n g) (p : Fin g → ℝ) (i : Fin n) :
    M.spent p i = ∑ j, p j * M.forcedAmount p i j := by
  unfold FisherMarket.spent FisherMarket.forcedAmount
  rw [Finset.sum_filter, Fintype.sum_sigma]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_filter, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  split_ifs <;> simp [FisherMarket.segValue, mul_comm]

theorem aux_plc_vae_eq (M : FisherMarket n g) (p : Fin g → ℝ) (hp : ∀ j, 0 < p j) (i : Fin n)
    (r : ℝ) {inst : DecidablePred (fun s : M.Seg i => r ≤ M.segBpb p s)} :
    ∑ s ∈ Finset.univ.filter (fun s : M.Seg i => r ≤ M.segBpb p s), M.segValue p s =
      ∑ j, p j * aux_plc_B (M.util i j).segs (r * p j) := by
  rw [Finset.sum_filter, Fintype.sum_sigma]
  refine Finset.sum_congr rfl fun j _ => ?_
  unfold aux_plc_B
  rw [← aux_plc_sumget, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [FisherMarket.segBpb, FisherMarket.segSlope, FisherMarket.segValue,
    FisherMarket.segAmount, le_div_iff₀ (hp j)]
  split_ifs <;> ring

theorem aux_plc_flex_facts (M : FisherMarket n g) (p : Fin g → ℝ) (hp : ∀ j, 0 < p j) (i : Fin n)
    (hg : Nonempty (Fin g)) :
    0 ≤ M.flexBpb p i ∧ (∀ j, ((M.util i j).tail : ℝ) ≤ M.flexBpb p i * p j) ∧
      M.ValueAboveExceeds p i (M.flexBpb p i) := by
  obtain ⟨j0⟩ := hg
  set T := {r | r ∈ Set.range (fun s : M.Piece i => M.pieceBpb p s) ∧ M.ValueAboveExceeds p i r}
    with hT
  have hfin : T.Finite := (Set.finite_range _).subset (fun r hr => hr.1)
  have htail : ∀ j, M.pieceBpb p (⟨j, none⟩ : M.Piece i) ∈ T :=
    fun j => ⟨⟨_, rfl⟩, Or.inl ⟨j, le_rfl⟩⟩
  have hmem : M.flexBpb p i ∈ T := Set.Nonempty.csSup_mem ⟨_, htail j0⟩ hfin
  have hle : ∀ j, M.pieceBpb p (⟨j, none⟩ : M.Piece i) ≤ M.flexBpb p i :=
    fun j => le_csSup hfin.bddAbove (htail j)
  have hpb : ∀ j, M.pieceBpb p (⟨j, none⟩ : M.Piece i) = ((M.util i j).tail : ℝ) / p j :=
    fun j => rfl
  refine ⟨?_, fun j => ?_, hmem.2⟩
  · have h1 := hle j0
    rw [hpb] at h1
    have h2 : 0 ≤ ((M.util i j0).tail : ℝ) / p j0 :=
      div_nonneg (by exact_mod_cast (M.util i j0).tail_nonneg) (hp j0).le
    linarith
  · have h1 := hle j
    rw [hpb, div_le_iff₀ (hp j)] at h1
    exact h1

theorem aux_plc_flexTail_iff (M : FisherMarket n g) (p : Fin g → ℝ) (hp : ∀ j, 0 < p j) (i : Fin n)
    (j : Fin g) : M.IsFlexibleTail p i j ↔ ((M.util i j).tail : ℝ) = M.flexBpb p i * p j := by
  show ((M.util i j).tail : ℝ) / p j = M.flexBpb p i ↔ _
  rw [div_eq_iff (hp j).ne']

theorem aux_plc_sum_super (M : FisherMarket n g) (p : Fin g → ℝ) (i : Fin n) (r : ℝ)
    (x z : Fin g → ℝ) :
    ∑ j, (aux_plc_F (M.util i j).segs (M.util i j).tail (x j) + r * p j * (z j - x j)) =
      M.utility i x + r * (∑ j, p j * z j - ∑ j, p j * x j) := by
  rw [Finset.sum_add_distrib, ← Finset.sum_sub_distrib, Finset.mul_sum]
  congr 1
  exact Finset.sum_congr rfl (fun j _ => by ring)

theorem aux_plc_fwd_buyer (M : FisherMarket n g) (p : Fin g → ℝ) (hp : ∀ j, 0 < p j) (i : Fin n)
    (hg : Nonempty (Fin g)) (hunsp : 0 ≤ M.unspent p i)
    (x : Fin g → ℝ) (hx : M.IsOptimalBundle p i x) (j : Fin g) :
    0 ≤ p j * (x j - M.forcedAmount p i j) ∧
      (¬ M.IsFlexibleTail p i j → p j * (x j - M.forcedAmount p i j) ≤ M.flexCap p j i) := by
  obtain ⟨hr0, htl, hvae⟩ := aux_plc_flex_facts M p hp i hg
  set r := M.flexBpb p i with hr
  set A : Fin g → ℝ := fun j => aux_plc_A (M.util i j).segs (r * p j) with hA
  set B : Fin g → ℝ := fun j => aux_plc_B (M.util i j).segs (r * p j) with hB
  have hA0 : ∀ j, 0 ≤ A j := fun j => aux_plc_A_nonneg _ _ (M.util i j).amount_pos
  have hAB : ∀ j, A j ≤ B j := fun j => by
    simp only [hA, hB]
    rw [aux_plc_B_eq]
    linarith [aux_plc_C_nonneg (r * p j) _ (M.util i j).amount_pos]
  have hspent : M.spent p i = ∑ j, p j * A j := by
    rw [aux_plc_spent_eq]
    exact Finset.sum_congr rfl fun j _ => by rw [aux_plc_forced_eq M p hp]
  obtain ⟨xs, hxsA, hxsB, hxse⟩ : ∃ xs : Fin g → ℝ, (∀ j, A j ≤ xs j) ∧
      (∀ j, ((M.util i j).tail : ℝ) < r * p j → xs j ≤ B j) ∧
      ∑ j, p j * xs j = M.budget i := by
    unfold FisherMarket.ValueAboveExceeds at hvae
    rcases hvae with ⟨j0, hj0⟩ | hlt
    · have hj0' : ((M.util i j0).tail : ℝ) = r * p j0 := by
        have h1 : r ≤ ((M.util i j0).tail : ℝ) / p j0 := hj0
        rw [le_div_iff₀ (hp j0)] at h1
        exact le_antisymm (htl j0) h1
      refine ⟨fun j => A j + if j = j0 then M.unspent p i / p j else 0, fun j => ?_,
        fun j hj => ?_, ?_⟩
      · have : 0 ≤ (if j = j0 then M.unspent p i / p j else 0) := by
          split_ifs
          · exact div_nonneg hunsp (hp j).le
          · exact le_rfl
        linarith
      · have hne : j ≠ j0 := by rintro rfl; linarith
        simp only [if_neg hne, add_zero]
        exact hAB j
      · have e : ∀ j, p j * (A j + if j = j0 then M.unspent p i / p j else 0) =
            p j * A j + if j = j0 then M.unspent p i else 0 := by
          intro j
          split_ifs
          · have := (hp j).ne'
            field_simp
          · ring
        simp only [e, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true,
          ← hspent]
        unfold FisherMarket.unspent
        ring
    · rw [aux_plc_vae_eq M p hp i] at hlt
      have hVA : ∑ j, p j * A j ≤ M.budget i := by
        have h1 := hunsp
        unfold FisherMarket.unspent at h1
        linarith
      have hVAB : ∑ j, p j * A j < ∑ j, p j * B j := lt_of_le_of_lt hVA hlt
      set θ := ((M.budget i : ℝ) - ∑ j, p j * A j) / (∑ j, p j * B j - ∑ j, p j * A j) with hθ
      have hθ0 : 0 ≤ θ := div_nonneg (by linarith) (by linarith)
      have hθ1 : θ ≤ 1 := by rw [hθ, div_le_one (by linarith)]; linarith
      refine ⟨fun j => A j + θ * (B j - A j), fun j => ?_, fun j _ => ?_, ?_⟩
      · have := mul_nonneg hθ0 (sub_nonneg.2 (hAB j))
        linarith
      · have := mul_nonneg (sub_nonneg.2 hθ1) (sub_nonneg.2 (hAB j))
        linarith
      · have e : ∑ j, p j * (A j + θ * (B j - A j)) =
            ∑ j, p j * A j + θ * (∑ j, p j * B j - ∑ j, p j * A j) := by
          rw [← Finset.sum_sub_distrib, Finset.mul_sum, ← Finset.sum_add_distrib]
          exact Finset.sum_congr rfl fun j _ => by ring
        rw [e, hθ, div_mul_cancel₀ _ (sub_pos.2 hVAB).ne']
        ring
  have hxs0 : ∀ j, 0 ≤ xs j := fun j => (hA0 j).trans (hxsA j)
  have hU : M.utility i xs ≤ M.utility i x := hx.2.2 xs hxs0 (le_of_eq hxse)
  have hsup := fun j => aux_plc_super (M.util i j).tail (r * p j) (M.util i j).segs
    (M.util i j).amount_pos (M.util i j).slope_antitone (M.util i j).tail_le (htl j) (xs j)
    (hxs0 j) (hxsA j) (hxsB j) (x j) (hx.1 j)
  have hno : ∀ j0, ¬ (aux_plc_F (M.util i j0).segs (M.util i j0).tail (x j0) <
      aux_plc_F (M.util i j0).segs (M.util i j0).tail (xs j0) + r * p j0 * (x j0 - xs j0)) := by
    intro j0 hj0
    have hlt := Finset.sum_lt_sum (fun j (_ : j ∈ Finset.univ) => (hsup j).1)
      ⟨j0, Finset.mem_univ _, hj0⟩
    rw [aux_plc_sum_super M p i r xs x] at hlt
    have hux : M.utility i x = ∑ j, aux_plc_F (M.util i j).segs (M.util i j).tail (x j) := rfl
    rw [← hux] at hlt
    have hpx := hx.2.1
    have : r * (∑ j, p j * x j - ∑ j, p j * xs j) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hr0 (by linarith)
    linarith
  have hfj : M.forcedAmount p i j = A j := aux_plc_forced_eq M p hp i j
  rw [hfj]
  have hxA : A j ≤ x j := by
    by_contra h
    rw [not_le] at h
    exact hno j ((hsup j).2.1 h)
  refine ⟨mul_nonneg (hp j).le (by linarith), fun hnf => ?_⟩
  have htlt : ((M.util i j).tail : ℝ) < r * p j :=
    lt_of_le_of_ne (htl j) (fun h => hnf ((aux_plc_flexTail_iff M p hp i j).2 h))
  have hxB : x j ≤ B j := by
    by_contra h
    rw [not_le] at h
    exact hno j ((hsup j).2.2 htlt h)
  rw [aux_plc_flexCap_eq M p hp i j]
  have hBC : B j = A j + aux_plc_C (M.util i j).segs (r * p j) := aux_plc_B_eq _ _
  exact mul_le_mul_of_nonneg_left (by linarith) (hp j).le

end market

end PLCMarkets.Rationality

open PLCMarkets.Rationality

theorem solution {n g : ℕ} (M : FisherMarket n g) (p : Fin g → ℝ)
    (hp : ∀ j, 0 < p j)
    (hsum : ∑ j, p j = ∑ i, (M.budget i : ℝ))
    (hunspent : ∀ i, 0 ≤ M.unspent p i)
    (hunsold : ∀ j, 0 ≤ M.unsold p j) :
    M.IsEquilibrium p ↔ M.maxFlow p = ∑ i, M.unspent p i := by
  have hg : ∀ i : Fin n, Nonempty (Fin g) := by
    intro i
    by_contra hne
    rw [not_nonempty_iff] at hne
    have h0 : ∑ j, p j = 0 := by simp
    have hpos : 0 < ∑ i, (M.budget i : ℝ) :=
      Finset.sum_pos (fun i _ => by exact_mod_cast M.budget_pos i) ⟨i, Finset.mem_univ _⟩
    linarith
  have hid : ∑ j, M.unsold p j * p j = ∑ i, M.unspent p i := by
    simp only [FisherMarket.unsold, FisherMarket.forced, FisherMarket.unspent, aux_plc_spent_eq,
      sub_mul, one_mul, Finset.sum_sub_distrib, Finset.sum_mul, hsum]
    congr 1
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  have hbdd : ∀ y, M.IsFeasibleFlow p y → ∑ j, ∑ i, y j i ≤ ∑ i, M.unspent p i := by
    intro y hy
    rw [Finset.sum_comm]
    exact Finset.sum_le_sum (fun i _ => hy.2.2.2 i)
  have hBdd : BddAbove {v | ∃ y, M.IsFeasibleFlow p y ∧ v = ∑ j, ∑ i, y j i} := by
    refine ⟨∑ i, M.unspent p i, ?_⟩
    rintro v ⟨y, hy, rfl⟩
    exact hbdd y hy
  constructor
  · rintro ⟨-, x, hxopt, hxclear⟩
    have hfb := fun i j => aux_plc_fwd_buyer M p hp i (hg i) (hunspent i) (x i) (hxopt i) j
    have hcol : ∀ j, ∑ i, p j * (x i j - M.forcedAmount p i j) = M.unsold p j * p j := by
      intro j
      rw [← Finset.mul_sum, Finset.sum_sub_distrib, hxclear]
      simp only [FisherMarket.unsold, FisherMarket.forced]
      ring
    have hy : M.IsFeasibleFlow p (fun j i => p j * (x i j - M.forcedAmount p i j)) := by
      refine ⟨fun j i => (hfb i j).1, fun j i h => (hfb i j).2 h, fun j => le_of_eq (hcol j),
        fun i => ?_⟩
      have h1 := (hxopt i).2.1
      simp only [mul_sub, Finset.sum_sub_distrib, FisherMarket.unspent, aux_plc_spent_eq]
      linarith
    have hval : ∑ j, ∑ i, p j * (x i j - M.forcedAmount p i j) = ∑ i, M.unspent p i := by
      rw [← hid]
      exact Finset.sum_congr rfl fun j _ => hcol j
    apply le_antisymm
    · exact csSup_le ⟨_, _, hy, rfl⟩ (by rintro v ⟨y', hy', rfl⟩; exact hbdd y' hy')
    · rw [← hval]
      exact le_csSup hBdd ⟨_, hy, rfl⟩
  · intro hmax
    have hcpt : IsCompact {y : Fin g → Fin n → ℝ | M.IsFeasibleFlow p y} := by
      apply (isCompact_Icc (a := (0 : Fin g → Fin n → ℝ))
        (b := fun _ i => M.unspent p i)).of_isClosed_subset
      · simp only [FisherMarket.IsFeasibleFlow, Set.ofPred_and, Set.ofPred_forall]
        refine IsClosed.inter ?_ (IsClosed.inter ?_ (IsClosed.inter ?_ ?_))
        · exact isClosed_iInter fun j => isClosed_iInter fun i =>
            isClosed_le continuous_const (by fun_prop)
        · exact isClosed_iInter fun j => isClosed_iInter fun i => isClosed_iInter fun _ =>
            isClosed_le (by fun_prop) continuous_const
        · exact isClosed_iInter fun j => isClosed_le (by fun_prop) continuous_const
        · exact isClosed_iInter fun i => isClosed_le (by fun_prop) continuous_const
      · intro y hy
        refine ⟨fun j i => hy.1 j i, fun j i => ?_⟩
        calc y j i ≤ ∑ j', y j' i := Finset.single_le_sum (fun j' _ => hy.1 j' i) (Finset.mem_univ j)
          _ ≤ M.unspent p i := hy.2.2.2 i
    have hne : ({y : Fin g → Fin n → ℝ | M.IsFeasibleFlow p y}).Nonempty := by
      refine ⟨0, fun j i => le_rfl, fun j i _ => ?_, fun j => ?_, fun i => ?_⟩
      · rw [aux_plc_flexCap_eq M p hp i j]
        exact mul_nonneg (hp j).le (aux_plc_C_nonneg _ _ (M.util i j).amount_pos)
      · simp only [Pi.zero_apply, Finset.sum_const_zero]
        exact mul_nonneg (hunsold j) (hp j).le
      · simp only [Pi.zero_apply, Finset.sum_const_zero]
        exact hunspent i
    have himg := (hcpt.image (f := fun y : Fin g → Fin n → ℝ => ∑ j, ∑ i, y j i)
      (by fun_prop)).sSup_mem (hne.image _)
    have hset : (fun y : Fin g → Fin n → ℝ => ∑ j, ∑ i, y j i) ''
        {y : Fin g → Fin n → ℝ | M.IsFeasibleFlow p y} =
        {v | ∃ y, M.IsFeasibleFlow p y ∧ v = ∑ j, ∑ i, y j i} := by
      ext v
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact ⟨y, hy, rfl⟩
      · rintro ⟨y, hy, rfl⟩
        exact ⟨y, hy, rfl⟩
    rw [hset] at himg
    obtain ⟨y, hy, hyv⟩ := himg
    have hyv' : ∑ j, ∑ i, y j i = ∑ i, M.unspent p i := by
      rw [← hmax, ← hyv]
      rfl
    have hti : ∀ i, ∑ j, y j i = M.unspent p i := by
      intro i0
      by_contra hne'
      have hlt : ∑ i, ∑ j, y j i < ∑ i, M.unspent p i :=
        Finset.sum_lt_sum (fun i _ => hy.2.2.2 i)
          ⟨i0, Finset.mem_univ _, lt_of_le_of_ne (hy.2.2.2 i0) hne'⟩
      rw [Finset.sum_comm] at hlt
      linarith
    have htj : ∀ j, ∑ i, y j i = M.unsold p j * p j := by
      intro j0
      by_contra hne'
      have hlt : ∑ j, ∑ i, y j i < ∑ j, M.unsold p j * p j :=
        Finset.sum_lt_sum (fun j _ => hy.2.2.1 j)
          ⟨j0, Finset.mem_univ _, lt_of_le_of_ne (hy.2.2.1 j0) hne'⟩
      linarith
    refine ⟨fun j => (hp j).le, fun i j => M.forcedAmount p i j + y j i / p j, fun i => ?_,
      fun j => ?_⟩
    · obtain ⟨hr0, htl, -⟩ := aux_plc_flex_facts M p hp i (hg i)
      have hA : ∀ j, M.forcedAmount p i j =
          aux_plc_A (M.util i j).segs (M.flexBpb p i * p j) := aux_plc_forced_eq M p hp i
      have hx0 : ∀ j, 0 ≤ M.forcedAmount p i j + y j i / p j := fun j => by
        rw [hA]
        have := aux_plc_A_nonneg (M.flexBpb p i * p j) _ (M.util i j).amount_pos
        have := div_nonneg (hy.1 j i) (hp j).le
        linarith
      have hspend : ∑ j, p j * (M.forcedAmount p i j + y j i / p j) = M.budget i := by
        have e : ∀ j, p j * (M.forcedAmount p i j + y j i / p j) =
            p j * M.forcedAmount p i j + y j i := fun j => by
          have := (hp j).ne'
          field_simp
        simp only [e, Finset.sum_add_distrib, hti, ← aux_plc_spent_eq, FisherMarket.unspent]
        ring
      refine ⟨hx0, le_of_eq hspend, fun z hz hzb => ?_⟩
      have hsup : ∀ j, aux_plc_F (M.util i j).segs (M.util i j).tail (z j) ≤
          aux_plc_F (M.util i j).segs (M.util i j).tail (M.forcedAmount p i j + y j i / p j) +
            M.flexBpb p i * p j * (z j - (M.forcedAmount p i j + y j i / p j)) := by
        intro j
        refine (aux_plc_super (M.util i j).tail (M.flexBpb p i * p j) (M.util i j).segs
          (M.util i j).amount_pos (M.util i j).slope_antitone (M.util i j).tail_le (htl j) _
          (hx0 j) ?_ ?_ (z j) (hz j)).1
        · rw [← hA]
          have := div_nonneg (hy.1 j i) (hp j).le
          linarith
        · intro htlt
          have hnf : ¬ M.IsFlexibleTail p i j := fun h =>
            absurd ((aux_plc_flexTail_iff M p hp i j).1 h) (ne_of_lt htlt)
          have hcap := hy.2.1 j i hnf
          rw [aux_plc_flexCap_eq M p hp i j] at hcap
          rw [aux_plc_B_eq, ← hA]
          have : y j i / p j ≤ aux_plc_C (M.util i j).segs (M.flexBpb p i * p j) := by
            rw [div_le_iff₀ (hp j)]
            linarith [mul_comm (p j) (aux_plc_C (M.util i j).segs (M.flexBpb p i * p j))]
          linarith
      have hsum' := Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) => hsup j)
      rw [aux_plc_sum_super M p i (M.flexBpb p i)
        (fun j => M.forcedAmount p i j + y j i / p j) z] at hsum'
      have hut : M.utility i z = ∑ j, aux_plc_F (M.util i j).segs (M.util i j).tail (z j) := rfl
      rw [hut]
      have : M.flexBpb p i * (∑ j, p j * z j -
          ∑ j, p j * (M.forcedAmount p i j + y j i / p j)) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos hr0 (by rw [hspend]; linarith)
      linarith
    · show ∑ i, (M.forcedAmount p i j + y j i / p j) = 1
      rw [Finset.sum_add_distrib, ← Finset.sum_div, htj]
      have := (hp j).ne'
      field_simp
      simp only [FisherMarket.unsold, FisherMarket.forced]
      ring
