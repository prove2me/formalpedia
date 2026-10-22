-- Prove2me | solution 1 for QCircMITM.Search.main_result
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung
-- created : 2026-10-21T16:43:53.310295+00:00
-- url     : https://prove2.me/submissions/ba1eec78-2428-4d98-8dde-cb36eff32120

import Mathlib
import Definitions.Def_QCircMITM_Search_Algorithm

open QCircMITM.Search

theorem qc_mem_circuits {n : ℕ} (V : Finset (Unitary n)) (i : ℕ) (c : List (Unitary n)) :
    c ∈ circuits V i ↔ c.length = i ∧ ∀ W ∈ c, W ∈ V := by
  induction i generalizing c with
  | zero =>
    simp only [circuits, Finset.mem_singleton]
    constructor
    · rintro rfl; simp
    · rintro ⟨h, -⟩; exact List.length_eq_zero_iff.1 h
  | succ i ih =>
    simp only [circuits, Finset.mem_image, Finset.mem_product]
    constructor
    · rintro ⟨⟨W, c'⟩, ⟨hW, hc'⟩, rfl⟩
      rw [ih] at hc'
      refine ⟨by simp [hc'.1], ?_⟩
      intro X hX
      rcases List.mem_cons.1 hX with rfl | hX
      · exact hW
      · exact hc'.2 X hX
    · rintro ⟨hlen, hall⟩
      cases c with
      | nil => simp at hlen
      | cons W c' =>
        refine ⟨⟨W, c'⟩, ⟨hall W (List.mem_cons_self), ?_⟩, rfl⟩
        rw [ih]
        exact ⟨by simpa using hlen, fun X hX => hall X (List.mem_cons_of_mem _ hX)⟩

theorem qc_S_eq {n : ℕ} (V : Finset (Unitary n)) (i : ℕ) :
    S V i = (circuits V i).image List.prod := by
  induction i with
  | zero => simp [S, circuits]
  | succ i ih =>
    ext U
    simp only [S, circuits, ih, Finset.mem_image, Finset.mem_product, Prod.exists]
    constructor
    · rintro ⟨W, X, ⟨hW, c, hc, rfl⟩, rfl⟩
      exact ⟨W :: c, ⟨W, c, ⟨hW, hc⟩, rfl⟩, by simp⟩
    · rintro ⟨_, ⟨W, c, ⟨hW, hc⟩, rfl⟩, rfl⟩
      exact ⟨W, c.prod, ⟨hW, c, hc, rfl⟩, by simp⟩

theorem qc_mem_S {n : ℕ} (V : Finset (Unitary n)) (i : ℕ) (U : Unitary n) :
    U ∈ S V i ↔ ∃ c : List (Unitary n), c.length = i ∧ (∀ W ∈ c, W ∈ V) ∧ c.prod = U := by
  rw [qc_S_eq, Finset.mem_image]
  constructor
  · rintro ⟨c, hc, rfl⟩
    rw [qc_mem_circuits] at hc
    exact ⟨c, hc.1, hc.2, rfl⟩
  · rintro ⟨c, h1, h2, rfl⟩
    exact ⟨c, (qc_mem_circuits V i c).2 ⟨h1, h2⟩, rfl⟩

theorem qc_split {n : ℕ} (V : Finset (Unitary n)) (p q : ℕ) (U : Unitary n) :
    (∃ a ∈ circuits V p, ∃ b ∈ circuits V q, a.prod⁻¹ * U = b.prod) ↔ U ∈ S V (p + q) := by
  rw [qc_mem_S]
  constructor
  · rintro ⟨a, ha, b, hb, hab⟩
    rw [qc_mem_circuits] at ha hb
    refine ⟨a ++ b, by simp [ha.1, hb.1], ?_, ?_⟩
    · intro W hW
      rcases List.mem_append.1 hW with h | h
      · exact ha.2 W h
      · exact hb.2 W h
    · rw [List.prod_append, ← hab, mul_inv_cancel_left]
  · rintro ⟨c, hlen, hall, rfl⟩
    refine ⟨c.take p, ?_, c.drop p, ?_, ?_⟩
    · rw [qc_mem_circuits]
      exact ⟨by simp [hlen], fun W hW => hall W (List.mem_of_mem_take hW)⟩
    · rw [qc_mem_circuits]
      exact ⟨by simp [hlen], fun W hW => hall W (List.mem_of_mem_drop hW)⟩
    · rw [inv_mul_eq_iff_eq_mul, ← List.prod_append, List.take_append_drop]
theorem qc_iteration_tests {n : ℕ} (V : Finset (Unitary n)) (U : Unitary n) (i : ℕ) (hi : 1 ≤ i) :
    (mitmStep V U i = none ↔ U ∉ S V (2 * i - 1) ∧ U ∉ S V (2 * i)) ∧
    ∀ c, mitmStep V U i = some c →
      (∀ W ∈ c, W ∈ V) ∧ c.prod = U ∧
      (U ∈ S V (2 * i - 1) → c.length = 2 * i - 1) ∧
      (U ∉ S V (2 * i - 1) → c.length = 2 * i) := by
  have e1 := qc_split V (i - 1) i U
  have e2 := qc_split V i i U
  rw [show i - 1 + i = 2 * i - 1 by omega] at e1
  rw [show i + i = 2 * i by omega] at e2
  -- generic fact about a chosen pair
  have gen : ∀ p q (h : ∃ a ∈ circuits V p, ∃ b ∈ circuits V q, a.prod⁻¹ * U = b.prod),
      let c := Classical.choose h ++ Classical.choose (Classical.choose_spec h).2
      (∀ W ∈ c, W ∈ V) ∧ c.prod = U ∧ c.length = p + q := by
    intro p q h
    obtain ⟨ha, hrest⟩ := Classical.choose_spec h
    obtain ⟨hb, hab⟩ := Classical.choose_spec hrest
    rw [qc_mem_circuits] at ha hb
    refine ⟨?_, ?_, ?_⟩
    · intro W hW
      rcases List.mem_append.1 hW with h' | h'
      · exact ha.2 W h'
      · exact hb.2 W h'
    · rw [List.prod_append, ← hab, mul_inv_cancel_left]
    · rw [List.length_append, ha.1, hb.1]
  constructor
  · unfold mitmStep
    split_ifs with h1 h2
    · simp only [reduceCtorEq, false_iff, not_and, not_not]
      intro h; exact absurd (e1.1 h1) h
    · simp only [reduceCtorEq, false_iff, not_and, not_not]
      intro _; exact e2.1 h2
    · simp only [true_iff]
      exact ⟨fun h => h1 (e1.2 h), fun h => h2 (e2.2 h)⟩
  · intro c hc
    unfold mitmStep at hc
    split_ifs at hc with h1 h2
    · obtain ⟨g1, g2, g3⟩ := gen _ _ h1
      simp only [Option.some.injEq] at hc
      subst hc
      refine ⟨g1, g2, fun _ => by rw [g3]; omega, fun h => absurd (e1.1 h1) h⟩
    · obtain ⟨g1, g2, g3⟩ := gen _ _ h2
      simp only [Option.some.injEq] at hc
      subst hc
      refine ⟨g1, g2, fun h => absurd (e1.2 h) h1, fun _ => by rw [g3]; omega⟩
theorem qc_terminates {n : ℕ} (V : Finset (Unitary n)) (U : Unitary n) (l : ℕ) :
    (∀ d : ℕ, 1 ≤ d → d ≤ 2 * ((l + 1) / 2) → U ∈ S V d →
        (∀ d' : ℕ, 1 ≤ d' → d' < d → U ∉ S V d') →
        ∃ c, mitmFactor V U l = some c ∧ c.length = d ∧ (∀ W ∈ c, W ∈ V) ∧ c.prod = U) ∧
    ((∀ d : ℕ, 1 ≤ d → d ≤ 2 * ((l + 1) / 2) → U ∉ S V d) → mitmFactor V U l = none) := by
  set K := (l + 1) / 2 with hK
  constructor
  · intro d hd1 hdK hUd hmin
    set i0 := (d + 1) / 2 with hi0
    have hi01 : 1 ≤ i0 := by omega
    have hi0K : i0 ≤ K := by omega
    have hpre : ∀ i ∈ List.range' 1 (i0 - 1), mitmStep V U i = none := by
      intro i hi
      rw [List.mem_range'_1] at hi
      have := (qc_iteration_tests V U i hi.1).1
      rw [this]
      exact ⟨hmin _ (by omega) (by omega), hmin _ (by omega) (by omega)⟩
    have hT := qc_iteration_tests V U i0 hi01
    obtain ⟨c, hc⟩ : ∃ c, mitmStep V U i0 = some c := by
      rcases h : mitmStep V U i0 with _ | c
      · exfalso
        obtain ⟨h1, h2⟩ := hT.1.1 h
        rcases (by omega : d = 2 * i0 - 1 ∨ d = 2 * i0) with hd | hd
        · exact h1 (hd ▸ hUd)
        · exact h2 (hd ▸ hUd)
      · exact ⟨c, rfl⟩
    obtain ⟨g1, g2, g3, g4⟩ := hT.2 c hc
    refine ⟨c, ?_, ?_, g1, g2⟩
    · unfold mitmFactor
      have hsplit : List.range' 1 K = List.range' 1 (i0 - 1) ++ (i0 :: List.range' (i0 + 1) (K - i0)) := by
        have gen : ∀ j K : ℕ, j + 1 ≤ K →
            List.range' 1 K = List.range' 1 j ++ ((j + 1) :: List.range' (j + 1 + 1) (K - (j + 1))) := by
          intro j K hjK
          rw [← List.range'_succ, show j + 1 = 1 + j by omega, List.range'_append_1]
          congr 1; omega
        have := gen (i0 - 1) K (by omega)
        rw [show i0 - 1 + 1 = i0 by omega] at this
        exact this
      rw [← hK, hsplit, List.findSome?_append, List.findSome?_eq_none_iff.2 hpre, Option.none_or,
        List.findSome?_cons, hc]
    · rcases (by omega : d = 2 * i0 - 1 ∨ d = 2 * i0) with hd | hd
      · rw [g3 (hd ▸ hUd), hd]
      · rw [g4 (hmin _ (by omega) (by omega)), hd]
  · intro hnone
    unfold mitmFactor
    rw [← hK, List.findSome?_eq_none_iff]
    intro i hi
    rw [List.mem_range'_1] at hi
    rw [(qc_iteration_tests V U i hi.1).1]
    exact ⟨hnone _ (by omega) (by omega), hnone _ (by omega) (by omega)⟩
theorem qc_card_S_le {n : ℕ} (V : Finset (Unitary n)) (i : ℕ) :
    (S V i).card ≤ V.card ^ i := by
  induction i with
  | zero => simp [S]
  | succ i ih =>
    simp only [S]
    calc ((V ×ˢ S V i).image (fun p => p.1 * p.2)).card ≤ (V ×ˢ S V i).card :=
          Finset.card_image_le
      _ = V.card * (S V i).card := Finset.card_product _ _
      _ ≤ V.card * V.card ^ i := Nat.mul_le_mul_left _ ih
      _ = V.card ^ (i + 1) := by ring

theorem qc_geo (m : ℝ) (k : ℕ) : (m - 1) * ∑ i ∈ Finset.Icc 1 k, m ^ i = m ^ (k + 1) - m := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_Icc_succ_top (by omega), mul_add, ih]
    ring

theorem qc_stop_le {n : ℕ} (V : Finset (Unitary n)) (U : Unitary n) (l : ℕ) :
    mitmStop V U l ≤ (l + 1) / 2 := by
  unfold mitmStop
  rcases h : (List.range' 1 ((l + 1) / 2)).find? (fun i => (mitmStep V U i).isSome) with _ | x
  · simp
  · have hx := List.mem_of_find?_eq_some h
    rw [List.mem_range'_1] at hx
    simp only [Option.getD_some]
    omega

theorem qc_logb_card_le (b : ℕ) (x : ℝ) (hx : 1 ≤ x) (hb : (b : ℝ) ≤ x) :
    0 ≤ Real.logb 2 (b : ℝ) ∧ Real.logb 2 (b : ℝ) ≤ Real.logb 2 x := by
  rcases Nat.eq_zero_or_pos b with h0 | hpos
  · subst h0
    simp only [Nat.cast_zero, Real.logb_zero, le_refl, true_and]
    exact Real.logb_nonneg (by norm_num) hx
  · have h1 : (1 : ℝ) ≤ b := by exact_mod_cast hpos
    exact ⟨Real.logb_nonneg (by norm_num) h1,
      Real.logb_le_logb_of_le (by norm_num) (by linarith) hb⟩

theorem solution {n : ℕ} (V : Finset (Unitary n)) (U : Unitary n) (l : ℕ) :
    (mitmFactor V U l = none ↔ ∀ d : ℕ, 1 ≤ d → d ≤ 2 * ((l + 1) / 2) → U ∉ S V d) ∧
    (Even l → (mitmFactor V U l = none ↔ ∀ d : ℕ, 1 ≤ d → d ≤ l → U ∉ S V d)) ∧
    (∀ c, mitmFactor V U l = some c →
        (∀ W ∈ c, W ∈ V) ∧ c.prod = U ∧ 1 ≤ c.length ∧ c.length ≤ 2 * ((l + 1) / 2) ∧
        ∀ c' : List (Unitary n), (∀ W ∈ c', W ∈ V) → c'.prod = U → 1 ≤ c'.length →
          c.length ≤ c'.length) ∧
    (2 ≤ V.card →
      mitmCost V U l ≤
        8 * (V.card : ℝ) ^ ((l + 1) / 2) * Real.logb 2 ((V.card : ℝ) ^ ((l + 1) / 2))) := by
  classical
  obtain ⟨T1, T2⟩ := qc_terminates V U l
  set K := (l + 1) / 2 with hK
  -- minimal depth extraction
  have hmin : ∀ (hex : ∃ d, 1 ≤ d ∧ d ≤ 2 * K ∧ U ∈ S V d),
      ∃ c, mitmFactor V U l = some c ∧ c.length = Nat.find hex ∧ (∀ W ∈ c, W ∈ V) ∧ c.prod = U := by
    intro hex
    obtain ⟨h1, h2, h3⟩ := Nat.find_spec hex
    apply T1 _ h1 h2 h3
    intro d' hd' hlt hUd'
    exact Nat.find_min hex hlt ⟨hd', by omega, hUd'⟩
  have P1 : mitmFactor V U l = none ↔ ∀ d : ℕ, 1 ≤ d → d ≤ 2 * K → U ∉ S V d := by
    constructor
    · intro hnone d hd1 hd2 hUd
      obtain ⟨c, hc, -⟩ := hmin ⟨d, hd1, hd2, hUd⟩
      rw [hnone] at hc; exact absurd hc (by simp)
    · exact T2
  refine ⟨P1, ?_, ?_, ?_⟩
  · intro hl
    obtain ⟨r, hr⟩ := hl
    rw [show 2 * K = l by omega] at P1
    exact P1
  · intro c hc
    have hex : ∃ d, 1 ≤ d ∧ d ≤ 2 * K ∧ U ∈ S V d := by
      by_contra hne
      push_neg at hne
      have := P1.2 (fun d h1 h2 => hne d h1 h2)
      rw [this] at hc; exact absurd hc (by simp)
    obtain ⟨c0, hc0, hlen, hV0, hprod0⟩ := hmin hex
    rw [hc] at hc0
    simp only [Option.some.injEq] at hc0
    subst hc0
    obtain ⟨s1, s2, -⟩ := Nat.find_spec hex
    refine ⟨hV0, hprod0, by omega, by omega, ?_⟩
    intro c' hc'V hc'p hc'l
    have hU' : U ∈ S V c'.length := (qc_mem_S V _ U).2 ⟨c', rfl, hc'V, hc'p⟩
    rw [hlen]
    rcases le_or_gt c'.length (2 * K) with hle | hgt
    · exact Nat.find_min' hex ⟨hc'l, hle, hU'⟩
    · omega
  · intro hV2
    set m : ℝ := (V.card : ℝ) with hmdef
    have hm2 : (2 : ℝ) ≤ m := by rw [hmdef]; exact_mod_cast hV2
    have hm1 : (1 : ℝ) ≤ m := by linarith
    set LK : ℝ := Real.logb 2 (m ^ K) with hLK
    have hterm : ∀ i ∈ Finset.Icc 1 K,
        (((V.card : ℝ) * (S V (i - 1)).card)
          + ((S V i).card : ℝ) * Real.logb 2 ((S V i).card)
          + (((S V (i - 1)).card : ℝ) + (S V i).card) * Real.logb 2 ((S V i).card))
        ≤ 4 * LK * m ^ i := by
      intro i hi
      rw [Finset.mem_Icc] at hi
      have ha : ((S V (i - 1)).card : ℝ) ≤ m ^ (i - 1) := by
        rw [hmdef]; exact_mod_cast qc_card_S_le V (i - 1)
      have hb : ((S V i).card : ℝ) ≤ m ^ i := by
        rw [hmdef]; exact_mod_cast qc_card_S_le V i
      have hmi1 : (1 : ℝ) ≤ m ^ i := one_le_pow₀ hm1
      obtain ⟨hL0, hLi⟩ := qc_logb_card_le _ _ hmi1 hb
      have hLiK : Real.logb 2 (m ^ i) ≤ LK :=
        Real.logb_le_logb_of_le (by norm_num) (by linarith) (pow_le_pow_right₀ hm1 hi.2)
      have hLb : Real.logb 2 ((S V i).card : ℝ) ≤ LK := hLi.trans hLiK
      have hLK1 : 1 ≤ LK := by
        have : Real.logb 2 (m ^ 1) ≤ LK :=
          Real.logb_le_logb_of_le (by norm_num) (by norm_num; linarith) (pow_le_pow_right₀ hm1 (by omega))
        have h2 : (1 : ℝ) ≤ Real.logb 2 (m ^ 1) := by
          rw [pow_one, Real.le_logb_iff_rpow_le (by norm_num) (by linarith)]
          simpa using hm2
        linarith
      have hmm : m * m ^ (i - 1) = m ^ i := by
        rw [← pow_succ']; congr 1; omega
      have hpm : m ^ (i - 1) ≤ m ^ i := pow_le_pow_right₀ hm1 (by omega)
      have ha0 : (0 : ℝ) ≤ (S V (i - 1)).card := Nat.cast_nonneg _
      have hb0 : (0 : ℝ) ≤ (S V i).card := Nat.cast_nonneg _
      have hmi0 : (0 : ℝ) ≤ m ^ i := by linarith
      have e1 : (V.card : ℝ) * (S V (i - 1)).card ≤ LK * m ^ i := by
        rw [← hmdef]
        calc m * (S V (i - 1)).card ≤ m * m ^ (i - 1) := mul_le_mul_of_nonneg_left ha (by linarith)
          _ = m ^ i := hmm
          _ = 1 * m ^ i := by ring
          _ ≤ LK * m ^ i := mul_le_mul_of_nonneg_right hLK1 hmi0
      have e2 : ((S V i).card : ℝ) * Real.logb 2 ((S V i).card) ≤ LK * m ^ i := by
        calc ((S V i).card : ℝ) * Real.logb 2 ((S V i).card) ≤ m ^ i * LK :=
              mul_le_mul hb hLb hL0 hmi0
          _ = LK * m ^ i := by ring
      have e3 : (((S V (i - 1)).card : ℝ) + (S V i).card) * Real.logb 2 ((S V i).card)
          ≤ 2 * LK * m ^ i := by
        calc (((S V (i - 1)).card : ℝ) + (S V i).card) * Real.logb 2 ((S V i).card)
            ≤ (m ^ i + m ^ i) * LK := mul_le_mul (by linarith) hLb hL0 (by linarith)
          _ = 2 * LK * m ^ i := by ring
      linarith
    have hstop := qc_stop_le V U l
    rw [← hK] at hstop
    unfold mitmCost
    have hLK0 : 0 ≤ LK := Real.logb_nonneg (by norm_num) (one_le_pow₀ hm1)
    calc _ ≤ ∑ i ∈ Finset.Icc 1 (mitmStop V U l), 4 * LK * m ^ i := by
          apply Finset.sum_le_sum
          intro i hi
          apply hterm
          rw [Finset.mem_Icc] at hi ⊢; omega
      _ ≤ ∑ i ∈ Finset.Icc 1 K, 4 * LK * m ^ i := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro i hi; rw [Finset.mem_Icc] at hi ⊢; omega
          · intro i _ _; have : (0 : ℝ) ≤ m ^ i := by positivity
            positivity
      _ = 4 * LK * ∑ i ∈ Finset.Icc 1 K, m ^ i := by rw [Finset.mul_sum]
      _ ≤ 4 * LK * (2 * m ^ K) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          have hg := qc_geo m K
          have hpos : (0 : ℝ) < m - 1 := by linarith
          have hsum0 : 0 ≤ ∑ i ∈ Finset.Icc 1 K, m ^ i := by
            apply Finset.sum_nonneg; intro i _; positivity
          -- (m-1) Σ = m^(K+1) - m ≤ 2 (m-1) m^K  since m^(K+1) = m * m^K and m ≥ 2
          have hmK : (1 : ℝ) ≤ m ^ K := one_le_pow₀ hm1
          have : (m - 1) * ∑ i ∈ Finset.Icc 1 K, m ^ i ≤ (m - 1) * (2 * m ^ K) := by
            rw [hg, pow_succ]
            nlinarith
          exact le_of_mul_le_mul_left this hpos
      _ = 8 * m ^ K * LK := by ring
