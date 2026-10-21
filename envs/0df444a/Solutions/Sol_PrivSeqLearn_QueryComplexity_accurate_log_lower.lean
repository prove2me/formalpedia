-- Prove2me | solution 1 for PrivSeqLearn.QueryComplexity.accurate_log_lower
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T18:54:39.763883+00:00
-- url     : https://prove2.me/submissions/0ad9ba5c-8401-4c54-8aed-10f7176a32db

import Mathlib
import Definitions.Def_PrivSeqLearn_QueryComplexity_Setting

set_option autoImplicit false
open PrivSeqLearn.QueryComplexity

open Classical in
/-- number of queries at positions `≥ j` landing in `(0, δ)` -/
noncomputable def pslCnt {N : ℕ} (φ : Strategy N) (δ x : ℝ) (y : Fin φ.Ybar) (j : ℕ) : ℕ :=
  (Finset.univ.filter (fun k : Fin N => j ≤ k.val ∧ queries φ x y k ∈ Set.Ioo (0 : ℝ) δ)).card

lemma pslCnt_succ_le {N : ℕ} (φ : Strategy N) (δ x : ℝ) (y : Fin φ.Ybar) (j : ℕ) :
    pslCnt φ δ x y (j + 1) ≤ pslCnt φ δ x y j := by
  unfold pslCnt
  apply Finset.card_le_card
  intro k hk
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk ⊢
  exact ⟨by omega, hk.2⟩

lemma pslCnt_succ_add {N : ℕ} (φ : Strategy N) (δ x : ℝ) (y : Fin φ.Ybar) (j : ℕ) (hj : j < N)
    (hP : queries φ x y ⟨j, hj⟩ ∈ Set.Ioo (0 : ℝ) δ) :
    pslCnt φ δ x y (j + 1) + 1 ≤ pslCnt φ δ x y j := by
  classical
  unfold pslCnt
  have hnot : (⟨j, hj⟩ : Fin N) ∉ Finset.univ.filter
      (fun k : Fin N => j + 1 ≤ k.val ∧ queries φ x y k ∈ Set.Ioo (0 : ℝ) δ) := by
    simp
  rw [← Finset.card_insert_of_notMem hnot]
  apply Finset.card_le_card
  intro k hk
  rw [Finset.mem_insert] at hk
  rcases hk with rfl | hk
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨le_rfl, hP⟩
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk ⊢
    exact ⟨by omega, hk.2⟩

lemma pslCnt_zero {N : ℕ} (φ : Strategy N) (δ x : ℝ) (y : Fin φ.Ybar) :
    pslCnt φ δ x y 0 = {k : Fin N | queries φ x y k ∈ Set.Ioo (0 : ℝ) δ}.ncard := by
  classical
  unfold pslCnt
  rw [← Set.ncard_coe_finset]
  congr 1
  ext k
  simp

lemma psl_vol_bound {N : ℕ} (ϵ δ : ℝ) (φ : Strategy N) (hacc : IsAccurate ϵ φ)
    (hδ1 : δ ≤ 1) (y : Fin φ.Ybar) :
    ∀ d m j (h : List Bool), j + d = N →
      (∀ x ∈ Set.Ioo (0 : ℝ) δ, hist φ x y j = h → pslCnt φ δ x y j ≤ m) →
      MeasureTheory.volume {x : ℝ | x ∈ Set.Ioo (0 : ℝ) δ ∧ hist φ x y j = h} ≤
        2 ^ m * ENNReal.ofReal ϵ := by
  intro d
  induction d with
  | zero =>
    intro m j h hjN _
    have hjN' : j = N := by omega
    subst hjN'
    have hsub : {x : ℝ | x ∈ Set.Ioo (0 : ℝ) δ ∧ hist φ x y j = h} ⊆
        Set.Icc (φ.est h y - ϵ / 2) (φ.est h y + ϵ / 2) := by
      rintro x ⟨hx, hxh⟩
      have := hacc x ⟨hx.1.le, lt_of_lt_of_le hx.2 hδ1⟩ y
      have e : estimate φ x y = φ.est h y := by
        unfold estimate; rw [hxh]
      rw [e, abs_le] at this
      constructor <;> linarith [this.1, this.2]
    calc MeasureTheory.volume {x : ℝ | x ∈ Set.Ioo (0 : ℝ) δ ∧ hist φ x y j = h}
        ≤ MeasureTheory.volume (Set.Icc (φ.est h y - ϵ / 2) (φ.est h y + ϵ / 2)) :=
          MeasureTheory.measure_mono hsub
      _ = ENNReal.ofReal ϵ := by
          rw [Real.volume_Icc]; congr 1; ring
      _ ≤ 2 ^ m * ENNReal.ofReal ϵ :=
          le_mul_of_one_le_left bot_le (one_le_pow₀ (by norm_num))
  | succ d ih =>
    intro m j h hjN hcnt
    have hj : j < N := by omega
    set c := φ.query h y with hc
    have hstep : ∀ x : ℝ, hist φ x y j = h →
        hist φ x y (j + 1) = h ++ [decide (c ≤ x)] := by
      intro x hx
      show hist φ x y j ++ [decide (φ.query (hist φ x y j) y ≤ x)] = _
      rw [hx]
    have hback : ∀ (x : ℝ) (b : Bool), hist φ x y (j + 1) = h ++ [b] → hist φ x y j = h := by
      intro x b hx
      have : hist φ x y j ++ [decide (φ.query (hist φ x y j) y ≤ x)] = h ++ [b] := hx
      exact (List.append_inj' this rfl).1
    by_cases hcI : c ∈ Set.Ioo (0 : ℝ) δ
    · -- informative query
      have hinfo : ∀ x : ℝ, hist φ x y j = h → queries φ x y ⟨j, hj⟩ ∈ Set.Ioo (0 : ℝ) δ := by
        intro x hx
        show φ.query (hist φ x y j) y ∈ _
        rw [hx]; exact hcI
      cases m with
      | zero =>
        have : {x : ℝ | x ∈ Set.Ioo (0 : ℝ) δ ∧ hist φ x y j = h} = ∅ := by
          ext x
          simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and]
          intro hx hxh
          have h1 := hcnt x hx hxh
          have h2 := pslCnt_succ_add φ δ x y j hj (hinfo x hxh)
          omega
        rw [this]; simp
      | succ m' =>
        have hb : ∀ b : Bool, MeasureTheory.volume
            {x : ℝ | x ∈ Set.Ioo (0 : ℝ) δ ∧ hist φ x y (j + 1) = h ++ [b]} ≤
            2 ^ m' * ENNReal.ofReal ϵ := by
          intro b
          apply ih m' (j + 1) (h ++ [b]) (by omega)
          intro x hx hxh
          have hxj := hback x b hxh
          have h1 := hcnt x hx hxj
          have h2 := pslCnt_succ_add φ δ x y j hj (hinfo x hxj)
          omega
        have hsub : {x : ℝ | x ∈ Set.Ioo (0 : ℝ) δ ∧ hist φ x y j = h} ⊆
            {x : ℝ | x ∈ Set.Ioo (0 : ℝ) δ ∧ hist φ x y (j + 1) = h ++ [true]} ∪
            {x : ℝ | x ∈ Set.Ioo (0 : ℝ) δ ∧ hist φ x y (j + 1) = h ++ [false]} := by
          rintro x ⟨hx, hxh⟩
          simp only [Set.mem_union, Set.mem_setOf_eq]
          rw [hstep x hxh]
          cases hd : decide (c ≤ x)
          · exact Or.inr ⟨hx, rfl⟩
          · exact Or.inl ⟨hx, rfl⟩
        calc MeasureTheory.volume {x : ℝ | x ∈ Set.Ioo (0 : ℝ) δ ∧ hist φ x y j = h}
            ≤ MeasureTheory.volume ({x : ℝ | x ∈ Set.Ioo (0 : ℝ) δ ∧ hist φ x y (j + 1) = h ++ [true]} ∪
              {x : ℝ | x ∈ Set.Ioo (0 : ℝ) δ ∧ hist φ x y (j + 1) = h ++ [false]}) :=
              MeasureTheory.measure_mono hsub
          _ ≤ _ := MeasureTheory.measure_union_le _ _
          _ ≤ 2 ^ m' * ENNReal.ofReal ϵ + 2 ^ m' * ENNReal.ofReal ϵ := add_le_add (hb true) (hb false)
          _ = 2 ^ (m' + 1) * ENNReal.ofReal ϵ := by rw [pow_succ]; ring
    · -- uninformative query: the response is the same for all x ∈ (0, δ)
      have hconst : ∀ x ∈ Set.Ioo (0 : ℝ) δ, decide (c ≤ x) = decide (c ≤ 0) := by
        intro x hx
        by_cases hc0 : c ≤ 0
        · have : c ≤ x := hc0.trans hx.1.le
          simp [hc0, this]
        · have hδc : δ ≤ c := by
            by_contra hlt
            exact hcI ⟨not_le.1 hc0, not_le.1 hlt⟩
          have : ¬ c ≤ x := not_le.2 (lt_of_lt_of_le hx.2 hδc)
          simp [hc0, this]
      have hsub : {x : ℝ | x ∈ Set.Ioo (0 : ℝ) δ ∧ hist φ x y j = h} ⊆
          {x : ℝ | x ∈ Set.Ioo (0 : ℝ) δ ∧ hist φ x y (j + 1) = h ++ [decide (c ≤ 0)]} := by
        rintro x ⟨hx, hxh⟩
        refine ⟨hx, ?_⟩
        rw [hstep x hxh, hconst x hx]
      calc MeasureTheory.volume {x : ℝ | x ∈ Set.Ioo (0 : ℝ) δ ∧ hist φ x y j = h}
          ≤ MeasureTheory.volume
              {x : ℝ | x ∈ Set.Ioo (0 : ℝ) δ ∧ hist φ x y (j + 1) = h ++ [decide (c ≤ 0)]} :=
            MeasureTheory.measure_mono hsub
        _ ≤ 2 ^ m * ENNReal.ofReal ϵ := by
          apply ih m (j + 1) (h ++ [decide (c ≤ 0)]) (by omega)
          intro x hx hxh
          have hxj := hback x _ hxh
          exact (pslCnt_succ_le φ δ x y j).trans (hcnt x hx hxj)

lemma psl_lemma_7_1 {N : ℕ} (ϵ δ : ℝ) (φ : Strategy N) (hacc : IsAccurate ϵ φ) (hϵ : 0 < ϵ)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (y : Fin φ.Ybar) :
    ∃ x ∈ Set.Ioo (0 : ℝ) δ,
      ⌈Real.logb 2 (δ / ϵ)⌉₊ ≤ {k : Fin N | queries φ x y k ∈ Set.Ioo (0 : ℝ) δ}.ncard := by
  by_contra hcon
  push_neg at hcon
  have hpos : 0 < ⌈Real.logb 2 (δ / ϵ)⌉₊ := by
    have := hcon (δ / 2) ⟨by linarith, by linarith⟩
    omega
  set t := ⌈Real.logb 2 (δ / ϵ)⌉₊ with ht
  have hm : ∀ x ∈ Set.Ioo (0 : ℝ) δ, pslCnt φ δ x y 0 ≤ t - 1 := by
    intro x hx
    rw [pslCnt_zero]
    have := hcon x hx
    omega
  have hvol := psl_vol_bound ϵ δ φ hacc hδ1 y N (t - 1) 0 [] (by omega)
    (fun x hx _ => hm x hx)
  have hset : {x : ℝ | x ∈ Set.Ioo (0 : ℝ) δ ∧ hist φ x y 0 = []} = Set.Ioo 0 δ := by
    ext x; simp [hist]
  rw [hset, Real.volume_Ioo] at hvol
  have h2 : δ ≤ 2 ^ (t - 1) * ϵ := by
    have : ENNReal.ofReal (δ - 0) ≤ ENNReal.ofReal (2 ^ (t - 1) * ϵ) := by
      rw [ENNReal.ofReal_mul (by positivity)]
      simpa [ENNReal.ofReal_pow] using hvol
    rw [ENNReal.ofReal_le_ofReal_iff (by positivity)] at this
    linarith
  have h3 : δ / ϵ ≤ 2 ^ (t - 1) := by
    rw [div_le_iff₀ hϵ]; exact h2
  have h4 : Real.logb 2 (δ / ϵ) ≤ ((t - 1 : ℕ) : ℝ) := by
    rw [Real.logb_le_iff_le_rpow (by norm_num) (by positivity), Real.rpow_natCast]
    exact h3
  have h5 : ((t - 1 : ℕ) : ℝ) < Real.logb 2 (δ / ϵ) := Nat.lt_ceil.1 (by omega)
  linarith

theorem solution {N : ℕ} (ϵ : ℝ) (φ : Strategy N) (hϵ : 0 < ϵ)
    (hacc : IsAccurate ϵ φ) :
    ⌈Real.logb 2 (1 / ϵ)⌉ ≤ (N : ℤ) := by
  let y : Fin φ.Ybar := ⟨0, φ.Ybar_pos⟩
  obtain ⟨x, hx, hcnt⟩ := psl_lemma_7_1 ϵ 1 φ hacc hϵ one_pos le_rfl y
  have h1 : {k : Fin N | queries φ x y k ∈ Set.Ioo (0 : ℝ) 1}.ncard ≤ N := by
    calc _ ≤ (Set.univ : Set (Fin N)).ncard := Set.ncard_le_ncard (Set.subset_univ _)
      _ = N := by simp [Set.ncard_univ]
  have h2 : ⌈Real.logb 2 (1 / ϵ)⌉₊ ≤ N := by simpa using hcnt.trans h1
  have h3 : ⌈Real.logb 2 (1 / ϵ)⌉ ≤ (⌈Real.logb 2 (1 / ϵ)⌉₊ : ℤ) :=
    Int.ceil_le.2 (by exact_mod_cast Nat.le_ceil _)
  exact h3.trans (by exact_mod_cast h2)
