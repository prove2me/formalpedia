-- Prove2me | solution 1 for RiskUncSets.Distortion.theorem_4_2
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T19:10:58.387714+00:00
-- url     : https://prove2.me/submissions/e0da4228-8795-4774-935d-72b7b6917b6c

import Mathlib
import Definitions.Def_RiskUncSets_Distortion_Setting

open RiskUncSets.Distortion Finset MeasureTheory



/-- rearrangement: antitone weights, sorted (monotone) arrangement is maximal for `∑ q_i (-X_i)`. -/
theorem ru83_rearr {N : ℕ} (q X : Fin N → ℝ) (hq : Antitone q) (π σ : Equiv.Perm (Fin N))
    (hπ : Monotone (X ∘ π)) :
    ∑ i, q i * (-X (σ i)) ≤ ∑ i, q i * (-X (π i)) := by
  have hg : Antitone (fun i => -X (π i)) := fun a b hab => by
    have := hπ hab; simp only [Function.comp] at this; linarith
  have hmv : Monovary q (fun i => -X (π i)) := hq.monovary hg
  have := hmv.sum_mul_comp_perm_le_sum_mul (σ := σ.trans π.symm)
  simpa using this

theorem ru83_reindex {N : ℕ} (f h : Fin N → ℝ) (σ : Equiv.Perm (Fin N)) :
    ∑ i, f (σ i) * h i = ∑ j, f j * h (σ.symm j) := by
  rw [← Equiv.sum_comp σ.symm]; simp

theorem ru83_muQ_generates {N : ℕ} (q : Fin N → ℝ) (hq : q ∈ restrictedSimplex N) :
    Generates (Set.range fun σ : Equiv.Perm (Fin N) => q ∘ σ) (muQ q) := by
  obtain ⟨⟨hq0, hq1⟩, hqa⟩ := hq
  refine ⟨?_, fun X => ?_⟩
  · rintro _ ⟨σ, rfl⟩
    refine ⟨fun i => hq0 _, ?_⟩
    simp only [Function.comp]
    rw [Equiv.sum_comp σ q, hq1]
  · have hτ : Monotone (X ∘ Tuple.sort X) := Tuple.monotone_sort X
    have hS : muQ q X = ∑ i, q i * (-X (Tuple.sort X i)) := by
      simp [muQ, mul_neg, sum_neg_distrib]
    refine ⟨?_, ?_⟩
    · rintro _ ⟨_, ⟨σ, rfl⟩, rfl⟩
      simp only [Function.comp]
      rw [ru83_reindex q (fun i => -X i) σ, hS]
      exact ru83_rearr q X hqa _ _ hτ
    · intro b hb
      apply hb
      refine ⟨q ∘ (Tuple.sort X).symm, ⟨(Tuple.sort X).symm, rfl⟩, ?_⟩
      simp only [Function.comp]
      rw [ru83_reindex q (fun i => -X i) (Tuple.sort X).symm, hS]
      simp



theorem ru83_w_facts {N : ℕ} (hN : 0 < N) (α : ℝ) (hα : α ∈ Set.Ioc (0 : ℝ) 1) :
    (∀ i, 0 ≤ cvarWeight N α i) ∧ (∀ i, cvarWeight N α i ≤ 1 / ((N : ℝ) * α)) ∧
      Antitone (cvarWeight N α) ∧ ∑ i, cvarWeight N α i = 1 := by
  obtain ⟨hα0, hα1⟩ := hα
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  set a : ℝ := (N : ℝ) * α with ha
  have ha0 : 0 < a := mul_pos hNr hα0
  have haN : a ≤ N := by rw [ha]; nlinarith
  set k := ⌊a⌋₊ with hk
  have hka : (k : ℝ) ≤ a := Nat.floor_le ha0.le
  have hak : a < k + 1 := Nat.lt_floor_add_one a
  have hkN : k ≤ N := by
    have : (k : ℝ) ≤ N := hka.trans haN
    exact_mod_cast this
  have hc : 0 < 1 / a := by positivity
  have hr0 : 0 ≤ (a - k) / a := div_nonneg (by linarith) ha0.le
  have hr1 : (a - k) / a ≤ 1 / a := div_le_div_of_nonneg_right (by linarith) ha0.le
  have hw : ∀ i : Fin N, cvarWeight N α i =
      if (i : ℕ) + 1 ≤ k then 1 / a else if (i : ℕ) = k then (a - k) / a else 0 := fun i => rfl
  refine ⟨fun i => ?_, fun i => ?_, fun i j hij => ?_, ?_⟩
  · rw [hw]; split_ifs <;> linarith
  · rw [hw]; split_ifs <;> linarith
  · rw [hw, hw]
    have : (i : ℕ) ≤ j := hij
    split_ifs <;> first | linarith | omega
  · have hsum : ∑ i : Fin N, cvarWeight N α i = ∑ n ∈ range N,
        (if n + 1 ≤ k then 1 / a else if n = k then (a - k) / a else 0) :=
      Fin.sum_univ_eq_sum_range (fun n => if n + 1 ≤ k then 1 / a else if n = k then (a - k) / a else 0) N
    rw [hsum]
    have hfirst : ∀ m, m ≤ k → ∑ n ∈ range m,
        (if n + 1 ≤ k then 1 / a else if n = k then (a - k) / a else 0) = m * (1 / a) := by
      intro m hm
      rw [sum_congr rfl (g := fun _ => 1 / a)]
      · simp
      · intro n hn; rw [mem_range] at hn; rw [if_pos (by omega)]
    rcases Nat.lt_or_ge k N with hlt | hge
    · obtain ⟨d, hd⟩ : ∃ d, N = (k + 1) + d := ⟨N - (k+1), by omega⟩
      rw [hd, sum_range_add, sum_range_succ, hfirst k le_rfl]
      rw [sum_eq_zero (fun x _ => by rw [if_neg (by omega), if_neg (by omega)])]
      rw [if_neg (by omega), if_pos rfl]
      field_simp; ring
    · have hkN' : k = N := le_antisymm hkN hge
      rw [hfirst N (by omega)]
      have : a = N := le_antisymm haN (by rw [← hkN']; exact hka)
      rw [this]; field_simp



theorem ru83_cvar_lower {N : ℕ} (α : ℝ) (hα : 0 < α) (X q : Fin N → ℝ)
    (hq : q ∈ stdSimplex ℝ (Fin N)) (hqc : ∀ i, q i ≤ 1 / ((N : ℝ) * α)) (v : ℝ) :
    ∑ i, q i * (-X i) ≤ v + (1 / α) * ∑ i, uniform N i * max (-v - X i) 0 := by
  obtain ⟨hq0, hq1⟩ := hq
  have hc : 1 / ((N : ℝ) * α) = (1 / α) * (1 / (N : ℝ)) := by
    rw [mul_comm (N : ℝ) α]; field_simp
  have key : ∀ i, q i * (-X i) ≤ q i * v + (1 / α) * (uniform N i * max (-v - X i) 0) := by
    intro i
    have h1 : q i * (-X i - v) ≤ q i * max (-v - X i) 0 :=
      mul_le_mul_of_nonneg_left (by rw [le_max_iff]; left; linarith) (hq0 i)
    have h2 : q i * max (-v - X i) 0 ≤ (1 / α) * (1 / (N : ℝ)) * max (-v - X i) 0 :=
      mul_le_mul_of_nonneg_right (hc ▸ hqc i) (le_max_right _ _)
    simp only [uniform]
    nlinarith
  calc ∑ i, q i * (-X i) ≤ ∑ i, (q i * v + (1 / α) * (uniform N i * max (-v - X i) 0)) :=
        sum_le_sum fun i _ => key i
    _ = v + (1 / α) * ∑ i, uniform N i * max (-v - X i) 0 := by
        rw [sum_add_distrib, ← sum_mul, hq1, mul_sum]; ring

theorem ru83_cvar_main {N : ℕ} (hN : 0 < N) (α : ℝ) (hα : α ∈ Set.Ioc (0 : ℝ) 1)
    (X : Fin N → ℝ) :
    IsLUB ((fun q : Fin N → ℝ => ∑ i, q i * (-X i)) ''
        {q | q ∈ stdSimplex ℝ (Fin N) ∧ ∀ i, q i ≤ 1 / ((N : ℝ) * α)})
        (cvar (uniform N) α X) ∧
      cvar (uniform N) α X = -∑ i, cvarWeight N α i * X (Tuple.sort X i) ∧
      cvarWeight N α ∈ restrictedSimplex N := by
  obtain ⟨hw0, hwc, hwa, hw1⟩ := ru83_w_facts hN α hα
  obtain ⟨hα0, hα1⟩ := hα
  set w := cvarWeight N α with hwdef
  set τ := Tuple.sort X with hτdef
  set S := -∑ i, w i * X (τ i) with hSdef
  set F : ℝ → ℝ := fun v => v + (1 / α) * ∑ i, uniform N i * max (-v - X i) 0 with hF
  have hcv : cvar (uniform N) α X = ⨅ v, F v := rfl
  -- q* attains S
  set qs : Fin N → ℝ := fun i => w (τ.symm i) with hqs
  have hqs_mem : qs ∈ {q | q ∈ stdSimplex ℝ (Fin N) ∧ ∀ i, q i ≤ 1 / ((N : ℝ) * α)} := by
    refine ⟨⟨fun i => hw0 _, ?_⟩, fun i => hwc _⟩
    simp only [hqs]; rw [Equiv.sum_comp τ.symm w, hw1]
  have hqs_val : ∑ i, qs i * (-X i) = S := by
    simp only [hqs]
    rw [ru83_reindex w (fun i => -X i) τ.symm]
    simp [hSdef, mul_neg, sum_neg_distrib]
  -- F v* = S
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  set a : ℝ := (N : ℝ) * α with ha
  set k := ⌊a⌋₊ with hk
  have hmN : min k (N - 1) < N := by omega
  set m : Fin N := ⟨min k (N - 1), hmN⟩ with hm
  set Y : Fin N → ℝ := fun j => -X (τ j) with hY
  have hYa : Antitone Y := fun i j hij => by
    have := Tuple.monotone_sort X hij; simp only [Function.comp] at this
    simp only [hY]; linarith
  have hterm : ∀ j : Fin N, (1 / α) * (uniform N j * max (Y j - Y m) 0) = w j * (Y j - Y m) := by
    intro j
    have hwj : w j = if (j : ℕ) + 1 ≤ k then 1 / a else if (j : ℕ) = k then (a - k) / a else 0 := rfl
    have hc : (1 / α) * (1 / (N : ℝ)) = 1 / a := by rw [ha]; field_simp
    simp only [uniform]
    rcases lt_trichotomy j m with hjm | hjm | hjm
    · have hle : Y m ≤ Y j := hYa hjm.le
      have hjk : (j : ℕ) + 1 ≤ k := by
        have : (j : ℕ) < min k (N - 1) := hjm
        omega
      rw [hwj, if_pos hjk, max_eq_left (by linarith), ← hc]; ring
    · subst hjm; simp
    · have hle : Y j ≤ Y m := hYa hjm.le
      have hjk : k < (j : ℕ) := by
        have : min k (N - 1) < (j : ℕ) := hjm
        have : (j : ℕ) < N := j.2
        omega
      rw [hwj, if_neg (by omega), if_neg (by omega), max_eq_right (by linarith)]; ring
  have hFm : F (Y m) = S := by
    simp only [hF]
    have : ∀ i, -Y m - X i = Y (τ.symm i) - Y m := fun i => by simp [hY]; ring
    simp_rw [this]
    rw [mul_sum]
    rw [← Equiv.sum_comp τ (fun i => (1 / α) * (uniform N i * max (Y (τ.symm i) - Y m) 0))]
    have h2 : ∀ j, (1 / α) * (uniform N (τ j) * max (Y (τ.symm (τ j)) - Y m) 0)
        = w j * (Y j - Y m) := fun j => by
      rw [Equiv.symm_apply_apply]; simpa [uniform] using hterm j
    simp_rw [h2]
    simp only [mul_sub, sum_sub_distrib, ← sum_mul, hw1, hSdef, hY, mul_neg, sum_neg_distrib]
    ring
  have hlow : ∀ v, S ≤ F v := fun v => by
    rw [← hqs_val]; exact ru83_cvar_lower α hα0 X qs hqs_mem.1 hqs_mem.2 v
  have hbdd : BddBelow (Set.range F) := ⟨S, by rintro _ ⟨v, rfl⟩; exact hlow v⟩
  have hcvS : cvar (uniform N) α X = S := by
    rw [hcv]
    exact le_antisymm (hFm ▸ ciInf_le hbdd (Y m)) (le_ciInf hlow)
  refine ⟨?_, hcvS, ⟨⟨hw0, hw1⟩, hwa⟩⟩
  rw [hcvS]
  refine IsGreatest.isLUB ⟨⟨qs, hqs_mem, hqs_val⟩, ?_⟩
  rintro _ ⟨q, hq, rfl⟩
  rw [← hFm]
  exact ru83_cvar_lower α hα0 X q hq.1 hq.2 _



theorem ru83_gen_le {N : ℕ} {Q : Set (Fin N → ℝ)} {μ : (Fin N → ℝ) → ℝ} (h : Generates Q μ)
    (X : Fin N → ℝ) {q : Fin N → ℝ} (hq : q ∈ Q) : ∑ i, q i * (-X i) ≤ μ X :=
  (h.2 X).1 ⟨q, hq, rfl⟩

theorem ru83_gen_ub {N : ℕ} {Q : Set (Fin N → ℝ)} {μ : (Fin N → ℝ) → ℝ} (h : Generates Q μ)
    (X : Fin N → ℝ) (c : ℝ) (hc : ∀ q ∈ Q, ∑ i, q i * (-X i) ≤ c) : μ X ≤ c :=
  (h.2 X).2 (by rintro _ ⟨q, hq, rfl⟩; exact hc q hq)

theorem ru83_gen_nonempty {N : ℕ} {Q : Set (Fin N → ℝ)} {μ : (Fin N → ℝ) → ℝ}
    (h : Generates Q μ) : Q.Nonempty := by
  by_contra hQ
  rw [Set.not_nonempty_iff_eq_empty] at hQ
  have := ru83_gen_ub h 0 (μ 0 - 1) (by simp [hQ])
  linarith

theorem ru83_gen_coherent {N : ℕ} {Q : Set (Fin N → ℝ)} {μ : (Fin N → ℝ) → ℝ}
    (h : Generates Q μ) : IsCoherent μ := by
  obtain ⟨q0, hq0⟩ := ru83_gen_nonempty h
  have hsum : ∀ q ∈ Q, ∑ i, q i = 1 := fun q hq => (h.1 hq).2
  have hnn : ∀ q ∈ Q, ∀ i, 0 ≤ q i := fun q hq => (h.1 hq).1
  refine ⟨⟨fun X Y hXY => ?_, fun X c => ?_⟩, fun X Y t ht0 ht1 => ?_, fun X t ht => ?_⟩
  · refine ru83_gen_ub h X _ fun q hq => le_trans ?_ (ru83_gen_le h Y hq)
    exact sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (by linarith [hXY i]) (hnn q hq i)
  · have hv : ∀ q ∈ Q, ∑ i, q i * (-(X i + c)) = ∑ i, q i * (-X i) - c := fun q hq => by
      simp only [neg_add, mul_add, sum_add_distrib, ← sum_mul, hsum q hq]; ring
    apply le_antisymm
    · refine ru83_gen_ub h _ _ fun q hq => ?_
      rw [hv q hq]; linarith [ru83_gen_le h X hq]
    · have : μ X ≤ μ (fun i => X i + c) + c := ru83_gen_ub h X _ fun q hq => by
        have := ru83_gen_le h (fun i => X i + c) hq
        rw [hv q hq] at this; linarith
      linarith
  · refine ru83_gen_ub h _ _ fun q hq => ?_
    have e : ∑ i, q i * (-(t • X + (1 - t) • Y) i) =
        t * ∑ i, q i * (-X i) + (1 - t) * ∑ i, q i * (-Y i) := by
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_sum, ← sum_add_distrib]
      refine sum_congr rfl fun i _ => by ring
    rw [e]
    have h1 := ru83_gen_le h X hq
    have h2 := ru83_gen_le h Y hq
    nlinarith
  · have e : ∀ q : Fin N → ℝ, ∑ i, q i * (-(t • X) i) = t * ∑ i, q i * (-X i) := fun q => by
      simp only [Pi.smul_apply, smul_eq_mul, mul_sum]
      refine sum_congr rfl fun i _ => by ring
    rcases ht.eq_or_lt with rfl | htp
    · simp only [zero_mul]
      apply le_antisymm
      · exact ru83_gen_ub h _ _ fun q hq => by rw [e]; simp
      · have := ru83_gen_le h ((0:ℝ) • X) hq0; rw [e] at this; simpa using this
    · apply le_antisymm
      · exact ru83_gen_ub h _ _ fun q hq => by
          rw [e]; exact mul_le_mul_of_nonneg_left (ru83_gen_le h X hq) ht
      · have : μ X ≤ (1 / t) * μ (t • X) := ru83_gen_ub h X _ fun q hq => by
          have := ru83_gen_le h (t • X) hq
          rw [e] at this
          rw [one_div, ← div_eq_inv_mul, le_div_iff₀ htp]; linarith
        have h2 := mul_le_mul_of_nonneg_left this ht
        rw [← mul_assoc, mul_one_div_cancel htp.ne', one_mul] at h2
        exact h2



theorem ru83_count_perm {N : ℕ} (X : Fin N → ℝ) (σ : Equiv.Perm (Fin N)) (t : ℝ) :
    (univ.filter (fun i => X (σ i) ≤ t)).card = (univ.filter (fun i => X i ≤ t)).card := by
  rw [card_filter, card_filter]
  exact Equiv.sum_comp σ (fun i => if X i ≤ t then 1 else 0)

theorem ru83_sameDist_iff {N : ℕ} (hN : 0 < N) (X Y : Fin N → ℝ) :
    SameDistribution (uniform N) X Y ↔ ∀ t, (univ.filter (fun i => X i ≤ t)).card =
      (univ.filter (fun i => Y i ≤ t)).card := by
  have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  simp only [SameDistribution, uniform, sum_const, nsmul_eq_mul]
  constructor
  · intro h t; have := h t
    have h2 := mul_right_cancel₀ (one_div_ne_zero hNr) this
    exact_mod_cast h2
  · intro h t; rw [h t]

theorem ru83_law_perm {N : ℕ} (hN : 0 < N) {μ : (Fin N → ℝ) → ℝ}
    (h : IsLawInvariant (uniform N) μ) (X : Fin N → ℝ) (σ : Equiv.Perm (Fin N)) :
    μ (X ∘ σ) = μ X :=
  h _ _ ((ru83_sameDist_iff hN _ _).2 fun t => ru83_count_perm X σ t)

/-- two monotone tuples with equal counting functions are equal -/
theorem ru83_mono_eq_aux {N : ℕ} (a b : Fin N → ℝ) (ha : Monotone a) (hb : Monotone b)
    (k : Fin N) (hlt : ∀ i < k, a i = b i) (hk : a k < b k) :
    (univ.filter (fun i => a i ≤ a k)).card ≠ (univ.filter (fun i => b i ≤ a k)).card := by
  have h1 : Iic k ⊆ univ.filter (fun i => a i ≤ a k) := fun i hi => by
    simp only [mem_Iic] at hi; simp [ha hi]
  have h2 : univ.filter (fun i => b i ≤ a k) ⊆ Iio k := fun i hi => by
    simp only [mem_filter, mem_univ, true_and] at hi
    simp only [mem_Iio]
    by_contra hc; push_neg at hc
    have := hb hc; linarith
  have c1 := card_le_card h1
  have c2 := card_le_card h2
  rw [Fin.card_Iic] at c1; rw [Fin.card_Iio] at c2
  omega

theorem ru83_mono_eq {N : ℕ} (a b : Fin N → ℝ) (ha : Monotone a) (hb : Monotone b)
    (h : ∀ t, (univ.filter (fun i => a i ≤ t)).card = (univ.filter (fun i => b i ≤ t)).card) :
    a = b := by
  by_contra hne
  have hs : (univ.filter (fun i => a i ≠ b i)).Nonempty := by
    obtain ⟨i, hi⟩ := Function.ne_iff.1 hne; exact ⟨i, by simp [hi]⟩
  set k := (univ.filter (fun i => a i ≠ b i)).min' hs
  have hkm : a k ≠ b k := by
    have := min'_mem _ hs; simpa using this
  have hlt : ∀ i < k, a i = b i := fun i hi => by
    by_contra hc
    have := min'_le (univ.filter (fun i => a i ≠ b i)) i (by simp [hc])
    exact absurd hi (not_lt.2 this)
  rcases lt_or_gt_of_ne hkm with hk | hk
  · exact ru83_mono_eq_aux a b ha hb k hlt hk (h _)
  · exact ru83_mono_eq_aux b a hb ha k (fun i hi => (hlt i hi).symm) hk (h _).symm

theorem ru83_muQ_eq_of_mono {N : ℕ} (q X : Fin N → ℝ) (π : Equiv.Perm (Fin N))
    (hπ : Monotone (X ∘ π)) : muQ q X = -∑ i, q i * X (π i) := by
  have := Tuple.comp_sort_eq_comp_iff_monotone.2 hπ
  simp only [muQ]
  congr 1
  refine sum_congr rfl fun i _ => ?_
  have := congrFun this i
  simp only [Function.comp] at this
  rw [this]

theorem ru83_muQ_law {N : ℕ} (hN : 0 < N) (q : Fin N → ℝ) : IsLawInvariant (uniform N) (muQ q) := by
  intro X Y hXY
  have hc := (ru83_sameDist_iff hN X Y).1 hXY
  have heq : X ∘ Tuple.sort X = Y ∘ Tuple.sort Y := by
    refine ru83_mono_eq _ _ (Tuple.monotone_sort X) (Tuple.monotone_sort Y) fun t => ?_
    have := ru83_count_perm X (Tuple.sort X) t
    have := ru83_count_perm Y (Tuple.sort Y) t
    simp only [Function.comp]
    rw [ru83_count_perm X, ru83_count_perm Y, hc t]
  simp only [muQ]
  congr 1
  refine sum_congr rfl fun i _ => ?_
  have := congrFun heq i
  simp only [Function.comp] at this
  rw [this]

theorem ru83_common_sort {N : ℕ} (X Y : Fin N → ℝ) (h : Comonotone X Y) :
    ∃ π : Equiv.Perm (Fin N), Monotone (X ∘ π) ∧ Monotone (Y ∘ π) := by
  set f : Fin N → ℝ ×ₗ ℝ := fun i => toLex (X i, Y i)
  refine ⟨Tuple.sort f, fun i j hij => ?_, fun i j hij => ?_⟩
  · have := Prod.Lex.monotone_fst _ _ (Tuple.monotone_sort f hij)
    simpa [f] using this
  · have := Prod.Lex.le_iff.1 (Tuple.monotone_sort f hij)
    simp only [Function.comp, f, ofLex_toLex] at this ⊢
    rcases this with h1 | ⟨_, h2⟩
    · have := h (Tuple.sort f i) (Tuple.sort f j)
      by_contra hc; push_neg at hc
      nlinarith
    · exact h2

theorem ru83_muQ_comon {N : ℕ} (q : Fin N → ℝ) : IsComonotonic (muQ q) := by
  intro X Y h
  obtain ⟨π, hX, hY⟩ := ru83_common_sort X Y h
  have hXY : Monotone ((X + Y) ∘ π) := fun i j hij => by
    have := hX hij; have := hY hij; simp only [Function.comp, Pi.add_apply] at *; linarith
  rw [ru83_muQ_eq_of_mono q X π hX, ru83_muQ_eq_of_mono q Y π hY, ru83_muQ_eq_of_mono q _ π hXY]
  simp only [Pi.add_apply, mul_add, sum_add_distrib]; ring

theorem ru83_muQ_distortion {N : ℕ} (hN : 0 < N) (q : Fin N → ℝ) (hq : q ∈ restrictedSimplex N) :
    IsDistortion (uniform N) (muQ q) :=
  ⟨ru83_gen_coherent (ru83_muQ_generates q hq), ru83_muQ_comon q, ru83_muQ_law hN q⟩



theorem ru83_mono_comon {N : ℕ} (A B : Fin N → ℝ) (hA : Monotone A) (hB : Monotone B) :
    Comonotone A B := by
  intro ω ω'
  rcases le_total ω ω' with h | h
  · have := hA h; have := hB h; nlinarith
  · have := hA h; have := hB h; nlinarith

/-- indicator of the index-upper set `{j | k ≤ j}` -/
noncomputable def ru83E (N k : ℕ) : Fin N → ℝ := fun j => if k ≤ (j : ℕ) then 1 else 0

theorem ru83E_mono (N k : ℕ) : Monotone (ru83E N k) := fun i j hij => by
  have : (i : ℕ) ≤ j := hij
  simp only [ru83E]; split_ifs <;> first | omega | norm_num

theorem ru83_distortion_muQ {N : ℕ} (hN : 0 < N) (μ : (Fin N → ℝ) → ℝ)
    (hD : IsDistortion (uniform N) μ) : ∃ q ∈ restrictedSimplex N, ∀ X, μ X = muQ q X := by
  obtain ⟨⟨⟨hmono, htrans⟩, hconv, hhom⟩, hcom, hlaw⟩ := hD
  have μ0 : μ 0 = 0 := by
    have := hhom 0 0 le_rfl; simpa using this
  have μc : ∀ c : ℝ, μ (fun _ => c) = -c := fun c => by
    have := htrans 0 c; simp only [Pi.zero_apply, zero_add] at this; rw [this, μ0]; ring
  have hsum_mono : ∀ (W : ℕ → Fin N → ℝ) (n : ℕ), (∀ k < n, Monotone (W k)) →
      Monotone (∑ k ∈ range n, W k) := by
    intro W n hW i j hij
    simp only [Finset.sum_apply]
    exact sum_le_sum fun k hk => hW k (mem_range.1 hk) hij
  have hadd : ∀ (W : ℕ → Fin N → ℝ) (n : ℕ), (∀ k < n, Monotone (W k)) →
      μ (∑ k ∈ range n, W k) = ∑ k ∈ range n, μ (W k) := by
    intro W n hW
    induction n with
    | zero => simp [μ0]
    | succ n ih =>
      rw [sum_range_succ, sum_range_succ,
        hcom _ _ (ru83_mono_comon _ _ (hsum_mono W n fun k hk => hW k (by omega)) (hW n (by omega))),
        ih fun k hk => hW k (by omega)]
  set φ : ℕ → ℝ := fun k => -μ (ru83E N k) with hφ
  set Q : ℕ → ℝ := fun n => φ n - φ (n + 1) with hQ
  have hE0 : ru83E N 0 = fun _ => 1 := by funext j; simp [ru83E]
  have hEN : ru83E N N = 0 := by funext j; simp [ru83E, j.2]
  have φ0 : φ 0 = 1 := by simp [hφ, hE0, μc]
  have φN : φ N = 0 := by simp [hφ, hEN, μ0]
  have hφanti : ∀ n, φ (n + 1) ≤ φ n := fun n => by
    simp only [hφ, neg_le_neg_iff]
    exact hmono _ _ fun i => by simp only [ru83E]; split_ifs <;> first | omega | norm_num
  -- formula for monotone Z
  have hmain : ∀ Z : Fin N → ℝ, Monotone Z → μ Z = -∑ i : Fin N, Q i * Z i := by
    intro Z hZ
    set Z' : ℕ → ℝ := fun n => if h : n < N then Z ⟨n, h⟩ else 0 with hZ'
    set d : ℕ → ℝ := fun k => Z' k - (if k = 0 then 0 else Z' (k - 1)) with hd
    set W : ℕ → Fin N → ℝ := fun k j => d k * ru83E N k j with hW
    have hdecomp : Z = ∑ k ∈ range N, W k := by
      funext j
      simp only [Finset.sum_apply, hW, ru83E, mul_ite, mul_one, mul_zero]
      rw [← sum_filter]
      have hf : (range N).filter (fun k => k ≤ (j : ℕ)) = range ((j : ℕ) + 1) := by
        ext k; simp only [mem_filter, mem_range]; have := j.2; omega
      rw [hf]
      have tele : ∀ m, m < N → ∑ x ∈ range (m + 1), d x = Z' m := by
        intro m
        induction m with
        | zero => intro _; simp [hd]
        | succ m ih =>
          intro hm
          rw [sum_range_succ, ih (by omega)]
          simp [hd]
      rw [tele j j.2]
      simp [hZ', j.2]
    have hdpos : ∀ k, 0 < k → k < N → 0 ≤ d k := by
      intro k hkpos hk
      simp only [hd, if_neg hkpos.ne', hZ', dif_pos hk, dif_pos (show k - 1 < N by omega)]
      have := hZ (show (⟨k - 1, by omega⟩ : Fin N) ≤ ⟨k, hk⟩ from by
        show k - 1 ≤ k; omega)
      linarith
    have hWmono : ∀ k < N, Monotone (W k) := by
      intro k hk
      rcases Nat.eq_zero_or_pos k with rfl | hkpos
      · intro i j _; simp [hW, hE0]
      · intro i j hij
        exact mul_le_mul_of_nonneg_left (ru83E_mono N k hij) (hdpos k hkpos hk)
    have hWval : ∀ k < N, μ (W k) = -(d k * φ k) := by
      intro k hk
      rcases Nat.eq_zero_or_pos k with rfl | hkpos
      · have : W 0 = fun _ => d 0 := by funext j; simp [hW, hE0]
        rw [this, μc, φ0]; ring
      · have : W k = d k • ru83E N k := by funext j; simp [hW]
        rw [this, hhom _ _ (hdpos k hkpos hk)]; simp [hφ]
    have hμZ : μ Z = -∑ k ∈ range N, d k * φ k := by
      conv_lhs => rw [hdecomp]
      rw [hadd W N hWmono, ← sum_neg_distrib]
      exact sum_congr rfl fun k hk => hWval k (mem_range.1 hk)
    have abel : ∀ n, ∑ k ∈ range n, d k * φ k =
        ∑ i ∈ range n, Q i * Z' i + φ n * (if n = 0 then 0 else Z' (n - 1)) := by
      intro n
      induction n with
      | zero => simp
      | succ n ih =>
        rw [sum_range_succ, ih, sum_range_succ]
        simp only [hd, hQ, if_neg (Nat.succ_ne_zero n), Nat.add_sub_cancel]
        ring
    have hfin : ∑ i : Fin N, Q i * Z i = ∑ i ∈ range N, Q i * Z' i := by
      rw [← Fin.sum_univ_eq_sum_range (fun i => Q i * Z' i) N]
      exact sum_congr rfl fun i _ => by simp [hZ', i.2]
    rw [hμZ, abel N, φN, hfin]; simp
  have hsubadd : ∀ A B : Fin N → ℝ, μ (A + B) ≤ μ A + μ B := by
    intro A B
    have h1 := hconv A B (1/2) (by norm_num) (by norm_num)
    have h2 := hhom ((1/2:ℝ) • A + (1 - 1/2 : ℝ) • B) 2 (by norm_num)
    have : (2:ℝ) • ((1/2:ℝ) • A + (1 - 1/2 : ℝ) • B) = A + B := by
      funext i; simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
    rw [this] at h2; linarith
  have hQstep : ∀ n, n + 2 ≤ N → Q (n + 1) ≤ Q n := by
    intro n hn
    set A := ru83E N (n + 1) with hA
    set σ := Equiv.swap (⟨n, by omega⟩ : Fin N) ⟨n + 1, by omega⟩ with hσ
    have hAB : A + A ∘ σ = ru83E N n + ru83E N (n + 2) := by
      funext j
      simp only [Pi.add_apply, Function.comp, hA, ru83E]
      by_cases h1 : (j : ℕ) = n
      · have : j = ⟨n, by omega⟩ := Fin.ext h1
        rw [this, hσ, Equiv.swap_apply_left]; simp
      · by_cases h2 : (j : ℕ) = n + 1
        · have : j = ⟨n + 1, by omega⟩ := Fin.ext h2
          rw [this, hσ, Equiv.swap_apply_right]; simp
        · rw [hσ, Equiv.swap_apply_of_ne_of_ne (fun h => h1 (by rw [h])) (fun h => h2 (by rw [h]))]
          split_ifs <;> first | omega | norm_num
    have hc : μ (ru83E N n + ru83E N (n + 2)) = μ (ru83E N n) + μ (ru83E N (n + 2)) :=
      hcom _ _ (ru83_mono_comon _ _ (ru83E_mono _ _) (ru83E_mono _ _))
    have hs := hsubadd A (A ∘ σ)
    have hp : μ (A ∘ σ) = μ A := ru83_law_perm hN hlaw A σ
    rw [hAB, hc, hp] at hs
    simp only [hQ, hφ]
    linarith
  refine ⟨fun i => Q i, ⟨⟨fun i => ?_, ?_⟩, ?_⟩, fun X => ?_⟩
  · simp only [hQ]; linarith [hφanti i]
  · rw [Fin.sum_univ_eq_sum_range Q N]
    simp only [hQ]
    rw [sum_range_sub', φ0, φN]; ring
  · intro i j hij
    have hij' : (i : ℕ) ≤ j := hij
    have key : ∀ d m, m + d < N → Q (m + d) ≤ Q m := by
      intro d
      induction d with
      | zero => intro m _; simp
      | succ d ih =>
        intro m hm
        have := hQstep (m + d) (by omega)
        have := ih m (by omega)
        rw [← add_assoc]; linarith
    have := key ((j : ℕ) - i) i (by have := j.2; omega)
    rw [show (i : ℕ) + ((j : ℕ) - i) = j by omega] at this
    exact this
  · rw [← ru83_law_perm hN hlaw X (Tuple.sort X), hmain _ (Tuple.monotone_sort X),
      ru83_muQ_eq_of_mono _ X _ (Tuple.monotone_sort X)]
    rfl



theorem ru83_cvarWeight_qhat {N : ℕ} (hN : 0 < N) (j : Fin N) :
    cvarWeight N (((j : ℕ) + 1 : ℝ) / N) = qhat j := by
  have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have h1 : (N : ℝ) * (((j : ℕ) + 1 : ℝ) / N) = (((j : ℕ) + 1 : ℕ) : ℝ) := by
    field_simp; push_cast; ring
  funext i
  simp only [cvarWeight, qhat, h1, Nat.floor_natCast]
  have hpos : (0 : ℝ) < ((j : ℕ) + 1 : ℕ) := by positivity
  split_ifs with a b c <;> first | omega | (push_cast; ring) | simp

theorem ru83_part3 {N : ℕ} (hN : 0 < N) (j : Fin N) :
    qhat j ∈ restrictedSimplex N ∧
      ∀ X, cvar (uniform N) (((j : ℕ) + 1 : ℝ) / N) X = muQ (qhat j) X := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hα : (((j : ℕ) + 1 : ℝ) / N) ∈ Set.Ioc (0 : ℝ) 1 := by
    refine ⟨by positivity, ?_⟩
    rw [div_le_one hNr]
    have : (j : ℕ) + 1 ≤ N := j.2
    exact_mod_cast this
  have h := ru83_cvarWeight_qhat hN j
  refine ⟨?_, fun X => ?_⟩
  · have := (ru83_cvar_main hN _ hα 0).2.2; rwa [h] at this
  · rw [(ru83_cvar_main hN _ hα X).2.1, h]; rfl

theorem ru83_part2 {N : ℕ} (q : Fin N → ℝ) (hq : q ∈ restrictedSimplex N) :
    ∃ lam : Fin N → ℝ, (∀ j, 0 ≤ lam j) ∧ ∑ j, lam j = 1 ∧ q = ∑ j, lam j • qhat j := by
  obtain ⟨⟨hq0, hq1⟩, hqa⟩ := hq
  set Q : ℕ → ℝ := fun n => if h : n < N then q ⟨n, h⟩ else 0 with hQ
  have hQN : Q N = 0 := by simp [hQ]
  have hQq : ∀ i : Fin N, Q i = q i := fun i => by simp [hQ, i.2]
  have hstep : ∀ n, n < N → Q (n + 1) ≤ Q n := by
    intro n hn
    by_cases h : n + 1 < N
    · simp only [hQ, dif_pos h, dif_pos hn]
      exact hqa (show (⟨n, hn⟩ : Fin N) ≤ ⟨n + 1, h⟩ from by show n ≤ n + 1; omega)
    · simp only [hQ, dif_neg h, dif_pos hn]; exact hq0 _
  refine ⟨fun j => ((j : ℕ) + 1 : ℝ) * (Q j - Q (j + 1)), fun j => ?_, ?_, ?_⟩
  · have := hstep j j.2
    have : (0 : ℝ) ≤ (j : ℕ) + 1 := by positivity
    nlinarith
  · rw [Fin.sum_univ_eq_sum_range (fun n => ((n : ℝ) + 1) * (Q n - Q (n + 1))) N]
    have key : ∀ n, ∑ j ∈ range n, ((j : ℝ) + 1) * (Q j - Q (j + 1)) =
        ∑ j ∈ range n, Q j - n * Q n := by
      intro n
      induction n with
      | zero => simp
      | succ n ih => rw [sum_range_succ, ih, sum_range_succ]; push_cast; ring
    rw [key, hQN, ← Fin.sum_univ_eq_sum_range Q N]
    simp only [hQq, hq1]; ring
  · funext i
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, qhat]
    rw [Fin.sum_univ_eq_sum_range (fun n => ((n : ℝ) + 1) * (Q n - Q (n + 1)) *
      (if (i : ℕ) ≤ n then 1 / ((n : ℝ) + 1) else 0)) N]
    have hsimp : ∀ n : ℕ, ((n : ℝ) + 1) * (Q n - Q (n + 1)) *
        (if (i : ℕ) ≤ n then 1 / ((n : ℝ) + 1) else 0) =
        if (i : ℕ) ≤ n then Q n - Q (n + 1) else 0 := by
      intro n
      split_ifs
      · have : (n : ℝ) + 1 ≠ 0 := by positivity
        field_simp
      · simp
    simp_rw [hsimp]
    have key : ∀ n, ∑ j ∈ range n, (if (i : ℕ) ≤ j then Q j - Q (j + 1) else 0) =
        if (i : ℕ) ≤ n then Q i - Q n else 0 := by
      intro n
      induction n with
      | zero => simp only [range_zero, sum_empty]; split_ifs with h <;> simp_all
      | succ n ih =>
        rw [sum_range_succ, ih]
        by_cases h1 : (i : ℕ) ≤ n
        · rw [if_pos h1, if_pos h1, if_pos (by omega)]; ring
        · by_cases h2 : (i : ℕ) = n + 1
          · rw [if_neg h1, if_neg h1, if_pos (by omega), h2]; ring
          · rw [if_neg h1, if_neg h1, if_neg (by omega)]; ring
    rw [key, if_pos (by have := i.2; omega), hQN, hQq]; ring


theorem solution {N : ℕ} (hN : 0 < N) (μ : (Fin N → ℝ) → ℝ) (hμ : IsRiskMeasure μ) :
    (IsDistortion (uniform N) μ ↔ ∃ q ∈ restrictedSimplex N, ∀ X, μ X = muQ q X) ∧
      (∀ q ∈ restrictedSimplex N, ∃ lam : Fin N → ℝ, (∀ j, 0 ≤ lam j) ∧ ∑ j, lam j = 1 ∧
        q = ∑ j, lam j • qhat j) ∧
      (∀ j : Fin N, qhat j ∈ restrictedSimplex N ∧
        ∀ X, cvar (uniform N) (((j : ℕ) + 1 : ℝ) / N) X = muQ (qhat j) X) := by


  refine ⟨⟨fun hD => ru83_distortion_muQ hN μ hD, fun ⟨q, hq, hμq⟩ => ?_⟩,
    fun q hq => ru83_part2 q hq, fun j => ru83_part3 hN j⟩
  rw [show μ = muQ q from funext hμq]
  exact ru83_muQ_distortion hN q hq
