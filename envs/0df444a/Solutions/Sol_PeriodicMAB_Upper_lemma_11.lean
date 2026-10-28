-- Prove2me | solution 1 for PeriodicMAB.Upper.lemma_11
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-25T00:16:06.049998+00:00
-- url     : https://prove2.me/submissions/e6cbf912-484e-4295-a94a-b8ea62183b15

import Mathlib
import Definitions.Def_PeriodicMAB_Upper_Model
import Definitions.Def_PeriodicMAB_Upper_Spectral
import Definitions.Def_PeriodicMAB_Upper_Policy
import Theorems.Thm_PeriodicMAB_Upper_lemma_9
import Theorems.Thm_PeriodicMAB_Upper_lemma_10
import Theorems.Thm_PeriodicMAB_Upper_lemma_16

open MeasureTheory ProbabilityTheory Finset
open scoped NNReal
open PeriodicMAB.Upper

section Struct
variable {K : ℕ} [NeZero K] (σ δ : ℝ) (T n : ℕ) (Phat : Fin K → ℕ) (Y : Fin K → ℕ → ℝ)

lemma pmab11_tourney_true (h : List (Decision K)) (t : ℕ) :
    ∀ (f s0 : ℕ) (a : Fin K) (s : ℕ), tourney σ δ T n Phat Y h t f s0 = (a, s, true) →
      s0 ≤ s ∧ s < s0 + f ∧ σ / 2 ^ s < wHat σ δ Phat h n s a t := by
  intro f
  induction f with
  | zero =>
    intro s0 a s hdec
    simp [tourney] at hdec
  | succ f ih =>
    intro s0 a s hdec
    rw [tourney] at hdec
    split_ifs at hdec with h1 h2
    · simp only [Prod.mk.injEq] at hdec
      obtain ⟨ha, hs, -⟩ := hdec
      subst hs
      refine ⟨le_rfl, by omega, ?_⟩
      have hne : ((activeSet σ n Phat Y h t s0).filter
          (fun k => σ / 2 ^ s0 < wHat σ δ Phat h n s0 k t)).Nonempty := by
        obtain ⟨k, hk, hk'⟩ := h1
        exact ⟨k, Finset.mem_filter.mpr ⟨hk, hk'⟩⟩
      rw [← ha]
      unfold firstOf
      rw [dif_pos hne]
      exact (Finset.mem_filter.mp (Finset.min'_mem _ hne)).2
    · simp at hdec
    · obtain ⟨h1, h2, h3⟩ := ih (s0 + 1) a s hdec
      exact ⟨by omega, by omega, h3⟩

lemma pmab11_runHist_length : ∀ m, (runHist σ δ T n Phat Y m).length = m := by
  intro m
  induction m with
  | zero => rfl
  | succ m ih => simp [runHist, ih]

lemma pmab11_runHist_get : ∀ m j, 1 ≤ j → j ≤ m →
    (runHist σ δ T n Phat Y m)[j - 1]? = some (decisionAt σ δ T n Phat Y j) := by
  intro m
  induction m with
  | zero => intro j h1 h2; omega
  | succ m ih =>
    intro j h1 h2
    rw [runHist]
    rcases Nat.lt_or_ge j (m + 1) with hj | hj
    · rw [List.getElem?_append_left (by rw [pmab11_runHist_length]; omega)]
      exact ih j h1 (by omega)
    · have hj' : j = m + 1 := by omega
      subst hj'
      rw [List.getElem?_append_right (by rw [pmab11_runHist_length]; omega)]
      simp [pmab11_runHist_length, decisionAt]

lemma pmab11_mem_psiAt (s t : ℕ) (j : ℕ) :
    j ∈ psiAt σ δ T n Phat Y s t ↔
      j ∈ Icc (n * K + 1) (t - 1) ∧ (decisionAt σ δ T n Phat Y j).2 = (s, true) := by
  unfold psiAt psiSet
  rw [Finset.mem_filter]
  constructor
  · rintro ⟨hj, htag⟩
    refine ⟨hj, ?_⟩
    rw [Finset.mem_Icc] at hj
    unfold tagAt at htag
    rw [pmab11_runHist_get σ δ T n Phat Y (t - 1) j (by omega) hj.2] at htag
    simpa using htag
  · rintro ⟨hj, htag⟩
    refine ⟨hj, ?_⟩
    rw [Finset.mem_Icc] at hj
    unfold tagAt
    rw [pmab11_runHist_get σ δ T n Phat Y (t - 1) j (by omega) hj.2]
    simp [htag]

lemma pmab11_wHat_nonneg (σ δ : ℝ) (Phat : Fin K → ℕ) (h : List (Decision K)) (n s : ℕ)
    (k : Fin K) (t : ℕ) : 0 ≤ wHat σ δ Phat h n s k t := by
  unfold wHat
  simp only
  positivity

end Struct

lemma pmab11_maxMean {K : ℕ} [NeZero K] (μ : Fin K → ℕ → ℝ) (t : ℕ) :
    ∃ kstar : Fin K, (∀ k, μ k t ≤ μ kstar t) ∧ maxMean μ t = μ kstar t := by
  have hne : (univ : Finset (Fin K)).Nonempty := univ_nonempty
  obtain ⟨kstar, -, hk⟩ := Finset.exists_max_image univ (fun k => μ k t) hne
  refine ⟨kstar, fun k => hk k (mem_univ _), ?_⟩
  unfold maxMean
  rw [dif_pos hne]
  exact le_antisymm (Finset.sup'_le _ _ (fun k _ => hk k (mem_univ _)))
    (Finset.le_sup' (fun k => μ k t) (mem_univ _))

lemma pmab11_gap_le_one {K : ℕ} [NeZero K] (μ : Fin K → ℕ → ℝ) (T : ℕ) (hA1 : Assumption1 μ T)
    (a : Fin K) (t : ℕ) (ht : t ∈ Icc 1 T) : maxMean μ t - μ a t ≤ 1 ∧ 0 ≤ maxMean μ t - μ a t := by
  obtain ⟨kstar, hstar, hmax⟩ := pmab11_maxMean μ t
  rw [Finset.mem_Icc] at ht
  rw [hmax]
  have h1 := (hA1 kstar t ht.1 ht.2).2
  have h2 := (hA1 a t ht.1 ht.2).1
  exact ⟨by linarith, by linarith [hstar a]⟩

/-- Per-epoch regret bound on the event `ℰ`. -/
lemma pmab11_gap {Ω : Type*} (ε : ℕ → Ω → ℝ) (σ : ℝ≥0) (hσ : 0 < σ)
    {K : ℕ} [NeZero K] (μ : Fin K → ℕ → ℝ) (Tper : Fin K → ℕ) (T n g : ℕ) (δ : ℝ)
    (hper : ∀ k, IsMinPeriod (μ k) (Tper k)) (hA1 : Assumption1 μ T)
    (hA3 : Assumption3 T n g Tper) (hnK : n * K ≤ T) (hδ : 0 < δ) (hδ1 : δ < 1)
    (ω : Ω) (hω : ω ∈ eventE μ ε σ δ T n Tper) (t : ℕ) (ht : t ∈ Icc 1 T) :
    maxMean μ t - μ (policy σ δ T n Tper (reward μ ε ω) t) t ≤
      (if t ≤ n * K ∨ t = T then 1 else 0) + 2 * σ / Real.sqrt T +
        (2 / σ + 8) * ∑ s ∈ Icc 1 (Nat.log 2 T),
          (if t ∈ psiAt σ δ T n Tper (reward μ ε ω) s T then
            wAt σ δ T n Tper (reward μ ε ω) s (policy σ δ T n Tper (reward μ ε ω) t) t else 0) := by
  set Y := reward μ ε ω with hY
  set pol := policy σ δ T n Tper Y with hpol
  have hσR : (0 : ℝ) < σ := by exact_mod_cast hσ
  have hsum_nn : 0 ≤ ∑ s ∈ Icc 1 (Nat.log 2 T),
      (if t ∈ psiAt σ δ T n Tper Y s T then wAt σ δ T n Tper Y s (pol t) t else 0) := by
    apply Finset.sum_nonneg; intro s _; split_ifs
    · exact pmab11_wHat_nonneg _ _ _ _ _ _ _ _
    · exact le_refl _
  have hc : 0 ≤ (2 / (σ : ℝ) + 8) := by positivity
  have hsq : 0 ≤ 2 * (σ : ℝ) / Real.sqrt T := by positivity
  have hgap := pmab11_gap_le_one μ T hA1 (pol t) t ht
  by_cases hcase : t ≤ n * K ∨ t = T
  · rw [if_pos hcase]
    nlinarith [mul_nonneg hc hsum_nn]
  rw [if_neg hcase]
  push Not at hcase
  obtain ⟨hcase1, hcase2⟩ := hcase
  have htI : t ∈ Icc (n * K + 1) T := by rw [Finset.mem_Icc] at ht ⊢; omega
  obtain ⟨kstar, hstar, hmax⟩ := pmab11_maxMean μ t
  rcases hdec : decisionAt σ δ T n Tper Y t with ⟨a, s, b⟩
  have hpa : pol t = a := by rw [hpol, policy, hdec]
  have L := lemma_10 ε σ hσ μ Tper T n g δ hper hA1 hA3 hnK hδ hδ1 ω hω t htI a s b hdec kstar hstar
  rw [hmax, hpa]
  rw [hpa] at hsum_nn
  cases b with
  | false =>
    have := L.2.2.2 rfl
    nlinarith [mul_nonneg hc hsum_nn]
  | true =>
    -- the decision came from the tournament, in round `s ∈ [1, S]`, with a wide width
    have hdec' : tourney σ δ T n Tper Y (runHist σ δ T n Tper Y (t - 1)) t (Nat.log 2 T) 1 =
        (a, s, true) := by
      rw [← hdec, decisionAt, decision, if_neg (by omega)]
    obtain ⟨hs1, hsS, hw⟩ := pmab11_tourney_true σ δ T n Tper Y _ t _ _ a s hdec'
    have hwAt : σ / 2 ^ s < wAt σ δ T n Tper Y s a t := hw
    have hmem : t ∈ psiAt σ δ T n Tper Y s T := by
      rw [pmab11_mem_psiAt]
      refine ⟨by rw [Finset.mem_Icc] at htI ⊢; omega, by rw [hdec]⟩
    have hsI : s ∈ Icc 1 (Nat.log 2 T) := by rw [Finset.mem_Icc]; omega
    have hsingle : wAt σ δ T n Tper Y s a t ≤ ∑ s' ∈ Icc 1 (Nat.log 2 T),
        (if t ∈ psiAt σ δ T n Tper Y s' T then wAt σ δ T n Tper Y s' a t else 0) := by
      have := Finset.single_le_sum (f := fun s' => if t ∈ psiAt σ δ T n Tper Y s' T then
          wAt σ δ T n Tper Y s' a t else 0) (fun s' _ => by
            split_ifs
            · exact pmab11_wHat_nonneg _ _ _ _ _ _ _ _
            · exact le_refl _) hsI
      simpa [hmem] using this
    have hw0 : 0 ≤ wAt σ δ T n Tper Y s a t := pmab11_wHat_nonneg _ _ _ _ _ _ _ _
    have hgapc : μ kstar t - μ a t ≤ (2 / (σ : ℝ) + 8) * wAt σ δ T n Tper Y s a t := by
      rcases Nat.lt_or_ge s 2 with hs | hs
      · have hs1' : s = 1 := by omega
        subst hs1'
        have := L.2.1 rfl rfl
        have h2 : (1 : ℝ) < 2 / σ * wAt σ δ T n Tper Y 1 a t := by
          rw [pow_one] at hwAt
          rw [div_mul_eq_mul_div, lt_div_iff₀ hσR]
          linarith
        nlinarith
      · have := L.2.2.1 rfl hs
        have h2 : 8 * (σ : ℝ) / 2 ^ s < 8 * wAt σ δ T n Tper Y s a t := by
          rw [mul_div_assoc]; linarith
        have h3 : 0 ≤ 2 / (σ : ℝ) * wAt σ δ T n Tper Y s a t := by positivity
        nlinarith
    nlinarith [mul_le_mul_of_nonneg_left hsingle hc]

lemma pmab11_arith {K : ℕ} [NeZero K] (T : ℕ) (Tper : Fin K → ℕ) (μ : Fin K → ℕ → ℝ)
    (hper : ∀ k, IsMinPeriod (μ k) (Tper k))
    (hA3 : Assumption3 T (nPar T K) (gPar (nPar T K)) Tper) :
    (7 : ℝ) ≤ nPar T K ∧ (K : ℝ) * (nPar T K) ^ 2 ≤ T ∧ (K : ℝ) ≤ effArms Tper ∧
      (49 : ℝ) ≤ T ∧ 1 ≤ Real.log T ∧ 1 ≤ Real.log (T / effArms Tper) ∧
      (nPar T K : ℝ) * K ≤ Real.sqrt T * Real.sqrt K := by
  set n := nPar T K with hn
  set g := gPar n with hg
  set d := effArms Tper with hd
  have hKpos : 0 < K := Nat.pos_of_ne_zero (NeZero.ne K)
  have hKR : (0 : ℝ) < K := by exact_mod_cast hKpos
  have hK1 : (1 : ℝ) ≤ K := by exact_mod_cast hKpos
  obtain ⟨hT4K, hg2, hsqg, hTk⟩ := hA3
  have hTk1 : ∀ k, (1 : ℝ) ≤ Tper k := fun k => by exact_mod_cast (hper k).1
  have hgR : (2 : ℝ) ≤ g := by exact_mod_cast hg2
  have h2gn : 2 * (g : ℝ) < n := by
    have h1 := hTk1 0
    have : (1 : ℝ) < n / (2 * g) := lt_of_le_of_lt h1 (hTk 0)
    rwa [one_lt_div (by positivity)] at this
  have hng : (n : ℝ) ≤ (g : ℝ) ^ 2 := by
    have h0 : (0:ℝ) ≤ n := by positivity
    calc (n : ℝ) = Real.sqrt n ^ 2 := (Real.sq_sqrt h0).symm
      _ ≤ (g : ℝ) ^ 2 := by gcongr
  have hn7 : (7 : ℝ) ≤ n := by
    have h2gn' : 2 * g < n := by exact_mod_cast h2gn
    have hng' : n ≤ g ^ 2 := by exact_mod_cast hng
    have : 7 ≤ n := by
      by_contra hc
      push Not at hc
      have : g = 2 := by omega
      rw [this] at hng' h2gn'
      omega
    exact_mod_cast this
  have hn_le : (n : ℝ) ≤ Real.sqrt ((T : ℝ) / K) := Nat.floor_le (Real.sqrt_nonneg _)
  have hKn2 : (K : ℝ) * n ^ 2 ≤ T := by
    have : (n : ℝ) ^ 2 ≤ (T : ℝ) / K := by
      calc (n : ℝ) ^ 2 ≤ Real.sqrt ((T : ℝ) / K) ^ 2 := by gcongr
        _ = (T : ℝ) / K := Real.sq_sqrt (by positivity)
    rwa [le_div_iff₀ hKR, mul_comm] at this
  have hdK : (K : ℝ) ≤ d := by
    rw [hd, effArms]; push_cast
    calc (K : ℝ) = ∑ _k : Fin K, (1 : ℝ) := by simp
      _ ≤ ∑ k, (Tper k : ℝ) := Finset.sum_le_sum (fun k _ => hTk1 k)
  have hdlt : (d : ℝ) ≤ K * n / 4 := by
    rw [hd, effArms]; push_cast
    calc ∑ k, (Tper k : ℝ) ≤ ∑ _k : Fin K, (n : ℝ) / (2 * g) :=
          Finset.sum_le_sum (fun k _ => (hTk k).le)
      _ = K * (n / (2 * g)) := by simp
      _ ≤ K * (n / 4) := by gcongr; linarith
      _ = K * n / 4 := by ring
  have he : Real.exp 1 ≤ 3 := le_trans Real.exp_one_lt_d9.le (by norm_num)
  have h49n : (49 : ℝ) ≤ (n : ℝ) ^ 2 := by nlinarith
  have h49 : (49 : ℝ) ≤ T := by nlinarith
  have hTpos : (0 : ℝ) < T := by linarith
  have hlogT : 1 ≤ Real.log T := by
    rw [Real.le_log_iff_exp_le hTpos]; linarith
  have hlogTd : 1 ≤ Real.log (T / d) := by
    have hdpos : (0 : ℝ) < d := by linarith
    rw [Real.le_log_iff_exp_le (by positivity), le_div_iff₀ hdpos]
    nlinarith
  have hnK : (n : ℝ) * K ≤ Real.sqrt T * Real.sqrt K := by
    have hs : Real.sqrt ((T : ℝ) / K) = Real.sqrt T / Real.sqrt K := Real.sqrt_div' _ hKR.le
    rw [hs, le_div_iff₀ (Real.sqrt_pos.mpr hKR)] at hn_le
    have hKK : Real.sqrt K * Real.sqrt K = K := Real.mul_self_sqrt hKR.le
    calc (n : ℝ) * K = n * Real.sqrt K * Real.sqrt K := by rw [mul_assoc, hKK]
      _ ≤ Real.sqrt T * Real.sqrt K := by gcongr
  exact ⟨hn7, hKn2, hdK, h49, hlogT, hlogTd, hnK⟩

lemma pmab11_cs {ι : Type*} (I : Finset ι) (x : ι → ℝ) (hx : ∀ i ∈ I, 0 ≤ x i) :
    ∑ i ∈ I, Real.sqrt (x i) ≤ Real.sqrt (I.card * ∑ i ∈ I, x i) := by
  apply Real.le_sqrt_of_sq_le
  have := Finset.sum_mul_sq_le_sq_mul_sq I (fun _ => (1 : ℝ)) (fun i => Real.sqrt (x i))
  simp only [one_mul, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one] at this
  calc (∑ i ∈ I, Real.sqrt (x i)) ^ 2 ≤ I.card * ∑ i ∈ I, Real.sqrt (x i) ^ 2 := this
    _ = I.card * ∑ i ∈ I, x i := by
      congr 1; exact Finset.sum_congr rfl (fun i hi => Real.sq_sqrt (hx i hi))

/-- Regret of the oracle on `ℰ`. -/
lemma pmab11_onE {Ω : Type*} (ε : ℕ → Ω → ℝ) (σ : ℝ≥0) (hσ : 0 < σ)
    {K : ℕ} [NeZero K] (μ : Fin K → ℕ → ℝ) (Tper : Fin K → ℕ) (T n g : ℕ) (δ : ℝ)
    (hper : ∀ k, IsMinPeriod (μ k) (Tper k)) (hA1 : Assumption1 μ T)
    (hA3 : Assumption3 T n g Tper) (hnK : n * K ≤ T) (hδ : 0 < δ) (hδ1 : δ < 1)
    (ω : Ω) (hω : ω ∈ eventE μ ε σ δ T n Tper) :
    pseudoRegret μ T (policy σ δ T n Tper (reward μ ε ω)) ≤
      ((n * K : ℕ) + 1 : ℝ) + 2 * σ * Real.sqrt T +
        (2 / σ + 8) * (4 * σ * Real.sqrt (Nat.log 2 T * (T * effArms Tper *
          Real.log (8 * T / δ) * Real.log (T / effArms Tper)))) := by
  set Y := reward μ ε ω with hY
  set pol := policy σ δ T n Tper Y with hpol
  set S := Nat.log 2 T with hS
  set Ψ := fun s => psiAt σ δ T n Tper Y s T with hΨ
  set W := fun s t => wAt σ δ T n Tper Y s (pol t) t with hW
  have hσR : (0 : ℝ) < σ := by exact_mod_cast hσ
  have hc : 0 ≤ (2 / (σ : ℝ) + 8) := by positivity
  have hΨsub : ∀ s, Ψ s ⊆ Icc 1 T := by
    intro s j hj
    rw [hΨ, pmab11_mem_psiAt] at hj
    rw [Finset.mem_Icc] at hj ⊢; omega
  -- step 1: sum the per-epoch bounds
  have h1 : pseudoRegret μ T pol ≤ ∑ t ∈ Icc 1 T,
      ((if t ≤ n * K ∨ t = T then (1 : ℝ) else 0) + 2 * σ / Real.sqrt T +
        (2 / σ + 8) * ∑ s ∈ Icc 1 S, (if t ∈ Ψ s then W s t else 0)) := by
    unfold pseudoRegret
    exact Finset.sum_le_sum (fun t ht =>
      pmab11_gap ε σ hσ μ Tper T n g δ hper hA1 hA3 hnK hδ hδ1 ω hω t ht)
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_comm] at h1
  -- the three parts
  have hA : ∑ t ∈ Icc 1 T, (if t ≤ n * K ∨ t = T then (1 : ℝ) else 0) ≤ ((n * K : ℕ) + 1 : ℝ) := by
    rw [Finset.sum_boole]
    have : (Icc 1 T).filter (fun t => t ≤ n * K ∨ t = T) ⊆ Icc 1 (n * K) ∪ {T} := by
      intro t ht
      rw [Finset.mem_filter, Finset.mem_Icc] at ht
      rw [Finset.mem_union, Finset.mem_Icc, Finset.mem_singleton]
      omega
    have h := (Finset.card_le_card this).trans (Finset.card_union_le _ _)
    simp only [Nat.card_Icc, Finset.card_singleton] at h
    have : (((Icc 1 T).filter (fun t => t ≤ n * K ∨ t = T)).card : ℝ) ≤ ((n * K + 1 - 1 + 1 : ℕ) : ℝ) := by
      exact_mod_cast h
    simpa using this
  have hB : ∑ t ∈ Icc 1 T, 2 * (σ : ℝ) / Real.sqrt T = 2 * σ * Real.sqrt T := by
    rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]
    rcases Nat.eq_zero_or_pos T with hT | hT
    · simp [hT]
    have hsT : Real.sqrt T * Real.sqrt T = T := Real.mul_self_sqrt (by positivity)
    have hsTpos : 0 < Real.sqrt T := Real.sqrt_pos.mpr (by exact_mod_cast hT)
    field_simp
    push_cast
    nlinarith
  have hC : ∑ s ∈ Icc 1 S, ∑ t ∈ Icc 1 T, (if t ∈ Ψ s then W s t else 0) ≤
      4 * σ * Real.sqrt (S * (T * effArms Tper *
          Real.log (8 * T / δ) * Real.log (T / effArms Tper))) := by
    have e1 : ∀ s, ∑ t ∈ Icc 1 T, (if t ∈ Ψ s then W s t else 0) = ∑ t ∈ Ψ s, W s t := by
      intro s
      rw [Finset.sum_ite_mem, Finset.inter_eq_right.mpr (hΨsub s)]
    simp_rw [e1]
    have L16 := lemma_16 σ hσ Tper T n g δ (fun k => (hper k).1) hA3 hnK hδ hδ1 Y
    set D := (effArms Tper : ℝ) * Real.log (8 * T / δ) * Real.log (T / effArms Tper) with hD
    have hD0 : 0 ≤ D ∨ D < 0 := le_or_gt 0 D
    calc ∑ s ∈ Icc 1 S, ∑ t ∈ Ψ s, W s t
        ≤ ∑ s ∈ Icc 1 S, 4 * σ * Real.sqrt ((Ψ s).card * effArms Tper *
            Real.log (8 * T / δ) * Real.log (T / effArms Tper)) :=
          Finset.sum_le_sum (fun s hs => L16 s hs)
      _ = 4 * σ * ∑ s ∈ Icc 1 S, Real.sqrt ((Ψ s).card * D) := by
          rw [Finset.mul_sum]; congr 1; ext s; rw [hD]; ring_nf
      _ ≤ 4 * σ * Real.sqrt (S * (T * D)) := by
          gcongr
          rcases hD0 with hD0 | hD0
          · calc ∑ s ∈ Icc 1 S, Real.sqrt ((Ψ s).card * D)
                ≤ Real.sqrt ((Icc 1 S).card * ∑ s ∈ Icc 1 S, ((Ψ s).card * D)) :=
                  pmab11_cs _ _ (fun s _ => by positivity)
              _ ≤ Real.sqrt (S * (T * D)) := by
                  apply Real.sqrt_le_sqrt
                  rw [Nat.card_Icc, Nat.add_sub_cancel, ← Finset.sum_mul]
                  have hdisj : ((Icc 1 S : Finset ℕ) : Set ℕ).PairwiseDisjoint Ψ := by
                    intro s _ s' _ hss'
                    rw [Function.onFun, Finset.disjoint_left]
                    intro j hj hj'
                    rw [hΨ, pmab11_mem_psiAt] at hj hj'
                    have := hj.2.symm.trans hj'.2
                    simp at this
                    exact hss' this
                  have hcard : ∑ s ∈ Icc 1 S, ((Ψ s).card : ℝ) ≤ T := by
                    have := Finset.card_biUnion hdisj
                    have hsub : (Icc 1 S).biUnion Ψ ⊆ Icc 1 T :=
                      Finset.biUnion_subset.mpr (fun s _ => hΨsub s)
                    have h2 := Finset.card_le_card hsub
                    rw [this, Nat.card_Icc] at h2
                    exact_mod_cast (show ∑ s ∈ Icc 1 S, (Ψ s).card ≤ T by omega)
                  have hS0 : (0 : ℝ) ≤ S := by positivity
                  nlinarith [mul_le_mul_of_nonneg_right hcard hD0]
          · have : ∀ s ∈ Icc 1 S, Real.sqrt ((Ψ s).card * D) = 0 := by
              intro s _
              apply Real.sqrt_eq_zero'.mpr
              nlinarith [(by positivity : (0 : ℝ) ≤ (Ψ s).card)]
            rw [Finset.sum_congr rfl this, Finset.sum_const_zero]
            exact Real.sqrt_nonneg _
      _ = 4 * σ * Real.sqrt (S * (T * effArms Tper *
          Real.log (8 * T / δ) * Real.log (T / effArms Tper))) := by
          rw [hD]; ring_nf
  calc pseudoRegret μ T pol ≤ _ := h1
    _ ≤ _ := by
      rw [hB]
      have := mul_le_mul_of_nonneg_left hC hc
      linarith

set_option maxHeartbeats 1000000 in
theorem solution (σ : ℝ≥0) (hσ : 0 < σ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (K : ℕ) [NeZero K] (T : ℕ) (Tper : Fin K → ℕ) (μ : Fin K → ℕ → ℝ)
        {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (ε : ℕ → Ω → ℝ),
        (∀ k, IsMinPeriod (μ k) (Tper k)) → Assumption1 μ T → IsSubGaussianNoise P ε σ →
        Assumption3 T (nPar T K) (gPar (nPar T K)) Tper →
        ∃ Z : Ω → ℝ, Integrable Z P ∧
          (∀ ω, pseudoRegret μ T (oracle μ ε σ (8 / T) T (nPar T K) Tper ω) ≤ Z ω) ∧
          ∫ ω, Z ω ∂P ≤ C * Real.sqrt (T * effArms Tper * Real.log T ^ 2 *
            Real.log (T / effArms Tper)) := by
  have hσR : (0 : ℝ) < σ := by exact_mod_cast hσ
  refine ⟨34 + 66 * σ, by positivity, ?_⟩
  intro K _ T Tper μ Ω _ P _ ε hper hA1 hε hA3
  obtain ⟨hn7, hKn2, hdK, h49, hlogT, hlogTd, hnKs⟩ := pmab11_arith T Tper μ hper hA3
  set n := nPar T K with hn
  set g := gPar n with hg
  set d := effArms Tper with hd
  set S := Nat.log 2 T with hS
  set R := Real.sqrt (T * d * Real.log T ^ 2 * Real.log (T / d)) with hR
  have hKpos : 0 < K := Nat.pos_of_ne_zero (NeZero.ne K)
  have hKR : (0 : ℝ) < K := by exact_mod_cast hKpos
  have hTpos : (0 : ℝ) < T := by linarith
  have hnK : n * K ≤ T := by
    have : (n : ℝ) * K ≤ T := by nlinarith
    exact_mod_cast this
  set δ : ℝ := 8 / T with hδdef
  have hδ : 0 < δ := by positivity
  have hδ1 : δ < 1 := by rw [hδdef, div_lt_one hTpos]; linarith
  have hlog8 : Real.log (8 * T / δ) = 2 * Real.log T := by
    rw [hδdef, show (8 : ℝ) * T / (8 / T) = (T : ℝ) ^ 2 by field_simp, Real.log_pow]; push_cast; ring
  have hlog2 : (1 / 2 : ℝ) < Real.log 2 := lt_trans (by norm_num) Real.log_two_gt_d9
  have hSle : (S : ℝ) ≤ 2 * Real.log T := by
    have hT0 : T ≠ 0 := by
      intro h0; rw [h0] at hTpos; simp at hTpos
    have hpow : 2 ^ S ≤ T := Nat.pow_log_le_self 2 hT0
    have : (S : ℝ) * Real.log 2 ≤ Real.log T := by
      rw [← Real.log_pow]
      exact Real.log_le_log (by positivity) (by exact_mod_cast hpow)
    nlinarith [Real.log_pos (show (1:ℝ) < 2 by norm_num)]
  have hd0 : (0 : ℝ) ≤ d := by positivity
  have hR0 : 0 ≤ R := Real.sqrt_nonneg _
  have hRsq : R ^ 2 = T * d * Real.log T ^ 2 * Real.log (T / d) := by
    rw [hR, Real.sq_sqrt]
    have : 0 ≤ Real.log (T / d) := by linarith
    positivity
  -- lower bounds on R
  have hlogT2 : 1 ≤ Real.log T ^ 2 := by nlinarith
  have hRTK : Real.sqrt T * Real.sqrt K ≤ R := by
    rw [← Real.sqrt_mul hTpos.le]
    apply Real.le_sqrt_of_sq_le
    rw [Real.sq_sqrt (by positivity)]
    have : (K : ℝ) ≤ d * Real.log T ^ 2 * Real.log (T / d) := by
      have h1 : d ≤ d * Real.log T ^ 2 := by nlinarith
      have h2 : d * Real.log T ^ 2 ≤ d * Real.log T ^ 2 * Real.log (T / d) := by nlinarith
      linarith
    nlinarith
  have hK1 : (1 : ℝ) ≤ Real.sqrt K := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt (by exact_mod_cast hKpos)
  have hsT1 : (1 : ℝ) ≤ Real.sqrt T := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt (by linarith)
  have hRT : Real.sqrt T ≤ R := by nlinarith [Real.sqrt_nonneg (T : ℝ)]
  have hR1 : 1 ≤ R := le_trans hsT1 hRT
  have hRlog : Real.log T ≤ R := by
    apply Real.le_sqrt_of_sq_le
    have : 1 ≤ (T : ℝ) * d * Real.log (T / d) := by
      have : (1 : ℝ) ≤ d := le_trans (by exact_mod_cast hKpos) hdK
      have h2 : (1 : ℝ) ≤ T * d := by nlinarith
      nlinarith
    nlinarith
  -- the bound on `ℰ`
  set B : ℝ := ((n * K : ℕ) + 1 : ℝ) + 2 * σ * Real.sqrt T +
        (2 / σ + 8) * (4 * σ * Real.sqrt (S * (T * d *
          Real.log (8 * T / δ) * Real.log (T / d)))) with hB
  have hsq : Real.sqrt (S * (T * d * Real.log (8 * T / δ) * Real.log (T / d))) ≤ 2 * R := by
    rw [hlog8]
    apply Real.sqrt_le_iff.mpr
    refine ⟨by positivity, ?_⟩
    rw [mul_pow, hRsq]
    have hL : 0 ≤ Real.log (T / d) := by linarith
    have hX : 0 ≤ (T : ℝ) * d * (2 * Real.log T) * Real.log (T / d) := by positivity
    calc (S : ℝ) * (T * d * (2 * Real.log T) * Real.log (T / d))
        ≤ (2 * Real.log T) * (T * d * (2 * Real.log T) * Real.log (T / d)) :=
          mul_le_mul_of_nonneg_right hSle hX
      _ = 2 ^ 2 * (T * d * Real.log T ^ 2 * Real.log (T / d)) := by ring
  have hBle : B ≤ (18 + 66 * σ) * R := by
    have hnK' : (((n * K : ℕ) : ℝ)) ≤ R := by push_cast; linarith
    have h3 : (2 / (σ : ℝ) + 8) * (4 * σ * Real.sqrt (S * (T * d *
          Real.log (8 * T / δ) * Real.log (T / d)))) ≤ (2 / (σ : ℝ) + 8) * (4 * σ * (2 * R)) := by
      gcongr
    have h4 : (2 / (σ : ℝ) + 8) * (4 * σ * (2 * R)) = (16 + 64 * σ) * R := by
      field_simp; ring
    have h5 : 2 * (σ : ℝ) * Real.sqrt T ≤ 2 * σ * R := by gcongr
    rw [hB]; nlinarith
  have hB0 : 0 ≤ B := by
    rw [hB]; positivity
  -- the failure event
  have hL9 := lemma_9 P ε σ hσ hε μ Tper T n g δ hper hA3 hnK hδ hδ1
  set E := eventE μ ε σ δ T n Tper with hE
  set M := toMeasurable P Eᶜ with hM
  have hMmeas : MeasurableSet M := measurableSet_toMeasurable _ _
  have hPM : P.real M ≤ δ * S := by
    rw [measureReal_def, hM, measure_toMeasurable]
    exact ENNReal.toReal_le_of_le_ofReal (by positivity) hL9
  refine ⟨fun ω => B + M.indicator (fun _ => (T : ℝ)) ω,
    (integrable_const _).add ((integrable_const _).indicator hMmeas), ?_, ?_⟩
  · intro ω
    beta_reduce
    by_cases hω : ω ∈ E
    · have := pmab11_onE ε σ hσ μ Tper T n g δ hper hA1 hA3 hnK hδ hδ1 ω hω
      have h0 : 0 ≤ M.indicator (fun _ => (T : ℝ)) ω := by
        unfold Set.indicator; split_ifs <;> positivity
      unfold oracle
      linarith
    · have hωM : ω ∈ M := subset_toMeasurable _ _ hω
      rw [Set.indicator_of_mem hωM]
      have hle : pseudoRegret μ T (oracle μ ε σ δ T n Tper ω) ≤ T := by
        unfold pseudoRegret
        calc ∑ t ∈ Icc 1 T, (maxMean μ t - μ (oracle μ ε σ δ T n Tper ω t) t)
            ≤ ∑ t ∈ Icc 1 T, (1 : ℝ) :=
              Finset.sum_le_sum (fun t ht => (pmab11_gap_le_one μ T hA1 _ t ht).1)
          _ = T := by simp
      linarith
  · rw [integral_add (integrable_const _) ((integrable_const _).indicator hMmeas),
      integral_indicator_const _ hMmeas, smul_eq_mul, integral_const, smul_eq_mul,
      probReal_univ, one_mul]
    have h1 : P.real M * T ≤ δ * S * T := by gcongr
    have h2 : δ * S * T = 8 * S := by rw [hδdef]; field_simp
    nlinarith
