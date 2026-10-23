-- Prove2me | solution 1 for RegretBandits.Stochastic.alpha_ucb_pseudo_regret
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-22T06:49:44.854007+00:00
-- url     : https://prove2.me/submissions/2c38ec69-2097-4020-91c0-ca9de6345b67

import Mathlib
import Definitions.Def_ImprovedLinBandits_UCBDelta_armModel
import Definitions.Def_RegretBandits_Stochastic_model
import Definitions.Def_RegretBandits_Stochastic_alphaPsiUCB



namespace RegretBandits.Stochastic

open MeasureTheory ImprovedLinBandits.UCBDelta ProbabilityTheory Real Finset

lemma uc_chernoff_sum {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Y : ℕ → Ω → ℝ) (hm : ∀ k, Measurable (Y k)) (hind : iIndepFun Y P)
    (hid : ∀ k, IdentDistrib (Y k) (Y 0) P P) (l c e : ℝ) (hl : 0 ≤ l)
    (hint : Integrable (fun ω => Real.exp (l * Y 0 ω)) P) (hc : mgf (Y 0) P l ≤ Real.exp c)
    (s : ℕ) (hs : 1 ≤ s) :
    P.real {ω | (s : ℝ) * e ≤ ∑ k ∈ range s, Y k ω} ≤
      Real.exp (-(l * ((s : ℝ) * e)) + s * c) := by
  have hint' : ∀ k ∈ range s, Integrable (fun ω => Real.exp (l * Y k ω)) P := by
    intro k _
    have := (hid k).comp (measurable_const_mul l).exp
    exact (this.integrable_iff).2 hint
  have hI := hind.integrable_exp_mul_sum (t := l) hm hint'
  have h1 := measure_ge_le_exp_mul_mgf (μ := P) (X := ∑ k ∈ range s, Y k) ((s : ℝ) * e) hl hI
  have h2 : mgf (∑ k ∈ range s, Y k) P l = mgf (Y 0) P l ^ s := by
    have := mgf_sum_of_identDistrib (μ := P) (X := Y) (s := range s) (j := 0) hm hind
      (fun i _ j _ => (hid i).trans (hid j).symm) (by simp; omega) l
    simpa using this
  rw [h2] at h1
  have h3 : mgf (Y 0) P l ^ s ≤ Real.exp c ^ s :=
    pow_le_pow_left₀ (mgf_nonneg) hc s
  have h4 : {ω | (s : ℝ) * e ≤ ∑ k ∈ range s, Y k ω} =
      {ω | (s : ℝ) * e ≤ (∑ k ∈ range s, Y k) ω} := by
    ext ω; simp [Finset.sum_apply]
  rw [h4]
  calc _ ≤ _ := h1
    _ ≤ Real.exp (-l * ((s : ℝ) * e)) * Real.exp c ^ s := by gcongr
    _ = _ := by
      rw [← Real.exp_nat_mul, ← Real.exp_add]; congr 1; ring

/-- For a stochastic bandit, functions of the arm-`i` rewards are independent. -/
lemma cc_indep_arm {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) {K : ℕ}
    (X : Fin K → ℕ → Ω → ℝ) (μ : Fin K → ℝ) (hX : IsStochasticBandit P X μ) (i : Fin K)
    (f : ℝ → ℝ) (hf : Measurable f) : iIndepFun (fun k => f ∘ X i k) P := by
  have h1 : iIndepFun (fun k : ℕ => X i k) P :=
    hX.indep.precomp (g := fun k : ℕ => (i, k)) (fun a b h => by simpa using h)
  exact h1.comp (fun _ => f) (fun _ => hf)


/-- Hoeffding tail, upper deviation. -/
lemma uc_hoeff_up {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {K : ℕ} (X : Fin K → ℕ → Ω → ℝ) (μ : Fin K → ℝ)
    (hX : IsStochasticBandit P X μ)
    (hbdd : ∀ i k, ∀ᵐ ω ∂P, X i k ω ∈ Set.Icc (0 : ℝ) 1)
    (i : Fin K) (s : ℕ) (hs : 1 ≤ s) (e : ℝ) (he : 0 ≤ e) :
    P.real {ω | e ≤ sampleMean X i s ω - μ i} ≤ Real.exp (-(2 * s * e ^ 2)) := by
  have hm : ∀ k, Measurable (fun ω => X i k ω - μ i) := fun k => (hX.measurable i k).sub_const _
  have hind := cc_indep_arm P X μ hX i (fun x => x - μ i) (measurable_id.sub_const _)
  have hid : ∀ k, IdentDistrib (fun ω => X i k ω - μ i) (fun ω => X i 0 ω - μ i) P P :=
    fun k => (hX.identDistrib i k).comp (measurable_id.sub_const _)
  have hsg := hasSubgaussianMGF_of_mem_Icc (μ := P) (hX.measurable i 0).aemeasurable (hbdd i 0)
  have hmean := hX.mean i
  have hl : (0:ℝ) ≤ 4 * e := by linarith
  have hint := hsg.integrable_exp_mul (4 * e)
  have hc : mgf (fun ω => X i 0 ω - μ i) P (4 * e) ≤ Real.exp (2 * e ^ 2) := by
    have := hsg.mgf_le (4 * e)
    rw [hmean] at this
    refine this.trans (Real.exp_le_exp.2 ?_)
    simp
    nlinarith
  have key := uc_chernoff_sum P (fun k ω => X i k ω - μ i) hm hind hid (4 * e) (2 * e ^ 2) e hl
    (by simpa [hmean] using hint) hc s hs
  refine le_trans (measureReal_mono ?_) (le_trans key (le_of_eq ?_))
  · intro ω hω
    simp only [Set.mem_ofPred_eq, sampleMean] at hω ⊢
    have hs0 : (0 : ℝ) < s := by exact_mod_cast hs
    rw [Finset.sum_sub_distrib]
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    have : e + μ i ≤ (∑ k ∈ range s, X i k ω) / s := by linarith
    rw [le_div_iff₀ hs0] at this
    nlinarith
  · congr 1; ring

/-- Hoeffding tail, lower deviation. -/
lemma uc_hoeff_low {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {K : ℕ} (X : Fin K → ℕ → Ω → ℝ) (μ : Fin K → ℝ)
    (hX : IsStochasticBandit P X μ)
    (hbdd : ∀ i k, ∀ᵐ ω ∂P, X i k ω ∈ Set.Icc (0 : ℝ) 1)
    (i : Fin K) (s : ℕ) (hs : 1 ≤ s) (e : ℝ) (he : 0 ≤ e) :
    P.real {ω | e ≤ μ i - sampleMean X i s ω} ≤ Real.exp (-(2 * s * e ^ 2)) := by
  have hm : ∀ k, Measurable (fun ω => μ i - X i k ω) := fun k => measurable_const.sub (hX.measurable i k)
  have hind := cc_indep_arm P X μ hX i (fun x => μ i - x) (measurable_const.sub measurable_id)
  have hid : ∀ k, IdentDistrib (fun ω => μ i - X i k ω) (fun ω => μ i - X i 0 ω) P P :=
    fun k => (hX.identDistrib i k).comp (measurable_const.sub measurable_id)
  have hsg0 := hasSubgaussianMGF_of_mem_Icc (μ := P) (hX.measurable i 0).aemeasurable (hbdd i 0)
  have hsg := hsg0.neg
  have hmean := hX.mean i
  have hl : (0:ℝ) ≤ 4 * e := by linarith
  have hint := hsg.integrable_exp_mul (4 * e)
  have hc : mgf (fun ω => μ i - X i 0 ω) P (4 * e) ≤ Real.exp (2 * e ^ 2) := by
    have := hsg.mgf_le (4 * e)
    rw [hmean] at this
    have h2 : (fun ω => μ i - X i 0 ω) = -(fun ω => X i 0 ω - μ i) := by
      ext ω; simp
    rw [h2]
    refine this.trans (Real.exp_le_exp.2 ?_)
    simp
    nlinarith
  have key := uc_chernoff_sum P (fun k ω => μ i - X i k ω) hm hind hid (4 * e) (2 * e ^ 2) e hl
    (hint.congr (Filter.Eventually.of_forall fun ω => by simp [hmean])) hc s hs
  refine le_trans (measureReal_mono ?_) (le_trans key (le_of_eq ?_))
  · intro ω hω
    simp only [Set.mem_ofPred_eq, sampleMean] at hω ⊢
    have hs0 : (0 : ℝ) < s := by exact_mod_cast hs
    rw [Finset.sum_sub_distrib]
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    have : (∑ k ∈ range s, X i k ω) / s ≤ μ i - e := by linarith
    rw [div_le_iff₀ hs0] at this
    nlinarith
  · congr 1; ring

lemma uc_leg (ε : ℝ) : legendreFenchel (fun l => l ^ 2 / 8) ε = ((2 * ε ^ 2 : ℝ) : EReal) := by
  unfold legendreFenchel
  apply le_antisymm
  · apply iSup_le
    intro l
    exact_mod_cast (by nlinarith [sq_nonneg (l - 4 * ε)] : l * ε - l ^ 2 / 8 ≤ 2 * ε ^ 2)
  · refine le_trans (le_of_eq ?_) (le_iSup _ (4 * ε))
    congr 1; ring

lemma uc_lfInv (y : ℝ) (hy : 0 ≤ y) : lfInv (fun l => l ^ 2 / 8) y = Real.sqrt (y / 2) := by
  unfold lfInv
  have : IsLeast {ε : ℝ | 0 ≤ ε ∧ (y : EReal) ≤ legendreFenchel (fun l => l ^ 2 / 8) ε}
      (Real.sqrt (y / 2)) := by
    constructor
    · refine ⟨Real.sqrt_nonneg _, ?_⟩
      rw [uc_leg]
      have : (Real.sqrt (y / 2)) ^ 2 = y / 2 := Real.sq_sqrt (by positivity)
      exact_mod_cast (by rw [this]; linarith : y ≤ 2 * (Real.sqrt (y / 2)) ^ 2)
    · rintro ε ⟨h0, h1⟩
      rw [uc_leg] at h1
      have h2 : y ≤ 2 * ε ^ 2 := by exact_mod_cast h1
      apply Real.sqrt_le_iff.2
      exact ⟨h0, by linarith⟩
  exact this.csInf_eq


lemma uc_pull_le {Ω : Type*} {K : ℕ} (I : ℕ → Ω → Fin K) (j : Fin K) (t : ℕ) (ω : Ω) :
    pullCount I j t ω ≤ t := by
  unfold pullCount
  exact (card_filter_le _ _).trans (by simp)

lemma uc_key {Ω : Type*} {K : ℕ} (X : Fin K → ℕ → Ω → ℝ) (μ : Fin K → ℝ) (α : ℝ) (hα : 2 < α)
    (I : ℕ → Ω → Fin K) (hrun : IsAlphaPsiUCBRun (fun l => l ^ 2 / 8) α X I)
    (i istar : Fin K) (hstar : μ istar = bestMean μ) (u : ℕ) (hu : 1 ≤ u)
    (t : ℕ) (ω : Ω)
    (hsmall : ∀ s : ℕ, u ≤ s → 2 * Real.sqrt (α * Real.log ((t:ℝ)+1) / s / 2) ≤ gap μ i)
    (hI : I (t+1) ω = i) (hN : u ≤ pullCount I i t ω) :
    (∃ s ∈ Icc 1 t, Real.sqrt (α * Real.log ((t:ℝ)+1) / s / 2) ≤ μ istar - sampleMean X istar s ω) ∨
    (∃ s ∈ Icc u t, Real.sqrt (α * Real.log ((t:ℝ)+1) / s / 2) ≤ sampleMean X i s ω - μ i) := by
  obtain ⟨h1, h2⟩ := hrun ω t
  have hall : ∀ j, pullCount I j t ω ≠ 0 := by
    intro j hj
    have := h1 ⟨j, hj⟩
    rw [hI] at this
    omega
  have hidx := h2 hall istar
  rw [hI] at hidx
  have hlog : 0 ≤ Real.log ((t:ℝ) + 1) := Real.log_nonneg (by linarith [(Nat.cast_nonneg t : (0:ℝ) ≤ t)])
  have hy : ∀ j : Fin K, 0 ≤ α * Real.log ((t:ℝ) + 1) / (pullCount I j t ω : ℝ) := fun j => by
    apply div_nonneg (mul_nonneg (by linarith) hlog) (Nat.cast_nonneg _)
  unfold ucbIndex at hidx
  rw [uc_lfInv _ (hy _), uc_lfInv _ (hy _)] at hidx
  by_contra hcon
  push_neg at hcon
  obtain ⟨hA, hB⟩ := hcon
  have hA' := hA (pullCount I istar t ω) (Finset.mem_Icc.2 ⟨Nat.one_le_iff_ne_zero.2 (hall istar), uc_pull_le _ _ _ _⟩)
  have hB' := hB (pullCount I i t ω) (Finset.mem_Icc.2 ⟨hN, uc_pull_le _ _ _ _⟩)
  have hS := hsmall _ hN
  have hg : gap μ i = μ istar - μ i := by unfold gap; rw [hstar]
  rw [hg] at hS
  linarith


lemma uc_pull_strict {Ω : Type*} {K : ℕ} (I : ℕ → Ω → Fin K) (i : Fin K) (ω : Ω) (t t' : ℕ)
    (htt : t < t') (hI : I (t + 1) ω = i) :
    pullCount I i t ω + 1 ≤ pullCount I i t' ω := by
  unfold pullCount
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_of_subset]
  · exact ⟨t, by simp [hI, htt], by simp⟩
  · intro x hx
    simp only [Finset.mem_filter, Finset.mem_range] at hx ⊢
    exact ⟨by omega, hx.2⟩

lemma uc_count_pointwise {Ω : Type*} {K : ℕ} (I : ℕ → Ω → Fin K) (i : Fin K) (n u : ℕ)
    (Bad : ℕ → Set Ω) (ω : Ω)
    (hbad : ∀ t, t < n → I (t + 1) ω = i → u ≤ pullCount I i t ω → ω ∈ Bad t) :
    (pullCount I i n ω : ℝ) ≤ u + ∑ t ∈ range n, (Bad t).indicator (fun _ => (1 : ℝ)) ω := by
  classical
  set F := (range n).filter (fun t => I (t + 1) ω = i) with hF
  have hcard : pullCount I i n ω = F.card := rfl
  have hsplit := Finset.card_filter_add_card_filter_not (s := F) (fun t => pullCount I i t ω < u)
  set F1 := F.filter (fun t => pullCount I i t ω < u)
  set F2 := F.filter (fun t => ¬ pullCount I i t ω < u)
  have h1 : F1.card ≤ u := by
    have : F1.card ≤ (range u).card := by
      apply Finset.card_le_card_of_injOn (fun t => pullCount I i t ω)
      · intro t ht
        have ht := Finset.mem_filter.1 (Finset.mem_coe.1 ht)
        simp [ht.2]
      · intro t ht t' ht' h
        have ht := Finset.mem_filter.1 (Finset.mem_coe.1 ht)
        have ht' := Finset.mem_filter.1 (Finset.mem_coe.1 ht')
        simp only [F, Finset.mem_filter, Finset.mem_range] at ht ht'
        by_contra hne
        rcases lt_or_gt_of_ne hne with hlt | hlt
        · have := uc_pull_strict I i ω t t' hlt ht.1.2
          simp only at h
          omega
        · have := uc_pull_strict I i ω t' t hlt ht'.1.2
          simp only at h
          omega
    simpa using this
  have h2 : (F2.card : ℝ) ≤ ∑ t ∈ range n, (Bad t).indicator (fun _ => (1 : ℝ)) ω := by
    calc (F2.card : ℝ) = ∑ t ∈ F2, (1:ℝ) := by simp
      _ = ∑ t ∈ F2, (Bad t).indicator (fun _ => (1 : ℝ)) ω := by
        apply Finset.sum_congr rfl
        intro t ht
        simp only [F2, F, Finset.mem_filter, Finset.mem_range, not_lt] at ht
        rw [Set.indicator_of_mem (hbad t ht.1.1 ht.1.2 ht.2)]
      _ ≤ _ := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro t ht
          simp only [F2, F, Finset.mem_filter, Finset.mem_range] at ht
          simpa using ht.1.1
        · intro t _ _
          exact Set.indicator_nonneg (fun _ _ => zero_le_one) _
  rw [hcard]
  have : (F.card : ℝ) = F1.card + F2.card := by exact_mod_cast hsplit.symm
  rw [this]
  have : (F1.card : ℝ) ≤ u := by exact_mod_cast h1
  linarith

lemma uc_sum_bound (α : ℝ) (hα : 2 < α) (n : ℕ) :
    ∑ t ∈ range n, (t : ℝ) * Real.exp (-(α * Real.log ((t : ℝ) + 1))) ≤ 1 / (α - 2) := by
  have hterm : ∀ t : ℕ, (t : ℝ) * Real.exp (-(α * Real.log ((t : ℝ) + 1))) ≤ ((t : ℝ) + 1) ^ (1 - α) := by
    intro t
    have hpos : (0 : ℝ) < (t : ℝ) + 1 := by positivity
    have : Real.exp (-(α * Real.log ((t : ℝ) + 1))) = ((t : ℝ) + 1) ^ (-α) := by
      rw [Real.rpow_def_of_pos hpos]; congr 1; ring
    rw [this]
    have h2 : ((t : ℝ) + 1) ^ (1 - α) = ((t : ℝ) + 1) * ((t : ℝ) + 1) ^ (-α) := by
      rw [sub_eq_add_neg, Real.rpow_add hpos, Real.rpow_one]
    rw [h2]
    have : (0:ℝ) ≤ ((t : ℝ) + 1) ^ (-α) := by positivity
    nlinarith
  cases n with
  | zero => simp; linarith
  | succ m =>
    rw [Finset.sum_range_succ']
    simp only [Nat.cast_zero, zero_mul, add_zero]
    have h1 : ∑ i ∈ range m, ((i + 1 : ℕ) : ℝ) * Real.exp (-(α * Real.log (((i + 1 : ℕ) : ℝ) + 1)))
        ≤ ∑ i ∈ range m, (fun x : ℝ => x ^ (1 - α)) (1 + ((i + 1 : ℕ) : ℝ)) := by
      apply Finset.sum_le_sum
      intro i _
      refine (hterm (i + 1)).trans (le_of_eq ?_)
      simp only; congr 1; ring
    refine h1.trans ?_
    have hanti : AntitoneOn (fun x : ℝ => x ^ (1 - α)) (Set.Icc 1 (1 + (m : ℝ))) := by
      intro x hx y hy hxy
      exact Real.rpow_le_rpow_of_nonpos (by linarith [hx.1]) hxy (by linarith)
    refine (AntitoneOn.sum_le_integral hanti).trans ?_
    rw [integral_rpow (Or.inr ⟨by linarith, by
      rw [Set.mem_uIcc]; push_neg; constructor <;> intro h <;> [skip; skip] <;> (try linarith)⟩)]
    have hp : (0:ℝ) ≤ (1 + (m:ℝ)) ^ (1 - α + 1) := by positivity
    rw [Real.one_rpow]
    have hne : α - 2 ≠ 0 := by linarith
    have key : ((1 + (m:ℝ)) ^ (1 - α + 1) - 1) / (1 - α + 1) = (1 - (1 + (m:ℝ)) ^ (1 - α + 1)) / (α - 2) := by
      have : 1 - α + 1 = -(α - 2) := by ring
      rw [this]; field_simp; ring
    rw [key]
    exact div_le_div_of_nonneg_right (by linarith) (by linarith)

lemma uc_pull_meas {Ω : Type*} [MeasurableSpace Ω] {K : ℕ} (I : ℕ → Ω → Fin K)
    (hI : ∀ t, Measurable (I t)) (i : Fin K) (n : ℕ) :
    Measurable (fun ω => (pullCount I i n ω : ℝ)) := by
  classical
  have : (fun ω => (pullCount I i n ω : ℝ)) =
      fun ω => ∑ t ∈ range n, if I (t + 1) ω = i then (1 : ℝ) else 0 := by
    ext ω
    unfold pullCount
    rw [Finset.card_filter]
    push_cast
    rfl
  rw [this]
  apply Finset.measurable_sum
  intro t _
  exact Measurable.ite (hI (t + 1) (measurableSet_singleton i)) measurable_const measurable_const


lemma uc_sample_meas {Ω : Type*} [MeasurableSpace Ω] {K : ℕ} (X : Fin K → ℕ → Ω → ℝ)
    (hXm : ∀ i k, Measurable (X i k)) (i : Fin K) (s : ℕ) :
    Measurable (fun ω => sampleMean X i s ω) := by
  unfold sampleMean
  exact (Finset.measurable_sum _ fun k _ => hXm i k).div_const _

lemma uc_tail_term {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {K : ℕ} (X : Fin K → ℕ → Ω → ℝ) (μ : Fin K → ℝ)
    (hX : IsStochasticBandit P X μ)
    (hbdd : ∀ i k, ∀ᵐ ω ∂P, X i k ω ∈ Set.Icc (0 : ℝ) 1) (α : ℝ) (hα : 2 < α)
    (j : Fin K) (t s : ℕ) (hs : 1 ≤ s) :
    P.real {ω | Real.sqrt (α * Real.log ((t:ℝ)+1) / s / 2) ≤ μ j - sampleMean X j s ω} ≤
        Real.exp (-(α * Real.log ((t:ℝ)+1))) ∧
    P.real {ω | Real.sqrt (α * Real.log ((t:ℝ)+1) / s / 2) ≤ sampleMean X j s ω - μ j} ≤
        Real.exp (-(α * Real.log ((t:ℝ)+1))) := by
  have hs0 : (0:ℝ) < s := by exact_mod_cast hs
  have hlog : 0 ≤ Real.log ((t:ℝ) + 1) := Real.log_nonneg (by linarith [(Nat.cast_nonneg t : (0:ℝ) ≤ t)])
  have hy : 0 ≤ α * Real.log ((t:ℝ) + 1) / s / 2 := by
    have : 0 ≤ α * Real.log ((t:ℝ) + 1) := mul_nonneg (by linarith) hlog
    positivity
  have heq : 2 * (s:ℝ) * (Real.sqrt (α * Real.log ((t:ℝ)+1) / s / 2)) ^ 2 = α * Real.log ((t:ℝ)+1) := by
    rw [Real.sq_sqrt hy]; field_simp
  constructor
  · have := uc_hoeff_low P X μ hX hbdd j s hs (Real.sqrt (α * Real.log ((t:ℝ)+1) / s / 2)) (Real.sqrt_nonneg _)
    rwa [heq] at this
  · have := uc_hoeff_up P X μ hX hbdd j s hs (Real.sqrt (α * Real.log ((t:ℝ)+1) / s / 2)) (Real.sqrt_nonneg _)
    rwa [heq] at this


lemma uc_ET {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {K : ℕ} (X : Fin K → ℕ → Ω → ℝ) (μ : Fin K → ℝ)
    (hX : IsStochasticBandit P X μ)
    (hbdd : ∀ i k, ∀ᵐ ω ∂P, X i k ω ∈ Set.Icc (0 : ℝ) 1)
    (α : ℝ) (hα : 2 < α) (I : ℕ → Ω → Fin K) (hI : ∀ t, Measurable (I t))
    (hrun : IsAlphaPsiUCBRun (fun l => l ^ 2 / 8) α X I) (n : ℕ)
    (i istar : Fin K) (hstar : μ istar = bestMean μ) (hgap : 0 < gap μ i) :
    ∫ ω, (pullCount I i n ω : ℝ) ∂P ≤ 2 * α / gap μ i ^ 2 * Real.log n + α / (α - 2) := by
  classical
  set Δ := gap μ i with hΔ
  set x : ℝ := 2 * α * Real.log n / Δ ^ 2 with hx
  have hlogn : 0 ≤ Real.log (n : ℝ) := Real.log_natCast_nonneg n
  have hx0 : 0 ≤ x := by
    have : 0 ≤ 2 * α * Real.log n := mul_nonneg (by linarith) hlogn
    positivity
  set u : ℕ := max 1 ⌈x⌉₊ with hu
  have hu1 : 1 ≤ u := le_max_left _ _
  have hux : (u : ℝ) ≤ x + 1 := by
    rcases le_total 1 ⌈x⌉₊ with h | h
    · rw [hu, max_eq_right h]
      exact (Nat.ceil_lt_add_one hx0).le
    · rw [hu, max_eq_left h]
      simp
      exact hx0
  have hxu : x ≤ (u : ℝ) := (Nat.le_ceil x).trans (by exact_mod_cast le_max_right _ _)
  -- smallness
  have hsmall : ∀ t : ℕ, t < n → ∀ s : ℕ, u ≤ s →
      2 * Real.sqrt (α * Real.log ((t:ℝ)+1) / s / 2) ≤ Δ := by
    intro t ht s hs
    have hs' : (1:ℝ) ≤ s := by exact_mod_cast hu1.trans hs
    have hs0 : (0:ℝ) < s := by linarith
    have hxs : x ≤ s := hxu.trans (by exact_mod_cast hs)
    have hlogt : Real.log ((t:ℝ)+1) ≤ Real.log n := by
      apply Real.log_le_log (by positivity)
      have : t + 1 ≤ n := ht
      exact_mod_cast this
    have hΔ2 : 0 < Δ ^ 2 := by positivity
    have h1 : 2 * α * Real.log n ≤ Δ ^ 2 * s := by
      have : x * Δ ^ 2 ≤ s * Δ ^ 2 := mul_le_mul_of_nonneg_right hxs hΔ2.le
      rw [hx, div_mul_cancel₀ _ hΔ2.ne'] at this
      linarith
    have h2 : α * Real.log ((t:ℝ)+1) / s / 2 ≤ (Δ / 2) ^ 2 := by
      rw [div_div, div_le_iff₀ (by positivity)]
      nlinarith
    have := Real.sqrt_le_iff.2 ⟨by positivity, h2⟩
    linarith
  -- bad events
  let e : ℕ → ℕ → ℝ := fun t s => Real.sqrt (α * Real.log ((t:ℝ)+1) / s / 2)
  let A : ℕ → ℕ → Set Ω := fun t s => {ω | e t s ≤ μ istar - sampleMean X istar s ω}
  let B : ℕ → ℕ → Set Ω := fun t s => {ω | e t s ≤ sampleMean X i s ω - μ i}
  let Bad : ℕ → Set Ω := fun t => (⋃ s ∈ Icc 1 t, A t s) ∪ (⋃ s ∈ Icc u t, B t s)
  have hAm : ∀ t s, MeasurableSet (A t s) := fun t s =>
    measurableSet_le measurable_const (measurable_const.sub (uc_sample_meas X hX.measurable _ _))
  have hBm : ∀ t s, MeasurableSet (B t s) := fun t s =>
    measurableSet_le measurable_const ((uc_sample_meas X hX.measurable _ _).sub measurable_const)
  have hBadm : ∀ t, MeasurableSet (Bad t) := fun t =>
    (Finset.measurableSet_biUnion _ fun s _ => hAm t s).union
      (Finset.measurableSet_biUnion _ fun s _ => hBm t s)
  have hpt : ∀ ω, (pullCount I i n ω : ℝ) ≤ u + ∑ t ∈ range n, (Bad t).indicator (fun _ => (1 : ℝ)) ω := by
    intro ω
    apply uc_count_pointwise I i n u Bad ω
    intro t ht hIt hN
    rcases uc_key X μ α hα I hrun i istar hstar u hu1 t ω (hsmall t ht) hIt hN with ⟨s, hs, h⟩ | ⟨s, hs, h⟩
    · left
      simp only [Set.mem_iUnion]
      exact ⟨s, hs, h⟩
    · right
      simp only [Set.mem_iUnion]
      exact ⟨s, hs, h⟩
  have hPbad : ∀ t, P.real (Bad t) ≤ 2 * (t * Real.exp (-(α * Real.log ((t:ℝ)+1)))) := by
    intro t
    have hc : 0 ≤ Real.exp (-(α * Real.log ((t:ℝ)+1))) := (Real.exp_pos _).le
    have hA : P.real (⋃ s ∈ Icc 1 t, A t s) ≤ t * Real.exp (-(α * Real.log ((t:ℝ)+1))) := by
      refine (measureReal_biUnion_finset_le _ _).trans ?_
      calc ∑ s ∈ Icc 1 t, P.real (A t s) ≤ ∑ s ∈ Icc 1 t, Real.exp (-(α * Real.log ((t:ℝ)+1))) := by
            apply Finset.sum_le_sum
            intro s hs
            exact (uc_tail_term P X μ hX hbdd α hα istar t s (Finset.mem_Icc.1 hs).1).1
        _ = t * Real.exp (-(α * Real.log ((t:ℝ)+1))) := by simp
    have hB : P.real (⋃ s ∈ Icc u t, B t s) ≤ t * Real.exp (-(α * Real.log ((t:ℝ)+1))) := by
      refine (measureReal_biUnion_finset_le _ _).trans ?_
      calc ∑ s ∈ Icc u t, P.real (B t s) ≤ ∑ s ∈ Icc u t, Real.exp (-(α * Real.log ((t:ℝ)+1))) := by
            apply Finset.sum_le_sum
            intro s hs
            exact (uc_tail_term P X μ hX hbdd α hα i t s (hu1.trans (Finset.mem_Icc.1 hs).1)).2
        _ ≤ t * Real.exp (-(α * Real.log ((t:ℝ)+1))) := by
            rw [Finset.sum_const, nsmul_eq_mul]
            apply mul_le_mul_of_nonneg_right _ hc
            have : (Icc u t).card ≤ t := by
              have := hu1
              simp
              omega
            exact_mod_cast this
    calc P.real (Bad t) ≤ P.real (⋃ s ∈ Icc 1 t, A t s) + P.real (⋃ s ∈ Icc u t, B t s) :=
          measureReal_union_le _ _
      _ ≤ _ := by linarith
  have hint_ind : ∀ t, Integrable ((Bad t).indicator (fun _ => (1 : ℝ))) P := fun t =>
    (integrable_const (1:ℝ)).indicator (hBadm t)
  have hintsum : Integrable (fun ω => ∑ t ∈ range n, (Bad t).indicator (fun _ => (1 : ℝ)) ω) P :=
    integrable_finsetSum _ (fun t _ => hint_ind t)
  have hint_pull : Integrable (fun ω => (pullCount I i n ω : ℝ)) P := by
    refine Integrable.mono' (integrable_const (n : ℝ)) (uc_pull_meas I hI i n).aestronglyMeasurable ?_
    refine Filter.Eventually.of_forall fun ω => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _)]
    exact_mod_cast uc_pull_le I i n ω
  calc ∫ ω, (pullCount I i n ω : ℝ) ∂P
      ≤ ∫ ω, ((u : ℝ) + ∑ t ∈ range n, (Bad t).indicator (fun _ => (1 : ℝ)) ω) ∂P :=
        integral_mono hint_pull ((integrable_const _).add hintsum) hpt
    _ = u + ∑ t ∈ range n, P.real (Bad t) := by
        rw [integral_add (integrable_const _) hintsum, integral_const, integral_finsetSum _ (fun t _ => hint_ind t)]
        simp only [probReal_univ, one_smul]
        congr 1
        apply Finset.sum_congr rfl
        intro t _
        rw [integral_indicator_const _ (hBadm t)]
        simp
    _ ≤ u + ∑ t ∈ range n, 2 * (t * Real.exp (-(α * Real.log ((t:ℝ)+1)))) := by
        gcongr with t ht
        exact hPbad t
    _ ≤ (x + 1) + 2 * (1 / (α - 2)) := by
        rw [← Finset.mul_sum]
        have := uc_sum_bound α hα n
        linarith
    _ = _ := by
        have hne : α - 2 ≠ 0 := by linarith
        have hne2 : α - 2 ≠ 0 := hne
        rw [hx]
        field_simp
        ring_nf


lemma uc_pull_int {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {K : ℕ} (I : ℕ → Ω → Fin K) (hI : ∀ t, Measurable (I t)) (i : Fin K) (n : ℕ) :
    Integrable (fun ω => (pullCount I i n ω : ℝ)) P := by
  refine Integrable.mono' (integrable_const (n : ℝ)) (uc_pull_meas I hI i n).aestronglyMeasurable ?_
  refine Filter.Eventually.of_forall fun ω => ?_
  rw [Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _)]
  exact_mod_cast uc_pull_le I i n ω

lemma uc_fiber {Ω : Type*} {K : ℕ} (I : ℕ → Ω → Fin K) (ω : Ω) (n : ℕ) (g : Fin K → ℝ) :
    ∑ t ∈ range n, g (I (t + 1) ω) = ∑ i : Fin K, (pullCount I i n ω : ℝ) * g i := by
  classical
  rw [← Finset.sum_fiberwise (range n) (fun t => I (t + 1) ω) (fun t => g (I (t + 1) ω))]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_congr rfl (fun t ht => by rw [(Finset.mem_filter.1 ht).2] : ∀ t ∈ (range n).filter (fun t => I (t + 1) ω = i), g (I (t + 1) ω) = g i)]
  rw [Finset.sum_const, nsmul_eq_mul]
  unfold pullCount
  ring

lemma uc_regret_eq {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {K : ℕ} (μ : Fin K → ℝ) (I : ℕ → Ω → Fin K) (hI : ∀ t, Measurable (I t)) (n : ℕ) :
    pseudoRegretBar P μ I n = ∑ i : Fin K, gap μ i * ∫ ω, (pullCount I i n ω : ℝ) ∂P := by
  unfold pseudoRegretBar
  have h1 : ∀ ω, ∑ t ∈ range n, μ (I (t + 1) ω) = ∑ i : Fin K, (pullCount I i n ω : ℝ) * μ i :=
    fun ω => uc_fiber I ω n μ
  have h2 : ∀ ω, ∑ i : Fin K, (pullCount I i n ω : ℝ) = n := by
    intro ω
    have := uc_fiber I ω n (fun _ => 1)
    simpa using this.symm
  simp_rw [h1]
  rw [integral_finsetSum _ (fun i _ => (uc_pull_int P I hI i n).mul_const (μ i))]
  have h3 : ∑ i : Fin K, ∫ ω, (pullCount I i n ω : ℝ) ∂P = n := by
    rw [← integral_finsetSum _ (fun i _ => uc_pull_int P I hI i n)]
    simp_rw [h2]
    simp
  have h4 : (n : ℝ) * bestMean μ = ∑ i : Fin K, bestMean μ * ∫ ω, (pullCount I i n ω : ℝ) ∂P := by
    rw [← Finset.mul_sum, h3]; ring
  rw [h4, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_mul_const]
  unfold gap
  ring


theorem uc_core {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {K : ℕ} (hK : 2 ≤ K) (X : Fin K → ℕ → Ω → ℝ) (μ : Fin K → ℝ)
    (hX : IsStochasticBandit P X μ)
    (hbdd : ∀ i k, ∀ᵐ ω ∂P, X i k ω ∈ Set.Icc (0 : ℝ) 1)
    (α : ℝ) (hα : 2 < α) (I : ℕ → Ω → Fin K) (hI : ∀ t, Measurable (I t))
    (hrun : IsAlphaPsiUCBRun (fun l => l ^ 2 / 8) α X I) (n : ℕ) :
    pseudoRegretBar P μ I n ≤
      ∑ i ∈ Finset.univ.filter (fun i => 0 < gap μ i),
        (2 * α / gap μ i * Real.log (n : ℝ) + α / (α - 2)) := by
  classical
  haveI : Nonempty (Fin K) := ⟨⟨0, by omega⟩⟩
  obtain ⟨istar, histar⟩ := exists_eq_ciSup_of_finite (f := μ)
  have hstar : μ istar = bestMean μ := histar
  have hμ01 : ∀ i, 0 ≤ μ i ∧ μ i ≤ 1 := by
    intro i
    rw [← hX.mean i]
    constructor
    · exact integral_nonneg_of_ae (by filter_upwards [hbdd i 0] with ω h using h.1)
    · calc ∫ ω, X i 0 ω ∂P ≤ ∫ _ω, (1:ℝ) ∂P :=
            integral_mono_ae (hX.integrable i) (integrable_const _)
              (by filter_upwards [hbdd i 0] with ω h using h.2)
        _ = 1 := by simp
  have hgap0 : ∀ i, 0 ≤ gap μ i := by
    intro i
    unfold gap bestMean
    have := le_ciSup (Set.finite_range μ).bddAbove i
    linarith
  have hgap1 : ∀ i, gap μ i ≤ 1 := by
    intro i
    unfold gap
    rw [← hstar]
    linarith [(hμ01 i).1, (hμ01 istar).2]
  have hα0 : 0 < α - 2 := by linarith
  have hlogn : 0 ≤ Real.log (n : ℝ) := Real.log_natCast_nonneg n
  rw [uc_regret_eq P μ I hI n]
  have hET0 : ∀ i, 0 ≤ ∫ ω, (pullCount I i n ω : ℝ) ∂P := fun i =>
    integral_nonneg (fun ω => Nat.cast_nonneg _)
  calc ∑ i : Fin K, gap μ i * ∫ ω, (pullCount I i n ω : ℝ) ∂P
      = ∑ i ∈ Finset.univ.filter (fun i => 0 < gap μ i), gap μ i * ∫ ω, (pullCount I i n ω : ℝ) ∂P := by
        symm
        apply Finset.sum_subset (Finset.filter_subset _ _)
        intro i _ hi
        have : gap μ i = 0 := by
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_lt] at hi
          exact le_antisymm hi (hgap0 i)
        rw [this, zero_mul]
    _ ≤ _ := by
        apply Finset.sum_le_sum
        intro i hi
        have hgi : 0 < gap μ i := (Finset.mem_filter.1 hi).2
        have hET := uc_ET P X μ hX hbdd α hα I hI hrun n i istar hstar hgi
        calc gap μ i * ∫ ω, (pullCount I i n ω : ℝ) ∂P
            ≤ gap μ i * (2 * α / gap μ i ^ 2 * Real.log n + α / (α - 2)) :=
              mul_le_mul_of_nonneg_left hET hgi.le
          _ = 2 * α / gap μ i * Real.log n + gap μ i * (α / (α - 2)) := by
              field_simp
          _ ≤ 2 * α / gap μ i * Real.log n + α / (α - 2) := by
              have : 0 ≤ α / (α - 2) := by positivity
              have := mul_le_of_le_one_left this (hgap1 i)
              linarith

end RegretBandits.Stochastic

open RegretBandits.Stochastic
open MeasureTheory ImprovedLinBandits.UCBDelta

theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {K : ℕ} (hK : 2 ≤ K) (X : Fin K → ℕ → Ω → ℝ) (μ : Fin K → ℝ)
    (hX : IsStochasticBandit P X μ)
    (hbdd : ∀ i k, ∀ᵐ ω ∂P, X i k ω ∈ Set.Icc (0 : ℝ) 1)
    (α : ℝ) (hα : 2 < α) (I : ℕ → Ω → Fin K) (hI : ∀ t, Measurable (I t))
    (hrun : IsAlphaPsiUCBRun (fun l => l ^ 2 / 8) α X I) (n : ℕ) :
    pseudoRegretBar P μ I n ≤
      ∑ i ∈ Finset.univ.filter (fun i => 0 < gap μ i),
        (2 * α / gap μ i * Real.log (n : ℝ) + α / (α - 2)) := by
  exact uc_core P hK X μ hX hbdd α hα I hI hrun n
