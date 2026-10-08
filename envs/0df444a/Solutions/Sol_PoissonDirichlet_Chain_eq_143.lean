-- Prove2me | solution 1 for PoissonDirichlet.Chain.eq_143
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T15:48:16.766982+00:00
-- url     : https://prove2.me/submissions/637bd0bd-781c-4bcb-bf9c-dcfffbceb2c0

import Mathlib
import Definitions.Def_PoissonDirichlet_Chain_Setting
open MeasureTheory ProbabilityTheory Filter Topology


namespace PoissonDirichlet.Chain

open PoissonDirichlet.Ratio

/-- The sorting key: larger values first, ties broken by index. -/
noncomputable def rkey (x : ℕ → ℝ) (i : ℕ) : Lex (ℝ × ℕ) := toLex (-(x i), i)

lemma rkey_injective (x : ℕ → ℝ) : Function.Injective (rkey x) := by
  intro i j h
  unfold rkey at h
  have := congrArg (fun p => (ofLex p).2) h
  simpa using this

lemma rkey_lt_iff (x : ℕ → ℝ) (i j : ℕ) :
    rkey x j < rkey x i ↔ x i < x j ∨ (x j = x i ∧ j < i) := by
  unfold rkey
  rw [Prod.Lex.lt_iff]
  simp only [ofLex_toLex]
  constructor
  · rintro (h | ⟨h1, h2⟩)
    · left; linarith
    · right; exact ⟨by linarith, h2⟩
  · rintro (h | ⟨h1, h2⟩)
    · left; linarith
    · right; exact ⟨by linarith, h2⟩

/-- The set of indices sorted before `i`. -/
def rpred (x : ℕ → ℝ) (i : ℕ) : Set ℕ := {j | rkey x j < rkey x i}

lemma rpred_finite (x : ℕ → ℝ) (hx : Tendsto x atTop (𝓝 0)) (hpos : ∀ i, 0 < x i) (i : ℕ) :
    (rpred x i).Finite := by
  have h1 : ∀ᶠ j in atTop, x j < x i := hx.eventually (gt_mem_nhds (hpos i))
  rw [← Nat.cofinite_eq_atTop, Filter.eventually_cofinite] at h1
  apply (h1.union (Set.finite_Iio i)).subset
  intro j hj
  rcases (rkey_lt_iff x i j).1 hj with h | ⟨h, h'⟩
  · left; simp only [Set.mem_setOf_eq, not_lt]; exact h.le
  · right; exact h'

lemma not_mem_rpred_self (x : ℕ → ℝ) (i : ℕ) : i ∉ rpred x i := by
  simp [rpred]

/-- The rank of index `i`. -/
noncomputable def rrank (x : ℕ → ℝ) (i : ℕ) : ℕ := (rpred x i).ncard

lemma ranked_eq_of_rrank (x : ℕ → ℝ) (hx : Tendsto x atTop (𝓝 0)) (hpos : ∀ i, 0 < x i)
    (i k : ℕ) (hk : rrank x i = k) : ranked x k = x i := by
  have hfin := rpred_finite x hx hpos i
  have hmem : x i ∈ {t : ℝ | 0 ≤ t ∧ {j | t < x j}.encard ≤ k} := by
    refine ⟨(hpos i).le, ?_⟩
    have hsub : {j | x i < x j} ⊆ rpred x i := by
      intro j hj
      exact (rkey_lt_iff x i j).2 (Or.inl hj)
    calc {j | x i < x j}.encard ≤ (rpred x i).encard := Set.encard_le_encard hsub
      _ = k := by rw [hfin.cast_ncard_eq.symm]; unfold rrank at hk; rw [hk]
  have hbdd : ∀ t ∈ {t : ℝ | 0 ≤ t ∧ {j | t < x j}.encard ≤ k}, x i ≤ t := by
    intro t ht
    by_contra hlt
    push_neg at hlt
    have hsub : insert i (rpred x i) ⊆ {j | t < x j} := by
      intro j hj
      rcases hj with rfl | hj
      · exact hlt
      · rcases (rkey_lt_iff x i j).1 hj with h | ⟨h, _⟩
        · exact lt_trans hlt h
        · simp only [Set.mem_setOf_eq]; linarith
    have h1 := Set.encard_le_encard hsub
    rw [Set.encard_insert_of_notMem (not_mem_rpred_self x i), ← hfin.cast_ncard_eq] at h1
    have h2 := le_trans h1 ht.2
    unfold rrank at hk
    rw [hk] at h2
    have : ((k : ℕ∞) + 1 : ℕ∞) = ((k + 1 : ℕ) : ℕ∞) := by push_cast; rfl
    rw [this] at h2
    have := ENat.coe_le_coe.1 h2
    omega
  unfold ranked
  apply le_antisymm
  · exact csInf_le ⟨0, fun t ht => ht.1⟩ hmem
  · exact le_csInf ⟨x i, hmem⟩ hbdd

lemma rrank_lt_of_lt (x : ℕ → ℝ) (hx : Tendsto x atTop (𝓝 0)) (hpos : ∀ i, 0 < x i)
    (i j : ℕ) (h : rkey x i < rkey x j) : rrank x i < rrank x j := by
  unfold rrank
  apply Set.ncard_lt_ncard _ (rpred_finite x hx hpos j)
  constructor
  · intro l hl; exact lt_trans hl h
  · intro hsub
    exact not_mem_rpred_self x i (hsub h)

lemma rrank_injective (x : ℕ → ℝ) (hx : Tendsto x atTop (𝓝 0)) (hpos : ∀ i, 0 < x i) :
    Function.Injective (rrank x) := by
  intro i j h
  by_contra hne
  rcases lt_or_gt_of_ne (fun e => hne (rkey_injective x e)) with hl | hl
  · exact absurd h (rrank_lt_of_lt x hx hpos i j hl).ne
  · exact absurd h (rrank_lt_of_lt x hx hpos j i hl).ne'

lemma rrank_pred (x : ℕ → ℝ) (hx : Tendsto x atTop (𝓝 0)) (hpos : ∀ i, 0 < x i)
    (i m : ℕ) (h : rrank x i = m + 1) : ∃ j, rrank x j = m := by
  have hfin := rpred_finite x hx hpos i
  have hne : (hfin.toFinset).Nonempty := by
    rw [Set.Finite.toFinset_nonempty, Set.nonempty_iff_ne_empty]
    intro he
    unfold rrank at h
    rw [he, Set.ncard_empty] at h
    omega
  obtain ⟨j, hj, hmax⟩ := Finset.exists_max_image hfin.toFinset (rkey x) hne
  rw [Set.Finite.mem_toFinset] at hj
  refine ⟨j, ?_⟩
  have heq : rpred x j = rpred x i \ {j} := by
    ext l
    simp only [rpred, Set.mem_setOf_eq, Set.mem_diff, Set.mem_singleton_iff]
    constructor
    · intro hl
      exact ⟨lt_trans hl hj, fun e => by rw [e] at hl; exact lt_irrefl _ hl⟩
    · rintro ⟨hl, hne⟩
      have := hmax l (by rw [Set.Finite.mem_toFinset]; exact hl)
      exact lt_of_le_of_ne this (fun e => hne (rkey_injective x e))
  unfold rrank
  rw [heq, Set.ncard_sdiff_singleton_of_mem hj]
  unfold rrank at h
  omega

lemma rrank_surjective (x : ℕ → ℝ) (hx : Tendsto x atTop (𝓝 0)) (hpos : ∀ i, 0 < x i) :
    Function.Surjective (rrank x) := by
  have hdown : ∀ d k, ∀ i, rrank x i = k + d → ∃ j, rrank x j = k := by
    intro d
    induction d with
    | zero => intro k i h; exact ⟨i, by simpa using h⟩
    | succ d ih =>
      intro k i h
      obtain ⟨j, hj⟩ := rrank_pred x hx hpos i (k + d) (by rw [h]; ring)
      exact ih k j hj
  intro k
  have hinf : (Set.range (rrank x)).Infinite :=
    Set.infinite_range_of_injective (rrank_injective x hx hpos)
  obtain ⟨b, ⟨i, hi⟩, hb⟩ := hinf.exists_gt k
  exact hdown (b - k) k i (by rw [hi]; omega)

/-- The ranked sequence is a rearrangement of a positive summable sequence. -/
lemma ranked_rearrangement (x : ℕ → ℝ) (hpos : ∀ i, 0 < x i) (hs : Summable x) :
    ∃ σ : ℕ ≃ ℕ, ∀ k, ranked x k = x (σ k) := by
  have hx := hs.tendsto_atTop_zero
  let σ := Equiv.ofBijective (rrank x) ⟨rrank_injective x hx hpos, rrank_surjective x hx hpos⟩
  refine ⟨σ.symm, fun k => ?_⟩
  apply ranked_eq_of_rrank x hx hpos
  exact σ.apply_symm_apply k

lemma ranked_pos (x : ℕ → ℝ) (hpos : ∀ i, 0 < x i) (hs : Summable x) (k : ℕ) :
    0 < ranked x k := by
  obtain ⟨σ, hσ⟩ := ranked_rearrangement x hpos hs
  rw [hσ]; exact hpos _

lemma ranked_summable (x : ℕ → ℝ) (hpos : ∀ i, 0 < x i) (hs : Summable x) :
    Summable (ranked x) := by
  obtain ⟨σ, hσ⟩ := ranked_rearrangement x hpos hs
  have : ranked x = x ∘ σ := funext hσ
  rw [this]
  exact (σ.summable_iff).2 hs

lemma ranked_tsum (x : ℕ → ℝ) (hpos : ∀ i, 0 < x i) (hs : Summable x) :
    ∑' k, ranked x k = ∑' i, x i := by
  obtain ⟨σ, hσ⟩ := ranked_rearrangement x hpos hs
  simp_rw [hσ]
  exact σ.tsum_eq x


lemma beta_lintegral_one_sub (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    ∫⁻ x, ENNReal.ofReal (1 - x) ∂(betaMeasure a b) = ENNReal.ofReal (b / (a + b)) := by
  have hmeas : Measurable (betaPDF a b) := (measurable_betaPDFReal a b).ennreal_ofReal
  rw [betaMeasure, lintegral_withDensity_eq_lintegral_mul _ hmeas (by fun_prop)]
  have hpt : ∀ x, betaPDF a b x * ENNReal.ofReal (1 - x) =
      ENNReal.ofReal (b / (a + b)) * betaPDF a (b + 1) x := by
    intro x
    by_cases hx : 0 < x ∧ x < 1
    · rw [betaPDF_of_pos_lt_one hx.1 hx.2, betaPDF_of_pos_lt_one hx.1 hx.2]
      rw [← ENNReal.ofReal_mul (by
        have := beta_pos ha hb
        have := Real.rpow_nonneg hx.1.le (a - 1)
        have := Real.rpow_nonneg (by linarith : (0:ℝ) ≤ 1 - x) (b - 1)
        positivity), ← ENNReal.ofReal_mul (by positivity)]
      congr 1
      have h1 : (1 - x) ^ (b + 1 - 1) = (1 - x) ^ (b - 1) * (1 - x) := by
        rw [show b + 1 - 1 = (b - 1) + 1 by ring, Real.rpow_add_one (by linarith)]
      rw [h1]
      have hB : beta a (b + 1) = beta a b * (b / (a + b)) := by
        unfold beta
        rw [Real.Gamma_add_one hb.ne', show a + (b + 1) = (a + b) + 1 by ring,
          Real.Gamma_add_one (by positivity : a + b ≠ 0)]
        have := Real.Gamma_pos_of_pos ha
        have := Real.Gamma_pos_of_pos hb
        have := Real.Gamma_pos_of_pos (add_pos ha hb)
        field_simp
      rw [hB]
      have := beta_pos ha hb
      field_simp
    · rw [betaPDF_eq, if_neg hx, betaPDF_eq, if_neg hx]; simp
  simp_rw [Pi.mul_apply, hpt]
  rw [lintegral_const_mul _ (show Measurable (betaPDF a (b+1)) from
      (measurable_betaPDFReal a (b+1)).ennreal_ofReal),
    lintegral_betaPDF_eq_one ha (by linarith), mul_one]

lemma beta_ae_Ioo (a b : ℝ) :
    betaMeasure a b {x | ¬ (0 < x ∧ x < 1)} = 0 := by
  rw [betaMeasure, withDensity_apply _ (by
      exact (measurableSet_Ioo (a := (0:ℝ)) (b := 1)).compl)]
  apply setLIntegral_eq_zero (by exact (measurableSet_Ioo (a := (0:ℝ)) (b := 1)).compl)
  intro x hx
  rw [betaPDF_eq, if_neg hx]; simp

/-- Under a stick law the coordinates lie in `(0,1)` almost surely. -/
lemma stick_ae_Ioo (α θ : ℝ) (μ : Measure (ℕ → ℝ)) (hμ : IsStickLaw α θ μ) :
    ∀ᵐ y ∂μ, ∀ k, 0 < y k ∧ y k < 1 := by
  rw [ae_all_iff]
  intro k
  rw [ae_iff]
  have hm : Measurable (fun y : ℕ → ℝ => y k) := measurable_pi_apply k
  have hs : MeasurableSet {x : ℝ | ¬ (0 < x ∧ x < 1)} :=
    (measurableSet_Ioo (a := (0:ℝ)) (b := 1)).compl
  have := (hμ.2.2 k).map_eq
  rw [show {y : ℕ → ℝ | ¬ (0 < y k ∧ y k < 1)} = (fun y : ℕ → ℝ => y k) ⁻¹' {x | ¬ (0 < x ∧ x < 1)}
    from rfl, ← Measure.map_apply hm hs, this, beta_ae_Ioo]

/-- Expected value of the product of the `(1 - y i)`. -/
lemma stick_prod_lintegral (α θ : ℝ) (hα1 : α < 1) (hθ : -α < θ) (hα : 0 < α)
    (μ : Measure (ℕ → ℝ)) (hμ : IsStickLaw α θ μ) (n : ℕ) :
    ∫⁻ y, ∏ i ∈ Finset.range n, ENNReal.ofReal (1 - y i) ∂μ =
      ∏ i ∈ Finset.range n, ENNReal.ofReal ((θ + ((i : ℝ) + 1) * α) / (1 - α + (θ + ((i : ℝ) + 1) * α))) := by
  have hind : iIndepFun (fun i (y : ℕ → ℝ) => ENNReal.ofReal (1 - y i)) μ := by
    have := hμ.2.1.comp (fun i (x : ℝ) => ENNReal.ofReal (1 - x)) (fun i => by fun_prop)
    exact this
  have hmeas : ∀ i, Measurable (fun y : ℕ → ℝ => ENNReal.ofReal (1 - y i)) := fun i => by fun_prop
  rw [lintegral_prod_eq_prod_lintegral_of_indepFun (Finset.range n) _ hind hmeas]
  apply Finset.prod_congr rfl
  intro i _
  have hm : Measurable (fun y : ℕ → ℝ => y i) := measurable_pi_apply i
  rw [← lintegral_map (f := fun x : ℝ => ENNReal.ofReal (1 - x)) (by fun_prop) hm,
    (hμ.2.2 i).map_eq, beta_lintegral_one_sub]
  · linarith
  · have : (0:ℝ) ≤ i := Nat.cast_nonneg i
    nlinarith

lemma harmonic_bound (α θ : ℝ) (hα : 0 < α) (hα1 : α < 1) (hθ : -α < θ) :
    Tendsto (fun n : ℕ => ∑ i ∈ Finset.range n, (1 - α) / (1 - α + (θ + ((i : ℝ) + 1) * α)))
      atTop atTop := by
  have hC : 0 < 1 + θ + α := by linarith
  have hc : 0 < (1 - α) / (1 + θ + α) := by positivity
  have h := (Real.tendsto_sum_range_one_div_nat_succ_atTop).const_mul_atTop hc
  refine tendsto_atTop_mono (fun n => ?_) h
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  have hi : (0:ℝ) ≤ i := Nat.cast_nonneg i
  rw [mul_one_div, div_div]
  apply div_le_div_of_nonneg_left (by linarith) (by nlinarith)
  nlinarith

/-- The products `∏ (1 - y i)` tend to zero almost surely. -/
lemma stick_prod_tendsto_zero (α θ : ℝ) (hα : 0 < α) (hα1 : α < 1) (hθ : -α < θ)
    (μ : Measure (ℕ → ℝ)) (hμ : IsStickLaw α θ μ) :
    ∀ᵐ y ∂μ, Tendsto (fun n : ℕ => ∏ i ∈ Finset.range n, (1 - y i)) atTop (𝓝 0) := by
  haveI : IsProbabilityMeasure μ := hμ.1
  set Wn : ℕ → (ℕ → ℝ) → ℝ := fun n y => ∏ i ∈ Finset.range n, (1 - y i) with hWn
  set W : (ℕ → ℝ) → ℝ := fun y => ⨅ n, Wn n y with hW
  have hWnm : ∀ n, Measurable (Wn n) := fun n => by
    simp only [hWn]; exact Finset.measurable_prod _ (fun i _ => by fun_prop)
  have hWm : Measurable W := Measurable.iInf hWnm
  have hgood := stick_ae_Ioo α θ μ hμ
  -- on the good set
  have hfacts : ∀ y : ℕ → ℝ, (∀ k, 0 < y k ∧ y k < 1) →
      (∀ n, 0 ≤ Wn n y) ∧ Antitone (fun n => Wn n y) := by
    intro y hy
    have h0 : ∀ n, 0 ≤ Wn n y := fun n =>
      Finset.prod_nonneg (fun i _ => by linarith [(hy i).2])
    refine ⟨h0, antitone_nat_of_succ_le (fun n => ?_)⟩
    simp only [hWn, Finset.prod_range_succ]
    have := h0 n
    simp only [hWn] at this
    nlinarith [(hy n).1]
  -- the integral of ofReal W is zero
  have hbound : ∀ n, ∫⁻ y, ENNReal.ofReal (W y) ∂μ ≤
      ENNReal.ofReal (Real.exp (-∑ i ∈ Finset.range n, (1 - α) / (1 - α + (θ + ((i : ℝ) + 1) * α)))) := by
    intro n
    calc ∫⁻ y, ENNReal.ofReal (W y) ∂μ ≤ ∫⁻ y, ENNReal.ofReal (Wn n y) ∂μ := by
          apply lintegral_mono_ae
          filter_upwards [hgood] with y hy
          apply ENNReal.ofReal_le_ofReal
          exact ciInf_le ⟨0, by rintro _ ⟨m, rfl⟩; exact (hfacts y hy).1 m⟩ n
      _ = ∫⁻ y, ∏ i ∈ Finset.range n, ENNReal.ofReal (1 - y i) ∂μ := by
          apply lintegral_congr_ae
          filter_upwards [hgood] with y hy
          simp only [hWn]
          rw [ENNReal.ofReal_prod_of_nonneg (fun i _ => by linarith [(hy i).2])]
      _ = ∏ i ∈ Finset.range n, ENNReal.ofReal ((θ + ((i : ℝ) + 1) * α) / (1 - α + (θ + ((i : ℝ) + 1) * α))) :=
          stick_prod_lintegral α θ hα1 hθ hα μ hμ n
      _ ≤ ENNReal.ofReal (Real.exp (-∑ i ∈ Finset.range n, (1 - α) / (1 - α + (θ + ((i : ℝ) + 1) * α)))) := by
          have hpos : ∀ i : ℕ, 0 < 1 - α + (θ + ((i : ℝ) + 1) * α) := fun i => by
            have : (0:ℝ) ≤ i := Nat.cast_nonneg i
            nlinarith
          have hnn : ∀ i : ℕ, 0 ≤ (θ + ((i : ℝ) + 1) * α) / (1 - α + (θ + ((i : ℝ) + 1) * α)) := fun i => by
            have : (0:ℝ) ≤ i := Nat.cast_nonneg i
            apply div_nonneg _ (hpos i).le
            nlinarith
          rw [← ENNReal.ofReal_prod_of_nonneg (fun i _ => hnn i)]
          apply ENNReal.ofReal_le_ofReal
          rw [Real.exp_neg, Real.exp_sum, ← Finset.prod_inv_distrib]
          apply Finset.prod_le_prod (fun i _ => hnn i)
          intro i _
          rw [← Real.exp_neg]
          have h1 : (θ + ((i : ℝ) + 1) * α) / (1 - α + (θ + ((i : ℝ) + 1) * α)) =
              1 - (1 - α) / (1 - α + (θ + ((i : ℝ) + 1) * α)) := by
            field_simp [(hpos i).ne']
            ring
          rw [h1]
          have := Real.add_one_le_exp (-((1 - α) / (1 - α + (θ + ((i : ℝ) + 1) * α))))
          linarith
  have hzero : ∫⁻ y, ENNReal.ofReal (W y) ∂μ = 0 := by
    refine le_antisymm ?_ bot_le
    have hlim : Tendsto (fun n : ℕ => ENNReal.ofReal (Real.exp (-∑ i ∈ Finset.range n,
        (1 - α) / (1 - α + (θ + ((i : ℝ) + 1) * α))))) atTop (𝓝 (ENNReal.ofReal 0)) := by
      apply ENNReal.tendsto_ofReal
      have := Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp (harmonic_bound α θ hα hα1 hθ))
      exact this
    rw [ENNReal.ofReal_zero] at hlim
    exact ge_of_tendsto' hlim hbound
  rw [lintegral_eq_zero_iff hWm.ennreal_ofReal] at hzero
  filter_upwards [hgood, hzero] with y hy hz
  have hW0 : W y = 0 := by
    simp only [Pi.zero_apply, ENNReal.ofReal_eq_zero] at hz
    apply le_antisymm hz
    exact le_ciInf (fun n => (hfacts y hy).1 n)
  have := tendsto_atTop_ciInf (hfacts y hy).2 ⟨0, by rintro _ ⟨m, rfl⟩; exact (hfacts y hy).1 m⟩
  rw [← hW0]
  exact this


lemma stick_pos' (y : ℕ → ℝ) (hy : ∀ k, 0 < y k ∧ y k < 1) (k : ℕ) : 0 < stick y k := by
  unfold stick
  exact mul_pos (Finset.prod_pos (fun i _ => by linarith [(hy i).2])) (hy k).1

lemma stick_partial_sum (y : ℕ → ℝ) (n : ℕ) :
    ∑ k ∈ Finset.range n, stick y k = 1 - ∏ i ∈ Finset.range n, (1 - y i) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, Finset.prod_range_succ]
    unfold stick; ring

lemma stick_hasSum (y : ℕ → ℝ) (hy : ∀ k, 0 < y k ∧ y k < 1)
    (hlim : Tendsto (fun n : ℕ => ∏ i ∈ Finset.range n, (1 - y i)) atTop (𝓝 0)) :
    HasSum (stick y) 1 := by
  rw [hasSum_iff_tendsto_nat_of_nonneg (fun k => (stick_pos' y hy k).le)]
  simp_rw [stick_partial_sum]
  have := hlim.const_sub 1
  simpa using this

/-- The good set of sequences: positive entries and total mass one. -/
def goodSet : Set (ℕ → ℝ) :=
  {v | (∀ k, 0 < v k) ∧ Tendsto (fun n : ℕ => ∑ i ∈ Finset.range n, v i) atTop (𝓝 1)}

lemma goodSet_measurable : MeasurableSet goodSet := by
  unfold goodSet
  rw [Set.setOf_and]
  apply MeasurableSet.inter
  · rw [Set.setOf_forall]
    exact MeasurableSet.iInter (fun k => measurableSet_lt measurable_const (measurable_pi_apply k))
  · exact measurableSet_tendsto (𝓝 (1:ℝ))
      (fun n => Finset.measurable_sum _ (fun i _ => measurable_pi_apply i))

lemma ranked_stick_ae_good (α θ : ℝ) (hα : 0 < α) (hα1 : α < 1) (hθ : -α < θ)
    (μ : Measure (ℕ → ℝ)) (hμ : IsStickLaw α θ μ) :
    ∀ᵐ y ∂μ, ranked (stick y) ∈ goodSet := by
  filter_upwards [stick_ae_Ioo α θ μ hμ, stick_prod_tendsto_zero α θ hα hα1 hθ μ hμ] with y hy hlim
  have hS := stick_hasSum y hy hlim
  have hpos := fun k => stick_pos' y hy k
  refine ⟨fun k => ranked_pos _ hpos hS.summable k, ?_⟩
  have h1 : HasSum (ranked (stick y)) 1 := by
    have := (ranked_summable _ hpos hS.summable).hasSum
    rwa [ranked_tsum _ hpos hS.summable, hS.tsum_eq] at this
  exact h1.tendsto_sum_nat

lemma hasPD_ae_good {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (α θ : ℝ)
    (hα : 0 < α) (hα1 : α < 1) (hθ : -α < θ) (V : Ω → ℕ → ℝ) (hV : HasPD α θ P V) :
    ∀ᵐ ω ∂P, V ω ∈ goodSet := by
  obtain ⟨_, μ, hμ, hP⟩ := hV
  rw [ae_iff]
  have := hP goodSetᶜ goodSet_measurable.compl
  rw [show {ω | ¬ V ω ∈ goodSet} = V ⁻¹' goodSetᶜ from rfl, this]
  have h := ranked_stick_ae_good α θ hα hα1 hθ μ hμ
  rw [ae_iff] at h
  exact h

theorem eq_143_core {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (α θ : ℝ) (hα : 0 < α) (hα1 : α < 1) (hθ : -α < θ) (V : Ω → ℕ → ℝ) (hV : HasPD α θ P V)
    (L : Ω → ℝ)
    (hL : ∀ᵐ ω ∂P, Tendsto (fun k : ℕ => ((k : ℝ) + 1) * V ω k ^ α) atTop (𝓝 (L ω))) :
    ∀ᵐ ω ∂P, Tendsto (fun k : ℕ => Yseq (V ω) 0 ^ α *
        (((k : ℝ) + 1) * (∏ i ∈ Finset.range (k + 1), ratio (V ω) i) ^ α)) atTop (𝓝 (L ω)) := by
  filter_upwards [hasPD_ae_good P α θ hα hα1 hθ V hV, hL] with ω hω hLω
  obtain ⟨hpos, hsum⟩ := hω
  have hS : HasSum (V ω) 1 := (hasSum_iff_tendsto_nat_of_nonneg (fun k => (hpos k).le) 1).2 hsum
  have hY : Yseq (V ω) 0 = V ω 0 := by
    unfold Yseq; simp only [zero_add]; rw [hS.tsum_eq, div_one]
  have hprod : ∀ k, ∏ i ∈ Finset.range (k + 1), ratio (V ω) i = V ω (k + 1) / V ω 0 := by
    intro k
    induction k with
    | zero => simp [ratio]
    | succ k ih =>
      rw [Finset.prod_range_succ, ih]
      unfold ratio
      have := (hpos (k + 1)).ne'
      have := (hpos 0).ne'
      field_simp
  have heq : ∀ k : ℕ, Yseq (V ω) 0 ^ α *
      (((k : ℝ) + 1) * (∏ i ∈ Finset.range (k + 1), ratio (V ω) i) ^ α)
      = (((k:ℝ) + 1) / ((k:ℝ) + 2)) * ((((k + 1 : ℕ) : ℝ) + 1) * V ω (k + 1) ^ α) := by
    intro k
    rw [hY, hprod, Real.div_rpow (hpos _).le (hpos 0).le]
    have h0 : V ω 0 ^ α ≠ 0 := (Real.rpow_pos_of_pos (hpos 0) α).ne'
    push_cast
    field_simp
    ring
  simp_rw [heq]
  have h1 : Tendsto (fun k : ℕ => ((k:ℝ) + 1) / ((k:ℝ) + 2)) atTop (𝓝 1) := by
    have := (tendsto_natCast_div_add_atTop (1:ℝ)).comp (tendsto_add_atTop_nat 1)
    refine this.congr (fun k => ?_)
    simp only [Function.comp]
    push_cast
    ring
  have h2 : Tendsto (fun k : ℕ => (((k + 1 : ℕ) : ℝ) + 1) * V ω (k + 1) ^ α) atTop (𝓝 (L ω)) :=
    hLω.comp (tendsto_add_atTop_nat 1)
  have := h1.mul h2
  rw [one_mul] at this
  exact this

end PoissonDirichlet.Chain

open PoissonDirichlet.Chain


theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (α θ : ℝ) (hα : 0 < α) (hα1 : α < 1) (hθ : -α < θ) (V : Ω → ℕ → ℝ) (hV : PoissonDirichlet.Ratio.HasPD α θ P V)
    (L : Ω → ℝ)
    (hL : ∀ᵐ ω ∂P, Tendsto (fun k : ℕ => ((k : ℝ) + 1) * V ω k ^ α) atTop (𝓝 (L ω))) :
    ∀ᵐ ω ∂P, Tendsto (fun k : ℕ => Yseq (V ω) 0 ^ α *
        (((k : ℝ) + 1) * (∏ i ∈ Finset.range (k + 1), PoissonDirichlet.Ratio.ratio (V ω) i) ^ α)) atTop (𝓝 (L ω)) := by
  exact eq_143_core P α θ hα hα1 hθ V hV L hL
