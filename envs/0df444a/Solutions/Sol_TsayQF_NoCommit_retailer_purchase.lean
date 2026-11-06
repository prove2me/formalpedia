-- Prove2me | solution 1 for TsayQF.NoCommit.retailer_purchase
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-05T15:06:36.833464+00:00
-- url     : https://prove2.me/submissions/5df99c71-e696-4297-9bc5-28402df06bba

import Mathlib
import Definitions.Def_TsayQF_NoCommit_Model
open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace TsayQFRPAux
open Set Filter Topology

lemma min_inc_lower (x Q Q' : ℝ) (h : Q ≤ Q') :
    (Ioi Q').indicator (fun _ => Q' - Q) x ≤ min x Q' - min x Q := by
  by_cases hx : x ∈ Ioi Q'
  · rw [indicator_of_mem hx]
    have : Q' < x := hx
    rw [min_eq_right this.le, min_eq_right (by linarith)]
  · rw [indicator_of_notMem hx]
    have := min_le_min_left x h
    linarith

lemma min_inc_upper (x Q Q' : ℝ) (h : Q ≤ Q') :
    min x Q' - min x Q ≤ (Ioi Q).indicator (fun _ => Q' - Q) x := by
  by_cases hx : x ∈ Ioi Q
  · rw [indicator_of_mem hx]
    have : Q < x := hx
    rw [min_eq_right this.le]
    have := min_le_right x Q'
    linarith
  · rw [indicator_of_notMem hx]
    have : x ≤ Q := not_lt.1 hx
    rw [min_eq_left this, min_eq_left (by linarith)]
    simp

lemma real_Ioi (ρ : Measure ℝ) [IsProbabilityMeasure ρ] (x : ℝ) :
    ρ.real (Ioi x) = 1 - cdf ρ x := by
  rw [← compl_Iic, probReal_compl_eq_one_sub measurableSet_Iic, cdf_eq_real]

lemma int_min (ρ : Measure ℝ) [IsProbabilityMeasure ρ] (hint : Integrable id ρ) (Q : ℝ) :
    Integrable (fun y => min y Q) ρ := by
  have := hint.inf (integrable_const Q)
  exact this

lemma inc_lo (ρ : Measure ℝ) [IsProbabilityMeasure ρ] (hint : Integrable id ρ) (Q Q' : ℝ)
    (h : Q ≤ Q') :
    (Q' - Q) * (1 - cdf ρ Q') ≤ ∫ y, min y Q' ∂ρ - ∫ y, min y Q ∂ρ := by
  rw [← integral_sub (int_min ρ hint _) (int_min ρ hint _), ← real_Ioi, mul_comm,
    ← smul_eq_mul, ← integral_indicator_const _ measurableSet_Ioi]
  exact integral_mono ((integrable_const _).indicator measurableSet_Ioi)
    ((int_min ρ hint _).sub (int_min ρ hint _)) (fun x => min_inc_lower x Q Q' h)

lemma inc_hi (ρ : Measure ℝ) [IsProbabilityMeasure ρ] (hint : Integrable id ρ) (Q Q' : ℝ)
    (h : Q ≤ Q') :
    ∫ y, min y Q' ∂ρ - ∫ y, min y Q ∂ρ ≤ (Q' - Q) * (1 - cdf ρ Q) := by
  rw [← integral_sub (int_min ρ hint _) (int_min ρ hint _), ← real_Ioi, mul_comm,
    ← smul_eq_mul, ← integral_indicator_const _ measurableSet_Ioi]
  exact integral_mono ((int_min ρ hint _).sub (int_min ρ hint _))
    ((integrable_const _).indicator measurableSet_Ioi) (fun x => min_inc_upper x Q Q' h)


lemma min_inc_lower' (x Q Q' : ℝ) (h : Q ≤ Q') :
    (Ici Q').indicator (fun _ => Q' - Q) x ≤ min x Q' - min x Q := by
  by_cases hx : x ∈ Ici Q'
  · rw [indicator_of_mem hx]
    have : Q' ≤ x := hx
    rw [min_eq_right this, min_eq_right (by linarith)]
  · rw [indicator_of_notMem hx]
    have := min_le_min_left x h
    linarith

lemma inc_lo' (ρ : Measure ℝ) [IsProbabilityMeasure ρ] (hint : Integrable id ρ) (Q Q' : ℝ)
    (h : Q ≤ Q') :
    (Q' - Q) * ρ.real (Ici Q') ≤ ∫ y, min y Q' ∂ρ - ∫ y, min y Q ∂ρ := by
  rw [← integral_sub (int_min ρ hint _) (int_min ρ hint _), mul_comm,
    ← smul_eq_mul, ← integral_indicator_const _ measurableSet_Ici]
  exact integral_mono ((integrable_const _).indicator measurableSet_Ici)
    ((int_min ρ hint _).sub (int_min ρ hint _)) (fun x => min_inc_lower' x Q Q' h)

/-- A newsvendor objective whose distribution function crosses the critical fractile `k` at
`rs` is strictly increasing up to `rs` and strictly decreasing after it, so its maximizers over
`r ≤ Q` are exactly `min rs Q`. -/
lemma constrained (ρ : Measure ℝ) [IsProbabilityMeasure ρ] (hint : Integrable id ρ)
    (a b k rs C : ℝ) (ha : 0 < a) (hab : b = a * (1 - k))
    (H1 : ∀ t ≤ rs, 1 - k ≤ ρ.real (Ici t)) (H2 : ∀ t < rs, cdf ρ t < k)
    (H4 : ∀ t ≥ rs, k ≤ cdf ρ t) (H3 : ∀ t > rs, k < cdf ρ t) :
    ∀ Q r : ℝ, (r ≤ Q ∧ IsMaxOn (fun r => a * ∫ y, min y r ∂ρ - b * r + C) (Iic Q) r) ↔
      r = min rs Q := by
  set f := fun r => a * ∫ y, min y r ∂ρ - b * r + C with hf
  have inc : ∀ r1 r2, r1 < r2 → r2 ≤ rs → f r1 < f r2 := by
    intro r1 r2 h12 h2
    set m := (r1 + r2) / 2 with hm
    have hd1 : 0 < m - r1 := by rw [hm]; linarith
    have hd2 : 0 < r2 - m := by rw [hm]; linarith
    have A := inc_lo' ρ hint r1 m (by linarith)
    have hI : ρ.real (Ioi m) ≤ ρ.real (Ici m) := measureReal_mono Ioi_subset_Ici_self
    rw [real_Ioi] at hI
    have hFm := H2 m (by linarith)
    have A1 : (m - r1) * (1 - k) < (m - r1) * (1 - cdf ρ m) :=
      mul_lt_mul_of_pos_left (by linarith) hd1
    have A2 : (m - r1) * (1 - cdf ρ m) ≤ (m - r1) * ρ.real (Ici m) :=
      mul_le_mul_of_nonneg_left hI hd1.le
    have A3 := mul_lt_mul_of_pos_left (lt_of_lt_of_le (lt_of_lt_of_le A1 A2) A) ha
    have B := inc_lo' ρ hint m r2 (by linarith)
    have B1 : (r2 - m) * (1 - k) ≤ (r2 - m) * ρ.real (Ici r2) :=
      mul_le_mul_of_nonneg_left (H1 r2 h2) hd2.le
    have B3 := mul_le_mul_of_nonneg_left (le_trans B1 B) ha.le
    simp only [hf]
    rw [hab] at *
    nlinarith
  have dec : ∀ r1 r2, rs ≤ r1 → r1 < r2 → f r2 < f r1 := by
    intro r1 r2 h1 h12
    set m := (r1 + r2) / 2 with hm
    have hd1 : 0 < m - r1 := by rw [hm]; linarith
    have hd2 : 0 < r2 - m := by rw [hm]; linarith
    have A := inc_hi ρ hint r1 m (by linarith)
    have A1 : (m - r1) * (1 - cdf ρ r1) ≤ (m - r1) * (1 - k) :=
      mul_le_mul_of_nonneg_left (by linarith [H4 r1 h1]) hd1.le
    have A3 := mul_le_mul_of_nonneg_left (le_trans A A1) ha.le
    have B := inc_hi ρ hint m r2 (by linarith)
    have B1 : (r2 - m) * (1 - cdf ρ m) < (r2 - m) * (1 - k) :=
      mul_lt_mul_of_pos_left (by linarith [H3 m (by linarith)]) hd2
    have B3 := mul_lt_mul_of_pos_left (lt_of_le_of_lt B B1) ha
    simp only [hf]
    rw [hab] at *
    nlinarith
  intro Q r
  constructor
  · rintro ⟨hrQ, hmax⟩
    have hmax' := isMaxOn_iff.1 hmax
    by_contra hne
    rcases lt_or_gt_of_ne hne with h | h
    · have := inc r (min rs Q) h (min_le_left _ _)
      have := hmax' (min rs Q) (Set.mem_Iic.2 (min_le_right _ _))
      linarith
    · have hrs : min rs Q = rs := by
        rcases min_choice rs Q with e | e
        · exact e
        · rw [e] at h; linarith
      rw [hrs] at h
      have := dec rs r le_rfl h
      have := hmax' rs (show rs ≤ Q by linarith)
      linarith
  · rintro rfl
    refine ⟨min_le_right _ _, isMaxOn_iff.2 fun r' hr' => ?_⟩
    have hr' : r' ≤ Q := hr'
    rcases lt_trichotomy r' (min rs Q) with h | h | h
    · exact (inc r' (min rs Q) h (min_le_left _ _)).le
    · rw [h]
    · have hrs : min rs Q = rs := by
        rcases min_choice rs Q with e | e
        · exact e
        · rw [e] at h; linarith
      rw [hrs] at h ⊢
      exact (dec rs r' le_rfl h).le

end TsayQFRPAux

namespace TsayQFRPAux
open TsayQF.NoCommit Set

lemma kfacts (D : Data) : 0 < kR D ∧ kR D < 1 ∧
    D.c - D.u = (D.p + D.s - D.u) * (1 - kR D) := by
  have hm := D.hm; have hmc := D.hmc; have hcp := D.hcp; have hum := D.hum; have hs := D.hs
  have h1 : 0 < D.p + D.s - D.u := by linarith
  refine ⟨?_, ?_, ?_⟩
  · unfold kR; apply div_pos <;> linarith
  · unfold kR; rw [div_lt_one h1]; linarith
  · unfold kR; field_simp; ring

lemma payoff_eq1 (D : Data) (x r : ℝ) :
    payoff D x r = (D.p + D.s - D.c) * r - D.s * x - (D.p + D.s - D.u) * max (r - x) 0 := by
  unfold payoff
  rcases le_total x r with h | h
  · rw [min_eq_left h, max_eq_right (by linarith), max_eq_left (by linarith)]; ring
  · rw [min_eq_right h, max_eq_left (by linarith), max_eq_right (by linarith)]; ring

lemma payoff_eq2 (D : Data) (x r : ℝ) :
    payoff D x r = (D.p + D.s - D.u) * min x r - (D.c - D.u) * r + (- D.s * x) := by
  unfold payoff
  rcases le_total x r with h | h
  · rw [min_eq_left h, max_eq_right (by linarith), max_eq_left (by linarith)]; ring
  · rw [min_eq_right h, max_eq_left (by linarith), max_eq_right (by linarith)]; ring

lemma gauss_N (v : ℝ≥0) (hv : v ≠ 0) :
    (gaussianReal 0 1).map (fun x => Real.sqrt v * x) = gaussianReal 0 v := by
  rw [gaussianReal_map_const_mul]
  congr 1
  · simp
  · ext; simp [Real.sq_sqrt (NNReal.coe_nonneg v)]

lemma gauss_cdf_z (D : Data) (v : ℝ≥0) (hv : v ≠ 0) (z μ : ℝ)
    (hz : cdf (gaussianReal 0 1) z = kR D) :
    cdf (gaussianReal μ v) (μ + z * Real.sqrt v) = kR D := by
  have hs : 0 < Real.sqrt v := Real.sqrt_pos.2 (by
    rcases (NNReal.coe_nonneg v).lt_or_eq with h | h
    · exact h
    · exact absurd (by exact_mod_cast h.symm) hv)
  have e1 := gaussianReal_map_const_add (μ := 0) (v := v) μ
  rw [zero_add] at e1
  rw [cdf_eq_real, ← e1, map_measureReal_apply (by fun_prop) measurableSet_Iic,
    ← gauss_N v hv, map_measureReal_apply (by fun_prop) (measurableSet_Iic.preimage (by fun_prop)),
    ← hz, cdf_eq_real]
  congr 1
  ext x
  simp only [mem_preimage, mem_Iic]
  constructor
  · intro h; nlinarith
  · intro h; nlinarith

lemma gauss_strict (μ : ℝ) (v : ℝ≥0) (hv : v ≠ 0) : StrictMono (cdf (gaussianReal μ v)) := by
  intro x y hxy
  have hpos : 0 < (gaussianReal μ v) (Ioc x y) := by
    rw [pos_iff_ne_zero]
    intro h
    have := gaussianReal_absolutelyContinuous' μ hv h
    simp at this
    linarith
  rw [← measure_cdf (gaussianReal μ v), StieltjesFunction.measure_Ioc] at hpos
  have := ENNReal.ofReal_pos.1 hpos
  linarith

lemma dirac_real (μ : ℝ) {s : Set ℝ} (hs : MeasurableSet s) [Decidable (μ ∈ s)] :
    (Measure.dirac μ).real s = if μ ∈ s then 1 else 0 := by
  rw [measureReal_def, Measure.dirac_apply' _ hs]
  by_cases h : μ ∈ s
  · rw [indicator_of_mem h, if_pos h]; simp
  · rw [indicator_of_notMem h, if_neg h]; simp

end TsayQFRPAux

open TsayQF.NoCommit Set TsayQFRPAux in
theorem solution (D : Data) (v : ℝ≥0) (z : ℝ)
    (hz : cdf (gaussianReal 0 1) z = kR D) :
    (∀ r μ : ℝ, G D v r μ = (D.p + D.s - D.c) * r - D.s * μ
        - (D.p + D.s - D.u) * ∫ x, max (r - x) 0 ∂(gaussianReal μ v)) ∧
      ∀ μ Q r : ℝ, (r ≤ Q ∧ IsMaxOn (fun r' => G D v r' μ) (Set.Iic Q) r) ↔
        r = ncPurchase v z μ Q := by
  obtain ⟨hk0, hk1, hab⟩ := kfacts D
  have ha : 0 < D.p + D.s - D.u := by linarith [D.hcp, D.hmc, D.hum, D.hs]
  have hX : ∀ μ : ℝ, Integrable id (gaussianReal μ v) := fun μ =>
    (memLp_id_gaussianReal' (μ := μ) (v := v) 1 ENNReal.one_ne_top).integrable le_rfl
  refine ⟨fun r μ => ?_, fun μ Q r => ?_⟩
  · have hmx : Integrable (fun x => max (r - x) 0) (gaussianReal μ v) := by
      have := ((integrable_const r).sub (hX μ)).sup (integrable_zero ℝ ℝ (gaussianReal μ v))
      exact this
    have i1 : Integrable (fun x : ℝ => (D.p + D.s - D.c) * r - D.s * x) (gaussianReal μ v) :=
      (integrable_const _).sub ((hX μ).const_mul _)
    have i2 : Integrable (fun x : ℝ => D.s * x) (gaussianReal μ v) := (hX μ).const_mul _
    unfold G
    simp_rw [payoff_eq1]
    rw [integral_sub i1 (hmx.const_mul _), integral_sub (integrable_const _) i2,
      integral_const_mul, integral_const_mul, integral_const, integral_id_gaussianReal]
    simp [integral_const_mul]
  · have hGf : (fun r' => G D v r' μ) = fun r' => (D.p + D.s - D.u) *
        ∫ y, min y r' ∂(gaussianReal μ v) - (D.c - D.u) * r' + (- D.s * μ) := by
      funext r'
      have hm := int_min (gaussianReal μ v) (hX μ) r'
      have i2 : Integrable (fun x : ℝ => -D.s * x) (gaussianReal μ v) := (hX μ).const_mul _
      have i3 : Integrable (fun x : ℝ => (D.p + D.s - D.u) * min x r' - (D.c - D.u) * r')
        (gaussianReal μ v) := (hm.const_mul _).sub (integrable_const _)
      unfold G
      simp_rw [payoff_eq2]
      rw [integral_add i3 i2,
        integral_sub (hm.const_mul _) (integrable_const _), integral_const_mul,
        integral_const_mul (-D.s), integral_const, integral_id_gaussianReal]
      simp
    rw [hGf]
    have hnc : ncPurchase v z μ Q = min (μ + z * Real.sqrt v) Q := rfl
    rw [hnc]
    by_cases hv : v = 0
    · subst hv
      simp only [NNReal.coe_zero, Real.sqrt_zero, mul_zero, add_zero]
      rw [gaussianReal_zero_var] at *
      have hX0 : Integrable id (Measure.dirac μ) := by
        have := hX μ; rwa [gaussianReal_zero_var] at this
      classical
      refine constrained (Measure.dirac μ) hX0 _ _ (kR D) μ _ ha hab ?_ ?_ ?_ ?_ Q r
      · intro t ht; rw [dirac_real μ measurableSet_Ici, if_pos (show μ ∈ Ici t from ht)]
        linarith
      · intro t ht; rw [cdf_eq_real, dirac_real μ measurableSet_Iic,
          if_neg (show μ ∉ Iic t by simp only [mem_Iic, not_le]; exact ht)]; exact hk0
      · intro t ht; rw [cdf_eq_real, dirac_real μ measurableSet_Iic,
          if_pos (show μ ∈ Iic t from ht)]; exact hk1.le
      · intro t ht; rw [cdf_eq_real, dirac_real μ measurableSet_Iic,
          if_pos (show μ ∈ Iic t from ht.le)]; exact hk1
    · have h0 := gauss_cdf_z D v hv z μ hz
      have hsm := gauss_strict μ v hv
      refine constrained (gaussianReal μ v) (hX μ) _ _ (kR D) (μ + z * Real.sqrt v) _ ha hab
        ?_ ?_ ?_ ?_ Q r
      · intro t ht
        have hI : (gaussianReal μ v).real (Ioi t) ≤ (gaussianReal μ v).real (Ici t) :=
          measureReal_mono Ioi_subset_Ici_self
        rw [real_Ioi] at hI
        have := monotone_cdf (gaussianReal μ v) ht
        linarith
      · intro t ht; rw [← h0]; exact hsm ht
      · intro t ht; rw [← h0]; exact monotone_cdf _ ht
      · intro t ht; rw [← h0]; exact hsm ht
