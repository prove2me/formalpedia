-- Prove2me | solution 1 for RobustOpt2009.MatrixChance.theorem_B_5_1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-31T06:15:02.146216+00:00
-- url     : https://prove2.me/submissions/314c10e9-045e-4f35-a85e-a4db7597b33d
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_RobustOpt2009_MatrixChance_borell_enlargement_B_5

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace MCB51Aux

open RobustOpt2009.MatrixChance

lemma normalTail_coe (t : ℝ) : normalTail (t : EReal) = (gaussianReal 0 1 (Set.Ioi t)).toReal := by
  unfold normalTail
  congr 2
  ext x; simp [EReal.coe_lt_coe_iff]

lemma normalTail_nonneg (t : EReal) : 0 ≤ normalTail t := ENNReal.toReal_nonneg

lemma normalTail_top : normalTail ⊤ = 0 := by
  unfold normalTail
  have : {x : ℝ | (⊤ : EReal) < (x : EReal)} = ∅ := by
    ext x; simp
  rw [this]; simp

lemma normalTail_anti {s t : EReal} (h : s ≤ t) : normalTail t ≤ normalTail s := by
  unfold normalTail
  exact ENNReal.toReal_mono (measure_ne_top _ _)
    (measure_mono fun x hx => lt_of_le_of_lt h hx)

lemma gaussianEnvelope_nonneg (t : EReal) : 0 ≤ gaussianEnvelope t := by
  unfold gaussianEnvelope
  split_ifs
  · exact le_rfl
  · exact (Real.exp_pos _).le

lemma gaussianEnvelope_coe (s : ℝ) : gaussianEnvelope (s : EReal) = Real.exp (-(s ^ 2) / 2) := by
  unfold gaussianEnvelope
  rw [if_neg (by simp)]
  simp

lemma gaussian_Ioi_zero : gaussianReal 0 1 (Set.Ioi 0) = 1 / 2 := by
  have hns := nullSingletonClass_gaussianReal (μ := 0) (v := 1) one_ne_zero
  have hsymm : gaussianReal 0 1 (Set.Iio 0) = gaussianReal 0 1 (Set.Ioi 0) := by
    have h := gaussianReal_map_neg (μ := (0 : ℝ)) (v := 1)
    rw [neg_zero] at h
    conv_rhs => rw [← h]
    rw [Measure.map_apply measurable_neg measurableSet_Ioi]
    congr 1
    ext x; simp
  have hunion : Set.Iio (0 : ℝ) ∪ {0} ∪ Set.Ioi 0 = Set.univ := by
    ext x; simp only [Set.mem_union, Set.mem_Iio, Set.mem_singleton_iff, Set.mem_Ioi, Set.mem_univ,
      iff_true]
    rcases lt_trichotomy x 0 with h | h | h
    · exact Or.inl (Or.inl h)
    · exact Or.inl (Or.inr h)
    · exact Or.inr h
  have h1 : gaussianReal 0 1 (Set.Iio (0 : ℝ) ∪ {0} ∪ Set.Ioi 0) = 1 := by
    rw [hunion, measure_univ]
  rw [measure_union (by
      rw [Set.disjoint_union_left]; constructor
      · exact Set.disjoint_left.2 fun x hx hx' => by simp at hx hx'; linarith
      · exact Set.disjoint_left.2 fun x hx hx' => by simp at hx hx'; linarith) measurableSet_Ioi,
    measure_union (Set.disjoint_left.2 fun x hx hx' => by simp at hx hx'; linarith)
      (measurableSet_singleton 0), measure_singleton, add_zero, hsymm] at h1
  rw [← two_mul] at h1
  rw [ENNReal.eq_div_iff two_ne_zero ENNReal.ofNat_ne_top]
  exact h1

lemma gaussian_tail_le (s : ℝ) (hs : 0 ≤ s) :
    gaussianReal 0 1 (Set.Ioi s) ≤ ENNReal.ofReal (Real.exp (-(s ^ 2) / 2)) * (1 / 2) := by
  rw [gaussianReal_apply 0 one_ne_zero]
  have hpt : ∀ x ∈ Set.Ioi s, gaussianPDF 0 1 x ≤
      ENNReal.ofReal (Real.exp (-(s ^ 2) / 2)) * gaussianPDF 0 1 (x - s) := by
    intro x hx
    simp only [gaussianPDF_def, gaussianPDFReal_def]
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le]
    apply ENNReal.ofReal_le_ofReal
    have hx' : s < x := hx
    have hc : 0 ≤ (√(2 * Real.pi * ((1 : NNReal) : ℝ)))⁻¹ := by positivity
    rw [mul_left_comm]
    apply mul_le_mul_of_nonneg_left _ hc
    rw [← Real.exp_add]
    apply Real.exp_le_exp.2
    simp only [NNReal.coe_one, mul_one, sub_zero]
    nlinarith [mul_nonneg hs (sub_nonneg.2 hx'.le)]
  calc ∫⁻ x in Set.Ioi s, gaussianPDF 0 1 x
      ≤ ∫⁻ x in Set.Ioi s, ENNReal.ofReal (Real.exp (-(s ^ 2) / 2)) * gaussianPDF 0 1 (x - s) :=
        setLIntegral_mono' measurableSet_Ioi hpt
    _ = ENNReal.ofReal (Real.exp (-(s ^ 2) / 2)) * ∫⁻ x in Set.Ioi s, gaussianPDF 0 1 (x - s) := by
        rw [lintegral_const_mul]
        exact (measurable_gaussianPDF 0 1).comp (measurable_id.sub_const s)
    _ = ENNReal.ofReal (Real.exp (-(s ^ 2) / 2)) * (1 / 2) := by
        congr 1
        have e1 : ∫⁻ x in Set.Ioi s, gaussianPDF 0 1 (x - s) =
            ∫⁻ x, (Set.Ioi (0 : ℝ)).indicator (gaussianPDF 0 1) (x - s) := by
          rw [← lintegral_indicator measurableSet_Ioi]
          congr 1; funext x
          simp only [Set.indicator, Set.mem_Ioi, sub_pos]
        rw [e1, lintegral_sub_right_eq_self (fun x => (Set.Ioi (0 : ℝ)).indicator (gaussianPDF 0 1) x) s,
          lintegral_indicator measurableSet_Ioi, ← gaussianReal_apply 0 one_ne_zero, gaussian_Ioi_zero]

lemma tq_le_of {p : ℝ} {t : EReal} (h : normalTail t ≤ p) : tailQuantile p ≤ t :=
  sInf_le h

lemma lt_normalTail_of_lt_tq {p : ℝ} {t : EReal} (h : t < tailQuantile p) : p < normalTail t := by
  by_contra h'
  exact absurd (tq_le_of (not_lt.1 h')) (not_le.2 h)

lemma real_lt_toReal_of {a : ℝ} {b : ENNReal} (hb : b ≠ ⊤) (h : ENNReal.ofReal a < b) :
    a < b.toReal := by
  rcases lt_or_ge a 0 with ha | ha
  · exact lt_of_lt_of_le ha ENNReal.toReal_nonneg
  · exact (ENNReal.ofReal_lt_iff_lt_toReal ha hb).1 h

lemma tq_pos {χ : ℝ} (hχ : 1 / 2 < χ) : 0 < tailQuantile (1 - χ) := by
  have hmono : Monotone (fun n : ℕ => Set.Ioi (1 / ((n : ℝ) + 1))) := by
    intro n n' h x hx
    simp only [Set.mem_Ioi] at hx ⊢
    refine lt_of_le_of_lt ?_ hx
    exact one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right h 1)
  have hU : (⋃ n : ℕ, Set.Ioi (1 / ((n : ℝ) + 1))) = Set.Ioi 0 := by
    ext x
    simp only [Set.mem_iUnion, Set.mem_Ioi]
    constructor
    · rintro ⟨n, hn⟩; exact lt_trans (by positivity) hn
    · intro hx
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt hx
      exact ⟨n, hn⟩
  have hlim := tendsto_measure_iUnion_atTop (μ := gaussianReal 0 1) hmono
  rw [hU, gaussian_Ioi_zero] at hlim
  have hhalf : (1 / 2 : ENNReal) = ENNReal.ofReal (1 / 2) := by
    rw [ENNReal.ofReal_div_of_pos two_pos]; simp
  have hlt : ENNReal.ofReal (1 - χ) < 1 / 2 := by
    rw [hhalf, ENNReal.ofReal_lt_ofReal_iff (by norm_num)]
    linarith
  obtain ⟨n, hn⟩ := (hlim.eventually (lt_mem_nhds hlt)).exists
  have hδ : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
  refine lt_of_lt_of_le (EReal.coe_lt_coe_iff.2 hδ) ?_
  refine le_sInf fun t ht => ?_
  by_contra hcon
  rw [not_le] at hcon
  have hsub : Set.Ioi (1 / ((n : ℝ) + 1)) ⊆ {x : ℝ | t < (x : EReal)} := by
    intro x hx
    exact lt_trans hcon (EReal.coe_lt_coe_iff.2 hx)
  have h1 : (gaussianReal 0 1 (Set.Ioi (1 / ((n : ℝ) + 1)))).toReal ≤ normalTail t :=
    ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono hsub)
  have h2 := real_lt_toReal_of (measure_ne_top _ _) hn
  have h3 : normalTail t ≤ 1 - χ := ht
  linarith

lemma halfspace {m : ℕ} (L : StrongDual ℝ (EuclideanSpace ℝ (Fin m))) (hL : ‖L‖ = 1) (r : ℝ) :
    stdGaussian (EuclideanSpace ℝ (Fin m)) {y | r < L y} = gaussianReal 0 1 (Set.Ioi r) := by
  have hmap : (stdGaussian (EuclideanSpace ℝ (Fin m))).map L = gaussianReal 0 1 := by
    rw [IsGaussian.map_eq_gaussianReal L, integral_strongDual_stdGaussian,
      variance_dual_stdGaussian, hL]
    simp
  rw [← hmap, Measure.map_apply L.continuous.measurable measurableSet_Ioi]
  rfl

lemma toReal_compl {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ]
    {S : Set α} (hS : MeasurableSet S) : (μ Sᶜ).toReal = 1 - (μ S).toReal := by
  have h := measure_add_measure_compl (μ := μ) hS
  rw [measure_univ] at h
  have h2 := congrArg ENNReal.toReal h
  rw [ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _), ENNReal.toReal_one] at h2
  linarith

lemma part_i {m : ℕ} (Q : Set (EuclideanSpace ℝ (Fin m))) (χ : ℝ) (hQc : IsClosed Q)
    (hQconv : Convex ℝ Q) (hχ : 0 < χ)
    (hprob : χ ≤ ((stdGaussian (EuclideanSpace ℝ (Fin m))) Q).toReal) :
    {x : EuclideanSpace ℝ (Fin m) | (‖x‖ : EReal) ≤ tailQuantile (1 - χ)} ⊆ Q := by
  intro x hx
  by_contra hxQ
  obtain ⟨f, u, hfQ, hux⟩ := geometric_hahn_banach_closed_point hQconv hQc hxQ
  have hQne : Q.Nonempty := by
    rcases Q.eq_empty_or_nonempty with h | h
    · rw [h] at hprob; simp at hprob; linarith
    · exact h
  obtain ⟨a, ha⟩ := hQne
  have hf0 : ‖f‖ ≠ 0 := by
    intro h
    have hf : f = 0 := norm_eq_zero.1 h
    have h1 := hfQ a ha
    rw [hf] at h1 hux
    simp at h1 hux
    linarith
  have hfpos : 0 < ‖f‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hf0)
  set L : StrongDual ℝ (EuclideanSpace ℝ (Fin m)) := ‖f‖⁻¹ • f with hLdef
  have hL : ‖L‖ = 1 := by
    rw [hLdef, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hf0]
  set r := u / ‖f‖ with hr
  have hLy : ∀ y, L y = f y / ‖f‖ := by
    intro y; rw [hLdef]; simp [div_eq_inv_mul]
  have hsub : Q ⊆ {y | r < L y}ᶜ := by
    intro y hy
    simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, not_lt]
    rw [hLy, hr]
    exact (div_le_div_iff_of_pos_right hfpos).2 (hfQ y hy).le
  have hmeasS : MeasurableSet {y : EuclideanSpace ℝ (Fin m) | r < L y} :=
    measurableSet_lt measurable_const L.continuous.measurable
  have h1 : ((stdGaussian (EuclideanSpace ℝ (Fin m))) Q).toReal ≤
      1 - (gaussianReal 0 1 (Set.Ioi r)).toReal := by
    rw [← halfspace L hL r, ← toReal_compl _ hmeasS]
    exact ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono hsub)
  have hrx : r < ‖x‖ := by
    have h2 : r < L x := by
      rw [hLy, hr]; exact (div_lt_div_iff_of_pos_right hfpos).2 hux
    have h3 : L x ≤ ‖x‖ := by
      have := L.le_opNorm x
      rw [hL, one_mul] at this
      exact le_trans (le_abs_self _) (by simpa [Real.norm_eq_abs] using this)
    linarith
  have h4 : ((r : ℝ) : EReal) < tailQuantile (1 - χ) :=
    lt_of_lt_of_le (EReal.coe_lt_coe_iff.2 hrx) hx
  have h5 := lt_normalTail_of_lt_tq h4
  rw [normalTail_coe] at h5
  linarith

lemma tail_half_env (s : ℝ) (hs : 0 ≤ s) :
    normalTail (s : EReal) ≤ (1 / 2) * gaussianEnvelope (s : EReal) := by
  rw [normalTail_coe, gaussianEnvelope_coe]
  have h := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (by simp)) (gaussian_tail_le s hs)
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.exp_pos _).le] at h
  have h2 : (1 / 2 : ENNReal).toReal = 1 / 2 := by simp
  rw [h2] at h
  linarith

lemma part_ii {m : ℕ} (Q : Set (EuclideanSpace ℝ (Fin m))) (χ : ℝ) (hQc : IsClosed Q)
    (hQconv : Convex ℝ Q) (hχ : 1 / 2 < χ)
    (hprob : χ ≤ ((stdGaussian (EuclideanSpace ℝ (Fin m))) Q).toReal)
    (r : ℝ) (hqr : tailQuantile (1 - χ) ≤ (r : EReal))
    (hball : Metric.closedBall (0 : EuclideanSpace ℝ (Fin m)) r ⊆ Q) (α : ℝ) (hα : 1 ≤ α) :
    ((stdGaussian (EuclideanSpace ℝ (Fin m))) ((fun x => α • x) '' Q)ᶜ).toReal ≤
        normalTail (tailQuantile (1 - χ) + (((α - 1) * r : ℝ) : EReal)) ∧
      normalTail (tailQuantile (1 - χ) + (((α - 1) * r : ℝ) : EReal)) ≤
        normalTail ((α : EReal) * tailQuantile (1 - χ)) ∧
      normalTail ((α : EReal) * tailQuantile (1 - χ)) ≤
        (1 / 2) * gaussianEnvelope ((α : EReal) * tailQuantile (1 - χ)) := by
  have hqpos := tq_pos hχ
  have htop : tailQuantile (1 - χ) ≠ ⊤ := ne_top_of_le_ne_top (EReal.coe_ne_top r) hqr
  have hbot : tailQuantile (1 - χ) ≠ ⊥ := ne_bot_of_gt hqpos
  set q0 := (tailQuantile (1 - χ)).toReal with hq0
  have hq : tailQuantile (1 - χ) = (q0 : EReal) := (EReal.coe_toReal htop hbot).symm
  have hq0pos : 0 < q0 := by
    have := hqpos; rw [hq] at this; exact_mod_cast this
  have hq0r : q0 ≤ r := by
    have := hqr; rw [hq] at this; exact_mod_cast this
  have hr0 : 0 ≤ r := le_trans hq0pos.le hq0r
  have hε : 0 ≤ (α - 1) * r := mul_nonneg (by linarith) hr0
  have hincl : ((fun x => α • x) '' Q)ᶜ ⊆ {x | (α - 1) * r < Metric.infDist x Q} := by
    intro x hx
    by_contra hcon
    simp only [Set.mem_ofPred_eq, not_lt] at hcon
    have h0Q : (0 : EuclideanSpace ℝ (Fin m)) ∈ Q := hball (Metric.mem_closedBall_self hr0)
    obtain ⟨y, hyQ, hyd⟩ := hQc.exists_infDist_eq_dist ⟨0, h0Q⟩ x
    apply hx
    rcases eq_or_lt_of_le hα with h1 | h1
    · subst h1
      have : dist x y ≤ 0 := by rw [← hyd]; simpa using hcon
      have hxy : x = y := dist_le_zero.1 this
      exact ⟨y, hyQ, by simp [hxy]⟩
    · have hα1 : 0 < α - 1 := by linarith
      set w := (α - 1)⁻¹ • (x - y) with hw
      have hwQ : w ∈ Q := by
        apply hball
        rw [mem_closedBall_zero_iff, hw, norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos hα1,
          ← dist_eq_norm, ← hyd, inv_mul_le_iff₀ hα1]
        linarith
      have hαpos : 0 < α := by linarith
      have hz : α⁻¹ • y + (1 - α⁻¹) • w ∈ Q :=
        hQconv hyQ hwQ (inv_nonneg.2 hαpos.le) (by
          rw [sub_nonneg]; exact inv_le_one_of_one_le₀ hα) (by ring)
      refine ⟨α⁻¹ • y + (1 - α⁻¹) • w, hz, ?_⟩
      show α • (α⁻¹ • y + (1 - α⁻¹) • w) = x
      rw [hw, smul_add, smul_smul, smul_smul, smul_smul, mul_inv_cancel₀ hαpos.ne', one_smul]
      have : α * (1 - α⁻¹) * (α - 1)⁻¹ = 1 := by field_simp
      rw [this, one_smul]; abel
  have hB := borell_enlargement_B_5 Q χ ((α - 1) * r) hQc (by linarith) hε hprob
  refine ⟨le_trans (ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono hincl)) hB, ?_, ?_⟩
  · apply normalTail_anti
    rw [hq, ← EReal.coe_mul, ← EReal.coe_add, EReal.coe_le_coe_iff]
    nlinarith
  · rw [hq, ← EReal.coe_mul]
    exact tail_half_env _ (mul_nonneg (by linarith) hq0pos.le)

end MCB51Aux

open RobustOpt2009.MatrixChance MCB51Aux

theorem solution {m : ℕ} [NeZero m] :
    (∀ (Q : Set (EuclideanSpace ℝ (Fin m))) (χ : ℝ),
      IsClosed Q → Convex ℝ Q → (1 / 2 : ℝ) < χ →
      χ ≤ ((stdGaussian (EuclideanSpace ℝ (Fin m))) Q).toReal →
      0 < tailQuantile (1 - χ) ∧
      {x : EuclideanSpace ℝ (Fin m) | (‖x‖ : EReal) ≤ tailQuantile (1 - χ)} ⊆ Q ∧
      (∀ r : ℝ, tailQuantile (1 - χ) ≤ (r : EReal) →
        Metric.closedBall (0 : EuclideanSpace ℝ (Fin m)) r ⊆ Q →
        ∀ α : ℝ, 1 ≤ α →
          ((stdGaussian (EuclideanSpace ℝ (Fin m))) ((fun x => α • x) '' Q)ᶜ).toReal ≤
            normalTail (tailQuantile (1 - χ) + (((α - 1) * r : ℝ) : EReal)) ∧
          normalTail (tailQuantile (1 - χ) + (((α - 1) * r : ℝ) : EReal)) ≤
            normalTail ((α : EReal) * tailQuantile (1 - χ)) ∧
          normalTail ((α : EReal) * tailQuantile (1 - χ)) ≤
            (1 / 2) * gaussianEnvelope ((α : EReal) * tailQuantile (1 - χ)))) ∧
    (∀ (C : Matrix (Fin m) (Fin m) ℝ), C.PosSemidef →
      ∀ (Q : Set (EuclideanSpace ℝ (Fin m))) (δ α : ℝ),
        IsClosed Q → Convex ℝ Q → δ < (1 / 2 : ℝ) → 1 ≤ α →
        ((multivariateGaussian 0 C) Qᶜ).toReal ≤ δ →
        ((multivariateGaussian 0 C) ((fun x => α • x) '' Q)ᶜ).toReal ≤
          normalTail ((α : EReal) * tailQuantile δ) ∧
        normalTail ((α : EReal) * tailQuantile δ) ≤
          (1 / 2) * gaussianEnvelope ((α : EReal) * tailQuantile δ)) := by
  refine ⟨fun Q χ hQc hQconv hχ hprob =>
    ⟨tq_pos hχ, part_i Q χ hQc hQconv (by linarith) hprob,
      fun r hqr hball α hα => part_ii Q χ hQc hQconv hχ hprob r hqr hball α hα⟩, ?_⟩
  intro C _hC Q δ α hQc hQconv hδ hα hfail
  have hαpos : 0 < α := by linarith
  obtain ⟨T, hmG⟩ : ∃ T : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m),
      multivariateGaussian 0 C = (stdGaussian (EuclideanSpace ℝ (Fin m))).map T := by
    open scoped MatrixOrder in
    exact ⟨Matrix.toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt C), by
      rw [multivariateGaussian]
      congr 1
      funext x; simp⟩
  have hTm : Measurable T := T.continuous.measurable
  set Q' := T ⁻¹' Q with hQ'
  have hQ'c : IsClosed Q' := hQc.preimage T.continuous
  have hQ'conv : Convex ℝ Q' := hQconv.linear_preimage (T : EuclideanSpace ℝ (Fin m) →ₗ[ℝ] _)
  have hαQc : IsClosed ((fun x => α • x) '' Q) :=
    (Homeomorph.smulOfNeZero α hαpos.ne').isClosedMap Q hQc
  have hfail' : (stdGaussian (EuclideanSpace ℝ (Fin m)) Q'ᶜ).toReal ≤ δ := by
    rw [hmG, Measure.map_apply hTm hQc.measurableSet.compl] at hfail
    exact hfail
  have hprob' : 1 - δ ≤ (stdGaussian (EuclideanSpace ℝ (Fin m)) Q').toReal := by
    have := toReal_compl (stdGaussian (EuclideanSpace ℝ (Fin m))) hQ'c.measurableSet
    linarith
  have hχ' : (1 / 2 : ℝ) < 1 - δ := by linarith
  have hqδ : tailQuantile (1 - (1 - δ)) = tailQuantile δ := by congr 1; ring
  have hball' := part_i Q' (1 - δ) hQ'c hQ'conv (by linarith) hprob'
  rw [hqδ] at hball'
  have hincl : T ⁻¹' ((fun x => α • x) '' Q)ᶜ ⊆ ((fun x => α • x) '' Q')ᶜ := by
    intro x hx hx'
    obtain ⟨y, hy, rfl⟩ := hx'
    apply hx
    exact ⟨T y, hy, by simp [map_smul]⟩
  have hstep : ((multivariateGaussian 0 C) ((fun x => α • x) '' Q)ᶜ).toReal ≤
      ((stdGaussian (EuclideanSpace ℝ (Fin m))) ((fun x => α • x) '' Q')ᶜ).toReal := by
    rw [hmG, Measure.map_apply hTm hαQc.measurableSet.compl]
    exact ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono hincl)
  by_cases htop : tailQuantile δ = ⊤
  · have hall : ((fun x => α • x) '' Q')ᶜ = ∅ := by
      ext x
      simp only [Set.mem_compl_iff, Set.mem_empty_iff_false, iff_false, not_not]
      refine ⟨α⁻¹ • x, hball' (by simp only [Set.mem_ofPred_eq, htop]; exact le_top), ?_⟩
      show α • α⁻¹ • x = x
      rw [smul_smul, mul_inv_cancel₀ hαpos.ne', one_smul]
    rw [hall, measure_empty, ENNReal.toReal_zero] at hstep
    rw [htop, EReal.coe_mul_top_of_pos hαpos, normalTail_top]
    refine ⟨hstep, ?_⟩
    unfold gaussianEnvelope
    simp
  · have hqpos := tq_pos hχ'
    rw [hqδ] at hqpos
    have hbot : tailQuantile δ ≠ ⊥ := ne_bot_of_gt hqpos
    set q0 := (tailQuantile δ).toReal with hq0
    have hq : tailQuantile δ = (q0 : EReal) := (EReal.coe_toReal htop hbot).symm
    have hballr : Metric.closedBall (0 : EuclideanSpace ℝ (Fin m)) q0 ⊆ Q' := by
      intro x hx
      rw [mem_closedBall_zero_iff] at hx
      exact hball' (by rw [hq]; exact_mod_cast hx)
    obtain ⟨h1, h2, h3⟩ := part_ii Q' (1 - δ) hQ'c hQ'conv hχ' hprob' q0
      (by rw [hqδ, hq]) hballr α hα
    rw [hqδ] at h1 h2 h3
    exact ⟨le_trans hstep (le_trans h1 h2), h3⟩
