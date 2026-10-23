-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Claimed50.P22.finiteMeasure_Lp_inclusion_and_strictness
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T07:16:22.606962+00:00
-- url     : https://prove2.me/submissions/d801b51b-74fd-4c45-8ad8-a10396bfa538

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P22

noncomputable section

open Set Filter Topology MeasureTheory
open scoped ENNReal

universe u

namespace X6P22

/-- Part 1: inclusion `Lq → Lp` on a finite measure space. -/
lemma part1 {X : Type*} [MeasurableSpace X] (mu : Measure X) [IsFiniteMeasure mu]
    (p q : ℝ≥0∞) (hp : 1 ≤ p) (hpq : p < q) (hq : q < ⊤) :
    letI : Fact (1 ≤ p) := ⟨hp⟩
    letI : Fact (1 ≤ q) := ⟨le_trans hp (le_of_lt hpq)⟩
    (∃ J : Lp ℂ q mu →L[ℂ] Lp ℂ p mu,
      Function.Injective J ∧ ∀ f : Lp ℂ q mu, ∀ᵐ x ∂mu, J f x = f x) := by
  letI : Fact (1 ≤ p) := ⟨hp⟩
  letI : Fact (1 ≤ q) := ⟨le_trans hp (le_of_lt hpq)⟩
  let L : Lp ℂ q mu →ₗ[ℂ] Lp ℂ p mu :=
    { toFun := fun f => ((Lp.memLp f).mono_exponent hpq.le).toLp f
      map_add' := by
        intro f g
        apply Lp.ext
        filter_upwards [MemLp.coeFn_toLp ((Lp.memLp (f + g)).mono_exponent hpq.le),
          MemLp.coeFn_toLp ((Lp.memLp f).mono_exponent hpq.le),
          MemLp.coeFn_toLp ((Lp.memLp g).mono_exponent hpq.le),
          Lp.coeFn_add f g,
          Lp.coeFn_add (((Lp.memLp f).mono_exponent hpq.le).toLp f)
            (((Lp.memLp g).mono_exponent hpq.le).toLp g)] with x h1 h2 h3 h4 h5
        rw [h5, Pi.add_apply, h1, h2, h3, h4, Pi.add_apply]
      map_smul' := by
        intro c f
        apply Lp.ext
        filter_upwards [MemLp.coeFn_toLp ((Lp.memLp (c • f)).mono_exponent hpq.le),
          MemLp.coeFn_toLp ((Lp.memLp f).mono_exponent hpq.le),
          Lp.coeFn_smul c f,
          Lp.coeFn_smul c (((Lp.memLp f).mono_exponent hpq.le).toLp f)] with x h1 h2 h3 h4
        rw [RingHom.id_apply, h4, Pi.smul_apply, h1, h2, h3, Pi.smul_apply] }
  have hL : ∀ f, (L f : X → ℂ) =ᵐ[mu] f := fun f =>
    MemLp.coeFn_toLp ((Lp.memLp f).mono_exponent hpq.le)
  let C : ℝ := (mu Set.univ ^ (1 / p.toReal - 1 / q.toReal)).toReal
  have hbound : ∀ f, ‖L f‖ ≤ C * ‖f‖ := by
    intro f
    rw [Lp.norm_def, Lp.norm_def, eLpNorm_congr_ae (hL f), mul_comm, ← ENNReal.toReal_mul]
    apply ENNReal.toReal_mono
    · apply ENNReal.mul_ne_top (Lp.eLpNorm_ne_top f)
      apply ENNReal.rpow_ne_top_of_nonneg _ (measure_ne_top _ _)
      rw [sub_nonneg]
      have hp0 : 0 < p.toReal := ENNReal.toReal_pos
        (by intro h0; rw [h0] at hp; simp at hp) (hpq.trans hq).ne
      have : p.toReal ≤ q.toReal := ENNReal.toReal_mono hq.ne hpq.le
      exact one_div_le_one_div_of_le hp0 this
    · exact eLpNorm_le_eLpNorm_mul_rpow_measure_univ hpq.le (Lp.aestronglyMeasurable f)
  refine ⟨L.mkContinuous C hbound, ?_, fun f => hL f⟩
  intro f g hfg
  apply Lp.ext
  have h1 := hL f
  have h2 := hL g
  have h3 : (L f : X → ℂ) =ᵐ[mu] (L g : X → ℂ) := by
    have : L f = L g := hfg
    rw [this]
  filter_upwards [h1, h2, h3] with x a b c
  rw [← a, ← b, c]


lemma enorm_ofReal_toReal (c : ℝ≥0∞) (hc : c ≠ ⊤) : ‖((c.toReal : ℝ) : ℂ)‖ₑ = c := by
  rw [show ((c.toReal : ℝ) : ℂ) = ((c.toReal : ℝ) : ℂ) from rfl]
  rw [← ofReal_norm, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hc]

/-- Part 2: strictness under a dyadic partition. -/
lemma part2 {X : Type*} [MeasurableSpace X] (mu : Measure X) [IsFiniteMeasure mu]
    (p q : ℝ≥0∞) (hp : 1 ≤ p) (hpq : p < q) (hq : q < ⊤) :
    (∃ A : ℕ → Set X,
      (∀ n, MeasurableSet (A n)) ∧
      (Pairwise (fun n m => Disjoint (A n) (A m))) ∧
      (⋃ n, A n) = Set.univ ∧
      ∀ n, 0 < mu (A n) ∧
        mu (A n) ≤ ((2 : ENNReal) ^ (n + 1))⁻¹ * mu Set.univ) →
      ∃ f : X → ℂ, MemLp f p mu ∧ ¬ MemLp f q mu := by
  rintro ⟨A, hmeas, hdisj, hcover, hA⟩
  have hp0 : p ≠ 0 := by intro h0; rw [h0] at hp; simp at hp
  have hq0 : q ≠ 0 := (lt_of_le_of_lt bot_le hpq).ne'
  have hpt : p ≠ ⊤ := (hpq.trans hq).ne
  have hqt : q ≠ ⊤ := hq.ne
  set pr := p.toReal
  set qr := q.toReal
  have hpr : 0 < pr := ENNReal.toReal_pos hp0 hpt
  have hqr : 0 < qr := ENNReal.toReal_pos hq0 hqt
  have hprq : pr < qr := (ENNReal.toReal_lt_toReal hpt hqt).2 hpq
  have hex : ∀ x, ∃ n, x ∈ A n := by
    intro x
    have : x ∈ ⋃ n, A n := by rw [hcover]; trivial
    simpa using this
  classical
  let idx : X → ℕ := fun x => Nat.find (hex x)
  have hidx : ∀ n, ∀ x ∈ A n, idx x = n := by
    intro n x hx
    by_contra hne
    exact Set.disjoint_left.1 (hdisj hne) (Nat.find_spec (hex x)) hx
  have hidx_meas : Measurable idx := measurable_find hex hmeas
  set m : ℕ → ℝ≥0∞ := fun n => mu (A n)
  have hm0 : ∀ n, m n ≠ 0 := fun n => (hA n).1.ne'
  have hmt : ∀ n, m n ≠ ⊤ := fun n => measure_ne_top _ _
  let c : ℕ → ℝ≥0∞ := fun n => m n ^ (-(1 / qr))
  have hct : ∀ n, c n ≠ ⊤ := fun n =>
    ENNReal.rpow_ne_top_of_ne_zero (hm0 n) (hmt n)
  let f : X → ℂ := fun x => (((c (idx x)).toReal : ℝ) : ℂ)
  have hfm : Measurable f := by
    have : Measurable (fun n : ℕ => (((c n).toReal : ℝ) : ℂ)) := measurable_from_nat
    exact this.comp hidx_meas
  -- lintegral formula
  have hint : ∀ r : ℝ, ∫⁻ x, ‖f x‖ₑ ^ r ∂mu = ∑' n, c n ^ r * m n := by
    intro r
    rw [← setLIntegral_univ, ← hcover, lintegral_iUnion hmeas hdisj]
    congr 1
    ext n
    rw [setLIntegral_congr_fun (hmeas n) (g := fun _ => c n ^ r)]
    · rw [setLIntegral_const]
    · intro x hx
      simp only [f, hidx n x hx, enorm_ofReal_toReal _ (hct n)]
  refine ⟨f, ?_, ?_⟩
  · refine ⟨hfm.aestronglyMeasurable, ?_⟩
    rw [eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top hp0 hpt, hint]
    set M := mu Set.univ
    set s : ℝ := 1 - pr / qr
    have hs : 0 < s := by
      simp only [s]; rw [sub_pos, div_lt_one hqr]; exact hprq
    set r : ℝ≥0∞ := ((2 : ℝ≥0∞) ^ s)⁻¹
    have hr : r < 1 := by
      simp only [r]
      rw [ENNReal.inv_lt_one]
      exact ENNReal.one_lt_rpow (by norm_num) hs
    have hle : ∀ n, c n ^ pr * m n ≤ M ^ s * r ^ n := by
      intro n
      have e1 : c n ^ pr * m n = m n ^ s := by
        simp only [c]
        rw [← ENNReal.rpow_mul]
        conv_lhs => rw [show m n = m n ^ (1 : ℝ) by rw [ENNReal.rpow_one]]
        rw [← ENNReal.rpow_mul, ← ENNReal.rpow_add _ _ (hm0 n) (hmt n)]
        congr 1
        simp only [s]; ring
      rw [e1]
      have h2 : m n ≤ ((2 : ℝ≥0∞) ^ n)⁻¹ * M := by
        refine (hA n).2.trans ?_
        gcongr
        · norm_num
        · omega
      calc m n ^ s ≤ (((2 : ℝ≥0∞) ^ n)⁻¹ * M) ^ s := ENNReal.rpow_le_rpow h2 hs.le
        _ = M ^ s * r ^ n := by
          rw [ENNReal.mul_rpow_of_nonneg _ _ hs.le, mul_comm, ENNReal.inv_rpow]
          simp only [r]
          rw [← ENNReal.inv_pow]
          congr 2
          rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul,
            ← ENNReal.rpow_mul, mul_comm]
    calc ∑' n, c n ^ pr * m n ≤ ∑' n, M ^ s * r ^ n := ENNReal.tsum_le_tsum hle
      _ = M ^ s * (1 - r)⁻¹ := by rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric]
      _ < ⊤ := by
        apply ENNReal.mul_lt_top
        · exact ENNReal.rpow_lt_top_of_nonneg hs.le (measure_ne_top _ _)
        · rw [ENNReal.inv_lt_top]; exact tsub_pos_of_lt hr
  · intro hf
    have := hf.2
    rw [eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top hq0 hqt, hint] at this
    have h1 : ∀ n, c n ^ qr * m n = 1 := by
      intro n
      simp only [c]
      rw [← ENNReal.rpow_mul, show -(1 / qr) * qr = -1 by field_simp, ENNReal.rpow_neg_one,
        ENNReal.inv_mul_cancel (hm0 n) (hmt n)]
    rw [show (fun n => c n ^ qr * m n) = fun _ => 1 from funext h1,
      ENNReal.tsum_const_eq_top_of_ne_zero one_ne_zero] at this
    exact lt_irrefl _ this


/-- distribution function of `Y`. -/
lemma dist_fn (Y : Set ℝ) (hsub : Y ⊆ Set.Icc 0 1) :
    ∀ k : ℕ, ∃ t ∈ Set.Icc (0 : ℝ) 1,
      volume (Y ∩ Set.Iic t) = ((2 : ℝ≥0∞) ^ k)⁻¹ * volume Y := by
  have hVt : volume Y ≠ ⊤ :=
    ne_top_of_le_ne_top (by simp [Real.volume_Icc]) (measure_mono hsub)
  let F : ℝ → ℝ := fun t => (volume (Y ∩ Set.Iic t)).toReal
  have hfin : ∀ t, volume (Y ∩ Set.Iic t) ≠ ⊤ := fun t =>
    ne_top_of_le_ne_top hVt (measure_mono Set.inter_subset_left)
  have hmono : Monotone F := by
    intro a b hab
    exact ENNReal.toReal_mono (hfin b) (measure_mono (Set.inter_subset_inter_right _
      (Set.Iic_subset_Iic.2 hab)))
  have hlip : ∀ a b, a ≤ b → F b - F a ≤ b - a := by
    intro a b hab
    have hsplit : Y ∩ Set.Iic b ⊆ (Y ∩ Set.Iic a) ∪ Set.Ioc a b := by
      intro x ⟨hx1, hx2⟩
      by_cases h : x ≤ a
      · exact Or.inl ⟨hx1, h⟩
      · exact Or.inr ⟨lt_of_not_ge h, hx2⟩
    have := (measure_mono hsplit).trans (measure_union_le (μ := volume) _ _)
    rw [Real.volume_Ioc] at this
    have h2 := ENNReal.toReal_mono (by
      exact ENNReal.add_ne_top.2 ⟨hfin a, ENNReal.ofReal_ne_top⟩) this
    rw [ENNReal.toReal_add (hfin a) ENNReal.ofReal_ne_top,
      ENNReal.toReal_ofReal (by linarith)] at h2
    simp only [F]; linarith
  have hcont : Continuous F := by
    rw [Metric.continuous_iff]
    intro b ε hε
    refine ⟨ε, hε, fun a hab => ?_⟩
    rw [Real.dist_eq] at hab ⊢
    rcases le_total a b with h | h
    · have := hlip a b h; have := hmono h
      rw [abs_lt] at hab ⊢; constructor <;> linarith
    · have := hlip b a h; have := hmono h
      rw [abs_lt] at hab ⊢; constructor <;> linarith
  have hF0 : F 0 = 0 := by
    simp only [F]
    have : Y ∩ Set.Iic 0 ⊆ {0} := by
      intro x ⟨hx1, hx2⟩
      have := (hsub hx1).1
      simp only [Set.mem_singleton_iff]; exact le_antisymm hx2 this
    have h0 := measure_mono (μ := volume) this
    rw [Real.volume_singleton, nonpos_iff_eq_zero] at h0
    rw [h0]; rfl
  have hF1 : F 1 = (volume Y).toReal := by
    simp only [F]
    congr 2
    exact Set.inter_eq_left.2 (fun x hx => (hsub hx).2)
  intro k
  have hmem : ((2 : ℝ) ^ k)⁻¹ * (volume Y).toReal ∈ Set.Icc (F 0) (F 1) := by
    rw [hF0, hF1]
    constructor
    · positivity
    · apply mul_le_of_le_one_left ENNReal.toReal_nonneg
      apply inv_le_one_of_one_le₀
      exact one_le_pow₀ (by norm_num)
  obtain ⟨t, ht, hFt⟩ := intermediate_value_Icc (zero_le_one) hcont.continuousOn hmem
  refine ⟨t, ht, ?_⟩
  simp only [F] at hFt
  rw [← ENNReal.ofReal_toReal (hfin t), hFt, ENNReal.ofReal_mul (by positivity),
    ENNReal.ofReal_toReal hVt, ENNReal.ofReal_inv_of_pos (by positivity)]
  congr
  rw [ENNReal.ofReal_pow (by norm_num)]
  simp


lemma part3 (Y : Set ℝ) (hY : MeasurableSet Y) (hsub : Y ⊆ Set.Icc 0 1)
    (hpos : 0 < volume Y) :
    ∃ A : ℕ → Set ℝ,
      (∀ n, MeasurableSet (A n)) ∧
      (Pairwise (fun n m => Disjoint (A n) (A m))) ∧
      (⋃ n, A n) = Y ∧
      ∀ n, 0 < volume (A n) ∧ volume (A n) ≤ ((2 : ENNReal) ^ (n + 1))⁻¹ * volume Y := by
  set V := volume Y with hVdef
  have hVt : V ≠ ⊤ :=
    ne_top_of_le_ne_top (by simp [Real.volume_Icc]) (measure_mono hsub)
  have hV0 : V ≠ 0 := hpos.ne'
  choose s _hs hG using dist_fn Y hsub
  have hfin : ∀ t, volume (Y ∩ Set.Iic t) ≠ ⊤ := fun t =>
    ne_top_of_le_ne_top hVt (measure_mono Set.inter_subset_left)
  have hlt2 : ∀ k : ℕ, ((2 : ℝ≥0∞) ^ (k + 1))⁻¹ * V < ((2 : ℝ≥0∞) ^ k)⁻¹ * V := by
    intro k
    apply ENNReal.mul_lt_mul_left hV0 hVt
    apply ENNReal.inv_lt_inv.2
    exact_mod_cast Nat.pow_lt_pow_right (by norm_num) (Nat.lt_succ_self k)
  have hsdec : StrictAnti s := by
    apply strictAnti_nat_of_succ_lt
    intro k
    by_contra h
    push Not at h
    have := measure_mono (μ := volume) (Set.inter_subset_inter_right Y (Set.Iic_subset_Iic.2 h))
    rw [hG, hG] at this
    exact absurd this (not_le.2 (hlt2 k))
  let B : ℕ → Set ℝ := fun n => Y ∩ Set.Ioc (s (n + 1)) (s n)
  have hBm : ∀ n, MeasurableSet (B n) := fun n => hY.inter measurableSet_Ioc
  have hBY : ∀ n, B n ⊆ Y := fun n => Set.inter_subset_left
  have hBvol : ∀ n, volume (B n) = ((2 : ℝ≥0∞) ^ (n + 1))⁻¹ * V := by
    intro n
    have hu : Y ∩ Set.Iic (s n) = (Y ∩ Set.Iic (s (n + 1))) ∪ B n := by
      ext x
      simp only [B, Set.mem_inter_iff, Set.mem_Iic, Set.mem_union, Set.mem_Ioc]
      constructor
      · rintro ⟨h1, h2⟩
        by_cases h : x ≤ s (n + 1)
        · exact Or.inl ⟨h1, h⟩
        · exact Or.inr ⟨h1, lt_of_not_ge h, h2⟩
      · rintro (⟨h1, h2⟩ | ⟨h1, _, h3⟩)
        · exact ⟨h1, h2.trans (hsdec (Nat.lt_succ_self n)).le⟩
        · exact ⟨h1, h3⟩
    have hd : Disjoint (Y ∩ Set.Iic (s (n + 1))) (B n) := by
      rw [Set.disjoint_left]
      rintro x ⟨_, h1⟩ ⟨_, h2, _⟩
      exact absurd h1 (not_le.2 h2)
    have := measure_union (μ := volume) hd (hBm n)
    rw [← hu, hG, hG] at this
    have h2 : ((2 : ℝ≥0∞) ^ n)⁻¹ * V =
        ((2 : ℝ≥0∞) ^ (n + 1))⁻¹ * V + ((2 : ℝ≥0∞) ^ (n + 1))⁻¹ * V := by
      rw [← add_mul, pow_succ, ENNReal.mul_inv (Or.inl (by simp)) (Or.inl (by simp)),
        ← mul_add, ENNReal.inv_two_add_inv_two, mul_one]
    rw [h2] at this
    exact (ENNReal.add_right_inj (ENNReal.mul_ne_top (by simp) hVt)).1 this |>.symm
  have hBdisj : Pairwise (fun j k => Disjoint (B j) (B k)) := by
    have key : ∀ j k, j < k → Disjoint (B j) (B k) := by
      intro j k hjk
      rw [Set.disjoint_left]
      rintro x ⟨_, h1, _⟩ ⟨_, _, h2⟩
      have : s k ≤ s (j + 1) := hsdec.antitone (by omega)
      linarith
    intro j k hjk
    rcases lt_or_gt_of_ne hjk with h | h
    · exact key j k h
    · exact (key k j h).symm
  let A0 : Set ℝ := Y \ ⋃ k, B (k + 1)
  have hA0m : MeasurableSet A0 := hY.diff (MeasurableSet.iUnion fun k => hBm (k + 1))
  have hA0vol : volume A0 = ((2 : ℝ≥0∞) ^ (0 + 1))⁻¹ * V := by
    have hU : Y = A0 ∪ ⋃ k, B (k + 1) := by
      simp only [A0]
      rw [Set.sdiff_union_self, Set.union_eq_left.2 (Set.iUnion_subset fun k => hBY (k + 1))]
    have hdis : Disjoint A0 (⋃ k, B (k + 1)) := Set.disjoint_sdiff_left
    have h1 := measure_union (μ := volume) hdis (MeasurableSet.iUnion fun k => hBm (k + 1))
    rw [← hU, measure_iUnion (fun i j hij => hBdisj (by omega)) (fun k => hBm (k + 1))] at h1
    simp only [hBvol] at h1
    have hsum : ∑' k : ℕ, ((2 : ℝ≥0∞) ^ (k + 1 + 1))⁻¹ * V = 2⁻¹ * V := by
      rw [ENNReal.tsum_mul_right]
      congr 1
      have : ∀ k : ℕ, ((2 : ℝ≥0∞) ^ (k + 1 + 1))⁻¹ = 4⁻¹ * 2⁻¹ ^ k := by
        intro k
        rw [ENNReal.inv_pow, show k + 1 + 1 = 2 + k by ring, pow_add, ← ENNReal.inv_pow]
        norm_num
      simp only [this]
      rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric, ENNReal.one_sub_inv_two, inv_inv]
      rw [show (4 : ℝ≥0∞) = 2 * 2 by norm_num, ENNReal.mul_inv (Or.inl (by simp))
        (Or.inl (by simp)), mul_assoc, ENNReal.inv_mul_cancel (by simp) (by simp), mul_one]
    rw [hsum] at h1
    simp only [zero_add, pow_one]
    have hne : 2⁻¹ * V ≠ ⊤ := ENNReal.mul_ne_top (by simp) hVt
    have h2 : V = 2⁻¹ * V + 2⁻¹ * V := by
      rw [← add_mul, ENNReal.inv_two_add_inv_two, one_mul]
    change V = _ at h1
    conv_lhs at h1 => rw [h2]
    exact ((ENNReal.add_left_inj hne).1 h1).symm
  refine ⟨fun n => if n = 0 then A0 else B n, ?_, ?_, ?_, ?_⟩
  · intro n
    by_cases h : n = 0 <;> simp only [h, if_true, if_false]
    · exact hA0m
    · exact hBm n
  · intro i j hij
    by_cases hi : i = 0 <;> by_cases hj : j = 0 <;> simp only [hi, hj, if_true, if_false]
    · exact absurd (hi.trans hj.symm) hij
    · obtain ⟨j', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hj
      exact Set.disjoint_of_subset_right (Set.subset_iUnion (fun k => B (k + 1)) j')
        Set.disjoint_sdiff_left
    · obtain ⟨i', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hi
      exact (Set.disjoint_of_subset_right (Set.subset_iUnion (fun k => B (k + 1)) i')
        Set.disjoint_sdiff_left).symm
    · exact hBdisj hij
  · apply Set.Subset.antisymm
    · apply Set.iUnion_subset
      intro n
      by_cases h : n = 0 <;> simp only [h, if_true, if_false]
      · exact Set.sdiff_subset
      · exact hBY n
    · intro x hx
      by_cases hb : x ∈ ⋃ k, B (k + 1)
      · obtain ⟨k, hk⟩ := Set.mem_iUnion.1 hb
        exact Set.mem_iUnion.2 ⟨k + 1, by simp only [Nat.succ_ne_zero, if_false]; exact hk⟩
      · exact Set.mem_iUnion.2 ⟨0, by simp only [if_true]; exact ⟨hx, hb⟩⟩
  · intro n
    by_cases h : n = 0
    · subst h
      simp only [if_true]
      rw [hA0vol]
      exact ⟨ENNReal.mul_pos (by simp) hV0, le_rfl⟩
    · simp only [h, if_false]
      rw [hBvol]
      exact ⟨ENNReal.mul_pos (by simp) hV0, le_rfl⟩

end X6P22

open X6P22 in
theorem solution
    {X : Type u} [MeasurableSpace X]
    (mu : MeasureTheory.Measure X) [MeasureTheory.IsFiniteMeasure mu]
    (p q : ENNReal) (hp : 1 ≤ p) (hpq : p < q) (hq : q < ⊤) :
    letI : Fact (1 ≤ p) := ⟨hp⟩
    letI : Fact (1 ≤ q) := ⟨le_trans hp (le_of_lt hpq)⟩
    (∃ J : MeasureTheory.Lp ℂ q mu →L[ℂ] MeasureTheory.Lp ℂ p mu,
      Function.Injective J ∧
      ∀ f : MeasureTheory.Lp ℂ q mu, ∀ᵐ x ∂mu, J f x = f x) ∧
    ((∃ A : ℕ → Set X,
      (∀ n, MeasurableSet (A n)) ∧
      (Pairwise (fun n m => Disjoint (A n) (A m))) ∧
      (⋃ n, A n) = Set.univ ∧
      ∀ n, 0 < mu (A n) ∧
        mu (A n) ≤ ((2 : ENNReal) ^ (n + 1))⁻¹ * mu Set.univ) →
      ∃ f : X → ℂ, MeasureTheory.MemLp f p mu ∧ ¬ MeasureTheory.MemLp f q mu) ∧
    (∀ Y : Set ℝ, MeasurableSet Y → Y ⊆ Set.Icc 0 1 →
      0 < MeasureTheory.volume Y →
      ∃ A : ℕ → Set ℝ,
        (∀ n, MeasurableSet (A n)) ∧
        (Pairwise (fun n m => Disjoint (A n) (A m))) ∧
        (⋃ n, A n) = Y ∧
        ∀ n, 0 < MeasureTheory.volume (A n) ∧
          MeasureTheory.volume (A n) ≤
            ((2 : ENNReal) ^ (n + 1))⁻¹ * MeasureTheory.volume Y) :=
  ⟨part1 mu p q hp hpq hq, part2 mu p q hp hpq hq, fun Y hY hsub hpos => part3 Y hY hsub hpos⟩
