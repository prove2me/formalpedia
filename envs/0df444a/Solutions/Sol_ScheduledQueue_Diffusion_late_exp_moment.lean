-- Prove2me | solution 1 for ScheduledQueue.Diffusion.late_exp_moment
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-24T17:56:00.342627+00:00
-- url     : https://prove2.me/submissions/7f6130c5-1a5d-4bc3-8e05-5ece8d63a941

import Mathlib
import Definitions.Def_ScheduledQueue_Diffusion_Setting

open Set Filter Topology MeasureTheory ProbabilityTheory

lemma SQE_tsum_le {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Y : Ω → ℝ) (hY : Integrable Y P) (hYm : Measurable Y) (hY0 : ∀ ω, 0 ≤ Y ω) :
    ∑' k : ℕ, P {ω | (k : ℝ) ≤ Y ω} ≤ ENNReal.ofReal (∫ ω, Y ω ∂P + 1) := by
  have hms : ∀ k : ℕ, MeasurableSet {ω | (k : ℝ) ≤ Y ω} :=
    fun k => measurableSet_le measurable_const hYm
  have hpt : ∀ ω, ∑' k : ℕ, ({ω | (k : ℝ) ≤ Y ω}.indicator (1 : Ω → ENNReal) ω)
      ≤ ENNReal.ofReal (Y ω + 1) := by
    intro ω
    rw [tsum_eq_sum (s := Finset.range (⌊Y ω⌋₊ + 1))]
    · calc ∑ k ∈ Finset.range (⌊Y ω⌋₊ + 1), ({ω | (k : ℝ) ≤ Y ω}.indicator (1 : Ω → ENNReal) ω)
          ≤ ∑ k ∈ Finset.range (⌊Y ω⌋₊ + 1), (1 : ENNReal) := by
            refine Finset.sum_le_sum (fun k _ => ?_)
            simp only [Set.indicator, mem_setOf_eq, Pi.one_apply]
            split_ifs <;> simp
        _ = ((⌊Y ω⌋₊ + 1 : ℕ) : ENNReal) := by simp
        _ ≤ ENNReal.ofReal (Y ω + 1) := by
            rw [← ENNReal.ofReal_natCast]
            apply ENNReal.ofReal_le_ofReal
            push_cast
            linarith [Nat.floor_le (hY0 ω)]
    · intro k hk
      simp only [Finset.mem_range, not_lt] at hk
      have : Y ω < (k : ℝ) := by
        have h1 := Nat.lt_floor_add_one (Y ω)
        have h2 : ((⌊Y ω⌋₊ + 1 : ℕ) : ℝ) ≤ k := by exact_mod_cast hk
        push_cast at h2; linarith
      simp [Set.indicator, not_le.mpr this]
  calc ∑' k : ℕ, P {ω | (k : ℝ) ≤ Y ω}
      = ∑' k : ℕ, ∫⁻ ω, ({ω | (k : ℝ) ≤ Y ω}.indicator (1 : Ω → ENNReal) ω) ∂P := by
        congr 1; funext k; rw [lintegral_indicator_one (hms k)]
    _ = ∫⁻ ω, ∑' k : ℕ, ({ω | (k : ℝ) ≤ Y ω}.indicator (1 : Ω → ENNReal) ω) ∂P := by
        rw [lintegral_tsum]
        intro k
        exact (measurable_const.indicator (hms k)).aemeasurable
    _ ≤ ∫⁻ ω, ENNReal.ofReal (Y ω + 1) ∂P := lintegral_mono hpt
    _ = ENNReal.ofReal (∫ ω, (Y ω + 1) ∂P) := by
        have hI : Integrable (fun ω => Y ω + 1) P := hY.add (integrable_const 1)
        rw [ofReal_integral_eq_lintegral_ofReal hI
          (Eventually.of_forall (fun ω => by have := hY0 ω; simp only [Pi.zero_apply]; linarith))]
    _ = ENNReal.ofReal (∫ ω, Y ω ∂P + 1) := by
        rw [integral_add hY (integrable_const 1)]; simp

lemma SQE_core {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : ℝ) (hh : 0 < h) (Z : ℕ → Ω → ℝ) (hZm : ∀ k, Measurable (Z k))
    (hind : iIndepFun Z P) (hid : ∀ k, IdentDistrib (Z k) (Z 0) P P) (hint : Integrable (Z 0) P)
    (N : Ω → ℕ∞) (hN : ∀ᵐ ω ∂P, N ω ≤ {k : ℕ | (k : ℝ) * h ≤ Z k ω}.encard)
    (θ : ℝ) (hθ : 0 < θ) :
    (∀ᵐ ω ∂P, N ω ≠ ⊤) ∧
    ∫⁻ ω, ENNReal.ofReal (Real.exp (θ * ((N ω).toNat : ℝ))) ∂P ≤
      ENNReal.ofReal (Real.exp ((Real.exp θ - 1) * ((∫ ω, max (Z 0 ω) 0 ∂P) / h + 1))) := by
  classical
  set Y : Ω → ℝ := fun ω => max (Z 0 ω) 0 / h with hYdef
  have hYm : Measurable Y := ((hZm 0).max measurable_const).div_const h
  have hYi : Integrable Y P := (hint.sup (integrable_const 0)).div_const h
  have hY0 : ∀ ω, 0 ≤ Y ω := fun ω => div_nonneg (le_max_right _ _) hh.le
  have hEY : ∫ ω, Y ω ∂P = (∫ ω, max (Z 0 ω) 0 ∂P) / h := by
    simp only [hYdef]; rw [integral_div]
  have hms : ∀ k : ℕ, MeasurableSet {ω | (k : ℝ) * h ≤ Z k ω} :=
    fun k => measurableSet_le measurable_const (hZm k)
  -- termwise bound
  have hterm : ∀ k : ℕ, P {ω | (k : ℝ) * h ≤ Z k ω} ≤ P {ω | (k : ℝ) ≤ Y ω} := by
    intro k
    have e : P {ω | (k : ℝ) * h ≤ Z k ω} = P {ω | (k : ℝ) * h ≤ Z 0 ω} := by
      have := (hid k).measure_mem_eq (s := Ici ((k : ℝ) * h)) measurableSet_Ici
      exact this
    rw [e]
    refine measure_mono (fun ω hω => ?_)
    simp only [mem_setOf_eq, hYdef] at hω ⊢
    rw [le_div_iff₀ hh]
    exact le_trans hω (le_max_left _ _)
  have hsum : ∑' k : ℕ, P {ω | (k : ℝ) * h ≤ Z k ω} ≤
      ENNReal.ofReal ((∫ ω, max (Z 0 ω) 0 ∂P) / h + 1) := by
    rw [← hEY]
    exact (ENNReal.tsum_le_tsum hterm).trans (SQE_tsum_le P Y hYi hYm hY0)
  have hfin : ∀ᵐ ω ∂P, {k : ℕ | (k : ℝ) * h ≤ Z k ω}.Finite :=
    ae_finite_setOfPred_mem (s := fun k : ℕ => {ω | (k : ℝ) * h ≤ Z k ω})
      (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hsum)
  -- the indicator variables
  set X : ℕ → Ω → ℝ := fun k ω => if (k : ℝ) * h ≤ Z k ω then 1 else 0 with hXdef
  have hXm : ∀ k, Measurable (X k) := fun k =>
    Measurable.ite (hms k) measurable_const measurable_const
  have hXind : iIndepFun X P := by
    have := hind.comp (fun k (x : ℝ) => if (k : ℝ) * h ≤ x then (1 : ℝ) else 0)
      (fun k => Measurable.ite (measurableSet_le measurable_const measurable_id)
        measurable_const measurable_const)
    exact this
  have hX01 : ∀ k ω, 0 ≤ X k ω ∧ X k ω ≤ 1 := by
    intro k ω; simp only [hXdef]; split_ifs <;> norm_num
  set c : ℝ := Real.exp θ - 1 with hc
  have hc0 : 0 < c := by rw [hc, sub_pos]; exact Real.one_lt_exp_iff.mpr hθ
  have hmgf1 : ∀ k, mgf (X k) P θ ≤ Real.exp (P.real {ω | (k : ℝ) * h ≤ Z k ω} * c) := by
    intro k
    have hpt : (fun ω => Real.exp (θ * X k ω)) =
        fun ω => 1 + c * ({ω | (k : ℝ) * h ≤ Z k ω}.indicator 1 ω) := by
      funext ω
      simp only [hXdef, Set.indicator, mem_setOf_eq, Pi.one_apply, hc]
      split_ifs <;> simp
    have hval : mgf (X k) P θ = 1 + c * P.real {ω | (k : ℝ) * h ≤ Z k ω} := by
      rw [mgf, hpt, integral_add (integrable_const 1), integral_const_mul,
        integral_indicator_one (hms k)]
      · simp
      · exact ((integrable_const (1:ℝ)).indicator (hms k)).const_mul c
    rw [hval]
    have := Real.add_one_le_exp (P.real {ω | (k : ℝ) * h ≤ Z k ω} * c)
    linarith
  have hpsum : ∀ n : ℕ, ∑ k ∈ Finset.range n, P.real {ω | (k : ℝ) * h ≤ Z k ω} ≤
      (∫ ω, max (Z 0 ω) 0 ∂P) / h + 1 := by
    intro n
    have hnn : 0 ≤ (∫ ω, max (Z 0 ω) 0 ∂P) / h + 1 := by
      have : 0 ≤ ∫ ω, max (Z 0 ω) 0 ∂P := integral_nonneg (fun ω => le_max_right _ _)
      positivity
    simp only [measureReal_def]
    rw [← ENNReal.toReal_sum (fun k _ => measure_ne_top P _)]
    apply ENNReal.toReal_le_of_le_ofReal hnn
    exact (ENNReal.sum_le_tsum _).trans hsum
  set S : ℕ → Ω → ℝ := fun n ω => ∑ k ∈ Finset.range n, X k ω with hSdef
  have hSm : ∀ n, Measurable (S n) := fun n =>
    Finset.measurable_sum _ (fun k _ => hXm k)
  have hS0 : ∀ n ω, 0 ≤ S n ω := fun n ω =>
    Finset.sum_nonneg (fun k _ => (hX01 k ω).1)
  have hSle : ∀ n ω, S n ω ≤ n := by
    intro n ω
    calc S n ω ≤ ∑ k ∈ Finset.range n, (1 : ℝ) := Finset.sum_le_sum (fun k _ => (hX01 k ω).2)
      _ = n := by simp
  have hmgfS : ∀ n, mgf (S n) P θ ≤ Real.exp (c * ((∫ ω, max (Z 0 ω) 0 ∂P) / h + 1)) := by
    intro n
    have e : S n = ∑ k ∈ Finset.range n, X k := by
      funext ω; simp [hSdef, Finset.sum_apply]
    rw [e, hXind.mgf_sum hXm]
    calc ∏ k ∈ Finset.range n, mgf (X k) P θ
        ≤ ∏ k ∈ Finset.range n, Real.exp (P.real {ω | (k : ℝ) * h ≤ Z k ω} * c) :=
          Finset.prod_le_prod (fun k _ => mgf_nonneg) (fun k _ => hmgf1 k)
      _ = Real.exp ((∑ k ∈ Finset.range n, P.real {ω | (k : ℝ) * h ≤ Z k ω}) * c) := by
          rw [← Real.exp_sum, Finset.sum_mul]
      _ ≤ Real.exp (c * ((∫ ω, max (Z 0 ω) 0 ∂P) / h + 1)) := by
          apply Real.exp_le_exp.mpr
          rw [mul_comm]
          exact mul_le_mul_of_nonneg_left (hpsum n) hc0.le
  -- pointwise domination
  have hdom : ∀ᵐ ω ∂P, N ω ≠ ⊤ ∧ ENNReal.ofReal (Real.exp (θ * ((N ω).toNat : ℝ))) ≤
      ⨆ n : ℕ, ENNReal.ofReal (Real.exp (θ * S n ω)) := by
    filter_upwards [hN, hfin] with ω hNω hfω
    set F := {k : ℕ | (k : ℝ) * h ≤ Z k ω} with hF
    have hNt : N ω ≠ ⊤ := ne_top_of_le_ne_top (hfω.encard_lt_top.ne) hNω
    refine ⟨hNt, ?_⟩
    obtain ⟨M, hM⟩ := hfω.bddAbove
    have hFeq : F = ↑((Finset.range (M + 1)).filter (fun k : ℕ => (k : ℝ) * h ≤ Z k ω)) := by
      ext k
      simp only [hF, mem_setOf_eq, Finset.coe_filter, Finset.mem_range]
      constructor
      · intro hk; exact ⟨Nat.lt_succ_of_le (hM hk), hk⟩
      · intro hk; exact hk.2
    have hSF : S (M + 1) ω = (F.ncard : ℝ) := by
      rw [hFeq, Set.ncard_coe_finset]
      simp [hSdef, hXdef, Finset.sum_boole]
    have hNle : ((N ω).toNat : ℝ) ≤ (F.ncard : ℝ) := by
      have h1 : N ω ≤ (F.ncard : ℕ∞) := by
        rw [hfω.cast_ncard_eq]; exact hNω
      have h2 : (N ω).toNat ≤ F.ncard := by
        have := ENat.toNat_le_toNat h1 (ENat.natCast_ne_top _)
        simpa using this
      exact_mod_cast h2
    refine le_iSup_of_le (M + 1) ?_
    apply ENNReal.ofReal_le_ofReal
    apply Real.exp_le_exp.mpr
    rw [hSF]
    exact mul_le_mul_of_nonneg_left hNle hθ.le
  refine ⟨hdom.mono (fun ω hω => hω.1), ?_⟩
  have hmono : Monotone (fun n : ℕ => fun ω => ENNReal.ofReal (Real.exp (θ * S n ω))) := by
    intro n m hnm ω
    apply ENNReal.ofReal_le_ofReal
    apply Real.exp_le_exp.mpr
    apply mul_le_mul_of_nonneg_left _ hθ.le
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hnm)
      (fun k _ _ => (hX01 k ω).1)
  calc ∫⁻ ω, ENNReal.ofReal (Real.exp (θ * ((N ω).toNat : ℝ))) ∂P
      ≤ ∫⁻ ω, ⨆ n : ℕ, ENNReal.ofReal (Real.exp (θ * S n ω)) ∂P :=
        lintegral_mono_ae (hdom.mono (fun ω hω => hω.2))
    _ = ⨆ n : ℕ, ∫⁻ ω, ENNReal.ofReal (Real.exp (θ * S n ω)) ∂P := by
        exact lintegral_iSup (f := fun n ω => ENNReal.ofReal (Real.exp (θ * S n ω)))
          (fun n => (Real.measurable_exp.comp ((hSm n).const_mul θ)).ennreal_ofReal) hmono
    _ ≤ ENNReal.ofReal (Real.exp (c * ((∫ ω, max (Z 0 ω) 0 ∂P) / h + 1))) := by
        refine iSup_le (fun n => ?_)
        have hint' : Integrable (fun ω => Real.exp (θ * S n ω)) P := by
          refine Integrable.of_bound (Real.measurable_exp.comp
            ((hSm n).const_mul θ)).aestronglyMeasurable (Real.exp (θ * n)) ?_
          filter_upwards with ω
          rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
          exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (hSle n ω) hθ.le)
        rw [← ofReal_integral_eq_lintegral_ofReal hint'
          (Eventually.of_forall (fun ω => (Real.exp_pos _).le))]
        exact ENNReal.ofReal_le_ofReal (hmgfS n)

open ScheduledQueue.Diffusion in
theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : ℝ) (hh : 0 < h) (ξ : ℤ → Ω → ℝ) (U : Ω → ℝ) (hin : ScheduledQueue.Stability.ScheduledInput P ξ U) :
    ∀ θ : ℝ, 0 < θ →
      (∀ᵐ ω ∂P, late h ξ U 0 ω ≠ ⊤) ∧
      ∫⁻ ω, ENNReal.ofReal (Real.exp (θ * ((late h ξ U 0 ω).toNat : ℝ))) ∂P ≤
        ENNReal.ofReal (Real.exp ((Real.exp θ - 1) * ((∫ ω, max (ξ 0 ω) 0 ∂P) / h + 1))) := by
  intro θ hθ
  have hU : ∀ᵐ ω ∂P, U ω ∈ Icc (0:ℝ) 1 := by
    rw [ae_iff]
    rw [hin.uniform.measure_eq (p := fun v => v ∉ Icc (0:ℝ) 1) measurableSet_Icc.compl]
    show (volume.restrict (Icc (0:ℝ) 1)) (Icc (0:ℝ) 1)ᶜ = 0
    rw [Measure.restrict_apply measurableSet_Icc.compl]
    simp
  set g : ℕ → ℤ := fun k => -((k : ℤ) + 1) with hg
  have hginj : Function.Injective g := by
    intro a b hab; simp only [hg] at hab; omega
  set Z : ℕ → Ω → ℝ := fun k ω => ξ (g k) ω with hZ
  have hZm : ∀ k, Measurable (Z k) := fun k => hin.measurable _
  have hind : iIndepFun Z P := hin.indep.precomp hginj
  have hid' : ∀ k, IdentDistrib (Z k) (ξ 0) P P := fun k => hin.identDistrib (g k)
  have hid : ∀ k, IdentDistrib (Z k) (Z 0) P P := fun k => (hid' k).trans (hid' 0).symm
  have hint : Integrable (Z 0) P := (hid' 0).integrable_iff.mpr hin.integrable
  have hmaxeq : ∫ ω, max (Z 0 ω) 0 ∂P = ∫ ω, max (ξ 0 ω) 0 ∂P := by
    have := ((hid' 0).comp (measurable_id.max (measurable_const (a := (0:ℝ))))).integral_eq
    simpa [Function.comp_def] using this
  have hN : ∀ᵐ ω ∂P, late h ξ U 0 ω ≤ {k : ℕ | (k : ℝ) * h ≤ Z k ω}.encard := by
    filter_upwards [hU] with ω hu
    have hsub : {i : ℤ | i * h + U ω * h < 0 ∧ (0:ℝ) ≤ i * h + U ω * h + ξ i ω} ⊆
        g '' {k : ℕ | (k : ℝ) * h ≤ Z k ω} := by
      intro i hi
      simp only [mem_setOf_eq] at hi
      have hi0 : i < 0 := by
        by_contra hc
        have : (0 : ℝ) ≤ i := by exact_mod_cast (not_lt.mp hc)
        nlinarith [hu.1, hu.2]
      have hk : g ((-i - 1).toNat) = i := by
        simp only [hg]; omega
      refine ⟨(-i - 1).toNat, ?_, hk⟩
      simp only [mem_setOf_eq, hZ, hk]
      have : (((-i - 1).toNat : ℕ) : ℝ) = -(i : ℝ) - 1 := by
        have e : (((-i - 1).toNat : ℕ) : ℤ) = -i - 1 := Int.toNat_of_nonneg (by omega)
        have : ((((-i - 1).toNat : ℕ) : ℤ) : ℝ) = ((-i - 1 : ℤ) : ℝ) := by rw [e]
        push_cast at this; exact this
      rw [this]
      nlinarith [hu.2]
    calc late h ξ U 0 ω
        = {i : ℤ | i * h + U ω * h < 0 ∧ (0:ℝ) ≤ i * h + U ω * h + ξ i ω}.encard := rfl
      _ ≤ (g '' {k : ℕ | (k : ℝ) * h ≤ Z k ω}).encard := Set.encard_le_encard hsub
      _ = {k : ℕ | (k : ℝ) * h ≤ Z k ω}.encard := hginj.encard_image _
  have := SQE_core P h hh Z hZm hind hid hint (late h ξ U 0) hN θ hθ
  rw [hmaxeq] at this
  exact this
