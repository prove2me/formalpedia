-- Prove2me | solution 1 for WassDDRO.Consistency.theorem_3_5
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-07T12:19:09.727638+00:00
-- url     : https://prove2.me/submissions/d0237015-c0ce-4d22-860e-b7342bc66c37

import Definitions.Def_WassDDRO_Consistency_Setting
import Mathlib
set_option autoImplicit false
section
set_option autoImplicit false
namespace WassConsistencyCodex
open WassDDRO.Consistency

theorem rpow_nonneg_small_exponent (x y : ℝ) (hy : 0 ≤ y) (hy' : y ≤ 1/2) :
    0 ≤ x ^ y := by
  by_cases hx : 0 ≤ x
  · exact Real.rpow_nonneg hx y
  · rw [Real.rpow_def_of_neg (lt_of_not_ge hx)]
    apply mul_nonneg (Real.exp_pos _).le
    apply Real.cos_nonneg_of_neg_pi_div_two_le_of_le
    · nlinarith [Real.pi_pos,mul_nonneg hy Real.pi_pos.le]
    · nlinarith [Real.pi_pos,mul_nonneg (sub_nonneg.mpr hy') Real.pi_pos.le]

theorem radius_nonnegative (c₁ c₂ a : ℝ) (m N : ℕ) (b : ℝ)
    (hc₂ : 0 < c₂) (hN : 1 ≤ N) : 0 ≤ radius c₁ c₂ a m N b := by
  have hn : 0 < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hm : (2 : ℝ) ≤ (max m 2 : ℝ) := by exact_mod_cast (le_max_right m 2)
  unfold radius
  split_ifs with hh
  · apply rpow_nonneg_small_exponent
    · positivity
    · apply (div_le_iff₀ (by linarith : 0 < (max m 2 : ℝ))).mpr
      linarith
  · apply Real.rpow_nonneg
    have hl : 0 < Real.log (c₁/b) := by
      have hg : (N : ℝ) < Real.log (c₁/b)/c₂ := lt_of_not_ge hh
      have := (lt_div_iff₀ hc₂).mp hg
      nlinarith
    positivity
end WassConsistencyCodex

end

section
set_option autoImplicit false
namespace WassConsistencyCodex
open WassDDRO.Consistency

theorem radius_positive_calibrated (c₁ c₂ a : ℝ) (m N : ℕ) (b : ℝ)
    (hc₁ : 0 < c₁) (hc₂ : 0 < c₂) (ha : 0 < a) (hN : 1 ≤ N)
    (hb : 0 < b) (hbc : b < c₁) :
    0 < radius c₁ c₂ a m N b ∧
    (if radius c₁ c₂ a m N b ≤ 1 then
      c₁ * Real.exp (-c₂*N*(radius c₁ c₂ a m N b) ^ (max m 2 : ℝ))
    else c₁ * Real.exp (-c₂*N*(radius c₁ c₂ a m N b) ^ a)) = b := by
  have hn : 0 < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hm : 0 < (max m 2 : ℝ) := by
    have : (2 : ℝ) ≤ (max m 2 : ℝ) := by exact_mod_cast le_max_right m 2
    linarith
  have hcdiv : 0 < c₁/b := div_pos hc₁ hb
  have hlog : 0 < Real.log (c₁/b) := Real.log_pos ((lt_div_iff₀ hb).mpr (by simpa using hbc))
  let q := Real.log (c₁/b)/(c₂*N)
  have hq : 0 < q := div_pos hlog (mul_pos hc₂ hn)
  have hpow (t : ℝ) (ht : 0 < t) : (q ^ (1/t)) ^ t = q := by
    rw [← Real.rpow_mul hq.le,one_div_mul_cancel ht.ne',Real.rpow_one]
  have hcal : c₁*Real.exp (-c₂*N*q) = b := by
    have hid : -c₂*N*q = -Real.log (c₁/b) := by dsimp [q]; field_simp
    rw [hid,Real.exp_neg,Real.exp_log hcdiv]
    field_simp
  by_cases hbranch : Real.log (c₁/b)/c₂ ≤ (N : ℝ)
  · simp only [radius,if_pos hbranch]
    have hqle : q ≤ 1 := by
      apply (div_le_iff₀ (mul_pos hc₂ hn)).mpr
      have hl := (div_le_iff₀ hc₂).mp hbranch
      simpa [mul_comm] using hl
    have hrle : q ^ (1/(max m 2 : ℝ)) ≤ 1 := Real.rpow_le_one hq.le hqle (by positivity)
    refine ⟨Real.rpow_pos_of_pos hq _,?_⟩
    change (if q ^ (1/(max m 2 : ℝ)) ≤ 1 then _ else _) = b
    rw [if_pos hrle,hpow _ hm]
    exact hcal
  · simp only [radius,if_neg hbranch]
    have hql : 1 < q := by
      apply (lt_div_iff₀ (mul_pos hc₂ hn)).mpr
      have hl := (lt_div_iff₀ hc₂).mp (lt_of_not_ge hbranch)
      simpa [mul_comm] using hl
    have hrl : 1 < q ^ (1/a) := Real.one_lt_rpow hql (by positivity)
    refine ⟨Real.rpow_pos_of_pos hq _,?_⟩
    change (if q ^ (1/a) ≤ 1 then _ else _) = b
    rw [if_neg (not_le.mpr hrl),hpow _ ha]
    exact hcal
end WassConsistencyCodex

end

section
set_option autoImplicit false
open MeasureTheory
namespace WassConsistencyCodex

theorem measure_positive_le_of_uniform_tail {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (d : Ω → ENNReal) (C : ENNReal)
    (ht : ∀ ε : ℝ, 0 < ε → μ {ω | ENNReal.ofReal ε ≤ d ω} ≤ C) :
    μ {ω | 0 < d ω} ≤ C := by
  let s : ℕ → Set Ω := fun n => {ω | ENNReal.ofReal (1/(n+1 : ℝ)) ≤ d ω}
  have hs : Monotone s := by
    intro n m hnm ω hn
    change ENNReal.ofReal (1/(m+1 : ℝ)) ≤ d ω
    change ENNReal.ofReal (1/(n+1 : ℝ)) ≤ d ω at hn
    apply le_trans _ hn
    apply ENNReal.ofReal_le_ofReal
    apply one_div_le_one_div_of_le
    · positivity
    · exact_mod_cast Nat.add_le_add_right hnm 1
  have heq : {ω | 0 < d ω} = ⋃ n, s n := by
    ext ω
    constructor
    · intro hω
      obtain ⟨r,hr,hrd⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hω
      have hr' : 0 < (r : ℝ) := by exact_mod_cast hr
      obtain ⟨n,hn⟩ := exists_nat_one_div_lt hr'
      apply Set.mem_iUnion.mpr
      refine ⟨n,?_⟩
      change ENNReal.ofReal (1/(n+1 : ℝ)) ≤ d ω
      have hc : ENNReal.ofReal (r : ℝ) = (r : ENNReal) := ENNReal.ofReal_coe_nnreal
      exact (ENNReal.ofReal_le_ofReal hn.le).trans (hc ▸ hrd.le)
    · intro hω
      obtain ⟨n,hn⟩ := Set.mem_iUnion.mp hω
      have hp : 0 < ENNReal.ofReal (1/(n+1 : ℝ)) := ENNReal.ofReal_pos.mpr (by positivity)
      exact hp.trans_le hn
  rw [heq,hs.measure_iUnion]
  exact iSup_le (fun n => ht _ (by positivity))
end WassConsistencyCodex

end

section
set_option autoImplicit false
open MeasureTheory
namespace WassConsistencyCodex
open WassDDRO.Consistency WassersteinDRO.Duality

theorem concentration_tail_le_c1 {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] (P : Measure E) [IsProbabilityMeasure P]
    (a c₁ c₂ : ℝ) (hc₁ : 0 ≤ c₁) (hc₂ : 0 ≤ c₂) (h7 : Concentration7 P a c₁ c₂)
    (N : ℕ) (hN : 1 ≤ N) (ε : ℝ) (hε : 0 < ε) :
    (Measure.pi fun _ : Fin N => P)
      {ω | ENNReal.ofReal ε ≤ wassersteinDistance 1 P (empiricalDistribution ω)} ≤
      ENNReal.ofReal c₁ := by
  apply (h7 N hN ε hε).trans
  apply ENNReal.ofReal_le_ofReal
  split_ifs
  all_goals
    apply mul_le_of_le_one_right hc₁
    apply Real.exp_le_one_iff.mpr
    have hr : 0 ≤ ε ^ (max (Module.finrank ℝ E) 2 : ℝ) := Real.rpow_nonneg hε.le _
    have hra : 0 ≤ ε ^ a := Real.rpow_nonneg hε.le _
    have hn : 0 ≤ (N : ℝ) := Nat.cast_nonneg N
    nlinarith [mul_nonneg hc₂ hn,mul_nonneg (mul_nonneg hc₂ hn) hr,
      mul_nonneg (mul_nonneg hc₂ hn) hra]

theorem concentration_positive_tail_le_c1 {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] (P : Measure E) [IsProbabilityMeasure P]
    (a c₁ c₂ : ℝ) (hc₁ : 0 ≤ c₁) (hc₂ : 0 ≤ c₂) (h7 : Concentration7 P a c₁ c₂)
    (N : ℕ) (hN : 1 ≤ N) :
    (Measure.pi fun _ : Fin N => P)
      {ω | 0 < wassersteinDistance 1 P (empiricalDistribution ω)} ≤ ENNReal.ofReal c₁ := by
  apply measure_positive_le_of_uniform_tail
  exact fun ε hε => concentration_tail_le_c1 P a c₁ c₂ hc₁ hc₂ h7 N hN ε hε
end WassConsistencyCodex

end

section
set_option autoImplicit false
open MeasureTheory
namespace WassConsistencyCodex
open WassDDRO.Consistency WassersteinDRO.Duality

theorem concentration_radius_tail {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] (P : Measure E) [IsProbabilityMeasure P]
    (a c₁ c₂ : ℝ) (ha : 0 < a) (hc₁ : 0 < c₁) (hc₂ : 0 < c₂)
    (h7 : Concentration7 P a c₁ c₂) (N : ℕ) (hN : 1 ≤ N) (b : ℝ) (hb : 0 < b) :
    (Measure.pi fun _ : Fin N => P)
      {ω | ENNReal.ofReal (radius c₁ c₂ a (Module.finrank ℝ E) N b) <
        wassersteinDistance 1 P (empiricalDistribution ω)} ≤ ENNReal.ofReal b := by
  by_cases hbc : b < c₁
  · obtain ⟨hr,hcal⟩ := radius_positive_calibrated c₁ c₂ a (Module.finrank ℝ E) N b
      hc₁ hc₂ ha hN hb hbc
    have hs : {ω : Fin N → E | ENNReal.ofReal (radius c₁ c₂ a (Module.finrank ℝ E) N b) < wassersteinDistance 1 P (empiricalDistribution ω)} ⊆
        {ω | ENNReal.ofReal (radius c₁ c₂ a (Module.finrank ℝ E) N b) ≤ wassersteinDistance 1 P (empiricalDistribution ω)} := by
      intro ω hω
      change ENNReal.ofReal (radius c₁ c₂ a (Module.finrank ℝ E) N b) < wassersteinDistance 1 P (empiricalDistribution ω) at hω
      change ENNReal.ofReal (radius c₁ c₂ a (Module.finrank ℝ E) N b) ≤ wassersteinDistance 1 P (empiricalDistribution ω)
      exact le_of_lt hω
    apply (measure_mono hs).trans
    have ht := h7 N hN _ hr
    rw [hcal] at ht
    exact ht
  · have hs : {ω : Fin N → E | ENNReal.ofReal (radius c₁ c₂ a (Module.finrank ℝ E) N b) < wassersteinDistance 1 P (empiricalDistribution ω)} ⊆
        {ω | 0 < wassersteinDistance 1 P (empiricalDistribution ω)} := by
      intro ω hω
      change ENNReal.ofReal (radius c₁ c₂ a (Module.finrank ℝ E) N b) < wassersteinDistance 1 P (empiricalDistribution ω) at hω
      change 0 < wassersteinDistance 1 P (empiricalDistribution ω)
      exact lt_of_le_of_lt bot_le hω
    apply (measure_mono hs).trans
    exact (concentration_positive_tail_le_c1 P a c₁ c₂ hc₁.le hc₂.le h7 N hN).trans
      (ENNReal.ofReal_le_ofReal (le_of_not_gt hbc))
end WassConsistencyCodex

end

section
set_option autoImplicit false
open MeasureTheory
namespace WassConsistencyCodex

theorem wassersteinDistance_symm {E : Type*} [NormedAddCommGroup E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] (p : ℝ) (P Q : Measure E) :
    WassersteinDRO.Duality.wassersteinDistance p P Q =
      WassersteinDRO.Duality.wassersteinDistance p Q P := by
  have hcost (P Q : Measure E) :
      (⨅ (π : Measure (E × E)) (_ : π.map Prod.fst = P ∧ π.map Prod.snd = Q),
        ∫⁻ z : E × E, ENNReal.ofReal (‖z.1-z.2‖ ^ p) ∂π) ≤
      (⨅ (π : Measure (E × E)) (_ : π.map Prod.fst = Q ∧ π.map Prod.snd = P),
        ∫⁻ z : E × E, ENNReal.ofReal (‖z.1-z.2‖ ^ p) ∂π) := by
    apply le_iInf
    intro π
    apply le_iInf
    intro hπ
    apply iInf_le_of_le (π.map Prod.swap)
    have hm : (π.map Prod.swap).map Prod.fst = P ∧ (π.map Prod.swap).map Prod.snd = Q := by
      constructor
      · change (π.map Prod.swap).fst = P
        rw [Measure.fst_map_swap]
        exact hπ.2
      · change (π.map Prod.swap).snd = Q
        rw [Measure.snd_map_swap]
        exact hπ.1
    apply iInf_le_of_le hm
    have hf : Measurable (fun z : E × E => ENNReal.ofReal (‖z.1-z.2‖ ^ p)) :=
      (((measurable_fst.sub measurable_snd).norm.pow_const p).ennreal_ofReal)
    rw [lintegral_map hf measurable_swap]
    change (∫⁻ z : E × E, ENNReal.ofReal (‖z.2-z.1‖ ^ p) ∂π) ≤ _
    simp only [norm_sub_rev]
    exact le_rfl
  unfold WassersteinDRO.Duality.wassersteinDistance
  rw [le_antisymm (hcost P Q) (hcost Q P)]
end WassConsistencyCodex

end

section
set_option autoImplicit false
open MeasureTheory
namespace WassConsistencyCodex
open WassDDRO.Consistency WassersteinDRO.Duality

theorem nominalRisk_le_worstCase {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E]
    (P PN : Measure E) (Ξ : Set E) (ε : ℝ) (h : E → ℝ)
    (hball : P ∈ ambiguitySet ε 1 Ξ PN) (hint : Integrable h P) :
    ((∫ ξ, h ξ ∂P : ℝ) : EReal) ≤ worstCaseRisk ε 1 Ξ PN h := by
  unfold worstCaseRisk
  exact le_iSup_of_le P (le_iSup_of_le hball (le_iSup_of_le hint le_rfl))

theorem optimizer_guarantee {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E]
    {D : Type*} {N : ℕ} (P : Measure E) (Ξ : Set E) (ε : ℝ)
    (X : Set D) (h : D → E → ℝ) (ξhat : Fin N → E) (xh : D)
    (hball : P ∈ ambiguitySet ε 1 Ξ (empiricalDistribution ξhat))
    (hint : Integrable (h xh) P) (hopt : ∀ x ∈ X,
      worstCaseRisk ε 1 Ξ (empiricalDistribution ξhat) (h xh) ≤
        worstCaseRisk ε 1 Ξ (empiricalDistribution ξhat) (h x)) :
    ((∫ ξ, h xh ξ ∂P : ℝ) : EReal) ≤ droValue X h ε Ξ ξhat := by
  apply (nominalRisk_le_worstCase P _ Ξ ε (h xh) hball hint).trans
  exact le_iInf₂ hopt

theorem true_distribution_mem_ball {E : Type*} [NormedAddCommGroup E]
    [MeasurableSpace E] [BorelSpace E] (P PN : Measure E) [IsProbabilityMeasure P]
    (Ξ : Set E) (ε : ℝ) (hP : P Ξᶜ = 0)
    (hd : wassersteinDistance 1 P PN ≤ ENNReal.ofReal ε) :
    P ∈ ambiguitySet ε 1 Ξ PN := by
  exact ⟨measure_univ,hP,hd⟩
end WassConsistencyCodex

end

section
set_option autoImplicit false
open MeasureTheory Filter
namespace WassConsistencyCodex
open WassDDRO.Consistency WassersteinDRO.Duality

theorem samples_mem_support_ae {E : Type*} [MeasurableSpace E]
    (P : Measure E) [IsProbabilityMeasure P] (Ξ : Set E) (hP : P Ξᶜ = 0) (N : ℕ) :
    ∀ᵐ ω ∂(Measure.pi fun _ : Fin N => P), ∀ i, ω i ∈ Ξ := by
  have hs : ∀ᵐ x ∂P, x ∈ Ξ := by exact mem_ae_iff.mpr hP
  exact eventually_all.mpr (fun i => Measure.tendsto_eval_ae_ae.eventually hs)

theorem failure_measure_le_distance_tail {E : Type*} [NormedAddCommGroup E]
    [MeasurableSpace E] [BorelSpace E] {D : Type*} {N : ℕ}
    (P : Measure E) [IsProbabilityMeasure P] (Ξ : Set E) (hP : P Ξᶜ = 0)
    (ε : ℝ) (X : Set D) (h : D → E → ℝ) (hint : ∀ x ∈ X, Integrable (h x) P)
    (xh : (Fin N → E) → D)
    (hopt : ∀ ξhat, (∀ i, ξhat i ∈ Ξ) → xh ξhat ∈ X ∧ ∀ x ∈ X,
      worstCaseRisk ε 1 Ξ (empiricalDistribution ξhat) (h (xh ξhat)) ≤
        worstCaseRisk ε 1 Ξ (empiricalDistribution ξhat) (h x)) :
    (Measure.pi fun _ : Fin N => P)
      {ξhat | ¬ (((∫ ξ, h (xh ξhat) ξ ∂P : ℝ) : EReal) ≤ droValue X h ε Ξ ξhat)} ≤
    (Measure.pi fun _ : Fin N => P)
      {ξhat | ENNReal.ofReal ε < wassersteinDistance 1 P (empiricalDistribution ξhat)} := by
  apply measure_mono_ae
  filter_upwards [samples_mem_support_ae P Ξ hP N] with ξhat hξ
  intro hbad
  by_contra hnot
  have hd : wassersteinDistance 1 P (empiricalDistribution ξhat) ≤ ENNReal.ofReal ε :=
    le_of_not_gt hnot
  obtain ⟨hx,ho⟩ := hopt ξhat hξ
  exact hbad (optimizer_guarantee P Ξ ε X h ξhat (xh ξhat)
    (true_distribution_mem_ball P _ Ξ ε hP hd) (hint _ hx) ho)
end WassConsistencyCodex

end

set_option autoImplicit false
open MeasureTheory WassDDRO.Consistency
theorem solution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    (P : Measure E) [IsProbabilityMeasure P] (Ξ : Set E) (hP : P Ξᶜ = 0)
    (a : ℝ) (ha : 1 < a) (hA : Integrable (fun ξ => Real.exp (‖ξ‖ ^ a)) P)
    (hm : Module.finrank ℝ E ≠ 2)
    (c₁ c₂ : ℝ) (hc₁ : 0 < c₁) (hc₂ : 0 < c₂) (h7 : Concentration7 P a c₁ c₂)
    (N : ℕ) (hN : 1 ≤ N) (b : ℝ) (hb : 0 < b ∧ b < 1)
    {n : ℕ} (X : Set (EuclideanSpace ℝ (Fin n))) (h : EuclideanSpace ℝ (Fin n) → E → ℝ)
    (hmeas : ∀ x, Measurable (h x)) (hint : ∀ x ∈ X, Integrable (h x) P)
    (xh : (Fin N → E) → EuclideanSpace ℝ (Fin n))
    (hopt : ∀ ξhat : Fin N → E, (∀ i, ξhat i ∈ Ξ) →
      xh ξhat ∈ X ∧ ∀ x ∈ X,
        WassersteinDRO.Duality.worstCaseRisk (radius c₁ c₂ a (Module.finrank ℝ E) N b) 1 Ξ
            (WassersteinDRO.Duality.empiricalDistribution ξhat) (h (xh ξhat)) ≤
          WassersteinDRO.Duality.worstCaseRisk (radius c₁ c₂ a (Module.finrank ℝ E) N b) 1 Ξ
            (WassersteinDRO.Duality.empiricalDistribution ξhat) (h x)) :
    (Measure.pi fun _ : Fin N => P)
        {ξhat | ¬ (((∫ ξ, h (xh ξhat) ξ ∂P : ℝ) : EReal) ≤
          droValue X h (radius c₁ c₂ a (Module.finrank ℝ E) N b) Ξ ξhat)} ≤
      ENNReal.ofReal b := by
  apply (WassConsistencyCodex.failure_measure_le_distance_tail P Ξ hP
    (radius c₁ c₂ a (Module.finrank ℝ E) N b) X h hint xh hopt).trans
  exact WassConsistencyCodex.concentration_radius_tail P a c₁ c₂ (by linarith) hc₁ hc₂
    h7 N hN b hb.1


#print axioms solution
