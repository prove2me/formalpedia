-- Prove2me | solution 1 for RegretBandits.Stochastic.alpha_psi_ucb_pseudo_regret
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-17T23:18:31.352335+00:00
-- url     : https://prove2.me/submissions/3409f6e2-3386-427c-a32b-27f444cd4c71

import Mathlib
import Definitions.Def_ImprovedLinBandits_UCBDelta_armModel
import Definitions.Def_RegretBandits_Stochastic_model
import Definitions.Def_RegretBandits_Stochastic_alphaPsiUCB

set_option autoImplicit false

open ImprovedLinBandits.UCBDelta in
theorem pullCount_eq_sum_cb7 {Ω : Type*} {K : ℕ} (I : ℕ → Ω → Fin K) (i : Fin K) (t : ℕ)
    (ω : Ω) :
    pullCount I i t ω = ∑ s ∈ Finset.range t, if I (s + 1) ω = i then 1 else 0 := by
  unfold pullCount; rw [Finset.card_filter]

open MeasureTheory ProbabilityTheory in
/-- Chernoff bound for a sum of iid real variables at a fixed `l ≥ 0`. -/
theorem chernoff_sum_cb7 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (Z : ℕ → Ω → ℝ) (hZm : ∀ k, Measurable (Z k))
    (hind : iIndepFun Z P) (hid : ∀ k, IdentDistrib (Z k) (Z 0) P P) (ψ : ℝ → ℝ)
    (l : ℝ) (hl : 0 ≤ l) (hint : Integrable (fun ω => Real.exp (l * Z 0 ω)) P)
    (hlog : Real.log (∫ ω, Real.exp (l * Z 0 ω) ∂P) ≤ ψ l) (s : ℕ) (ε : ℝ) :
    P.real {ω | (s : ℝ) * ε ≤ ∑ k ∈ Finset.range s, Z k ω} ≤
      Real.exp (-(s : ℝ) * (l * ε - ψ l)) := by
  have hu : Measurable (fun x : ℝ => Real.exp (l * x)) := by fun_prop
  have hintk : ∀ k, Integrable (fun ω => Real.exp (l * Z k ω)) P := by
    intro k
    exact ((hid k).comp hu).integrable_iff.mpr hint
  have hmgfk : ∀ k, mgf (Z k) P l = mgf (Z 0) P l := by
    intro k
    exact ((hid k).comp hu).integral_eq
  have hm0 : mgf (Z 0) P l ≤ Real.exp (ψ l) := by
    have hpos : 0 < mgf (Z 0) P l := mgf_pos hint
    rw [← Real.log_le_iff_le_exp hpos]
    exact hlog
  have hsum : mgf (∑ k ∈ Finset.range s, Z k) P l = mgf (Z 0) P l ^ s := by
    rw [hind.mgf_sum hZm, Finset.prod_congr rfl (fun k _ => hmgfk k), Finset.prod_const,
      Finset.card_range]
  have hint_s := hind.integrable_exp_mul_sum (t := l) hZm (s := Finset.range s)
    (fun k _ => hintk k)
  have hmk := measure_ge_le_exp_mul_mgf (X := ∑ k ∈ Finset.range s, Z k) (μ := P)
    ((s : ℝ) * ε) hl hint_s
  have hset : {ω | (s : ℝ) * ε ≤ ∑ k ∈ Finset.range s, Z k ω} =
      {ω | (s : ℝ) * ε ≤ (∑ k ∈ Finset.range s, Z k) ω} := by
    ext ω; simp [Finset.sum_apply]
  rw [hset]
  refine hmk.trans ?_
  rw [hsum]
  have h0 : 0 ≤ mgf (Z 0) P l := mgf_nonneg
  calc Real.exp (-l * ((s : ℝ) * ε)) * mgf (Z 0) P l ^ s
      ≤ Real.exp (-l * ((s : ℝ) * ε)) * Real.exp (ψ l) ^ s := by gcongr
    _ = Real.exp (-(s : ℝ) * (l * ε - ψ l)) := by
      rw [← Real.exp_nat_mul, ← Real.exp_add]; congr 1; ring

open RegretBandits.Stochastic in
theorem lf_coe_le_cb7 (ψ : ℝ → ℝ) (ε l : ℝ) :
    ((l * ε - ψ l : ℝ) : EReal) ≤ legendreFenchel ψ ε :=
  le_iSup (fun l : ℝ => ((l * ε - ψ l : ℝ) : EReal)) l

open RegretBandits.Stochastic in
theorem lf_ne_bot_cb7 (ψ : ℝ → ℝ) (ε : ℝ) : legendreFenchel ψ ε ≠ ⊥ :=
  ne_bot_of_le_ne_bot (EReal.coe_ne_bot (0 * ε - ψ 0)) (lf_coe_le_cb7 ψ ε 0)

open RegretBandits.Stochastic in
theorem lf_le_toReal_cb7 (ψ : ℝ → ℝ) (ε : ℝ) (h : legendreFenchel ψ ε ≠ ⊤) (l : ℝ) :
    l * ε - ψ l ≤ (legendreFenchel ψ ε).toReal := by
  have h1 := lf_coe_le_cb7 ψ ε l
  rw [← EReal.coe_toReal h (lf_ne_bot_cb7 ψ ε)] at h1
  exact_mod_cast h1

open MeasureTheory ProbabilityTheory RegretBandits.Stochastic in
/-- Optimised Chernoff bound: if `y ≤ ψ*(ε)` and `ε ≥ 0`, the tail is at most `e^{-s y}`. -/
theorem tail_bound_cb7 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (Z : ℕ → Ω → ℝ) (hZm : ∀ k, Measurable (Z k))
    (hind : iIndepFun Z P) (hid : ∀ k, IdentDistrib (Z k) (Z 0) P P) (ψ : ℝ → ℝ)
    (hψneg : ∀ l : ℝ, l ≤ 0 → ψ 0 ≤ ψ l)
    (hmom : ∀ l : ℝ, 0 ≤ l → Integrable (fun ω => Real.exp (l * Z 0 ω)) P ∧
      Real.log (∫ ω, Real.exp (l * Z 0 ω) ∂P) ≤ ψ l)
    (s : ℕ) (hs : 1 ≤ s) (ε : ℝ) (hε : 0 ≤ ε) (y : ℝ)
    (hy : (y : EReal) ≤ legendreFenchel ψ ε) :
    P.real {ω | (s : ℝ) * ε ≤ ∑ k ∈ Finset.range s, Z k ω} ≤ Real.exp (-(s : ℝ) * y) := by
  have hs' : (0 : ℝ) < s := by exact_mod_cast hs
  apply le_of_forall_gt_imp_ge_of_dense
  intro c hc
  have hcpos : 0 < c := lt_trans (Real.exp_pos _) hc
  have hlogc : -(s : ℝ) * y < Real.log c := by
    rw [Real.lt_log_iff_exp_lt hcpos]; exact hc
  set δ := (Real.log c + s * y) / s with hδ
  have hδpos : 0 < δ := by rw [hδ]; apply div_pos _ hs'; linarith
  have hlt : ((y - δ : ℝ) : EReal) < legendreFenchel ψ ε := by
    refine lt_of_lt_of_le ?_ hy
    exact_mod_cast (by linarith : y - δ < y)
  rw [legendreFenchel, lt_iSup_iff] at hlt
  obtain ⟨l, hl⟩ := hlt
  have hl' : y - δ < l * ε - ψ l := by exact_mod_cast hl
  obtain ⟨l0, hl0, hl0v⟩ : ∃ l0 : ℝ, 0 ≤ l0 ∧ y - δ < l0 * ε - ψ l0 := by
    by_cases h : 0 ≤ l
    · exact ⟨l, h, hl'⟩
    · push Not at h
      refine ⟨0, le_refl _, ?_⟩
      have h1 := hψneg l h.le
      have h2 : l * ε ≤ 0 := mul_nonpos_of_nonpos_of_nonneg h.le hε
      linarith
  have hb := chernoff_sum_cb7 P Z hZm hind hid ψ l0 hl0 (hmom l0 hl0).1 (hmom l0 hl0).2 s ε
  refine hb.trans ?_
  have h3 : Real.exp (-(s : ℝ) * (l0 * ε - ψ l0)) ≤ Real.exp (-(s : ℝ) * (y - δ)) := by
    apply Real.exp_le_exp.mpr
    nlinarith
  refine h3.trans (le_of_eq ?_)
  have h4 : (s : ℝ) * ((Real.log c + s * y) / s) = Real.log c + s * y :=
    mul_div_cancel₀ _ hs'.ne'
  rw [show -(s : ℝ) * (y - δ) = Real.log c by rw [hδ]; linear_combination h4]
  exact Real.exp_log hcpos

open RegretBandits.Stochastic in
/-- The generalized inverse is attained: `y ≤ ψ*((ψ*)⁻¹(y))` (convexity in `ε`). -/
theorem lfInv_spec_cb7 (ψ : ℝ → ℝ) (hψfin : ∀ ε : ℝ, 0 ≤ ε → legendreFenchel ψ ε ≠ ⊤)
    (y : ℝ) : 0 ≤ lfInv ψ y ∧ (y : EReal) ≤ legendreFenchel ψ (lfInv ψ y) := by
  set S := {ε : ℝ | 0 ≤ ε ∧ (y : EReal) ≤ legendreFenchel ψ ε} with hS
  have hne : S.Nonempty := by
    refine ⟨max 0 (y + ψ 1), le_max_left _ _, ?_⟩
    refine le_trans ?_ (lf_coe_le_cb7 ψ _ 1)
    have : y ≤ 1 * max 0 (y + ψ 1) - ψ 1 := by
      have := le_max_right 0 (y + ψ 1); linarith
    exact_mod_cast this
  have hbdd : BddBelow S := ⟨0, fun x hx => hx.1⟩
  have h0 : 0 ≤ lfInv ψ y := le_csInf hne (fun x hx => hx.1)
  refine ⟨h0, ?_⟩
  set e := lfInv ψ y with he
  by_contra hcon
  push Not at hcon
  set a := (legendreFenchel ψ e).toReal with ha
  set b := (legendreFenchel ψ (e + 1)).toReal with hb
  have hae : legendreFenchel ψ e = (a : EReal) :=
    (EReal.coe_toReal (hψfin e h0) (lf_ne_bot_cb7 ψ e)).symm
  have hay : a < y := by rw [hae] at hcon; exact_mod_cast hcon
  set θ := min 1 ((y - a) / (2 * (|b - a| + 1))) with hθ
  have hpos2 : (0 : ℝ) < 2 * (|b - a| + 1) := by positivity
  have hθpos : 0 < θ := lt_min one_pos (div_pos (by linarith) hpos2)
  have hlt : sInf S < e + θ := by
    have : e < e + θ := by linarith
    exact this
  obtain ⟨x, hxS, hxlt⟩ := exists_lt_of_csInf_lt hne hlt
  have hex : e ≤ x := csInf_le hbdd hxS
  set θ' := x - e with hθ'
  have hθ'0 : 0 ≤ θ' := by linarith
  have hθ'θ : θ' < θ := by linarith
  have hθ'1 : θ' ≤ 1 := by linarith [min_le_left 1 ((y - a) / (2 * (|b - a| + 1)))]
  have hup : legendreFenchel ψ x ≤ ((a + θ' * (b - a) : ℝ) : EReal) := by
    apply iSup_le
    intro l
    have h1 := lf_le_toReal_cb7 ψ e (hψfin e h0) l
    have h2 := lf_le_toReal_cb7 ψ (e + 1) (hψfin (e + 1) (by linarith)) l
    have hx : x = e + θ' := by rw [hθ']; ring
    have hcomb : l * x - ψ l = (1 - θ') * (l * e - ψ l) + θ' * (l * (e + 1) - ψ l) := by
      rw [hx]; ring
    have h5 : l * x - ψ l ≤ a + θ' * (b - a) := by
      rw [hcomb]
      have m1 := mul_le_mul_of_nonneg_left h1 (by linarith : (0 : ℝ) ≤ 1 - θ')
      have m2 := mul_le_mul_of_nonneg_left h2 hθ'0
      linarith
    exact_mod_cast h5
  have hsmall : a + θ' * (b - a) < y := by
    have hq : θ' * (b - a) ≤ θ' * |b - a| := mul_le_mul_of_nonneg_left (le_abs_self _) hθ'0
    have hθ2 : θ ≤ (y - a) / (2 * (|b - a| + 1)) := min_le_right _ _
    have h3 := (le_div_iff₀ hpos2).mp hθ2
    have h6 : θ' * |b - a| ≤ θ * (|b - a| + 1) :=
      mul_le_mul hθ'θ.le (by linarith) (abs_nonneg _) hθpos.le
    linarith
  have h7 := hxS.2.trans hup
  have h8 : y ≤ a + θ' * (b - a) := by exact_mod_cast h7
  linarith

open MeasureTheory ProbabilityTheory RegretBandits.Stochastic in
theorem arm_indep_cb7 {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {K : ℕ}
    {X : Fin K → ℕ → Ω → ℝ} {μ : Fin K → ℝ} (hX : IsStochasticBandit P X μ) (j : Fin K)
    (f : ℝ → ℝ) (hf : Measurable f) :
    iIndepFun (fun k => fun ω => f (X j k ω)) P := by
  have h1 := hX.indep.precomp (g := fun k : ℕ => (j, k)) (fun a b h => by simpa using h)
  exact h1.comp (fun _ => f) (fun _ => hf)

open MeasureTheory ProbabilityTheory RegretBandits.Stochastic in
/-- (2.3) in the form used: both tails of `μ̂_{j,s}` at `(ψ*)⁻¹(y)` are at most `e^{-s y}`. -/
theorem arm_tail_cb7 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {K : ℕ} {X : Fin K → ℕ → Ω → ℝ} {μ : Fin K → ℝ}
    (hX : IsStochasticBandit P X μ) {ψ : ℝ → ℝ} (hψ : SatisfiesMomentCondition P ψ X μ)
    (hψneg : ∀ l : ℝ, l ≤ 0 → ψ 0 ≤ ψ l)
    (hψfin : ∀ ε : ℝ, 0 ≤ ε → legendreFenchel ψ ε ≠ ⊤) (j : Fin K) (s : ℕ) (hs : 1 ≤ s)
    (y : ℝ) :
    P.real {ω | lfInv ψ y ≤ μ j - sampleMean X j s ω} ≤ Real.exp (-(s : ℝ) * y) ∧
    P.real {ω | lfInv ψ y ≤ sampleMean X j s ω - μ j} ≤ Real.exp (-(s : ℝ) * y) := by
  obtain ⟨h0, hy⟩ := lfInv_spec_cb7 ψ hψfin y
  have hs' : (0 : ℝ) < s := by exact_mod_cast hs
  have hsm : ∀ ω, (s : ℝ) * sampleMean X j s ω = ∑ k ∈ Finset.range s, X j k ω := by
    intro ω; unfold sampleMean; field_simp
  constructor
  · have hb := tail_bound_cb7 P (fun k ω => μ j - X j k ω)
      (fun k => measurable_const.sub (hX.measurable j k))
      (arm_indep_cb7 hX j (fun x => μ j - x) (by fun_prop))
      (fun k => (hX.identDistrib j k).comp (u := fun x => μ j - x) (by fun_prop)) ψ hψneg
      (fun l hl => ⟨(hψ.2 j l hl).2.2.1, (hψ.2 j l hl).2.2.2⟩) s hs (lfInv ψ y) h0 y hy
    refine le_trans (le_of_eq ?_) hb
    congr 1
    ext ω
    simp only [Set.mem_setOf_eq, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range,
      nsmul_eq_mul]
    rw [← hsm ω]
    constructor
    · intro h; nlinarith
    · intro h; nlinarith
  · have hb := tail_bound_cb7 P (fun k ω => X j k ω - μ j)
      (fun k => (hX.measurable j k).sub measurable_const)
      (arm_indep_cb7 hX j (fun x => x - μ j) (by fun_prop))
      (fun k => (hX.identDistrib j k).comp (u := fun x => x - μ j) (by fun_prop)) ψ hψneg
      (fun l hl => ⟨(hψ.2 j l hl).1, (hψ.2 j l hl).2.1⟩) s hs (lfInv ψ y) h0 y hy
    refine le_trans (le_of_eq ?_) hb
    congr 1
    ext ω
    simp only [Set.mem_setOf_eq, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range,
      nsmul_eq_mul]
    rw [← hsm ω]
    constructor
    · intro h; nlinarith
    · intro h; nlinarith

open MeasureTheory in
theorem union_bound_cb7 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (F : ℕ → Set Ω) (t : ℕ) (q : ℝ) (hq : 0 ≤ q)
    (hF : ∀ s ∈ Finset.Icc 1 t, P.real (F s) ≤ q) (E : Set Ω)
    (hE : E ⊆ ⋃ s ∈ Finset.Icc 1 t, F s) :
    P E ≤ ENNReal.ofReal ((t : ℝ) * q) := by
  calc P E ≤ P (⋃ s ∈ Finset.Icc 1 t, F s) := measure_mono hE
    _ ≤ ∑ s ∈ Finset.Icc 1 t, P (F s) := measure_biUnion_finset_le _ _
    _ ≤ ∑ s ∈ Finset.Icc 1 t, ENNReal.ofReal q := by
        gcongr with s hs
        rw [← ofReal_measureReal]
        exact ENNReal.ofReal_le_ofReal (hF s hs)
    _ = ENNReal.ofReal ((t : ℝ) * q) := by
        rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul, ENNReal.ofReal_mul (Nat.cast_nonneg _)]
        simp

theorem rpow_exp_cb7 (α : ℝ) (t s : ℕ) (hs : 1 ≤ s) :
    Real.exp (-(s : ℝ) * (α * Real.log ((t : ℝ) + 1) / (s : ℝ))) = ((t : ℝ) + 1) ^ (-α) := by
  have hs' : (s : ℝ) ≠ 0 := by
    have : (0 : ℝ) < s := by exact_mod_cast hs
    exact this.ne'
  rw [Real.rpow_def_of_pos (by positivity)]
  congr 1
  field_simp

open MeasureTheory ImprovedLinBandits.UCBDelta RegretBandits.Stochastic in
theorem prob_index_low_cb7 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {K : ℕ} (hK : 2 ≤ K) (X : Fin K → ℕ → Ω → ℝ) (μ : Fin K → ℝ)
    (hX : IsStochasticBandit P X μ) (ψ : ℝ → ℝ) (hψ : SatisfiesMomentCondition P ψ X μ)
    (hψneg : ∀ l : ℝ, l ≤ 0 → ψ 0 ≤ ψ l)
    (hψfin : ∀ ε : ℝ, 0 ≤ ε → legendreFenchel ψ ε ≠ ⊤)
    (α : ℝ) (hα : 2 < α) (I : ℕ → Ω → Fin K) (hI : ∀ t, Measurable (I t)) (j : Fin K) (t : ℕ) :
    P {ω | (∀ k, pullCount I k t ω ≠ 0) ∧ ucbIndex ψ α X I j t ω ≤ μ j} ≤
      ENNReal.ofReal ((t : ℝ) * ((t : ℝ) + 1) ^ (-α)) := by
  have hq : 0 ≤ ((t : ℝ) + 1) ^ (-α) := Real.rpow_nonneg (by positivity) _
  refine union_bound_cb7 P
    (fun s => {ω | lfInv ψ (α * Real.log ((t : ℝ) + 1) / (s : ℝ)) ≤ μ j - sampleMean X j s ω})
    t _ hq ?_ _ ?_
  · intro s hs
    have hs1 : 1 ≤ s := (Finset.mem_Icc.mp hs).1
    rw [← rpow_exp_cb7 α t s hs1]
    exact (arm_tail_cb7 P hX hψ hψneg hψfin j s hs1 _).1
  · intro ω hω
    obtain ⟨hall, hidx⟩ := hω
    have hT1 : 1 ≤ pullCount I j t ω := Nat.one_le_iff_ne_zero.mpr (hall j)
    have hTt : pullCount I j t ω ≤ t :=
      (Finset.card_filter_le _ _).trans (Finset.card_range t).le
    simp only [Set.mem_iUnion]
    refine ⟨pullCount I j t ω, Finset.mem_Icc.mpr ⟨hT1, hTt⟩, ?_⟩
    simp only [Set.mem_setOf_eq]
    unfold ucbIndex at hidx
    linarith

open MeasureTheory ImprovedLinBandits.UCBDelta RegretBandits.Stochastic in
theorem prob_mean_high_cb7 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {K : ℕ} (hK : 2 ≤ K) (X : Fin K → ℕ → Ω → ℝ) (μ : Fin K → ℝ)
    (hX : IsStochasticBandit P X μ) (ψ : ℝ → ℝ) (hψ : SatisfiesMomentCondition P ψ X μ)
    (hψneg : ∀ l : ℝ, l ≤ 0 → ψ 0 ≤ ψ l)
    (hψfin : ∀ ε : ℝ, 0 ≤ ε → legendreFenchel ψ ε ≠ ⊤)
    (α : ℝ) (hα : 2 < α) (I : ℕ → Ω → Fin K) (hI : ∀ t, Measurable (I t)) (j : Fin K) (t : ℕ) :
    P {ω | (∀ k, pullCount I k t ω ≠ 0) ∧
        μ j + lfInv ψ (α * Real.log ((t : ℝ) + 1) / (pullCount I j t ω : ℝ)) <
          sampleMean X j (pullCount I j t ω) ω} ≤
      ENNReal.ofReal ((t : ℝ) * ((t : ℝ) + 1) ^ (-α)) := by
  have hq : 0 ≤ ((t : ℝ) + 1) ^ (-α) := Real.rpow_nonneg (by positivity) _
  refine union_bound_cb7 P
    (fun s => {ω | lfInv ψ (α * Real.log ((t : ℝ) + 1) / (s : ℝ)) ≤ sampleMean X j s ω - μ j})
    t _ hq ?_ _ ?_
  · intro s hs
    have hs1 : 1 ≤ s := (Finset.mem_Icc.mp hs).1
    rw [← rpow_exp_cb7 α t s hs1]
    exact (arm_tail_cb7 P hX hψ hψneg hψfin j s hs1 _).2
  · intro ω hω
    obtain ⟨hall, hidx⟩ := hω
    have hT1 : 1 ≤ pullCount I j t ω := Nat.one_le_iff_ne_zero.mpr (hall j)
    have hTt : pullCount I j t ω ≤ t :=
      (Finset.card_filter_le _ _).trans (Finset.card_range t).le
    simp only [Set.mem_iUnion]
    refine ⟨pullCount I j t ω, Finset.mem_Icc.mpr ⟨hT1, hTt⟩, ?_⟩
    simp only [Set.mem_setOf_eq]
    linarith

theorem step_cb7 (β : ℝ) (hβ : 0 < β) (t : ℕ) (ht : 1 ≤ t) :
    (t : ℝ) * ((t : ℝ) + 1) ^ (-(β + 2)) ≤
      (Real.exp (-β * Real.log t) - Real.exp (-β * Real.log ((t : ℝ) + 1))) / β := by
  have ht0 : (0 : ℝ) < t := by exact_mod_cast ht
  have ht1 : (0 : ℝ) < (t : ℝ) + 1 := by linarith
  set L := Real.log (t : ℝ) with hL
  set L' := Real.log ((t : ℝ) + 1) with hL'
  have hdiff : 1 / ((t : ℝ) + 1) ≤ L' - L := by
    have h := Real.log_le_sub_one_of_pos (div_pos ht0 ht1)
    rw [Real.log_div ht0.ne' ht1.ne'] at h
    have : (t : ℝ) / (t + 1) - 1 = -(1 / (t + 1)) := by field_simp; ring
    linarith
  have hexpL' : Real.exp (-L') = 1 / ((t : ℝ) + 1) := by
    rw [Real.exp_neg, Real.exp_log ht1, one_div]
  rw [Real.rpow_def_of_pos ht1, le_div_iff₀ hβ]
  have h1 : (t : ℝ) * Real.exp (L' * -(β + 2)) ≤ Real.exp (-(β + 1) * L') := by
    have : Real.exp (-(β + 1) * L') = ((t : ℝ) + 1) * Real.exp (L' * -(β + 2)) := by
      rw [show -(β + 1) * L' = L' + L' * -(β + 2) by ring, Real.exp_add, Real.exp_log ht1]
    rw [this]
    have := Real.exp_pos (L' * -(β + 2))
    nlinarith
  have h2 : Real.exp (-β * L') * (1 + β * (L' - L)) ≤ Real.exp (-β * L) := by
    have : Real.exp (-β * L) = Real.exp (-β * L') * Real.exp (β * (L' - L)) := by
      rw [← Real.exp_add]; congr 1; ring
    rw [this]
    apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
    linarith [Real.add_one_le_exp (β * (L' - L))]
  have h3 : Real.exp (-(β + 1) * L') = Real.exp (-β * L') * (1 / ((t : ℝ) + 1)) := by
    rw [← hexpL', ← Real.exp_add]; congr 1; ring
  have h4 : Real.exp (-β * L') * (β * (1 / ((t : ℝ) + 1))) ≤
      Real.exp (-β * L') * (β * (L' - L)) := by
    apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
    exact mul_le_mul_of_nonneg_left hdiff hβ.le
  calc (t : ℝ) * Real.exp (L' * -(β + 2)) * β ≤ Real.exp (-(β + 1) * L') * β :=
        mul_le_mul_of_nonneg_right h1 hβ.le
    _ = Real.exp (-β * L') * (β * (1 / ((t : ℝ) + 1))) := by rw [h3]; ring
    _ ≤ Real.exp (-β * L') * (β * (L' - L)) := h4
    _ ≤ Real.exp (-β * L) - Real.exp (-β * L') := by linarith

theorem sum_bound_cb7 (β : ℝ) (hβ : 0 < β) (n : ℕ) (hn : 1 ≤ n) :
    ∑ t ∈ Finset.range n, (t : ℝ) * ((t : ℝ) + 1) ^ (-(β + 2)) ≤
      (1 - Real.exp (-β * Real.log n)) / β := by
  induction n, hn using Nat.le_induction with
  | base => simp
  | succ m hm ih =>
    rw [Finset.sum_range_succ]
    have := step_cb7 β hβ m hm
    push_cast
    calc _ ≤ (1 - Real.exp (-β * Real.log m)) / β +
          (Real.exp (-β * Real.log m) - Real.exp (-β * Real.log ((m : ℝ) + 1))) / β :=
          add_le_add ih this
      _ = _ := by ring

theorem sum_tail_rpow_le_cb7 (α : ℝ) (hα : 2 < α) (n : ℕ) :
    ∑ t ∈ Finset.range n, 2 * ((t : ℝ) * ((t : ℝ) + 1) ^ (-α)) ≤ 2 / (α - 2) := by
  rw [← Finset.mul_sum]
  have hβ : 0 < α - 2 := by linarith
  have key : ∑ t ∈ Finset.range n, (t : ℝ) * ((t : ℝ) + 1) ^ (-α) ≤ 1 / (α - 2) := by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp only [Finset.range_zero, Finset.sum_empty]; positivity
    · have h := sum_bound_cb7 (α - 2) hβ n hn
      simp only [show -(α - 2 + 2) = -α by ring] at h
      refine h.trans ?_
      gcongr
      linarith [Real.exp_pos (-(α - 2) * Real.log n)]
  calc 2 * ∑ t ∈ Finset.range n, (t : ℝ) * ((t : ℝ) + 1) ^ (-α) ≤ 2 * (1 / (α - 2)) := by
        gcongr
    _ = 2 / (α - 2) := by ring

open MeasureTheory ImprovedLinBandits.UCBDelta in
theorem pullCount_measurable_cb7 {Ω : Type*} [MeasurableSpace Ω] {K : ℕ}
    (I : ℕ → Ω → Fin K) (hI : ∀ t, Measurable (I t)) (j : Fin K) (t : ℕ) :
    Measurable (fun ω => pullCount I j t ω) := by
  have : (fun ω => pullCount I j t ω) =
      fun ω => ∑ s ∈ Finset.range t, if I (s + 1) ω = j then 1 else 0 := by
    funext ω; exact pullCount_eq_sum_cb7 I j t ω
  rw [this]
  refine Finset.measurable_sum _ (fun s _ => ?_)
  exact Measurable.ite ((hI (s + 1)) (measurableSet_singleton j)) measurable_const
    measurable_const

open MeasureTheory RegretBandits.Stochastic in
theorem sampleMean_measurable_cb7 {Ω : Type*} [MeasurableSpace Ω] {K : ℕ}
    (X : Fin K → ℕ → Ω → ℝ) (hXm : ∀ i k, Measurable (X i k)) (j : Fin K) (s : ℕ) :
    Measurable (fun ω => sampleMean X j s ω) := by
  unfold sampleMean
  exact (Finset.measurable_sum _ (fun k _ => hXm j k)).div_const _

theorem compose_measurable_cb7 {Ω : Type*} [MeasurableSpace Ω] (T : Ω → ℕ)
    (hT : Measurable T) (F : ℕ → Ω → ℝ) (hF : ∀ s, Measurable (F s)) :
    Measurable (fun ω => F (T ω) ω) := by
  have h : Measurable (fun p : ℕ × Ω => F p.1 p.2) :=
    measurable_from_prod_countable_right (fun s => hF s)
  exact h.comp (hT.prodMk measurable_id)

open MeasureTheory ImprovedLinBandits.UCBDelta RegretBandits.Stochastic in
theorem events_measurable_cb7 {Ω : Type*} [MeasurableSpace Ω] {K : ℕ} (X : Fin K → ℕ → Ω → ℝ)
    (hXm : ∀ i k, Measurable (X i k)) (μ : Fin K → ℝ) (ψ : ℝ → ℝ) (α : ℝ)
    (I : ℕ → Ω → Fin K) (hI : ∀ t, Measurable (I t)) (j : Fin K) (t : ℕ) :
    MeasurableSet {ω | (∀ k, pullCount I k t ω ≠ 0) ∧ ucbIndex ψ α X I j t ω ≤ μ j} ∧
    MeasurableSet {ω | (∀ k, pullCount I k t ω ≠ 0) ∧
        μ j + lfInv ψ (α * Real.log ((t : ℝ) + 1) / (pullCount I j t ω : ℝ)) <
          sampleMean X j (pullCount I j t ω) ω} ∧
    Measurable (fun ω => (pullCount I j t ω : ℝ)) := by
  have hT : ∀ k, Measurable (fun ω => pullCount I k t ω) := fun k =>
    pullCount_measurable_cb7 I hI k t
  have hall : MeasurableSet {ω | ∀ k, pullCount I k t ω ≠ 0} := by
    rw [Set.setOf_forall]
    exact MeasurableSet.iInter (fun k => (hT k (measurableSet_singleton 0)).compl)
  have hidx : Measurable (fun ω => ucbIndex ψ α X I j t ω) :=
    compose_measurable_cb7 _ (hT j)
      (fun s ω => sampleMean X j s ω + lfInv ψ (α * Real.log ((t : ℝ) + 1) / (s : ℝ)))
      (fun s => (sampleMean_measurable_cb7 X hXm j s).add_const _)
  have hsm : Measurable (fun ω => sampleMean X j (pullCount I j t ω) ω) :=
    compose_measurable_cb7 _ (hT j) (fun s ω => sampleMean X j s ω)
      (fun s => sampleMean_measurable_cb7 X hXm j s)
  have hrad : Measurable
      (fun ω => μ j + lfInv ψ (α * Real.log ((t : ℝ) + 1) / (pullCount I j t ω : ℝ))) :=
    compose_measurable_cb7 _ (hT j)
      (fun s _ => μ j + lfInv ψ (α * Real.log ((t : ℝ) + 1) / (s : ℝ)))
      (fun s => measurable_const)
  refine ⟨?_, ?_, ?_⟩
  · exact hall.inter (measurableSet_le hidx measurable_const)
  · exact hall.inter (measurableSet_lt hrad hsm)
  · exact (measurable_from_nat (f := fun n : ℕ => (n : ℝ))).comp (hT j)

open ImprovedLinBandits.UCBDelta in
theorem pullCount_succ_cb7 {Ω : Type*} {K : ℕ} (I : ℕ → Ω → Fin K) (i : Fin K) (t : ℕ)
    (ω : Ω) :
    pullCount I i (t + 1) ω = pullCount I i t ω + (if I (t + 1) ω = i then 1 else 0) := by
  rw [pullCount_eq_sum_cb7, pullCount_eq_sum_cb7, Finset.sum_range_succ]

open ImprovedLinBandits.UCBDelta in
theorem pullCount_mono_cb7 {Ω : Type*} {K : ℕ} (I : ℕ → Ω → Fin K) (i : Fin K) (ω : Ω)
    (a b : ℕ) (hab : a ≤ b) : pullCount I i a ω ≤ pullCount I i b ω := by
  unfold pullCount
  exact Finset.card_le_card (Finset.filter_subset_filter _ (Finset.range_mono hab))

open ImprovedLinBandits.UCBDelta in
theorem pullCount_strict_cb7 {Ω : Type*} {K : ℕ} (I : ℕ → Ω → Fin K) (i : Fin K) (ω : Ω)
    (a b : ℕ) (hab : a < b) (ha : I (a + 1) ω = i) :
    pullCount I i a ω < pullCount I i b ω := by
  have h1 := pullCount_succ_cb7 I i a ω
  rw [if_pos ha] at h1
  have h2 := pullCount_mono_cb7 I i ω (a + 1) b hab
  omega

open RegretBandits.Stochastic ImprovedLinBandits.UCBDelta in
/-- Eqs. (2.5)–(2.7) (copied from our accepted proof b053a74f). -/
theorem ucb_three_events_cb7 {Ω : Type*} {K : ℕ} (hK : 2 ≤ K) (ψ : ℝ → ℝ) (α : ℝ) (hα : 0 < α)
    (X : Fin K → ℕ → Ω → ℝ) (μ : Fin K → ℝ) (I : ℕ → Ω → Fin K)
    (hrun : IsAlphaPsiUCBRun ψ α X I) (n t : ℕ) (htn : t + 1 ≤ n) (ω : Ω) (i istar : Fin K)
    (hstar : μ istar = bestMean μ) (hgap : 0 < gap μ i)
    (hψpos : (0 : EReal) < legendreFenchel ψ (gap μ i / 2))
    (hplayed : ∀ j, pullCount I j t ω ≠ 0) (hIt : I (t + 1) ω = i) :
    ucbIndex ψ α X I istar t ω ≤ bestMean μ ∨
      μ i + lfInv ψ (α * Real.log ((t : ℝ) + 1) / (pullCount I i t ω : ℝ)) <
        sampleMean X i (pullCount I i t ω) ω ∨
      (pullCount I i t ω : ℝ) <
        α * Real.log (n : ℝ) / (legendreFenchel ψ (gap μ i / 2)).toReal := by
  by_contra hcon
  push Not at hcon
  obtain ⟨hA, hB, hC⟩ := hcon
  set T : ℕ := pullCount I i t ω with hT
  set y : ℝ := α * Real.log ((t : ℝ) + 1) / (T : ℝ) with hy
  set L : ℝ := lfInv ψ y with hL
  have hTpos : (0 : ℝ) < (T : ℝ) := by
    have := hplayed i
    exact_mod_cast Nat.pos_of_ne_zero this
  have hmax := (hrun ω t).2 hplayed istar
  rw [hIt] at hmax
  have hidx : ucbIndex ψ α X I i t ω = sampleMean X i T ω + L := rfl
  have hgapdef : gap μ i = bestMean μ - μ i := rfl
  have hLgt : gap μ i / 2 < L := by
    have h1 : bestMean μ < sampleMean X i T ω + L := lt_of_lt_of_le hA (hidx ▸ hmax)
    rw [hgapdef]; linarith
  have hmem : gap μ i / 2 ∈ {ε : ℝ | 0 ≤ ε ∧ (y : EReal) ≤ legendreFenchel ψ ε} := by
    refine ⟨by linarith, ?_⟩
    have hlog : Real.log ((t : ℝ) + 1) ≤ Real.log (n : ℝ) := by
      apply Real.log_le_log (by positivity)
      exact_mod_cast htn
    have hlog0 : 0 ≤ Real.log ((t : ℝ) + 1) :=
      Real.log_nonneg (by linarith [(Nat.cast_nonneg t : (0:ℝ) ≤ t)])
    by_cases htop : legendreFenchel ψ (gap μ i / 2) = ⊤
    · rw [htop]; exact le_top
    · have hbot : legendreFenchel ψ (gap μ i / 2) ≠ ⊥ := ne_bot_of_gt hψpos
      have hcoe : legendreFenchel ψ (gap μ i / 2) =
          ((legendreFenchel ψ (gap μ i / 2)).toReal : EReal) := (EReal.coe_toReal htop hbot).symm
      generalize hcd : (legendreFenchel ψ (gap μ i / 2)).toReal = c at hcoe hC
      rw [hcoe] at hψpos ⊢
      have hc : (0 : ℝ) < c := by exact_mod_cast hψpos
      have hTc : α * Real.log (n : ℝ) ≤ (T : ℝ) * c := by
        rw [div_le_iff₀ hc] at hC; exact hC
      have : y ≤ c := by
        rw [hy, div_le_iff₀ hTpos]
        nlinarith
      exact_mod_cast this
  have hLle : L ≤ gap μ i / 2 := csInf_le ⟨0, fun x hx => hx.1⟩ hmem
  linarith

open Classical RegretBandits.Stochastic ImprovedLinBandits.UCBDelta in
/-- Pathwise counting (R3): `T_i(n) ≤ 1 + A + #{t < n : (2.5) or (2.6)}`. -/
theorem pullCount_le_events_cb7 {Ω : Type*} {K : ℕ} (hK : 2 ≤ K) (ψ : ℝ → ℝ) (α : ℝ)
    (hα : 0 < α)
    (X : Fin K → ℕ → Ω → ℝ) (μ : Fin K → ℝ) (I : ℕ → Ω → Fin K)
    (hrun : IsAlphaPsiUCBRun ψ α X I) (n : ℕ) (ω : Ω) (i istar : Fin K)
    (hstar : μ istar = bestMean μ) (hgap : 0 < gap μ i)
    (hψpos : (0 : EReal) < legendreFenchel ψ (gap μ i / 2)) :
    (pullCount I i n ω : ℝ) ≤
      1 + α * Real.log (n : ℝ) / (legendreFenchel ψ (gap μ i / 2)).toReal +
        ∑ t ∈ Finset.range n,
          ((if (∀ k, pullCount I k t ω ≠ 0) ∧ ucbIndex ψ α X I istar t ω ≤ μ istar
              then (1 : ℝ) else 0) +
           (if (∀ k, pullCount I k t ω ≠ 0) ∧
              μ i + lfInv ψ (α * Real.log ((t : ℝ) + 1) / (pullCount I i t ω : ℝ)) <
                sampleMean X i (pullCount I i t ω) ω then (1 : ℝ) else 0)) := by
  set A := α * Real.log (n : ℝ) / (legendreFenchel ψ (gap μ i / 2)).toReal with hA
  have hA0 : 0 ≤ A := by
    apply div_nonneg (mul_nonneg hα.le (Real.log_natCast_nonneg n))
    exact EReal.toReal_nonneg hψpos.le
  set f : ℕ → ℝ := fun t =>
    ((if (∀ k, pullCount I k t ω ≠ 0) ∧ ucbIndex ψ α X I istar t ω ≤ μ istar
        then (1 : ℝ) else 0) +
     (if (∀ k, pullCount I k t ω ≠ 0) ∧
        μ i + lfInv ψ (α * Real.log ((t : ℝ) + 1) / (pullCount I i t ω : ℝ)) <
          sampleMean X i (pullCount I i t ω) ω then (1 : ℝ) else 0)) with hf
  have hf0 : ∀ t, 0 ≤ f t := fun t => by
    simp only [hf]; split_ifs <;> norm_num
  set S := (Finset.range n).filter (fun t => I (t + 1) ω = i) with hS
  have hinj : ∀ a ∈ S, ∀ b ∈ S, pullCount I i a ω = pullCount I i b ω → a = b := by
    intro a ha b hb hab
    have ha' := (Finset.mem_filter.mp ha).2
    have hb' := (Finset.mem_filter.mp hb).2
    rcases lt_trichotomy a b with h | h | h
    · exact absurd hab (pullCount_strict_cb7 I i ω a b h ha').ne
    · exact h
    · exact absurd hab.symm (pullCount_strict_cb7 I i ω b a h hb').ne
  set S0 := S.filter (fun t => pullCount I i t ω = 0) with hS0
  set S1 := S.filter (fun t => pullCount I i t ω ≠ 0 ∧ (pullCount I i t ω : ℝ) < A) with hS1
  set S2 := S.filter (fun t => pullCount I i t ω ≠ 0 ∧ ¬ (pullCount I i t ω : ℝ) < A)
    with hS2
  have hsub : S ⊆ S0 ∪ S1 ∪ S2 := by
    intro t ht
    simp only [hS0, hS1, hS2, Finset.mem_union, Finset.mem_filter]
    by_cases h0 : pullCount I i t ω = 0
    · exact Or.inl (Or.inl ⟨ht, h0⟩)
    · by_cases h1 : (pullCount I i t ω : ℝ) < A
      · exact Or.inl (Or.inr ⟨ht, h0, h1⟩)
      · exact Or.inr ⟨ht, h0, h1⟩
  have hc0 : S0.card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro a ha b hb
    have ha' := Finset.mem_filter.mp ha
    have hb' := Finset.mem_filter.mp hb
    exact hinj a ha'.1 b hb'.1 (by rw [ha'.2, hb'.2])
  have hc1 : (S1.card : ℝ) ≤ A := by
    have h1 : S1.card ≤ (Finset.Ico 1 ⌈A⌉₊).card := by
      apply Finset.card_le_card_of_injOn (fun t => pullCount I i t ω)
      · intro t ht
        have ht' := Finset.mem_filter.mp (Finset.mem_coe.mp ht)
        simp only [Finset.coe_Ico, Set.mem_Ico]
        exact ⟨Nat.one_le_iff_ne_zero.mpr ht'.2.1, Nat.lt_ceil.mpr ht'.2.2⟩
      · intro a ha b hb hab
        exact hinj a (Finset.mem_filter.mp (Finset.mem_coe.mp ha)).1 b
          (Finset.mem_filter.mp (Finset.mem_coe.mp hb)).1 hab
    rw [Nat.card_Ico] at h1
    have h2 : ((⌈A⌉₊ - 1 : ℕ) : ℝ) ≤ A := by
      rcases Nat.eq_zero_or_pos ⌈A⌉₊ with h | h
      · rw [h]; simpa using hA0
      · rw [Nat.cast_sub h]
        have := Nat.ceil_lt_add_one hA0
        push_cast
        linarith
    exact le_trans (by exact_mod_cast h1) h2
  have hc2 : (S2.card : ℝ) ≤ ∑ t ∈ Finset.range n, f t := by
    have hS2sub : S2 ⊆ Finset.range n := fun t ht =>
      (Finset.mem_filter.mp (Finset.mem_filter.mp ht).1).1
    have hge : ∀ t ∈ S2, (1 : ℝ) ≤ f t := by
      intro t ht
      have ht' := Finset.mem_filter.mp ht
      have htS := Finset.mem_filter.mp ht'.1
      have htn : t + 1 ≤ n := Finset.mem_range.mp htS.1
      have hIt : I (t + 1) ω = i := htS.2
      have hplayed : ∀ k, pullCount I k t ω ≠ 0 := by
        by_contra hcon
        push Not at hcon
        have h1 := (hrun ω t).1 hcon
        rw [hIt] at h1
        exact ht'.2.1 h1
      rcases ucb_three_events_cb7 hK ψ α hα X μ I hrun n t htn ω i istar hstar hgap hψpos
        hplayed hIt with h | h | h
      · have h5 : (∀ k, pullCount I k t ω ≠ 0) ∧ ucbIndex ψ α X I istar t ω ≤ μ istar :=
          ⟨hplayed, by rw [hstar]; exact h⟩
        simp only [hf, if_pos h5]
        split_ifs <;> norm_num
      · have h6 : (∀ k, pullCount I k t ω ≠ 0) ∧
            μ i + lfInv ψ (α * Real.log ((t : ℝ) + 1) / (pullCount I i t ω : ℝ)) <
              sampleMean X i (pullCount I i t ω) ω := ⟨hplayed, h⟩
        simp only [hf, if_pos h6]
        split_ifs <;> norm_num
      · exact absurd h ht'.2.2
    calc (S2.card : ℝ) = ∑ t ∈ S2, (1 : ℝ) := by simp
      _ ≤ ∑ t ∈ S2, f t := Finset.sum_le_sum hge
      _ ≤ ∑ t ∈ Finset.range n, f t :=
          Finset.sum_le_sum_of_subset_of_nonneg hS2sub (fun t _ _ => hf0 t)
  have hcard : S.card ≤ S0.card + S1.card + S2.card :=
    (Finset.card_le_card hsub).trans
      ((Finset.card_union_le _ _).trans (by
        have := Finset.card_union_le S0 S1
        omega))
  have hpc : (pullCount I i n ω : ℝ) = (S.card : ℝ) := rfl
  have hcardR : (S.card : ℝ) ≤ S0.card + S1.card + S2.card := by exact_mod_cast hcard
  have hc0R : (S0.card : ℝ) ≤ 1 := by exact_mod_cast hc0
  rw [hpc]
  show (S.card : ℝ) ≤ 1 + A + ∑ t ∈ Finset.range n, f t
  linarith

open MeasureTheory ImprovedLinBandits.UCBDelta in
theorem pullCount_cast_eq_7d8a {Ω : Type*} {K : ℕ} (I : ℕ → Ω → Fin K) (i : Fin K) (n : ℕ)
    (ω : Ω) :
    (pullCount I i n ω : ℝ) = ∑ t ∈ Finset.range n, if I (t + 1) ω = i then (1 : ℝ) else 0 := by
  rw [pullCount, Finset.card_filter]
  push_cast
  rfl

open MeasureTheory ImprovedLinBandits.UCBDelta in
theorem pullCount_integrable_7d8a {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {K : ℕ} (I : ℕ → Ω → Fin K)
    (hI : ∀ t, Measurable (I t)) (i : Fin K) (n : ℕ) :
    Integrable (fun ω => (pullCount I i n ω : ℝ)) P := by
  simp_rw [pullCount_cast_eq_7d8a]
  refine integrable_finsetSum _ (fun t _ => ?_)
  have hm : MeasurableSet {ω | I (t + 1) ω = i} := (hI (t + 1)) (measurableSet_singleton i)
  have : (fun ω => if I (t + 1) ω = i then (1 : ℝ) else 0)
      = Set.indicator {ω | I (t + 1) ω = i} (fun _ => (1 : ℝ)) := by
    funext ω; simp [Set.indicator]
  rw [this]
  exact (integrable_const (1 : ℝ)).indicator hm

open MeasureTheory ImprovedLinBandits.UCBDelta in
theorem sum_pullCount_7d8a {Ω : Type*} {K : ℕ} (I : ℕ → Ω → Fin K) (n : ℕ) (ω : Ω) :
    ∑ i, (pullCount I i n ω : ℝ) = n := by
  simp_rw [pullCount_cast_eq_7d8a]
  rw [Finset.sum_comm]
  simp

open MeasureTheory ImprovedLinBandits.UCBDelta in
theorem sum_pullCount_mul_7d8a {Ω : Type*} {K : ℕ} (μ : Fin K → ℝ) (I : ℕ → Ω → Fin K) (n : ℕ)
    (ω : Ω) :
    ∑ i, (pullCount I i n ω : ℝ) * μ i = ∑ t ∈ Finset.range n, μ (I (t + 1) ω) := by
  simp_rw [pullCount_cast_eq_7d8a, Finset.sum_mul]
  rw [Finset.sum_comm]
  simp

open MeasureTheory ImprovedLinBandits.UCBDelta RegretBandits.Stochastic in
theorem pseudo_regret_decomposition_cb7 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {K : ℕ} (hK : 2 ≤ K) (μ : Fin K → ℝ) (I : ℕ → Ω → Fin K)
    (hI : ∀ t, Measurable (I t)) (n : ℕ) :
    pseudoRegretBar P μ I n =
        (∑ i, ∫ ω, (pullCount I i n ω : ℝ) ∂P) * bestMean μ
          - ∫ ω, ∑ i, (pullCount I i n ω : ℝ) * μ i ∂P ∧
      pseudoRegretBar P μ I n = ∑ i, gap μ i * ∫ ω, (pullCount I i n ω : ℝ) ∂P := by
  have hint := pullCount_integrable_7d8a P I hI
  have hsum : ∑ i, ∫ ω, (pullCount I i n ω : ℝ) ∂P = n := by
    rw [← integral_finsetSum _ (fun i _ => hint i n)]
    simp_rw [sum_pullCount_7d8a]
    simp
  have hmul : ∫ ω, ∑ i, (pullCount I i n ω : ℝ) * μ i ∂P
      = ∑ i, (∫ ω, (pullCount I i n ω : ℝ) ∂P) * μ i := by
    rw [integral_finsetSum _ (fun i _ => (hint i n).mul_const (μ i))]
    simp_rw [integral_mul_const]
  have h1 : pseudoRegretBar P μ I n =
      (∑ i, ∫ ω, (pullCount I i n ω : ℝ) ∂P) * bestMean μ
        - ∫ ω, ∑ i, (pullCount I i n ω : ℝ) * μ i ∂P := by
    unfold pseudoRegretBar
    rw [hsum]
    simp_rw [sum_pullCount_mul_7d8a]
  refine ⟨h1, ?_⟩
  rw [h1, hmul, hsum]
  rw [← hsum, Finset.sum_mul, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  unfold gap
  ring

open MeasureTheory ImprovedLinBandits.UCBDelta RegretBandits.Stochastic in
theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {K : ℕ} (hK : 2 ≤ K) (X : Fin K → ℕ → Ω → ℝ) (μ : Fin K → ℝ)
    (hX : IsStochasticBandit P X μ) (ψ : ℝ → ℝ) (hψ : SatisfiesMomentCondition P ψ X μ)
    (hψneg : ∀ l : ℝ, l ≤ 0 → ψ 0 ≤ ψ l)
    (hψfin : ∀ ε : ℝ, 0 ≤ ε → legendreFenchel ψ ε ≠ ⊤)
    (hψpos : ∀ i, 0 < gap μ i → (0 : EReal) < legendreFenchel ψ (gap μ i / 2))
    (α : ℝ) (hα : 2 < α) (I : ℕ → Ω → Fin K) (hI : ∀ t, Measurable (I t))
    (hrun : IsAlphaPsiUCBRun ψ α X I) (n : ℕ) :
    pseudoRegretBar P μ I n ≤
      ∑ i ∈ Finset.univ.filter (fun i => 0 < gap μ i),
        gap μ i * (α * Real.log (n : ℝ) / (legendreFenchel ψ (gap μ i / 2)).toReal
          + α / (α - 2)) := by
  classical
  have hα0 : 0 < α := by linarith
  have hgap0 : ∀ i, 0 ≤ gap μ i := fun i =>
    sub_nonneg.mpr (le_ciSup (Set.finite_range μ).bddAbove i)
  have : Nonempty (Fin K) := ⟨⟨0, by omega⟩⟩
  obtain ⟨istar, hstar⟩ := exists_eq_ciSup_of_finite (f := μ)
  have harm : ∀ i, 0 < gap μ i → ∫ ω, (pullCount I i n ω : ℝ) ∂P ≤
      α * Real.log (n : ℝ) / (legendreFenchel ψ (gap μ i / 2)).toReal + α / (α - 2) := by
    intro i hgi
    set A := α * Real.log (n : ℝ) / (legendreFenchel ψ (gap μ i / 2)).toReal with hA
    set E5 : ℕ → Set Ω := fun t =>
      {ω | (∀ k, pullCount I k t ω ≠ 0) ∧ ucbIndex ψ α X I istar t ω ≤ μ istar} with hE5
    set E6 : ℕ → Set Ω := fun t =>
      {ω | (∀ k, pullCount I k t ω ≠ 0) ∧
        μ i + lfInv ψ (α * Real.log ((t : ℝ) + 1) / (pullCount I i t ω : ℝ)) <
          sampleMean X i (pullCount I i t ω) ω} with hE6
    have hm5 : ∀ t, MeasurableSet (E5 t) := fun t =>
      (events_measurable_cb7 X hX.measurable μ ψ α I hI istar t).1
    have hm6 : ∀ t, MeasurableSet (E6 t) := fun t =>
      (events_measurable_cb7 X hX.measurable μ ψ α I hI i t).2.1
    have hind5 : ∀ t, Integrable ((E5 t).indicator (1 : Ω → ℝ)) P := fun t =>
      (integrable_const (1 : ℝ)).indicator (hm5 t)
    have hind6 : ∀ t, Integrable ((E6 t).indicator (1 : Ω → ℝ)) P := fun t =>
      (integrable_const (1 : ℝ)).indicator (hm6 t)
    have hpt : ∀ ω, (pullCount I i n ω : ℝ) ≤
        1 + A + ∑ t ∈ Finset.range n, ((E5 t).indicator 1 ω + (E6 t).indicator 1 ω) := by
      intro ω
      have h := pullCount_le_events_cb7 hK ψ α hα0 X μ I hrun n ω i istar hstar hgi (hψpos i hgi)
      simpa only [hE5, hE6, Set.indicator_apply, Set.mem_setOf_eq, Pi.one_apply] using h
    have hint : Integrable (fun ω => (pullCount I i n ω : ℝ)) P := by
      refine Integrable.of_bound
        (events_measurable_cb7 X hX.measurable μ ψ α I hI i n).2.2.aestronglyMeasurable
        (n : ℝ) (Filter.Eventually.of_forall fun ω => ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _)]
      exact_mod_cast (Finset.card_filter_le _ _).trans (Finset.card_range n).le
    have hsumint : Integrable (fun ω => ∑ t ∈ Finset.range n,
        ((E5 t).indicator (1 : Ω → ℝ) ω + (E6 t).indicator 1 ω)) P :=
      integrable_finset_sum _ fun t _ => (hind5 t).add (hind6 t)
    have hP5 := fun t => prob_index_low_cb7 P hK X μ hX ψ hψ hψneg hψfin α hα I hI istar t
    have hP6 := fun t => prob_mean_high_cb7 P hK X μ hX ψ hψ hψneg hψfin α hα I hI i t
    have hbnd : ∀ t : ℕ, 0 ≤ (t : ℝ) * ((t : ℝ) + 1) ^ (-α) := fun t =>
      mul_nonneg (Nat.cast_nonneg t) (Real.rpow_nonneg (by positivity) _)
    calc ∫ ω, (pullCount I i n ω : ℝ) ∂P
        ≤ ∫ ω, (1 + A + ∑ t ∈ Finset.range n,
            ((E5 t).indicator (1 : Ω → ℝ) ω + (E6 t).indicator 1 ω)) ∂P :=
          integral_mono hint ((integrable_const _).add hsumint) hpt
      _ = 1 + A + ∑ t ∈ Finset.range n, (P.real (E5 t) + P.real (E6 t)) := by
          have hfs := integral_finset_sum (μ := P) (Finset.range n)
            (f := fun t ω => (E5 t).indicator (1 : Ω → ℝ) ω + (E6 t).indicator 1 ω)
            (fun t _ => (hind5 t).add (hind6 t))
          rw [integral_add (integrable_const _) hsumint, integral_const, hfs]
          simp only [probReal_univ, one_smul]
          congr 1
          refine Finset.sum_congr rfl fun t _ => ?_
          rw [integral_add (hind5 t) (hind6 t), integral_indicator_one (hm5 t),
            integral_indicator_one (hm6 t)]
      _ ≤ 1 + A + ∑ t ∈ Finset.range n, 2 * ((t : ℝ) * ((t : ℝ) + 1) ^ (-α)) := by
          gcongr with t ht
          have a5 := ENNReal.toReal_le_of_le_ofReal (hbnd t) (hP5 t)
          have a6 := ENNReal.toReal_le_of_le_ofReal (hbnd t) (hP6 t)
          rw [measureReal_def, measureReal_def]
          linarith
      _ ≤ 1 + A + 2 / (α - 2) := by linarith [sum_tail_rpow_le_cb7 α hα n]
      _ = A + α / (α - 2) := by
          have : α - 2 ≠ 0 := by linarith
          field_simp
          ring
  rw [(pseudo_regret_decomposition_cb7 P hK μ I hI n).2,
    ← Finset.sum_filter_of_ne (p := fun i => 0 < gap μ i)]
  · exact Finset.sum_le_sum fun i hi =>
      mul_le_mul_of_nonneg_left (harm i (Finset.mem_filter.mp hi).2) (hgap0 i)
  · intro i _ hne
    exact lt_of_le_of_ne (hgap0 i) (fun h => hne (by rw [← h, zero_mul]))

