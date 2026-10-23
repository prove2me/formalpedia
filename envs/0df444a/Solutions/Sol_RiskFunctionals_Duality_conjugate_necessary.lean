-- Prove2me | solution 1 for RiskFunctionals.Duality.conjugate_necessary
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T17:45:22.953419+00:00
-- url     : https://prove2.me/submissions/33be95fe-8b12-4cda-9bcf-acf05ff56ad7

import Mathlib
import Definitions.Def_RiskFunctionals_Duality_Functionals
import Definitions.Def_RiskFunctionals_Duality_Conjugates
-- ===== module A

noncomputable section
set_option linter.unusedSectionVars false
open MeasureTheory RiskFunctionals.Duality

namespace X5CN

/-! ### EReal helpers -/

lemma bot_of {x : EReal} {α β : ℝ} (hβ : β < 0)
    (h : ∀ c : ℝ, 0 ≤ c → x ≤ ((α + c * β : ℝ) : EReal)) : x = ⊥ := by
  rw [EReal.eq_bot_iff_forall_lt]
  intro y
  set c := (|y| + |α| + 1) / (-β)
  have hc : 0 ≤ c := div_nonneg (by positivity) (by linarith)
  have hcb : c * β = -(|y| + |α| + 1) := by
    have hb : -β ≠ 0 := by linarith
    calc c * β = -(c * -β) := by ring
      _ = -(|y| + |α| + 1) := by simp only [c]; rw [div_mul_cancel₀ _ hb]
  refine lt_of_le_of_lt (h c hc) ?_
  rw [EReal.coe_lt_coe_iff, hcb]
  have := neg_abs_le y; have := le_abs_self α
  linarith

lemma top_of {x : EReal} {α β : ℝ} (hβ : 0 < β)
    (h : ∀ c : ℝ, 0 ≤ c → ((α + c * β : ℝ) : EReal) ≤ x) : x = ⊤ := by
  rw [EReal.eq_top_iff_forall_lt]
  intro y
  set c := (|y| + |α| + 1) / β
  have hc : 0 ≤ c := div_nonneg (by positivity) hβ.le
  have hcb : c * β = |y| + |α| + 1 := div_mul_cancel₀ _ hβ.ne'
  refine lt_of_lt_of_le ?_ (h c hc)
  rw [EReal.coe_lt_coe_iff, hcb]
  have := le_abs_self y; have := neg_abs_le α
  linarith

lemma bot_of_ne {x : EReal} {α β : ℝ} (hβ : β ≠ 0)
    (h : ∀ c : ℝ, x ≤ ((α + c * β : ℝ) : EReal)) : x = ⊥ := by
  rcases lt_or_gt_of_ne hβ with hb | hb
  · exact bot_of hb fun c _ => h c
  · refine bot_of (α := α) (β := -β) (by linarith) fun c _ => ?_
    have := h (-c); rwa [show α + -c * β = α + c * -β by ring] at this

lemma top_of_ne {x : EReal} {α β : ℝ} (hβ : β ≠ 0)
    (h : ∀ c : ℝ, ((α + c * β : ℝ) : EReal) ≤ x) : x = ⊤ := by
  rcases lt_or_gt_of_ne hβ with hb | hb
  · refine top_of (α := α) (β := -β) (by linarith) fun c _ => ?_
    have := h (-c); rwa [show α + -c * β = α + c * -β by ring] at this
  · exact top_of hb fun c _ => h c

lemma real_of {x : EReal} (h1 : x ≠ ⊥) (h2 : x ≠ ⊤) : ∃ a : ℝ, x = a :=
  ⟨x.toReal, (EReal.coe_toReal h2 h1).symm⟩

/-! ### Lp helpers -/

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {p q : ENNReal} [hp1 : Fact (1 ≤ p)] [hpq : p.HolderConjugate q]

include hp1 hpq

lemma one_le_q : 1 ≤ q := by
  have h := (ENNReal.holderConjugate_iff.mp hpq)
  have h' : q⁻¹ ≤ 1 := h ▸ le_add_self
  rwa [ENNReal.inv_le_one] at h'

lemma int_mul (Y : Lp ℝ p P) (Z : Lp ℝ q P) : Integrable (fun ω => Y ω * Z ω) P :=
  (Lp.memLp Y).integrable_mul (Lp.memLp Z)

omit hpq in
lemma int_Y (Y : Lp ℝ p P) : Integrable Y P := (Lp.memLp Y).integrable hp1.out

lemma int_Z (Z : Lp ℝ q P) : Integrable Z P := (Lp.memLp Z).integrable (one_le_q (p := p))

lemma pair_add (Y W : Lp ℝ p P) (Z : Lp ℝ q P) :
    pairing (Y + W) Z = pairing Y Z + pairing W Z := by
  unfold pairing
  rw [← integral_add (int_mul Y Z) (int_mul W Z)]
  refine integral_congr_ae ?_
  filter_upwards [Lp.coeFn_add Y W] with ω h
  rw [h, Pi.add_apply, add_mul]

lemma pair_smul (r : ℝ) (Y : Lp ℝ p P) (Z : Lp ℝ q P) :
    pairing (r • Y) Z = r * pairing Y Z := by
  unfold pairing
  rw [← integral_const_mul]
  refine integral_congr_ae ?_
  filter_upwards [Lp.coeFn_smul r Y] with ω h
  rw [h, Pi.smul_apply, smul_eq_mul, mul_assoc]

lemma pair_zero (Z : Lp ℝ q P) : pairing (0 : Lp ℝ p P) Z = 0 := by
  have := pair_smul (0 : ℝ) (0 : Lp ℝ p P) Z
  simpa using this

lemma pair_const (c : ℝ) (Z : Lp ℝ q P) :
    pairing (Lp.const p P c) Z = c * expectation Z := by
  unfold pairing expectation
  rw [← integral_const_mul]
  refine integral_congr_ae ?_
  filter_upwards [Lp.coeFn_const (p := p) (μ := P) c] with ω h
  rw [h]; rfl

lemma pair_ind {B : Set Ω} (hB : MeasurableSet B) (Z : Lp ℝ q P) :
    pairing (indicatorConstLp p hB (measure_ne_top P B) (1 : ℝ)) Z = ∫ ω in B, Z ω ∂P := by
  unfold pairing
  rw [← integral_indicator hB]
  refine integral_congr_ae ?_
  filter_upwards [indicatorConstLp_coeFn (p := p) (hs := hB) (hμs := measure_ne_top P B)
    (c := (1 : ℝ))] with ω h
  rw [h]
  by_cases hω : ω ∈ B <;> simp [hω]

omit hpq in
lemma exp_add (Y W : Lp ℝ p P) : expectation (Y + W) = expectation Y + expectation W := by
  unfold expectation
  rw [← integral_add (int_Y Y) (int_Y W)]
  exact integral_congr_ae (Lp.coeFn_add Y W)

omit hpq in
lemma exp_smul (r : ℝ) (Y : Lp ℝ p P) : expectation (r • Y) = r * expectation Y := by
  unfold expectation
  rw [← integral_const_mul]
  exact integral_congr_ae (Lp.coeFn_smul r Y)

omit hpq in
lemma exp_ind {B : Set Ω} (hB : MeasurableSet B) :
    expectation (indicatorConstLp p hB (measure_ne_top P B) (1 : ℝ)) = P.real B := by
  unfold expectation
  rw [integral_congr_ae indicatorConstLp_coeFn, integral_indicator_const _ hB]
  simp

omit hpq in
lemma ind_nonneg {B : Set Ω} (hB : MeasurableSet B) {r : ℝ} (hr : 0 ≤ r) (Y : Lp ℝ p P) :
    ∀ᵐ ω ∂P, Y ω ≤ (Y + r • indicatorConstLp p hB (measure_ne_top P B) (1 : ℝ)) ω := by
  filter_upwards [Lp.coeFn_add Y (r • indicatorConstLp p hB (measure_ne_top P B) (1 : ℝ)),
    Lp.coeFn_smul r (indicatorConstLp p hB (measure_ne_top P B) (1 : ℝ)),
    indicatorConstLp_coeFn (p := p) (hs := hB) (hμs := measure_ne_top P B) (c := (1 : ℝ))]
    with ω h1 h2 h3
  rw [h1, Pi.add_apply, h2, Pi.smul_apply, h3, smul_eq_mul]
  have : 0 ≤ B.indicator (fun _ => (1 : ℝ)) ω := Set.indicator_nonneg (fun _ _ => zero_le_one) ω
  nlinarith

omit hp1 hpq in
/-- Pull-out: `∫ f * g = ∫ E[g|m] * f` for `f` `m`-measurable. -/
lemma pull_out {m : MeasurableSpace Ω} (hm : m ≤ mΩ)
    {f g : Ω → ℝ} (hf : StronglyMeasurable[m] f) (hfg : Integrable (f * g) P)
    (hg : Integrable g P) :
    ∫ ω, f ω * g ω ∂P = ∫ ω, P[g | m] ω * f ω ∂P := by
  have h := condExp_mul_of_stronglyMeasurable_left (μ := P) hf hfg hg
  have h' : (fun ω => P[g | m] ω * f ω) =ᵐ[P] P[f * g | m] := by
    filter_upwards [h] with ω hω
    rw [hω]; simp [mul_comm]
  rw [integral_congr_ae h', integral_condExp hm]
  rfl

/-- `∫ Y E[Z|m] = ∫ E[Y|m] Z`. -/
lemma condExp_pair (m : {m : MeasurableSpace Ω // m ≤ mΩ}) (Y : Lp ℝ p P) (Z : Lp ℝ q P) :
    ∫ ω, Y ω * condExp m.1 P (Z : Ω → ℝ) ω ∂P = ∫ ω, condExp m.1 P (Y : Ω → ℝ) ω * Z ω ∂P := by
  have hq : 1 ≤ q := one_le_q (p := p)
  have : ENNReal.HolderTriple q p 1 := ⟨by
    rw [add_comm]; exact (ENNReal.holderConjugate_iff.mp hpq).trans inv_one.symm⟩
  have hYc : MemLp (condExp m.1 P (Y : Ω → ℝ)) p P := (Lp.memLp Y).condExp hp1.out
  have hZc : MemLp (condExp m.1 P (Z : Ω → ℝ)) q P := (Lp.memLp Z).condExp hq
  have e1 := pull_out (P := P) m.2 (f := condExp m.1 P (Y : Ω → ℝ)) (g := Z)
    (stronglyMeasurable_condExp (m := m.1) (μ := P))
    (hYc.integrable_mul (Lp.memLp Z)) (int_Z (p := p) Z)
  have e2 := pull_out (P := P) m.2 (f := condExp m.1 P (Z : Ω → ℝ)) (g := Y)
    (stronglyMeasurable_condExp (m := m.1) (μ := P))
    (hZc.integrable_mul (Lp.memLp Y)) (int_Y Y)
  rw [e1]
  simp_rw [mul_comm (Y _)]
  rw [e2]
  simp_rw [mul_comm]

end X5CN

-- ===== module B

noncomputable section
set_option linter.unusedSectionVars false
open MeasureTheory RiskFunctionals.Duality

namespace X5CN

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {p q : ENNReal} [hp1 : Fact (1 ≤ p)] [hpq : p.HolderConjugate q]

omit hp1 hpq in
lemma pos_set (Z : Ω → ℝ) (hZ : AEStronglyMeasurable Z P) (g : ℝ → ℝ) (hg : Continuous g)
    (hgi : Integrable (fun ω => g (Z ω)) P) (hpos : P {ω | 0 < g (Z ω)} ≠ 0) :
    ∃ B : Set Ω, MeasurableSet B ∧ 0 < ∫ ω in B, g (Z ω) ∂P := by
  set Zm := hZ.mk Z
  have hZm : Z =ᵐ[P] Zm := hZ.ae_eq_mk
  set B := {ω | 0 < g (Zm ω)}
  have hB : MeasurableSet B :=
    measurableSet_lt measurable_const (hg.measurable.comp hZ.stronglyMeasurable_mk.measurable)
  have hPB : P B = P {ω | 0 < g (Z ω)} := by
    refine measure_congr ?_
    filter_upwards [hZm] with ω hω
    change (0 < g (Zm ω)) = (0 < g (Z ω))
    rw [hω]
  refine ⟨B, hB, ?_⟩
  have e : ∫ ω in B, g (Z ω) ∂P = ∫ ω in B, g (Zm ω) ∂P :=
    integral_congr_ae (ae_restrict_of_ae (hZm.fun_comp g))
  rw [e, setIntegral_pos_iff_support_of_nonneg_ae]
  · have : Function.support (fun ω => g (Zm ω)) ∩ B = B := by
      ext ω
      simp only [Set.mem_inter_iff, Function.mem_support, and_iff_right_iff_imp]
      intro h; exact ne_of_gt h
    rw [this, hPB]; exact pos_iff_ne_zero.mpr hpos
  · exact (ae_restrict_mem hB).mono fun ω h => le_of_lt h
  · exact ((hgi.congr (hZm.fun_comp g)).integrableOn)

/-- The concave half of the statement. -/
lemma concave_half (A : Lp ℝ p P → EReal) (hpr : IsProperConcave A) :
      (TranslationEquivariant P A → ∀ Z, ⊥ < concaveConj q A Z → expectation Z = 1) ∧
      (PositivelyHomogeneous A → ∀ Z, concaveConj q A Z = 0 ∨ concaveConj q A Z = ⊥) ∧
      (PointwiseMonotone P A → ∀ Z : Lp ℝ q P, 0 < P {ω | Z ω < 0} → concaveConj q A Z = ⊥) ∧
      (VersionIndependent P A →
        (∀ m : {m : MeasurableSpace Ω // m ≤ mΩ}, ∀ Y Y' : Lp ℝ p P,
          (Y' : Ω → ℝ) =ᵐ[P] condExp m.1 P (Y : Ω → ℝ) → A Y ≤ A Y') →
        (∀ m : {m : MeasurableSpace Ω // m ≤ mΩ}, ∀ Z Z' : Lp ℝ q P,
          (Z' : Ω → ℝ) =ᵐ[P] condExp m.1 P (Z : Ω → ℝ) →
            concaveConj q A Z ≤ concaveConj q A Z')) := by
  obtain ⟨htop, Y0, hY0⟩ := hpr
  obtain ⟨a, ha⟩ := real_of hY0 (htop Y0)
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- (i)
    intro hTE Z hZ
    by_contra hne
    have hb : concaveConj q A Z = ⊥ := by
      refine bot_of_ne (α := pairing Y0 Z - a) (β := expectation Z - 1) (sub_ne_zero.mpr hne)
        fun c => ?_
      refine (iInf_le _ (Y0 + Lp.const p P c)).trans (le_of_eq ?_)
      rw [hTE, ha, pair_add, pair_const, ← EReal.coe_add, ← EReal.coe_sub]
      congr 1; ring
    rw [hb] at hZ; exact lt_irrefl _ hZ
  · -- (ii)
    intro hPH Z
    have h0 : A 0 = 0 := by
      have := hPH 0 0 le_rfl
      rwa [zero_smul, EReal.coe_zero, zero_mul] at this
    have hle : concaveConj q A Z ≤ 0 := by
      refine (iInf_le _ (0 : Lp ℝ p P)).trans (le_of_eq ?_)
      rw [h0, pair_zero]; simp
    by_cases hz : concaveConj q A Z = 0
    · exact Or.inl hz
    right
    have hlt : concaveConj q A Z < 0 := lt_of_le_of_ne hle hz
    obtain ⟨Y, hY⟩ := iInf_lt_iff.mp hlt
    have hYb : A Y ≠ ⊥ := by
      intro h; rw [h, EReal.coe_sub_bot] at hY; exact absurd hY (not_lt.mpr le_top)
    obtain ⟨b, hb⟩ := real_of hYb (htop Y)
    rw [hb, ← EReal.coe_sub] at hY
    have hY' : pairing Y Z - b < 0 := by exact_mod_cast hY
    refine bot_of (α := 0) hY' fun c hc => ?_
    refine (iInf_le _ (c • Y)).trans (le_of_eq ?_)
    rw [hPH Y c hc, hb, pair_smul, ← EReal.coe_mul, ← EReal.coe_sub]
    congr 1; ring
  · -- (iii)
    intro hPM Z hZ
    obtain ⟨B, hB, hβ⟩ := pos_set (Z : Ω → ℝ) (Lp.aestronglyMeasurable Z) (fun x => -x)
      continuous_neg (int_Z (p := p) Z).neg (by
        have : {ω | 0 < -(Z : Ω → ℝ) ω} = {ω | Z ω < 0} := by ext ω; simp
        rw [this]; exact hZ.ne')
    rw [integral_neg] at hβ
    refine bot_of (α := pairing Y0 Z - a) (β := ∫ ω in B, Z ω ∂P) (by linarith) fun c hc => ?_
    set W := c • indicatorConstLp p hB (measure_ne_top P B) (1 : ℝ)
    have hmono : A Y0 ≤ A (Y0 + W) := hPM _ _ (ind_nonneg hB hc Y0)
    refine (iInf_le _ (Y0 + W)).trans ((EReal.sub_le_sub le_rfl hmono).trans (le_of_eq ?_))
    rw [ha, pair_add, pair_smul, pair_ind, ← EReal.coe_sub]
    congr 1; ring
  · -- (iv)
    intro _ hCE m Z Z' hZ'
    refine le_iInf fun Y => ?_
    set Y' : Lp ℝ p P := ((Lp.memLp Y).condExp (m := m.1) hp1.out).toLp _
    have hY' : (Y' : Ω → ℝ) =ᵐ[P] condExp m.1 P (Y : Ω → ℝ) := MemLp.coeFn_toLp _
    have hA := hCE m Y Y' hY'
    have hpair : pairing Y' Z = pairing Y Z' := by
      unfold pairing
      have e1 : ∫ ω, Y' ω * Z ω ∂P = ∫ ω, condExp m.1 P (Y : Ω → ℝ) ω * Z ω ∂P := by
        refine integral_congr_ae ?_
        filter_upwards [hY'] with ω h; rw [h]
      have e2 : ∫ ω, Y ω * Z' ω ∂P = ∫ ω, Y ω * condExp m.1 P (Z : Ω → ℝ) ω ∂P := by
        refine integral_congr_ae ?_
        filter_upwards [hZ'] with ω h; rw [h]
      rw [e1, e2]
      exact (condExp_pair (p := p) (q := q) m Y Z).symm
    refine (iInf_le _ Y').trans ?_
    rw [hpair]
    exact EReal.sub_le_sub le_rfl hA

end X5CN

-- ===== module C

noncomputable section
set_option linter.unusedSectionVars false
open MeasureTheory RiskFunctionals.Duality

namespace X5CN

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {p q : ENNReal} [hp1 : Fact (1 ≤ p)] [hpq : p.HolderConjugate q]

lemma ereal_aux {x y : ℝ} {z : EReal} (h : (x : EReal) ≤ (y : EReal) - z) :
    z ≤ ((y - x : ℝ) : EReal) := by
  induction z using EReal.rec with
  | bot => exact bot_le
  | top => rw [EReal.sub_top] at h; exact absurd h (not_le.mpr (EReal.bot_lt_coe x))
  | coe z =>
    rw [← EReal.coe_sub, EReal.coe_le_coe_iff] at h
    exact EReal.coe_le_coe_iff.mpr (by linarith)

/-- The convex half of the statement. -/
lemma convex_half (D : Lp ℝ p P → EReal) (hpr : IsProperConvex D) :
      (TranslationInvariant P D → ∀ Z, convexConj q D Z < ⊤ → expectation Z = 0) ∧
      (PositivelyHomogeneous D → ∀ Z, convexConj q D Z = 0 ∨ convexConj q D Z = ⊤) ∧
      (MeanMinusMonotone P D → ∀ Z : Lp ℝ q P, 0 < P {ω | 1 < Z ω} →
        convexConj q D Z = ⊤) := by
  obtain ⟨hbot, Y0, hY0⟩ := hpr
  obtain ⟨d, hd⟩ := real_of (hbot Y0) hY0
  refine ⟨?_, ?_, ?_⟩
  · -- (v)
    intro hTI Z hZ
    by_contra hne
    have ht : convexConj q D Z = ⊤ := by
      refine top_of_ne (α := pairing Y0 Z - d) (β := expectation Z) hne fun c => ?_
      refine le_trans (le_of_eq ?_) (le_iSup _ (Y0 + Lp.const p P c))
      rw [hTI, hd, pair_add, pair_const, ← EReal.coe_sub]
      congr 1; ring
    rw [ht] at hZ; exact lt_irrefl _ hZ
  · -- (vi)
    intro hPH Z
    have h0 : D 0 = 0 := by
      have := hPH 0 0 le_rfl
      rwa [zero_smul, EReal.coe_zero, zero_mul] at this
    have hle : 0 ≤ convexConj q D Z := by
      refine le_trans (le_of_eq ?_) (le_iSup _ (0 : Lp ℝ p P))
      rw [h0, pair_zero]; simp
    by_cases hz : convexConj q D Z = 0
    · exact Or.inl hz
    right
    have hlt : 0 < convexConj q D Z := lt_of_le_of_ne hle (Ne.symm hz)
    obtain ⟨Y, hY⟩ := lt_iSup_iff.mp hlt
    have hYt : D Y ≠ ⊤ := by
      intro h; rw [h, EReal.sub_top] at hY; exact absurd hY (not_lt.mpr bot_le)
    obtain ⟨b, hb⟩ := real_of (hbot Y) hYt
    rw [hb, ← EReal.coe_sub] at hY
    have hY' : 0 < pairing Y Z - b := by exact_mod_cast hY
    refine top_of (α := 0) hY' fun c hc => ?_
    refine le_trans (le_of_eq ?_) (le_iSup _ (c • Y))
    rw [hPH Y c hc, hb, pair_smul, ← EReal.coe_mul, ← EReal.coe_sub]
    congr 1; ring
  · -- (vii)
    intro hMM Z hZ
    obtain ⟨B, hB, hβ⟩ := pos_set (Z : Ω → ℝ) (Lp.aestronglyMeasurable Z) (fun x => x - 1)
      (continuous_id.sub continuous_const) ((int_Z (p := p) Z).sub (integrable_const 1)) (by
        have : {ω | 0 < (Z : Ω → ℝ) ω - 1} = {ω | 1 < Z ω} := by ext ω; simp
        rw [this]; exact hZ.ne')
    rw [integral_sub (int_Z (p := p) Z).integrableOn (integrable_const 1).integrableOn,
      setIntegral_const, smul_eq_mul, mul_one] at hβ
    refine top_of (α := pairing Y0 Z - d) (β := (∫ ω in B, Z ω ∂P) - P.real B) hβ
      fun c hc => ?_
    set W := c • indicatorConstLp p hB (measure_ne_top P B) (1 : ℝ)
    have hmono := hMM _ _ (ind_nonneg hB hc Y0)
    rw [hd, exp_add, exp_smul, exp_ind, ← EReal.coe_sub] at hmono
    have hDle := ereal_aux hmono
    refine le_trans ?_ (le_iSup _ (Y0 + W))
    refine le_trans (le_of_eq ?_) (EReal.sub_le_sub le_rfl hDle)
    rw [pair_add, pair_smul, pair_ind, ← EReal.coe_sub]
    congr 1; ring

end X5CN


end

open MeasureTheory ProbabilityTheory RiskFunctionals.Duality

theorem solution {Ω : Type*} [m0 : MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (hP : IsNonAtomic P) (p q : ENNReal) [Fact (1 ≤ p)] (hp : p ≠ ⊤)
    [p.HolderConjugate q] :
    (∀ A : Lp ℝ p P → EReal, ConcaveFunctional A → IsProperConcave A →
      (∀ Y, A Y = ⨅ Z : Lp ℝ q P, ((pairing Y Z : ℝ) : EReal) - concaveConj q A Z) →
      (TranslationEquivariant P A → ∀ Z, ⊥ < concaveConj q A Z → expectation Z = 1) ∧
      (PositivelyHomogeneous A → ∀ Z, concaveConj q A Z = 0 ∨ concaveConj q A Z = ⊥) ∧
      (PointwiseMonotone P A → ∀ Z : Lp ℝ q P, 0 < P {ω | Z ω < 0} → concaveConj q A Z = ⊥) ∧
      (VersionIndependent P A →
        (∀ m : {m : MeasurableSpace Ω // m ≤ m0}, ∀ Y Y' : Lp ℝ p P,
          (Y' : Ω → ℝ) =ᵐ[P] condExp m.1 P (Y : Ω → ℝ) → A Y ≤ A Y') →
        (∀ m : {m : MeasurableSpace Ω // m ≤ m0}, ∀ Z Z' : Lp ℝ q P,
          (Z' : Ω → ℝ) =ᵐ[P] condExp m.1 P (Z : Ω → ℝ) →
            concaveConj q A Z ≤ concaveConj q A Z'))) ∧
    (∀ D : Lp ℝ p P → EReal, ConvexFunctional D → IsProperConvex D →
      (∀ Y, D Y = ⨆ Z : Lp ℝ q P, ((pairing Y Z : ℝ) : EReal) - convexConj q D Z) →
      (TranslationInvariant P D → ∀ Z, convexConj q D Z < ⊤ → expectation Z = 0) ∧
      (PositivelyHomogeneous D → ∀ Z, convexConj q D Z = 0 ∨ convexConj q D Z = ⊤) ∧
      (MeanMinusMonotone P D → ∀ Z : Lp ℝ q P, 0 < P {ω | 1 < Z ω} →
        convexConj q D Z = ⊤)) :=
  ⟨fun A _ hpr _ => X5CN.concave_half A hpr, fun D _ hpr _ => X5CN.convex_half D hpr⟩

