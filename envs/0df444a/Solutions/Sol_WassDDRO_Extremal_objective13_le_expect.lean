-- Prove2me | solution 1 for WassDDRO.Extremal.objective13_le_expect
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-07T10:46:15.681062+00:00
-- url     : https://prove2.me/submissions/611d8eb8-69fd-462e-87cb-1faea0105298

import Definitions.Def_WassDDRO_Extremal_Setting
import Definitions.Def_WassDDRO_Reduction_Setting
set_option autoImplicit false
section
set_option autoImplicit false
namespace WassExtremalCodex
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {K N : ℕ}

def toReductionAssumption (Ξ : Set E) (ℓ : Fin K → E → EReal)
    (h : WassDDRO.Extremal.Assumption41 Ξ ℓ) : WassDDRO.Reduction.Assumption41 Ξ ℓ :=
  ⟨h.convex, h.closed, h.ne_top, h.convex_epigraph, h.lsc, h.not_bot_on⟩

theorem maxLoss_eq (ℓ : Fin K → E → EReal) :
    WassDDRO.Extremal.maxLoss ℓ = WassDDRO.Reduction.maxLoss ℓ := rfl

theorem program12f_eq (ε : ℝ) (Ξ : Set E) (ξhat : Fin N → E) (ℓ : Fin K → E → EReal) :
    WassDDRO.Extremal.program12fValue ε Ξ ξhat ℓ = WassDDRO.Reduction.program12fValue ε Ξ ξhat ℓ := rfl

theorem worstCase_eq (ε : ℝ) (Ξ : Set E) (ξhat : Fin N → E) (L : E → EReal) :
    WassDDRO.Extremal.worstCaseExpectation ε Ξ ξhat L = WassDDRO.Reduction.worstCaseExpectation ε Ξ ξhat L := rfl
end WassExtremalCodex

end

section
set_option autoImplicit false
open MeasureTheory
namespace WassExtremalCodex

theorem weighted_rows_probability {Z : Type*} [MeasurableSpace Z] {N K : ℕ}
    (hN : 0 < N) (a : Fin N → Fin K → ℝ) (x : Fin N → Fin K → Z)
    (ha : ∀ i k, 0 ≤ a i k) (hs : ∀ i, ∑ k, a i k = 1) :
    IsProbabilityMeasure ((N : ENNReal)⁻¹ • ∑ i, ∑ k, ENNReal.ofReal (a i k) • Measure.dirac (x i k)) := by
  have hr : ∀ i, (∑ k, ENNReal.ofReal (a i k)) = 1 := by
    intro i
    rw [←ENNReal.ofReal_sum_of_nonneg (fun k _ => ha i k), hs i]
    simp
  constructor
  simp only [Measure.smul_apply, Measure.finsetSum_apply, Measure.dirac_apply_of_mem (Set.mem_univ _),
    smul_eq_mul, mul_one, hr, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  exact ENNReal.inv_mul_cancel (by exact_mod_cast hN.ne') (ENNReal.natCast_ne_top N)

theorem weighted_rows_ae_support {Z : Type*} [MeasurableSpace Z] [MeasurableSingletonClass Z]
    {N K : ℕ} (a : Fin N → Fin K → ℝ) (x : Fin N → Fin K → Z) (S : Set Z)
    (hx : ∀ i k, a i k ≠ 0 → x i k ∈ S) :
    ∀ᵐ z ∂((N : ENNReal)⁻¹ • ∑ i, ∑ k, ENNReal.ofReal (a i k) • Measure.dirac (x i k)), z∈S := by
  apply Measure.ae_smul_measure
  rw [ae_finsetSum_measure_iff]
  intro i hi
  rw [ae_finsetSum_measure_iff]
  intro k hk
  by_cases hz : a i k = 0
  · simp [hz]
  · apply Measure.ae_smul_measure
    rw [ae_dirac_eq]
    exact hx i k hz

theorem discreteQ_probability {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] {N K : ℕ}
    (hN : 0 < N) (Ξ : Set E) (ξhat : Fin N → E) (ε : ℝ)
    (α : Fin N → Fin K → ℝ) (q : Fin N → Fin K → E)
    (h : WassDDRO.Extremal.Feasible13 ε Ξ ξhat α q) :
    IsProbabilityMeasure (WassDDRO.Extremal.discreteQ ξhat α q) :=
  weighted_rows_probability hN α (fun i k => WassDDRO.Extremal.atom13 (ξhat i) (α i k) (q i k)) h.2.2.1 h.2.1

theorem discreteQ_ae_support {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] {N K : ℕ}
    (Ξ : Set E) (ξhat : Fin N → E) (ε : ℝ)
    (α : Fin N → Fin K → ℝ) (q : Fin N → Fin K → E)
    (h : WassDDRO.Extremal.Feasible13 ε Ξ ξhat α q) :
    ∀ᵐ x ∂WassDDRO.Extremal.discreteQ ξhat α q, x∈Ξ :=
  weighted_rows_ae_support α (fun i k => WassDDRO.Extremal.atom13 (ξhat i) (α i k) (q i k)) Ξ
    (fun i k => (h.2.2.2 i k).2)
end WassExtremalCodex

end

section
set_option autoImplicit false
open MeasureTheory
namespace WassExtremalCodex

theorem weighted_rows_map {Z Y : Type*} [MeasurableSpace Z] [MeasurableSpace Y] {N K : ℕ}
    (a : Fin N → Fin K → ℝ) (x : Fin N → Fin K → Z) (f : Z → Y) (hf : Measurable f) :
    ((N : ENNReal)⁻¹ • ∑ i, ∑ k, ENNReal.ofReal (a i k) • Measure.dirac (x i k)).map f =
      (N : ENNReal)⁻¹ • ∑ i, ∑ k, ENNReal.ofReal (a i k) • Measure.dirac (f (x i k)) := by
  simp only [Measure.map_smul, Measure.map_finset_sum' hf.aemeasurable, Measure.map_dirac' hf]

theorem weighted_rows_lintegral {Z : Type*} [MeasurableSpace Z] [MeasurableSingletonClass Z]
    {N K : ℕ} (a : Fin N → Fin K → ℝ) (x : Fin N → Fin K → Z) (f : Z → ENNReal) :
    (∫⁻ z, f z ∂((N : ENNReal)⁻¹ • ∑ i, ∑ k, ENNReal.ofReal (a i k) • Measure.dirac (x i k))) =
      (N : ENNReal)⁻¹ * ∑ i, ∑ k, ENNReal.ofReal (a i k) * f (x i k) := by
  simp only [lintegral_smul_measure, lintegral_finsetSum_measure, lintegral_dirac, smul_eq_mul]

theorem atom13_weighted_cost {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (sample q : E) (α : ℝ) (hα : 0 ≤ α) (hz : α = 0 → q = 0) :
    α * ‖WassDDRO.Extremal.atom13 sample α q-sample‖ = ‖q‖ := by
  by_cases h : α=0
  · simp [h,hz h]
  · have hp : 0 < α := lt_of_le_of_ne hα (Ne.symm h)
    have he : WassDDRO.Extremal.atom13 sample α q-sample = -(α⁻¹ • q) := by
      unfold WassDDRO.Extremal.atom13
      abel
    rw [he,norm_neg,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hp),←mul_assoc,mul_inv_cancel₀ h,one_mul]

noncomputable def coupling13 {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] {N K : ℕ}
    (ξhat : Fin N → E) (α : Fin N → Fin K → ℝ) (q : Fin N → Fin K → E) : Measure (E×E) :=
  (N : ENNReal)⁻¹ • ∑ i, ∑ k, ENNReal.ofReal (α i k) •
    Measure.dirac (WassDDRO.Extremal.atom13 (ξhat i) (α i k) (q i k),ξhat i)

theorem coupling13_first {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] {N K : ℕ}
    (ξhat : Fin N → E) (α : Fin N → Fin K → ℝ) (q : Fin N → Fin K → E) :
    (coupling13 ξhat α q).map Prod.fst = WassDDRO.Extremal.discreteQ ξhat α q :=
  weighted_rows_map α _ Prod.fst measurable_fst

theorem coupling13_second {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] {N K : ℕ}
    (ξhat : Fin N → E) (α : Fin N → Fin K → ℝ) (q : Fin N → Fin K → E)
    (hα : ∀ i k, 0 ≤ α i k) (hs : ∀ i, ∑ k, α i k=1) :
    (coupling13 ξhat α q).map Prod.snd = WassersteinDRO.Duality.empiricalDistribution ξhat := by
  rw [coupling13,weighted_rows_map α _ Prod.snd measurable_snd]
  have hr : ∀ i, (∑ k, ENNReal.ofReal (α i k))=1 := by
    intro i
    rw [←ENNReal.ofReal_sum_of_nonneg (fun k _ => hα i k),hs i]
    simp
  simp only [←Finset.sum_smul,hr,one_smul]
  rfl
end WassExtremalCodex

end

section
set_option autoImplicit false
open MeasureTheory
namespace WassExtremalCodex

theorem weighted_rows_integrable {Z : Type*} [MeasurableSpace Z] [MeasurableSingletonClass Z]
    {N K : ℕ} (hN : 0 < N) (a : Fin N → Fin K → ℝ) (x : Fin N → Fin K → Z) (f : Z → ℝ) :
    Integrable f ((N : ENNReal)⁻¹ • ∑ i, ∑ k, ENNReal.ofReal (a i k) • Measure.dirac (x i k)) := by
  apply Integrable.smul_measure
  · apply integrable_finsetSum_measure.mpr
    intro i hi
    apply integrable_finsetSum_measure.mpr
    intro k hk
    exact (integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top
  · exact ENNReal.inv_ne_top.mpr (by exact_mod_cast hN.ne')

theorem weighted_rows_integral {Z : Type*} [MeasurableSpace Z] [MeasurableSingletonClass Z]
    {N K : ℕ} (a : Fin N → Fin K → ℝ) (x : Fin N → Fin K → Z) (f : Z → ℝ)
    (ha : ∀ i k, 0 ≤ a i k) :
    (∫ z, f z ∂((N : ENNReal)⁻¹ • ∑ i, ∑ k, ENNReal.ofReal (a i k) • Measure.dirac (x i k))) =
      (1/(N : ℝ)) * ∑ i, ∑ k, a i k * f (x i k) := by
  have hint : ∀ i k, Integrable f (ENNReal.ofReal (a i k) • Measure.dirac (x i k)) :=
    fun i k => (integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top
  have hr : ∀ i, (∫ z, f z ∂(∑ k, ENNReal.ofReal (a i k) • Measure.dirac (x i k))) =
      ∑ k, a i k*f (x i k) := by
    intro i
    rw [integral_finsetSum_measure (fun k _ => hint i k)]
    apply Finset.sum_congr rfl
    intro k hk
    rw [integral_smul_measure,integral_dirac,ENNReal.toReal_ofReal (ha i k)]
    rfl
  rw [integral_smul_measure,integral_finsetSum_measure (fun i _ =>
    integrable_finsetSum_measure.mpr (fun k _ => hint i k))]
  simp only [hr,ENNReal.toReal_inv,ENNReal.toReal_natCast,smul_eq_mul,one_div]
end WassExtremalCodex

end

section
set_option autoImplicit false
open MeasureTheory
namespace WassReductionCodex
open DupacovaWets.Consistency

lemma expect_mono {Z : Type*} [MeasurableSpace Z] (Q : Measure Z)
    (f g : Z → EReal) (hfg : f ≤ᵐ[Q] g) :
    expect Q f ≤ expect Q g := by
  have hpos : (∫⁻ z, (f z).toENNReal ∂Q) ≤ ∫⁻ z, (g z).toENNReal ∂Q :=
    lintegral_mono_ae (hfg.mono fun z hz => EReal.toENNReal_le_toENNReal hz)
  have hneg : (∫⁻ z, (-g z).toENNReal ∂Q) ≤ ∫⁻ z, (-f z).toENNReal ∂Q :=
    lintegral_mono_ae (hfg.mono fun z hz => EReal.toENNReal_le_toENNReal (EReal.neg_le_neg_iff.mpr hz))
  unfold expect
  by_cases hgtop : (∫⁻ z, (g z).toENNReal ∂Q) = ⊤
  · rw [if_pos hgtop]
    exact le_top
  · have hftop : (∫⁻ z, (f z).toENNReal ∂Q) ≠ ⊤ :=
      (lt_of_le_of_lt hpos (lt_top_iff_ne_top.mpr hgtop)).ne
    rw [if_neg hgtop, if_neg hftop]
    exact EReal.sub_le_sub (EReal.coe_ennreal_le_coe_ennreal_iff.mpr hpos)
      (EReal.coe_ennreal_le_coe_ennreal_iff.mpr hneg)

end WassReductionCodex

end

section
set_option autoImplicit false
open MeasureTheory
namespace WassReductionCodex
open DupacovaWets.Consistency
lemma expect_eq_integral {E : Type*} [MeasurableSpace E]
    (Q : Measure E) (l : E → ℝ) (hl : Integrable l Q) :
    expect Q (fun x => (l x : EReal)) = (∫ x, l x ∂Q : ℝ) := by
  have hp : (∫⁻ x, ENNReal.ofReal (l x) ∂Q) ≠ ⊤ :=
    ((lintegral_ofReal_le_lintegral_enorm l).trans_lt hl.2).ne
  have hn : (∫⁻ x, ENNReal.ofReal (-l x) ∂Q) ≠ ⊤ :=
    ((lintegral_ofReal_le_lintegral_enorm (fun x => -l x)).trans_lt hl.neg.2).ne
  unfold expect
  rw [if_neg (show (∫⁻ x, ((l x : EReal)).toENNReal ∂Q) ≠ ⊤ from hp)]
  simp only [EReal.real_coe_toENNReal, ← EReal.coe_neg]
  rw [ ← EReal.coe_ennreal_toReal hp, ← EReal.coe_ennreal_toReal hn,
    ← EReal.coe_sub, integral_eq_lintegral_pos_part_sub_lintegral_neg_part hl]


end WassReductionCodex

end

section
set_option autoImplicit false
open MeasureTheory
namespace WassExtremalCodex
open DupacovaWets.Consistency

theorem weighted_rows_expect_of_finite {Z : Type*} [MeasurableSpace Z] [MeasurableSingletonClass Z]
    {N K : ℕ} (hN : 0 < N) (a : Fin N → Fin K → ℝ) (x : Fin N → Fin K → Z)
    (L : Z → EReal) (ha : ∀ i k, 0 ≤ a i k) (htop : ∀ i k, L (x i k)≠⊤)
    (hbot : ∀ i k, a i k≠0 → L (x i k)≠⊥) :
    expect ((N : ENNReal)⁻¹ • ∑ i, ∑ k, ENNReal.ofReal (a i k) • Measure.dirac (x i k)) L =
      ((1/(N : ℝ) : ℝ) : EReal) * ∑ i, ∑ k, (a i k : EReal)*L (x i k) := by
  let μ : Measure Z := (N : ENNReal)⁻¹ • ∑ i, ∑ k, ENNReal.ofReal (a i k) • Measure.dirac (x i k)
  let f : Z → ℝ := fun z => (L z).toReal
  have hae : L =ᵐ[μ] (fun z => (f z : EReal)) := by
    apply weighted_rows_ae_support a x {z | L z=(f z : EReal)}
    intro i k h
    exact (EReal.coe_toReal (htop i k) (hbot i k h)).symm
  have he : expect μ L=expect μ (fun z => (f z : EReal)) :=
    le_antisymm (WassReductionCodex.expect_mono _ _ _ (hae.mono fun z hz => hz.le))
      (WassReductionCodex.expect_mono _ _ _ (hae.mono fun z hz => hz.ge))
  rw [he,WassReductionCodex.expect_eq_integral μ f (weighted_rows_integrable hN a x f),
    weighted_rows_integral a x f ha]
  have hc : ∀ i k, (a i k : EReal)*L (x i k)=((a i k*f (x i k) : ℝ) : EReal) := by
    intro i k
    by_cases h : a i k=0
    · simp [h]
    · rw [←EReal.coe_toReal (htop i k) (hbot i k h),←EReal.coe_mul]
  simp_rw [hc]
  let toE : ℝ →+ EReal := ⟨⟨Real.toEReal,EReal.coe_zero⟩,EReal.coe_add⟩
  have hs : (∑ i, ∑ k, ((a i k*f (x i k) : ℝ) : EReal)) =
      ((∑ i, ∑ k, a i k*f (x i k) : ℝ) : EReal) := by
    calc
      _ = ∑ i, ((∑ k, a i k*f (x i k) : ℝ) : EReal) :=
        Finset.sum_congr rfl (fun i _ => (map_sum toE _ _).symm)
      _ = _ := (map_sum toE _ _).symm
  rw [hs,←EReal.coe_mul]

theorem weighted_rows_expect_of_ne_top {Z : Type*} [MeasurableSpace Z] [MeasurableSingletonClass Z]
    {N K : ℕ} (hN : 0 < N) (a : Fin N → Fin K → ℝ) (x : Fin N → Fin K → Z)
    (L : Z → EReal) (ha : ∀ i k, 0 ≤ a i k) (htop : ∀ i k, L (x i k)≠⊤) :
    expect ((N : ENNReal)⁻¹ • ∑ i, ∑ k, ENNReal.ofReal (a i k) • Measure.dirac (x i k)) L =
      ((1/(N : ℝ) : ℝ) : EReal) * ∑ i, ∑ k, (a i k : EReal)*L (x i k) := by
  by_cases hb : ∃ i k, a i k≠0 ∧ L (x i k)=⊥
  · obtain ⟨i,k,hak,hL⟩ := hb
    have hap : 0 < a i k := lt_of_le_of_ne (ha i k) (Ne.symm hak)
    have haz : ENNReal.ofReal (a i k)≠0 := (ENNReal.ofReal_pos.mpr hap).ne'
    have hpos : (∫⁻ z, (L z).toENNReal ∂((N : ENNReal)⁻¹ •
        ∑ i, ∑ k, ENNReal.ofReal (a i k) • Measure.dirac (x i k)))≠⊤ := by
      rw [weighted_rows_lintegral]
      apply ENNReal.mul_ne_top (ENNReal.inv_ne_top.mpr (by exact_mod_cast hN.ne'))
      apply ENNReal.sum_ne_top.mpr
      intro j hj
      apply ENNReal.sum_ne_top.mpr
      intro l hl
      exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (EReal.toENNReal_ne_top_iff.mpr (htop j l))
    have hneg : (∫⁻ z, (-L z).toENNReal ∂((N : ENNReal)⁻¹ •
        ∑ i, ∑ k, ENNReal.ofReal (a i k) • Measure.dirac (x i k)))=⊤ := by
      rw [weighted_rows_lintegral]
      have hk : ENNReal.ofReal (a i k)*(-L (x i k)).toENNReal=⊤ := by
        simp [hL,haz]
      have hs : (∑ j, ∑ l, ENNReal.ofReal (a j l)*(-L (x j l)).toENNReal)=⊤ := by
        apply top_le_iff.mp
        rw [←hk]
        exact (Finset.single_le_sum (f := fun l : Fin K => ENNReal.ofReal (a i l)*(-L (x i l)).toENNReal)
          (fun l _ => bot_le) (Finset.mem_univ k)).trans
          (Finset.single_le_sum (f := fun j : Fin N => ∑ l, ENNReal.ofReal (a j l)*(-L (x j l)).toENNReal)
            (fun j _ => bot_le) (Finset.mem_univ i))
      rw [hs,ENNReal.mul_top]
      simp
    have hterm : (a i k : EReal)*L (x i k)=⊥ := by
      rw [hL]
      exact EReal.mul_bot_of_pos (by exact_mod_cast hap)
    have hs : (∑ j, ∑ l, (a j l : EReal)*L (x j l))=⊥ := by
      have hi : (∑ l, (a i l : EReal)*L (x i l))=⊥ := by
        rw [←Finset.add_sum_erase _ _ (Finset.mem_univ k),hterm,EReal.bot_add]
      rw [←Finset.add_sum_erase _ _ (Finset.mem_univ i),hi,EReal.bot_add]
    rw [expect,if_neg hpos,hneg,EReal.coe_ennreal_top,EReal.sub_top,hs]
    symm
    exact EReal.mul_bot_of_pos (by exact_mod_cast (one_div_pos.mpr (Nat.cast_pos.mpr hN)))
  · apply weighted_rows_expect_of_finite hN a x L ha htop
    intro i k hk hL
    exact hb ⟨i,k,hk,hL⟩
end WassExtremalCodex

end

section
set_option autoImplicit false
open MeasureTheory
namespace WassExtremalCodex
open WassDDRO.Extremal DupacovaWets.Consistency

theorem term13_eq_weight {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (L : E → EReal) (sample q : E) (α : ℝ) :
    term13 L sample α q=(α : EReal)*L (atom13 sample α q) := by
  by_cases h : α=0 <;> simp [term13,h]

theorem discreteQ_expect_eq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] {N K : ℕ}
    (hN : 0 < N) (ξhat : Fin N → E) (α : Fin N → Fin K → ℝ) (q : Fin N → Fin K → E)
    (L : E → EReal) (ha : ∀ i k, 0 ≤ α i k) (htop : ∀ i k, L (atom13 (ξhat i) (α i k) (q i k))≠⊤) :
    expect (discreteQ ξhat α q) L =
      ((1/(N : ℝ) : ℝ) : EReal)*∑ i, ∑ k, term13 L (ξhat i) (α i k) (q i k) := by
  simp_rw [term13_eq_weight]
  exact weighted_rows_expect_of_ne_top hN α _ L ha htop

theorem objective13_le_expect_full {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] {N K : ℕ}
    (hN : 0 < N) (Ξ : Set E) (ℓ : Fin K → E → EReal) (hne_top : ∀ k x, ℓ k x≠⊤)
    (ξhat : Fin N → E) (ε : ℝ) (α : Fin N → Fin K → ℝ) (q : Fin N → Fin K → E)
    (h : Feasible13 ε Ξ ξhat α q) :
    expect (discreteQ ξhat α q) (maxLoss ℓ) =
      ((1/(N : ℝ) : ℝ) : EReal)*∑ i, ∑ k, term13 (maxLoss ℓ) (ξhat i) (α i k) (q i k) ∧
    objective13 ξhat ℓ α q ≤ expect (discreteQ ξhat α q) (maxLoss ℓ) := by
  have he := discreteQ_expect_eq hN ξhat α q (maxLoss ℓ) h.2.2.1
    (fun i k => iSup_ne_top (fun l => hne_top l (atom13 (ξhat i) (α i k) (q i k))))
  refine ⟨he,?_⟩
  rw [he]
  unfold objective13
  apply mul_le_mul_of_nonneg_left _ (by exact_mod_cast (one_div_nonneg.mpr (Nat.cast_nonneg N)))
  apply Finset.sum_le_sum
  intro i hi
  apply Finset.sum_le_sum
  intro k hk
  simp only [term13_eq_weight]
  exact mul_le_mul_of_nonneg_left (le_iSup (fun l => ℓ l (atom13 (ξhat i) (α i k) (q i k))) k)
    (by exact_mod_cast h.2.2.1 i k)
end WassExtremalCodex

end

set_option autoImplicit false
open WassDDRO.Extremal
theorem solution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {K N : ℕ} (hN : 0 < N) (Ξ : Set E) (ℓ : Fin K → E → EReal)
    (hmeas : ∀ k, Measurable (ℓ k)) (hne_top : ∀ k ξ, ℓ k ξ ≠ ⊤)
    (ξhat : Fin N → E) (ε : ℝ)
    (α : Fin N → Fin K → ℝ) (q : Fin N → Fin K → E) (h : Feasible13 ε Ξ ξhat α q) :
    DupacovaWets.Consistency.expect (discreteQ ξhat α q) (maxLoss ℓ) =
        ((1 / (N : ℝ) : ℝ) : EReal) * ∑ i, ∑ k, term13 (maxLoss ℓ) (ξhat i) (α i k) (q i k) ∧
      objective13 ξhat ℓ α q ≤
        DupacovaWets.Consistency.expect (discreteQ ξhat α q) (maxLoss ℓ) := by
  exact WassExtremalCodex.objective13_le_expect_full hN Ξ ℓ hne_top ξhat ε α q h



#print axioms solution
