-- Prove2me | solution 1 for RiskFunctionals.Kusuoka.covariance_coupling
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T17:32:51.00603+00:00
-- url     : https://prove2.me/submissions/8605ba3d-c7d5-4387-859e-38c5b01ddb98

import Mathlib

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal

namespace KC82

variable {Q : Type*} [MeasurableSpace Q] (ρ : Measure Q) [IsProbabilityMeasure ρ]

/-- double layer cake for a product of two nonnegative parts -/
theorem lay (A B : ℝ → Set Q) (f g : Q → ℝ) (hg : Measurable g)
    (hA : ∀ ω, ENNReal.ofReal (f ω) = volume ({s | ω ∈ A s} ∩ Ioi 0))
    (hB : ∀ ω, ENNReal.ofReal (g ω) = volume ({s | ω ∈ B s} ∩ Ioi 0))
    (hAm : MeasurableSet {p : ℝ × Q | p.2 ∈ A p.1})
    (hBm : MeasurableSet {p : ℝ × Q | p.2 ∈ B p.1}) :
    ∫⁻ ω, ENNReal.ofReal (f ω) * ENNReal.ofReal (g ω) ∂ρ =
      ∫⁻ s in Ioi 0, ∫⁻ t in Ioi 0, ρ (A s ∩ B t) := by
  set IA : ℝ × Q → ℝ≥0∞ := {p : ℝ × Q | p.2 ∈ A p.1}.indicator 1 with hIA
  set IB : ℝ × Q → ℝ≥0∞ := {p : ℝ × Q | p.2 ∈ B p.1}.indicator 1 with hIB
  have mIA : Measurable IA := measurable_one.indicator hAm
  have mIB : Measurable IB := measurable_one.indicator hBm
  have hsec : ∀ (C : ℝ → Set Q) (hC : MeasurableSet {p : ℝ × Q | p.2 ∈ C p.1}) (ω : Q),
      volume ({s | ω ∈ C s} ∩ Ioi 0) =
        ∫⁻ s in Ioi 0, ({p : ℝ × Q | p.2 ∈ C p.1}.indicator 1 : ℝ × Q → ℝ≥0∞) (s, ω) := by
    intro C hC ω
    have hm : MeasurableSet {s | ω ∈ C s} := measurable_prodMk_right hC
    rw [← Measure.restrict_apply hm, ← lintegral_indicator_one hm]
    congr 1
  have key1 : ∀ s t, ρ (A s ∩ B t) = ∫⁻ ω, IA (s, ω) * IB (t, ω) ∂ρ := by
    intro s t
    have hmA : MeasurableSet (A s) := measurable_prodMk_left hAm
    have hmB : MeasurableSet (B t) := measurable_prodMk_left hBm
    rw [← lintegral_indicator_one (hmA.inter hmB)]
    congr 1; funext ω
    simp only [IA, IB, indicator, mem_inter_iff, mem_setOf_eq, Pi.one_apply]
    split_ifs <;> simp_all
  have mg : Measurable fun ω => ENNReal.ofReal (g ω) := ENNReal.measurable_ofReal.comp hg
  calc ∫⁻ ω, ENNReal.ofReal (f ω) * ENNReal.ofReal (g ω) ∂ρ
      = ∫⁻ ω, (∫⁻ s in Ioi 0, IA (s, ω) * ENNReal.ofReal (g ω)) ∂ρ := by
        refine lintegral_congr fun ω => ?_
        rw [hA ω, hsec A hAm ω]
        have h : Measurable fun s : ℝ => IA (s, ω) := mIA.comp (measurable_id.prodMk measurable_const)
        exact (lintegral_mul_const _ h).symm
    _ = ∫⁻ s in Ioi 0, ∫⁻ ω, IA (s, ω) * ENNReal.ofReal (g ω) ∂ρ := by
        apply lintegral_lintegral_swap
        exact (((mIA.comp (measurable_snd.prodMk measurable_fst))).mul
          (mg.comp measurable_fst)).aemeasurable
    _ = ∫⁻ s in Ioi 0, ∫⁻ ω, (∫⁻ t in Ioi 0, IA (s, ω) * IB (t, ω)) ∂ρ := by
        refine lintegral_congr fun s => lintegral_congr fun ω => ?_
        rw [hB ω, hsec B hBm ω]
        have h : Measurable fun t : ℝ => IB (t, ω) := mIB.comp (measurable_id.prodMk measurable_const)
        exact (lintegral_const_mul _ h).symm
    _ = ∫⁻ s in Ioi 0, ∫⁻ t in Ioi 0, ∫⁻ ω, IA (s, ω) * IB (t, ω) ∂ρ := by
        refine lintegral_congr fun s => ?_
        apply lintegral_lintegral_swap
        exact ((mIA.comp (measurable_const.prodMk measurable_fst)).mul
          (mIB.comp (measurable_snd.prodMk measurable_fst))).aemeasurable
    _ = _ := by
        refine lintegral_congr fun s => lintegral_congr fun t => (key1 s t).symm

def Ap (Z : Q → ℝ) (s : ℝ) : Set Q := {ω | s < Z ω}
def Am (Z : Q → ℝ) (s : ℝ) : Set Q := {ω | Z ω ≤ -s}

theorem Ap_vol (Z : Q → ℝ) (ω : Q) :
    ENNReal.ofReal (Z ω) = volume ({s | ω ∈ Ap Z s} ∩ Ioi 0) := by
  have : {s | ω ∈ Ap Z s} ∩ Ioi 0 = Ioo 0 (Z ω) := by
    ext s; simp only [Ap, mem_setOf_eq, mem_inter_iff, mem_Ioi, mem_Ioo]; tauto
  rw [this, Real.volume_Ioo, sub_zero]

theorem Am_vol (Z : Q → ℝ) (ω : Q) :
    ENNReal.ofReal (-Z ω) = volume ({s | ω ∈ Am Z s} ∩ Ioi 0) := by
  have : {s | ω ∈ Am Z s} ∩ Ioi 0 = Ioc 0 (-Z ω) := by
    ext s; simp only [Am, mem_setOf_eq, mem_inter_iff, mem_Ioi, mem_Ioc]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨h2, by linarith⟩
    · rintro ⟨h1, h2⟩; exact ⟨by linarith, h1⟩
  rw [this, Real.volume_Ioc, sub_zero]

theorem Ap_meas {Z : Q → ℝ} (hZ : Measurable Z) : MeasurableSet {p : ℝ × Q | p.2 ∈ Ap Z p.1} :=
  measurableSet_lt measurable_fst (hZ.comp measurable_snd)

theorem Am_meas {Z : Q → ℝ} (hZ : Measurable Z) : MeasurableSet {p : ℝ × Q | p.2 ∈ Am Z p.1} :=
  measurableSet_le (hZ.comp measurable_snd) measurable_fst.neg

/-- the quadrant term -/
noncomputable def T (A B : ℝ → Set Q) : ℝ≥0∞ := ∫⁻ s in Ioi 0, ∫⁻ t in Ioi 0, ρ (A s ∩ B t)

theorem piece (a b : Q → ℝ) (A B : ℝ → Set Q) (ha : Measurable a) (hb : Measurable b)
    (hA : ∀ ω, ENNReal.ofReal (a ω) = volume ({s | ω ∈ A s} ∩ Ioi 0))
    (hB : ∀ ω, ENNReal.ofReal (b ω) = volume ({s | ω ∈ B s} ∩ Ioi 0))
    (hAm : MeasurableSet {p : ℝ × Q | p.2 ∈ A p.1})
    (hBm : MeasurableSet {p : ℝ × Q | p.2 ∈ B p.1})
    (hI : Integrable (fun ω => a ω * b ω) ρ) :
    Integrable (fun ω => max (a ω) 0 * max (b ω) 0) ρ ∧
    ∫ ω, max (a ω) 0 * max (b ω) 0 ∂ρ = (T ρ A B).toReal ∧ T ρ A B ≠ ⊤ := by
  have hm : Measurable fun ω => max (a ω) 0 * max (b ω) 0 :=
    (ha.max measurable_const).mul (hb.max measurable_const)
  have hI' : Integrable (fun ω => max (a ω) 0 * max (b ω) 0) ρ := by
    refine hI.norm.mono' hm.aestronglyMeasurable (Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (le_max_right _ _) (le_max_right _ _)),
      Real.norm_eq_abs, abs_mul]
    exact mul_le_mul (max_le (le_abs_self _) (abs_nonneg _)) (max_le (le_abs_self _) (abs_nonneg _))
      (le_max_right _ _) (abs_nonneg _)
  have hof : ∀ x : ℝ, ENNReal.ofReal (max x 0) = ENNReal.ofReal x := by
    intro x; rcases le_total x 0 with h | h
    · rw [max_eq_right h, ENNReal.ofReal_zero, ENNReal.ofReal_of_nonpos h]
    · rw [max_eq_left h]
  have hL : ∫⁻ ω, ENNReal.ofReal (max (a ω) 0 * max (b ω) 0) ∂ρ = T ρ A B := by
    rw [T, ← lay ρ A B a b hb hA hB hAm hBm]
    refine lintegral_congr fun ω => ?_
    rw [ENNReal.ofReal_mul (le_max_right _ _), hof, hof]
  refine ⟨hI', ?_, ?_⟩
  · rw [integral_eq_lintegral_of_nonneg_ae
      (Eventually.of_forall fun ω => mul_nonneg (le_max_right _ _) (le_max_right _ _))
      hm.aestronglyMeasurable, hL]
  · rw [← hL]; exact (hI'.lintegral_lt_top).ne

/-- E[Z₁Z₂] as a signed combination of four quadrant terms -/
theorem cov_quad (Z₁ Z₂ : Q → ℝ) (m₁ : Measurable Z₁) (m₂ : Measurable Z₂)
    (h₁ : MemLp Z₁ 2 ρ) (h₂ : MemLp Z₂ 2 ρ) :
    ∫ ω, Z₁ ω * Z₂ ω ∂ρ =
      (T ρ (Ap Z₁) (Ap Z₂)).toReal + (T ρ (Am Z₁) (Am Z₂)).toReal -
        (T ρ (Ap Z₁) (Am Z₂)).toReal - (T ρ (Am Z₁) (Ap Z₂)).toReal ∧
    T ρ (Ap Z₁) (Ap Z₂) ≠ ⊤ ∧ T ρ (Am Z₁) (Am Z₂) ≠ ⊤ ∧
    T ρ (Ap Z₁) (Am Z₂) ≠ ⊤ ∧ T ρ (Am Z₁) (Ap Z₂) ≠ ⊤ := by
  have hI : Integrable (fun ω => Z₁ ω * Z₂ ω) ρ := h₁.integrable_mul h₂
  have hI2 : Integrable (fun ω => -Z₁ ω * -Z₂ ω) ρ := by simpa using hI
  have hI3 : Integrable (fun ω => Z₁ ω * -Z₂ ω) ρ := by simpa using hI.neg
  have hI4 : Integrable (fun ω => -Z₁ ω * Z₂ ω) ρ := by simpa using hI.neg
  obtain ⟨i1, e1, f1⟩ := piece ρ Z₁ Z₂ (Ap Z₁) (Ap Z₂) m₁ m₂ (Ap_vol Z₁) (Ap_vol Z₂)
    (Ap_meas m₁) (Ap_meas m₂) hI
  obtain ⟨i2, e2, f2⟩ := piece ρ (fun ω => -Z₁ ω) (fun ω => -Z₂ ω) (Am Z₁) (Am Z₂) m₁.neg m₂.neg
    (Am_vol Z₁) (Am_vol Z₂) (Am_meas m₁) (Am_meas m₂) hI2
  obtain ⟨i3, e3, f3⟩ := piece ρ Z₁ (fun ω => -Z₂ ω) (Ap Z₁) (Am Z₂) m₁ m₂.neg (Ap_vol Z₁)
    (Am_vol Z₂) (Ap_meas m₁) (Am_meas m₂) hI3
  obtain ⟨i4, e4, f4⟩ := piece ρ (fun ω => -Z₁ ω) Z₂ (Am Z₁) (Ap Z₂) m₁.neg m₂ (Am_vol Z₁)
    (Ap_vol Z₂) (Am_meas m₁) (Ap_meas m₂) hI4
  refine ⟨?_, f1, f2, f3, f4⟩
  have k3 : ∫ ω, (max (Z₁ ω) 0 * max (Z₂ ω) 0 + max (-Z₁ ω) 0 * max (-Z₂ ω) 0 -
      max (Z₁ ω) 0 * max (-Z₂ ω) 0 - max (-Z₁ ω) 0 * max (Z₂ ω) 0) ∂ρ =
      ∫ ω, (max (Z₁ ω) 0 * max (Z₂ ω) 0 + max (-Z₁ ω) 0 * max (-Z₂ ω) 0 -
      max (Z₁ ω) 0 * max (-Z₂ ω) 0) ∂ρ - ∫ ω, max (-Z₁ ω) 0 * max (Z₂ ω) 0 ∂ρ :=
    integral_sub ((i1.add i2).sub i3) i4
  have k2 : ∫ ω, (max (Z₁ ω) 0 * max (Z₂ ω) 0 + max (-Z₁ ω) 0 * max (-Z₂ ω) 0 -
      max (Z₁ ω) 0 * max (-Z₂ ω) 0) ∂ρ =
      ∫ ω, (max (Z₁ ω) 0 * max (Z₂ ω) 0 + max (-Z₁ ω) 0 * max (-Z₂ ω) 0) ∂ρ -
      ∫ ω, max (Z₁ ω) 0 * max (-Z₂ ω) 0 ∂ρ := integral_sub (i1.add i2) i3
  have k1 : ∫ ω, (max (Z₁ ω) 0 * max (Z₂ ω) 0 + max (-Z₁ ω) 0 * max (-Z₂ ω) 0) ∂ρ =
      ∫ ω, max (Z₁ ω) 0 * max (Z₂ ω) 0 ∂ρ + ∫ ω, max (-Z₁ ω) 0 * max (-Z₂ ω) 0 ∂ρ :=
    integral_add i1 i2
  rw [← e1, ← e2, ← e3, ← e4, ← k1, ← k2, ← k3]
  refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
  show Z₁ ω * Z₂ ω = max (Z₁ ω) 0 * max (Z₂ ω) 0 + max (-Z₁ ω) 0 * max (-Z₂ ω) 0 - max (Z₁ ω) 0 * max (-Z₂ ω) 0 - max (-Z₁ ω) 0 * max (Z₂ ω) 0
  rcases le_total (Z₁ ω) 0 with h1 | h1 <;> rcases le_total (Z₂ ω) 0 with h2 | h2
  · rw [max_eq_right h1, max_eq_right h2, max_eq_left (neg_nonneg.2 h1),
      max_eq_left (neg_nonneg.2 h2)]; ring
  · rw [max_eq_right h1, max_eq_left h2, max_eq_left (neg_nonneg.2 h1),
      max_eq_right (neg_nonpos.2 h2)]; ring
  · rw [max_eq_left h1, max_eq_right h2, max_eq_right (neg_nonpos.2 h1),
      max_eq_left (neg_nonneg.2 h2)]; ring
  · rw [max_eq_left h1, max_eq_left h2, max_eq_right (neg_nonpos.2 h1),
      max_eq_right (neg_nonpos.2 h2)]; ring

end KC82


open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal

namespace KC82

theorem T_mono {Q Q' : Type*} [MeasurableSpace Q] [MeasurableSpace Q'] (ρ : Measure Q) (ρ' : Measure Q')
    [IsFiniteMeasure ρ] [IsFiniteMeasure ρ'] (A B : ℝ → Set Q) (A' B' : ℝ → Set Q')
    (h : ∀ s t, ρ.real (A s ∩ B t) ≤ ρ'.real (A' s ∩ B' t)) : T ρ A B ≤ T ρ' A' B' := by
  refine lintegral_mono fun s => lintegral_mono fun t => ?_
  rw [← ENNReal.ofReal_toReal (measure_ne_top ρ _), ← ENNReal.ofReal_toReal (measure_ne_top ρ' _)]
  exact ENNReal.ofReal_le_ofReal (h s t)

variable {Q : Type*} [MeasurableSpace Q] (ρ : Measure Q) [IsProbabilityMeasure ρ]

theorem frechet_up {A B : Set Q} : ρ.real (A ∩ B) ≤ min (ρ.real A) (ρ.real B) :=
  le_min (measureReal_mono inter_subset_left) (measureReal_mono inter_subset_right)

theorem frechet_lo {A B : Set Q} (hA : MeasurableSet A) (hB : MeasurableSet B) :
    max (ρ.real A + ρ.real B - 1) 0 ≤ ρ.real (A ∩ B) := by
  have h1 := measureReal_union_add_inter (μ := ρ) (s := A) hB
  have h2 : ρ.real (A ∪ B) ≤ 1 := measureReal_le_one
  exact max_le (by linarith) measureReal_nonneg

theorem Ap_eq (Z : Q → ℝ) (s : ℝ) : Ap Z s = {ω | Z ω ≤ s}ᶜ := by
  ext ω; simp [Ap]

theorem Am_eq (Z : Q → ℝ) (s : ℝ) : Am Z s = {ω | Z ω ≤ -s} := rfl

/-- the four quadrant probabilities in terms of the joint distribution function -/
theorem quad_formulas {A0 B0 : Set Q} (hA : MeasurableSet A0) (hB : MeasurableSet B0) :
    ρ.real (A0ᶜ ∩ B0ᶜ) = 1 - ρ.real A0 - ρ.real B0 + ρ.real (A0 ∩ B0) ∧
    ρ.real (A0ᶜ ∩ B0) = ρ.real B0 - ρ.real (A0 ∩ B0) ∧
    ρ.real (A0 ∩ B0ᶜ) = ρ.real A0 - ρ.real (A0 ∩ B0) := by
  have hc : ∀ {C : Set Q}, MeasurableSet C → ρ.real Cᶜ = 1 - ρ.real C := fun hC =>
    probReal_compl_eq_one_sub hC
  refine ⟨?_, ?_, ?_⟩
  · rw [← compl_union, hc (hA.union hB)]
    have := measureReal_union_add_inter (μ := ρ) (s := A0) hB
    linarith
  · have := measureReal_inter_add_diff (μ := ρ) (s := B0) hA
    rw [diff_eq, inter_comm B0 A0] at this
    rw [inter_comm]; linarith
  · have := measureReal_inter_add_diff (μ := ρ) (s := A0) hB
    rw [diff_eq] at this; linarith

section
variable {ρ}
variable (Y₁ Y₂ : Q → ℝ) (m₁ : Measurable Y₁) (m₂ : Measurable Y₂)

include m₁ m₂ in
theorem co_quads
    (hc : ∀ u v : ℝ, ρ.real {ω | Y₁ ω ≤ u ∧ Y₂ ω ≤ v} =
      min (ρ.real {ω | Y₁ ω ≤ u}) (ρ.real {ω | Y₂ ω ≤ v})) (s t : ℝ) :
    ρ.real (Ap Y₁ s ∩ Ap Y₂ t) = min (ρ.real (Ap Y₁ s)) (ρ.real (Ap Y₂ t)) ∧
    ρ.real (Am Y₁ s ∩ Am Y₂ t) = min (ρ.real (Am Y₁ s)) (ρ.real (Am Y₂ t)) ∧
    ρ.real (Ap Y₁ s ∩ Am Y₂ t) = max (ρ.real (Ap Y₁ s) + ρ.real (Am Y₂ t) - 1) 0 ∧
    ρ.real (Am Y₁ s ∩ Ap Y₂ t) = max (ρ.real (Am Y₁ s) + ρ.real (Ap Y₂ t) - 1) 0 := by
  have hm1 : ∀ u, MeasurableSet {ω | Y₁ ω ≤ u} := fun u => measurableSet_le m₁ measurable_const
  have hm2 : ∀ u, MeasurableSet {ω | Y₂ ω ≤ u} := fun u => measurableSet_le m₂ measurable_const
  have hcomp : ∀ C : Set Q, MeasurableSet C → ρ.real Cᶜ = 1 - ρ.real C := fun C hC =>
    probReal_compl_eq_one_sub hC
  have hc' : ∀ u v, ρ.real ({ω | Y₁ ω ≤ u} ∩ {ω | Y₂ ω ≤ v}) =
      min (ρ.real {ω | Y₁ ω ≤ u}) (ρ.real {ω | Y₂ ω ≤ v}) := hc
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [Ap_eq, Ap_eq, (quad_formulas ρ (hm1 s) (hm2 t)).1, hcomp _ (hm1 s), hcomp _ (hm2 t), hc']
    simp only [min_def, max_def]; split_ifs <;> linarith
  · exact hc' (-s) (-t)
  · rw [Ap_eq, Am_eq, (quad_formulas ρ (hm1 s) (hm2 (-t))).2.1, hcomp _ (hm1 s), hc']
    simp only [min_def, max_def]; split_ifs <;> linarith
  · rw [Am_eq, Ap_eq, (quad_formulas ρ (hm1 (-s)) (hm2 t)).2.2, hcomp _ (hm2 t), hc']
    simp only [min_def, max_def]; split_ifs <;> linarith

include m₁ m₂ in
theorem anti_quads
    (hc : ∀ u v : ℝ, ρ.real {ω | Y₁ ω ≤ u ∧ Y₂ ω ≤ v} =
      max (ρ.real {ω | Y₁ ω ≤ u} + ρ.real {ω | Y₂ ω ≤ v} - 1) 0) (s t : ℝ) :
    ρ.real (Ap Y₁ s ∩ Ap Y₂ t) = max (ρ.real (Ap Y₁ s) + ρ.real (Ap Y₂ t) - 1) 0 ∧
    ρ.real (Am Y₁ s ∩ Am Y₂ t) = max (ρ.real (Am Y₁ s) + ρ.real (Am Y₂ t) - 1) 0 ∧
    ρ.real (Ap Y₁ s ∩ Am Y₂ t) = min (ρ.real (Ap Y₁ s)) (ρ.real (Am Y₂ t)) ∧
    ρ.real (Am Y₁ s ∩ Ap Y₂ t) = min (ρ.real (Am Y₁ s)) (ρ.real (Ap Y₂ t)) := by
  have hm1 : ∀ u, MeasurableSet {ω | Y₁ ω ≤ u} := fun u => measurableSet_le m₁ measurable_const
  have hm2 : ∀ u, MeasurableSet {ω | Y₂ ω ≤ u} := fun u => measurableSet_le m₂ measurable_const
  have hcomp : ∀ C : Set Q, MeasurableSet C → ρ.real Cᶜ = 1 - ρ.real C := fun C hC =>
    probReal_compl_eq_one_sub hC
  have hc' : ∀ u v, ρ.real ({ω | Y₁ ω ≤ u} ∩ {ω | Y₂ ω ≤ v}) =
      max (ρ.real {ω | Y₁ ω ≤ u} + ρ.real {ω | Y₂ ω ≤ v} - 1) 0 := hc
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [Ap_eq, Ap_eq, (quad_formulas ρ (hm1 s) (hm2 t)).1, hcomp _ (hm1 s), hcomp _ (hm2 t), hc']
    simp only [min_def, max_def]; split_ifs <;> linarith
  · exact hc' (-s) (-t)
  · rw [Ap_eq, Am_eq, (quad_formulas ρ (hm1 s) (hm2 (-t))).2.1, hcomp _ (hm1 s), hc']
    simp only [min_def, max_def]; split_ifs <;> linarith
  · rw [Am_eq, Ap_eq, (quad_formulas ρ (hm1 (-s)) (hm2 t)).2.2, hcomp _ (hm2 t), hc']
    simp only [min_def, max_def]; split_ifs <;> linarith

end

theorem main_meas {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {Ω' : Type*} [MeasurableSpace Ω'] (P' : Measure Ω')
    [IsProbabilityMeasure P']
    (Y₁ Y₂ : Ω → ℝ) (hY₁ : MemLp Y₁ 2 P) (hY₂ : MemLp Y₂ 2 P)
    (X₁ X₂ : Ω' → ℝ) (h₁ : IdentDistrib X₁ Y₁ P' P) (h₂ : IdentDistrib X₂ Y₂ P' P)
    (mY₁ : Measurable Y₁) (mY₂ : Measurable Y₂) (mX₁ : Measurable X₁) (mX₂ : Measurable X₂) :
    ((∀ u v : ℝ, P.real {ω | Y₁ ω ≤ u ∧ Y₂ ω ≤ v} =
          min (P.real {ω | Y₁ ω ≤ u}) (P.real {ω | Y₂ ω ≤ v})) →
        ∫ ω, X₁ ω * X₂ ω ∂P' ≤ ∫ ω, Y₁ ω * Y₂ ω ∂P) ∧
    ((∀ u v : ℝ, P.real {ω | Y₁ ω ≤ u ∧ Y₂ ω ≤ v} =
          max (P.real {ω | Y₁ ω ≤ u} + P.real {ω | Y₂ ω ≤ v} - 1) 0) →
        ∫ ω, Y₁ ω * Y₂ ω ∂P ≤ ∫ ω, X₁ ω * X₂ ω ∂P') := by
  have hX₁ : MemLp X₁ 2 P' := h₁.memLp_iff.2 hY₁
  have hX₂ : MemLp X₂ 2 P' := h₂.memLp_iff.2 hY₂
  obtain ⟨eY, fY1, fY2, fY3, fY4⟩ := cov_quad P Y₁ Y₂ mY₁ mY₂ hY₁ hY₂
  obtain ⟨eX, fX1, fX2, fX3, fX4⟩ := cov_quad P' X₁ X₂ mX₁ mX₂ hX₁ hX₂
  have mp1 : ∀ s, P'.real (Ap X₁ s) = P.real (Ap Y₁ s) := fun s => by
    simp only [measureReal_def]; congr 1; exact h₁.measure_mem_eq measurableSet_Ioi
  have mp2 : ∀ s, P'.real (Ap X₂ s) = P.real (Ap Y₂ s) := fun s => by
    simp only [measureReal_def]; congr 1; exact h₂.measure_mem_eq measurableSet_Ioi
  have mm1 : ∀ s, P'.real (Am X₁ s) = P.real (Am Y₁ s) := fun s => by
    simp only [measureReal_def]; congr 1; exact h₁.measure_mem_eq measurableSet_Iic
  have mm2 : ∀ s, P'.real (Am X₂ s) = P.real (Am Y₂ s) := fun s => by
    simp only [measureReal_def]; congr 1; exact h₂.measure_mem_eq measurableSet_Iic
  have apm : ∀ (Z : Ω' → ℝ), Measurable Z → ∀ s, MeasurableSet (Ap Z s) := fun Z hZ s =>
    measurableSet_lt measurable_const hZ
  have amm : ∀ (Z : Ω' → ℝ), Measurable Z → ∀ s, MeasurableSet (Am Z s) := fun Z hZ s =>
    measurableSet_le hZ measurable_const
  constructor
  · intro hc
    have q := co_quads Y₁ Y₂ mY₁ mY₂ hc
    have t1 : T P' (Ap X₁) (Ap X₂) ≤ T P (Ap Y₁) (Ap Y₂) := T_mono _ _ _ _ _ _ fun s t => by
      rw [(q s t).1, ← mp1, ← mp2]; exact frechet_up P'
    have t2 : T P' (Am X₁) (Am X₂) ≤ T P (Am Y₁) (Am Y₂) := T_mono _ _ _ _ _ _ fun s t => by
      rw [(q s t).2.1, ← mm1, ← mm2]; exact frechet_up P'
    have t3 : T P (Ap Y₁) (Am Y₂) ≤ T P' (Ap X₁) (Am X₂) := T_mono _ _ _ _ _ _ fun s t => by
      rw [(q s t).2.2.1, ← mp1, ← mm2]; exact frechet_lo P' (apm _ mX₁ s) (amm _ mX₂ t)
    have t4 : T P (Am Y₁) (Ap Y₂) ≤ T P' (Am X₁) (Ap X₂) := T_mono _ _ _ _ _ _ fun s t => by
      rw [(q s t).2.2.2, ← mm1, ← mp2]; exact frechet_lo P' (amm _ mX₁ s) (apm _ mX₂ t)
    have r1 := ENNReal.toReal_mono fY1 t1
    have r2 := ENNReal.toReal_mono fY2 t2
    have r3 := ENNReal.toReal_mono fX3 t3
    have r4 := ENNReal.toReal_mono fX4 t4
    rw [eX, eY]; linarith
  · intro hc
    have q := anti_quads Y₁ Y₂ mY₁ mY₂ hc
    have t1 : T P (Ap Y₁) (Ap Y₂) ≤ T P' (Ap X₁) (Ap X₂) := T_mono _ _ _ _ _ _ fun s t => by
      rw [(q s t).1, ← mp1, ← mp2]; exact frechet_lo P' (apm _ mX₁ s) (apm _ mX₂ t)
    have t2 : T P (Am Y₁) (Am Y₂) ≤ T P' (Am X₁) (Am X₂) := T_mono _ _ _ _ _ _ fun s t => by
      rw [(q s t).2.1, ← mm1, ← mm2]; exact frechet_lo P' (amm _ mX₁ s) (amm _ mX₂ t)
    have t3 : T P' (Ap X₁) (Am X₂) ≤ T P (Ap Y₁) (Am Y₂) := T_mono _ _ _ _ _ _ fun s t => by
      rw [(q s t).2.2.1, ← mp1, ← mm2]; exact frechet_up P'
    have t4 : T P' (Am X₁) (Ap X₂) ≤ T P (Am Y₁) (Ap Y₂) := T_mono _ _ _ _ _ _ fun s t => by
      rw [(q s t).2.2.2, ← mm1, ← mp2]; exact frechet_up P'
    have r1 := ENNReal.toReal_mono fX1 t1
    have r2 := ENNReal.toReal_mono fX2 t2
    have r3 := ENNReal.toReal_mono fY3 t3
    have r4 := ENNReal.toReal_mono fY4 t4
    rw [eX, eY]; linarith

end KC82


open MeasureTheory ProbabilityTheory Set Filter Topology

theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {Ω' : Type*} [MeasurableSpace Ω'] (P' : Measure Ω')
    [IsProbabilityMeasure P']
    (Y₁ Y₂ : Ω → ℝ) (hY₁ : MemLp Y₁ 2 P) (hY₂ : MemLp Y₂ 2 P)
    (X₁ X₂ : Ω' → ℝ) (h₁ : IdentDistrib X₁ Y₁ P' P) (h₂ : IdentDistrib X₂ Y₂ P' P) :
    ((∀ u v : ℝ, P.real {ω | Y₁ ω ≤ u ∧ Y₂ ω ≤ v} =
          min (P.real {ω | Y₁ ω ≤ u}) (P.real {ω | Y₂ ω ≤ v})) →
        (∫ ω, X₁ ω * X₂ ω ∂P') - (∫ ω, X₁ ω ∂P') * (∫ ω, X₂ ω ∂P') ≤
          (∫ ω, Y₁ ω * Y₂ ω ∂P) - (∫ ω, Y₁ ω ∂P) * (∫ ω, Y₂ ω ∂P)) ∧
    ((∀ u v : ℝ, P.real {ω | Y₁ ω ≤ u ∧ Y₂ ω ≤ v} =
          max (P.real {ω | Y₁ ω ≤ u} + P.real {ω | Y₂ ω ≤ v} - 1) 0) →
        (∫ ω, Y₁ ω * Y₂ ω ∂P) - (∫ ω, Y₁ ω ∂P) * (∫ ω, Y₂ ω ∂P) ≤
          (∫ ω, X₁ ω * X₂ ω ∂P') - (∫ ω, X₁ ω ∂P') * (∫ ω, X₂ ω ∂P')) := by
  -- measurable modifications
  have aY₁ := hY₁.aestronglyMeasurable.aemeasurable
  have aY₂ := hY₂.aestronglyMeasurable.aemeasurable
  have aX₁ := h₁.aemeasurable_fst
  have aX₂ := h₂.aemeasurable_fst
  set Y₁' := aY₁.mk Y₁
  set Y₂' := aY₂.mk Y₂
  set X₁' := aX₁.mk X₁
  set X₂' := aX₂.mk X₂
  have eY₁ : Y₁ =ᵐ[P] Y₁' := aY₁.ae_eq_mk
  have eY₂ : Y₂ =ᵐ[P] Y₂' := aY₂.ae_eq_mk
  have eX₁ : X₁ =ᵐ[P'] X₁' := aX₁.ae_eq_mk
  have eX₂ : X₂ =ᵐ[P'] X₂' := aX₂.ae_eq_mk
  have h₁' : IdentDistrib X₁' Y₁' P' P :=
    ((IdentDistrib.of_ae_eq aX₁ eX₁).symm.trans h₁).trans (IdentDistrib.of_ae_eq aY₁ eY₁)
  have h₂' : IdentDistrib X₂' Y₂' P' P :=
    ((IdentDistrib.of_ae_eq aX₂ eX₂).symm.trans h₂).trans (IdentDistrib.of_ae_eq aY₂ eY₂)
  have M := KC82.main_meas P P' Y₁' Y₂' (hY₁.ae_eq eY₁) (hY₂.ae_eq eY₂) X₁' X₂' h₁' h₂'
    aY₁.measurable_mk aY₂.measurable_mk aX₁.measurable_mk aX₂.measurable_mk
  have iY : ∫ ω, Y₁ ω * Y₂ ω ∂P = ∫ ω, Y₁' ω * Y₂' ω ∂P :=
    integral_congr_ae (eY₁.mul eY₂)
  have iX : ∫ ω, X₁ ω * X₂ ω ∂P' = ∫ ω, X₁' ω * X₂' ω ∂P' :=
    integral_congr_ae (eX₁.mul eX₂)
  have m1 : ∫ ω, X₁ ω ∂P' = ∫ ω, Y₁ ω ∂P := h₁.integral_eq
  have m2 : ∫ ω, X₂ ω ∂P' = ∫ ω, Y₂ ω ∂P := h₂.integral_eq
  have hs1 : ∀ u, P.real {ω | Y₁ ω ≤ u} = P.real {ω | Y₁' ω ≤ u} := fun u =>
    measureReal_congr (eY₁.mono fun ω h => by
      change (Y₁ ω ≤ u) = (Y₁' ω ≤ u); rw [h])
  have hs2 : ∀ u, P.real {ω | Y₂ ω ≤ u} = P.real {ω | Y₂' ω ≤ u} := fun u =>
    measureReal_congr (eY₂.mono fun ω h => by
      change (Y₂ ω ≤ u) = (Y₂' ω ≤ u); rw [h])
  have hs12 : ∀ u v, P.real {ω | Y₁ ω ≤ u ∧ Y₂ ω ≤ v} = P.real {ω | Y₁' ω ≤ u ∧ Y₂' ω ≤ v} :=
    fun u v => measureReal_congr ((eY₁.and eY₂).mono fun ω h => by
      change (Y₁ ω ≤ u ∧ Y₂ ω ≤ v) = (Y₁' ω ≤ u ∧ Y₂' ω ≤ v); rw [h.1, h.2])
  rw [iY, iX, m1, m2]
  constructor
  · intro hc
    have := M.1 fun u v => by rw [← hs12, ← hs1, ← hs2]; exact hc u v
    linarith
  · intro hc
    have := M.2 fun u v => by rw [← hs12, ← hs1, ← hs2]; exact hc u v
    linarith

