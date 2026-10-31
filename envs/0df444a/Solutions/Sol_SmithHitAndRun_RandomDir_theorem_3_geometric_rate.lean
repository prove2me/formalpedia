-- Prove2me | solution 1 for SmithHitAndRun.RandomDir.theorem_3_geometric_rate
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-30T16:43:09.024349+00:00
-- url     : https://prove2.me/submissions/fbc8d9f1-513b-46ed-8406-6278a1ea6693

import Mathlib
import Definitions.Def_MarkovIterKernel
import Definitions.Def_SmithHitAndRun_RandomDir_RandomDirectionsKernel
import Definitions.Def_SmithHitAndRun_RandomDir_UniformLaw
import Definitions.Def_SmithHitAndRun_RandomDir_RateConstants

set_option autoImplicit false

open MeasureTheory ProbabilityTheory SmithHitAndRun.RandomDir
open scoped ENNReal

namespace SmithT3Aux

lemma iter_succ' {X : Type*} [MeasurableSpace X] (P : Kernel X X) (k : ℕ) :
    MarkovChainCLT.iterKernel P (k + 1) = MarkovChainCLT.iterKernel P k ∘ₖ P := by
  induction k with
  | zero => simp
  | succ k ih =>
    calc MarkovChainCLT.iterKernel P (k + 1 + 1) = P ∘ₖ MarkovChainCLT.iterKernel P (k + 1) := rfl
      _ = P ∘ₖ (MarkovChainCLT.iterKernel P k ∘ₖ P) := by rw [ih]
      _ = (P ∘ₖ MarkovChainCLT.iterKernel P k) ∘ₖ P := (Kernel.comp_assoc _ _ _).symm
      _ = MarkovChainCLT.iterKernel P (k + 1) ∘ₖ P := rfl

lemma stat_iter {X : Type*} [MeasurableSpace X] (P : Kernel X X) (lam : Measure X)
    (h : P ∘ₘ lam = lam) (k : ℕ) : MarkovChainCLT.iterKernel P k ∘ₘ lam = lam := by
  induction k with
  | zero => simp
  | succ k ih => rw [MarkovChainCLT.iterKernel_succ, ← Measure.comp_assoc, ih, h]

lemma doeblin_step {X : Type*} [MeasurableSpace X] (μ lam : Measure X) [IsProbabilityMeasure lam]
    (S : Set X) (hμ1 : μ Set.univ = 1) (hμS : μ Sᶜ = 0) (ε : ℝ≥0∞) (hε1 : ε ≤ 1)
    (hmin : ε • lam ≤ μ) (f : X → ℝ≥0∞) (c r : ℝ) (hc0 : 0 ≤ c) (hr : 0 ≤ r)
    (hc : ∫⁻ y, f y ∂lam = ENNReal.ofReal c)
    (hfS : ∀ y ∈ S, f y ≠ ⊤ ∧ |(f y).toReal - c| ≤ r) :
    ∫⁻ y, f y ∂μ ≠ ⊤ ∧ |(∫⁻ y, f y ∂μ).toReal - c| ≤ (1 - ε.toReal) * r := by
  have hεt : ε ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top hε1
  haveI : IsFiniteMeasure (ε • lam) := ⟨by
    rw [Measure.smul_apply, measure_univ, smul_eq_mul, mul_one]; exact hεt.lt_top⟩
  set ν := μ - ε • lam with hν
  have hdec : μ = ν + ε • lam := (Measure.sub_add_cancel_of_le hmin).symm
  have hνle : ν ≤ μ := Measure.sub_le
  have hνS : ν Sᶜ = 0 := le_antisymm ((Measure.le_iff'.1 hνle Sᶜ).trans hμS.le) bot_le
  have hae : ∀ᵐ y ∂ν, y ∈ S := by rw [ae_iff]; exact hνS
  have huniv : ν Set.univ + ε = 1 := by
    have h := congrArg (fun m : Measure X => m Set.univ) hdec
    simp only [Measure.add_apply, Measure.smul_apply, measure_univ, smul_eq_mul, mul_one] at h
    rw [← h, hμ1]
  have hνt : ν Set.univ ≠ ⊤ := by
    intro h; rw [h, top_add] at huniv; exact ENNReal.top_ne_one huniv
  have hνr : (ν Set.univ).toReal = 1 - ε.toReal := by
    have h := congrArg ENNReal.toReal huniv
    rw [ENNReal.toReal_add hνt hεt, ENNReal.toReal_one] at h
    linarith
  have hup : ∫⁻ y, f y ∂ν ≤ ∫⁻ _y, ENNReal.ofReal (c + r) ∂ν := by
    refine lintegral_mono_ae (hae.mono fun y hy => ?_)
    obtain ⟨h1, h2⟩ := hfS y hy
    rw [← ENNReal.ofReal_toReal h1]
    exact ENNReal.ofReal_le_ofReal (by linarith [(abs_le.1 h2).2])
  have hlo : ∫⁻ _y, ENNReal.ofReal (c - r) ∂ν ≤ ∫⁻ y, f y ∂ν := by
    refine lintegral_mono_ae (hae.mono fun y hy => ?_)
    obtain ⟨h1, h2⟩ := hfS y hy
    rw [← ENNReal.ofReal_toReal h1]
    exact ENNReal.ofReal_le_ofReal (by linarith [(abs_le.1 h2).1])
  rw [lintegral_const] at hup hlo
  have hIt : ∫⁻ y, f y ∂ν ≠ ⊤ :=
    ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hνt) hup
  have hsplit : ∫⁻ y, f y ∂μ = ∫⁻ y, f y ∂ν + ε * ENNReal.ofReal c := by
    conv_lhs => rw [hdec]
    rw [lintegral_add_measure, lintegral_smul_measure, hc, smul_eq_mul]
  have hUr : (∫⁻ y, f y ∂ν).toReal ≤ (c + r) * (1 - ε.toReal) := by
    have := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hνt) hup
    rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by linarith), hνr] at this
  have hLr : (c - r) * (1 - ε.toReal) ≤ (∫⁻ y, f y ∂ν).toReal := by
    have := ENNReal.toReal_mono hIt hlo
    rw [ENNReal.toReal_mul, hνr] at this
    have h1 : 0 ≤ 1 - ε.toReal := by rw [← hνr]; exact ENNReal.toReal_nonneg
    have h2 : c - r ≤ (ENNReal.ofReal (c - r)).toReal := by
      rw [ENNReal.toReal_ofReal']; exact le_max_left _ _
    nlinarith
  refine ⟨?_, ?_⟩
  · rw [hsplit]; exact ENNReal.add_ne_top.2 ⟨hIt, ENNReal.mul_ne_top hεt ENNReal.ofReal_ne_top⟩
  · rw [hsplit, ENNReal.toReal_add hIt (ENNReal.mul_ne_top hεt ENNReal.ofReal_ne_top),
      ENNReal.toReal_mul, ENNReal.toReal_ofReal hc0, abs_le]
    constructor <;> nlinarith

theorem doeblin {X : Type*} [MeasurableSpace X] (P : Kernel X X) (lam : Measure X)
    [IsProbabilityMeasure lam] (S : Set X) (hstat : P ∘ₘ lam = lam)
    (h1 : ∀ x ∈ S, P x Set.univ = 1) (hSc : ∀ x ∈ S, P x Sᶜ = 0)
    (ε : ℝ≥0∞) (hε1 : ε ≤ 1) (hmin : ∀ x ∈ S, ε • lam ≤ P x)
    (A : Set X) (hA : MeasurableSet A) (k : ℕ) :
    ∀ x ∈ S, MarkovChainCLT.iterKernel P k x A ≠ ⊤ ∧
      |(MarkovChainCLT.iterKernel P k x A).toReal - (lam A).toReal| ≤ (1 - ε.toReal) ^ k := by
  have hl : (lam A).toReal ≤ 1 := by
    have := prob_le_one (μ := lam) (s := A)
    exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using this)
  have hl0 : 0 ≤ (lam A).toReal := ENNReal.toReal_nonneg
  have he1 : ε.toReal ≤ 1 := ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using hε1)
  induction k with
  | zero =>
    intro x _
    simp only [MarkovChainCLT.iterKernel_zero, Kernel.id_apply, pow_zero]
    rw [Measure.dirac_apply' _ hA]
    by_cases hxA : x ∈ A
    · simp only [Set.indicator_of_mem hxA, Pi.one_apply]
      refine ⟨ENNReal.one_ne_top, ?_⟩
      rw [abs_le]; constructor <;> simp <;> linarith
    · simp only [Set.indicator_of_notMem hxA]
      refine ⟨ENNReal.zero_ne_top, ?_⟩
      rw [abs_le]; constructor <;> simp <;> linarith
  | succ k ih =>
    intro x hx
    have hstk := stat_iter P lam hstat k
    have hc : ∫⁻ y, MarkovChainCLT.iterKernel P k y A ∂lam = ENNReal.ofReal (lam A).toReal := by
      rw [ENNReal.ofReal_toReal (measure_ne_top _ _), ← Measure.bind_apply hA (Kernel.aemeasurable _)]
      exact congrArg (fun m : Measure X => m A) hstk
    rw [iter_succ', Kernel.comp_apply' _ _ _ hA]
    have h := doeblin_step (P x) lam S (h1 x hx) (hSc x hx) ε hε1 (hmin x hx)
      (fun y => MarkovChainCLT.iterKernel P k y A) (lam A).toReal ((1 - ε.toReal) ^ k) hl0
      (pow_nonneg (by linarith) _) hc ih
    refine ⟨h.1, ?_⟩
    rw [pow_succ]
    linarith [h.2]



lemma nontriv_E {n : ℕ} (hn : 1 ≤ n) : Nontrivial (EuclideanSpace ℝ (Fin n)) := by
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  infer_instance

lemma toSphere_univ {n : ℕ} :
    ((volume : Measure (EuclideanSpace ℝ (Fin n))).toSphere.map Subtype.val) Set.univ =
      n * volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1) := by
  rw [Measure.map_apply measurable_subtype_coe MeasurableSet.univ, Set.preimage_univ,
    Measure.toSphere_apply_univ, finrank_euclideanSpace_fin]

lemma sphereUniform_prob {n : ℕ} (hn : 1 ≤ n) : IsProbabilityMeasure (sphereUniform n) := by
  have := nontriv_E hn
  constructor
  have h0 : ((volume : Measure (EuclideanSpace ℝ (Fin n))).toSphere.map Subtype.val) Set.univ
      ≠ 0 := by
    rw [toSphere_univ]
    refine mul_ne_zero (by exact_mod_cast (by omega : n ≠ 0)) (Metric.measure_ball_pos _ _ one_pos).ne'
  have ht : ((volume : Measure (EuclideanSpace ℝ (Fin n))).toSphere.map Subtype.val) Set.univ
      ≠ ⊤ := by
    rw [toSphere_univ]
    exact ENNReal.mul_ne_top (ENNReal.natCast_ne_top n) measure_ball_lt_top.ne
  rw [sphereUniform, Measure.smul_apply, smul_eq_mul]
  exact ENNReal.inv_mul_cancel h0 ht

lemma sphereUniform_ae_unit {n : ℕ} : ∀ᵐ d ∂(sphereUniform n), ‖d‖ = 1 := by
  have hmeas : MeasurableSet {a : EuclideanSpace ℝ (Fin n) | ¬‖a‖ = 1} :=
    (measurable_norm (measurableSet_singleton (1 : ℝ))).compl
  rw [ae_iff, sphereUniform, Measure.smul_apply, Measure.map_apply measurable_subtype_coe hmeas]
  have : (Subtype.val ⁻¹' {a : EuclideanSpace ℝ (Fin n) | ¬‖a‖ = 1} :
      Set (Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1)) = ∅ := by
    ext u; simp
  rw [this, measure_empty, smul_zero]

lemma lineUniform_apply {n : ℕ} (S : Set (EuclideanSpace ℝ (Fin n)))
    (x d : EuclideanSpace ℝ (Fin n)) {B : Set (EuclideanSpace ℝ (Fin n))} (hB : MeasurableSet B) :
    lineUniform S x d B = (lineLength S x d)⁻¹ * volume {t : ℝ | x + t • d ∈ S ∩ B} := by
  have hf : Measurable (fun t : ℝ => x + t • d) := by fun_prop
  rw [lineUniform, Measure.smul_apply, Measure.map_apply hf hB, Measure.restrict_apply (hf hB),
    smul_eq_mul]
  congr 2
  ext t
  simp [and_comm]

lemma lineLength_le {n : ℕ} (S : Set (EuclideanSpace ℝ (Fin n)))
    (x d : EuclideanSpace ℝ (Fin n)) (hd : ‖d‖ = 1) :
    lineLength S x d ≤ Metric.ediam S := by
  unfold lineLength
  refine (Real.volume_le_diam _).trans (Metric.ediam_le fun t ht s hs => ?_)
  calc edist t s = edist (x + t • d) (x + s • d) := by
        rw [edist_dist, edist_dist, dist_add_left, dist_eq_norm, dist_eq_norm, ← sub_smul,
          norm_smul, hd, mul_one]
    _ ≤ _ := Metric.edist_le_ediam_of_mem ht hs

lemma lineLength_pos {n : ℕ} {S : Set (EuclideanSpace ℝ (Fin n))} (hSo : IsOpen S)
    {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ S) (d : EuclideanSpace ℝ (Fin n)) (hd : ‖d‖ = 1) :
    0 < lineLength S x d := by
  obtain ⟨ρ, hρ, hball⟩ := Metric.isOpen_iff.1 hSo x hx
  have hsub : Set.Ioo (-ρ) ρ ⊆ {t : ℝ | x + t • d ∈ S} := by
    intro t ht
    apply hball
    rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, hd, mul_one,
      Real.norm_eq_abs, abs_lt]
    exact ht
  calc (0 : ℝ≥0∞) < volume (Set.Ioo (-ρ) ρ) := by
        rw [Real.volume_Ioo]; exact ENNReal.ofReal_pos.2 (by linarith)
    _ ≤ _ := measure_mono hsub

lemma lineLength_ne_top {n : ℕ} {S : Set (EuclideanSpace ℝ (Fin n))}
    (hSb : Bornology.IsBounded S) (x d : EuclideanSpace ℝ (Fin n)) (hd : ‖d‖ = 1) :
    lineLength S x d ≠ ⊤ :=
  ne_top_of_le_ne_top hSb.ediam_ne_top (lineLength_le S x d hd)

lemma rd_apply {n : ℕ} (hn : 1 ≤ n) {S : Set (EuclideanSpace ℝ (Fin n))} (hS : MeasurableSet S)
    {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ S) {B : Set (EuclideanSpace ℝ (Fin n))}
    (hB : MeasurableSet B) :
    rdKernel S x B = ∫⁻ d, lineUniform S x d B ∂(sphereUniform n) := by
  have := sphereUniform_prob hn
  have hm : Measurable fun p => lineKernel S hS p B := Kernel.measurable_coe _ hB
  unfold rdKernel
  rw [dif_pos hS]
  simp only [Kernel.piecewise_apply, if_pos hx]
  rw [Kernel.comp_apply' _ _ _ hB,
    Kernel.prod_apply, Kernel.deterministic_apply, Kernel.const_apply, Measure.dirac_prod,
    lintegral_map hm measurable_prodMk_left]
  rfl

lemma rd_univ {n : ℕ} (hn : 1 ≤ n) {S : Set (EuclideanSpace ℝ (Fin n))} (hSo : IsOpen S)
    (hSb : Bornology.IsBounded S) {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ S) :
    rdKernel S x Set.univ = 1 := by
  have := sphereUniform_prob hn
  rw [rd_apply hn hSo.measurableSet hx MeasurableSet.univ]
  have : ∀ᵐ d ∂(sphereUniform n), lineUniform S x d Set.univ = 1 := by
    filter_upwards [sphereUniform_ae_unit] with d hd
    rw [lineUniform_apply S x d MeasurableSet.univ, Set.inter_univ]
    exact ENNReal.inv_mul_cancel (lineLength_pos hSo hx d hd).ne' (lineLength_ne_top hSb x d hd)
  rw [lintegral_congr_ae this, lintegral_one, measure_univ]

lemma rd_compl {n : ℕ} (hn : 1 ≤ n) {S : Set (EuclideanSpace ℝ (Fin n))} (hSo : IsOpen S)
    {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ S) :
    rdKernel S x Sᶜ = 0 := by
  rw [rd_apply hn hSo.measurableSet hx hSo.measurableSet.compl]
  have : ∀ d, lineUniform S x d Sᶜ = 0 := by
    intro d
    rw [lineUniform_apply S x d hSo.measurableSet.compl, Set.inter_compl_self]
    simp
  simp [this]

lemma polar_lower {n : ℕ} (hn : 1 ≤ n) (F : Set (EuclideanSpace ℝ (Fin n))) (hF : MeasurableSet F)
    (D : ℝ) (hD : 0 ≤ D) (hFD : ∀ y ∈ F, ‖y‖ ≤ D) :
    volume F ≤ ENNReal.ofReal (D ^ (n - 1)) *
      ∫⁻ u, volume ({t : ℝ | t • (u : EuclideanSpace ℝ (Fin n)) ∈ F} ∩ Set.Ioi 0)
        ∂((volume : Measure (EuclideanSpace ℝ (Fin n))).toSphere) := by
  have := nontriv_E hn
  have hmp := (volume : Measure (EuclideanSpace ℝ (Fin n))).measurePreserving_homeomorphUnitSphereProd
  rw [finrank_euclideanSpace_fin] at hmp
  set s : Set (Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 × Set.Ioi (0 : ℝ)) :=
    {p | ((p.2 : ℝ)) • (p.1 : EuclideanSpace ℝ (Fin n)) ∈ F} with hs_def
  have hs : MeasurableSet s := hF.preimage
    ((measurable_subtype_coe.comp measurable_snd).smul (measurable_subtype_coe.comp measurable_fst))
  have hpre : (homeomorphUnitSphereProd (EuclideanSpace ℝ (Fin n))) ⁻¹' s =
      Subtype.val ⁻¹' F := by
    ext ⟨y, hy⟩
    simp only [Set.mem_preimage, hs_def, Set.mem_setOf_eq,
      homeomorphUnitSphereProd_apply_snd_coe, homeomorphUnitSphereProd_apply_fst_coe]
    have : ‖y‖ ≠ 0 := by simpa using hy
    rw [smul_smul, mul_inv_cancel₀ this, one_smul]
  have h1 : volume F = (volume : Measure (EuclideanSpace ℝ (Fin n))).comap Subtype.val
      (Subtype.val ⁻¹' F : Set ({0}ᶜ : Set (EuclideanSpace ℝ (Fin n)))) := by
    rw [comap_subtype_coe_apply (measurableSet_singleton 0).compl, Subtype.image_preimage_coe,
      Set.inter_comm, ← Set.diff_eq, measure_diff_null (measure_singleton 0)]
  rw [h1, ← hpre, hmp.measure_preimage hs.nullMeasurableSet, Measure.prod_apply hs,
    ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_mono fun u => ?_
  rw [Measure.volumeIoiPow, withDensity_apply _ (measurable_prodMk_left hs)]
  calc ∫⁻ r in Prod.mk u ⁻¹' s, ENNReal.ofReal ((r : ℝ) ^ (n - 1))
        ∂(Measure.comap Subtype.val volume)
      ≤ ∫⁻ _r in Prod.mk u ⁻¹' s, ENNReal.ofReal (D ^ (n - 1))
          ∂(Measure.comap Subtype.val volume) := by
        refine setLIntegral_mono measurable_const fun r hr => ?_
        have hr' : ((r : ℝ)) • (u : EuclideanSpace ℝ (Fin n)) ∈ F := hr
        have hnorm := hFD _ hr'
        rw [norm_smul, norm_eq_of_mem_sphere u, mul_one, Real.norm_eq_abs,
          abs_of_pos r.2] at hnorm
        exact ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ r.2.le hnorm _)
    _ = ENNReal.ofReal (D ^ (n - 1)) *
          (Measure.comap Subtype.val volume) (Prod.mk u ⁻¹' s) := by
        rw [setLIntegral_const, mul_comm]
    _ ≤ _ := by
        gcongr
        rw [comap_subtype_coe_apply measurableSet_Ioi]
        apply measure_mono
        rintro _ ⟨r, hr, rfl⟩
        exact ⟨hr, r.2⟩

lemma line_two_halves {n : ℕ} (x u : EuclideanSpace ℝ (Fin n)) (Es : Set (EuclideanSpace ℝ (Fin n)))
    (hE : MeasurableSet Es) :
    volume ({t : ℝ | t • u ∈ {y | x + y ∈ Es}} ∩ Set.Ioi 0) +
      volume ({t : ℝ | t • u ∈ {y | x + -y ∈ Es}} ∩ Set.Ioi 0) ≤
      volume {t : ℝ | x + t • u ∈ Es} := by
  have hA : MeasurableSet {t : ℝ | x + t • u ∈ Es} := hE.preimage (by fun_prop)
  have h2 : {t : ℝ | t • u ∈ {y | x + -y ∈ Es}} ∩ Set.Ioi 0 =
      -({t : ℝ | x + t • u ∈ Es} ∩ Set.Iio 0) := by
    ext t; simp [neg_smul]
  have h1 : {t : ℝ | t • u ∈ {y | x + y ∈ Es}} ∩ Set.Ioi 0 =
      {t : ℝ | x + t • u ∈ Es} ∩ Set.Ioi 0 := rfl
  rw [h2, Measure.measure_neg, h1, ← measure_union _ (hA.inter measurableSet_Iio)]
  · exact measure_mono (Set.union_subset Set.inter_subset_left Set.inter_subset_left)
  · exact Set.disjoint_left.2 fun t h1 h2 => lt_asymm (Set.mem_Ioi.1 h1.2) (Set.mem_Iio.1 h2.2)

lemma minor {n : ℕ} (hn : 1 ≤ n) {S : Set (EuclideanSpace ℝ (Fin n))} (hSo : IsOpen S)
    (hSb : Bornology.IsBounded S) {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ S)
    {B : Set (EuclideanSpace ℝ (Fin n))} (hB : MeasurableSet B) :
    2 * volume (S ∩ B) ≤ Metric.ediam S *
      ((n : ℝ≥0∞) * volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1)) *
      ENNReal.ofReal (Metric.diam S ^ (n - 1)) * rdKernel S x B := by
  have := nontriv_E hn
  have hEs : MeasurableSet (S ∩ B) := hSo.measurableSet.inter hB
  have hc0 : ((n : ℝ≥0∞) * volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1)) ≠ 0 :=
    mul_ne_zero (by exact_mod_cast (by omega : n ≠ 0)) (Metric.measure_ball_pos _ _ one_pos).ne'
  have hct : ((n : ℝ≥0∞) * volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1)) ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.natCast_ne_top n) measure_ball_lt_top.ne
  have hED : Metric.ediam S ≠ ⊤ := hSb.ediam_ne_top
  have hED0 : Metric.ediam S ≠ 0 := by
    set e : EuclideanSpace ℝ (Fin n) := EuclideanSpace.single (⟨0, hn⟩ : Fin n) (1 : ℝ)
    have he : ‖e‖ = 1 := by simp [e]
    exact ((lineLength_pos hSo hx e he).trans_le (lineLength_le S x e he)).ne'
  have hg : Measurable (fun d : EuclideanSpace ℝ (Fin n) => volume {t : ℝ | x + t • d ∈ S ∩ B}) :=
    measurable_measure_prodMk_left
      (s := {p : EuclideanSpace ℝ (Fin n) × ℝ | x + p.2 • p.1 ∈ S ∩ B}) (hEs.preimage (by fun_prop))
  have hP : (Metric.ediam S)⁻¹ *
      (((n : ℝ≥0∞) * volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1))⁻¹ *
      ∫⁻ u, volume {t : ℝ | x + t • (u : EuclideanSpace ℝ (Fin n)) ∈ S ∩ B}
        ∂((volume : Measure (EuclideanSpace ℝ (Fin n))).toSphere)) ≤ rdKernel S x B := by
    rw [rd_apply hn hSo.measurableSet hx hB]
    calc _ = ∫⁻ d, (Metric.ediam S)⁻¹ * volume {t : ℝ | x + t • d ∈ S ∩ B}
          ∂(sphereUniform n) := by
          rw [lintegral_const_mul _ hg, sphereUniform, lintegral_smul_measure,
            lintegral_map hg measurable_subtype_coe, toSphere_univ, smul_eq_mul]
      _ ≤ _ := by
          refine lintegral_mono_ae (sphereUniform_ae_unit.mono fun d hd => ?_)
          rw [lineUniform_apply S x d hB]
          gcongr
          exact lineLength_le S x d hd
  have hFD1 : ∀ y ∈ {y : EuclideanSpace ℝ (Fin n) | x + y ∈ S ∩ B}, ‖y‖ ≤ Metric.diam S := by
    intro y hy
    have := Metric.dist_le_diam_of_mem hSb hy.1 hx
    rwa [dist_eq_norm, add_sub_cancel_left] at this
  have hFD2 : ∀ y ∈ {y : EuclideanSpace ℝ (Fin n) | x + -y ∈ S ∩ B}, ‖y‖ ≤ Metric.diam S := by
    intro y hy
    have := Metric.dist_le_diam_of_mem hSb hx hy.1
    rw [dist_eq_norm, sub_add_cancel_left] at this
    simpa using this
  have hF1 := polar_lower hn {y | x + y ∈ S ∩ B} (hEs.preimage (measurable_const_add x))
    (Metric.diam S) Metric.diam_nonneg hFD1
  have hF2 := polar_lower hn {y | x + -y ∈ S ∩ B}
    (hEs.preimage ((measurable_const_add x).comp measurable_neg)) (Metric.diam S)
    Metric.diam_nonneg hFD2
  have hv1 : volume {y : EuclideanSpace ℝ (Fin n) | x + y ∈ S ∩ B} = volume (S ∩ B) :=
    measure_preimage_add _ _ _
  have hv2 : volume {y : EuclideanSpace ℝ (Fin n) | x + -y ∈ S ∩ B} = volume (S ∩ B) := by
    have : {y : EuclideanSpace ℝ (Fin n) | x + -y ∈ S ∩ B} = -{y | x + y ∈ S ∩ B} := by
      ext y; simp
    rw [this, Measure.measure_neg, hv1]
  have hint : 2 * volume (S ∩ B) ≤ ENNReal.ofReal (Metric.diam S ^ (n - 1)) *
      ∫⁻ u, volume {t : ℝ | x + t • (u : EuclideanSpace ℝ (Fin n)) ∈ S ∩ B}
        ∂((volume : Measure (EuclideanSpace ℝ (Fin n))).toSphere) := by
    calc 2 * volume (S ∩ B) = volume {y : EuclideanSpace ℝ (Fin n) | x + y ∈ S ∩ B} +
          volume {y : EuclideanSpace ℝ (Fin n) | x + -y ∈ S ∩ B} := by rw [hv1, hv2, two_mul]
      _ ≤ _ := add_le_add hF1 hF2
      _ = _ := (mul_add _ _ _).symm
      _ ≤ _ := by
          gcongr
          refine (le_lintegral_add _ _).trans (lintegral_mono fun u => ?_)
          exact line_two_halves x u (S ∩ B) hEs
  refine hint.trans ?_
  set I := ∫⁻ u, volume {t : ℝ | x + t • (u : EuclideanSpace ℝ (Fin n)) ∈ S ∩ B}
        ∂((volume : Measure (EuclideanSpace ℝ (Fin n))).toSphere)
  set c := ((n : ℝ≥0∞) * volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1))
  calc ENNReal.ofReal (Metric.diam S ^ (n - 1)) * I
      = (Metric.ediam S * (Metric.ediam S)⁻¹) * (c * c⁻¹) *
          ENNReal.ofReal (Metric.diam S ^ (n - 1)) * I := by
        rw [ENNReal.mul_inv_cancel hED0 hED, ENNReal.mul_inv_cancel hc0 hct]; ring
    _ = Metric.ediam S * c * ENNReal.ofReal (Metric.diam S ^ (n - 1)) *
          ((Metric.ediam S)⁻¹ * (c⁻¹ * I)) := by ring
    _ ≤ _ := by gcongr

lemma lineLength_translate {n : ℕ} (S : Set (EuclideanSpace ℝ (Fin n)))
    (z d : EuclideanSpace ℝ (Fin n)) (s : ℝ) :
    lineLength S (z + s • d) d = lineLength S z d := by
  unfold lineLength
  have : {t : ℝ | z + s • d + t • d ∈ S} = (fun t => s + t) ⁻¹' {t : ℝ | z + t • d ∈ S} := by
    ext t; simp [add_smul, add_assoc]
  rw [this, measure_preimage_add]

lemma stat_dir {n : ℕ} {S : Set (EuclideanSpace ℝ (Fin n))} (hSo : IsOpen S)
    (hSb : Bornology.IsBounded S) {B : Set (EuclideanSpace ℝ (Fin n))} (hB : MeasurableSet B)
    (d : EuclideanSpace ℝ (Fin n)) (hd : ‖d‖ = 1) :
    ∫⁻ y in S, (lineLength S y d)⁻¹ * volume {t : ℝ | y + t • d ∈ S ∩ B} = volume (S ∩ B) := by
  have hSm : MeasurableSet S := hSo.measurableSet
  have hSB : MeasurableSet (S ∩ B) := hSm.inter hB
  have hL : Measurable (fun y => lineLength S y d) :=
    measurable_measure_prodMk_left
      (s := {p : EuclideanSpace ℝ (Fin n) × ℝ | p.1 + p.2 • d ∈ S}) (hSm.preimage (by fun_prop))
  have hind : ∀ (A : Set (EuclideanSpace ℝ (Fin n))), MeasurableSet A →
      ∀ g : ℝ → EuclideanSpace ℝ (Fin n), Measurable g →
      ∫⁻ t : ℝ, A.indicator 1 (g t) = volume (g ⁻¹' A) := by
    intro A hA g hg
    rw [← lintegral_indicator_one (hA.preimage hg)]
    refine lintegral_congr fun t => ?_
    by_cases h : g t ∈ A
    · simp [h]
    · simp [h]
  have hvol : ∀ y : EuclideanSpace ℝ (Fin n), volume {t : ℝ | y + t • d ∈ S ∩ B} =
      ∫⁻ t : ℝ, (S ∩ B).indicator 1 (y + t • d) := fun y =>
    (hind (S ∩ B) hSB (fun t => y + t • d) (by fun_prop)).symm
  have hH : Measurable (fun p : EuclideanSpace ℝ (Fin n) × ℝ =>
      S.indicator 1 p.1 * (lineLength S p.1 d)⁻¹ * (S ∩ B).indicator 1 (p.1 + p.2 • d)) :=
    (((measurable_one.indicator hSm).comp measurable_fst).mul ((hL.comp measurable_fst).inv)).mul
      ((measurable_one.indicator hSB).comp (by fun_prop))
  have hK : Measurable (fun p : ℝ × EuclideanSpace ℝ (Fin n) =>
      S.indicator 1 (p.2 + -(p.1 • d)) * (lineLength S p.2 d)⁻¹ * (S ∩ B).indicator 1 p.2) :=
    (((measurable_one.indicator hSm).comp (by fun_prop)).mul ((hL.comp measurable_snd).inv)).mul
      ((measurable_one.indicator hSB).comp measurable_snd)
  calc ∫⁻ y in S, (lineLength S y d)⁻¹ * volume {t : ℝ | y + t • d ∈ S ∩ B}
      = ∫⁻ y, ∫⁻ t : ℝ, S.indicator 1 y * (lineLength S y d)⁻¹ * (S ∩ B).indicator 1 (y + t • d) := by
        rw [← lintegral_indicator hSm]
        refine lintegral_congr fun y => ?_
        by_cases hy : y ∈ S
        · simp only [Set.indicator_of_mem hy, Pi.one_apply, one_mul]
          rw [lintegral_const_mul' _ _ (ENNReal.inv_ne_top.2 (lineLength_pos hSo hy d hd).ne'),
            ← hvol]
        · simp [hy]
    _ = ∫⁻ t : ℝ, ∫⁻ y, S.indicator 1 y * (lineLength S y d)⁻¹ * (S ∩ B).indicator 1 (y + t • d) :=
        lintegral_lintegral_swap hH.aemeasurable
    _ = ∫⁻ t : ℝ, ∫⁻ z, S.indicator 1 (z + -(t • d)) * (lineLength S z d)⁻¹ * (S ∩ B).indicator 1 z := by
        refine lintegral_congr fun t => ?_
        rw [← lintegral_add_right_eq_self _ (-(t • d))]
        refine lintegral_congr fun z => ?_
        have : z + -(t • d) = z + (-t) • d := by rw [neg_smul]
        simp only [neg_add_cancel_right]
        rw [this, lineLength_translate]
    _ = ∫⁻ z, ∫⁻ t : ℝ, S.indicator 1 (z + -(t • d)) * (lineLength S z d)⁻¹ * (S ∩ B).indicator 1 z :=
        lintegral_lintegral_swap hK.aemeasurable
    _ = ∫⁻ z, (S ∩ B).indicator 1 z := by
        refine lintegral_congr fun z => ?_
        have hmeasS : Measurable (fun t : ℝ => S.indicator (1 : EuclideanSpace ℝ (Fin n) → ℝ≥0∞)
            (z + -(t • d))) := (measurable_one.indicator hSm).comp (by fun_prop)
        rw [lintegral_mul_const _ (hmeasS.mul_const _)]
        rw [lintegral_mul_const _ hmeasS]
        have hneg : ∫⁻ t : ℝ, S.indicator (1 : EuclideanSpace ℝ (Fin n) → ℝ≥0∞) (z + -(t • d)) =
            lineLength S z d := by
          rw [hind S hSm (fun t => z + -(t • d)) (by fun_prop)]
          unfold lineLength
          have : (fun t : ℝ => z + -(t • d)) ⁻¹' S = Neg.neg ⁻¹' {t : ℝ | z + t • d ∈ S} := by
            ext t; simp [neg_smul]
          rw [this, Measure.measure_preimage_neg]
        rw [hneg]
        by_cases hz : z ∈ S ∩ B
        · have h := ENNReal.mul_inv_cancel (lineLength_pos hSo hz.1 d hd).ne'
            (lineLength_ne_top hSb z d hd)
          simp only [Set.indicator_of_mem hz, Pi.one_apply, mul_one]
          exact h
        · simp [Set.indicator_of_notMem hz]
    _ = volume (S ∩ B) := lintegral_indicator_one hSB

lemma stat_set {n : ℕ} (hn : 1 ≤ n) {S : Set (EuclideanSpace ℝ (Fin n))} (hSo : IsOpen S)
    (hSb : Bornology.IsBounded S) {B : Set (EuclideanSpace ℝ (Fin n))} (hB : MeasurableSet B) :
    ∫⁻ y in S, rdKernel S y B = volume (S ∩ B) := by
  have := sphereUniform_prob hn
  have hSm : MeasurableSet S := hSo.measurableSet
  have hm : Measurable (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
      (lineLength S p.1 p.2)⁻¹ * volume {t : ℝ | p.1 + t • p.2 ∈ S ∩ B}) := by
    refine Measurable.mul ?_ ?_
    · exact (measurable_measure_prodMk_left
        (s := {q : (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) × ℝ |
          q.1.1 + q.2 • q.1.2 ∈ S}) (hSm.preimage (by fun_prop))).inv
    · exact measurable_measure_prodMk_left
        (s := {q : (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) × ℝ |
          q.1.1 + q.2 • q.1.2 ∈ S ∩ B}) ((hSm.inter hB).preimage (by fun_prop))
  calc ∫⁻ y in S, rdKernel S y B
      = ∫⁻ y in S, ∫⁻ d, (lineLength S y d)⁻¹ * volume {t : ℝ | y + t • d ∈ S ∩ B}
          ∂(sphereUniform n) := by
        refine setLIntegral_congr_fun hSm (fun y hy => ?_)
        rw [rd_apply hn hSm hy hB]
        exact lintegral_congr fun d => lineUniform_apply S y d hB
    _ = ∫⁻ d, (∫⁻ y in S, (lineLength S y d)⁻¹ * volume {t : ℝ | y + t • d ∈ S ∩ B})
          ∂(sphereUniform n) := lintegral_lintegral_swap hm.aemeasurable
    _ = ∫⁻ _d, volume (S ∩ B) ∂(sphereUniform n) :=
        lintegral_congr_ae (sphereUniform_ae_unit.mono fun d hd => stat_dir hSo hSb hB d hd)
    _ = volume (S ∩ B) := by rw [lintegral_const, measure_univ, mul_one]

lemma stationary {n : ℕ} (hn : 1 ≤ n) {S : Set (EuclideanSpace ℝ (Fin n))} (hSo : IsOpen S)
    (hSb : Bornology.IsBounded S) : rdKernel S ∘ₘ unif S = unif S := by
  ext B hB
  rw [Measure.bind_apply hB (Kernel.aemeasurable _), unif, lintegral_smul_measure,
    stat_set hn hSo hSb hB, Measure.smul_apply, Measure.restrict_apply hB, Set.inter_comm]


lemma enclosing {n : ℕ} (hn : 1 ≤ n) {S : Set (EuclideanSpace ℝ (Fin n))}
    (hSb : Bornology.IsBounded S) {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ S) :
    Metric.diam S ≤ 2 * enclosingRadius S ∧
      (volume S).toReal ≤ enclosingRadius S ^ n *
        (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1)).toReal := by
  set T := {r : ℝ | ∃ c : EuclideanSpace ℝ (Fin n), S ⊆ Metric.closedBall c r} with hT_def
  have hR : enclosingRadius S = sInf T := rfl
  have hT : T.Nonempty := by
    obtain ⟨r, hr⟩ := hSb.subset_closedBall x
    exact ⟨r, x, hr⟩
  have hT0 : ∀ r ∈ T, 0 ≤ r := fun r ⟨c, hc⟩ => dist_nonneg.trans (Metric.mem_closedBall.1 (hc hx))
  have hbdd : BddBelow T := ⟨0, hT0⟩
  have hvolT : ∀ r ∈ T, (volume S).toReal ≤ r ^ n *
      (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1)).toReal := by
    rintro r ⟨c, hc⟩
    have h1 := measure_mono (μ := volume) hc
    rw [Measure.addHaar_closedBall volume c (hT0 r ⟨c, hc⟩), finrank_euclideanSpace_fin] at h1
    have h2 := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      measure_ball_lt_top.ne) h1
    rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal (pow_nonneg (hT0 r ⟨c, hc⟩) _)] at h2
  refine ⟨?_, ?_⟩
  · have : Metric.diam S / 2 ≤ sInf T := by
      refine le_csInf hT fun r hr => ?_
      obtain ⟨c, hc⟩ := hr
      have h1 := Metric.diam_mono hc Metric.isBounded_closedBall
      have h2 := Metric.diam_closedBall (x := c) (hT0 r ⟨c, hc⟩)
      linarith
    rw [hR]; linarith
  · rw [hR]
    by_contra hcon
    push Not at hcon
    set Vb := (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1)).toReal
    have hev : ∀ᶠ r in nhds (sInf T), r ^ n * Vb < (volume S).toReal :=
      (((continuous_pow n).mul continuous_const).tendsto (sInf T)).eventually (gt_mem_nhds hcon)
    obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.1 hev
    obtain ⟨t, htT, htlt⟩ := exists_lt_of_csInf_lt hT (by linarith : sInf T < sInf T + δ / 2)
    have hR0 : 0 ≤ sInf T := le_csInf hT hT0
    have hVb : 0 ≤ Vb := ENNReal.toReal_nonneg
    have h1 := hvolT t htT
    have h2 : t ^ n * Vb ≤ (sInf T + δ / 2) ^ n * Vb :=
      mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (hT0 t htT) htlt.le _) hVb
    have h3 := hball (y := sInf T + δ / 2) (by
      rw [Real.dist_eq, add_sub_cancel_left, abs_of_pos (by linarith)]; linarith)
    linarith

lemma ediam_pos {n : ℕ} (hn : 1 ≤ n) {S : Set (EuclideanSpace ℝ (Fin n))} (hSo : IsOpen S)
    {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ S) : Metric.ediam S ≠ 0 := by
  set e : EuclideanSpace ℝ (Fin n) := EuclideanSpace.single (⟨0, hn⟩ : Fin n) (1 : ℝ)
  have he : ‖e‖ = 1 := by simp [e]
  exact ((lineLength_pos hSo hx e he).trans_le (lineLength_le S x e he)).ne'

lemma minor_eps {n : ℕ} (hn : 1 ≤ n) {S : Set (EuclideanSpace ℝ (Fin n))} (hSo : IsOpen S)
    (hSb : Bornology.IsBounded S) {y : EuclideanSpace ℝ (Fin n)} (hy : y ∈ S)
    {B : Set (EuclideanSpace ℝ (Fin n))} (hB : MeasurableSet B) (e : ℝ) (he0 : 0 ≤ e)
    (hreal : e * ((volume S).toReal)⁻¹ * (Metric.diam S * (n *
      (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1)).toReal) * Metric.diam S ^ (n - 1))
      ≤ 2) :
    ENNReal.ofReal e * unif S B ≤ rdKernel S y B := by
  have hm := minor hn hSo hSb hy hB
  have hED : Metric.ediam S ≠ ⊤ := hSb.ediam_ne_top
  have hED0 := ediam_pos hn hSo hy
  have hD : 0 < Metric.diam S := ENNReal.toReal_pos hED0 hED
  have hDr : ENNReal.ofReal (Metric.diam S) = Metric.ediam S := ENNReal.ofReal_toReal hED
  have hV0 : 0 < (volume S).toReal :=
    ENNReal.toReal_pos (hSo.measure_pos volume ⟨y, hy⟩).ne' hSb.measure_lt_top.ne
  have hVr : ENNReal.ofReal (volume S).toReal = volume S :=
    ENNReal.ofReal_toReal hSb.measure_lt_top.ne
  have hBr : ENNReal.ofReal (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1)).toReal =
      volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1) :=
    ENNReal.ofReal_toReal measure_ball_lt_top.ne
  have := nontriv_E hn
  have hc0 : ((n : ℝ≥0∞) * volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1)) ≠ 0 :=
    mul_ne_zero (by exact_mod_cast (by omega : n ≠ 0)) (Metric.measure_ball_pos _ _ one_pos).ne'
  have hct : ((n : ℝ≥0∞) * volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1)) ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.natCast_ne_top n) measure_ball_lt_top.ne
  set K := Metric.ediam S * ((n : ℝ≥0∞) * volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1)) *
      ENNReal.ofReal (Metric.diam S ^ (n - 1)) with hK
  have hK0 : K ≠ 0 := mul_ne_zero (mul_ne_zero hED0 hc0)
    (ENNReal.ofReal_pos.2 (pow_pos hD _)).ne'
  have hKt : K ≠ ⊤ := ENNReal.mul_ne_top (ENNReal.mul_ne_top hED hct) ENNReal.ofReal_ne_top
  have hconst : ENNReal.ofReal e * (volume S)⁻¹ * K ≤ 2 := by
    have heq : ENNReal.ofReal (e * ((volume S).toReal)⁻¹ * (Metric.diam S * (n *
        (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1)).toReal) * Metric.diam S ^ (n - 1)))
        = ENNReal.ofReal e * (volume S)⁻¹ * K := by
      rw [ENNReal.ofReal_mul (mul_nonneg he0 (inv_nonneg.2 hV0.le)), ENNReal.ofReal_mul he0,
        ENNReal.ofReal_mul (mul_nonneg hD.le (mul_nonneg (Nat.cast_nonneg n)
          ENNReal.toReal_nonneg)),
        ENNReal.ofReal_mul hD.le, ENNReal.ofReal_mul (Nat.cast_nonneg n), ENNReal.ofReal_natCast,
        ENNReal.ofReal_inv_of_pos hV0, hVr, hDr, hBr]
    rw [← heq]
    exact (ENNReal.ofReal_le_ofReal hreal).trans (by simp)
  refine (ENNReal.mul_le_mul_iff_right hK0 hKt).1 ?_
  rw [unif, Measure.smul_apply, Measure.restrict_apply hB, smul_eq_mul]
  calc K * (ENNReal.ofReal e * ((volume S)⁻¹ * volume (B ∩ S)))
      = (ENNReal.ofReal e * (volume S)⁻¹ * K) * volume (S ∩ B) := by
        rw [Set.inter_comm]; ring
    _ ≤ 2 * volume (S ∩ B) := by gcongr
    _ ≤ K * rdKernel S y B := hm

end SmithT3Aux

set_option maxHeartbeats 1000000 in
open SmithHitAndRun.RandomDir in
theorem solution {n : ℕ} (hn : 2 ≤ n)
    (S : Set (EuclideanSpace ℝ (Fin n))) (hSo : IsOpen S) (hSb : Bornology.IsBounded S)
    (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ S)
    (A : Set (EuclideanSpace ℝ (Fin n))) (hA : MeasurableSet A) (hAS : A ⊆ S)
    (m : ℕ) (hm : 1 ≤ m) :
    |(MarkovChainCLT.iterKernel (rdKernel S) m x A).toReal - (unif S A).toReal| <
      (1 - gammaRatio S / ((n : ℝ) * 2 ^ (n - 1))) ^ (m - 1) := by
  have hn1 : 1 ≤ n := by omega
  have hV0 : 0 < (volume S).toReal :=
    ENNReal.toReal_pos (hSo.measure_pos volume ⟨x, hx⟩).ne' hSb.measure_lt_top.ne
  have hprob : IsProbabilityMeasure (unif S) := ⟨by
    rw [unif, Measure.smul_apply, Measure.restrict_apply_univ, smul_eq_mul]
    exact ENNReal.inv_mul_cancel (hSo.measure_pos volume ⟨x, hx⟩).ne' hSb.measure_lt_top.ne⟩
  obtain ⟨hDR, hVR⟩ := SmithT3Aux.enclosing hn1 hSb hx
  set R := enclosingRadius S
  set Vb := (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1)).toReal
  set V := (volume S).toReal
  set D := Metric.diam S
  have := SmithT3Aux.nontriv_E hn1
  have hVb : 0 < Vb := ENNReal.toReal_pos (Metric.measure_ball_pos _ _ one_pos).ne'
    measure_ball_lt_top.ne
  have hRn : 0 < R ^ n * Vb := lt_of_lt_of_le hV0 hVR
  have hRn' : 0 < R ^ n := pos_of_mul_pos_left hRn hVb.le
  have hD0 : 0 ≤ D := Metric.diam_nonneg
  have hR0 : 0 ≤ R := by linarith
  have hR : 0 < R := by
    rcases hR0.lt_or_eq with h | h
    · exact h
    · rw [← h, zero_pow (by omega)] at hRn'; exact absurd hRn' (lt_irrefl 0)
  have hVr : (volume (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) R)).toReal = R ^ n * Vb := by
    rw [Measure.addHaar_closedBall volume 0 hR0, finrank_euclideanSpace_fin, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (pow_nonneg hR0 _)]
  have hgam : gammaRatio S = V / (R ^ n * Vb) := by rw [gammaRatio, hVr]
  set e := gammaRatio S / ((n : ℝ) * 2 ^ (n - 1)) with he_def
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  have hk : k + 1 - 1 = k := by omega
  rw [hk] at he_def
  have h2k : (1 : ℝ) ≤ 2 ^ k := one_le_pow₀ (by norm_num)
  have hkpos : (2 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by
    have : 2 ≤ k + 1 := hn
    exact_mod_cast this
  have he0 : 0 < e := by
    rw [he_def, hgam]; positivity
  have hgam1 : gammaRatio S ≤ 1 := by
    rw [hgam, div_le_one hRn]; exact hVR
  have he1 : e < 1 := by
    rw [he_def, div_lt_one (by positivity)]
    calc gammaRatio S ≤ 1 := hgam1
      _ < ((k + 1 : ℕ) : ℝ) * 2 ^ k := by nlinarith
  have hreal : e * V⁻¹ * (D * (((k + 1 : ℕ) : ℝ) * Vb) * D ^ (k + 1 - 1)) ≤ 2 := by
    rw [hk, he_def, hgam]
    have hDk : D ^ (k + 1) ≤ (2 * R) ^ (k + 1) := pow_le_pow_left₀ hD0 hDR _
    have hR2 : (0 : ℝ) < (2 * R) ^ (k + 1) := by positivity
    have hlhs : V / (R ^ (k + 1) * Vb) / (((k + 1 : ℕ) : ℝ) * 2 ^ k) * V⁻¹ *
        (D * (((k + 1 : ℕ) : ℝ) * Vb) * D ^ k) = 2 * (D ^ (k + 1) / (2 * R) ^ (k + 1)) := by
      field_simp
      ring
    rw [hlhs]
    have : D ^ (k + 1) / (2 * R) ^ (k + 1) ≤ 1 := (div_le_one hR2).2 hDk
    linarith
  have hmin : ∀ y ∈ S, ENNReal.ofReal e • unif S ≤ rdKernel S y := by
    intro y hy
    refine Measure.le_iff.2 fun B hB => ?_
    rw [Measure.smul_apply, smul_eq_mul]
    exact SmithT3Aux.minor_eps hn1 hSo hSb hy hB e he0.le hreal
  have key := SmithT3Aux.doeblin (rdKernel S) (unif S) S (SmithT3Aux.stationary hn1 hSo hSb)
    (fun y hy => SmithT3Aux.rd_univ hn1 hSo hSb hy) (fun y hy => SmithT3Aux.rd_compl hn1 hSo hy)
    (ENNReal.ofReal e) (ENNReal.ofReal_le_one.2 he1.le) hmin A hA m x hx
  rw [ENNReal.toReal_ofReal he0.le] at key
  obtain ⟨j, rfl⟩ : ∃ j, m = j + 1 := ⟨m - 1, by omega⟩
  rw [show j + 1 - 1 = j by omega]
  calc _ ≤ (1 - e) ^ (j + 1) := key.2
    _ < (1 - e) ^ j := by
      rw [pow_succ]
      exact mul_lt_of_lt_one_right (pow_pos (by linarith) _) (by linarith)
