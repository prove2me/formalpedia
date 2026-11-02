-- Prove2me | solution 1 for StochKolmogorov.Persist.eq_4_26
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-02T01:49:25.23148+00:00
-- url     : https://prove2.me/submissions/3464dd5f-3178-4c1c-b484-d5954059ed13

import Mathlib
import Definitions.Def_StochKolmogorov_Persist_Model
import Definitions.Def_StochKolmogorov_Persist_Persistence
import Definitions.Def_TotalVariationDist
import Theorems.Thm_StochKolmogorov_Persist_markov_property
import Theorems.Thm_StochKolmogorov_Persist_proposition_4_1
import Theorems.Thm_StochKolmogorov_Persist_eq_4_18
import Theorems.Thm_StochKolmogorov_Persist_kolmogorov_face_box_tv_overlap

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib

/-! HA (Harris route, s29): abstract Hairer-Mattingly contraction ("Yet another look at Harris'
ergodic theorem", Thm 3.1) in function form. Drift `QV ≤ γ V + K` plus pairwise overlap
`tvDist (Q x) (Q y) ≤ 1 - α` on `{V x + V y ≤ R}` (`R > 2K/(1-γ)`) make `Q` a strict contraction
for the weighted oscillation `|φ x - φ y| ≤ M (2 + β V x + β V y)`. -/

section HA
variable {X : Type*} [MeasurableSpace X]

theorem abs_sub_le_tvDist (μ ν : Measure X) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {A : Set X} (hA : MeasurableSet A) :
    |(μ A).toReal - (ν A).toReal| ≤ MarkovChainCLT.tvDist μ ν := by
  refine le_csSup ⟨1, ?_⟩ ⟨A, hA, rfl⟩
  rintro _ ⟨B, -, rfl⟩
  have h1 : (μ B).toReal ≤ 1 := by
    have := ENNReal.toReal_mono ENNReal.one_ne_top (prob_le_one (μ := μ) (s := B)); simpa using this
  have h2 : (ν B).toReal ≤ 1 := by
    have := ENNReal.toReal_mono ENNReal.one_ne_top (prob_le_one (μ := ν) (s := B)); simpa using this
  rw [abs_sub_le_iff]
  constructor <;> linarith [ENNReal.toReal_nonneg (a := μ B), ENNReal.toReal_nonneg (a := ν B)]

theorem tvDist_nonneg (μ ν : Measure X) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    0 ≤ MarkovChainCLT.tvDist μ ν :=
  (abs_nonneg _).trans (abs_sub_le_tvDist μ ν MeasurableSet.empty)

/-- Layer cake: for `0 ≤ ψ ≤ A`, `∫ ψ dμ ≤ ∫ ψ dν + A · tvDist μ ν`. -/
theorem integral_le_add_tv (μ ν : Measure X) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {ψ : X → ℝ} (hψm : Measurable ψ) {A : ℝ} (hA : 0 ≤ A) (h0 : ∀ z, 0 ≤ ψ z)
    (h1 : ∀ z, ψ z ≤ A) :
    ∫ z, ψ z ∂μ ≤ ∫ z, ψ z ∂ν + A * MarkovChainCLT.tvDist μ ν := by
  set tv := MarkovChainCLT.tvDist μ ν
  have htv0 : 0 ≤ tv := tvDist_nonneg μ ν
  have hmu := lintegral_eq_lintegral_meas_lt μ (ae_of_all _ h0) hψm.aemeasurable
  have hnu := lintegral_eq_lintegral_meas_lt ν (ae_of_all _ h0) hψm.aemeasurable
  have hpt : ∀ t ∈ Ioi (0 : ℝ), μ {a | t < ψ a} ≤
      ν {a | t < ψ a} + (Iio A).indicator (fun _ => ENNReal.ofReal tv) t := by
    intro t _
    by_cases ht : t < A
    · rw [indicator_of_mem (show t ∈ Iio A from ht)]
      have hm : MeasurableSet {a | t < ψ a} := measurableSet_lt measurable_const hψm
      have hab := abs_sub_le_tvDist μ ν hm
      rw [abs_sub_le_iff] at hab
      have hfin : ν {a | t < ψ a} ≠ ∞ := measure_ne_top _ _
      rw [← ENNReal.ofReal_toReal (measure_ne_top μ {a | t < ψ a}),
        ← ENNReal.ofReal_toReal hfin, ← ENNReal.ofReal_add ENNReal.toReal_nonneg htv0]
      exact ENNReal.ofReal_le_ofReal (by linarith [hab.1])
    · have he : {a | t < ψ a} = ∅ := by
        ext a; simp only [mem_setOf_eq, mem_empty_iff_false, iff_false, not_lt]
        exact (h1 a).trans (not_lt.1 ht)
      rw [he, measure_empty]; exact zero_le
  have key : ∫⁻ z, ENNReal.ofReal (ψ z) ∂μ ≤
      ∫⁻ z, ENNReal.ofReal (ψ z) ∂ν + ENNReal.ofReal (A * tv) := by
    rw [hmu, hnu]
    calc ∫⁻ t in Ioi 0, μ {a | t < ψ a}
        ≤ ∫⁻ t in Ioi 0, (ν {a | t < ψ a} + (Iio A).indicator (fun _ => ENNReal.ofReal tv) t) :=
          setLIntegral_mono' measurableSet_Ioi hpt
      _ = (∫⁻ t in Ioi 0, ν {a | t < ψ a}) +
            ∫⁻ t in Ioi 0, (Iio A).indicator (fun _ => ENNReal.ofReal tv) t :=
          lintegral_add_right _ (measurable_const.indicator (measurableSet_Iio (a := A)))
      _ ≤ (∫⁻ t in Ioi 0, ν {a | t < ψ a}) + ENNReal.ofReal (A * tv) := by
          gcongr
          rw [lintegral_indicator_const measurableSet_Iio, Measure.restrict_apply measurableSet_Iio]
          have : Iio A ∩ Ioi (0 : ℝ) = Ioo 0 A := by
            ext t; simp only [mem_inter_iff, mem_Iio, mem_Ioi, mem_Ioo]; tauto
          rw [this, Real.volume_Ioo, sub_zero, ← ENNReal.ofReal_mul htv0, mul_comm]
  have hfinν : ∫⁻ z, ENNReal.ofReal (ψ z) ∂ν ≠ ∞ := by
    refine ne_top_of_le_ne_top (b := ∫⁻ _, ENNReal.ofReal A ∂ν) ?_ ?_
    · rw [lintegral_const]; exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _)
    · exact lintegral_mono fun z => ENNReal.ofReal_le_ofReal (h1 z)
  rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ h0) hψm.aestronglyMeasurable,
    integral_eq_lintegral_of_nonneg_ae (ae_of_all _ h0) hψm.aestronglyMeasurable]
  have := ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨hfinν, ENNReal.ofReal_ne_top⟩) key
  rwa [ENNReal.toReal_add hfinν ENNReal.ofReal_ne_top, ENNReal.toReal_ofReal (by positivity)]
    at this

/-- `|∫ ψ dμ - ∫ ψ dν| ≤ 2 A tvDist μ ν` for `|ψ| ≤ A`. -/
theorem abs_integral_sub_le_tv (μ ν : Measure X) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {ψ : X → ℝ} (hψm : Measurable ψ) {A : ℝ} (hA : 0 ≤ A) (hψ : ∀ z, |ψ z| ≤ A) :
    |∫ z, ψ z ∂μ - ∫ z, ψ z ∂ν| ≤ 2 * A * MarkovChainCLT.tvDist μ ν := by
  have hint : ∀ m : Measure X, IsProbabilityMeasure m → Integrable ψ m := fun m _ =>
    (integrable_const A).mono' hψm.aestronglyMeasurable
      (ae_of_all _ fun z => by simpa [Real.norm_eq_abs] using hψ z)
  have hp : ∀ m : Measure X, IsProbabilityMeasure m → ∫ z, (ψ z + A) ∂m = ∫ z, ψ z ∂m + A :=
    fun m hm => by rw [integral_add (hint m hm) (integrable_const A)]; simp
  have hq : ∀ m : Measure X, IsProbabilityMeasure m → ∫ z, (A - ψ z) ∂m = A - ∫ z, ψ z ∂m :=
    fun m hm => by rw [integral_sub (integrable_const A) (hint m hm)]; simp
  have e1 := integral_le_add_tv μ ν (hψm.add_const A) (by linarith : 0 ≤ 2 * A)
    (fun z => by linarith [(abs_le.1 (hψ z)).1]) (fun z => by linarith [(abs_le.1 (hψ z)).2])
  have e2 := integral_le_add_tv μ ν (ψ := fun z => A - ψ z) (measurable_const.sub hψm) (by linarith : 0 ≤ 2 * A)
    (fun z => by linarith [(abs_le.1 (hψ z)).2]) (fun z => by linarith [(abs_le.1 (hψ z)).1])
  rw [hp μ inferInstance, hp ν inferInstance] at e1
  rw [hq μ inferInstance, hq ν inferInstance] at e2
  rw [abs_le]; constructor <;> linarith

theorem tvDist_comm (μ ν : Measure X) :
    MarkovChainCLT.tvDist ν μ = MarkovChainCLT.tvDist μ ν := by
  unfold MarkovChainCLT.tvDist
  congr 1
  ext r
  constructor <;> rintro ⟨B, hB, rfl⟩ <;> exact ⟨B, hB, abs_sub_comm _ _⟩

theorem clamp_resid {t A D : ℝ} (hA : 0 ≤ A) (hD : 0 ≤ D) (h : |t| ≤ A + D) :
    |t - max (-A) (min A t)| ≤ D := by
  rw [abs_le] at h
  rcases le_total t A with h1 | h1 <;> rcases le_total (-A) t with h2 | h2
  · rw [min_eq_right h1, max_eq_right h2, sub_self, abs_zero]; exact hD
  · rw [min_eq_right h1, max_eq_left h2, abs_le]; constructor <;> linarith
  · rw [min_eq_left h1, max_eq_right (by linarith : -A ≤ A), abs_le]; constructor <;> linarith
  · rw [min_eq_left h1, max_eq_right (by linarith : -A ≤ A), abs_le]; constructor <;> linarith

theorem clamp_abs_le {t A : ℝ} (hA : 0 ≤ A) : |max (-A) (min A t)| ≤ A := by
  rw [abs_le]; constructor
  · exact le_max_left _ _
  · exact max_le (by linarith) (min_le_left _ _)

/-- Hairer-Mattingly contraction step (function form). -/
theorem hm_contract (Q : X → Measure X) [hQ : ∀ x, IsProbabilityMeasure (Q x)] (V : X → ℝ)
    (hVm : Measurable V) (hV0 : ∀ x, 0 ≤ V x) (hVi : ∀ x, Integrable V (Q x))
    {γ K R α : ℝ} (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (hK : 0 < K) (hR : 2 * K < (1 - γ) * R)
    (hα : 0 < α) (hdrift : ∀ x, ∫ z, V z ∂Q x ≤ γ * V x + K)
    (hmin : ∀ x y, V x + V y ≤ R → MarkovChainCLT.tvDist (Q x) (Q y) ≤ 1 - α) :
    ∃ β : ℝ, 0 < β ∧ ∃ ab : ℝ, 0 ≤ ab ∧ ab < 1 ∧ ∀ (φ : X → ℝ) (M : ℝ), 0 ≤ M → Measurable φ →
      (∃ B, ∀ z, |φ z| ≤ B) → (∀ x y, |φ x - φ y| ≤ M * (2 + β * V x + β * V y)) →
      ∀ x y, |∫ z, φ z ∂Q x - ∫ z, φ z ∂Q y| ≤ ab * M * (2 + β * V x + β * V y) := by
  have hRpos : 0 < R := by nlinarith
  set β : ℝ := α / (2 * K) with hβdef
  have hβ : 0 < β := by positivity
  have hβK : β * (2 * K) = α := by rw [hβdef]; field_simp
  set γ0 : ℝ := (γ + 2 * K / R + 1) / 2 with hγ0def
  have hKR : 2 * K / R < 1 - γ := by rw [div_lt_iff₀ hRpos]; linarith
  have hγ0lt : γ0 < 1 := by rw [hγ0def]; linarith
  have hγγ0 : γ ≤ γ0 := by rw [hγ0def]; have : 0 ≤ 2 * K / R := by positivity
                           linarith
  have h2K : 2 * K ≤ (γ0 - γ) * R := by
    have e : (γ0 - γ) * R = (2 * K / R) * R / 2 + (1 - γ) * R / 2 := by rw [hγ0def]; ring
    rw [e, div_mul_cancel₀ _ hRpos.ne']; linarith
  set q : ℝ := (2 + R * β * γ0) / (2 + R * β) with hqdef
  have hq2 : q * (2 + R * β) = 2 + R * β * γ0 := by rw [hqdef]; field_simp
  have hγ0q : γ0 ≤ q := by
    rw [hqdef, le_div_iff₀ (by positivity)]; nlinarith
  set ab : ℝ := max (1 - α / 2) q with habdef
  have hab1 : ab < 1 := max_lt (by linarith) (by
    rw [hqdef, div_lt_one (by positivity)]
    have := mul_pos (mul_pos hRpos hβ) (sub_pos.2 hγ0lt); linarith)
  have hγ0nn : 0 ≤ γ0 := by rw [hγ0def]; positivity
  have hab0 : 0 ≤ ab := le_max_of_le_right (hγ0nn.trans hγ0q)
  have habq : q ≤ ab := le_max_right _ _
  have habα : 1 - α / 2 ≤ ab := le_max_left _ _
  have habR : ∀ s, R ≤ s → 2 + β * γ0 * s ≤ ab * (2 + β * s) := by
    intro s hs
    have h1 : q * (2 + β * s) = 2 + R * β * γ0 + q * β * (s - R) := by
      have : q * (2 + β * s) = q * (2 + R * β) + q * β * (s - R) := by ring
      rw [this, hq2]
    have h2 : γ0 * (β * (s - R)) ≤ q * (β * (s - R)) :=
      mul_le_mul_of_nonneg_right hγ0q (by have := sub_nonneg.2 hs; positivity)
    have h3 : q * (2 + β * s) ≤ ab * (2 + β * s) :=
      mul_le_mul_of_nonneg_right habq (by nlinarith)
    nlinarith
  refine ⟨β, hβ, ab, hab0, hab1, ?_⟩
  rintro φ M hM hφm ⟨B, hB⟩ hφ x y
  have hint : ∀ w, Integrable φ (Q w) := fun w =>
    (integrable_const B).mono' hφm.aestronglyMeasurable
      (ae_of_all _ fun z => by simpa [Real.norm_eq_abs] using hB z)
  have hbdd : BddAbove (Set.range fun z => φ z - M * (1 + β * V z)) := by
    refine ⟨B, ?_⟩
    rintro _ ⟨z, rfl⟩
    have : 0 ≤ M * (1 + β * V z) := by have := hV0 z; positivity
    linarith [le_abs_self (φ z), hB z]
  set c : ℝ := sSup (Set.range fun z => φ z - M * (1 + β * V z)) with hcdef
  have hc1 : ∀ z, φ z - M * (1 + β * V z) ≤ c := fun z => le_csSup hbdd ⟨z, rfl⟩
  have hc2 : ∀ z, c ≤ φ z + M * (1 + β * V z) := by
    intro z
    refine csSup_le ⟨_, ⟨x, rfl⟩⟩ ?_
    rintro _ ⟨w, rfl⟩
    have := (abs_le.1 (hφ w z)).2
    nlinarith
  set g : X → ℝ := fun z => φ z - c with hgdef
  have hgm : Measurable g := hφm.sub measurable_const
  have hgi : ∀ w, Integrable g (Q w) := fun w => (hint w).sub (integrable_const c)
  have hg : ∀ z, |g z| ≤ M + M * β * V z := by
    intro z
    rw [abs_le]; constructor <;> nlinarith [hc1 z, hc2 z]
  have he : ∀ w, ∫ z, g z ∂Q w = ∫ z, φ z ∂Q w - c := fun w => by
    rw [hgdef, integral_sub (hint w) (integrable_const c)]; simp
  have hdiff : ∫ z, φ z ∂Q x - ∫ z, φ z ∂Q y = ∫ z, g z ∂Q x - ∫ z, g z ∂Q y := by
    rw [he, he]; ring
  rw [hdiff]
  have hVint : ∀ w, ∫ z, (M * β * V z) ∂Q w = M * β * ∫ z, V z ∂Q w := fun w =>
    integral_const_mul _ _
  have hMβ : 0 ≤ M * β := by positivity
  have hVQ : ∀ w, M * β * ∫ z, V z ∂Q w ≤ M * β * (γ * V w + K) := fun w =>
    mul_le_mul_of_nonneg_left (hdrift w) hMβ
  by_cases hs : R ≤ V x + V y
  · -- far case
    have hA : ∀ w, |∫ z, g z ∂Q w| ≤ M + M * β * (γ * V w + K) := by
      intro w
      have hb : Integrable (fun z => M + M * β * V z) (Q w) :=
        (integrable_const M).add ((hVi w).const_mul (M * β))
      calc |∫ z, g z ∂Q w| = ‖∫ z, g z ∂Q w‖ := (Real.norm_eq_abs _).symm
        _ ≤ ∫ z, ‖g z‖ ∂Q w := norm_integral_le_integral_norm _
        _ ≤ ∫ z, (M + M * β * V z) ∂Q w :=
            integral_mono (hgi w).norm hb fun z => by simpa [Real.norm_eq_abs] using hg z
        _ = M + M * β * ∫ z, V z ∂Q w := by
            rw [integral_add (integrable_const M) ((hVi w).const_mul (M * β)), hVint]; simp
        _ ≤ M + M * β * (γ * V w + K) := by linarith [hVQ w]
    have hsum := abs_sub (∫ z, g z ∂Q x) (∫ z, g z ∂Q y)
    have h1 : M * β * (2 * K) ≤ M * β * ((γ0 - γ) * (V x + V y)) :=
      mul_le_mul_of_nonneg_left (h2K.trans (mul_le_mul_of_nonneg_left hs (by linarith))) hMβ
    have h2 : M * (2 + β * γ0 * (V x + V y)) ≤ M * (ab * (2 + β * (V x + V y))) :=
      mul_le_mul_of_nonneg_left (habR _ hs) hM
    nlinarith [hA x, hA y]
  · -- near case: overlap
    push_neg at hs
    have htv := hmin x y hs.le
    set gb : X → ℝ := fun z => max (-M) (min M (g z)) with hgbdef
    set gu : X → ℝ := fun z => g z - gb z with hgudef
    have hgbm : Measurable gb := measurable_const.max (measurable_const.min hgm)
    have hgb : ∀ z, |gb z| ≤ M := fun z => clamp_abs_le hM
    have hgu : ∀ z, |gu z| ≤ M * β * V z := fun z =>
      clamp_resid hM (by have := hV0 z; positivity) (hg z)
    have hgbi : ∀ w, Integrable gb (Q w) := fun w =>
      (integrable_const M).mono' hgbm.aestronglyMeasurable
        (ae_of_all _ fun z => by simpa [Real.norm_eq_abs] using hgb z)
    have hgui : ∀ w, Integrable gu (Q w) := fun w => (hgi w).sub (hgbi w)
    have hsplit : ∀ w, ∫ z, g z ∂Q w = ∫ z, gb z ∂Q w + ∫ z, gu z ∂Q w := fun w => by
      rw [← integral_add (hgbi w) (hgui w)]; congr 1; ext z; simp [hgudef]
    have hU : ∀ w, |∫ z, gu z ∂Q w| ≤ M * β * (γ * V w + K) := by
      intro w
      calc |∫ z, gu z ∂Q w| = ‖∫ z, gu z ∂Q w‖ := (Real.norm_eq_abs _).symm
        _ ≤ ∫ z, ‖gu z‖ ∂Q w := norm_integral_le_integral_norm _
        _ ≤ ∫ z, (M * β * V z) ∂Q w :=
            integral_mono (hgui w).norm ((hVi w).const_mul (M * β))
              fun z => by simpa [Real.norm_eq_abs] using hgu z
        _ = M * β * ∫ z, V z ∂Q w := hVint w
        _ ≤ M * β * (γ * V w + K) := hVQ w
    have hTV := abs_integral_sub_le_tv (Q x) (Q y) hgbm hM hgb
    have hTV' : 2 * M * MarkovChainCLT.tvDist (Q x) (Q y) ≤ 2 * M * (1 - α) :=
      mul_le_mul_of_nonneg_left htv (by positivity)
    rw [hsplit, hsplit]
    have hsum := abs_sub (∫ z, gu z ∂Q x) (∫ z, gu z ∂Q y)
    have habs : |∫ z, gb z ∂Q x + ∫ z, gu z ∂Q x - (∫ z, gb z ∂Q y + ∫ z, gu z ∂Q y)| ≤
        |∫ z, gb z ∂Q x - ∫ z, gb z ∂Q y| + |∫ z, gu z ∂Q x - ∫ z, gu z ∂Q y| := by
      have := abs_add_le (∫ z, gb z ∂Q x - ∫ z, gb z ∂Q y) (∫ z, gu z ∂Q x - ∫ z, gu z ∂Q y)
      rw [show ∫ z, gb z ∂Q x + ∫ z, gu z ∂Q x - (∫ z, gb z ∂Q y + ∫ z, gu z ∂Q y) =
        (∫ z, gb z ∂Q x - ∫ z, gb z ∂Q y) + (∫ z, gu z ∂Q x - ∫ z, gu z ∂Q y) by ring]
      exact this
    have k1 : M * (2 * (1 - α / 2)) ≤ M * (2 * ab) := mul_le_mul_of_nonneg_left (by linarith) hM
    have k2 : M * β * (γ * (V x + V y)) ≤ M * β * (ab * (V x + V y)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (hγγ0.trans (hγ0q.trans habq))
        (by linarith [hV0 x, hV0 y])) hMβ
    have k3 : M * β * (2 * K) = M * α := by rw [mul_assoc, hβK]
    linarith [hU x, hU y]

/-- Iterated Hairer-Mattingly contraction: `φ (k+1) = Q φ k`, `|φ 0| ≤ 1` gives
`|φ k x - φ k y| ≤ ab^k (2 + β V x + β V y)`. -/
theorem hm_iterate (Q : X → Measure X) [hQ : ∀ x, IsProbabilityMeasure (Q x)] (V : X → ℝ)
    (hVm : Measurable V) (hV0 : ∀ x, 0 ≤ V x) (hVi : ∀ x, Integrable V (Q x))
    {γ K R α : ℝ} (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (hK : 0 < K) (hR : 2 * K < (1 - γ) * R)
    (hα : 0 < α) (hdrift : ∀ x, ∫ z, V z ∂Q x ≤ γ * V x + K)
    (hmin : ∀ x y, V x + V y ≤ R → MarkovChainCLT.tvDist (Q x) (Q y) ≤ 1 - α) :
    ∃ β : ℝ, 0 < β ∧ ∃ ab : ℝ, 0 ≤ ab ∧ ab < 1 ∧ ∀ φ : ℕ → X → ℝ, (∀ k, Measurable (φ k)) →
      (∀ z, |φ 0 z| ≤ 1) → (∀ k x, φ (k + 1) x = ∫ z, φ k z ∂Q x) →
      ∀ k x y, |φ k x - φ k y| ≤ ab ^ k * (2 + β * V x + β * V y) := by
  obtain ⟨β, hβ, ab, hab0, hab1, hstep⟩ :=
    hm_contract Q V hVm hV0 hVi hγ0 hγ1 hK hR hα hdrift hmin
  refine ⟨β, hβ, ab, hab0, hab1, ?_⟩
  intro φ hφm h0 hrec
  have hb : ∀ k z, |φ k z| ≤ 1 := by
    intro k
    induction k with
    | zero => exact h0
    | succ k ih =>
      intro z
      rw [hrec]
      have := norm_integral_le_of_norm_le_const (μ := Q z) (f := φ k) (C := 1)
        (ae_of_all _ fun w => by rw [Real.norm_eq_abs]; exact ih w)
      simpa [Real.norm_eq_abs] using this
  intro k
  induction k with
  | zero =>
    intro x y
    have h1 := abs_sub (φ 0 x) (φ 0 y)
    have := mul_nonneg hβ.le (hV0 x)
    have := mul_nonneg hβ.le (hV0 y)
    rw [pow_zero, one_mul]
    linarith [h0 x, h0 y]
  | succ k ih =>
    intro x y
    rw [hrec, hrec]
    have := hstep (φ k) (ab ^ k) (pow_nonneg hab0 k) (hφm k) ⟨1, hb k⟩ ih x y
    calc _ ≤ ab * ab ^ k * (2 + β * V x + β * V y) := this
      _ = ab ^ (k + 1) * (2 + β * V x + β * V y) := by ring

end HA
end ItoLib

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib

/-! HB (Harris route, s30): iterates of a Markov kernel, drift iteration, and the TV-Cauchy
estimate for `kpow κ k x` coming from `hm_iterate` (HA). -/

section HB
variable {X : Type*} [MeasurableSpace X]

/-- `k`-step kernel, `kpow κ (k+1) = kpow κ k ∘ₖ κ`. -/
noncomputable def kpow (κ : Kernel X X) : ℕ → Kernel X X
  | 0 => Kernel.id
  | k + 1 => kpow κ k ∘ₖ κ

theorem kpow_zero (κ : Kernel X X) : kpow κ 0 = Kernel.id := rfl
theorem kpow_succ (κ : Kernel X X) (k : ℕ) : kpow κ (k + 1) = kpow κ k ∘ₖ κ := rfl

theorem kpow_isMarkov (κ : Kernel X X) [IsMarkovKernel κ] (k : ℕ) : IsMarkovKernel (kpow κ k) := by
  induction k with
  | zero => rw [kpow_zero]; infer_instance
  | succ k ih => rw [kpow_succ]; infer_instance

theorem kpow_add (κ : Kernel X X) (j k : ℕ) : kpow κ (j + k) = kpow κ j ∘ₖ kpow κ k := by
  induction k with
  | zero => simp [kpow_zero]
  | succ k ih => rw [← add_assoc, kpow_succ, ih, kpow_succ, Kernel.comp_assoc]

theorem kpow_one (κ : Kernel X X) : kpow κ 1 = κ := by
  rw [kpow_succ, kpow_zero, Kernel.id_comp]

theorem kpow_succ' (κ : Kernel X X) (k : ℕ) : kpow κ (k + 1) = κ ∘ₖ kpow κ k := by
  rw [add_comm, kpow_add, kpow_one]

/-- Drift in lintegral form iterates: `∫⁻ V d(kpow k x) ≤ γ^k V x + K/(1-γ)`. -/
theorem kpow_lintegral_V (κ : Kernel X X) [IsMarkovKernel κ] (V : X → ℝ) (hVm : Measurable V)
    (hV0 : ∀ x, 0 ≤ V x) {γ K : ℝ} (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (hK : 0 ≤ K)
    (hdl : ∀ x, ∫⁻ z, ENNReal.ofReal (V z) ∂κ x ≤ ENNReal.ofReal (γ * V x + K)) (k : ℕ) (x : X) :
    ∫⁻ z, ENNReal.ofReal (V z) ∂kpow κ k x ≤ ENNReal.ofReal (γ ^ k * V x + K / (1 - γ)) := by
  have hD : 0 ≤ K / (1 - γ) := div_nonneg hK (by linarith)
  induction k generalizing x with
  | zero =>
    rw [kpow_zero, Kernel.id_apply, lintegral_dirac' _ hVm.ennreal_ofReal]
    exact ENNReal.ofReal_le_ofReal (by rw [pow_zero, one_mul]; linarith)
  | succ k ih =>
    haveI := kpow_isMarkov κ k
    rw [kpow_succ', Kernel.lintegral_comp _ _ _ hVm.ennreal_ofReal]
    calc ∫⁻ b, ∫⁻ c, ENNReal.ofReal (V c) ∂κ b ∂kpow κ k x
        ≤ ∫⁻ b, ENNReal.ofReal (γ * V b + K) ∂kpow κ k x := lintegral_mono fun b => hdl b
      _ = ENNReal.ofReal γ * ∫⁻ b, ENNReal.ofReal (V b) ∂kpow κ k x + ENNReal.ofReal K := by
          have e : ∀ b, ENNReal.ofReal (γ * V b + K) = ENNReal.ofReal γ * ENNReal.ofReal (V b) +
              ENNReal.ofReal K := fun b => by
            rw [ENNReal.ofReal_add (mul_nonneg hγ0 (hV0 b)) hK, ENNReal.ofReal_mul hγ0]
          simp_rw [e]
          rw [lintegral_add_right _ measurable_const, lintegral_const_mul _
            hVm.ennreal_ofReal, lintegral_const, measure_univ, mul_one]
      _ ≤ ENNReal.ofReal γ * ENNReal.ofReal (γ ^ k * V x + K / (1 - γ)) + ENNReal.ofReal K := by
          gcongr; exact ih x
      _ = ENNReal.ofReal (γ ^ (k + 1) * V x + K / (1 - γ)) := by
          rw [← ENNReal.ofReal_mul hγ0, ← ENNReal.ofReal_add (mul_nonneg hγ0 (add_nonneg (mul_nonneg (pow_nonneg hγ0 _) (hV0 x)) hD)) hK]
          congr 1
          have h1 : (1 - γ) ≠ 0 := by linarith
          field_simp
          ring

theorem kpow_V_integrable (κ : Kernel X X) [IsMarkovKernel κ] (V : X → ℝ) (hVm : Measurable V)
    (hV0 : ∀ x, 0 ≤ V x) {γ K : ℝ} (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (hK : 0 ≤ K)
    (hdl : ∀ x, ∫⁻ z, ENNReal.ofReal (V z) ∂κ x ≤ ENNReal.ofReal (γ * V x + K)) (k : ℕ) (x : X) :
    Integrable V (kpow κ k x) ∧ ∫ z, V z ∂kpow κ k x ≤ γ ^ k * V x + K / (1 - γ) := by
  have hl := kpow_lintegral_V κ V hVm hV0 hγ0 hγ1 hK hdl k x
  have hlt : ∫⁻ z, ENNReal.ofReal (V z) ∂kpow κ k x < ⊤ := lt_of_le_of_lt hl ENNReal.ofReal_lt_top
  have hint : Integrable V (kpow κ k x) := by
    refine ⟨hVm.aestronglyMeasurable, ?_⟩
    unfold HasFiniteIntegral
    have e : ∀ z, ‖V z‖ₑ = ENNReal.ofReal (V z) := fun z => Real.enorm_of_nonneg (hV0 z)
    simp_rw [e]; exact hlt
  refine ⟨hint, ?_⟩
  rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ hV0) hVm.aestronglyMeasurable]
  have hD : 0 ≤ γ ^ k * V x + K / (1 - γ) :=
    add_nonneg (mul_nonneg (pow_nonneg hγ0 _) (hV0 x)) (div_nonneg hK (by linarith))
  exact ENNReal.toReal_le_of_le_ofReal hD hl

theorem kpow_toReal_le_one (κ : Kernel X X) [IsMarkovKernel κ] (k : ℕ) (x : X) (A : Set X) :
    |(kpow κ k x A).toReal| ≤ 1 := by
  haveI := kpow_isMarkov κ k
  rw [abs_of_nonneg ENNReal.toReal_nonneg]
  exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by rw [ENNReal.ofReal_one]; exact prob_le_one)

theorem kpow_toReal_add (κ : Kernel X X) [IsMarkovKernel κ] (k j : ℕ) {A : Set X}
    (hA : MeasurableSet A) (x : X) :
    (kpow κ (k + j) x A).toReal = ∫ z, (kpow κ k z A).toReal ∂kpow κ j x := by
  haveI := kpow_isMarkov κ k
  rw [kpow_add, Kernel.comp_apply' _ _ _ hA, integral_toReal
    ((kpow κ k).measurable_coe hA).aemeasurable (ae_of_all _ fun z => measure_lt_top _ _)]

theorem kpow_toReal_succ (κ : Kernel X X) [IsMarkovKernel κ] (k : ℕ) {A : Set X}
    (hA : MeasurableSet A) (x : X) :
    (kpow κ (k + 1) x A).toReal = ∫ z, (kpow κ k z A).toReal ∂κ x := by
  rw [kpow_toReal_add κ k 1 hA x, kpow_one]

/-- TV-Cauchy estimate for the iterates (Hairer-Mattingly + drift iteration). -/
theorem kpow_cauchy (κ : Kernel X X) [IsMarkovKernel κ] (V : X → ℝ)
    (hVm : Measurable V) (hV0 : ∀ x, 0 ≤ V x) (hVi : ∀ x, Integrable V (κ x))
    {γ K R α : ℝ} (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (hK : 0 < K) (hR : 2 * K < (1 - γ) * R)
    (hα : 0 < α) (hdrift : ∀ x, ∫ z, V z ∂κ x ≤ γ * V x + K)
    (hmin : ∀ x y, V x + V y ≤ R → MarkovChainCLT.tvDist (κ x) (κ y) ≤ 1 - α) :
    ∃ β : ℝ, 0 < β ∧ ∃ ab : ℝ, 0 ≤ ab ∧ ab < 1 ∧
      (∀ k x y (A : Set X), MeasurableSet A →
        |(kpow κ k x A).toReal - (kpow κ k y A).toReal| ≤ ab ^ k * (2 + β * V x + β * V y)) ∧
      (∀ k j x (A : Set X), MeasurableSet A →
        |(kpow κ (k + j) x A).toReal - (kpow κ k x A).toReal| ≤
          ab ^ k * (2 + 2 * β * V x + β * (K / (1 - γ)))) := by
  obtain ⟨β, hβ, ab, hab0, hab1, hit⟩ :=
    hm_iterate (⇑κ) V hVm hV0 hVi hγ0 hγ1 hK hR hα hdrift hmin
  have hdl : ∀ x, ∫⁻ z, ENNReal.ofReal (V z) ∂κ x ≤ ENNReal.ofReal (γ * V x + K) := fun x => by
    rw [← ofReal_integral_eq_lintegral_ofReal (hVi x) (ae_of_all _ hV0)]
    exact ENNReal.ofReal_le_ofReal (hdrift x)
  have hosc : ∀ (A : Set X), MeasurableSet A → ∀ k x y,
      |(kpow κ k x A).toReal - (kpow κ k y A).toReal| ≤ ab ^ k * (2 + β * V x + β * V y) :=
    fun A hA => hit (fun k x => (kpow κ k x A).toReal)
      (fun k => ((kpow κ k).measurable_coe hA).ennreal_toReal)
      (fun z => kpow_toReal_le_one κ 0 z A) (fun k x => kpow_toReal_succ κ k hA x)
  refine ⟨β, hβ, ab, hab0, hab1, fun k x y A hA => hosc A hA k x y, ?_⟩
  intro k j x A hA
  haveI := kpow_isMarkov κ j
  obtain ⟨hVint, hVle⟩ := kpow_V_integrable κ V hVm hV0 hγ0 hγ1 hK.le hdl j x
  set φ : X → ℝ := fun z => (kpow κ k z A).toReal with hφ
  have hφm : Measurable φ := ((kpow κ k).measurable_coe hA).ennreal_toReal
  have hφi : Integrable φ (kpow κ j x) :=
    (integrable_const (1 : ℝ)).mono' hφm.aestronglyMeasurable
      (ae_of_all _ fun z => by rw [Real.norm_eq_abs]; exact kpow_toReal_le_one κ k z A)
  rw [kpow_toReal_add κ k j hA x]
  have e : (kpow κ k x A).toReal = ∫ _z, φ x ∂(kpow κ j x) := by simp [φ]
  rw [e, ← integral_sub hφi (integrable_const _)]
  set c1 : ℝ := ab ^ k * (2 + β * V x) with hc1
  set c2 : ℝ := ab ^ k * β with hc2
  have hc2n : 0 ≤ c2 := mul_nonneg (pow_nonneg hab0 _) hβ.le
  have hgi : Integrable (fun z => c1 + c2 * V z) (kpow κ j x) :=
    (integrable_const c1).add (hVint.const_mul c2)
  have hpt : ∀ z, |φ z - φ x| ≤ c1 + c2 * V z := fun z =>
    le_of_le_of_eq (hosc A hA k z x) (by rw [hc1, hc2]; ring)
  have hgint : ∫ z, (c1 + c2 * V z) ∂kpow κ j x = c1 + c2 * ∫ z, V z ∂kpow κ j x := by
    have h1 : ∫ z, c2 * V z ∂kpow κ j x = c2 * ∫ z, V z ∂kpow κ j x := integral_const_mul c2 _
    rw [integral_add (integrable_const c1) (hVint.const_mul c2), h1]
    congr 1; simp
  have hγj : γ ^ j * V x ≤ V x := mul_le_of_le_one_left (hV0 x) (pow_le_one₀ hγ0 hγ1.le)
  have key : c2 * ∫ z, V z ∂kpow κ j x ≤ c2 * (V x + K / (1 - γ)) :=
    mul_le_mul_of_nonneg_left (by linarith) hc2n
  calc |∫ z, (φ z - φ x) ∂kpow κ j x| ≤ ∫ z, |φ z - φ x| ∂kpow κ j x :=
        abs_integral_le_integral_abs
    _ ≤ ∫ z, (c1 + c2 * V z) ∂kpow κ j x :=
        integral_mono_of_nonneg (ae_of_all _ fun z => abs_nonneg _) hgi (ae_of_all _ hpt)
    _ ≤ ab ^ k * (2 + 2 * β * V x + β * (K / (1 - γ))) := by
        rw [hgint]
        have : ab ^ k * (2 + 2 * β * V x + β * (K / (1 - γ))) = c1 + c2 * (V x + K / (1 - γ)) := by
          rw [hc1, hc2]; ring
        linarith

/-- A sequence of probability measures that is uniformly Cauchy on measurable sets converges
setwise (uniformly) to a probability measure. -/
theorem exists_limit_measure (μ : ℕ → Measure X) [hμ : ∀ k, IsProbabilityMeasure (μ k)] (e : ℕ → ℝ)
    (he : Tendsto e atTop (𝓝 0))
    (hc : ∀ k j (A : Set X), MeasurableSet A → |(μ (k + j) A).toReal - (μ k A).toReal| ≤ e k) :
    ∃ π : Measure X, IsProbabilityMeasure π ∧
      ∀ k (A : Set X), MeasurableSet A → |(μ k A).toReal - (π A).toReal| ≤ e k := by
  set s : Set X → ℕ → ℝ := fun A k => (μ k A).toReal with hs
  have hs01 : ∀ A k, 0 ≤ s A k ∧ s A k ≤ 1 := fun A k =>
    ⟨ENNReal.toReal_nonneg, ENNReal.toReal_le_of_le_ofReal zero_le_one
      (by rw [ENNReal.ofReal_one]; exact prob_le_one)⟩
  have hev : ∀ ε : ℝ, 0 < ε → ∃ N, ∀ n ≥ N, e n < ε := fun ε hε =>
    Filter.eventually_atTop.1 (he.eventually (gt_mem_nhds hε))
  have hcs : ∀ A, MeasurableSet A → CauchySeq (s A) := by
    intro A hA
    rw [Metric.cauchySeq_iff']
    intro ε hε
    obtain ⟨N, hN⟩ := hev ε hε
    refine ⟨N, fun n hn => ?_⟩
    obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hn
    rw [Real.dist_eq]; exact lt_of_le_of_lt (hc N j A hA) (hN N le_rfl)
  set L : Set X → ℝ := fun A => limUnder atTop (s A) with hLdef
  have hL : ∀ A, MeasurableSet A → Tendsto (s A) atTop (𝓝 (L A)) := fun A hA =>
    (hcs A hA).tendsto_limUnder
  have hbd : ∀ A, MeasurableSet A → ∀ k, |s A k - L A| ≤ e k := by
    intro A hA k
    have ht : Tendsto (fun j => |s A k - (s A ∘ fun a => a + k) j|) atTop (𝓝 |s A k - L A|) :=
      (tendsto_const_nhds.sub ((hL A hA).comp (tendsto_add_atTop_nat k))).abs
    refine le_of_tendsto' ht fun j => ?_
    show |s A k - s A (j + k)| ≤ e k
    rw [add_comm j k, abs_sub_comm]; exact hc k j A hA
  have hL01 : ∀ A, MeasurableSet A → 0 ≤ L A ∧ L A ≤ 1 := fun A hA =>
    ⟨ge_of_tendsto' (hL A hA) fun k => (hs01 A k).1, le_of_tendsto' (hL A hA) fun k => (hs01 A k).2⟩
  have hLe : L ∅ = 0 := tendsto_nhds_unique (hL ∅ MeasurableSet.empty)
    (by simp only [hs, measure_empty, ENNReal.toReal_zero]; exact tendsto_const_nhds)
  have hLu : L univ = 1 := tendsto_nhds_unique (hL univ MeasurableSet.univ)
    (by simp only [hs, measure_univ, ENNReal.toReal_one]; exact tendsto_const_nhds)
  have hfin : ∀ (f : ℕ → Set X), (∀ i, MeasurableSet (f i)) → Pairwise (Function.onFun Disjoint f) → ∀ n,
      ∑ i ∈ Finset.range n, L (f i) = L (⋃ i ∈ Finset.range n, f i) := by
    intro f hf hd n
    have hU : MeasurableSet (⋃ i ∈ Finset.range n, f i) :=
      Finset.measurableSet_biUnion _ fun i _ => hf i
    refine tendsto_nhds_unique (tendsto_finset_sum _ fun i _ => hL (f i) (hf i)) ?_
    have : (fun k => ∑ i ∈ Finset.range n, s (f i) k) = s (⋃ i ∈ Finset.range n, f i) := by
      funext k; simp only [hs]
      rw [measure_biUnion_finset (fun i _ j _ hij => hd hij) (fun i _ => hf i),
        ENNReal.toReal_sum (fun i _ => measure_ne_top _ _)]
    rw [this]; exact hL _ hU
  have hcount : ∀ (f : ℕ → Set X), (∀ i, MeasurableSet (f i)) → Pairwise (Function.onFun Disjoint f) →
      HasSum (fun i => L (f i)) (L (⋃ i, f i)) := by
    intro f hf hd
    have hU : MeasurableSet (⋃ i, f i) := MeasurableSet.iUnion hf
    rw [hasSum_iff_tendsto_nat_of_nonneg (fun i => (hL01 _ (hf i)).1)]
    simp_rw [hfin f hf hd]
    set U : ℕ → Set X := fun n => ⋃ i ∈ Finset.range n, f i with hUdef
    have hUm : ∀ n, MeasurableSet (U n) := fun n => Finset.measurableSet_biUnion _ fun i _ => hf i
    have hmono : Monotone U := fun a b hab =>
      Set.biUnion_subset_biUnion_left (by intro i hi; simp only [Finset.coe_range, Set.mem_Iio] at hi ⊢; omega)
    have hUU : ⋃ n, U n = ⋃ i, f i := by
      ext z; simp only [hUdef, Set.mem_iUnion, Finset.mem_range, exists_prop]
      constructor
      · rintro ⟨n, i, -, hz⟩; exact ⟨i, hz⟩
      · rintro ⟨i, hz⟩; exact ⟨i + 1, i, by omega, hz⟩
    have hk : ∀ k, Tendsto (fun n => s (U n) k) atTop (𝓝 (s (⋃ i, f i) k)) := by
      intro k
      have h := tendsto_measure_iUnion_atTop (μ := μ k) hmono
      rw [hUU] at h
      exact (ENNReal.tendsto_toReal (measure_ne_top _ _)).comp h
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨k, hk3⟩ := hev (ε / 3) (by positivity)
    obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 (hk k) (ε / 3) (by positivity)
    refine ⟨N, fun n hn => ?_⟩
    have h1 := hbd (U n) (hUm n) k
    have h2 := hbd (⋃ i, f i) hU k
    have h3 := hN n hn
    have h4 := hk3 k le_rfl
    rw [Real.dist_eq] at h3 ⊢
    obtain ⟨a1, a2⟩ := abs_le.1 h1
    obtain ⟨b1, b2⟩ := abs_le.1 h2
    obtain ⟨c1, c2⟩ := abs_lt.1 h3
    rw [abs_lt]; constructor <;> linarith
  let π : Measure X := Measure.ofMeasurable (fun A _ => ENNReal.ofReal (L A)) (by simp [hLe])
    (fun f hf hd => by
      rw [(hcount f hf hd).tsum_eq.symm,
        ENNReal.ofReal_tsum_of_nonneg (fun i => (hL01 _ (hf i)).1) (hcount f hf hd).summable])
  have hπA : ∀ A, MeasurableSet A → π A = ENNReal.ofReal (L A) := fun A hA =>
    Measure.ofMeasurable_apply A hA
  refine ⟨π, ⟨by rw [hπA _ MeasurableSet.univ, hLu, ENNReal.ofReal_one]⟩, fun k A hA => ?_⟩
  rw [hπA A hA, ENNReal.toReal_ofReal (hL01 A hA).1]
  exact hbd A hA k

theorem tvDist_le_of_forall (μ ν : Measure X) {c : ℝ}
    (h : ∀ A : Set X, MeasurableSet A → |(μ A).toReal - (ν A).toReal| ≤ c) :
    MarkovChainCLT.tvDist μ ν ≤ c :=
  csSup_le ⟨_, ∅, MeasurableSet.empty, rfl⟩ (by rintro _ ⟨A, hA, rfl⟩; exact h A hA)

theorem eq_of_abs_le_geom {a b ab c : ℝ} (hab0 : 0 ≤ ab) (hab1 : ab < 1)
    (h : ∀ k : ℕ, |a - b| ≤ ab ^ k * c) : a = b := by
  have h0 := ge_of_tendsto' ((tendsto_pow_atTop_nhds_zero_of_lt_one hab0 hab1).mul_const c) h
  rw [zero_mul] at h0
  exact sub_eq_zero.1 (abs_nonpos_iff.1 h0)

/-- Set-wise invariance for `κ` gives set-wise invariance for every iterate. -/
theorem kpow_inv (κ : Kernel X X) [IsMarkovKernel κ] (ν : Measure X)
    (hν : ∀ A, MeasurableSet A → ∫⁻ z, κ z A ∂ν = ν A) (k : ℕ) (A : Set X) (hA : MeasurableSet A) :
    ∫⁻ z, kpow κ k z A ∂ν = ν A := by
  have hb : ν.bind κ = ν := Measure.ext fun B hB => by
    rw [Measure.bind_apply hB κ.aemeasurable]; exact hν B hB
  induction k generalizing A with
  | zero =>
    simp_rw [kpow_zero, Kernel.id_apply, Measure.dirac_apply' _ hA]
    exact lintegral_indicator_one hA
  | succ k ih =>
    simp_rw [kpow_succ, Kernel.comp_apply' _ _ _ hA]
    rw [← Measure.lintegral_bind κ.aemeasurable ((kpow κ k).measurable_coe hA).aemeasurable, hb]
    exact ih A hA

/-- **Harris theorem (existence, uniqueness, geometric TV convergence)** for a Markov kernel with
a Lyapunov drift and pairwise overlap on a large sublevel set (Hairer-Mattingly). -/
theorem harris_exists (κ : Kernel X X) [IsMarkovKernel κ] (V : X → ℝ)
    (hVm : Measurable V) (hV0 : ∀ x, 0 ≤ V x) (hVi : ∀ x, Integrable V (κ x))
    {γ K R α : ℝ} (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (hK : 0 < K) (hR : 2 * K < (1 - γ) * R)
    (hα : 0 < α) (hdrift : ∀ x, ∫ z, V z ∂κ x ≤ γ * V x + K)
    (hmin : ∀ x y, V x + V y ≤ R → MarkovChainCLT.tvDist (κ x) (κ y) ≤ 1 - α) (x0 : X) :
    ∃ π : Measure X, IsProbabilityMeasure π ∧
      (∀ A, MeasurableSet A → ∫⁻ z, κ z A ∂π = π A) ∧
      (∀ ν : Measure X, IsProbabilityMeasure ν →
        (∀ A, MeasurableSet A → ∫⁻ z, κ z A ∂ν = ν A) → ν = π) ∧
      ∃ ab C : ℝ, 0 ≤ ab ∧ ab < 1 ∧ 0 ≤ C ∧
        ∀ k x, MarkovChainCLT.tvDist (kpow κ k x) π ≤ ab ^ k * (C * (1 + V x)) := by
  obtain ⟨β, hβ, ab, hab0, hab1, hosc, hcau⟩ :=
    kpow_cauchy κ V hVm hV0 hVi hγ0 hγ1 hK hR hα hdrift hmin
  have hP : ∀ k x, IsProbabilityMeasure (kpow κ k x) := fun k x => by
    have := kpow_isMarkov κ k; infer_instance
  have hD : 0 ≤ K / (1 - γ) := div_nonneg hK.le (by linarith)
  set C0 : ℝ := 2 + 2 * β * V x0 + β * (K / (1 - γ)) with hC0
  have hC0n : 0 ≤ C0 := by have := hV0 x0; positivity
  have hgeo : Tendsto (fun k : ℕ => ab ^ k * C0) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hab0 hab1).mul_const C0
  obtain ⟨π, hπ, hlim⟩ := exists_limit_measure (hμ := fun k => hP k x0) (fun k => kpow κ k x0)
    (fun k => ab ^ k * C0) hgeo (fun k j A hA => hcau k j x0 A hA)
  -- pointwise set bound
  have hset : ∀ k x (A : Set X), MeasurableSet A →
      |(kpow κ k x A).toReal - (π A).toReal| ≤ ab ^ k * ((2 + β * V x + β * V x0) + C0) := by
    intro k x A hA
    have h1 := hosc k x x0 A hA
    have h2 := hlim k A hA
    calc |(kpow κ k x A).toReal - (π A).toReal|
        ≤ |(kpow κ k x A).toReal - (kpow κ k x0 A).toReal| +
            |(kpow κ k x0 A).toReal - (π A).toReal| := abs_sub_le _ _ _
      _ ≤ ab ^ k * (2 + β * V x + β * V x0) + ab ^ k * C0 := add_le_add h1 h2
      _ = ab ^ k * ((2 + β * V x + β * V x0) + C0) := by ring
  set C : ℝ := 2 + β * V x0 + C0 + β with hC
  have hCn : 0 ≤ C := by have := hV0 x0; positivity
  have htv : ∀ k x, MarkovChainCLT.tvDist (kpow κ k x) π ≤ ab ^ k * (C * (1 + V x)) := by
    intro k x
    refine tvDist_le_of_forall _ _ fun A hA => (hset k x A hA).trans ?_
    have hv := hV0 x
    have hx : 0 ≤ (2 + β * V x0 + C0) * V x := mul_nonneg (by have := hV0 x0; positivity) hv
    have e : ab ^ k * (C * (1 + V x)) = ab ^ k * ((2 + β * V x + β * V x0) + C0) +
        ab ^ k * (β + (2 + β * V x0 + C0) * V x) := by rw [hC]; ring
    rw [e]
    have : 0 ≤ ab ^ k * (β + (2 + β * V x0 + C0) * V x) :=
      mul_nonneg (pow_nonneg hab0 _) (by linarith)
    linarith
  refine ⟨π, hπ, ?_, ?_, ab, C, hab0, hab1, hCn, htv⟩
  · -- invariance
    intro A hA
    set g : X → ℝ := fun z => (κ z A).toReal with hg
    have hgm : Measurable g := (κ.measurable_coe hA).ennreal_toReal
    have hgb : ∀ z, |g z| ≤ 1 := fun z => by
      rw [hg, abs_of_nonneg ENNReal.toReal_nonneg]
      exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by rw [ENNReal.ofReal_one]; exact prob_le_one)
    have hstep : ∀ k, (kpow κ (k + 1) x0 A).toReal = ∫ z, g z ∂kpow κ k x0 := fun k => by
      rw [kpow_succ', Kernel.comp_apply' _ _ _ hA, integral_toReal (κ.measurable_coe hA).aemeasurable
        (ae_of_all _ fun z => measure_lt_top _ _)]
    have hpi : (∫⁻ z, κ z A ∂π).toReal = ∫ z, g z ∂π := by
      rw [integral_toReal (κ.measurable_coe hA).aemeasurable (ae_of_all _ fun z => measure_lt_top _ _)]
    have hreal : ∫ z, g z ∂π = (π A).toReal := by
      refine eq_of_abs_le_geom hab0 hab1 (c := 2 * C0 + C0) fun k => ?_
      have h1 := abs_integral_sub_le_tv (kpow κ k x0) π hgm zero_le_one hgb
      have h2 : MarkovChainCLT.tvDist (kpow κ k x0) π ≤ ab ^ k * C0 :=
        tvDist_le_of_forall _ _ fun B hB => hlim k B hB
      have h3 := hlim (k + 1) A hA
      rw [← hstep k] at h1
      have h4 : ab ^ (k + 1) * C0 ≤ ab ^ k * C0 := by
        rw [pow_succ]; exact mul_le_mul_of_nonneg_right
          (mul_le_of_le_one_right (pow_nonneg hab0 _) hab1.le) hC0n
      calc |∫ z, g z ∂π - (π A).toReal|
          ≤ |(kpow κ (k + 1) x0 A).toReal - ∫ z, g z ∂π| +
              |(kpow κ (k + 1) x0 A).toReal - (π A).toReal| := by
            rw [abs_sub_comm (kpow κ (k + 1) x0 A).toReal]; exact abs_sub_le _ _ _
        _ ≤ 2 * 1 * (ab ^ k * C0) + ab ^ (k + 1) * C0 := by
            gcongr
            · exact h1.trans (by gcongr)
        _ ≤ ab ^ k * (2 * C0 + C0) := by nlinarith
    have hfin : ∫⁻ z, κ z A ∂π ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top
      (le_trans (lintegral_mono fun z => prob_le_one) (by simp))
    exact (ENNReal.toReal_eq_toReal_iff' hfin (measure_ne_top _ _)).1 (hpi.trans hreal)
  · -- uniqueness
    intro ν hν hinv
    refine Measure.ext fun A hA => ?_
    refine (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).1 ?_
    set F : ℕ → X → ℝ := fun k z => (kpow κ k z A).toReal with hF
    have hconst : ∀ k, ∫ z, F k z ∂ν = (ν A).toReal := fun k => by
      rw [hF, integral_toReal ((kpow κ k).measurable_coe hA).aemeasurable
        (ae_of_all _ fun z => measure_lt_top _ _), kpow_inv κ ν hinv k A hA]
    have hlimF : Tendsto (fun k => ∫ z, F k z ∂ν) atTop (𝓝 (∫ _z, (π A).toReal ∂ν)) := by
      refine tendsto_integral_of_dominated_convergence (fun _ => (1 : ℝ))
        (fun k => ((kpow κ k).measurable_coe hA).ennreal_toReal.aestronglyMeasurable)
        (integrable_const _) (fun k => ae_of_all _ fun z => ?_) (ae_of_all _ fun z => ?_)
      · rw [Real.norm_eq_abs]; exact kpow_toReal_le_one κ k z A
      · rw [tendsto_iff_norm_sub_tendsto_zero]
        have hg := (tendsto_pow_atTop_nhds_zero_of_lt_one hab0 hab1).mul_const
          ((2 + β * V z + β * V x0) + C0)
        rw [zero_mul] at hg
        refine squeeze_zero (fun k => norm_nonneg _) (fun k => ?_) hg
        rw [Real.norm_eq_abs]; exact hset k z A hA
    simp_rw [hconst] at hlimF
    rw [integral_const, smul_eq_mul] at hlimF
    simp only [ENNReal.toReal_one, one_mul, probReal_univ] at hlimF
    exact tendsto_nhds_unique tendsto_const_nhds hlimF

end HB
end ItoLib

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib

/-! HC (s30): TV contraction of a Markov kernel (for moving core_overlap from small T to the
skeleton step via Chapman-Kolmogorov). -/

section HC
variable {X Z : Type*} [MeasurableSpace X] [MeasurableSpace Z]

/-- `tvDist (μ η) (ν η) ≤ tvDist μ ν` for a Markov kernel `η`. -/
theorem tvDist_bind_le (μ ν : Measure X) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (η : Kernel X Z) [IsMarkovKernel η] :
    MarkovChainCLT.tvDist (μ.bind η) (ν.bind η) ≤ MarkovChainCLT.tvDist μ ν := by
  refine tvDist_le_of_forall _ _ fun A hA => ?_
  set ψ : X → ℝ := fun z => (η z A).toReal with hψ
  have hψm : Measurable ψ := (η.measurable_coe hA).ennreal_toReal
  have h0 : ∀ z, 0 ≤ ψ z := fun z => ENNReal.toReal_nonneg
  have h1 : ∀ z, ψ z ≤ 1 := fun z =>
    ENNReal.toReal_le_of_le_ofReal zero_le_one (by rw [ENNReal.ofReal_one]; exact prob_le_one)
  have e : ∀ m : Measure X, ((m.bind η) A).toReal = ∫ z, ψ z ∂m := fun m => by
    rw [Measure.bind_apply hA η.aemeasurable, integral_toReal (η.measurable_coe hA).aemeasurable
      (ae_of_all _ fun z => measure_lt_top _ _)]
  rw [e μ, e ν]
  have a1 := integral_le_add_tv μ ν hψm zero_le_one h0 h1
  have a2 := integral_le_add_tv ν μ hψm zero_le_one h0 h1
  have a3 : MarkovChainCLT.tvDist ν μ = MarkovChainCLT.tvDist μ ν := tvDist_comm _ _
  rw [abs_le]; constructor <;> linarith

end HC
end ItoLib


open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib

/-! EHA (8ab663e7 s1): abstract skeleton Harris. From a transition family `tr` with Markov kernels
agreeing on `Or`, Chapman-Kolmogorov, invariance of `U ⊆ Or`, a drift `W` for the step `τ` on `U`
and a TV overlap at SOME time `T₀` on every sublevel set of `W`, the `τ`-skeleton has an invariant
law `π` on `U` with geometric TV convergence `tv(tr (kτ) x, π) ≤ Cx r^k`. -/

section EHA
variable {S : Type*} [MeasurableSpace S]

theorem eh_kpow_kpow (κ : Kernel S S) (m k : ℕ) : kpow (kpow κ m) k = kpow κ (m * k) := by
  induction k with
  | zero => rw [Nat.mul_zero, kpow_zero, kpow_zero]
  | succ k ih => rw [kpow_succ, ih, show m * (k + 1) = m * k + m by ring, kpow_add]

theorem eh_bind_comp (μ : Measure S) (κ η : Kernel S S) :
    μ.bind (η ∘ₖ κ) = (μ.bind κ).bind η := by
  rw [Measure.bind_bind κ.aemeasurable η.aemeasurable]
  congr 1

theorem eh_inv_iff (κ : Kernel S S) (ν : Measure S) :
    (∀ A, MeasurableSet A → ∫⁻ z, κ z A ∂ν = ν A) ↔ ν.bind κ = ν := by
  constructor
  · intro h
    ext A hA
    rw [Measure.bind_apply hA κ.aemeasurable]
    exact h A hA
  · intro h A hA
    rw [← Measure.bind_apply hA κ.aemeasurable, h]

theorem eh_bind_congr (U : Set S) (μ : Measure S) (hμ : μ Uᶜ = 0) (η η' : Kernel S S)
    (h : ∀ y ∈ U, η y = η' y) : μ.bind η = μ.bind η' := by
  ext A hA
  rw [Measure.bind_apply hA η.aemeasurable, Measure.bind_apply hA η'.aemeasurable]
  refine lintegral_congr_ae ?_
  filter_upwards [(mem_ae_iff.2 hμ : ∀ᵐ x ∂μ, x ∈ U)] with y hy
  rw [h y hy]

theorem eh_tv_le_one (μ ν : Measure S) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    MarkovChainCLT.tvDist μ ν ≤ 1 := by
  refine tvDist_le_of_forall _ _ fun A _ => ?_
  have h1 : (μ A).toReal ≤ 1 := by
    have := prob_le_one (μ := μ) (s := A)
    exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using this)
  have h2 : (ν A).toReal ≤ 1 := by
    have := prob_le_one (μ := ν) (s := A)
    exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using this)
  have h3 : 0 ≤ (μ A).toReal := ENNReal.toReal_nonneg
  have h4 : 0 ≤ (ν A).toReal := ENNReal.toReal_nonneg
  rw [abs_le]; constructor <;> linarith

theorem eh_kernel_ck (Or : Set S) (tr : ℝ≥0 → S → Measure S) (κ : ℝ≥0 → Kernel S S)
    (hκx : ∀ t, ∀ x ∈ Or, κ t x = tr t x)
    (hCK : ∀ (s t : ℝ≥0) (x : S), x ∈ Or → ∀ A : Set S, MeasurableSet A →
      tr (s + t) x A = ∫⁻ y, tr t y A ∂(tr s x))
    (hOr : ∀ t, ∀ x ∈ Or, tr t x Orᶜ = 0) (s t : ℝ≥0) {x : S} (hx : x ∈ Or) :
    κ (s + t) x = (κ s x).bind (κ t) := by
  ext A hA
  rw [hκx _ x hx, hCK s t x hx A hA, Measure.bind_apply hA (κ t).aemeasurable, hκx s x hx]
  refine lintegral_congr_ae ?_
  filter_upwards [(mem_ae_iff.2 (hOr s x hx) : ∀ᵐ y ∂(tr s x), y ∈ Or)] with y hy
  rw [hκx t y hy]

/-- Exponent bookkeeping: `ab^q ≤ (1/b) ρ^k` for `k = m q + r`, `r < m`, `ρ = b^(1/m)`. -/
theorem eh_rate {ab b : ℝ} (hab0 : 0 ≤ ab) (hb : ab ≤ b) (hb0 : 0 < b) (hb1 : b ≤ 1) (m k : ℕ)
    (hm : 0 < m) :
    ab ^ (k / m) ≤ (1 / b) * (b ^ (1 / (m : ℝ))) ^ k := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hq : ab ^ (k / m) ≤ b ^ (k / m) := pow_le_pow_left₀ hab0 hb _
  have hk : (k : ℝ) / m ≤ ((k / m : ℕ) : ℝ) + 1 := by
    have h1 : k < m * (k / m + 1) := by
      have := Nat.lt_div_mul_add hm (a := k)
      nlinarith [Nat.div_add_mod k m, Nat.mod_lt k hm]
    have h2 : (k : ℝ) < m * (((k / m : ℕ) : ℝ) + 1) := by exact_mod_cast h1
    rw [div_le_iff₀ hmR]; linarith
  have hpow : (b ^ (1 / (m : ℝ))) ^ k = b ^ ((k : ℝ) / m) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hb0.le]; congr 1; field_simp
  have hge : b ^ ((((k / m : ℕ) : ℝ) + 1)) ≤ b ^ ((k : ℝ) / m) :=
    Real.rpow_le_rpow_of_exponent_ge hb0 hb1 hk
  have hq1 : b ^ ((((k / m : ℕ) : ℝ) + 1)) = b ^ (k / m) * b := by
    rw [Real.rpow_add hb0, Real.rpow_natCast, Real.rpow_one]
  rw [hpow]
  rw [hq1] at hge
  have : b ^ (k / m) ≤ (1 / b) * b ^ ((k : ℝ) / m) := by
    rw [one_div, ← div_eq_inv_mul, le_div_iff₀ hb0]; exact hge
  linarith

open Classical in
theorem skel_harris (U Or : Set S) (hUm : MeasurableSet U) (hUOr : U ⊆ Or) (x0 : S) (hx0 : x0 ∈ U)
    (tr : ℝ≥0 → S → Measure S) (κ : ℝ≥0 → Kernel S S) (hκM : ∀ t, IsMarkovKernel (κ t))
    (hκx : ∀ t, ∀ x ∈ Or, κ t x = tr t x)
    (hCK : ∀ (s t : ℝ≥0) (x : S), x ∈ Or → ∀ A : Set S, MeasurableSet A →
      tr (s + t) x A = ∫⁻ y, tr t y A ∂(tr s x))
    (hOr : ∀ t, ∀ x ∈ Or, tr t x Orᶜ = 0)
    (hU : ∀ t, ∀ x ∈ U, tr t x Uᶜ = 0)
    (τ : ℝ≥0) (hτ : 0 < τ) (W : S → ℝ) (hWm : Measurable W) (hW0 : ∀ x ∈ U, 0 ≤ W x)
    {γ K : ℝ} (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (hK : 0 < K)
    (hdrift : ∀ x ∈ U, ∫⁻ z, ENNReal.ofReal (W z) ∂(tr τ x) ≤ ENNReal.ofReal (γ * W x + K))
    (hovl : ∀ R : ℝ, ∃ T₀ : ℝ≥0, ∃ ε : ℝ, 0 < ε ∧ ∀ x ∈ U, ∀ y ∈ U, W x ≤ R → W y ≤ R →
      MarkovChainCLT.tvDist (tr T₀ x) (tr T₀ y) ≤ 1 - ε) :
    ∃ π : Measure S, IsProbabilityMeasure π ∧ π Uᶜ = 0 ∧
      (∀ A, MeasurableSet A → ∫⁻ x, tr τ x A ∂π = π A) ∧
      ∃ r : ℝ, 0 < r ∧ r < 1 ∧ ∀ x ∈ U, ∃ Cx : ℝ, 0 < Cx ∧ ∀ k : ℕ,
        MarkovChainCLT.tvDist (tr (k * τ) x) π ≤ Cx * r ^ k := by
  -- constants
  set K₁ : ℝ := K + |W x0| with hK₁
  have hK₁ : 0 < K₁ := by positivity
  have h1γ : 0 < 1 - γ := by linarith
  set R : ℝ := 2 * K₁ / (1 - γ) ^ 2 + 1 with hR
  have hRpos : 0 < R := by positivity
  set R0 : ℝ := R + 1 with hR0
  obtain ⟨T₀, ε, hε, hov⟩ := hovl R
  -- the kernel
  set Q : Kernel S S := Kernel.piecewise hUm (κ τ) (Kernel.const S (Measure.dirac x0)) with hQ
  haveI : IsMarkovKernel (κ τ) := hκM τ
  have hQM : IsMarkovKernel Q := by rw [hQ]; infer_instance
  have hQ1 : ∀ x ∈ U, Q x = tr τ x := fun x hx => by
    rw [hQ, Kernel.piecewise_apply, if_pos hx, hκx τ x (hUOr hx)]
  have hQ2 : ∀ x, x ∉ U → Q x = Measure.dirac x0 := fun x hx => by
    rw [hQ, Kernel.piecewise_apply, if_neg hx, Kernel.const_apply]
  have hQ3 : ∀ x, Q x Uᶜ = 0 := fun x => by
    by_cases hx : x ∈ U
    · rw [hQ1 x hx]; exact hU τ x hx
    · rw [hQ2 x hx, Measure.dirac_apply' _ hUm.compl]
      simp [hx0]
  -- iterates
  have hQP : ∀ k : ℕ, ∀ x ∈ U, kpow Q (k + 1) x = tr (((k + 1 : ℕ) : ℝ≥0) * τ) x := by
    intro k
    induction k with
    | zero => intro x hx; rw [zero_add, kpow_one, hQ1 x hx]; simp
    | succ k ih =>
      intro x hx
      rw [kpow_succ, Kernel.comp_apply, hQ1 x hx]
      have hb : (tr τ x).bind (kpow Q (k + 1)) = (tr τ x).bind (κ (((k + 1 : ℕ) : ℝ≥0) * τ)) :=
        eh_bind_congr U _ (hU τ x hx) _ _ fun y hy => by
          rw [ih y hy, hκx _ y (hUOr hy)]
      rw [hb, ← hκx τ x (hUOr hx), ← eh_kernel_ck Or tr κ hκx hCK hOr τ _ (hUOr hx),
        hκx _ x (hUOr hx)]
      congr 1
      push_cast; ring
  -- V
  set V : S → ℝ := fun x => if x ∈ U then W x else R0 with hV
  have hVm : Measurable V := Measurable.ite hUm hWm measurable_const
  have hV0 : ∀ x, 0 ≤ V x := fun x => by
    by_cases hx : x ∈ U
    · simp only [hV, if_pos hx]; exact hW0 x hx
    · simp only [hV, if_neg hx]; linarith
  have hVU : ∀ x ∈ U, V x = W x := fun x hx => by simp only [hV, if_pos hx]
  have hdl : ∀ x, ∫⁻ z, ENNReal.ofReal (V z) ∂Q x ≤ ENNReal.ofReal (γ * V x + K₁) := by
    intro x
    by_cases hx : x ∈ U
    · rw [hQ1 x hx]
      have he : ∫⁻ z, ENNReal.ofReal (V z) ∂tr τ x = ∫⁻ z, ENNReal.ofReal (W z) ∂tr τ x := by
        refine lintegral_congr_ae ?_
        filter_upwards [(mem_ae_iff.2 (hU τ x hx) : ∀ᵐ y ∂(tr τ x), y ∈ U)] with y hy
        rw [hVU y hy]
      rw [he, hVU x hx]
      refine (hdrift x hx).trans (ENNReal.ofReal_le_ofReal ?_)
      have := abs_nonneg (W x0); linarith
    · rw [hQ2 x hx, lintegral_dirac' _ hVm.ennreal_ofReal, hVU x0 hx0]
      refine ENNReal.ofReal_le_ofReal ?_
      have h1 : W x0 ≤ |W x0| := le_abs_self _
      have h2 : 0 ≤ γ * V x := mul_nonneg hγ0 (hV0 x)
      linarith
  -- the m-step kernel
  set m : ℕ := ⌈(T₀ / τ : ℝ≥0)⌉₊ + 1 with hm
  have hm0 : 0 < m := Nat.succ_pos _
  have hT₀m : T₀ ≤ (m : ℝ≥0) * τ := by
    have h1 : T₀ / τ ≤ (⌈(T₀ / τ : ℝ≥0)⌉₊ : ℝ≥0) := Nat.le_ceil _
    have h2 : T₀ = T₀ / τ * τ := by rw [div_mul_cancel₀ _ hτ.ne']
    calc T₀ = T₀ / τ * τ := h2
      _ ≤ (⌈(T₀ / τ : ℝ≥0)⌉₊ : ℝ≥0) * τ := by gcongr
      _ ≤ (m : ℝ≥0) * τ := by
        gcongr
        rw [hm]; exact_mod_cast le_self_add
  set Q' : Kernel S S := kpow Q m with hQ'
  haveI hQ'M : IsMarkovKernel Q' := kpow_isMarkov Q m
  have hQ'U : ∀ x ∈ U, Q' x = tr ((m : ℝ≥0) * τ) x := fun x hx => by
    have := hQP (m - 1) x hx
    rw [Nat.sub_add_cancel hm0] at this
    exact this
  have hγm1 : γ ^ m < 1 := pow_lt_one₀ hγ0 hγ1 hm0.ne'
  have hγm0 : 0 ≤ γ ^ m := pow_nonneg hγ0 m
  have hγmγ : γ ^ m ≤ γ := pow_le_of_le_one hγ0 hγ1.le hm0.ne'
  have hint := kpow_V_integrable Q V hVm hV0 hγ0 hγ1 hK₁.le hdl m
  have hRK : 2 * (K₁ / (1 - γ)) < (1 - γ ^ m) * R := by
    have e1 : (1 - γ) * R = 2 * K₁ / (1 - γ) + (1 - γ) := by
      rw [hR]; field_simp; try ring
    have e2 : (1 - γ) * R ≤ (1 - γ ^ m) * R :=
      mul_le_mul_of_nonneg_right (by linarith) hRpos.le
    have e3 : 2 * (K₁ / (1 - γ)) = 2 * K₁ / (1 - γ) := by ring
    linarith
  have hmin : ∀ x y, V x + V y ≤ R → MarkovChainCLT.tvDist (Q' x) (Q' y) ≤ 1 - ε := by
    intro x y hxy
    have hxU : x ∈ U := by
      by_contra hx
      have : V x = R0 := by simp only [hV, if_neg hx]
      have := hV0 y; linarith
    have hyU : y ∈ U := by
      by_contra hy
      have : V y = R0 := by simp only [hV, if_neg hy]
      have := hV0 x; linarith
    have hWx : W x ≤ R := by have := hV0 y; rw [hVU x hxU] at hxy; linarith
    have hWy : W y ≤ R := by have := hV0 x; rw [hVU y hyU] at hxy; linarith
    rw [hQ'U x hxU, hQ'U y hyU]
    have hsplit : (m : ℝ≥0) * τ = T₀ + ((m : ℝ≥0) * τ - T₀) := (add_tsub_cancel_of_le hT₀m).symm
    haveI : IsMarkovKernel (κ ((m : ℝ≥0) * τ - T₀)) := hκM _
    haveI : IsProbabilityMeasure (κ T₀ x) := (hκM T₀).isProbabilityMeasure x
    haveI : IsProbabilityMeasure (κ T₀ y) := (hκM T₀).isProbabilityMeasure y
    rw [hsplit, ← hκx _ x (hUOr hxU), ← hκx _ y (hUOr hyU),
      eh_kernel_ck Or tr κ hκx hCK hOr _ _ (hUOr hxU),
      eh_kernel_ck Or tr κ hκx hCK hOr _ _ (hUOr hyU)]
    refine (tvDist_bind_le _ _ _).trans ?_
    rw [hκx _ x (hUOr hxU), hκx _ y (hUOr hyU)]
    exact hov x hxU y hyU hWx hWy
  obtain ⟨π, hπP, hπinv, hπuniq, ab, Cc, hab0, hab1, hC0, hrate⟩ :=
    harris_exists Q' V hVm hV0 (fun x => (hint x).1) hγm0 hγm1 (div_pos hK₁ h1γ) hRK hε
      (fun x => (hint x).2) hmin x0
  -- π is Q-invariant
  have hπb : π.bind Q' = π := (eh_inv_iff Q' π).1 hπinv
  have hQinv : π.bind Q = π := by
    haveI : IsProbabilityMeasure (π.bind Q) := by
      constructor
      rw [Measure.bind_apply MeasurableSet.univ Q.aemeasurable]
      simp
    refine hπuniq _ inferInstance ((eh_inv_iff Q' _).2 ?_)
    rw [← eh_bind_comp, hQ', ← kpow_succ, kpow_succ', eh_bind_comp, hπb]
  have hπU : π Uᶜ = 0 := by
    rw [← hQinv, Measure.bind_apply hUm.compl Q.aemeasurable]
    simp [hQ3]
  refine ⟨π, hπP, hπU, ?_, ?_⟩
  · intro A hA
    have : ∫⁻ x, tr τ x A ∂π = ∫⁻ x, Q x A ∂π := by
      refine lintegral_congr_ae ?_
      filter_upwards [(mem_ae_iff.2 hπU : ∀ᵐ y ∂π, y ∈ U)] with y hy
      rw [hQ1 y hy]
    rw [this, ← Measure.bind_apply hA Q.aemeasurable, hQinv]
  · set b : ℝ := max ab (1 / 2) with hb
    have hb0 : 0 < b := lt_of_lt_of_le (by norm_num) (le_max_right _ _)
    have hb1 : b < 1 := max_lt hab1 (by norm_num)
    have hmR : (0 : ℝ) < 1 / (m : ℝ) := by
      have : (0 : ℝ) < m := by exact_mod_cast hm0
      positivity
    refine ⟨b ^ (1 / (m : ℝ)), Real.rpow_pos_of_pos hb0 _, Real.rpow_lt_one hb0.le hb1 hmR, ?_⟩
    intro x hx
    have hCx0 : 0 ≤ Cc * (1 + V x) / b := by have := hV0 x; positivity
    refine ⟨Cc * (1 + V x) / b + 1, by linarith, ?_⟩
    intro k
    have hρ0 : 0 ≤ (b ^ (1 / (m : ℝ))) ^ k := by
      have := Real.rpow_pos_of_pos hb0 (1 / (m : ℝ)); positivity
    have hρ1 : (b ^ (1 / (m : ℝ))) ^ k ≤ 1 :=
      pow_le_one₀ (Real.rpow_pos_of_pos hb0 _).le (Real.rpow_lt_one hb0.le hb1 hmR).le
    rcases Nat.eq_zero_or_pos k with hk | hk
    · subst hk
      haveI : IsProbabilityMeasure (tr ((0 : ℕ) * τ) x) := by
        rw [← hκx _ x (hUOr hx)]; exact (hκM _).isProbabilityMeasure x
      refine (eh_tv_le_one _ _).trans ?_
      simp only [pow_zero, mul_one]; linarith
    · have hkx : tr (k * τ) x = kpow Q k x := by
        have := hQP (k - 1) x hx
        rw [Nat.sub_add_cancel hk] at this
        exact this.symm
      have hdec : kpow Q k = kpow Q (k % m) ∘ₖ kpow Q (m * (k / m)) := by
        rw [← kpow_add, Nat.mod_add_div]
      haveI := kpow_isMarkov Q (k % m)
      haveI : IsProbabilityMeasure (kpow Q (m * (k / m)) x) :=
        (kpow_isMarkov Q (m * (k / m))).isProbabilityMeasure x
      have hπr : π.bind (kpow Q (k % m)) = π :=
        (eh_inv_iff _ π).1 (kpow_inv Q π ((eh_inv_iff Q π).2 hQinv) (k % m))
      have hstep : MarkovChainCLT.tvDist (tr (k * τ) x) π ≤ ab ^ (k / m) * (Cc * (1 + V x)) := by
        rw [hkx, hdec, Kernel.comp_apply]
        conv_lhs => rw [← hπr]
        refine (tvDist_bind_le _ _ _).trans ?_
        rw [← eh_kpow_kpow]
        exact hrate (k / m) x
      have hr := eh_rate hab0 (le_max_left _ _) hb0 hb1.le m k hm0
      have hCV : 0 ≤ Cc * (1 + V x) := by have := hV0 x; positivity
      calc MarkovChainCLT.tvDist (tr (k * τ) x) π ≤ ab ^ (k / m) * (Cc * (1 + V x)) := hstep
        _ ≤ (1 / b) * (b ^ (1 / (m : ℝ))) ^ k * (Cc * (1 + V x)) :=
          mul_le_mul_of_nonneg_right hr hCV
        _ = (Cc * (1 + V x) / b) * (b ^ (1 / (m : ℝ))) ^ k := by ring
        _ ≤ (Cc * (1 + V x) / b + 1) * (b ^ (1 / (m : ℝ))) ^ k := by nlinarith

end EHA
end ItoLib

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib
open StochKolmogorov.Persist EthierKurtz

/-! EHB (8ab663e7 s1): concrete facts for eq_4_26: δ₀ < 1 (copied from QF), measurability, the
sublevel box of `Vfun`, `Hconst ≥ 0`. -/

section EHB
variable {n : ℕ}

noncomputable def eh_Sf (c y : SDEState n) : ℝ := 1 + ∑ i, c i * y i

theorem eh_one_le_Sf {c y : SDEState n} (hc : c ∈ openOrthant n) (hy : y ∈ orthant n) :
    1 ≤ eh_Sf c y := by
  unfold eh_Sf
  have : 0 ≤ ∑ i, c i * y i := Finset.sum_nonneg fun i _ => mul_nonneg (hc i).le (hy i)
  linarith

theorem eh_coord_le_Sf {c y : SDEState n} (hc : c ∈ openOrthant n) (hy : y ∈ orthant n) (i : Fin n) :
    c i * y i ≤ eh_Sf c y := by
  unfold eh_Sf
  have := Finset.single_le_sum (f := fun j => c j * y j)
    (fun j _ => mul_nonneg (hc j).le (hy j)) (Finset.mem_univ i)
  simp only at this; linarith

/-- `cBracket` in terms of `aᵢ = cᵢ zᵢ / S`. -/
theorem eh_cBracket_form (C : Coeffs n) {c z : SDEState n} (hc : c ∈ openOrthant n)
    (hz : z ∈ orthant n) :
    cBracket C c z = ∑ i, c i * z i / eh_Sf c z * C.f i z -
      (1 / 2) * ∑ i, ∑ i', (c i * z i / eh_Sf c z * C.g i z) * (c i' * z i' / eh_Sf c z * C.g i' z) *
        C.sig i i' := by
  have hS : eh_Sf c z ≠ 0 := by linarith [eh_one_le_Sf hc hz]
  unfold cBracket
  have e1 : (∑ i, c i * z i * C.f i z) / (1 + ∑ i, c i * z i) =
      ∑ i, c i * z i / eh_Sf c z * C.f i z := by
    rw [Finset.sum_div]
    exact Finset.sum_congr rfl fun i _ => by unfold eh_Sf at hS ⊢; field_simp
  have e2 : (∑ i, ∑ j, C.sig i j * c i * c j * z i * z j * C.g i z * C.g j z) /
      (1 + ∑ i, c i * z i) ^ 2 = ∑ i, ∑ i', (c i * z i / eh_Sf c z * C.g i z) *
        (c i' * z i' / eh_Sf c z * C.g i' z) * C.sig i i' := by
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_div]
    exact Finset.sum_congr rfl fun j _ => by unfold eh_Sf at hS ⊢; field_simp
  rw [e1, mul_div_assoc, e2]
  try ring

theorem eh_a_mem {c z : SDEState n} (hc : c ∈ openOrthant n) (hz : z ∈ orthant n) (i : Fin n) :
    0 ≤ c i * z i / eh_Sf c z ∧ c i * z i / eh_Sf c z ≤ 1 := by
  have hS := eh_one_le_Sf hc hz
  refine ⟨div_nonneg (mul_nonneg (hc i).le (hz i)) (by linarith), ?_⟩
  rw [div_le_one (by linarith)]
  exact eh_coord_le_Sf hc hz i

theorem eh_dsum_le (u : Fin n → ℝ) (sig : Fin n → Fin n → ℝ) (i : Fin n) :
    |u i * u i * sig i i| ≤ ∑ i', |u i * u i' * sig i i'| :=
  Finset.single_le_sum (f := fun i' => |u i * u i' * sig i i'|) (fun _ _ => abs_nonneg _)
    (Finset.mem_univ i)

/-- Lower bound of the bracket used for `δ₀ < 1`. -/
theorem eh_cBracket_ge (C : Coeffs n) {c z : SDEState n} (hc : c ∈ openOrthant n)
    (hz : z ∈ orthant n) :
    -(∑ i, |C.f i z|) - (1 / 2) * ∑ i, ∑ i', |C.g i z * C.g i' z * C.sig i i'| ≤ cBracket C c z := by
  rw [eh_cBracket_form C hc hz]
  have h1 : -(∑ i, |C.f i z|) ≤ ∑ i, c i * z i / eh_Sf c z * C.f i z := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_le_sum fun i _ => ?_
    obtain ⟨h0, h1⟩ := eh_a_mem hc hz i
    have : |c i * z i / eh_Sf c z * C.f i z| ≤ |C.f i z| := by
      rw [abs_mul, abs_of_nonneg h0]; exact mul_le_of_le_one_left (abs_nonneg _) h1
    linarith [neg_abs_le (c i * z i / eh_Sf c z * C.f i z)]
  have h2 : ∑ i, ∑ i', (c i * z i / eh_Sf c z * C.g i z) * (c i' * z i' / eh_Sf c z * C.g i' z) *
      C.sig i i' ≤ ∑ i, ∑ i', |C.g i z * C.g i' z * C.sig i i'| := by
    refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun i' _ => ?_
    obtain ⟨a0, a1⟩ := eh_a_mem hc hz i
    obtain ⟨b0, b1⟩ := eh_a_mem hc hz i'
    have e : (c i * z i / eh_Sf c z * C.g i z) * (c i' * z i' / eh_Sf c z * C.g i' z) * C.sig i i' =
        (c i * z i / eh_Sf c z * (c i' * z i' / eh_Sf c z)) * (C.g i z * C.g i' z * C.sig i i') := by ring
    rw [e]
    refine (le_abs_self _).trans ?_
    rw [abs_mul, abs_of_nonneg (mul_nonneg a0 b0)]
    exact mul_le_of_le_one_left (abs_nonneg _) (mul_le_one₀ a1 b0 b1)
  linarith

/-- `δ₀ < 1`, from Assumption 1.1 at a far point and (3.2). -/
theorem eh_delta0_lt_one (hn : 0 < n) {C : Coeffs n} {c : SDEState n} {γb δ₀ : ℝ}
    (hA : Assumption11 C c γb) (hδ : IsDelta0 C γb δ₀) : δ₀ < 1 := by
  obtain ⟨-, -, hc, hγ, ε, hε, R, hR⟩ := hA
  obtain ⟨hδ0, hδγ, hδg⟩ := hδ
  by_contra h1
  push_neg at h1
  set i0 : Fin n := ⟨0, hn⟩
  set x : SDEState n := EuclideanSpace.single i0 (|R| + 1) with hx
  have hxo : x ∈ orthant n := fun j => by
    rw [hx, EuclideanSpace.single_apply]; split_ifs <;> positivity
  have hl : R ≤ l1 x := by
    unfold l1
    rw [Finset.sum_eq_single i0 (fun j _ hj => by simp [hx, EuclideanSpace.single_apply, hj])
      (by simp)]
    rw [show x i0 = |R| + 1 by simp [hx], abs_of_pos (by positivity)]
    linarith [le_abs_self R]
  have hA1 := hR x hxo hl
  have hD := hδg x hxo
  have hcb := eh_cBracket_ge C hc hxo
  set F := ∑ i, |C.f i x|
  set T := ∑ i, ∑ i', |C.g i x * C.g i' x * C.sig i i'|
  set Gs := ∑ i, C.g i x ^ 2
  have hF : 0 ≤ F := Finset.sum_nonneg fun i _ => abs_nonneg _
  have hT : 0 ≤ T := Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun i' _ => abs_nonneg _
  have hG : 0 ≤ Gs := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hsplit : ∑ i, (|C.f i x| + C.g i x ^ 2) = F + Gs := Finset.sum_add_distrib
  have hT' : 3 * δ₀ * T = 3 * δ₀ * ∑ i, ∑ j, |C.g i x * C.g j x * C.sig i j| := rfl
  rw [hsplit] at hA1
  have hγ1 : 1 ≤ γb := by linarith
  have p1 : F ≤ γb * F := le_mul_of_one_le_left hF hγ1
  have p2 : T ≤ δ₀ * T := le_mul_of_one_le_left hT h1
  nlinarith


theorem eh_coord_cont (i : Fin n) : Continuous fun x : SDEState n => x i :=
  (continuous_apply i).comp (PiLp.continuous_ofLp 2 _)

theorem eh_openOrthant_meas : MeasurableSet (openOrthant n) := by
  have : openOrthant n = ⋂ i, {x : SDEState n | 0 < x i} := by
    ext x; simp [openOrthant]
  rw [this]
  exact MeasurableSet.iInter fun i => measurableSet_lt measurable_const (eh_coord_cont i).measurable

theorem eh_Vfun_meas (c p : SDEState n) (θ : ℝ) : Measurable fun x => Vfun c p x ^ θ := by
  unfold Vfun
  refine Measurable.pow_const (Measurable.div ?_ ?_) θ
  · exact measurable_const.add
      (Finset.measurable_sum _ fun i _ => measurable_const.mul (eh_coord_cont i).measurable)
  · exact Finset.measurable_prod _ fun i _ => (eh_coord_cont i).measurable.pow_const (p i)

theorem eh_prod_pos {p x : SDEState n} (hx : x ∈ openOrthant n) : 0 < ∏ i, x i ^ p i :=
  Finset.prod_pos fun i _ => Real.rpow_pos_of_pos (hx i) _

theorem eh_Vfun_pos {c p x : SDEState n} (hc : c ∈ openOrthant n) (hx : x ∈ openOrthant n) :
    0 < Vfun c p x := by
  unfold Vfun
  have : 0 ≤ ∑ i, c i * x i := Finset.sum_nonneg fun i _ => mul_nonneg (hc i).le (hx i).le
  exact div_pos (by linarith) (eh_prod_pos hx)

/-- Sublevel sets of `Vfun` in the open orthant are contained in boxes `[α, β]ⁿ`. -/
theorem eh_box {c p : SDEState n} (hc : c ∈ openOrthant n) (hp : p ∈ openOrthant n)
    (hp1 : ∑ i, p i < 1) (R : ℝ) :
    ∃ α β : ℝ, 0 < α ∧ α ≤ β ∧ ∀ x ∈ openOrthant n, Vfun c p x ≤ R → ∀ i, α ≤ x i ∧ x i ≤ β := by
  set d : ℝ := ∑ i, p i with hd
  have hd0 : 0 ≤ d := Finset.sum_nonneg fun i _ => (hp i).le
  set R1 : ℝ := max R 1 with hR1
  have hR1p : 0 < R1 := lt_of_lt_of_le one_pos (le_max_right _ _)
  set Ci : ℝ := ∑ j, 1 / c j + 1 with hCi
  have hCi1 : 1 ≤ Ci := by
    have : 0 ≤ ∑ j, 1 / c j := Finset.sum_nonneg fun j _ => (one_div_pos.2 (hc j)).le
    linarith
  set Lm : ℝ := (R1 * Ci ^ d) ^ (1 / (1 - d)) with hLm
  set β0 : ℝ := max (Lm * Ci) 1 with hβ0
  have hβ01 : 1 ≤ β0 := le_max_right _ _
  set e : ℝ := min (1 / (R1 * β0)) 1 with he
  have he0 : 0 < e := lt_min (by have : 0 < R1 * β0 := by positivity
                                 positivity) one_pos
  have he1 : e ≤ 1 := min_le_right _ _
  set N : ℝ := ∑ i, 1 / p i with hN
  set α : ℝ := e ^ N with hα
  have hα0 : 0 < α := Real.rpow_pos_of_pos he0 _
  refine ⟨α, max β0 α, hα0, le_max_right _ _, ?_⟩
  intro x hx hV i
  have hVR : Vfun c p x ≤ R1 := hV.trans (le_max_left _ _)
  set L : ℝ := 1 + ∑ j, c j * x j with hL
  have hs0 : 0 ≤ ∑ j, c j * x j := Finset.sum_nonneg fun j _ => mul_nonneg (hc j).le (hx j).le
  have hL1 : 1 ≤ L := by linarith
  have hL0 : 0 < L := by linarith
  have hxj : ∀ j, x j ≤ L * Ci := by
    intro j
    have h1 : c j * x j ≤ L := by
      have := Finset.single_le_sum (f := fun k => c k * x k)
        (fun k _ => mul_nonneg (hc k).le (hx k).le) (Finset.mem_univ j)
      simp only at this; linarith
    have h2 : 1 / c j ≤ Ci := by
      have := Finset.single_le_sum (f := fun k => 1 / c k)
        (fun k _ => (one_div_pos.2 (hc k)).le) (Finset.mem_univ j)
      simp only at this; linarith
    have h3 : x j ≤ L * (1 / c j) := by
      rw [mul_one_div, le_div_iff₀ (hc j)]; linarith [mul_comm (c j) (x j)]
    calc x j ≤ L * (1 / c j) := h3
      _ ≤ L * Ci := mul_le_mul_of_nonneg_left h2 hL0.le
  have hprod_le : ∏ j, x j ^ p j ≤ (L * Ci) ^ d := by
    rw [hd, Real.rpow_sum_of_pos (by positivity)]
    exact Finset.prod_le_prod (fun j _ => (Real.rpow_pos_of_pos (hx j) _).le)
      fun j _ => Real.rpow_le_rpow (hx j).le (hxj j) (hp j).le
  have hP0 : 0 < ∏ j, x j ^ p j := eh_prod_pos hx
  have hVdef : Vfun c p x = L / ∏ j, x j ^ p j := rfl
  have hLP : L ≤ R1 * ∏ j, x j ^ p j := by
    rw [hVdef, div_le_iff₀ hP0] at hVR; linarith
  have hLle : L ≤ Lm := by
    have h2 : L ≤ R1 * (L ^ d * Ci ^ d) := by
      rw [← Real.mul_rpow hL0.le (by linarith)]
      exact hLP.trans (mul_le_mul_of_nonneg_left hprod_le hR1p.le)
    have h3 : L ^ (1 - d) ≤ R1 * Ci ^ d := by
      have hLd : 0 < L ^ d := Real.rpow_pos_of_pos hL0 _
      rw [Real.rpow_sub hL0, Real.rpow_one, div_le_iff₀ hLd]
      linarith
    have h1d : 0 < 1 - d := by linarith
    calc L = (L ^ (1 - d)) ^ (1 / (1 - d)) := by
          rw [← Real.rpow_mul hL0.le, mul_one_div_cancel h1d.ne', Real.rpow_one]
      _ ≤ (R1 * Ci ^ d) ^ (1 / (1 - d)) :=
          Real.rpow_le_rpow (Real.rpow_pos_of_pos hL0 _).le h3 (by positivity)
  have hxβ : ∀ j, x j ≤ β0 := fun j =>
    (hxj j).trans ((mul_le_mul_of_nonneg_right hLle (by linarith)).trans (le_max_left _ _))
  refine ⟨?_, (hxβ i).trans (le_max_left _ _)⟩
  have hPge : 1 / R1 ≤ ∏ j, x j ^ p j := by
    rw [div_le_iff₀ hR1p]; linarith [mul_comm R1 (∏ j, x j ^ p j)]
  have hsplit : ∏ j, x j ^ p j = x i ^ p i * ∏ j ∈ Finset.univ.erase i, x j ^ p j :=
    (Finset.mul_prod_erase _ _ (Finset.mem_univ i)).symm
  have hrest : ∏ j ∈ Finset.univ.erase i, x j ^ p j ≤ β0 := by
    calc ∏ j ∈ Finset.univ.erase i, x j ^ p j ≤ ∏ j ∈ Finset.univ.erase i, β0 ^ p j :=
          Finset.prod_le_prod (fun j _ => (Real.rpow_pos_of_pos (hx j) _).le)
            fun j _ => Real.rpow_le_rpow (hx j).le (hxβ j) (hp j).le
      _ = β0 ^ (∑ j ∈ Finset.univ.erase i, p j) := (Real.rpow_sum_of_pos (by linarith) _ _).symm
      _ ≤ β0 ^ (1 : ℝ) := by
          refine Real.rpow_le_rpow_of_exponent_le hβ01 ?_
          have : ∑ j ∈ Finset.univ.erase i, p j ≤ ∑ j, p j :=
            Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _) fun j _ _ => (hp j).le
          linarith
      _ = β0 := Real.rpow_one _
  have hxi_p : e ≤ x i ^ p i := by
    have hpos : 0 < x i ^ p i := Real.rpow_pos_of_pos (hx i) _
    have h1 : 1 / R1 ≤ x i ^ p i * β0 := by
      calc 1 / R1 ≤ ∏ j, x j ^ p j := hPge
        _ = x i ^ p i * ∏ j ∈ Finset.univ.erase i, x j ^ p j := hsplit
        _ ≤ x i ^ p i * β0 := mul_le_mul_of_nonneg_left hrest hpos.le
    have h2 : 1 / (R1 * β0) ≤ x i ^ p i := by
      rw [div_le_iff₀ (by positivity)]
      rw [div_le_iff₀ hR1p] at h1
      have : x i ^ p i * β0 * R1 = x i ^ p i * (R1 * β0) := by ring
      linarith
    exact (min_le_left _ _).trans h2
  have hxi : e ^ (1 / p i) ≤ x i := by
    have := Real.rpow_le_rpow he0.le hxi_p (one_div_pos.2 (hp i)).le
    rwa [← Real.rpow_mul (hx i).le, mul_one_div_cancel (hp i).ne', Real.rpow_one] at this
  have hNi : 1 / p i ≤ N := by
    have := Finset.single_le_sum (f := fun k => 1 / p k) (fun k _ => (one_div_pos.2 (hp k)).le)
      (Finset.mem_univ i)
    simp only at this; exact this
  exact (Real.rpow_le_rpow_of_exponent_ge he0 he1 hNi).trans hxi

theorem eh_Hconst_nonneg {C : Coeffs n} {c : SDEState n} {γb δ₀ : ℝ} (hγ : 0 < γb) (hδ : 0 < δ₀) :
    0 ≤ Hconst C c γb δ₀ := by
  unfold Hconst
  by_cases hb : BddAbove ((bracket35 C c γb δ₀) '' orthant n)
  · have h0 : (0 : SDEState n) ∈ orthant n := fun i => by simp
    refine le_trans ?_ (le_csSup hb ⟨0, h0, rfl⟩)
    have hc0 : cBracket C c 0 = 0 := by simp [cBracket]
    unfold bracket35
    rw [hc0]
    have h1 : 0 ≤ ∑ i, (2 * |C.f i 0| + C.g i 0 ^ 2) := Finset.sum_nonneg fun i _ => by positivity
    have h2 : 0 ≤ ∑ i, ∑ j, |C.g i 0 * C.g j 0 * C.sig i j| :=
      Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => abs_nonneg _
    have := mul_nonneg hδ.le h1
    have := mul_nonneg (by linarith : (0 : ℝ) ≤ 3 * δ₀) h2
    linarith
  · rw [Real.sSup_of_not_bddAbove hb]

/-- eq_4_26 glue: Markov facts + drift of `V^θ` at the skeleton step + face-box TV overlap. -/
theorem eh_main {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : SDEState n → ℝ≥0 → Ω → SDEState n)
    {c p : SDEState n} (hc : c ∈ openOrthant n) (hp : p ∈ openOrthant n) (hp1 : ∑ i, p i < 1)
    {θ : ℝ} (hθ : 0 < θ)
    (κ : ℝ≥0 → Kernel (SDEState n) (SDEState n)) (hκM : ∀ t, IsMarkovKernel (κ t))
    (hκx : ∀ t, ∀ x ∈ orthant n, κ t x = trans P X t x)
    (hCK : ∀ (s t : ℝ≥0) (x : SDEState n), x ∈ orthant n → ∀ A : Set (SDEState n),
      MeasurableSet A → trans P X (s + t) x A = ∫⁻ y, trans P X t y A ∂(trans P X s x))
    (hOr : ∀ (t : ℝ≥0) (x : SDEState n), x ∈ orthant n → trans P X t x (orthant n)ᶜ = 0)
    (hU : ∀ (t : ℝ≥0) (x : SDEState n), x ∈ openOrthant n →
      trans P X t x (openOrthant n)ᶜ = 0)
    (τ : ℝ≥0) (hτ : 0 < τ) {γ K : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1) (hK : 0 < K)
    (hdr : ∀ x ∈ openOrthant n, ∫⁻ ω, ENNReal.ofReal (Vfun c p (X x τ ω) ^ θ) ∂P ≤
        ENNReal.ofReal (γ * Vfun c p x ^ θ + K))
    (hovl : ∀ α β : ℝ, 0 < α → α ≤ β → ∃ T : ℝ≥0, ∃ ε : ℝ, 0 < ε ∧
      ∀ x ∈ faceOpen (Finset.univ : Finset (Fin n)), (∀ i ∈ Finset.univ, α ≤ x i ∧ x i ≤ β) →
      ∀ y ∈ faceOpen (Finset.univ : Finset (Fin n)), (∀ i ∈ Finset.univ, α ≤ y i ∧ y i ≤ β) →
        MarkovChainCLT.tvDist (trans P X T x) (trans P X T y) ≤ 1 - ε) :
    ∃ πs : Measure (SDEState n), IsProbabilityMeasure πs ∧ πs (openOrthant n)ᶜ = 0 ∧
      (∀ A : Set (SDEState n), MeasurableSet A → ∫⁻ x, trans P X τ x A ∂πs = πs A) ∧
      ∃ r : ℝ, 0 < r ∧ r < 1 ∧ ∀ x ∈ openOrthant n, ∃ Cx : ℝ, 0 < Cx ∧ ∀ k : ℕ,
        MarkovChainCLT.tvDist (trans P X (k * τ) x) πs ≤ Cx * r ^ k := by
  have hUOr : openOrthant n ⊆ orthant n := fun x hx i => (hx i).le
  have hface : ∀ x ∈ openOrthant n, x ∈ faceOpen (Finset.univ : Finset (Fin n)) := fun x hx =>
    ⟨hUOr hx, fun i hi => absurd (Finset.mem_univ i) hi, fun i _ => hx i⟩
  refine skel_harris (openOrthant n) (orthant n) eh_openOrthant_meas hUOr c hc (trans P X) κ hκM
    hκx hCK hOr hU τ hτ (fun x => Vfun c p x ^ θ) (eh_Vfun_meas c p θ)
    (fun x hx => Real.rpow_nonneg (eh_Vfun_pos hc hx).le θ) hγ0.le hγ1 hK ?_ ?_
  · intro x hx
    have hprob : IsProbabilityMeasure (trans P X τ x) := by
      rw [← hκx τ x (hUOr hx)]; exact (hκM τ).isProbabilityMeasure x
    have hae : AEMeasurable (X x τ) P := by
      by_contra h
      have h0 : trans P X τ x = 0 := Measure.map_of_not_aemeasurable h
      exact (IsProbabilityMeasure.ne_zero (trans P X τ x)) h0
    show ∫⁻ z, ENNReal.ofReal (Vfun c p z ^ θ) ∂(P.map (X x τ)) ≤ _
    rw [lintegral_map' (eh_Vfun_meas c p θ).ennreal_ofReal.aemeasurable hae]
    exact hdr x hx
  · intro R
    obtain ⟨α, β, hα, hαβ, hbox⟩ := eh_box hc hp hp1 ((max R 0) ^ θ⁻¹)
    obtain ⟨T, ε, hε, hov⟩ := hovl α β hα hαβ
    have hb : ∀ x ∈ openOrthant n, Vfun c p x ^ θ ≤ R → ∀ i ∈ Finset.univ, α ≤ x i ∧ x i ≤ β :=
      fun x hx hR i _ => by
        have h0 : 0 ≤ Vfun c p x := (eh_Vfun_pos hc hx).le
        have h1 : (Vfun c p x ^ θ) ^ θ⁻¹ ≤ (max R 0) ^ θ⁻¹ :=
          Real.rpow_le_rpow (Real.rpow_nonneg h0 θ) (hR.trans (le_max_left _ _))
            (inv_nonneg.2 hθ.le)
        rw [Real.rpow_rpow_inv h0 hθ.ne'] at h1
        exact hbox x hx h1 i
    exact ⟨T, ε, hε, fun x hx y hy hxR hyR =>
      hov x (hface x hx) (hb x hx hxR) y (hface y hy) (hb y hy hyR)⟩


end EHB
end ItoLib


open MeasureTheory ProbabilityTheory Filter in
open scoped ENNReal NNReal Topology BigOperators in
open StochKolmogorov.Persist in
open EthierKurtz in
theorem solution {n : ℕ} (hn : 0 < n) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (C : Coeffs n)
    (B : ℝ≥0 → Ω → SDEState n) (X : SDEState n → ℝ≥0 → Ω → SDEState n)
    (hX : IsSolutionFamily P C B X) (c : SDEState n) (γb : ℝ) (hA : Assumption11 C c γb)
    (h12 : Assumption12 P C X) (M : ℝ) (hMpos : 0 < M) (hM : IsRadiusM C c γb M)
    (δ₀ : ℝ) (hδ₀ : IsDelta0 C γb δ₀) (p : SDEState n) (hp : p ∈ openOrthant n) (hpδ : l1 p = δ₀)
    (ρ : ℝ) (hρ : 0 < ρ) (h41 : IsWeightedInvasionMin P C X p ρ)
    (Tstar : ℝ) (hTstar : 0 < Tstar)
    (hT : ∀ T : ℝ, Tstar < T → ∀ x ∈ bdry n, l1 x ≤ M →
      Integrable (Phi C c p) (occMean P X x T) ∧ ∫ y, Phi C c p y ∂(occMean P X x T) ≤ -ρ)
    (nstar : ℕ) (hnstar : Hconst C c γb δ₀ < γb * ((nstar : ℝ) - 1)) :
    ∃ πs : Measure (SDEState n), IsProbabilityMeasure πs ∧ πs (openOrthant n)ᶜ = 0 ∧
      (∀ A : Set (SDEState n), MeasurableSet A →
        ∫⁻ x, trans P X ((nstar : ℝ) * Tstar).toNNReal x A ∂πs = πs A) ∧
      ∃ r : ℝ, 0 < r ∧ r < 1 ∧ ∀ x ∈ openOrthant n, ∃ Cx : ℝ, 0 < Cx ∧ ∀ k : ℕ,
        MarkovChainCLT.tvDist (trans P X (k * ((nstar : ℝ) * Tstar).toNNReal) x) πs ≤
          Cx * r ^ k := by
  obtain ⟨θ, hθ, hθδ, Kθ, hKθ, hprop⟩ := StochKolmogorov.Persist.proposition_4_1 hn P C B X hX c γb hA
    h12 M hMpos hM δ₀ hδ₀ p hp hpδ ρ hρ h41 Tstar hTstar hT nstar hnstar
  obtain ⟨κd, hκ0, hκ1, Kt, hKt, hdr⟩ := StochKolmogorov.Persist.eq_4_18 hn P C B X hX c γb hA h12 M
    hMpos hM δ₀ hδ₀ p hp hpδ ρ hρ h41 Tstar hTstar hT nstar hnstar θ hθ hθδ Kθ hKθ hprop
  obtain ⟨hk, hCK, hOr, hU⟩ := StochKolmogorov.Persist.markov_property P C B X hX c γb hA
  choose κ hκM hκx using hk
  have hγ : 0 < γb := hA.2.2.2.1
  have hH := ItoLib.eh_Hconst_nonneg (C := C) (c := c) hγ hδ₀.1
  have hn2 : (1 : ℝ) < nstar := by
    by_contra h0
    have h : (nstar : ℝ) ≤ 1 := le_of_not_gt h0
    have : γb * ((nstar : ℝ) - 1) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hγ.le (by linarith)
    linarith
  have hτ : 0 < ((nstar : ℝ) * Tstar).toNNReal := Real.toNNReal_pos.2 (mul_pos (by linarith) hTstar)
  have hp1 : ∑ i, p i < 1 := by
    have h1 : ∑ i, p i = l1 p := by
      unfold l1; exact Finset.sum_congr rfl fun i _ => (abs_of_pos (hp i)).symm
    rw [h1, hpδ]; exact ItoLib.eh_delta0_lt_one hn hA hδ₀
  exact ItoLib.eh_main P X hA.2.2.1 hp hp1 hθ κ hκM hκx hCK hOr hU _ hτ hκ0 hκ1 hKt hdr
    (fun α β hα hαβ => StochKolmogorov.Persist.kolmogorov_face_box_tv_overlap P C B X hX hA.2.1 hA.1
      Finset.univ hα hαβ)
