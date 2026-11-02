-- Prove2me | solution 1 for StochKolmogorov.Persist.theorem_1_1
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-02T02:01:10.309673+00:00
-- url     : https://prove2.me/submissions/91b82547-22a5-44a2-a5bf-f3293c21b7da

import Mathlib
import Definitions.Def_StochKolmogorov_Persist_Model
import Definitions.Def_StochKolmogorov_Persist_Persistence
import Definitions.Def_TotalVariationDist
import Theorems.Thm_StochKolmogorov_Persist_markov_property
import Theorems.Thm_StochKolmogorov_Persist_eq_4_1
import Theorems.Thm_StochKolmogorov_Persist_lemma_4_1
import Theorems.Thm_StochKolmogorov_Persist_eq_4_26
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

/-! Reduction of Theorem 1.1 (arXiv:1704.06984) to the skeleton-chain ergodicity (4.26), the weight
choice (4.1), the time `T*` of Lemma 4.1, and the Markov property of the solution. The glue below
passes from the skeleton chain `X(kτ)` to continuous time. -/

namespace ItoLib

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

theorem tvDist_le_of_forall (μ ν : Measure X) {c : ℝ}
    (h : ∀ A : Set X, MeasurableSet A → |(μ A).toReal - (ν A).toReal| ≤ c) :
    MarkovChainCLT.tvDist μ ν ≤ c :=
  csSup_le ⟨_, ∅, MeasurableSet.empty, rfl⟩ (by rintro _ ⟨A, hA, rfl⟩; exact h A hA)

/-- `tvDist (μ η) (ν η) ≤ tvDist μ ν` for a Markov kernel `η`. -/
theorem tvDist_bind_le (μ ν : Measure X) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {Z : Type*} [MeasurableSpace Z] (η : Kernel X Z) [IsMarkovKernel η] :
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

end HA

section TB
variable {S : Type*} [MeasurableSpace S]

theorem ae_of_compl_null {μ : Measure S} {A : Set S} (h : μ Aᶜ = 0) : ∀ᵐ x ∂μ, x ∈ A :=
  mem_ae_iff.2 h

theorem bind_apply_tr (tr : S → Measure S) (Or : Set S) (κ : Kernel S S)
    (hκx : ∀ x ∈ Or, κ x = tr x) (μ : Measure S) (hμ : μ Orᶜ = 0) {A : Set S}
    (hA : MeasurableSet A) : μ.bind κ A = ∫⁻ x, tr x A ∂μ := by
  rw [Measure.bind_apply hA κ.measurable.aemeasurable]
  refine lintegral_congr_ae ?_
  filter_upwards [ae_of_compl_null hμ] with x hx
  rw [hκx x hx]

theorem bind_isProb (κ : Kernel S S) [IsMarkovKernel κ] (μ : Measure S) [IsProbabilityMeasure μ] :
    IsProbabilityMeasure (μ.bind κ) := by
  constructor
  rw [Measure.bind_apply MeasurableSet.univ κ.measurable.aemeasurable]
  simp

theorem bind_compl_null (tr : S → Measure S) (Or U : Set S) (κ : Kernel S S)
    (hκx : ∀ x ∈ Or, κ x = tr x) (hU : U ⊆ Or) (hUm : MeasurableSet U)
    (htrU : ∀ x ∈ U, tr x Uᶜ = 0) (μ : Measure S) (hμ : μ Uᶜ = 0) : μ.bind κ Uᶜ = 0 := by
  have hμ' : μ Orᶜ = 0 := measure_mono_null (compl_subset_compl.2 hU) hμ
  rw [bind_apply_tr tr Or κ hκx μ hμ' hUm.compl]
  refine (lintegral_congr_ae ?_).trans lintegral_zero
  filter_upwards [ae_of_compl_null hμ] with x hx
  exact htrU x hx

variable (tr : ℝ≥0 → S → Measure S) (Or : Set S) (κ : ℝ≥0 → Kernel S S)
  (hκM : ∀ t, IsMarkovKernel (κ t)) (hκx : ∀ t, ∀ x ∈ Or, κ t x = tr t x)
  (hCK : ∀ (s t : ℝ≥0) (x : S), x ∈ Or → ∀ A : Set S, MeasurableSet A →
      tr (s + t) x A = ∫⁻ y, tr t y A ∂(tr s x))
  (hOr : ∀ t, ∀ x ∈ Or, tr t x Orᶜ = 0)
include hκx hCK hOr

theorem kernel_ck (s t : ℝ≥0) {x : S} (hx : x ∈ Or) : κ (s + t) x = (κ s x).bind (κ t) := by
  ext A hA
  rw [hκx _ x hx, hCK s t x hx A hA,
    bind_apply_tr (tr t) Or (κ t) (hκx t) (κ s x) (by rw [hκx s x hx]; exact hOr s x hx) hA,
    hκx s x hx]

theorem bind_ck (s t : ℝ≥0) (μ : Measure S) (hμ : μ Orᶜ = 0) :
    μ.bind (κ (s + t)) = (μ.bind (κ s)).bind (κ t) := by
  rw [Measure.bind_bind (κ s).measurable.aemeasurable (κ t).measurable.aemeasurable]
  ext A hA
  have hcm : Measurable (fun a => (κ s a).bind (κ t)) := by
    have : (fun a => (κ s a).bind (κ t)) = ⇑(κ t ∘ₖ κ s) := by
      funext a; rw [Kernel.comp_apply]
    rw [this]; exact (κ t ∘ₖ κ s).measurable
  rw [Measure.bind_apply hA (κ (s + t)).measurable.aemeasurable,
    Measure.bind_apply hA hcm.aemeasurable]
  refine lintegral_congr_ae ?_
  filter_upwards [ae_of_compl_null hμ] with x hx
  rw [kernel_ck tr Or κ hκx hCK hOr s t hx]

theorem bind_iter (τ : ℝ≥0) (ν : Measure S) (hν : ν Orᶜ = 0) (hinv : ν.bind (κ τ) = ν) :
    ∀ k : ℕ, ν.bind (κ (((k + 1 : ℕ) : ℝ≥0) * τ)) = ν := by
  intro k
  induction k with
  | zero => simpa using hinv
  | succ k ih =>
    rw [show (((k + 1 + 1 : ℕ) : ℝ≥0) * τ) = ((k + 1 : ℕ) : ℝ≥0) * τ + τ by push_cast; ring,
      bind_ck tr Or κ hκx hCK hOr _ τ ν hν, ih, hinv]

include hκM in
theorem uniq_of_skel (τ : ℝ≥0) (O : Set S) (hO : O ⊆ Or) (πs : Measure S) [IsProbabilityMeasure πs]
    (r : ℝ) (hr0 : 0 < r) (hr1 : r < 1)
    (hconv : ∀ x ∈ O, ∃ Cx : ℝ, 0 < Cx ∧ ∀ k : ℕ,
      MarkovChainCLT.tvDist (tr (k * τ) x) πs ≤ Cx * r ^ k)
    (ν : Measure S) [IsProbabilityMeasure ν] (hν : ν Oᶜ = 0) (hinv : ν.bind (κ τ) = ν) : ν = πs := by
  haveI : ∀ t, IsMarkovKernel (κ t) := hκM
  have hνOr : ν Orᶜ = 0 := measure_mono_null (compl_subset_compl.2 hO) hν
  ext A hA
  have hseq : ∀ k : ℕ, ν A = ∫⁻ x, κ (((k + 1 : ℕ) : ℝ≥0) * τ) x A ∂ν := fun k => by
    conv_lhs => rw [← bind_iter tr Or κ hκx hCK hOr τ ν hνOr hinv k]
    rw [Measure.bind_apply hA (κ _).measurable.aemeasurable]
  have hlim : Tendsto (fun k : ℕ => ∫⁻ x, κ (((k + 1 : ℕ) : ℝ≥0) * τ) x A ∂ν) atTop
      (𝓝 (∫⁻ _x, πs A ∂ν)) := by
    refine tendsto_lintegral_of_dominated_convergence (fun _ => 1)
      (fun k => (κ _).measurable_coe hA) (fun k => ae_of_all _ fun x => prob_le_one) (by simp) ?_
    filter_upwards [ae_of_compl_null hν] with x hx
    obtain ⟨Cx, -, hb⟩ := hconv x hx
    haveI : ∀ t, IsProbabilityMeasure (tr t x) := fun t => by
      rw [← hκx t x (hO hx)]; infer_instance
    rw [← ENNReal.tendsto_toReal_iff (fun k => measure_ne_top _ _) (measure_ne_top _ _)]
    have hk : ∀ k : ℕ, |(κ (((k + 1 : ℕ) : ℝ≥0) * τ) x A).toReal - (πs A).toReal| ≤ Cx * r ^ (k + 1) :=
      fun k => by rw [hκx _ x (hO hx)]; exact (abs_sub_le_tvDist _ _ hA).trans (hb (k + 1))
    have hr : Tendsto (fun k : ℕ => Cx * r ^ (k + 1)) atTop (𝓝 0) := by
      have := ((tendsto_pow_atTop_nhds_zero_of_lt_one hr0.le hr1).comp (tendsto_add_atTop_nat 1)).const_mul Cx
      simpa [Function.comp_def] using this
    exact tendsto_iff_dist_tendsto_zero.2
      (squeeze_zero (fun k => dist_nonneg) (fun k => by rw [Real.dist_eq]; exact hk k) hr)
  have hc : Tendsto (fun k : ℕ => ∫⁻ x, κ (((k + 1 : ℕ) : ℝ≥0) * τ) x A ∂ν) atTop (𝓝 (ν A)) := by
    simp_rw [← hseq]; exact tendsto_const_nhds
  rw [tendsto_nhds_unique hc hlim, lintegral_const, measure_univ, mul_one]

include hκM in
theorem glue_main (O : Set S) (hO : O ⊆ Or) (hOm : MeasurableSet O)
    (htrO : ∀ t, ∀ x ∈ O, tr t x Oᶜ = 0) (τ : ℝ≥0) (hτ : 0 < τ)
    (πs : Measure S) [IsProbabilityMeasure πs] (hπO : πs Oᶜ = 0)
    (hπinv : ∀ A : Set S, MeasurableSet A → ∫⁻ x, tr τ x A ∂πs = πs A)
    (r : ℝ) (hr0 : 0 < r) (hr1 : r < 1)
    (hconv : ∀ x ∈ O, ∃ Cx : ℝ, 0 < Cx ∧ ∀ k : ℕ,
      MarkovChainCLT.tvDist (tr (k * τ) x) πs ≤ Cx * r ^ k) :
    (∀ (t : ℝ≥0) (A : Set S), MeasurableSet A → ∫⁻ x, tr t x A ∂πs = πs A) ∧
    (∀ π : Measure S, IsProbabilityMeasure π → π Oᶜ = 0 →
      (∀ (t : ℝ≥0) (A : Set S), MeasurableSet A → ∫⁻ x, tr t x A ∂π = π A) → π = πs) ∧
    ∃ r' : ℝ, 0 < r' ∧ r' < 1 ∧ ∀ x ∈ O, ∃ K : ℝ, ∀ t : ℝ≥0,
      MarkovChainCLT.tvDist (tr t x) πs ≤ K * r' ^ (t : ℝ) := by
  haveI : ∀ t, IsMarkovKernel (κ t) := hκM
  have hπOr : πs Orᶜ = 0 := measure_mono_null (compl_subset_compl.2 hO) hπO
  have hbind : ∀ (t : ℝ≥0) (μ : Measure S), μ Orᶜ = 0 →
      (∀ A : Set S, MeasurableSet A → ∫⁻ x, tr t x A ∂μ = μ A) → μ.bind (κ t) = μ :=
    fun t μ hμ hi => by
      ext A hA; rw [bind_apply_tr (tr t) Or (κ t) (hκx t) μ hμ hA, hi A hA]
  have hπτ : πs.bind (κ τ) = πs := hbind τ πs hπOr hπinv
  have huniq : ∀ ν : Measure S, IsProbabilityMeasure ν → ν Oᶜ = 0 → ν.bind (κ τ) = ν → ν = πs :=
    fun ν _ hν hi => uniq_of_skel tr Or κ hκM hκx hCK hOr τ O hO πs r hr0 hr1 hconv ν hν hi
  have hall : ∀ t, πs.bind (κ t) = πs := fun t => by
    haveI := bind_isProb (κ t) πs
    refine huniq _ inferInstance
      (bind_compl_null (tr t) Or O (κ t) (hκx t) hO hOm (htrO t) πs hπO) ?_
    rw [← bind_ck tr Or κ hκx hCK hOr t τ πs hπOr, add_comm,
      bind_ck tr Or κ hκx hCK hOr τ t πs hπOr, hπτ]
  refine ⟨fun t A hA => by
      rw [← bind_apply_tr (tr t) Or (κ t) (hκx t) πs hπOr hA, hall t],
    fun π hπ hπO' hπinv' => huniq π hπ hπO'
      (hbind τ π (measure_mono_null (compl_subset_compl.2 hO) hπO') (hπinv' τ)), ?_⟩
  have hτ' : (0 : ℝ) < τ := hτ
  refine ⟨r ^ (1 / (τ : ℝ)), Real.rpow_pos_of_pos hr0 _,
    Real.rpow_lt_one hr0.le hr1 (by positivity), fun x hx => ?_⟩
  obtain ⟨Cx, hCx, hb⟩ := hconv x hx
  refine ⟨Cx / r, fun t => ?_⟩
  set k : ℕ := ⌊(t : ℝ) / τ⌋₊ with hkdef
  have hle : (k : ℝ≥0) * τ ≤ t := by
    rw [← NNReal.coe_le_coe]; push_cast
    exact (le_div_iff₀ hτ').1 (Nat.floor_le (by positivity))
  have hκt : κ t x = (κ (k * τ) x).bind (κ (t - k * τ)) := by
    rw [← kernel_ck tr Or κ hκx hCK hOr _ _ (hO hx), add_tsub_cancel_of_le hle]
  have hk : (t : ℝ) / τ - 1 ≤ k := by linarith [Nat.lt_floor_add_one ((t : ℝ) / τ)]
  have h1 : r ^ k ≤ r ^ ((t : ℝ) / τ - 1) := by
    rw [← Real.rpow_natCast]; exact Real.rpow_le_rpow_of_exponent_ge hr0 hr1.le hk
  have h2 : r ^ ((t : ℝ) / τ - 1) = (r ^ (1 / (τ : ℝ))) ^ (t : ℝ) / r := by
    rw [Real.rpow_sub hr0, Real.rpow_one, ← Real.rpow_mul hr0.le]
    congr 2; ring
  calc MarkovChainCLT.tvDist (tr t x) πs
      = MarkovChainCLT.tvDist ((κ (k * τ) x).bind (κ (t - k * τ)))
          (πs.bind (κ (t - k * τ))) := by rw [← hκx t x (hO hx), hκt, hall]
    _ ≤ MarkovChainCLT.tvDist (κ (k * τ) x) πs := tvDist_bind_le _ _ _
    _ = MarkovChainCLT.tvDist (tr (k * τ) x) πs := by rw [hκx _ x (hO hx)]
    _ ≤ Cx * r ^ k := hb k
    _ ≤ Cx * ((r ^ (1 / (τ : ℝ))) ^ (t : ℝ) / r) := by
      rw [← h2]; exact mul_le_mul_of_nonneg_left h1 hCx.le
    _ = Cx / r * (r ^ (1 / (τ : ℝ))) ^ (t : ℝ) := by ring

end TB

open StochKolmogorov.Persist EthierKurtz in
/-- `M` of (3.1) from Assumption 1.1: `M = max R 1`. -/
theorem exists_isRadiusM {n : ℕ} (C : Coeffs n) (c : SDEState n) (γb : ℝ)
    (hA : Assumption11 C c γb) : ∃ M : ℝ, 0 < M ∧ IsRadiusM C c γb M := by
  obtain ⟨-, -, -, -, ε, hε, R, hR⟩ := hA
  refine ⟨max R 1, lt_of_lt_of_le one_pos (le_max_right _ _), fun x hx hM => ?_⟩
  have := hR x hx (le_trans (le_max_left _ _) hM)
  linarith

open StochKolmogorov.Persist EthierKurtz in
/-- `δ₀` of (3.2) exists: `δ₀ = γ_b / (3 S n + 3)` with `S = ∑ᵢⱼ |σᵢⱼ|`. -/
theorem exists_isDelta0 {n : ℕ} (C : Coeffs n) (γb : ℝ) (hγ : 0 < γb) :
    ∃ δ₀ : ℝ, IsDelta0 C γb δ₀ := by
  set S : ℝ := ∑ i, ∑ j, |C.sig i j| with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => abs_nonneg _
  have hsij : ∀ i j, |C.sig i j| ≤ S := by
    intro i j
    calc |C.sig i j| ≤ ∑ j', |C.sig i j'| :=
          Finset.single_le_sum (f := fun j' => |C.sig i j'|) (fun _ _ => abs_nonneg _)
            (Finset.mem_univ j)
      _ ≤ S := Finset.single_le_sum (f := fun i' => ∑ j', |C.sig i' j'|)
            (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (Finset.mem_univ i)
  have hden : 0 < 3 * S * n + 3 := by positivity
  refine ⟨γb / (3 * S * n + 3), div_pos hγ hden, ?_, fun x _ => ?_⟩
  · rw [div_lt_div_iff₀ hden two_pos]
    nlinarith [mul_nonneg hS0 (Nat.cast_nonneg (α := ℝ) n)]
  · set δ := γb / (3 * S * n + 3) with hδ
    have hδ0 : 0 ≤ δ := (div_pos hγ hden).le
    set G : ℝ := ∑ i, C.g i x ^ 2 with hG
    have hG0 : 0 ≤ G := Finset.sum_nonneg fun i _ => sq_nonneg _
    have hterm : ∀ i j, |C.g i x * C.g j x * C.sig i j|
        ≤ S * ((C.g i x ^ 2 + C.g j x ^ 2) / 2) := by
      intro i j
      rw [abs_mul, abs_mul]
      have h1 : |C.g i x| * |C.g j x| ≤ (C.g i x ^ 2 + C.g j x ^ 2) / 2 := by
        nlinarith [sq_nonneg (|C.g i x| - |C.g j x|), sq_abs (C.g i x), sq_abs (C.g j x)]
      calc |C.g i x| * |C.g j x| * |C.sig i j| ≤ ((C.g i x ^ 2 + C.g j x ^ 2) / 2) * S :=
            mul_le_mul h1 (hsij i j) (abs_nonneg _) (by positivity)
        _ = S * ((C.g i x ^ 2 + C.g j x ^ 2) / 2) := by ring
    have hsum : ∑ i, ∑ j, |C.g i x * C.g j x * C.sig i j| ≤ S * n * G := by
      calc ∑ i, ∑ j, |C.g i x * C.g j x * C.sig i j|
          ≤ ∑ i : Fin n, ∑ j : Fin n, S * ((C.g i x ^ 2 + C.g j x ^ 2) / 2) :=
            Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hterm i j
        _ = S * n * G := by
            simp only [← Finset.mul_sum, add_div, Finset.sum_add_distrib, Finset.sum_const,
              Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, hG, ← Finset.sum_div]
            ring
    have hkey : δ * (3 * S * n + 3) = γb := by rw [hδ, div_mul_cancel₀ _ hden.ne']
    calc 3 * δ * ∑ i, ∑ j, |C.g i x * C.g j x * C.sig i j| + δ * G
        ≤ 3 * δ * (S * n * G) + δ * G := by nlinarith
      _ ≤ δ * (3 * S * n + 3) * G := by nlinarith [mul_nonneg hδ0 hG0]
      _ = γb * G := by rw [hkey]

end ItoLib

open StochKolmogorov.Persist EthierKurtz in
theorem solution {n : ℕ} (hn : 0 < n) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (C : Coeffs n)
    (B : ℝ≥0 → Ω → SDEState n) (X : SDEState n → ℝ≥0 → Ω → SDEState n)
    (hX : IsSolutionFamily P C B X) (c : SDEState n) (γb : ℝ) (hA : Assumption11 C c γb) (h12 : Assumption12 P C X) :
    ∃ πs : Measure (SDEState n), IsInvariant P X πs ∧ πs (openOrthant n)ᶜ = 0 ∧
      (∀ π : Measure (SDEState n), IsInvariant P X π → π (openOrthant n)ᶜ = 0 → π = πs) ∧
      ∃ r : ℝ, 0 < r ∧ r < 1 ∧ ∀ x ∈ openOrthant n, ∃ K : ℝ, ∀ t : ℝ≥0,
        MarkovChainCLT.tvDist (trans P X t x) πs ≤ K * r ^ (t : ℝ) := by
  obtain ⟨hκ, hCK, hOr, hO⟩ := markov_property P C B X hX c γb hA
  choose κ hκM hκx using hκ
  obtain ⟨M, hMpos, hM⟩ := ItoLib.exists_isRadiusM C c γb hA
  have hγ : 0 < γb := hA.2.2.2.1
  obtain ⟨δ₀, hδ₀⟩ := ItoLib.exists_isDelta0 C γb hγ
  obtain ⟨p, hp, hpδ, ρ, hρ, h41⟩ := eq_4_1 hn P C B X hX c γb hA h12 δ₀ hδ₀.1
  obtain ⟨Tstar, hTstar, hT⟩ :=
    lemma_4_1 hn P C B X hX c γb hA h12 M hMpos hM δ₀ hδ₀ p hp hpδ ρ hρ h41
  obtain ⟨N, hN⟩ := exists_nat_gt (Hconst C c γb δ₀ / γb + 1)
  have hnstar : Hconst C c γb δ₀ < γb * (((N + 1 : ℕ) : ℝ) - 1) := by
    have h1 : Hconst C c γb δ₀ / γb < ((N + 1 : ℕ) : ℝ) - 1 := by push_cast; linarith
    have h2 := mul_lt_mul_of_pos_left h1 hγ
    rwa [mul_div_cancel₀ _ hγ.ne'] at h2
  obtain ⟨πs, hπP, hπO, hπinv, r, hr0, hr1, hconv⟩ :=
    eq_4_26 hn P C B X hX c γb hA h12 M hMpos hM δ₀ hδ₀ p hp hpδ ρ hρ h41 Tstar hTstar hT (N + 1) hnstar
  have hτ : 0 < (((N + 1 : ℕ) : ℝ) * Tstar).toNNReal :=
    Real.toNNReal_pos.2 (mul_pos (by positivity) hTstar)
  have hOOr : openOrthant n ⊆ orthant n := fun x hx i => (hx i).le
  have hOm : MeasurableSet (openOrthant n) := by
    have : openOrthant n = ⋂ i, {y : SDEState n | 0 < y i} := by ext y; simp [openOrthant]
    rw [this]
    exact MeasurableSet.iInter fun i =>
      measurableSet_lt measurable_const (PiLp.continuous_apply 2 _ i).measurable
  obtain ⟨h1, h2, r', hr'0, hr'1, h3⟩ :=
    ItoLib.glue_main (fun t => trans P X t) (orthant n) κ hκM hκx hCK hOr (openOrthant n) hOOr hOm
      hO _ hτ πs hπO hπinv r hr0 hr1 hconv
  exact ⟨πs, ⟨hπP, measure_mono_null (compl_subset_compl.2 hOOr) hπO, h1⟩, hπO,
    fun π hπ hπO' => h2 π hπ.1 hπO' hπ.2.2, r', hr'0, hr'1, h3⟩
