-- Prove2me | solution 1 for OAI.WeakPinned.arithmetic_sequence_impossible
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-19T01:03:05.827323+00:00
-- url     : https://prove2.me/submissions/67d0541a-f345-4df2-8c9d-169d63a3b650

import Mathlib
import Definitions.Def_PinnedDistances
import Definitions.Def_OAIQWWP000
import Theorems.Thm_OAI_WeakPinned_arithmetic_no_unbounded
import Theorems.Thm_OAI_WeakPinned_sampling_variance_rates

section
-- module Solutions.OAIQW_WeakPinned.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. -/
section OAICompat434
theorem dite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a : p → α} {b : ¬p → α} (h : p) :
    (if hp : p then a hp else b hp) = a h := dif_pos h
/-- Mathlib's newer name for `measurable_pi_lambda` (with `f` implicit). -/
theorem Measurable.of_eval {δ ι : Type*} {π : ι → Type*} [MeasurableSpace δ]
    [∀ i, MeasurableSpace (π i)] {f : δ → ∀ i, π i}
    (h : ∀ i, Measurable fun a => f a i) : Measurable f := measurable_pi_lambda f h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQW_WeakPinned.FiniteLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u1 u2 u3

section
noncomputable section
open scoped BigOperators Topology ENNReal
open Filter MeasureTheory
namespace WeakPinned.Bounded

variable {I : Type u1} {X : Type u2} [Fintype I] [MeasurableSpace X] [MeasurableSingletonClass X]

lemma integral_finiteLaw (w : I → ℝ) (U : I → X) (hw : ∀ i,0≤ w i) (f : X → ℝ) :
    ∫ x,f x ∂ finiteLaw w U=∑ i,w i*f (U i) := by
  rw [finiteLaw,integral_finsetSum_measure]
  · simp only [integral_smul_measure,integral_dirac,ENNReal.toReal_ofReal (hw _),smul_eq_mul]
  · intro i _
    exact (integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top

lemma finiteLaw_ae (w : I → ℝ) (U : I → X) {p : X → Prop}
    (hp : ∀ i,w i≠0 → p (U i)) : ∀ᵐ x ∂ finiteLaw w U,p x := by
  rw [finiteLaw,ae_finsetSum_measure_iff]
  intro i _
  by_cases h : w i=0
  · simp [h]
  · exact Measure.ae_smul_measure (by simpa only [ae_dirac_eq,Filter.eventually_pure] using hp i h) _

omit [MeasurableSingletonClass X] in
lemma finiteLaw_map {Y : Type u3} [MeasurableSpace Y] (w : I → ℝ) (U : I → X)
    (f : X → Y) (hf : Measurable f) : (finiteLaw w U).map f=finiteLaw w (f ∘ U) := by
  simp only [finiteLaw, Measure.map_finset_sum' hf.aemeasurable,
    Measure.map_smul, Measure.map_dirac' hf, Function.comp_def]

end WeakPinned.Bounded

end
end

end OAI
end

section
-- module Solutions.OAIQW_WeakPinned.ConditionalIntegral
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u1 u2 u3 u4 u5

section
noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace WeakPinned.Bounded

lemma integrable_one_bound {X : Type u1} [MeasurableSpace X] (μ : Measure X) [IsFiniteMeasure μ]
    (f : X → ℝ) (hf : Measurable f) (hbound : ∀ x,‖f x‖≤1) : Integrable f μ := by
  exact (integrable_const (1:ℝ)).mono' hf.aestronglyMeasurable (Eventually.of_forall hbound)

variable {Ω : Type u2} {E : Type u3} {X : Type u4} {Y : Type u5} [MeasurableSpace Ω] [MeasurableSpace E]
  [MeasurableSpace X] [MeasurableSpace Y]

lemma integral_fiber_indicator (Q : Measure E) (μ : Measure X)
    [IsProbabilityMeasure Q] [IsProbabilityMeasure μ]
    (f : E × X → ℝ) (hf : Measurable f) (hbound : ∀ p,‖f p‖≤1)
    (s : Set E) (hs : MeasurableSet s) :
    (∫ e in s, ∫ x,f (e,x) ∂ μ ∂ Q)=
      ∫ p,(s ×ˢ Set.univ).indicator f p ∂ Q.prod μ := by
  have hi := integrable_one_bound (Q.prod μ) f hf hbound
  rw [integral_prod _ (hi.indicator (hs.prod MeasurableSet.univ))]
  rw [← integral_indicator hs]
  apply integral_congr_ae
  filter_upwards [] with e
  by_cases he : e∈s
  · simp [Set.indicator_of_mem,he]
  · simp [Set.indicator_of_notMem,he]

lemma conditional_integral_eq
    (R : Measure Ω) (Q : Measure E) (μ : Measure X) (ν : Measure Y)
    [IsProbabilityMeasure R] [IsProbabilityMeasure Q]
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (e : Ω → E) (z : Ω → X) (w : Ω → Y)
    (he : Measurable e) (hz : Measurable z) (hw : Measurable w)
    (hmz : R.map (fun r => (e r,z r))=Q.prod μ)
    (hmw : R.map (fun r => (e r,w r))=Q.prod ν)
    (f : E × X → ℝ) (g : E × Y → ℝ)
    (hf : Measurable f) (hg : Measurable g)
    (hfb : ∀ p,‖f p‖≤1) (hgb : ∀ p,‖g p‖≤1)
    (heq : ∀ᵐ r ∂ R,f (e r,z r)=g (e r,w r)) :
    ∀ᵐ a ∂ Q,(∫ x,f (a,x) ∂ μ)=(∫ y,g (a,y) ∂ ν) := by
  apply Integrable.ae_eq_of_forall_setIntegral_eq
  · exact (integrable_one_bound (Q.prod μ) f hf hfb).integral_prod_left
  · exact (integrable_one_bound (Q.prod ν) g hg hgb).integral_prod_left
  · intro s hs _
    rw [integral_fiber_indicator Q μ f hf hfb s hs,
      integral_fiber_indicator Q ν g hg hgb s hs,← hmz,← hmw]
    rw [integral_map_of_stronglyMeasurable (he.prodMk hz)
      (hf.indicator (hs.prod MeasurableSet.univ)).stronglyMeasurable,
      integral_map_of_stronglyMeasurable (he.prodMk hw)
      (hg.indicator (hs.prod MeasurableSet.univ)).stronglyMeasurable]
    apply integral_congr_ae
    filter_upwards [heq] with r hr
    by_cases h : e r∈s <;> simp [h,hr]

end WeakPinned.Bounded

end
end

end OAI
end

section
-- module Solutions.OAIQW_WeakPinned.MobiusObstruction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
/- A non-atomic obstruction for bounded cross-ratio energy. -/

noncomputable section
open Filter MeasureTheory
open scoped Topology ENNReal

namespace WeakPinned.Bounded

lemma measurable_crossKernel (a c : ℂ) : Measurable (crossKernel a c) := by
  unfold crossKernel
  fun_prop

lemma measurable_targetKernel (d : ℂ) : Measurable (targetKernel d) := by
  unfold targetKernel
  fun_prop

lemma crossKernel_nonneg (a c : ℂ) (zw : ℂ × ℂ) : 0 ≤ crossKernel a c zw := by
  exact le_min zero_le_one (norm_nonneg _)

lemma crossKernel_le_one (a c : ℂ) (zw : ℂ × ℂ) : crossKernel a c zw ≤ 1 :=
  min_le_left _ _

lemma targetKernel_nonneg (d : ℂ) (zw : ℂ × ℂ) : 0 ≤ targetKernel d zw := by
  exact le_min zero_le_one (norm_nonneg _)

lemma targetKernel_le_one (d : ℂ) (zw : ℂ × ℂ) : targetKernel d zw ≤ 1 :=
  min_le_left _ _

lemma integrable_targetKernel (ν : Measure ℂ) [IsFiniteMeasure ν] (d : ℂ) :
    Integrable (targetKernel d) (ν.prod ν) := by
  apply Integrable.mono' (integrable_const (1 : ℝ))
    (measurable_targetKernel d).aestronglyMeasurable
  exact Filter.Eventually.of_forall fun zw => by
    rw [Real.norm_eq_abs, abs_of_nonneg (targetKernel_nonneg d zw)]
    exact targetKernel_le_one d zw

lemma crossKernel_tendsto (c : ℂ) (zw : ℂ × ℂ)
    (hz : zw.1 ≠ c) (hw : zw.2 ≠ c) :
    Tendsto (fun a => crossKernel a c zw) (nhds c) (nhds 0) := by
  have hd : (zw.1 - c) * (c - zw.2) ≠ 0 :=
    mul_ne_zero (sub_ne_zero.mpr hz) (sub_ne_zero.mpr hw.symm)
  have hc : ContinuousAt (fun a : ℂ => crossKernel a c zw) c := by
    unfold crossKernel
    fun_prop
  simpa [crossKernel] using hc.tendsto

lemma ae_pair_ne (μ : Measure ℂ) [NullSingletonClass μ] [SFinite μ] (c : ℂ) :
    ∀ᵐ zw ∂ μ.prod μ, zw.1 ≠ c ∧ zw.2 ≠ c := by
  rw [Measure.ae_prod_iff_ae_ae]
  · filter_upwards [μ.ae_ne c] with z hz
    filter_upwards [μ.ae_ne c] with w hw
    exact ⟨hz, hw⟩
  · exact ((measurableSet_eq_fun measurable_fst measurable_const).compl).inter
      ((measurableSet_eq_fun measurable_snd measurable_const).compl)

lemma crossEnergy_tendsto (μ : Measure ℂ) [IsFiniteMeasure μ] [NullSingletonClass μ] (c : ℂ) :
    Tendsto (fun a => crossEnergy μ a c) (nhds c) (nhds 0) := by
  have h := tendsto_integral_filter_of_dominated_convergence
    (μ := μ.prod μ) (l := nhds c) (F := fun a zw => crossKernel a c zw)
    (f := fun _ => (0 : ℝ)) (fun _ => (1 : ℝ))
    (Filter.Eventually.of_forall fun a => (measurable_crossKernel a c).aestronglyMeasurable)
    (Filter.Eventually.of_forall fun a => Filter.Eventually.of_forall fun zw => by
      rw [Real.norm_eq_abs, abs_of_nonneg (crossKernel_nonneg a c zw)]
      exact crossKernel_le_one a c zw)
    (integrable_const (1 : ℝ))
    ((ae_pair_ne μ c).mono fun zw hzw => crossKernel_tendsto c zw hzw.1 hzw.2)
  simpa [crossEnergy] using h

lemma ae_distinct_pair (μ : Measure ℂ) [NullSingletonClass μ] [SFinite μ] :
    ∀ᵐ zw ∂ μ.prod μ, zw.1 ≠ zw.2 := by
  apply (Measure.ae_prod_iff_ae_ae (p := fun zw : ℂ × ℂ => zw.1 ≠ zw.2)
    (measurableSet_eq_fun measurable_fst measurable_snd).compl).mpr
  exact Filter.Eventually.of_forall fun z =>
    (μ.ae_ne z).mono fun w hw => hw.symm

lemma targetEnergy_pos (ν : Measure ℂ) [IsProbabilityMeasure ν] [NullSingletonClass ν]
    (d : ℂ) : 0 < targetEnergy ν d := by
  have hp : ∀ᵐ zw ∂ ν.prod ν, 0 < targetKernel d zw := by
    filter_upwards [ae_distinct_pair ν, ae_pair_ne ν d] with zw hzw hd
    exact lt_min zero_lt_one (norm_pos_iff.mpr
      (div_ne_zero (sub_ne_zero.mpr hzw) (sub_ne_zero.mpr hd.2)))
  have hn : 0 ≤ targetEnergy ν d := integral_nonneg (targetKernel_nonneg d)
  apply lt_of_le_of_ne hn
  intro he
  have hz : targetKernel d =ᵐ[ν.prod ν] 0 :=
    (integral_eq_zero_iff_of_nonneg (targetKernel_nonneg d)
      (integrable_targetKernel ν d)).mp he.symm
  have hf : ∀ᵐ zw ∂ ν.prod ν, False := hp.and hz |>.mono fun zw h => by
    simpa [h.2] using h.1
  simpa using (ae_iff.mp hf)

lemma not_ae_energy_eq (μ ν : Measure ℂ) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] [NullSingletonClass μ] [NullSingletonClass ν]
    (c d : ℂ) (hc : c ∈ μ.support) :
    ¬ (∀ᵐ a ∂ μ, crossEnergy μ a c = targetEnergy ν d) := by
  intro he
  have ht := targetEnergy_pos ν d
  have hn : {a | crossEnergy μ a c < targetEnergy ν d} ∈ nhds c :=
    (crossEnergy_tendsto μ c).eventually (eventually_lt_nhds ht)
  have hpos := (Measure.mem_support_iff_forall c).mp hc _ hn
  have hzero : μ {a | crossEnergy μ a c < targetEnergy ν d} = 0 := by
    have hnot : ∀ᵐ a ∂ μ, ¬ crossEnergy μ a c < targetEnergy ν d :=
      he.mono fun a ha => by simp [ha]
    simpa only [ae_iff, not_not, Set.ofPred_mem_eq] using hnot
  exact (ne_of_gt hpos) hzero

lemma measurable_crossEnergy (μ : Measure ℂ) [SFinite μ] :
    Measurable (fun ac : ℂ × ℂ => crossEnergy μ ac.1 ac.2) := by
  have hm : Measurable (fun v : (ℂ × ℂ) × (ℂ × ℂ) =>
      crossKernel v.1.1 v.1.2 v.2) := by
    unfold crossKernel
    fun_prop
  exact hm.stronglyMeasurable.integral_prod_right'.measurable

lemma measurable_targetEnergy (ν : Measure ℂ) [SFinite ν] :
    Measurable (targetEnergy ν) := by
  have hm : Measurable (fun v : ℂ × (ℂ × ℂ) => targetKernel v.1 v.2) := by
    unfold targetKernel
    fun_prop
  exact hm.stronglyMeasurable.integral_prod_right'.measurable

lemma mobius_sub_target (a b c d z : ℂ) (hz : z ≠ a) :
    mobius a b c d z - d = (d - b) * (c - z) / (z - a) := by
  unfold mobius
  field_simp
  ring

lemma kernel_mobius (a b c d : ℂ) (zw : ℂ × ℂ) (hbd : b ≠ d)
    (hz : zw.1 ≠ a) (hw : zw.2 ≠ a) (hwc : zw.2 ≠ c) :
    targetKernel d (mobius a b c d zw.1, mobius a b c d zw.2) =
      crossKernel a c zw := by
  unfold targetKernel crossKernel
  congr 2
  have hma := sub_ne_zero.mpr hz
  have hwa := sub_ne_zero.mpr hw
  have hc := sub_ne_zero.mpr hwc.symm
  have hdb := sub_ne_zero.mpr hbd.symm
  rw [mobius_sub_target a b c d zw.2 hw]
  unfold mobius
  field_simp
  ring

attribute [local irreducible] crossEnergy targetEnergy

lemma measurableSet_energy_eq (μ ν : Measure ℂ) [SFinite μ] [SFinite ν] :
    MeasurableSet {v : ℂ × (ℂ × ℂ) |
      crossEnergy μ v.1 v.2.1 = targetEnergy ν v.2.2} := by
  have h₁ : Measurable (fun v : ℂ × (ℂ × ℂ) => crossEnergy μ v.1 v.2.1) :=
    (measurable_crossEnergy μ).comp
      (show Measurable (fun v : ℂ × (ℂ × ℂ) => (v.1, v.2.1)) from by fun_prop)
  have h₂ : Measurable (fun v : ℂ × (ℂ × ℂ) => targetEnergy ν v.2.2) :=
    (measurable_targetEnergy ν).comp
      (show Measurable (fun v : ℂ × (ℂ × ℂ) => v.2.2) from by fun_prop)
  exact measurableSet_eq_fun h₁ h₂

attribute [local instance] OAI.WeakPinned.Bounded.instMeasurableSpaceSphere
local instance instBorelSpaceSphere : BorelSpace Sphere := ⟨rfl⟩

lemma measurableEmbedding_sphere_coe : MeasurableEmbedding ((↑) : ℂ → Sphere) :=
  OnePoint.isOpenEmbedding_coe.measurableEmbedding

end WeakPinned.Bounded

namespace WeakPinned.Bounded
open TopologicalSpace

attribute [local instance] OAI.WeakPinned.Bounded.instMeasurableSpaceSphere_1
attribute [local instance] OAI.WeakPinned.Bounded.instBorelSpaceSphere_1
/-- A useful Portmanteau consequence with an eventual bound; measures, not
    arbitrary test function samples, are passed to the limit. -/
lemma weak_open_bound {α : ℕ → ProbabilityMeasure Sphere} {β : ProbabilityMeasure Sphere}
    (hT : Tendsto α atTop (𝓝 β)) {U : Set Sphere} (hU : IsOpen U) (b : ℝ≥0∞)
    (hbound : ∀ᶠ n in atTop, (α n : Measure Sphere) U ≤ b) :
    (β : Measure Sphere) U ≤ b := by
  have hp := ProbabilityMeasure.le_liminf_measure_open_of_tendsto hT hU
  exact hp.trans (liminf_le_of_frequently_le hbound.frequently)

/-- Neighborhood control is enough to remove a possible atom in a weak limit. -/
lemma weak_singleton_zero {α : ℕ → ProbabilityMeasure Sphere} {β : ProbabilityMeasure Sphere}
    (hT : Tendsto α atTop (𝓝 β)) (z : Sphere)
    (hsmall : ∀ ε : ℝ, 0 < ε → ∃ U : Set Sphere, IsOpen U ∧ z ∈ U ∧
      ∀ᶠ n in atTop, (α n : Measure Sphere) U ≤ ENNReal.ofReal ε) :
    (β : Measure Sphere) {z}=0 := by
  apply le_antisymm _ zero_le
  apply ENNReal.le_of_forall_pos_le_add
  intro ε hε hεtop
  have hεR : (0:ℝ) < ε := by exact_mod_cast hε
  obtain ⟨U,hU,hz,hB⟩ := hsmall (ε:ℝ) hεR
  have hb := weak_open_bound hT hU (ENNReal.ofReal (ε:ℝ)) hB
  rw [ENNReal.ofReal_coe_nnreal] at hb
  simpa only [zero_add] using (measure_mono (Set.singleton_subset_iff.mpr hz)).trans hb

/-- Finiteness and nonatomicity on the sphere follow from open-tail and disk
    bounds through the Portmanteau inequality. -/
theorem weak_limit_nonatomic {α : ℕ → ProbabilityMeasure Sphere} {β : ProbabilityMeasure Sphere}
    (hT : Tendsto α atTop (𝓝 β))
    (htail : ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, ∀ᶠ n in atTop,
      (α n : Measure Sphere) (OnePoint.some '' Metric.closedBall (0:ℂ) R)ᶜ ≤ ENNReal.ofReal ε)
    (hball : ∀ z : ℂ, ∀ ε : ℝ, 0 < ε → ∃ r : ℝ, 0 < r ∧ ∀ᶠ n in atTop,
      (α n : Measure Sphere) (OnePoint.some '' Metric.ball z r) ≤ ENNReal.ofReal ε) :
    NullSingletonClass (β : Measure Sphere) := by
  constructor
  intro z
  apply weak_singleton_zero hT z
  intro ε hε
  induction z using OnePoint.rec with
  | infty =>
    obtain ⟨R,hR⟩ := htail ε hε
    exact ⟨_,OnePoint.isOpen_compl_image_coe.mpr ⟨Metric.isClosed_closedBall,isCompact_closedBall _ _⟩,
      OnePoint.infty_notMem_image_coe,hR⟩
  | coe z =>
    obtain ⟨r,hr,hR⟩ := hball z ε hε
    exact ⟨_,OnePoint.isOpen_image_coe.mpr Metric.isOpen_ball,⟨z,Metric.mem_ball_self hr,rfl⟩,hR⟩

lemma finitePart_probability (β : ProbabilityMeasure Sphere)
    (hinfty : (β : Measure Sphere) {OnePoint.infty}=0) : IsProbabilityMeasure (finitePart β) := by
  constructor
  rw [finitePart,measurableEmbedding_sphere_coe.comap_apply,Set.image_univ]
  have hh : (β : Measure Sphere) (Set.range ((↑) : ℂ → Sphere))ᶜ=0 := by
    simpa only [OnePoint.compl_range_coe] using hinfty
  exact measure_eq_measure_of_null_sdiff (Set.subset_univ _) (by simpa only [← Set.compl_eq_univ_sdiff] using hh) |>.trans (measure_univ)

lemma finitePart_nonatomic (β : ProbabilityMeasure Sphere) [NullSingletonClass (β : Measure Sphere)] :
    NullSingletonClass (finitePart β) := by
  constructor
  intro z
  rw [finitePart,measurableEmbedding_sphere_coe.comap_apply,Set.image_singleton,measure_singleton]

lemma finitePart_map (β : ProbabilityMeasure Sphere)
    (hinfty : (β : Measure Sphere) {OnePoint.infty}=0) :
    (finitePart β).map ((↑) : ℂ → Sphere)=(β : Measure Sphere) := by
  rw [finitePart,measurableEmbedding_sphere_coe.map_comap]
  apply Measure.restrict_eq_self_of_ae_mem
  rw [ae_iff]
  change (β : Measure Sphere) (Set.range ((↑) : ℂ → Sphere))ᶜ=0
  simpa only [OnePoint.compl_range_coe] using hinfty

end WeakPinned.Bounded

end
end

end OAI
end

section
-- module Solutions.OAIQW_WeakPinned.EnergyLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u1 u2

section
noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace WeakPinned.Bounded

lemma no_energy_law (μ ν : Measure ℂ) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] [NullSingletonClass μ] [NullSingletonClass ν]
    (Q : Measure (Quad ℂ)) [IsProbabilityMeasure Q]
    (hind : Q.map (fun q => (q.1,q.2.2))=μ.prod (Q.map (fun q => q.2.2)))
    (hsupp : ∀ᵐ q ∂ Q,q.2.2.1∈μ.support)
    (he : ∀ᵐ q ∂ Q,crossEnergy μ q.1 q.2.2.1=targetEnergy ν q.2.2.2) : False := by
  let τ : Measure (ℂ × ℂ) := Q.map (fun q => q.2.2)
  have : IsProbabilityMeasure τ :=
    Measure.isProbabilityMeasure_map (by fun_prop : Measurable (fun q : ℂ × ℂ × ℂ × ℂ => q.2.2)).aemeasurable
  have hp := measurableSet_energy_eq μ ν
  have he' : ∀ᵐ v ∂ μ.prod τ,crossEnergy μ v.1 v.2.1=targetEnergy ν v.2.2 := by
    rw [← hind]
    exact (ae_map_iff (by fun_prop) hp).mpr he
  have hf : ∀ᵐ cd ∂ τ,∀ᵐ a ∂ μ,crossEnergy μ a cd.1=targetEnergy ν cd.2 :=
    (Measure.ae_ae_comm hp).mp ((Measure.ae_prod_iff_ae_ae hp).mp he')
  have hs : ∀ᵐ cd ∂ τ,cd.1∈μ.support :=
    (ae_map_iff (by fun_prop) (μ.isClosed_support.measurableSet.preimage measurable_fst)).mpr hsupp
  obtain ⟨cd,hc,hcd⟩ := (hs.and hf).exists
  exact not_ae_energy_eq μ ν cd.1 cd.2 hc hcd

lemma mobius_of_product (a b c d z v : ℂ) (hz : z≠a)
    (hp : (z-a)*(v-b)=(c-a)*(d-b)) : v=mobius a b c d z := by
  unfold mobius
  have hh : v-b=(c-a)*(d-b)/(z-a) := (eq_div_iff (sub_ne_zero.mpr hz)).mpr (by simpa [mul_comm] using hp)
  linear_combination hh

lemma expanded_kernel_eq (μ ν : Measure ℂ) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] [NullSingletonClass μ]
    (Q : Measure (Quad ℂ)) (R : Measure (Expanded ℂ))
    [IsProbabilityMeasure Q] [IsProbabilityMeasure R]
    (he : R.map Prod.fst=Q)
    (hm : R.map (fun r => (r.1,(r.2.1.1,r.2.2.1)))=Q.prod (μ.prod μ))
    (hbd : ∀ᵐ q ∂ Q,q.2.1≠q.2.2.2)
    (hz : ∀ᵐ r ∂ R,(r.2.1.1-r.1.1)*(r.2.1.2-r.1.2.1)=
      (r.1.2.2.1-r.1.1)*(r.1.2.2.2-r.1.2.1))
    (hw : ∀ᵐ r ∂ R,(r.2.2.1-r.1.1)*(r.2.2.2-r.1.2.1)=
      (r.1.2.2.1-r.1.1)*(r.1.2.2.2-r.1.2.1)) :
    ∀ᵐ r ∂ R,crossKernel r.1.1 r.1.2.2.1 (r.2.1.1,r.2.2.1)=
      targetKernel r.1.2.2.2 (r.2.1.2,r.2.2.2) := by
  have hpred : MeasurableSet {p : Quad ℂ × (ℂ × ℂ) |
      p.2.1≠p.1.1 ∧ p.2.2≠p.1.1 ∧ p.2.2≠p.1.2.2.1} := by
    measurability
  have hpair : ∀ᵐ p ∂ Q.prod (μ.prod μ),
      p.2.1≠p.1.1 ∧ p.2.2≠p.1.1 ∧ p.2.2≠p.1.2.2.1 := by
    rw [Measure.ae_prod_iff_ae_ae hpred]
    exact Eventually.of_forall fun e => by
      filter_upwards [ae_pair_ne μ e.1,ae_pair_ne μ e.2.2.1] with zw ha hc
      exact ⟨ha.1,ha.2,hc.2⟩
  rw [← hm] at hpair
  have hp := (ae_map_iff (by fun_prop) hpred).mp hpair
  have hd : ∀ᵐ r ∂ R,r.1.2.1≠r.1.2.2.2 := by
    rw [← he] at hbd
    exact (ae_map_iff measurable_fst.aemeasurable (by measurability)).mp hbd
  filter_upwards [hp,hd,hz,hw] with r hp hd hz hw
  have hz' := mobius_of_product r.1.1 r.1.2.1 r.1.2.2.1 r.1.2.2.2 _ _ hp.1 hz
  have hw' := mobius_of_product r.1.1 r.1.2.1 r.1.2.2.1 r.1.2.2.2 _ _ hp.2.1 hw
  have hh := (kernel_mobius r.1.1 r.1.2.1 r.1.2.2.1 r.1.2.2.2
    (r.2.1.1,r.2.2.1) hd hp.1 hp.2.1 hp.2.2).symm
  simpa only [← hz',← hw'] using hh

lemma expanded_energy_eq (μ ν : Measure ℂ) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (Q : Measure (Quad ℂ)) (R : Measure (Expanded ℂ))
    [IsProbabilityMeasure Q] [IsProbabilityMeasure R]
    (hm₁ : R.map (fun r => (r.1,(r.2.1.1,r.2.2.1)))=Q.prod (μ.prod μ))
    (hm₂ : R.map (fun r => (r.1,(r.2.1.2,r.2.2.2)))=Q.prod (ν.prod ν))
    (hk : ∀ᵐ r ∂ R,crossKernel r.1.1 r.1.2.2.1 (r.2.1.1,r.2.2.1)=
      targetKernel r.1.2.2.2 (r.2.1.2,r.2.2.2)) :
    ∀ᵐ q ∂ Q,crossEnergy μ q.1 q.2.2.1=targetEnergy ν q.2.2.2 := by
  apply conditional_integral_eq R Q (μ.prod μ) (ν.prod ν) Prod.fst
    (fun r => (r.2.1.1,r.2.2.1)) (fun r => (r.2.1.2,r.2.2.2))
    (by fun_prop) (by fun_prop) (by fun_prop) hm₁ hm₂
    (fun p => crossKernel p.1.1 p.1.2.2.1 p.2)
    (fun p => targetKernel p.1.2.2.2 p.2) ?_ ?_ ?_ ?_ hk
  · unfold crossKernel; fun_prop
  · unfold targetKernel; fun_prop
  · intro p
    rw [Real.norm_eq_abs,abs_of_nonneg (crossKernel_nonneg _ _ _)]
    exact crossKernel_le_one _ _ _
  · intro p
    rw [Real.norm_eq_abs,abs_of_nonneg (targetKernel_nonneg _ _)]
    exact targetKernel_le_one _ _

end WeakPinned.Bounded

end
end

end OAI
end

section
-- module Solutions.OAIQW_WeakPinned.MixtureLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u1 u2 u3

section
noncomputable section
open MeasureTheory Filter
open scoped Topology BigOperators
namespace WeakPinned.Bounded

variable {I : Type u1} {V : Type u2} {X : Type u3} [Fintype I] [Fintype V]

lemma triple_integral (w : I → ℝ) (p : I → V → ℝ) (F : I → V → ℝ) (g h : V → ℝ) :
    (∑ r,tripleWeight w p r*(F r.1 r.2.1*g r.2.2.1*h r.2.2.2))=
      ∑ i,w i*(∑ y,p i y*F i y)*(∑ z,p i z*g z)*(∑ z,p i z*h z) := by
  simp only [tripleWeight,Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i _
  calc
    _ = ∑ y,∑ z,∑ t,(w i*p i y*F i y)*(p i z*g z)*(p i t*h t) := by
      apply Finset.sum_congr rfl; intro y _
      apply Finset.sum_congr rfl; intro z _
      apply Finset.sum_congr rfl; intro t _
      ring
    _ = (∑ y,w i*(p i y*F i y))*(∑ z,p i z*g z)*(∑ t,p i t*h t) := by
      simp only [← Finset.mul_sum,← Finset.sum_mul]
      simp only [mul_assoc]
      rw [← Finset.mul_sum]
      ring
    _ = _ := by rw [← Finset.mul_sum]

lemma avg_abs_bound (p : V → ℝ) (f : V → ℝ) (H : ℝ)
    (hp : ∀ x,0≤p x) (hpsum : ∑ x,p x=1) (hf : ∀ x,|f x|≤H) :
    |∑ x,p x*f x|≤H := by
  calc
    _ ≤ ∑ x,|p x*f x| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ x,p x*|f x| := by simp only [abs_mul,abs_of_nonneg (hp _)]
    _ ≤ ∑ x,p x*H := Finset.sum_le_sum (fun x _ => mul_le_mul_of_nonneg_left (hf x) (hp x))
    _ = H := by rw [← Finset.sum_mul,hpsum,one_mul]

lemma pair_test_error (m₁ m₂ A₁ A₂ H₁ H₂ : ℝ) (hm₂ : |m₂|≤H₂) (hA₁ : |A₁|≤H₁) :
    |m₁*m₂-A₁*A₂|≤H₂*|m₁-A₁|+H₁*|m₂-A₂| := by
  calc
    _ = |(m₁-A₁)*m₂+A₁*(m₂-A₂)| := by congr 1; ring
    _ ≤ |(m₁-A₁)*m₂|+|A₁*(m₂-A₂)| := abs_add_le _ _
    _ ≤ _ := by rw [abs_mul,abs_mul]; nlinarith [abs_nonneg (m₁-A₁),abs_nonneg (m₂-A₂)]

lemma mixture_pair_test_bound (w : I → ℝ) (p : I → V → ℝ) (F : I → V → ℝ)
    (g h : V → ℝ) (A₁ A₂ C H₁ H₂ : ℝ)
    (hw : ∀ i,0≤w i) (hp : ∀ i x,0≤p i x) (hpsum : ∀ i,∑ x,p i x=1)
    (hC : 0≤C) (hF : ∀ i x,|F i x|≤C) (hh : ∀ x,|h x|≤H₂)
    (hA₁ : |A₁|≤H₁) :
    |(∑ r,tripleWeight w p r*(F r.1 r.2.1*g r.2.2.1*h r.2.2.2))-
      (∑ r,edgeWeight w p r*F r.1 r.2)*A₁*A₂|≤
      C*(H₂*(∑ i,w i*|(∑ z,p i z*g z)-A₁|)+H₁*(∑ i,w i*|(∑ z,p i z*h z)-A₂|)) := by
  let M := fun i => ∑ y,p i y*F i y
  let G := fun i => ∑ z,p i z*g z
  let H := fun i => ∑ z,p i z*h z
  have hMC (i) : |M i|≤C := avg_abs_bound _ _ _ (hp i) (hpsum i) (hF i)
  rw [triple_integral]
  have he : (∑ r,edgeWeight w p r*F r.1 r.2)=∑ i,w i*M i := by
    simp only [edgeWeight,Fintype.sum_prod_type,M,Finset.mul_sum,mul_assoc]
  rw [he]
  change |(∑ i,w i*M i*G i*H i)-(∑ i,w i*M i)*A₁*A₂|≤_
  simp only [Finset.sum_mul,← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ i,|w i*M i*G i*H i-w i*M i*A₁*A₂| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i,w i*|M i| *|G i*H i-A₁*A₂| := by
      apply Finset.sum_congr rfl; intro i _
      rw [show w i*M i*G i*H i-w i*M i*A₁*A₂ = w i*M i*(G i*H i-A₁*A₂) by ring]
      rw [abs_mul,abs_mul,abs_of_nonneg (hw i)]
    _ ≤ ∑ i,w i*C*(H₂*|G i-A₁|+H₁*|H i-A₂|) := by
      apply Finset.sum_le_sum
      intro i _
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_left (hMC i) (hw i)
      · exact pair_test_error _ _ _ _ _ _ (avg_abs_bound _ _ _ (hp i) (hpsum i) hh) hA₁
      · exact abs_nonneg _
      · exact mul_nonneg (hw i) hC
    _ = _ := by simp only [Finset.mul_sum,← Finset.sum_add_distrib,G,H]; apply Finset.sum_congr rfl; intros; ring

end WeakPinned.Bounded

end
end

end OAI
end

section
-- module Solutions.OAIQW_WeakPinned.ProductFormula
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u1 u2 u3 u4

section

/- The finite-place absolute values are norm-normalized. Dividing their logarithms
   by [K:ℚ] gives the weighted contribution of locally normalized absolute values. -/

noncomputable section
open NumberField
open scoped BigOperators

namespace WeakPinned.Arithmetic

variable {K : Type u1} [Field K]

variable [NumberField K]

lemma log_product_formula (z : K) (hz : z ≠ 0) :
    (∑ v : InfinitePlace K, (v.mult : ℝ) * Real.log (v z)) +
      ∑ᶠ v : FinitePlace K, Real.log (v z) = 0 := by
  have hi : ∀ v : InfinitePlace K, 0 < v z := fun _ => InfinitePlace.pos_iff.mpr hz
  have hf : ∀ v : FinitePlace K, 0 < v z := fun _ => FinitePlace.pos_iff.mpr hz
  have h := congrArg Real.log (NumberField.prod_abs_eq_one hz)
  rw [Real.log_mul (Finset.prod_ne_zero_iff.mpr fun v _ => pow_ne_zero _ (hi v).ne')
    (finprod_ne_zero fun v => (hf v).ne'), Real.log_prod (fun v _ => pow_ne_zero _ (hi v).ne'),
    Real.log_finprod hf, Real.log_one] at h
  simpa only [Real.log_pow] using h

lemma sum_archWeight : ∑ v : InfinitePlace K, archWeight v = 1 := by
  classical
  unfold archWeight
  rw [← Finset.sum_div, ← Nat.cast_sum, InfinitePlace.sum_mult_eq, div_self]
  exact_mod_cast (Module.finrank_pos (R := ℚ) (M := K)).ne'

lemma archWeight_nonneg (v : InfinitePlace K) : 0 ≤ archWeight v := by
  unfold archWeight
  positivity

omit [NumberField K] in
/-- Multiplicativity gives the constant depth sum on each nonzero fiber at
    every absolute value; neither the embeddings nor the field are fixed. -/
lemma raw_fiber_identity (v : AbsoluteValue K ℝ) (a b : K) (ha : a ≠ 0) (hb : b ≠ 0) :
    -Real.log (v a) + -Real.log (v b) = -Real.log (v (a * b)) := by
  rw [map_mul, Real.log_mul (v.pos ha).ne' (v.pos hb).ne']
  ring

lemma normalized_log_product_formula (z : K) (hz : z ≠ 0) :
    (∑ v : InfinitePlace K, archWeight v * (-Real.log (v z))) +
      (Module.finrank ℚ K : ℝ)⁻¹ * ∑ᶠ v : FinitePlace K, -Real.log (v z) = 0 := by
  have hh := log_product_formula z hz
  simp only [archWeight, div_eq_mul_inv]
  rw [finsum_neg_distrib]
  have he : (∑ v : InfinitePlace K, (v.mult:ℝ) * (Module.finrank ℚ K : ℝ)⁻¹ * (-Real.log (v z))) =
      -(Module.finrank ℚ K : ℝ)⁻¹ * ∑ v : InfinitePlace K, (v.mult:ℝ) * Real.log (v z) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro v _
    ring
  rw [he]
  linear_combination -(Module.finrank ℚ K : ℝ)⁻¹ * hh

end WeakPinned.Arithmetic

end
end

end OAI
end

section
-- module Solutions.OAIQW_WeakPinned.Hierarchy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u1 u2 u3

section
noncomputable section
open NumberField
open scoped BigOperators

/- Deterministic giant-removal identity. -/

noncomputable section
open MeasureTheory
open scoped Topology

namespace WeakPinned.Hierarchy
variable {P : Type u1} [Fintype P] [DecidableEq P]

namespace Depth

variable (d : Depth P)

omit [Fintype P] [DecidableEq P] in
lemma share_refl (r : ℝ) (x : P) : d.share r x x := Or.inl rfl
omit [Fintype P] [DecidableEq P] in
lemma share_symm {r : ℝ} {x y : P} (h : d.share r x y) : d.share r y x := by
  rcases h with h | h
  · exact Or.inl h.symm
  · exact Or.inr (by simpa only [d.symm y x] using h)
omit [Fintype P] in
lemma share_trans {r : ℝ} {x y z : P} (hxy : d.share r x y) (hyz : d.share r y z) :
    d.share r x z := by
  by_cases h₁ : x = y
  · subst y; exact hyz
  by_cases h₂ : y = z
  · subst z; exact hxy
  by_cases h₃ : x = z
  · exact Or.inl h₃
  exact Or.inr ((le_min (hxy.resolve_left h₁) (hyz.resolve_left h₂)).trans
    (d.ultra x y z h₁ h₂ h₃))
omit [Fintype P] [DecidableEq P] in
lemma share_mono {r t : ℝ} (htr : t ≤ r) {x y : P} (h : d.share r x y) :
    d.share t x y := h.imp_right (htr.trans ·)

omit [DecidableEq P] in
@[simp] lemma self_mem_cell (r : ℝ) (x : P) : x ∈ d.cell r x := by
  simp [share_refl]

lemma cell_eq_of_share {r : ℝ} {x y : P} (h : d.share r x y) : d.cell r x = d.cell r y := by
  ext z
  simp only [mem_cell]
  exact ⟨fun hz => d.share_trans (d.share_symm h) hz, fun hz => d.share_trans h hz⟩

omit [DecidableEq P] in
lemma cell_mono {r t : ℝ} (htr : t ≤ r) (x : P) : d.cell r x ⊆ d.cell t x := by
  intro z hz
  exact (d.mem_cell t x z).mpr (d.share_mono htr ((d.mem_cell r x z).mp hz))

lemma cell_mem_cells (r : ℝ) (x : P) : d.cell r x ∈ d.cells r := by simp

lemma cell_of_mem {r : ℝ} {C : Finset P} (hC : C ∈ d.cells r) {x : P} (hx : x ∈ C) :
    C = d.cell r x := by
  obtain ⟨z, rfl⟩ := (d.mem_cells r C).mp hC
  exact d.cell_eq_of_share ((d.mem_cell r z x).mp hx)

lemma cells_disjoint {r : ℝ} {C D : Finset P} (hC : C ∈ d.cells r)
    (hD : D ∈ d.cells r) (hne : C ≠ D) : Disjoint C D := by
  apply Finset.disjoint_left.mpr
  intro x hx hd
  exact hne ((d.cell_of_mem hC hx).trans (d.cell_of_mem hD hd).symm)

lemma cells_pair_sum (r : ℝ) (x y : P) :
    (∑ C ∈ d.cells r, (if x ∈ C ∧ y ∈ C then (1 : ℝ) else 0)) =
      if d.share r x y then 1 else 0 := by
  have h : ∀ C ∈ d.cells r, (if x ∈ C ∧ y ∈ C then (1 : ℝ) else 0) =
      if C = d.cell r x then (if d.share r x y then 1 else 0) else 0 := by
    intro C hC
    by_cases hx : x ∈ C
    · rw [d.cell_of_mem hC hx]
      simp [d.share_refl]
    · have hne : C ≠ d.cell r x := by intro he; apply hx; simpa [he] using d.self_mem_cell r x
      simp [hx, hne]
  rw [Finset.sum_congr rfl h]
  simp [d.cell_mem_cells r x]

lemma giants_unique {r : ℝ} {C D : Finset P} (hC : C ∈ d.giants r)
    (hD : D ∈ d.giants r) : C = D := by
  rw [d.mem_giants] at hC hD
  by_contra hne
  have hd := d.cells_disjoint hC.1 hD.1 hne
  have hc := Finset.card_le_univ (C ∪ D)
  rw [Finset.card_union_of_disjoint hd] at hc
  omega

lemma giant_eq {r : ℝ} {C : Finset P} (hC : C ∈ d.giants r) : d.giant r = C := by
  have he : d.giants r = {C} := Finset.ext fun D => by
    simp only [Finset.mem_singleton]
    exact ⟨fun hd => d.giants_unique hd hC, fun hd => hd ▸ hC⟩
  simp [giant, he]

lemma sumCells_formula (f : Finset P → ℝ) (r : ℝ) :
    d.sumCells f r = (∑ C ∈ d.cells r, f C) +
      ∑ C ∈ d.giants r, (f Cᶜ - f C) := by
  classical
  simp only [sumCells, transformed, Multiset.map_add, Multiset.sum_add,
    Multiset.map_map, Finset.sum, Function.comp_def]
  change (∑ C ∈ (d.cells r).filter (fun C => ¬Fintype.card P < 2*C.card), f C) +
    (∑ C ∈ d.giants r, f Cᶜ) = (∑ C ∈ d.cells r, f C) +
      ∑ C ∈ d.giants r, (f Cᶜ - f C)
  rw [Finset.sum_sub_distrib]
  have hh := Finset.sum_filter_add_sum_filter_not (d.cells r)
    (fun C => Fintype.card P < 2*C.card) f
  change (∑ C ∈ d.giants r, f C) + _ = _ at hh
  linarith

lemma pairOverlap_formula (r : ℝ) (x y : P) :
    d.pairOverlap r x y = (if d.share r x y then 1 else 0) -
      d.giantIndicator r + d.outsideIndicator r x + d.outsideIndicator r y := by
  unfold pairOverlap
  rw [d.sumCells_formula, d.cells_pair_sum]
  unfold giantIndicator outsideIndicator
  by_cases hg : (d.giants r).Nonempty
  · obtain ⟨G,hG⟩ := hg
    have he : d.giants r = {G} := Finset.ext fun C => by
      simp only [Finset.mem_singleton]
      exact ⟨fun hc => d.giants_unique hc hG, fun hc => hc ▸ hG⟩
    rw [d.giant_eq hG]
    have hg : (d.giants r).Nonempty := ⟨G,hG⟩
    simp only [he, Finset.sum_singleton, Finset.mem_compl]
    by_cases hx : x ∈ G <;> by_cases hy : y ∈ G <;> simp [hx,hy]
    ring
  · have he : d.giants r = ∅ := Finset.not_nonempty_iff_eq_empty.mp hg
    simp [he]

lemma giants_nonempty_iff (r : ℝ) : (d.giants r).Nonempty ↔
    ∃ x : P, ∃ C : Finset P, Fintype.card P < 2*C.card ∧ ∀ y ∈ C, d.share r x y := by
  constructor
  · rintro ⟨C,hC⟩
    obtain ⟨hC,hc⟩ := (d.mem_giants r C).mp hC
    obtain ⟨x,rfl⟩ := (d.mem_cells r C).mp hC
    exact ⟨x,d.cell r x,hc,fun y hy => (d.mem_cell r x y).mp hy⟩
  · rintro ⟨x,C,hc,hC⟩
    have hsub : C ⊆ d.cell r x := fun y hy => (d.mem_cell r x y).mpr (hC y hy)
    refine ⟨d.cell r x, (d.mem_giants r _).mpr ⟨d.cell_mem_cells r x, ?_⟩⟩
    have := Finset.card_le_card hsub
    omega

lemma giants_mono {r t : ℝ} (htr : t ≤ r) (hr : (d.giants r).Nonempty) :
    (d.giants t).Nonempty := by
  rw [d.giants_nonempty_iff] at hr ⊢
  obtain ⟨x,C,hc,hC⟩ := hr
  exact ⟨x,C,hc,fun y hy => d.share_mono htr (hC y hy)⟩

lemma isClosed_giants : IsClosed {r : ℝ | (d.giants r).Nonempty} := by
  simp_rw [d.giants_nonempty_iff, Set.ofPred_exists]
  apply isClosed_iUnion_of_finite
  intro x
  apply isClosed_iUnion_of_finite
  intro C
  simp only [Set.ofPred_and]
  apply IsClosed.inter
  · by_cases h : Fintype.card P < 2*C.card <;> simp [h]
  · simp_rw [Set.ofPred_forall]
    apply isClosed_iInter
    intro y
    apply isClosed_iInter
    intro hy
    by_cases hxy : x = y
    · simp [share, hxy]
    · simp only [share, hxy, false_or]
      exact isClosed_le continuous_id continuous_const

omit [DecidableEq P] in
lemma radius_nonneg : 0 ≤ d.radius := by unfold radius; positivity

omit [DecidableEq P] in
lemma abs_value_le_radius (x y : P) : |d.value x y| ≤ d.radius := by
  have hx : (∑ y, |d.value x y|) ≤ d.radius :=
    Finset.single_le_sum (fun z _ => Finset.sum_nonneg (fun w _ => abs_nonneg (d.value z w)))
      (Finset.mem_univ x)
  exact (Finset.single_le_sum (fun z _ => abs_nonneg (d.value x z)) (Finset.mem_univ y)).trans hx

omit [DecidableEq P] in
lemma cell_of_low {r : ℝ} (hr : r ≤ -d.radius) (x : P) : d.cell r x = Finset.univ := by
  ext y
  simp only [mem_cell, Finset.mem_univ, iff_true]
  exact Or.inr (hr.trans (abs_le.mp (d.abs_value_le_radius x y)).1)

omit [DecidableEq P] in
lemma cell_of_high {r : ℝ} (hr : d.radius < r) (x : P) : d.cell r x = {x} := by
  ext y
  simp only [mem_cell, share, Finset.mem_singleton]
  have hh : ¬r ≤ d.value x y := not_le.mpr ((abs_le.mp (d.abs_value_le_radius x y)).2.trans_lt hr)
  simp [hh, eq_comm]

lemma giants_of_low (hn : 2 ≤ Fintype.card P) {r : ℝ} (hr : r ≤ -d.radius) :
    (d.giants r).Nonempty := by
  have : Nonempty P := Fintype.card_pos_iff.mp (by omega)
  obtain ⟨x⟩ := ‹Nonempty P›
  refine ⟨Finset.univ, (d.mem_giants r _).mpr ⟨?_, ?_⟩⟩
  · exact (d.mem_cells r _).mpr ⟨x, d.cell_of_low hr x⟩
  · simp only [Finset.card_univ]
    omega

lemma giants_le_radius (hn : 2 ≤ Fintype.card P) {r : ℝ} (hr : (d.giants r).Nonempty) :
    r ≤ d.radius := by
  by_contra! h
  obtain ⟨C,hC⟩ := hr
  obtain ⟨hC,hc⟩ := (d.mem_giants r C).mp hC
  obtain ⟨x,rfl⟩ := (d.mem_cells r C).mp hC
  rw [d.cell_of_high h x, Finset.card_singleton] at hc
  omega

lemma giants_cutoff (hn : 2 ≤ Fintype.card P) (r : ℝ) :
    (d.giants r).Nonempty ↔ r ≤ d.M := by
  have hne : Set.Nonempty {t : ℝ | (d.giants t).Nonempty} := ⟨-d.radius,d.giants_of_low hn le_rfl⟩
  have hbd : BddAbove {t : ℝ | (d.giants t).Nonempty} := ⟨d.radius,fun t ht => d.giants_le_radius hn ht⟩
  exact ⟨fun hr => le_csSup hbd hr, fun hr =>
    d.giants_mono hr (d.isClosed_giants.csSup_mem hne hbd)⟩

lemma M_bounds (hn : 2 ≤ Fintype.card P) : -d.radius ≤ d.M ∧ d.M ≤ d.radius := by
  constructor
  · exact (d.giants_cutoff hn _).mp (d.giants_of_low hn le_rfl)
  · exact d.giants_le_radius hn ((d.giants_cutoff hn _).mpr le_rfl)

omit [DecidableEq P] in
lemma measurable_cell (x : P) : Measurable (fun r : ℝ => d.cell r x) := by
  apply measurable_finset_iff.mpr
  intro y
  simp only [mem_cell, share]
  exact measurable_const.or (measurableSet_setOfPred.mp (measurableSet_le measurable_id measurable_const))

lemma measurable_cells : Measurable d.cells := by
  have hm : Measurable (fun r : ℝ => fun x : P => d.cell r x) :=
    measurable_pi_iff.mpr (d.measurable_cell)
  exact (measurable_of_finite (fun f : P → Finset P => Finset.univ.image f)).comp hm

lemma measurable_giants : Measurable d.giants :=
  (measurable_of_finite (fun s : Finset (Finset P) =>
    s.filter (fun C : Finset P => Fintype.card P < 2*C.card))).comp d.measurable_cells

lemma measurable_giant : Measurable d.giant :=
  (measurable_of_finite (fun s : Finset (Finset P) => s.biUnion id)).comp d.measurable_giants

lemma measurable_giantIndicator : Measurable d.giantIndicator :=
  (measurable_of_finite (fun s : Finset (Finset P) => if s.Nonempty then (1 : ℝ) else 0)).comp
    d.measurable_giants

lemma measurable_outsideIndicator (x : P) : Measurable (fun r => d.outsideIndicator r x) := by
  have hm : Measurable (fun r : ℝ => (d.giants r, d.giant r)) :=
    d.measurable_giants.prodMk d.measurable_giant
  exact (measurable_of_finite
    (fun st : Finset (Finset P) × Finset P => if st.1.Nonempty ∧ x ∉ st.2 then (1 : ℝ) else 0)).comp hm

lemma measurable_pairOverlap (x y : P) : Measurable (fun r => d.pairOverlap r x y) := by
  have hm : Measurable (fun r : ℝ => if d.share r x y then (1 : ℝ) else 0) := by
    apply Measurable.ite _ measurable_const measurable_const
    apply measurableSet_setOfPred.mpr
    exact measurable_const.or (measurableSet_setOfPred.mp (measurableSet_le measurable_id measurable_const))
  have ht : Measurable (fun r =>
      (if d.share r x y then (1 : ℝ) else 0) - d.giantIndicator r +
        d.outsideIndicator r x + d.outsideIndicator r y) :=
    ((hm.sub d.measurable_giantIndicator).add (d.measurable_outsideIndicator x)).add
      (d.measurable_outsideIndicator y)
  simpa only [pairOverlap_formula] using ht

lemma outsideIndicator_bounds (r : ℝ) (x : P) :
    0 ≤ d.outsideIndicator r x ∧ d.outsideIndicator r x ≤ 1 := by
  unfold outsideIndicator
  split_ifs <;> norm_num

lemma pairOverlap_bounds (r : ℝ) (x y : P) :
    0 ≤ d.pairOverlap r x y ∧ d.pairOverlap r x y ≤ 2 := by
  have lo : 0 ≤ d.pairOverlap r x y := by
    unfold pairOverlap sumCells
    apply Multiset.sum_nonneg
    intro t ht
    obtain ⟨C,hC,rfl⟩ := Multiset.mem_map.mp ht
    split_ifs <;> norm_num
  refine ⟨lo, ?_⟩
  rw [pairOverlap_formula]
  have hx := (d.outsideIndicator_bounds r x).2
  have hy := (d.outsideIndicator_bounds r y).2
  by_cases hg : (d.giants r).Nonempty
  · simp only [giantIndicator, hg, reduceIte]
    split_ifs <;> linarith
  · simp [giantIndicator, outsideIndicator, hg]
    split_ifs <;> norm_num

lemma outsideIndicator_zero_low (hn : 2 ≤ Fintype.card P) {r : ℝ} (hr : r ≤ -d.radius)
    (x : P) : d.outsideIndicator r x = 0 := by
  have hg : Finset.univ ∈ d.giants r := (d.mem_giants r _).mpr ⟨
    (d.mem_cells r _).mpr ⟨x,d.cell_of_low hr x⟩, by simp only [Finset.card_univ]; omega⟩
  simp [outsideIndicator, d.giant_eq hg]

lemma outsideIndicator_zero_high (hn : 2 ≤ Fintype.card P) {r : ℝ} (hr : d.radius < r)
    (x : P) : d.outsideIndicator r x = 0 := by
  have hg : ¬(d.giants r).Nonempty := fun hg => not_le.mpr hr (d.giants_le_radius hn hg)
  simp [outsideIndicator, hg]

lemma pairOverlap_zero_low (hn : 2 ≤ Fintype.card P) {r : ℝ} (hr : r ≤ -d.radius)
    (x y : P) : d.pairOverlap r x y = 0 := by
  have hxy : d.share r x y := Or.inr (hr.trans (abs_le.mp (d.abs_value_le_radius x y)).1)
  simp [pairOverlap_formula, giantIndicator, d.giants_of_low hn hr,
    d.outsideIndicator_zero_low hn hr, hxy]

lemma pairOverlap_zero_high (hn : 2 ≤ Fintype.card P) {r : ℝ} (hr : d.radius < r)
    (x y : P) (hxy : x ≠ y) : d.pairOverlap r x y = 0 := by
  have hg : ¬(d.giants r).Nonempty := fun hg => not_le.mpr hr (d.giants_le_radius hn hg)
  have hs : ¬d.share r x y := by
    simp only [share, hxy, false_or]
    exact not_le.mpr ((abs_le.mp (d.abs_value_le_radius x y)).2.trans_lt hr)
  simp [pairOverlap_formula, giantIndicator, hg, hs, d.outsideIndicator_zero_high hn hr]

/- The diagonal is deliberately absent from overlapLength's domain: the
   transformed singleton tails have infinite diagonal overlap. -/

lemma integrable_supported_Icc {f : ℝ → ℝ} {a b C : ℝ}
    (hm : Measurable f) (hb : ∀ r, ‖f r‖ ≤ C)
    (hz : ∀ r ∉ Set.Icc a b, f r = 0) : Integrable f := by
  have hi : IntegrableOn f (Set.Icc a b) :=
    IntegrableOn.of_bound measure_Icc_lt_top hm.aestronglyMeasurable C
      (Filter.Eventually.of_forall hb)
  have he : (Set.Icc a b).indicator f = f := by
    apply Set.indicator_eq_self.mpr
    intro r hr
    by_contra hn
    exact hr (hz r hn)
  simpa only [he] using hi.integrable_indicator measurableSet_Icc

lemma outsideIndicator_zero_compl (hn : 2 ≤ Fintype.card P) (x : P) :
    ∀ r ∉ Set.Icc (-d.radius) d.radius, d.outsideIndicator r x = 0 := by
  intro r hr
  by_cases hlo : r ≤ -d.radius
  · exact d.outsideIndicator_zero_low hn hlo x
  · exact d.outsideIndicator_zero_high hn
      (lt_of_not_ge (fun hhi => hr ⟨le_of_not_ge hlo, hhi⟩)) x

lemma pairOverlap_zero_compl (hn : 2 ≤ Fintype.card P) (x y : P) (hxy : x ≠ y) :
    ∀ r ∉ Set.Icc (-d.radius) d.radius, d.pairOverlap r x y = 0 := by
  intro r hr
  by_cases hlo : r ≤ -d.radius
  · exact d.pairOverlap_zero_low hn hlo x y
  · exact d.pairOverlap_zero_high hn
      (lt_of_not_ge (fun hhi => hr ⟨le_of_not_ge hlo, hhi⟩)) x y hxy

lemma integrable_outsideIndicator (hn : 2 ≤ Fintype.card P) (x : P) :
    Integrable (fun r => d.outsideIndicator r x) := by
  apply integrable_supported_Icc (d.measurable_outsideIndicator x) (C := 1)
  · intro r
    rw [Real.norm_eq_abs, abs_of_nonneg (d.outsideIndicator_bounds r x).1]
    exact (d.outsideIndicator_bounds r x).2
  · exact d.outsideIndicator_zero_compl hn x

lemma integrable_pairOverlap (hn : 2 ≤ Fintype.card P) (x y : P) (hxy : x ≠ y) :
    Integrable (fun r => d.pairOverlap r x y) := by
  apply integrable_supported_Icc (d.measurable_pairOverlap x y) (C := 2)
  · intro r
    rw [Real.norm_eq_abs, abs_of_nonneg (d.pairOverlap_bounds r x y).1]
    exact (d.pairOverlap_bounds r x y).2
  · exact d.pairOverlap_zero_compl hn x y hxy

lemma integral_cutoff {R a : ℝ} (hR : 0 ≤ R) (ha : a ∈ Set.Icc (-R) R) :
    (∫ r : ℝ in Set.Icc (-R) R, if r ≤ a then (1 : ℝ) else 0) = a + R := by
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by linarith : -R ≤ R)]
  change (∫ r : ℝ in (-R)..R, {r : ℝ | r ≤ a}.indicator (fun _ => (1 : ℝ)) r) = a + R
  rw [intervalIntegral.integral_indicator ha, intervalIntegral.integral_const]
  simp

lemma depth_identity (hn : 2 ≤ Fintype.card P) (x y : P) (hxy : x ≠ y) :
    d.value x y = d.M + d.overlapLength x y hxy - d.potential x - d.potential y := by
  let I := Set.Icc (-d.radius) d.radius
  have hoc : IntegrableOn (fun r : ℝ => if r ≤ d.value x y then (1 : ℝ) else 0) I := by
    apply IntegrableOn.of_bound measure_Icc_lt_top
      ((measurable_const.ite (measurableSet_le measurable_id measurable_const)
        measurable_const).aestronglyMeasurable) 1
    exact Filter.Eventually.of_forall (fun r => by split_ifs <;> norm_num)
  have hgc : IntegrableOn (fun r : ℝ => if r ≤ d.M then (1 : ℝ) else 0) I := by
    apply IntegrableOn.of_bound measure_Icc_lt_top
      ((measurable_const.ite (measurableSet_le measurable_id measurable_const)
        measurable_const).aestronglyMeasurable) 1
    exact Filter.Eventually.of_forall (fun r => by split_ifs <;> norm_num)
  have hs : IntegrableOn (fun r : ℝ => (if r ≤ d.value x y then (1 : ℝ) else 0) -
      (if r ≤ d.M then (1 : ℝ) else 0)) I := hoc.sub hgc
  have hx := (d.integrable_outsideIndicator hn x).integrableOn (s := I)
  have hy := (d.integrable_outsideIndicator hn y).integrableOn (s := I)
  have ha : IntegrableOn (fun r : ℝ => (if r ≤ d.value x y then (1 : ℝ) else 0) -
      (if r ≤ d.M then (1 : ℝ) else 0) + d.outsideIndicator r x) I := hs.add hx
  have he : (∫ r in I, d.pairOverlap r x y) =
      (∫ r in I, if r ≤ d.value x y then (1 : ℝ) else 0) -
      (∫ r in I, if r ≤ d.M then (1 : ℝ) else 0) +
      (∫ r in I, d.outsideIndicator r x) + (∫ r in I, d.outsideIndicator r y) := by
    calc
      _ = ∫ r in I, ((if r ≤ d.value x y then (1 : ℝ) else 0) -
          (if r ≤ d.M then 1 else 0) + d.outsideIndicator r x + d.outsideIndicator r y) := by
        apply setIntegral_congr_fun measurableSet_Icc
        intro r _
        simp only [pairOverlap_formula, share, hxy, false_or, giantIndicator,
          d.giants_cutoff hn]
      _ = _ := by rw [integral_add ha hy, integral_add hs hx, integral_sub hoc hgc]
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero (d.pairOverlap_zero_compl hn x y hxy)] at he
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero (d.outsideIndicator_zero_compl hn x),
    setIntegral_eq_integral_of_forall_compl_eq_zero (d.outsideIndicator_zero_compl hn y)] at he
  change d.overlapLength x y hxy = _ at he
  dsimp only [I] at he
  rw [integral_cutoff d.radius_nonneg (abs_le.mp (d.abs_value_le_radius x y)),
    integral_cutoff d.radius_nonneg (d.M_bounds hn)] at he
  change d.overlapLength x y hxy = _ - _ + d.potential x + d.potential y at he
  linarith

lemma potential_nonneg (x : P) : 0 ≤ d.potential x :=
  integral_nonneg (fun r => (d.outsideIndicator_bounds r x).1)

lemma overlapLength_nonneg (x y : P) (hxy : x ≠ y) : 0 ≤ d.overlapLength x y hxy :=
  integral_nonneg (fun r => (d.pairOverlap_bounds r x y).1)

lemma integral_bound_supported {f : ℝ → ℝ} {R C : ℝ} (hR : 0 ≤ R)
    (hi : Integrable f) (hb : ∀ r, f r ≤ C)
    (hz : ∀ r ∉ Set.Icc (-R) R, f r = 0) : (∫ r, f r) ≤ 2*R*C := by
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hz]
  have hh := integral_mono (hi.integrableOn (s := Set.Icc (-R) R))
    (integrableOn_const (s := Set.Icc (-R) R) (μ := volume)
      (C := C) (measure_Icc_lt_top.ne)) (fun r => hb r)
  rw [setIntegral_const] at hh
  simp only [Measure.real, Real.volume_Icc, sub_neg_eq_add,
    ENNReal.toReal_ofReal (by linarith : 0 ≤ R+R), smul_eq_mul] at hh
  nlinarith

lemma potential_le (hn : 2 ≤ Fintype.card P) (x : P) : d.potential x ≤ 2*d.radius := by
  have hh := integral_bound_supported d.radius_nonneg (d.integrable_outsideIndicator hn x)
    (fun r => (d.outsideIndicator_bounds r x).2) (d.outsideIndicator_zero_compl hn x)
  change d.potential x ≤ _ at hh
  simpa only [mul_one] using hh

lemma overlapLength_le (hn : 2 ≤ Fintype.card P) (x y : P) (hxy : x ≠ y) :
    d.overlapLength x y hxy ≤ 4*d.radius := by
  have hh := integral_bound_supported d.radius_nonneg (d.integrable_pairOverlap hn x y hxy)
    (fun r => (d.pairOverlap_bounds r x y).2) (d.pairOverlap_zero_compl hn x y hxy)
  change d.overlapLength x y hxy ≤ _ at hh
  linarith

lemma zero_values (hn : 2 ≤ Fintype.card P) (hzero : ∀ x y, d.value x y = 0) :
    d.M = 0 ∧ (∀ x, d.potential x = 0) ∧
      (∀ x y (hxy : x ≠ y), d.overlapLength x y hxy = 0) := by
  have hr : d.radius = 0 := by simp [radius, hzero]
  refine ⟨?_, ?_, ?_⟩
  · have := d.M_bounds hn
    rw [hr] at this
    linarith [this.1, this.2]
  · intro x
    have := d.potential_le hn x
    rw [hr] at this
    linarith [d.potential_nonneg x]
  · intro x y hxy
    have := d.overlapLength_le hn x y hxy
    rw [hr] at this
    linarith [d.overlapLength_nonneg x y hxy]

/- Joint measurability and averaging over a family of realized hierarchies. -/
section Param
variable {Ω : Type u3} [MeasurableSpace Ω] (D : Ω → Depth P)
  (hD : ∀ x y, Measurable (fun ω => (D ω).value x y))
  (R : Ω → ℝ) (hR : Measurable R)
include hD hR

omit [DecidableEq P] in
lemma measurable_cell_param (x : P) : Measurable (fun ω => (D ω).cell (R ω) x) := by
  apply measurable_finset_iff.mpr
  intro y
  simp only [mem_cell, share]
  exact measurable_const.or (measurableSet_setOfPred.mp (measurableSet_le hR (hD x y)))

lemma measurable_cells_param : Measurable (fun ω => (D ω).cells (R ω)) := by
  have hm : Measurable (fun ω => fun x : P => (D ω).cell (R ω) x) :=
    measurable_pi_iff.mpr (measurable_cell_param D hD R hR)
  exact (measurable_of_finite (fun f : P → Finset P => Finset.univ.image f)).comp hm

lemma measurable_giants_param : Measurable (fun ω => (D ω).giants (R ω)) :=
  (measurable_of_finite (fun s : Finset (Finset P) =>
    s.filter (fun C : Finset P => Fintype.card P < 2*C.card))).comp
      (measurable_cells_param D hD R hR)

lemma measurable_giant_param : Measurable (fun ω => (D ω).giant (R ω)) :=
  (measurable_of_finite (fun s : Finset (Finset P) => s.biUnion id)).comp
    (measurable_giants_param D hD R hR)

lemma measurable_giantIndicator_param : Measurable (fun ω => (D ω).giantIndicator (R ω)) :=
  (measurable_of_finite (fun s : Finset (Finset P) => if s.Nonempty then (1 : ℝ) else 0)).comp
    (measurable_giants_param D hD R hR)

lemma measurable_outsideIndicator_param (x : P) : Measurable (fun ω => (D ω).outsideIndicator (R ω) x) := by
  have hm := (measurable_giants_param D hD R hR).prodMk (measurable_giant_param D hD R hR)
  exact (measurable_of_finite
    (fun st : Finset (Finset P) × Finset P => if st.1.Nonempty ∧ x ∉ st.2 then (1 : ℝ) else 0)).comp hm

lemma measurable_pairOverlap_param (x y : P) : Measurable (fun ω => (D ω).pairOverlap (R ω) x y) := by
  have hm : Measurable (fun ω => if (D ω).share (R ω) x y then (1:ℝ) else 0) := by
    apply Measurable.ite _ measurable_const measurable_const
    apply measurableSet_setOfPred.mpr
    exact measurable_const.or (measurableSet_setOfPred.mp (measurableSet_le hR (hD x y)))
  have hh : Measurable (fun ω => (if (D ω).share (R ω) x y then (1:ℝ) else 0) -
      (D ω).giantIndicator (R ω) + (D ω).outsideIndicator (R ω) x + (D ω).outsideIndicator (R ω) y) :=
    ((hm.sub (measurable_giantIndicator_param D hD R hR)).add
    (measurable_outsideIndicator_param D hD R hR x)).add
    (measurable_outsideIndicator_param D hD R hR y)
  simpa only [pairOverlap_formula, Pi.add_apply, Pi.sub_apply] using hh

omit hR
lemma measurable_potential_param (x : P) : Measurable (fun ω => (D ω).potential x) := by
  have hm : Measurable (fun p : Ω × ℝ => (D p.1).outsideIndicator p.2 x) :=
    measurable_outsideIndicator_param (P := P) (Ω := Ω × ℝ) (fun p : Ω × ℝ => D p.1)
      (fun x y => (hD x y).comp measurable_fst) Prod.snd measurable_snd x
  simpa only [potential] using hm.stronglyMeasurable.integral_prod_right.measurable

lemma measurable_overlapLength_param (x y : P) (hxy : x ≠ y) :
    Measurable (fun ω => (D ω).overlapLength x y hxy) := by
  have hm : Measurable (fun p : Ω × ℝ => (D p.1).pairOverlap p.2 x y) :=
    measurable_pairOverlap_param (P := P) (Ω := Ω × ℝ) (fun p : Ω × ℝ => D p.1)
      (fun x y => (hD x y).comp measurable_fst) Prod.snd measurable_snd x y
  simpa only [overlapLength] using hm.stronglyMeasurable.integral_prod_right.measurable

lemma measurable_M_param (hn : 2 ≤ Fintype.card P) : Measurable (fun ω => (D ω).M) := by
  obtain ⟨x,hx,y,hy,hxy⟩ := Finset.one_lt_card.mp (show 1 < (Finset.univ : Finset P).card by simpa using (show 1 < Fintype.card P by omega))
  have hh := (((hD x y).sub (measurable_overlapLength_param D hD x y hxy)).add
    (measurable_potential_param D hD x)).add (measurable_potential_param D hD y)
  have he : (fun ω => (D ω).value x y - (D ω).overlapLength x y hxy +
      (D ω).potential x + (D ω).potential y) = (fun ω => (D ω).M) := by
    funext ω
    have := (D ω).depth_identity hn x y hxy
    linarith
  change Measurable (fun ω => (D ω).value x y - (D ω).overlapLength x y hxy +
      (D ω).potential x + (D ω).potential y) at hh
  rwa [he] at hh

variable {μ : Measure Ω} (hi : ∀ x y, Integrable (fun ω => (D ω).value x y) μ)
include hi

omit [DecidableEq P] in
omit hD in
lemma integrable_radius_param : Integrable (fun ω => (D ω).radius) μ := by
  unfold radius
  exact integrable_finsetSum _ (fun x _ => integrable_finsetSum _ (fun y _ => (hi x y).abs))

lemma integrable_potential_param (hn : 2 ≤ Fintype.card P) (x : P) :
    Integrable (fun ω => (D ω).potential x) μ := by
  apply Integrable.mono' ((integrable_radius_param D hi).const_mul 2)
    (measurable_potential_param D hD x).aestronglyMeasurable
  filter_upwards with ω
  rw [Real.norm_eq_abs, abs_of_nonneg ((D ω).potential_nonneg x)]
  exact (D ω).potential_le hn x

lemma integrable_overlapLength_param (hn : 2 ≤ Fintype.card P) (x y : P) (hxy : x ≠ y) :
    Integrable (fun ω => (D ω).overlapLength x y hxy) μ := by
  apply Integrable.mono' ((integrable_radius_param D hi).const_mul 4)
    (measurable_overlapLength_param D hD x y hxy).aestronglyMeasurable
  filter_upwards with ω
  rw [Real.norm_eq_abs, abs_of_nonneg ((D ω).overlapLength_nonneg x y hxy)]
  exact (D ω).overlapLength_le hn x y hxy

lemma integrable_M_param (hn : 2 ≤ Fintype.card P) : Integrable (fun ω => (D ω).M) μ := by
  apply Integrable.mono' (integrable_radius_param D hi) (measurable_M_param D hD hn).aestronglyMeasurable
  filter_upwards with ω
  rw [Real.norm_eq_abs]
  exact abs_le.mpr ((D ω).M_bounds hn)

lemma integral_depth_identity (hn : 2 ≤ Fintype.card P) (x y : P) (hxy : x ≠ y) :
    (∫ ω, (D ω).value x y ∂μ) =
      (∫ ω, (D ω).M ∂μ) + (∫ ω, (D ω).overlapLength x y hxy ∂μ) -
      (∫ ω, (D ω).potential x ∂μ) - (∫ ω, (D ω).potential y ∂μ) := by
  have hiM := integrable_M_param D hD hi hn
  have hiL := integrable_overlapLength_param D hD hi hn x y hxy
  have hix := integrable_potential_param D hD hi hn x
  have hiy := integrable_potential_param D hD hi hn y
  calc
    _ = ∫ ω, (D ω).M + (D ω).overlapLength x y hxy - (D ω).potential x - (D ω).potential y ∂μ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun ω => (D ω).depth_identity hn x y hxy)
    _ = _ := by
      have h₁ : Integrable (fun ω => (D ω).M + (D ω).overlapLength x y hxy) μ := hiM.add hiL
      have h₂ : Integrable (fun ω => (D ω).M + (D ω).overlapLength x y hxy - (D ω).potential x) μ := h₁.sub hix
      rw [integral_sub h₂ hiy, integral_sub h₁ hix, integral_add hiM hiL]
end Param

end Depth
end WeakPinned.Hierarchy

end
end
end

end OAI
end

section
-- module Solutions.OAIQW_WeakPinned.RandomGrids
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u1 u2 u3

section
noncomputable section
open NumberField
open scoped BigOperators
noncomputable section
open MeasureTheory
open scoped Topology

/- Square-grid construction and the finite-shift sharing law. -/

noncomputable section
open MeasureTheory
open scoped Topology ENNReal
namespace WeakPinned.Grid

lemma bin_period {l : ℝ} (hl : 0 < l) (s x : ℝ) :
    bin l (s+l) x = bin l s x - 1 := by
  unfold bin
  rw [show (x-(s+l))/l = (x-s)/l - 1 by field_simp; ring]
  exact Int.floor_sub_one _

lemma shares_period {l : ℝ} (hl : 0 < l) (x y : ℝ) :
    Function.Periodic (fun s => shares l s x y) l := by
  intro s
  simp [shares, bin_period hl]

lemma shares_symm (l s x y : ℝ) : shares l s x y = shares l s y x := by
  simp only [shares, eq_comm]

lemma measurable_shares (l x y : ℝ) : Measurable (fun s => shares l s x y) := by
  apply Measurable.ite _ measurable_const measurable_const
  exact measurableSet_eq_fun
    (((measurable_const.sub measurable_id).div_const l).floor)
    (((measurable_const.sub measurable_id).div_const l).floor)

lemma bin_small_shift {l x s : ℝ} (hl : 0 < l) (hs : s ∈ Set.Ioc x (x+l)) :
    bin l s x = -1 := by
  apply Int.floor_eq_iff.mpr
  constructor
  · apply (le_div_iff₀ hl).mpr
    norm_num
    linarith [hs.2]
  · apply (div_lt_iff₀ hl).mpr
    norm_num
    linarith [hs.1]

lemma shares_small_shift {l x y s : ℝ} (hl : 0 < l) (hxy : x ≤ y)
    (hs : s ∈ Set.Ioc x (x+l)) : shares l s x y = if y < s then 1 else 0 := by
  have he : bin l s y = -1 ↔ y < s := by
    simp only [bin, Int.floor_eq_iff]
    constructor
    · intro h
      have := (div_lt_iff₀ hl).mp h.2
      norm_num at this
      linarith
    · intro h
      constructor
      · apply (le_div_iff₀ hl).mpr
        norm_num
        linarith [hs.2]
      · apply (div_lt_iff₀ hl).mpr
        norm_num
        linarith
  simp only [shares, bin_small_shift hl hs, eq_comm (a := (-1 : ℤ))]
  simp only [he]

lemma shares_integral {l : ℝ} (hl : 0 < l) (x y : ℝ) :
    (∫ s : ℝ in Set.Ioc 0 l, shares l s x y) = max 0 (l-|x-y|) := by
  wlog hxy : x ≤ y
  · simpa only [shares_symm l _ x y, abs_sub_comm x y] using this hl y x (le_of_not_ge hxy)
  have hp := (shares_period hl x y).intervalIntegral_add_eq 0 x
  simp only [zero_add] at hp
  rw [intervalIntegral.integral_of_le hl.le,
    intervalIntegral.integral_of_le (by linarith : x ≤ x+l)] at hp
  rw [hp]
  have he : (∫ s : ℝ in Set.Ioc x (x+l), shares l s x y) =
      ∫ s : ℝ in Set.Ioc x (x+l), if y < s then (1 : ℝ) else 0 := by
    apply setIntegral_congr_fun measurableSet_Ioc
    intro s hs
    exact shares_small_shift hl hxy hs
  rw [he]
  change (∫ s : ℝ in Set.Ioc x (x+l), (Set.Ioi y).indicator (fun _ => (1 : ℝ)) s) = _
  rw [setIntegral_indicator measurableSet_Ioi]
  rw [show Set.Ioc x (x+l) ∩ Set.Ioi y = Set.Ioc y (x+l) by
    ext s; simp only [Set.mem_inter_iff, Set.mem_Ioc, Set.mem_Ioi]; constructor
    · rintro ⟨⟨h₁,h₂⟩,h₃⟩; exact ⟨h₃,h₂⟩
    · intro h; exact ⟨⟨hxy.trans_lt h.1,h.2⟩,h.1⟩]
  rw [setIntegral_const]
  simp only [Measure.real, Real.volume_Ioc, smul_eq_mul, mul_one, ENNReal.toReal_ofReal']
  rw [abs_of_nonpos (sub_nonpos.mpr hxy)]
  rw [max_comm]
  congr 1
  ring

lemma shares_integrableOn (l x y a b : ℝ) :
    IntegrableOn (fun s => shares l s x y) (Set.Ioc a b) := by
  apply IntegrableOn.of_bound measure_Ioc_lt_top (measurable_shares l x y).aestronglyMeasurable 1
  exact Filter.Eventually.of_forall (fun s => by unfold shares; split_ifs <;> norm_num)

lemma shares_gap {l : ℝ} (hl : 0 < l) {s x y : ℝ}
    (h : bin l s x = bin l s y) : |x-y| < l := by
  have hx := Int.floor_le ((x-s)/l)
  have hy := Int.lt_floor_add_one ((y-s)/l)
  have hx' := Int.floor_le ((y-s)/l)
  have hy' := Int.lt_floor_add_one ((x-s)/l)
  change (bin l s x : ℝ) ≤ (x-s)/l at hx
  change (y-s)/l < (bin l s y : ℝ) + 1 at hy
  change (bin l s y : ℝ) ≤ (y-s)/l at hx'
  change (x-s)/l < (bin l s x : ℝ) + 1 at hy'
  rw [h] at hx hy'
  rw [abs_lt]
  constructor
  · have : (y-s)/l < (x-s)/l+1 := by linarith
    have hh := (div_lt_iff₀ hl).mp this
    field_simp at hh
    linarith
  · have : (x-s)/l < (y-s)/l+1 := by linarith
    have hh := (div_lt_iff₀ hl).mp this
    field_simp at hh
    linarith

lemma bin_double {l : ℝ} (hl : 0 < l) (s x : ℝ) (b : ℤ) :
    bin (2*l) (s+b*l) x = (bin l s x-b)/2 := by
  unfold bin
  rw [show (x-(s+b*l))/(2*l) = ((x-s)/l-b)/2 by field_simp; ring]
  have hh := Int.floor_div_natCast (((x-s)/l)-(b:ℝ)) 2
  norm_num only [Nat.cast_ofNat, Int.floor_sub_intCast] at hh
  exact hh

lemma nested_bins {l : ℝ} (hl : 0 < l) (s x y : ℝ) (b : ℤ)
    (h : bin l s x = bin l s y) : bin (2*l) (s+b*l) x = bin (2*l) (s+b*l) y := by
  rw [bin_double hl, bin_double hl, h]

lemma uniformInterval_probability {l : ℝ} (hl : 0 < l) :
    IsProbabilityMeasure (uniformInterval l) := by
  constructor
  simp only [uniformInterval, Measure.smul_apply, Measure.restrict_apply MeasurableSet.univ,
    Set.univ_inter, Real.volume_Ioc, sub_zero, smul_eq_mul]
  exact ENNReal.inv_mul_cancel (ne_of_gt (ENNReal.ofReal_pos.mpr hl)) ENNReal.ofReal_ne_top

instance uniformInterval_finite (l : ℝ) : IsFiniteMeasure (uniformInterval l) := by
  by_cases hl : 0 < l
  · let := uniformInterval_probability hl
    infer_instance
  · have hz : uniformInterval l = 0 := by
      simp [uniformInterval, Set.Ioc_eq_empty_of_le (not_lt.mp hl)]
    rw [hz]
    infer_instance

lemma translate_restrict_Ioc (l : ℝ) :
    (volume.restrict (Set.Ioc 0 l)).map (fun x => x+l) =
      volume.restrict (Set.Ioc l (l+l)) := by
  have hh := (measurePreserving_add_right volume l).restrict_preimage
    (measurableSet_Ioc (a := l) (b := l+l))
  have he : (fun x : ℝ => x+l) ⁻¹' Set.Ioc l (l+l) = Set.Ioc 0 l := by
    ext x
    simp only [Set.mem_preimage, Set.mem_Ioc]
    constructor <;> intro h <;> constructor <;> linarith [h.1,h.2]
  rw [he] at hh
  exact hh.map_eq

lemma binaryStep_eq (l : ℝ) :
    binaryStep l = (2 : ℝ≥0∞)⁻¹ • Measure.dirac 0 + (2 : ℝ≥0∞)⁻¹ • Measure.dirac l := by
  simp only [binaryStep, ProbabilityTheory.bernoulliMeasure_def]
  rw [← Measure.coe_nnreal_smul, ← Measure.coe_nnreal_smul]
  congr 2
  · rw [← ENNReal.ofReal_coe_nnreal]
    change ENNReal.ofReal ((1:ℝ)/2) = _
    rw [ENNReal.ofReal_div_of_pos (by norm_num)]
    norm_num
  · rw [← ENNReal.ofReal_coe_nnreal]
    change ENNReal.ofReal (1-(1:ℝ)/2) = _
    norm_num only [show (1-(1:ℝ)/2) = 1/2 by norm_num]
    rw [ENNReal.ofReal_div_of_pos (by norm_num)]
    norm_num

lemma uniform_double {l : ℝ} (hl : 0 < l) :
    (uniformInterval l).conv (binaryStep l) = uniformInterval (2*l) := by
  rw [binaryStep_eq, Measure.conv_add, Measure.conv_smul_right,
    Measure.conv_smul_right, Measure.conv_dirac_zero, Measure.conv_dirac]
  rw [uniformInterval, Measure.map_smul, translate_restrict_Ioc]
  have hu : Set.Ioc 0 l ∪ Set.Ioc l (l+l) = Set.Ioc 0 (2*l) := by
    rw [Set.Ioc_union_Ioc_eq_Ioc hl.le (by linarith)]
    congr 1; linarith
  have hd : Disjoint (Set.Ioc 0 l) (Set.Ioc l (l+l)) :=
    Set.disjoint_left.mpr (by intro x h₁ h₂; exact (not_lt_of_ge h₁.2) h₂.1)
  rw [smul_smul, smul_smul, ← smul_add, ← Measure.restrict_union hd measurableSet_Ioc, hu]
  congr 1
  rw [ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2)]
  norm_num [ENNReal.mul_inv]

instance incrementLaw_probability (n : ℕ) : IsProbabilityMeasure (incrementLaw n) := by
  cases n with
  | zero => exact uniformInterval_probability zero_lt_one
  | succ n => exact binaryStep_probability _

instance axisLaw_probability : IsProbabilityMeasure axisLaw := by
  unfold axisLaw
  infer_instance

lemma measurable_shift (n : ℕ) : Measurable (shift n) := by
  exact Finset.measurable_sum _ (fun i _ => measurable_pi_apply i)

lemma shift_zero (ω : ℕ → ℝ) : shift 0 ω = ω 0 := by simp [shift]
lemma shift_succ (n : ℕ) (ω : ℕ → ℝ) :
    shift (n+1) ω = shift n ω + ω (n+1) := by simp [shift, Finset.sum_range_succ]

lemma map_shift (n : ℕ) : axisLaw.map (shift n) = uniformInterval (2^n) := by
  induction n with
  | zero =>
      simp only [pow_zero]
      rw [show shift 0 = (fun ω => ω 0) by funext ω; exact shift_zero ω]
      exact Measure.infinitePi_map_eval incrementLaw 0
  | succ n ih =>
      have hind := ProbabilityTheory.iIndepFun_infinitePi
        (P := incrementLaw) (X := fun _ => id) (fun _ => measurable_id)
      have hi := hind.indepFun_finsetSum_of_notMem
        (fun i => measurable_pi_apply i) (s := Finset.range (n+1)) (i := n+1) (by simp)
      have he : (∑ j ∈ Finset.range (n+1), (fun ω : ℕ → ℝ => id (ω j))) = shift n := by
        funext ω
        simp [shift]
      rw [he] at hi
      have hm := hi.map_add_eq_map_conv_map₀ (measurable_shift n).aemeasurable
        (measurable_pi_apply (n+1)).aemeasurable
      change axisLaw.map (fun ω => shift n ω + ω (n+1)) = _ at hm
      simp only [← shift_succ] at hm
      change axisLaw.map (shift (n+1)) = (axisLaw.map (shift n)).conv ((Measure.infinitePi incrementLaw).map (fun f => f (n+1))) at hm
      rw [ih, Measure.infinitePi_map_eval incrementLaw (n+1)] at hm
      rw [incrementLaw, uniform_double (by positivity)] at hm
      simpa only [pow_succ, mul_comm (2^n) (2:ℝ)] using hm

lemma integral_uniform_shares {l : ℝ} (hl : 0 < l) (x y : ℝ) :
    (∫ s, shares l s x y ∂uniformInterval l) = max 0 (1-|x-y|/l) := by
  rw [uniformInterval, integral_smul_measure, shares_integral hl]
  simp only [ENNReal.toReal_inv, ENNReal.toReal_ofReal hl.le, smul_eq_mul]
  rw [mul_max_of_nonneg _ _ (inv_nonneg.mpr hl.le), mul_zero]
  congr 1
  field_simp

lemma integral_shift_shares (n : ℕ) (x y : ℝ) :
    (∫ ω, shares (2^n) (shift n ω) x y ∂axisLaw) =
      max 0 (1-|x-y|/(2^n)) := by
  rw [← integral_map (measurable_shift n).aemeasurable
    (measurable_shares (2^n) x y).aestronglyMeasurable, map_shift]
  exact integral_uniform_shares (by positivity) x y

lemma integral_shares_nat_periods {l : ℝ} (hl : 0 < l) (k : ℕ) (x y : ℝ) :
    (∫ s in Set.Ioc 0 (k*l), shares l s x y) = (k:ℝ)*max 0 (l-|x-y|) := by
  have hh := (shares_period hl x y).intervalIntegral_add_zsmul_eq (k:ℤ) 0
    (fun a b => ⟨shares_integrableOn l x y a b, shares_integrableOn l x y b a⟩)
  simp only [zero_add, zsmul_eq_mul, Int.cast_natCast,
    intervalIntegral.integral_of_le (by positivity : (0:ℝ) ≤ k*l),
    intervalIntegral.integral_of_le hl.le, shares_integral hl] at hh
  exact hh

/-- The fine-scale shift is the original unit shift. Its sharing law is still
    the correct uniform-modulo-side law, not a fresh independent grid. -/
lemma integral_fine_shares (n : ℕ) (x y : ℝ) :
    (∫ ω, shares ((2:ℝ)^(- (n:ℤ))) (shift 0 ω) x y ∂axisLaw) =
      max 0 (1-|x-y|/((2:ℝ)^(- (n:ℤ)))) := by
  rw [← integral_map (measurable_shift 0).aemeasurable
    (measurable_shares _ x y).aestronglyMeasurable, map_shift]
  simp only [pow_zero, uniformInterval, ENNReal.ofReal_one, inv_one, one_smul]
  have hl : 0 < (2:ℝ)^(-(n:ℤ)) := by positivity
  have he : ((2^n:ℕ):ℝ)*(2:ℝ)^(-(n:ℤ)) = 1 := by
    simp [zpow_neg, zpow_natCast]
  have hh := integral_shares_nat_periods hl (2^n) x y
  rw [he] at hh
  rw [hh, mul_max_of_nonneg _ _ (by positivity : (0:ℝ) ≤ ((2^n:ℕ):ℝ)), mul_zero]
  congr 1
  simp only [Nat.cast_pow, Nat.cast_ofNat, zpow_neg, zpow_natCast, div_inv_eq_mul]
  field_simp

lemma binaryStep_ae (l : ℝ) : ∀ᵐ x ∂binaryStep l, x = 0 ∨ x = l := by
  rw [binaryStep_eq]
  simp only [ae_add_measure_iff]
  constructor
  · apply Measure.ae_smul_measure
    exact (ae_dirac_iff (by measurability)).mpr (Or.inl rfl)
  · apply Measure.ae_smul_measure
    exact (ae_dirac_iff (by measurability)).mpr (Or.inr rfl)

lemma axis_increment_ae (n : ℕ) :
    ∀ᵐ ω ∂axisLaw, ω (n+1) = 0 ∨ ω (n+1) = (2:ℝ)^n := by
  have hh : ∀ᵐ x ∂incrementLaw (n+1), x = 0 ∨ x = (2:ℝ)^n := binaryStep_ae _
  apply ae_of_ae_map (μ := axisLaw) (f := fun ω : ℕ → ℝ => ω (n+1))
    (p := fun x : ℝ => x = 0 ∨ x = (2:ℝ)^n) (measurable_pi_apply (n+1)).aemeasurable
  simpa only [axisLaw, Measure.infinitePi_map_eval] using hh

lemma bins_nested_ae (n : ℕ) (x y : ℝ) :
    ∀ᵐ ω ∂axisLaw, bin (2^n) (shift n ω) x = bin (2^n) (shift n ω) y →
      bin (2^(n+1)) (shift (n+1) ω) x = bin (2^(n+1)) (shift (n+1) ω) y := by
  filter_upwards [axis_increment_ae n] with ω hω
  intro h
  rcases hω with hω | hω
  · simpa only [shift_succ, hω, pow_succ, mul_comm (2^n) (2:ℝ),
      Int.cast_zero, zero_mul, add_zero] using nested_bins (by positivity) (shift n ω) x y 0 h
  · simpa only [shift_succ, hω, pow_succ, mul_comm (2^n) (2:ℝ),
      Int.cast_one, one_mul] using nested_bins (by positivity) (shift n ω) x y 1 h

instance squareLaw_probability : IsProbabilityMeasure squareLaw := by
  unfold squareLaw
  infer_instance

lemma measurableSet_shareAt (m : ℤ) (x y : ℝ × ℝ) :
    MeasurableSet {ω | shareAt m ω x y} := by
  unfold shareAt bin shiftZ
  apply MeasurableSet.inter
  · exact measurableSet_eq_fun
      (((measurable_const.sub ((measurable_shift _).comp measurable_fst)).div_const _).floor)
      (((measurable_const.sub ((measurable_shift _).comp measurable_fst)).div_const _).floor)
  · exact measurableSet_eq_fun
      (((measurable_const.sub ((measurable_shift _).comp measurable_snd)).div_const _).floor)
      (((measurable_const.sub ((measurable_shift _).comp measurable_snd)).div_const _).floor)

lemma integral_shiftZ_shares (m : ℤ) (x y : ℝ) :
    (∫ ω, shares ((2:ℝ)^m) (shiftZ m ω) x y ∂axisLaw) =
      max 0 (1-|x-y|/((2:ℝ)^m)) := by
  cases m with
  | ofNat n =>
      change (∫ ω, shares ((2:ℝ)^(n:ℤ)) (shift n ω) x y ∂axisLaw) =
        max 0 (1-|x-y|/((2:ℝ)^(n:ℤ)))
      simpa only [zpow_natCast] using integral_shift_shares n x y
  | negSucc n =>
      simpa [shiftZ, Int.negSucc_eq, Int.toNat_of_nonpos] using
        integral_fine_shares (n+1) x y

lemma sharing_probability (m : ℤ) (x y : ℝ × ℝ) :
    squareLaw.real {ω | shareAt m ω x y} =
      max 0 (1-|x.1-y.1|/((2:ℝ)^m)) * max 0 (1-|x.2-y.2|/((2:ℝ)^m)) := by
  rw [← integral_indicator_one (measurableSet_shareAt m x y)]
  have he : (fun ω : GridSample => Set.indicator {ω | shareAt m ω x y} 1 ω) =
      (fun ω => shares ((2:ℝ)^m) (shiftZ m ω.1) x.1 y.1 *
        shares ((2:ℝ)^m) (shiftZ m ω.2) x.2 y.2) := by
    funext ω
    simp only [Set.indicator, Set.mem_ofPred_eq, shareAt, shares, Pi.one_apply]
    by_cases h₁ : bin ((2:ℝ)^m) (shiftZ m ω.1) x.1 = bin ((2:ℝ)^m) (shiftZ m ω.1) y.1 <;>
      by_cases h₂ : bin ((2:ℝ)^m) (shiftZ m ω.2) x.2 = bin ((2:ℝ)^m) (shiftZ m ω.2) y.2 <;>
      simp [h₁,h₂]
  rw [he, squareLaw, integral_prod_mul (fun ω : ℕ → ℝ => shares ((2:ℝ)^m) (shiftZ m ω) x.1 y.1)
    (fun ω : ℕ → ℝ => shares ((2:ℝ)^m) (shiftZ m ω) x.2 y.2),
    integral_shiftZ_shares, integral_shiftZ_shares]

lemma max_sharing_bound {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    1 - max 0 (1-a) * max 0 (1-b) ≤ a+b := by
  by_cases ha' : a ≤ 1
  · by_cases hb' : b ≤ 1
    · rw [max_eq_right (by linarith), max_eq_right (by linarith)]
      nlinarith [mul_nonneg ha hb]
    · rw [max_eq_left (show 1-b ≤ 0 by linarith)]
      nlinarith
  · rw [max_eq_left (by linarith)]
    nlinarith

lemma separation_probability_le (m : ℤ) (x y : ℝ × ℝ) :
    squareLaw.real {ω | ¬ shareAt m ω x y} ≤
      (|x.1-y.1|+|x.2-y.2|)/((2:ℝ)^m) := by
  change squareLaw.real {ω | shareAt m ω x y}ᶜ ≤ _
  rw [measureReal_compl (measurableSet_shareAt m x y), probReal_univ,
    sharing_probability, add_div]
  exact max_sharing_bound (by positivity) (by positivity)

lemma share_eventually_exists (x y : ℝ × ℝ) :
    ∀ᵐ ω ∂squareLaw, ∃ n : ℕ, shareAt n ω x y := by
  rw [ae_iff]
  apply (measureReal_eq_zero_iff).mp
  apply le_antisymm _ (measureReal_nonneg)
  have hb (n : ℕ) : squareLaw.real {ω | ¬ ∃ n : ℕ, shareAt n ω x y} ≤
      (|x.1-y.1|+|x.2-y.2|)/((2:ℝ)^n) := by
    refine (measureReal_mono (s₂ := {ω | ¬ shareAt (n:ℤ) ω x y})
      (by intro ω h hn; exact h ⟨n, hn⟩)).trans ?_
    simpa only [zpow_natCast] using separation_probability_le (n:ℤ) x y
  exact le_of_tendsto_of_tendsto' tendsto_const_nhds
    (tendsto_const_nhds.div_atTop (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1:ℝ)<2))) hb

lemma axis_nestedZ_ae (m : ℤ) (x y : ℝ) :
    ∀ᵐ ω ∂axisLaw, bin ((2:ℝ)^m) (shiftZ m ω) x = bin ((2:ℝ)^m) (shiftZ m ω) y →
      bin ((2:ℝ)^(m+1)) (shiftZ (m+1) ω) x = bin ((2:ℝ)^(m+1)) (shiftZ (m+1) ω) y := by
  by_cases hm : 0 ≤ m
  · obtain ⟨n,rfl⟩ := Int.eq_ofNat_of_zero_le hm
    rw [show (n:ℤ)+1 = ((n+1:ℕ):ℤ) by omega]
    simpa only [shiftZ, Int.toNat_natCast, zpow_natCast] using bins_nested_ae n x y
  · have hm' : m+1 ≤ 0 := by omega
    filter_upwards with ω
    intro h
    simp only [shiftZ, Int.toNat_of_nonpos (by omega : m ≤ 0)] at h
    have hh := nested_bins (by positivity : 0 < (2:ℝ)^m) (shift 0 ω) x y 0
    simpa only [shiftZ, Int.toNat_of_nonpos (by omega : m ≤ 0),
      Int.toNat_of_nonpos hm', zpow_add₀ (by norm_num : (2:ℝ)≠0), zpow_one,
      mul_comm ((2:ℝ)^m) (2:ℝ), Int.cast_zero, zero_mul, add_zero] using hh h

lemma shareAt_nested_ae (m : ℤ) (x y : ℝ × ℝ) :
    ∀ᵐ ω ∂squareLaw, shareAt m ω x y → shareAt (m+1) ω x y := by
  filter_upwards [Measure.quasiMeasurePreserving_fst.ae (axis_nestedZ_ae m x.1 y.1),
    Measure.quasiMeasurePreserving_snd.ae (axis_nestedZ_ae m x.2 y.2)] with ω hx hy
  exact fun h => ⟨hx h.1, hy h.2⟩

lemma shareAt_trans (m : ℤ) (ω : GridSample) (x y z : ℝ × ℝ)
    (hxy : shareAt m ω x y) (hyz : shareAt m ω y z) : shareAt m ω x z :=
  ⟨hxy.1.trans hyz.1, hxy.2.trans hyz.2⟩

lemma shareAt_bddBelow (ω : GridSample) {x y : ℝ × ℝ} (hxy : x ≠ y) :
    BddBelow {m : ℤ | shareAt m ω x y} := by
  have bound {a b : ℝ} (h : a ≠ b) (f : ℤ → ℝ) :
      BddBelow {m : ℤ | bin ((2:ℝ)^m) (f m) a = bin ((2:ℝ)^m) (f m) b} := by
    obtain ⟨k,hk⟩ := exists_mem_Ico_zpow (abs_pos.mpr (sub_ne_zero.mpr h)) (by norm_num : (1:ℝ)<2)
    refine ⟨k, fun m hm => ?_⟩
    have hh := shares_gap (by positivity : 0 < (2:ℝ)^m) hm
    exact (zpow_le_zpow_iff_right₀ (by norm_num : (1:ℝ)<2)).mp (hk.1.trans hh.le)
  by_cases h₁ : x.1 = y.1
  · have h₂ : x.2 ≠ y.2 := fun h₂ => hxy (Prod.ext h₁ h₂)
    exact (bound h₂ (fun m => shiftZ m ω.2)).mono (fun _ h => h.2)
  · exact (bound h₁ (fun m => shiftZ m ω.1)).mono (fun _ h => h.1)

lemma minScale_mem {ω : GridSample} {x y : ℝ × ℝ} (hxy : x ≠ y)
    (he : ∃ m, shareAt m ω x y) : shareAt (minScale ω x y) ω x y :=
  Int.csInf_mem he (shareAt_bddBelow ω hxy)

lemma minScale_le {ω : GridSample} {x y : ℝ × ℝ} (hxy : x ≠ y)
    {m : ℤ} (hm : shareAt m ω x y) : minScale ω x y ≤ m :=
  csInf_le (shareAt_bddBelow ω hxy) hm

lemma shareAt_iff_minScale_le {ω : GridSample} {x y : ℝ × ℝ} (hxy : x ≠ y)
    (he : ∃ m, shareAt m ω x y)
    (hn : ∀ m, shareAt m ω x y → shareAt (m+1) ω x y) (m : ℤ) :
    shareAt m ω x y ↔ minScale ω x y ≤ m := by
  constructor
  · exact minScale_le hxy
  · intro hm
    have hmono : Monotone (fun k => shareAt k ω x y) := monotone_int_of_le_succ hn
    exact hmono hm (minScale_mem hxy he)

lemma minScale_eq_iff {ω : GridSample} {x y : ℝ × ℝ} (hxy : x ≠ y) (m : ℤ) :
    minScale ω x y = m ↔
      (shareAt m ω x y ∧ ∀ k : ℤ, k < m → ¬ shareAt k ω x y) ∨
      (m = 0 ∧ ¬ ∃ k : ℤ, shareAt k ω x y) := by
  by_cases he : ∃ k, shareAt k ω x y
  · have hs := minScale_mem hxy he
    constructor
    · intro h
      left
      rw [h] at hs
      refine ⟨hs, fun k hk hks => ?_⟩
      have hh := minScale_le hxy hks
      omega
    · rintro (⟨hm,hmin⟩ | ⟨_,hn⟩)
      · apply le_antisymm (minScale_le hxy hm)
        by_contra h
        exact hmin _ (by omega) hs
      · exact False.elim (hn he)
  · have hz : minScale ω x y = 0 := by
      unfold minScale
      rw [show {m | shareAt m ω x y} = ∅ by ext m; simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false]; exact iff_false_intro (fun h => he ⟨m,h⟩)]
      exact Int.csInf_empty
    simp only [hz]
    constructor
    · intro hm
      exact Or.inr ⟨hm.symm,he⟩
    · rintro (⟨hm,_⟩ | ⟨rfl,_⟩)
      · exact False.elim (he ⟨m,hm⟩)
      · rfl

lemma measurable_minScale {x y : ℝ × ℝ} (hxy : x ≠ y) :
    Measurable (fun ω => minScale ω x y) := by
  apply measurable_to_countable'
  intro m
  change MeasurableSet {ω | minScale ω x y = m}
  have he : {ω : GridSample | minScale ω x y = m} =
      ({ω | shareAt m ω x y} ∩ {ω | ∀ k < m, ¬shareAt k ω x y}) ∪
      ({ω | m = 0} ∩ {ω | ¬∃ k, shareAt k ω x y}) := by
    ext ω
    exact minScale_eq_iff hxy m
  rw [he]
  apply MeasurableSet.union
  · apply (measurableSet_shareAt m x y).inter
    have he : {ω : GridSample | ∀ k < m, ¬shareAt k ω x y} =
        ⋂ k : ℤ, ⋂ (_ : k < m), {ω : GridSample | shareAt k ω x y}ᶜ := by
      ext ω
      simp
    rw [he]
    exact MeasurableSet.iInter fun k =>
      MeasurableSet.iInter fun (_ : k < m) => (measurableSet_shareAt k x y).compl
  · apply (MeasurableSet.const (m = 0)).inter
    have he : {ω : GridSample | ¬∃ k, shareAt k ω x y} =
        (⋃ k : ℤ, {ω : GridSample | shareAt k ω x y})ᶜ := by
      ext ω
      simp
    rw [he]
    exact (MeasurableSet.iUnion fun k => measurableSet_shareAt k x y).compl

lemma measurable_gridDepth {x y : ℝ × ℝ} (hxy : x ≠ y) :
    Measurable (fun ω => gridDepth ω x y) := by
  exact (((measurable_of_countable (fun n : ℤ => (n:ℝ))).comp (measurable_minScale hxy)).neg).mul_const _

lemma gridDepth_ultra_ae {x y z : ℝ × ℝ} (hxy : x ≠ y) (hyz : y ≠ z) (hxz : x ≠ z) :
    ∀ᵐ ω ∂squareLaw, min (gridDepth ω x y) (gridDepth ω y z) ≤ gridDepth ω x z := by
  have hn : ∀ᵐ ω ∂squareLaw, ∀ m : ℤ,
      (shareAt m ω x y → shareAt (m+1) ω x y) ∧
      (shareAt m ω y z → shareAt (m+1) ω y z) := by
    rw [ae_all_iff]
    intro m
    filter_upwards [shareAt_nested_ae m x y, shareAt_nested_ae m y z] with ω h₁ h₂ using ⟨h₁,h₂⟩
  filter_upwards [share_eventually_exists x y, share_eventually_exists y z, hn] with ω h₁ h₂ hn
  have e₁ : ∃ m : ℤ, shareAt m ω x y := by obtain ⟨n,hn⟩ := h₁; exact ⟨n,hn⟩
  have e₂ : ∃ m : ℤ, shareAt m ω y z := by obtain ⟨n,hn⟩ := h₂; exact ⟨n,hn⟩
  have hm : minScale ω x z ≤ max (minScale ω x y) (minScale ω y z) := by
    apply minScale_le hxz
    apply shareAt_trans _ ω x y z
    · exact (shareAt_iff_minScale_le hxy e₁ (fun m => (hn m).1) _).mpr (le_max_left _ _)
    · exact (shareAt_iff_minScale_le hyz e₂ (fun m => (hn m).2) _).mpr (le_max_right _ _)
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  unfold gridDepth
  have hm' : (minScale ω x z : ℝ) ≤ max (minScale ω x y : ℝ) (minScale ω y z : ℝ) := by exact_mod_cast hm
  by_cases hl : (minScale ω x y : ℝ) ≤ minScale ω y z
  · rw [max_eq_right hl] at hm'
    apply (min_le_right _ _).trans
    nlinarith
  · rw [max_eq_left (le_of_not_ge hl)] at hm'
    apply (min_le_left _ _).trans
    nlinarith

/-- Euclidean norm can subsequently be used for `R`: only its elementary
    comparison with the two coordinate gaps is needed for the tail bound. -/
lemma error_upper_ae {x y : ℝ × ℝ} (hxy : x ≠ y) {R : ℝ} (hR : 0 < R)
    (hgap : R ≤ |x.1-y.1|+|x.2-y.2|) :
    ∀ᵐ ω ∂squareLaw, gridDepth ω x y + Real.log R ≤ Real.log 2 := by
  filter_upwards [share_eventually_exists x y] with ω he
  obtain ⟨n,hn⟩ := he
  have hs := minScale_mem hxy ⟨n,hn⟩
  have h₁ := shares_gap (by positivity : 0 < (2:ℝ)^(minScale ω x y)) hs.1
  have h₂ := shares_gap (by positivity : 0 < (2:ℝ)^(minScale ω x y)) hs.2
  have hr : R ≤ 2*(2:ℝ)^(minScale ω x y) := by linarith
  have hh := Real.log_le_log hR hr
  rw [Real.log_mul (by norm_num : (2:ℝ)≠0) (by positivity), Real.log_zpow] at hh
  unfold gridDepth
  linarith

lemma error_lower_tail {x y : ℝ × ℝ} (hxy : x ≠ y) {R : ℝ} (hR : 0 < R)
    (hgap : |x.1-y.1|+|x.2-y.2| ≤ 2*R) (u : ℝ) :
    squareLaw.real {ω | gridDepth ω x y + Real.log R < -u} ≤ 4*Real.exp (-u) := by
  obtain ⟨m,hm⟩ := exists_mem_Ico_zpow (mul_pos hR (Real.exp_pos u))
    (by norm_num : (1:ℝ)<2)
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hm₁ : (m:ℝ)*Real.log 2 ≤ Real.log R + u := by
    have hh := Real.log_le_log (by positivity : 0 < (2:ℝ)^m) hm.1
    rw [Real.log_zpow, Real.log_mul hR.ne' (Real.exp_ne_zero _), Real.log_exp] at hh
    exact hh
  have hsub : {ω | gridDepth ω x y + Real.log R < -u} ⊆
      {ω | ¬shareAt m ω x y} := by
    intro ω hω hs
    have hk : (minScale ω x y : ℝ) ≤ (m:ℝ) := by exact_mod_cast minScale_le hxy hs
    have := mul_le_mul_of_nonneg_right hk hl.le
    change gridDepth ω x y + Real.log R < -u at hω
    unfold gridDepth at hω
    linarith
  refine (measureReal_mono hsub).trans ((separation_probability_le m x y).trans ?_)
  have hpow : 0 < (2:ℝ)^m := by positivity
  have hm₂ : R*Real.exp u < 2*(2:ℝ)^m := by
    simpa only [zpow_add₀ (by norm_num : (2:ℝ)≠0), zpow_one, mul_comm] using hm.2
  apply (div_le_iff₀ hpow).mpr
  have hex : Real.exp u * Real.exp (-u) = 1 := by rw [← Real.exp_add]; simp
  have hh := mul_le_mul_of_nonneg_right hm₂.le (Real.exp_nonneg (-u))
  nlinarith

lemma error_abs_tail {x y : ℝ × ℝ} (hxy : x ≠ y) {R : ℝ} (hR : 0 < R)
    (hgap₁ : R ≤ |x.1-y.1|+|x.2-y.2|)
    (hgap₂ : |x.1-y.1|+|x.2-y.2| ≤ 2*R) {u : ℝ} (_hu : 0 ≤ u) :
    squareLaw.real {ω | u < |gridDepth ω x y + Real.log R|} ≤ 4*Real.exp (-u) := by
  by_cases hsmall : u ≤ Real.log 2
  · have hp : squareLaw.real {ω | u < |gridDepth ω x y + Real.log R|} ≤ 1 :=
      measureReal_le_one
    have hex : (1:ℝ)/2 ≤ Real.exp (-u) := by
      have := Real.exp_le_exp.mpr (neg_le_neg hsmall)
      rw [Real.exp_neg, Real.exp_log (by norm_num : (0:ℝ)<2)] at this
      simpa only [one_div] using this
    linarith
  · have hle : squareLaw.real {ω | u < |gridDepth ω x y + Real.log R|} ≤
        squareLaw.real {ω | gridDepth ω x y + Real.log R < -u} := by
      apply ENNReal.toReal_mono (measure_ne_top _ _)
      apply measure_mono_ae
      filter_upwards [error_upper_ae hxy hR hgap₁] with ω hω
      intro hh
      rcases lt_abs.mp hh with hh | hh
      · exact False.elim (hsmall (hh.le.trans hω))
      · show gridDepth ω x y + Real.log R < -u
        linarith
    exact hle.trans (error_lower_tail hxy hR hgap₂ u)

lemma error_abs_lintegral_le {x y : ℝ × ℝ} (hxy : x ≠ y) {R : ℝ} (hR : 0 < R)
    (hgap₁ : R ≤ |x.1-y.1|+|x.2-y.2|)
    (hgap₂ : |x.1-y.1|+|x.2-y.2| ≤ 2*R) :
    (∫⁻ ω, ENNReal.ofReal |gridDepth ω x y + Real.log R| ∂squareLaw) ≤ ENNReal.ofReal 4 := by
  rw [lintegral_eq_lintegral_meas_lt squareLaw
    (by filter_upwards with ω; exact abs_nonneg _)
    (((measurable_gridDepth hxy).add_const _).abs.aemeasurable)]
  have he : IntegrableOn (fun u : ℝ => 4 * Real.exp (-u)) (Set.Ioi 0) volume := by
    change Integrable (fun u : ℝ => 4 * Real.exp (-u)) (volume.restrict (Set.Ioi 0))
    simpa only [neg_one_mul] using (integrableOn_exp_mul_Ioi (by norm_num : (-1:ℝ)<0) 0).const_mul 4
  calc
    _ ≤ ∫⁻ u : ℝ in Set.Ioi 0, ENNReal.ofReal (4*Real.exp (-u)) := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
      rw [← ENNReal.ofReal_toReal (measure_ne_top squareLaw _)]
      exact ENNReal.ofReal_le_ofReal (error_abs_tail hxy hR hgap₁ hgap₂ hu.le)
    _ = ENNReal.ofReal 4 := by
      rw [← ofReal_integral_eq_lintegral_ofReal he (by filter_upwards with u; positivity)]
      congr 1
      rw [integral_const_mul]
      have hi := integral_exp_mul_Ioi (by norm_num : (-1:ℝ)<0) (0:ℝ)
      simp only [neg_one_mul, mul_zero, Real.exp_zero, neg_div_neg_eq, div_one] at hi
      rw [hi]
      norm_num

lemma error_integrable {x y : ℝ × ℝ} (hxy : x ≠ y) {R : ℝ} (hR : 0 < R)
    (hgap₁ : R ≤ |x.1-y.1|+|x.2-y.2|)
    (hgap₂ : |x.1-y.1|+|x.2-y.2| ≤ 2*R) :
    Integrable (fun ω => gridDepth ω x y + Real.log R) squareLaw := by
  have hm : AEStronglyMeasurable (fun ω => gridDepth ω x y + Real.log R) squareLaw :=
    ((measurable_gridDepth hxy).add_const (Real.log R)).aestronglyMeasurable
  apply (integrable_norm_iff hm).mp
  refine ⟨hm.norm, ?_⟩
  apply (hasFiniteIntegral_iff_ofReal (by filter_upwards with ω; exact norm_nonneg _)).mpr
  simpa only [Real.norm_eq_abs] using
    (error_abs_lintegral_le hxy hR hgap₁ hgap₂).trans_lt ENNReal.ofReal_lt_top

lemma mean_abs_error_le {x y : ℝ × ℝ} (hxy : x ≠ y) {R : ℝ} (hR : 0 < R)
    (hgap₁ : R ≤ |x.1-y.1|+|x.2-y.2|)
    (hgap₂ : |x.1-y.1|+|x.2-y.2| ≤ 2*R) :
    (∫ ω, |gridDepth ω x y + Real.log R| ∂squareLaw) ≤ 4 := by
  have hi := (error_integrable hxy hR hgap₁ hgap₂).abs
  have hh := error_abs_lintegral_le hxy hR hgap₁ hgap₂
  rw [← ofReal_integral_eq_lintegral_ofReal hi (by filter_upwards with ω; exact abs_nonneg _)] at hh
  have hh' := ENNReal.toReal_mono (by simp : ENNReal.ofReal (4:ℝ) ≠ ⊤) hh
  simpa only [ENNReal.toReal_ofReal (integral_nonneg fun ω => abs_nonneg _),
    ENNReal.toReal_ofReal (by norm_num : (0:ℝ)≤4)] using hh'

lemma minScale_cdf {x y : ℝ × ℝ} (hxy : x ≠ y) (m : ℤ) :
    squareLaw.real {ω | minScale ω x y ≤ m} =
      max 0 (1-|x.1-y.1|/((2:ℝ)^m)) * max 0 (1-|x.2-y.2|/((2:ℝ)^m)) := by
  have hn : ∀ᵐ ω ∂squareLaw, ∀ k : ℤ, shareAt k ω x y → shareAt (k+1) ω x y := by
    rw [ae_all_iff]
    exact fun k => shareAt_nested_ae k x y
  have he : {ω | minScale ω x y ≤ m} =ᵐ[squareLaw] {ω | shareAt m ω x y} := by
    filter_upwards [share_eventually_exists x y, hn] with ω he hn
    apply propext
    obtain ⟨n,hn'⟩ := he
    exact (shareAt_iff_minScale_le hxy ⟨n,hn'⟩ hn m).symm
  rw [measureReal_def, measure_congr he]
  exact sharing_probability m x y

lemma minScale_law_same_gaps {x y x' y' : ℝ × ℝ} (hxy : x ≠ y) (hxy' : x' ≠ y')
    (h₁ : |x.1-y.1| = |x'.1-y'.1|) (h₂ : |x.2-y.2| = |x'.2-y'.2|) :
    Measure.map (fun ω => minScale ω x y) squareLaw =
      Measure.map (fun ω => minScale ω x' y') squareLaw := by
  apply Measure.ext_of_Iic
  intro m
  rw [Measure.map_apply (measurable_minScale hxy) measurableSet_Iic,
    Measure.map_apply (measurable_minScale hxy') measurableSet_Iic]
  apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).mp
  change squareLaw.real {ω | minScale ω x y ≤ m} = squareLaw.real {ω | minScale ω x' y' ≤ m}
  rw [minScale_cdf hxy, minScale_cdf hxy', h₁, h₂]

lemma mean_depth_same_gaps {x y x' y' : ℝ × ℝ} (hxy : x ≠ y) (hxy' : x' ≠ y')
    (h₁ : |x.1-y.1| = |x'.1-y'.1|) (h₂ : |x.2-y.2| = |x'.2-y'.2|) :
    (∫ ω, gridDepth ω x y ∂squareLaw) = ∫ ω, gridDepth ω x' y' ∂squareLaw := by
  have hf : Measurable (fun n : ℤ => -(n:ℝ)*Real.log 2) := measurable_of_countable _
  unfold gridDepth
  rw [← integral_map (measurable_minScale hxy).aemeasurable hf.aestronglyMeasurable,
      ← integral_map (measurable_minScale hxy').aemeasurable hf.aestronglyMeasurable,
      minScale_law_same_gaps hxy hxy' h₁ h₂]

lemma minScale_law_double {x y : ℝ × ℝ} (hxy : x ≠ y) :
    Measure.map (fun ω => minScale ω (2*x.1,2*x.2) (2*y.1,2*y.2)) squareLaw =
      Measure.map (fun ω => minScale ω x y + 1) squareLaw := by
  have hd : (2*x.1,2*x.2) ≠ (2*y.1,2*y.2) := by
    intro h
    apply hxy
    have h₁ := congrArg Prod.fst h
    have h₂ := congrArg Prod.snd h
    apply Prod.ext <;> dsimp at h₁ h₂ ⊢ <;> linarith
  apply Measure.ext_of_Iic
  intro m
  rw [Measure.map_apply (measurable_minScale hd) measurableSet_Iic,
    Measure.map_apply ((measurable_minScale hxy).add_const 1) measurableSet_Iic]
  apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).mp
  change squareLaw.real {ω | minScale ω (2*x.1,2*x.2) (2*y.1,2*y.2) ≤ m} =
    squareLaw.real {ω | minScale ω x y + 1 ≤ m}
  rw [show {ω | minScale ω x y + 1 ≤ m} = {ω | minScale ω x y ≤ m-1} by ext ω; simp only [Set.mem_ofPred_eq]; omega,
    minScale_cdf hd, minScale_cdf hxy]
  have hpow : (2:ℝ)^(m-1) = (2:ℝ)^m / 2 := by rw [zpow_sub₀ (by norm_num), zpow_one]
  have hq (a b : ℝ) : |2*a-2*b| / (2:ℝ)^m = |a-b| / ((2:ℝ)^m/2) := by
    rw [← mul_sub, abs_mul]
    norm_num
    ring
  rw [hpow, hq x.1 y.1, hq x.2 y.2]

lemma gridDepth_integrable {x y : ℝ × ℝ} (hxy : x ≠ y) :
    Integrable (fun ω => gridDepth ω x y) squareLaw := by
  let R := |x.1-y.1|+|x.2-y.2|
  have hR : 0 < R := by
    by_cases h₁ : x.1 = y.1
    · have h₂ : x.2 ≠ y.2 := fun h₂ => hxy (Prod.ext h₁ h₂)
      exact add_pos_of_nonneg_of_pos (abs_nonneg _) (abs_pos.mpr (sub_ne_zero.mpr h₂))
    · exact add_pos_of_pos_of_nonneg (abs_pos.mpr (sub_ne_zero.mpr h₁)) (abs_nonneg _)
  have hi := error_integrable hxy hR (le_refl R) (by linarith : R ≤ 2*R)
  have hh := hi.sub (integrable_const (Real.log R))
  change Integrable (fun ω => (gridDepth ω x y + Real.log R) - Real.log R) squareLaw at hh
  simpa only [add_sub_cancel_right] using hh

lemma mean_depth_double {x y : ℝ × ℝ} (hxy : x ≠ y) :
    (∫ ω, gridDepth ω (2*x.1,2*x.2) (2*y.1,2*y.2) ∂squareLaw) =
      (∫ ω, gridDepth ω x y ∂squareLaw) - Real.log 2 := by
  have hd : (2*x.1,2*x.2) ≠ (2*y.1,2*y.2) := by
    intro h
    apply hxy
    have h₁ := congrArg Prod.fst h
    have h₂ := congrArg Prod.snd h
    apply Prod.ext <;> dsimp at h₁ h₂ ⊢ <;> linarith
  have hid : ProbabilityTheory.IdentDistrib
      (fun ω => minScale ω (2*x.1,2*x.2) (2*y.1,2*y.2))
      (fun ω => minScale ω x y + 1) squareLaw squareLaw :=
    ⟨(measurable_minScale hd).aemeasurable,
      ((measurable_minScale hxy).add_const 1).aemeasurable, minScale_law_double hxy⟩
  have hh := (hid.comp (measurable_of_countable (fun n : ℤ => -(n:ℝ)*Real.log 2))).integral_eq
  change (∫ ω, gridDepth ω (2*x.1,2*x.2) (2*y.1,2*y.2) ∂squareLaw) = _ at hh
  rw [hh]
  calc
    _ = ∫ ω, gridDepth ω x y - Real.log 2 ∂squareLaw := by
      apply integral_congr_ae
      filter_upwards with ω
      simp [gridDepth]
      ring
    _ = _ := by rw [integral_sub (gridDepth_integrable hxy) (integrable_const _)]; simp

/-- Parameter measurability, needed before integrating orientation and phase. -/
lemma measurableSet_shareAt_param {T : Type u1} [MeasurableSpace T]
    {W : T → GridSample} {X Y : T → ℝ × ℝ}
    (hW : Measurable W) (hX : Measurable X) (hY : Measurable Y) (m : ℤ) :
    MeasurableSet {t | shareAt m (W t) (X t) (Y t)} := by
  unfold shareAt bin shiftZ
  apply MeasurableSet.inter
  · exact measurableSet_eq_fun
      ((hX.fst.sub ((measurable_shift _).comp hW.fst)).div_const _).floor
      ((hY.fst.sub ((measurable_shift _).comp hW.fst)).div_const _).floor
  · exact measurableSet_eq_fun
      ((hX.snd.sub ((measurable_shift _).comp hW.snd)).div_const _).floor
      ((hY.snd.sub ((measurable_shift _).comp hW.snd)).div_const _).floor

lemma measurable_minScale_param {T : Type u2} [MeasurableSpace T]
    {W : T → GridSample} {X Y : T → ℝ × ℝ}
    (hW : Measurable W) (hX : Measurable X) (hY : Measurable Y) (hne : ∀ t, X t ≠ Y t) :
    Measurable (fun t => minScale (W t) (X t) (Y t)) := by
  apply measurable_to_countable'
  intro m
  change MeasurableSet {t | minScale (W t) (X t) (Y t) = m}
  have he : {t | minScale (W t) (X t) (Y t) = m} =
      ({t | shareAt m (W t) (X t) (Y t)} ∩
        ⋂ k : ℤ, ⋂ (_ : k < m), {t | shareAt k (W t) (X t) (Y t)}ᶜ) ∪
      ({t | m = 0} ∩ (⋃ k : ℤ, {t | shareAt k (W t) (X t) (Y t)})ᶜ) := by
    ext t
    simp only [Set.mem_ofPred_eq, Set.mem_union, Set.mem_inter_iff, Set.mem_iInter,
      Set.mem_compl_iff, Set.mem_iUnion]
    exact minScale_eq_iff (hne t) m
  rw [he]
  exact ((measurableSet_shareAt_param hW hX hY m).inter
    (MeasurableSet.iInter fun k => MeasurableSet.iInter fun (_ : k < m) =>
      (measurableSet_shareAt_param hW hX hY k).compl)).union
    ((MeasurableSet.const (m = 0)).inter (MeasurableSet.iUnion fun k =>
      measurableSet_shareAt_param hW hX hY k).compl)

lemma measurable_gridDepth_param {T : Type u3} [MeasurableSpace T]
    {W : T → GridSample} {X Y : T → ℝ × ℝ}
    (hW : Measurable W) (hX : Measurable X) (hY : Measurable Y) (hne : ∀ t, X t ≠ Y t) :
    Measurable (fun t => gridDepth (W t) (X t) (Y t)) := by
  exact (((measurable_of_countable (fun n : ℤ => (n:ℝ))).comp
    (measurable_minScale_param hW hX hY hne)).neg).mul_const _

lemma zero_ne_polarPair (t θ : ℝ) : (0,0) ≠ polarPair t θ := by
  intro h
  have he : Real.exp t ≠ 0 := Real.exp_ne_zero t
  have h₁ : Real.cos θ = 0 := (mul_eq_zero.mp (congrArg Prod.fst h).symm).resolve_left he
  have h₂ : Real.sin θ = 0 := (mul_eq_zero.mp (congrArg Prod.snd h).symm).resolve_left he
  have hh := Real.sin_sq_add_cos_sq θ
  rw [h₁,h₂] at hh
  norm_num at hh

lemma polarPair_gaps (t θ : ℝ) :
    Real.exp t ≤ |(polarPair t θ).1|+|(polarPair t θ).2| ∧
    |(polarPair t θ).1|+|(polarPair t θ).2| ≤ 2*Real.exp t := by
  have hsum : 1 ≤ |Real.cos θ|+|Real.sin θ| := by
    have hsq := Real.sin_sq_add_cos_sq θ
    have hpos := mul_nonneg (abs_nonneg (Real.cos θ)) (abs_nonneg (Real.sin θ))
    have hc := abs_nonneg (Real.cos θ)
    have hs := abs_nonneg (Real.sin θ)
    nlinarith [sq_abs (Real.cos θ), sq_abs (Real.sin θ)]
  have hsum' : |Real.cos θ|+|Real.sin θ| ≤ 2 := by
    linarith [Real.abs_cos_le_one θ, Real.abs_sin_le_one θ]
  simp only [polarPair, abs_mul, abs_of_pos (Real.exp_pos t)]
  constructor
  · nlinarith [mul_le_mul_of_nonneg_left hsum (Real.exp_nonneg t)]
  · nlinarith [mul_le_mul_of_nonneg_left hsum' (Real.exp_nonneg t)]

lemma polarMean_integral (t θ : ℝ) :
    polarMean t θ = ∫ ω, gridDepth ω (0,0) (polarPair t θ) + t ∂squareLaw := by
  rw [integral_add (gridDepth_integrable (zero_ne_polarPair t θ)) (integrable_const _)]
  simp [polarMean]

lemma polarMean_bound (t θ : ℝ) : |polarMean t θ| ≤ 4 := by
  rw [polarMean_integral]
  have hg := polarPair_gaps t θ
  have hh := mean_abs_error_le (zero_ne_polarPair t θ) (Real.exp_pos t)
    (by simpa only [zero_sub, abs_neg] using hg.1)
    (by simpa only [zero_sub, abs_neg] using hg.2)
  rw [Real.log_exp] at hh
  have hb : |∫ ω, gridDepth ω (0,0) (polarPair t θ) + t ∂squareLaw| ≤
      ∫ ω, |gridDepth ω (0,0) (polarPair t θ) + t| ∂squareLaw := by
    simpa only [Real.norm_eq_abs] using (norm_integral_le_integral_norm
      (f := fun ω => gridDepth ω (0,0) (polarPair t θ) + t) (μ := squareLaw))
  exact hb.trans hh

lemma measurable_polarPair : Measurable (fun p : ℝ × ℝ => polarPair p.1 p.2) := by
  exact (measurable_fst.exp.mul measurable_snd.cos).prodMk
    (measurable_fst.exp.mul measurable_snd.sin)

lemma measurable_polarMean : Measurable (fun p : ℝ × ℝ => polarMean p.1 p.2) := by
  have hm : Measurable (fun p : (ℝ × ℝ) × GridSample =>
      gridDepth p.2 (0,0) (polarPair p.1.1 p.1.2)) :=
    measurable_gridDepth_param measurable_snd measurable_const
      (measurable_polarPair.comp measurable_fst) (fun p => zero_ne_polarPair _ _)
  have hi : StronglyMeasurable (fun p : ℝ × ℝ => ∫ ω,
      gridDepth ω (0,0) (polarPair p.1 p.2) ∂squareLaw) :=
    hm.stronglyMeasurable.integral_prod_right
  exact hi.measurable.add measurable_fst

lemma polarPair_double (t θ : ℝ) : polarPair (t+Real.log 2) θ =
    (2*(polarPair t θ).1,2*(polarPair t θ).2) := by
  simp only [polarPair,Real.exp_add,Real.exp_log (by norm_num : (0:ℝ)<2)]
  congr 1 <;> ring

lemma polarMean_period_phase (θ : ℝ) : Function.Periodic (fun t => polarMean t θ) (Real.log 2) := by
  intro t
  have hm := mean_depth_double (zero_ne_polarPair t θ)
  simp only [mul_zero] at hm
  simp only [polarMean,polarPair_double,hm]
  ring

lemma polarMean_period_angle (t : ℝ) : Function.Periodic (polarMean t) (2*Real.pi) := by
  intro θ
  simp only [polarMean,polarPair,Real.cos_periodic θ,Real.sin_periodic θ]

lemma uniformInterval_integral {l : ℝ} (hl : 0 < l) (f : ℝ → ℝ) :
    (∫ x, f x ∂uniformInterval l) = l⁻¹ * ∫ x in (0:ℝ)..l, f x := by
  rw [uniformInterval, integral_smul_measure, ENNReal.toReal_inv,
    ENNReal.toReal_ofReal hl.le, smul_eq_mul, intervalIntegral.integral_of_le hl.le]

lemma uniformInterval_period_shift {l : ℝ} (hl : 0 < l) {f : ℝ → ℝ}
    (hf : Function.Periodic f l) (a : ℝ) :
    (∫ x, f (x+a) ∂uniformInterval l) = ∫ x, f x ∂uniformInterval l := by
  rw [uniformInterval_integral hl, uniformInterval_integral hl,
    intervalIntegral.integral_comp_add_right]
  congr 1
  simpa only [zero_add, add_comm l a] using hf.intervalIntegral_add_eq a 0

lemma uniformInterval_period_sub {l : ℝ} (hl : 0 < l) {f : ℝ → ℝ}
    (hf : Function.Periodic f l) (a : ℝ) :
    (∫ x, f (a-x) ∂uniformInterval l) = ∫ x, f (-x) ∂uniformInterval l := by
  have hp : Function.Periodic (fun x => f (-x)) l := by
    intro x
    simpa only [neg_add, sub_eq_add_neg] using hf.sub_eq (-x)
  have hh := uniformInterval_period_shift hl hp (-a)
  simpa only [neg_add, neg_neg, sub_eq_add_neg, add_comm] using hh

lemma polar_average_constant (t φ : ℝ) :
    (∫ ξ, ∫ θ, polarMean (t-ξ) (θ+φ)
      ∂uniformInterval (2*Real.pi) ∂uniformInterval (Real.log 2)) = kappa := by
  simp_rw [uniformInterval_period_shift (by positivity : 0 < 2*Real.pi)
    (polarMean_period_angle _) φ]
  have hp : Function.Periodic
      (fun t => ∫ θ, polarMean t θ ∂uniformInterval (2*Real.pi)) (Real.log 2) := by
    intro x
    apply integral_congr_ae
    filter_upwards with θ
    exact polarMean_period_phase θ x
  exact uniformInterval_period_sub (Real.log_pos (by norm_num)) hp t

lemma rotateC_sub (ξ θ : ℝ) (z w : ℂ) :
    rotateC ξ θ (z-w) = rotateC ξ θ z - rotateC ξ θ w := by
  exact mul_sub _ _ _

lemma norm_rotateC (ξ θ : ℝ) (z : ℂ) :
    ‖rotateC ξ θ z‖ = Real.exp (-ξ) * ‖z‖ := by
  simp only [rotateC, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _), Complex.norm_exp_ofReal_mul_I, mul_one]

lemma rotatePair_ne (ξ θ : ℝ) {z w : ℂ} (hne : z ≠ w) :
    rotatePair ξ θ z ≠ rotatePair ξ θ w := by
  intro he
  have h : rotateC ξ θ z = rotateC ξ θ w := Complex.ext
    (congrArg Prod.fst he) (congrArg Prod.snd he)
  have hn := norm_rotateC ξ θ (z-w)
  rw [rotateC_sub, h, sub_self, norm_zero] at hn
  have hz : ‖z-w‖ ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr hne)
  exact (mul_ne_zero (Real.exp_ne_zero _) hz) hn.symm

lemma rotatePair_gaps (ξ θ : ℝ) (z w : ℂ) :
    Real.exp (-ξ)*‖z-w‖ ≤
      |(rotatePair ξ θ z).1-(rotatePair ξ θ w).1| +
      |(rotatePair ξ θ z).2-(rotatePair ξ θ w).2| ∧
    |(rotatePair ξ θ z).1-(rotatePair ξ θ w).1| +
      |(rotatePair ξ θ z).2-(rotatePair ξ θ w).2| ≤ 2*(Real.exp (-ξ)*‖z-w‖) := by
  have hh := Complex.norm_le_abs_re_add_abs_im (rotateC ξ θ (z-w))
  have hr := Complex.abs_re_le_norm (rotateC ξ θ (z-w))
  have hi := Complex.abs_im_le_norm (rotateC ξ θ (z-w))
  rw [norm_rotateC, rotateC_sub] at hh hr hi
  simp only [Complex.sub_re, Complex.sub_im] at hh hr hi
  exact ⟨hh, by dsimp only [rotatePair]; linarith⟩

lemma rotateC_polar (ξ θ : ℝ) {z : ℂ} (hz : z ≠ 0) :
    rotateC ξ θ z = (Real.exp (Real.log ‖z‖-ξ) : ℂ) *
      Complex.exp (((θ+z.arg : ℝ) : ℂ)*Complex.I) := by
  rw [Complex.ofReal_add, add_mul, Complex.exp_add,
    Real.exp_sub, Real.exp_log (norm_pos_iff.mpr hz),
    div_eq_mul_inv, ← Real.exp_neg, Complex.ofReal_mul]
  calc
    _ = (Real.exp (-ξ) : ℂ) * Complex.exp ((θ:ℂ)*Complex.I) *
        ((‖z‖:ℂ) * Complex.exp ((z.arg:ℂ)*Complex.I)) := by
      rw [Complex.norm_mul_exp_arg_mul_I]
      rfl
    _ = _ := by ring

lemma exp_polarPair (t θ : ℝ) :
    ((Real.exp t : ℂ) * Complex.exp ((θ:ℂ)*Complex.I)).re = (polarPair t θ).1 ∧
    ((Real.exp t : ℂ) * Complex.exp ((θ:ℂ)*Complex.I)).im = (polarPair t θ).2 := by
  simp [polarPair, Complex.mul_re, Complex.mul_im, Complex.exp_re, Complex.exp_im]

lemma rotated_mean (ξ θ : ℝ) {z w : ℂ} (hne : z ≠ w) :
    (∫ ω, gridDepth ω (rotatePair ξ θ z) (rotatePair ξ θ w) ∂squareLaw)
      - ξ + Real.log ‖z-w‖ = polarMean (Real.log ‖z-w‖-ξ) (θ+(z-w).arg) := by
  have hp := exp_polarPair (Real.log ‖z-w‖-ξ) (θ+(z-w).arg)
  rw [← rotateC_polar ξ θ (sub_ne_zero.mpr hne), rotateC_sub] at hp
  have hm := mean_depth_same_gaps (rotatePair_ne ξ θ hne)
    (zero_ne_polarPair (Real.log ‖z-w‖-ξ) (θ+(z-w).arg))
    (by dsimp only [rotatePair]; simp only [zero_sub, abs_neg, ← hp.1]; rfl)
    (by dsimp only [rotatePair]; simp only [zero_sub, abs_neg, ← hp.2]; rfl)
  rw [hm, polarMean]
  ring

instance phaseLaw_probability : IsProbabilityMeasure phaseLaw := by
  let := uniformInterval_probability (Real.log_pos (by norm_num : (1:ℝ) < 2))
  let := uniformInterval_probability (by positivity : 0 < 2*Real.pi)
  exact Measure.prod.instIsProbabilityMeasure _ _

instance fullLaw_probability : IsProbabilityMeasure fullLaw := by
  exact Measure.prod.instIsProbabilityMeasure _ _

lemma measurable_rotatePair (z : ℂ) : Measurable (fun p : ℝ × ℝ => rotatePair p.1 p.2 z) := by
  unfold rotatePair rotateC
  fun_prop

lemma measurable_depth {z w : ℂ} (hne : z ≠ w) : Measurable (fun ω => depth ω z w) := by
  unfold depth
  exact (measurable_gridDepth_param measurable_snd
    ((measurable_rotatePair z).comp measurable_fst)
    ((measurable_rotatePair w).comp measurable_fst)
    (fun p => rotatePair_ne _ _ hne)).sub measurable_fst.fst

lemma measurable_error {z w : ℂ} (hne : z ≠ w) : Measurable (fun ω => error ω z w) :=
  (measurable_depth hne).add_const _

lemma error_fixed_phase {z w : ℂ} (hne : z ≠ w) (p : ℝ × ℝ) (ω : GridSample) :
    error (p,ω) z w = gridDepth ω (rotatePair p.1 p.2 z) (rotatePair p.1 p.2 w) +
      Real.log (Real.exp (-p.1)*‖z-w‖) := by
  rw [Real.log_mul (Real.exp_ne_zero _) (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hne)), Real.log_exp]
  simp only [error, depth]
  ring

lemma error_integrable_fixed {z w : ℂ} (hne : z ≠ w) (p : ℝ × ℝ) :
    Integrable (fun ω => error (p,ω) z w) squareLaw := by
  simp_rw [error_fixed_phase hne p]
  exact error_integrable (rotatePair_ne _ _ hne)
    (mul_pos (Real.exp_pos _) (norm_pos_iff.mpr (sub_ne_zero.mpr hne)))
    (rotatePair_gaps _ _ _ _).1 (rotatePair_gaps _ _ _ _).2

lemma mean_abs_error_fixed {z w : ℂ} (hne : z ≠ w) (p : ℝ × ℝ) :
    (∫ ω, |error (p,ω) z w| ∂squareLaw) ≤ 4 := by
  simp_rw [error_fixed_phase hne p]
  exact mean_abs_error_le (rotatePair_ne _ _ hne)
    (mul_pos (Real.exp_pos _) (norm_pos_iff.mpr (sub_ne_zero.mpr hne)))
    (rotatePair_gaps _ _ _ _).1 (rotatePair_gaps _ _ _ _).2

lemma error_integrable_full {z w : ℂ} (hne : z ≠ w) :
    Integrable (fun ω => error ω z w) fullLaw := by
  apply (integrable_prod_iff (measurable_error hne).aestronglyMeasurable).mpr
  constructor
  · exact Filter.Eventually.of_forall (error_integrable_fixed hne)
  · apply Integrable.of_bound ((measurable_error hne).norm.stronglyMeasurable.integral_prod_right.aestronglyMeasurable) 4
    filter_upwards with p
    rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg (fun _ => norm_nonneg _))]
    simpa only [Real.norm_eq_abs] using mean_abs_error_fixed hne p

lemma mean_error_fixed {z w : ℂ} (hne : z ≠ w) (p : ℝ × ℝ) :
    (∫ ω, error (p,ω) z w ∂squareLaw) =
      polarMean (Real.log ‖z-w‖-p.1) (p.2+(z-w).arg) := by
  have hi : Integrable (fun ω => gridDepth ω (rotatePair p.1 p.2 z) (rotatePair p.1 p.2 w)) squareLaw :=
    gridDepth_integrable (rotatePair_ne _ _ hne)
  have his : Integrable (fun ω => gridDepth ω (rotatePair p.1 p.2 z) (rotatePair p.1 p.2 w) - p.1) squareLaw :=
    hi.sub (integrable_const p.1)
  simp only [error, depth]
  rw [integral_add his (integrable_const (Real.log ‖z-w‖)), integral_sub hi (integrable_const p.1)]
  simp only [integral_const, probReal_univ, one_smul]
  exact rotated_mean _ _ hne

lemma measurable_shifted_polarMean (t φ : ℝ) :
    Measurable (fun p : ℝ × ℝ => polarMean (t-p.1) (p.2+φ)) := by
  have h₁ : Measurable (fun p : ℝ × ℝ => t-p.1) := measurable_const.sub measurable_fst
  have h₂ : Measurable (fun p : ℝ × ℝ => p.2+φ) := measurable_snd.add_const φ
  change Measurable ((fun p : ℝ × ℝ => polarMean p.1 p.2) ∘
    (fun p : ℝ × ℝ => (t-p.1,p.2+φ)))
  apply Measurable.comp measurable_polarMean
  exact h₁.prodMk h₂

lemma mean_error_full {z w : ℂ} (hne : z ≠ w) :
    (∫ ω, error ω z w ∂fullLaw) = kappa := by
  rw [fullLaw, integral_prod _ (error_integrable_full hne)]
  simp_rw [mean_error_fixed hne]
  have hm := measurable_shifted_polarMean (Real.log ‖z-w‖) (z-w).arg
  have hi := Integrable.of_bound (μ := phaseLaw) hm.aestronglyMeasurable 4
    (Filter.Eventually.of_forall (fun p => by simpa only [Real.norm_eq_abs] using polarMean_bound _ _))
  rw [phaseLaw, integral_prod _ hi]
  exact polar_average_constant _ _

lemma abs_error_tail_full {z w : ℂ} (hne : z ≠ w) {u : ℝ} (hu : 0 ≤ u) :
    fullLaw.real {ω | u < |error ω z w|} ≤ 4*Real.exp (-u) := by
  have hs : MeasurableSet {ω : FullSample | u < |error ω z w|} :=
    measurableSet_lt measurable_const (measurable_error hne).abs
  have hb : fullLaw {ω | u < |error ω z w|} ≤ ENNReal.ofReal (4*Real.exp (-u)) := by
    rw [fullLaw, Measure.prod_apply hs]
    calc
      _ ≤ ∫⁻ _p, ENNReal.ofReal (4*Real.exp (-u)) ∂phaseLaw := by
        apply lintegral_mono
        intro p
        have he : squareLaw.real {ω | u < |error (p,ω) z w|} ≤ 4*Real.exp (-u) := by
          simp_rw [error_fixed_phase hne p]
          exact error_abs_tail (rotatePair_ne _ _ hne)
            (mul_pos (Real.exp_pos _) (norm_pos_iff.mpr (sub_ne_zero.mpr hne)))
            (rotatePair_gaps _ _ _ _).1 (rotatePair_gaps _ _ _ _).2 hu
        have hh := ENNReal.ofReal_le_ofReal he
        rw [measureReal_def, ENNReal.ofReal_toReal (measure_ne_top _ _)] at hh
        exact hh
      _ = _ := by simp
  have hh := ENNReal.toReal_mono ENNReal.ofReal_ne_top hb
  rw [measureReal_def]
  simpa only [ENNReal.toReal_ofReal (by positivity : 0 ≤ 4*Real.exp (-u))] using hh

lemma mean_abs_error_full {z w : ℂ} (hne : z ≠ w) :
    (∫ ω, |error ω z w| ∂fullLaw) ≤ 4 := by
  rw [fullLaw, integral_prod _ (error_integrable_full hne).abs]
  calc
    _ ≤ ∫ _p, (4:ℝ) ∂phaseLaw := integral_mono
      (error_integrable_full hne).abs.integral_prod_left (integrable_const _)
      (mean_abs_error_fixed hne)
    _ = _ := by simp

lemma depth_ultra_ae {x y z : ℂ} (hxy : x ≠ y) (hyz : y ≠ z) (hxz : x ≠ z) :
    ∀ᵐ ω ∂fullLaw, min (depth ω x y) (depth ω y z) ≤ depth ω x z := by
  have hs : MeasurableSet {ω : FullSample | min (depth ω x y) (depth ω y z) ≤ depth ω x z} :=
    measurableSet_le ((measurable_depth hxy).min (measurable_depth hyz)) (measurable_depth hxz)
  apply (Measure.ae_prod_iff_ae_ae hs).mpr
  filter_upwards with p
  filter_upwards [gridDepth_ultra_ae (rotatePair_ne p.1 p.2 hxy)
    (rotatePair_ne p.1 p.2 hyz) (rotatePair_ne p.1 p.2 hxz)] with ω hh
  simpa only [depth,min_sub_sub_right,sub_le_sub_iff_right] using hh

end WeakPinned.Grid

end
end
end
end

end OAI
end

section
-- module Solutions.OAIQW_WeakPinned.ArithmeticHierarchy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u1 u2 u3 u4

section
noncomputable section
open NumberField
open scoped BigOperators
noncomputable section
open MeasureTheory
open scoped Topology
noncomputable section
open MeasureTheory
open scoped Topology ENNReal

noncomputable section
open MeasureTheory NumberField
open scoped BigOperators
namespace WeakPinned.Global
open Hierarchy
variable {P : Type u1} [Fintype P] [DecidableEq P]
variable {K : Type u2} [Field K] [NumberField K]
variable (Z : P → K) (hZ : Function.Injective Z)
include hZ

omit [Fintype P] [DecidableEq P] [NumberField K] in
lemma embedding_ne (v : InfinitePlace K) {x y : P} (hne : x ≠ y) :
    v.embedding (Z x) ≠ v.embedding (Z y) :=
  fun hh => hne (hZ (v.embedding.injective hh))

omit [DecidableEq P] [NumberField K] in
lemma measurableSet_good (v : InfinitePlace K) : MeasurableSet {ω | good Z v ω} := by
  simp only [good, Set.ofPred_forall]
  apply MeasurableSet.iInter
  intro x
  apply MeasurableSet.iInter
  intro y
  apply MeasurableSet.iInter
  intro z
  apply MeasurableSet.iInter
  intro hxy
  apply MeasurableSet.iInter
  intro hyz
  apply MeasurableSet.iInter
  intro hxz
  exact measurableSet_le
    ((Grid.measurable_depth (embedding_ne Z hZ v hxy)).min
      (Grid.measurable_depth (embedding_ne Z hZ v hyz)))
    (Grid.measurable_depth (embedding_ne Z hZ v hxz))

omit [DecidableEq P] [NumberField K] in
lemma good_ae (v : InfinitePlace K) : ∀ᵐ ω ∂Grid.fullLaw, good Z v ω := by
  simp only [good, Filter.eventually_all]
  intro x y z hxy hyz hxz
  exact Grid.depth_ultra_ae (embedding_ne Z hZ v hxy)
    (embedding_ne Z hZ v hyz) (embedding_ne Z hZ v hxz)

omit [NumberField K] in
lemma arch_value_ae (v : InfinitePlace K) {x y : P} (hxy : x ≠ y) :
    (fun ω => (arch Z v ω).value x y) =ᵐ[Grid.fullLaw]
      (fun ω => Grid.depth ω (v.embedding (Z x)) (v.embedding (Z y))) := by
  filter_upwards [good_ae Z hZ v] with ω h
  simp [arch,h,hxy]

omit [NumberField K] in
lemma arch_measurable (v : InfinitePlace K) (x y : P) :
    Measurable (fun ω => (arch Z v ω).value x y) := by
  by_cases hxy : x = y
  · subst y
    simpa only [arch,ne_eq,not_true_eq_false,and_false,reduceIte] using
      (measurable_const : Measurable (fun _ : Grid.FullSample => (0:ℝ)))
  · simpa [arch,hxy] using (Grid.measurable_depth (embedding_ne Z hZ v hxy)).ite
      (measurableSet_good Z hZ v) (measurable_const : Measurable (fun _ : Grid.FullSample => (0:ℝ)))

omit [NumberField K] in
lemma arch_integrable (v : InfinitePlace K) (x y : P) :
    Integrable (fun ω => (arch Z v ω).value x y) Grid.fullLaw := by
  by_cases hxy : x = y
  · subst y
    simpa only [arch,ne_eq,not_true_eq_false,and_false,reduceIte] using
      (integrable_const (0:ℝ) : Integrable (fun _ : Grid.FullSample => (0:ℝ)) Grid.fullLaw)
  · have hi := (Grid.error_integrable_full (embedding_ne Z hZ v hxy)).sub
      (integrable_const (Real.log ‖v.embedding (Z x) - v.embedding (Z y)‖))
    have he : (fun ω => Grid.error ω (v.embedding (Z x)) (v.embedding (Z y)) -
        Real.log ‖v.embedding (Z x) - v.embedding (Z y)‖) =
        (fun ω => Grid.depth ω (v.embedding (Z x)) (v.embedding (Z y))) := by
      funext ω; simp only [Grid.error,add_sub_cancel_right]
    change Integrable (fun ω => Grid.error ω (v.embedding (Z x)) (v.embedding (Z y)) -
        Real.log ‖v.embedding (Z x) - v.embedding (Z y)‖) Grid.fullLaw at hi
    rw [he] at hi
    exact hi.congr (arch_value_ae Z hZ v hxy).symm

lemma arch_mean (v : InfinitePlace K) (x y : P) (hxy : x ≠ y) :
    (∫ ω, (arch Z v ω).value x y ∂Grid.fullLaw) = -Real.log (v (Z x-Z y)) + Grid.kappa := by
  rw [integral_congr_ae (arch_value_ae Z hZ v hxy)]
  have hh := Grid.mean_error_full (embedding_ne Z hZ v hxy)
  have hi := (arch_integrable Z hZ v x y).congr (arch_value_ae Z hZ v hxy)
  simp only [Grid.error] at hh
  rw [integral_add hi (integrable_const _)] at hh
  simp only [integral_const,probReal_univ,one_smul] at hh
  rw [← map_sub, InfinitePlace.norm_embedding_eq] at hh
  linarith

omit [DecidableEq P] in
lemma badPlaces_mem (v : FinitePlace K) : v ∈ badPlaces Z hZ ↔ ∃ x y, x ≠ y ∧ v (Z x-Z y) ≠ 1 := by
  simp only [badPlaces, Set.Finite.mem_toFinset]
  constructor
  · rintro ⟨⟨⟨x,y⟩,hne⟩,hh⟩
    exact ⟨x,y,hne,hh⟩
  · rintro ⟨x,y,hne,hh⟩
    exact ⟨⟨(x,y),hne⟩,hh⟩

lemma finite_value_sum (x y : P) (hxy : x ≠ y) :
    (∑ v ∈ badPlaces Z hZ, (finite Z hZ v).value x y) =
      ∑ᶠ v : FinitePlace K, -Real.log (v (Z x-Z y)) := by
  simp only [finite,hxy,reduceIte]
  symm
  apply finsum_eq_sum_of_support_subset
  intro v hv
  apply (badPlaces_mem Z hZ v).mpr
  refine ⟨x,y,hxy,?_⟩
  intro hh
  exact hv (by simp [hh])

lemma coordinate_overlap_identity (hn : 2 ≤ Fintype.card P) (x y : P) (hxy : x ≠ y) :
    L Z hZ x y hxy = Grid.kappa - M Z hZ + S Z hZ x + S Z hZ y := by
  have harch : (∑ v : InfinitePlace K, Arithmetic.archWeight v *
      (∫ ω, (arch Z v ω).M ∂Grid.fullLaw)) +
      (∑ v : InfinitePlace K, Arithmetic.archWeight v *
      (∫ ω, (arch Z v ω).overlapLength x y hxy ∂Grid.fullLaw)) -
      (∑ v : InfinitePlace K, Arithmetic.archWeight v *
      (∫ ω, (arch Z v ω).potential x ∂Grid.fullLaw)) -
      (∑ v : InfinitePlace K, Arithmetic.archWeight v *
      (∫ ω, (arch Z v ω).potential y ∂Grid.fullLaw)) =
      (∑ v : InfinitePlace K, Arithmetic.archWeight v * (-Real.log (v (Z x-Z y)))) + Grid.kappa := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    have he : ∀ v : InfinitePlace K,
        Arithmetic.archWeight v * (∫ ω, (arch Z v ω).M ∂Grid.fullLaw) +
        Arithmetic.archWeight v * (∫ ω, (arch Z v ω).overlapLength x y hxy ∂Grid.fullLaw) -
        Arithmetic.archWeight v * (∫ ω, (arch Z v ω).potential x ∂Grid.fullLaw) -
        Arithmetic.archWeight v * (∫ ω, (arch Z v ω).potential y ∂Grid.fullLaw) =
        Arithmetic.archWeight v * (-Real.log (v (Z x-Z y))) + Arithmetic.archWeight v * Grid.kappa := by
      intro v
      have hh := Depth.integral_depth_identity (arch Z v) (arch_measurable Z hZ v)
        (arch_integrable Z hZ v) hn x y hxy
      rw [arch_mean Z hZ v x y hxy] at hh
      linear_combination -Arithmetic.archWeight v * hh
    simp_rw [he]
    rw [Finset.sum_add_distrib, ← Finset.sum_mul, Arithmetic.sum_archWeight,one_mul]
  have hfin : (∑ v ∈ badPlaces Z hZ, (finite Z hZ v).M) +
      (∑ v ∈ badPlaces Z hZ, (finite Z hZ v).overlapLength x y hxy) -
      (∑ v ∈ badPlaces Z hZ, (finite Z hZ v).potential x) -
      (∑ v ∈ badPlaces Z hZ, (finite Z hZ v).potential y) =
      ∑ᶠ v : FinitePlace K, -Real.log (v (Z x-Z y)) := by
    rw [← finite_value_sum Z hZ x y hxy, ← Finset.sum_add_distrib,
      ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro v _
    exact ((finite Z hZ v).depth_identity hn x y hxy).symm
  have hprod := Arithmetic.normalized_log_product_formula (Z x-Z y) (sub_ne_zero.mpr (hZ.ne hxy))
  dsimp only [L,M,S]
  linear_combination harch + (Module.finrank ℚ K : ℝ)⁻¹ * hfin + hprod

lemma S_nonneg (x : P) : 0 ≤ S Z hZ x := by
  apply add_nonneg
  · exact Finset.sum_nonneg (fun v _ => mul_nonneg (Arithmetic.archWeight_nonneg v)
      (integral_nonneg (fun ω => (arch Z v ω).potential_nonneg x)))
  · exact mul_nonneg (by positivity) (Finset.sum_nonneg (fun v _ => (finite Z hZ v).potential_nonneg x))

end WeakPinned.Global

namespace WeakPinned.Hierarchy.Depth
open MeasureTheory
variable {P : Type u3} [Fintype P] [DecidableEq P]
variable (d : Depth P)

lemma sum_map_count (m : Multiset (Finset P)) (f : Finset P → ℝ) :
    (m.map f).sum = ∑ C, (m.count C : ℝ) * f C := by
  induction m using Multiset.induction_on with
  | empty => simp
  | @cons a m ih =>
      simp only [Multiset.map_cons, Multiset.sum_cons, ih, Multiset.count_cons]
      simp_rw [Nat.cast_add, add_mul]
      rw [Finset.sum_add_distrib]
      simp [add_comm]

lemma sumCells_count (f : Finset P → ℝ) (r : ℝ) :
    d.sumCells f r = ∑ C, d.count r C * f C := sum_map_count _ _

lemma count_nonneg (r : ℝ) (C : Finset P) : 0 ≤ d.count r C := Nat.cast_nonneg _

lemma count_le_overlap (r : ℝ) (C : Finset P) (x y : P) (hx : x ∈ C) (hy : y ∈ C) :
    d.count r C ≤ d.pairOverlap r x y := by
  rw [pairOverlap, d.sumCells_count]
  calc
    d.count r C = d.count r C * (if x ∈ C ∧ y ∈ C then (1 : ℝ) else 0) := by simp [hx,hy]
    _ ≤ _ := Finset.single_le_sum (f := fun D => d.count r D * (if x ∈ D ∧ y ∈ D then (1 : ℝ) else 0)) (fun D _ => mul_nonneg (d.count_nonneg r D) (by positivity)) (Finset.mem_univ C)

lemma measurable_count (C : Finset P) : Measurable (fun r => d.count r C) := by
  let F : Finset (Finset P) × Finset (Finset P) → ℝ := fun st =>
    (((st.1.filter (fun D => ¬Fintype.card P < 2*D.card)).val +
       st.2.val.map (fun D => Dᶜ)).count C : ℝ)
  have hh : Measurable (fun r => F (d.cells r, d.giants r)) :=
    (measurable_of_finite F).comp (d.measurable_cells.prodMk d.measurable_giants)
  change Measurable (fun r => F (d.cells r, d.giants r))
  exact hh

lemma integrable_count (hn : 2 ≤ Fintype.card P) (C : Finset P) (hC : 2 ≤ C.card) :
    Integrable (fun r => d.count r C) := by
  obtain ⟨x,hx,y,hy,hxy⟩ := Finset.one_lt_card.mp hC
  apply (d.integrable_pairOverlap hn x y hxy).mono' (d.measurable_count C).aestronglyMeasurable
  filter_upwards with r
  simpa only [Real.norm_eq_abs, abs_of_nonneg (d.count_nonneg r C)] using d.count_le_overlap r C x y hx hy

lemma mass_nonneg (C : Finset P) : 0 ≤ d.mass C := by
  unfold mass
  split_ifs
  · exact integral_nonneg (fun r => d.count_nonneg r C)
  · rfl

lemma mass_singleton (C : Finset P) (hC : C.card ≤ 1) : d.mass C = 0 := by
  simp [mass, show ¬2 ≤ C.card by omega]

lemma mass_le_overlap (hn : 2 ≤ Fintype.card P) (C : Finset P) (x y : P)
    (hxy : x ≠ y) (hx : x ∈ C) (hy : y ∈ C) :
    d.mass C ≤ d.overlapLength x y hxy := by
  have hC : 2 ≤ C.card := Finset.one_lt_card.mpr ⟨x,hx,y,hy,hxy⟩
  rw [mass, ite_eq_left hC, overlapLength]
  exact integral_mono (d.integrable_count hn C hC) (d.integrable_pairOverlap hn x y hxy)
    (fun r => d.count_le_overlap r C x y hx hy)

lemma integral_sumCells (hn : 2 ≤ Fintype.card P) (f : Finset P → ℝ)
    (hf : ∀ C, C.card ≤ 1 → f C = 0) :
    (∫ r, d.sumCells f r) = ∑ C, d.mass C * f C := by
  have hi (C : Finset P) : Integrable (fun r => d.count r C * f C) := by
    by_cases hC : 2 ≤ C.card
    · exact (d.integrable_count hn C hC).mul_const _
    · simp [hf C (by omega)]
  simp_rw [d.sumCells_count]
  rw [integral_finsetSum _ (fun C _ => hi C)]
  apply Finset.sum_congr rfl
  intro C _
  by_cases hC : 2 ≤ C.card
  · simp [mass,hC,integral_mul_const]
  · simp [mass,hC,hf C (by omega)]

lemma mass_overlap (hn : 2 ≤ Fintype.card P) (x y : P) (hxy : x ≠ y) :
    (∑ C, d.mass C * (if x ∈ C ∧ y ∈ C then (1 : ℝ) else 0)) =
      d.overlapLength x y hxy := by
  symm
  apply d.integral_sumCells hn
  intro C hC
  have hh : ¬(x ∈ C ∧ y ∈ C) := by
    rintro ⟨hx,hy⟩
    have := Finset.one_lt_card.mpr ⟨x,hx,y,hy,hxy⟩
    omega
  simp [hh]

section Param
variable {Ω : Type u4} [MeasurableSpace Ω] (D : Ω → Depth P)
    (hD : ∀ x y, Measurable (fun ω => (D ω).value x y))
include hD
lemma measurable_count_param (C : Finset P) :
    Measurable (fun p : Ω × ℝ => (D p.1).count p.2 C) := by
  let F : Finset (Finset P) × Finset (Finset P) → ℝ := fun st =>
    (((st.1.filter (fun E => ¬Fintype.card P < 2*E.card)).val +
       st.2.val.map (fun E => Eᶜ)).count C : ℝ)
  have hm : Measurable (fun p : Ω×ℝ => ((D p.1).cells p.2, (D p.1).giants p.2)) :=
    (measurable_cells_param (P:=P) (Ω:=Ω×ℝ) (fun p : Ω×ℝ => D p.1)
      (fun x y => (hD x y).comp measurable_fst) Prod.snd measurable_snd).prodMk
    (measurable_giants_param (P:=P) (Ω:=Ω×ℝ) (fun p : Ω×ℝ => D p.1)
      (fun x y => (hD x y).comp measurable_fst) Prod.snd measurable_snd)
  have hh : Measurable (fun p : Ω×ℝ => F ((D p.1).cells p.2, (D p.1).giants p.2)) :=
    (measurable_of_finite F).comp hm
  change Measurable (fun p : Ω×ℝ => F ((D p.1).cells p.2, (D p.1).giants p.2))
  exact hh

lemma measurable_mass_param (C : Finset P) : Measurable (fun ω => (D ω).mass C) := by
  unfold mass
  split_ifs with hC
  · exact (measurable_count_param D hD C).stronglyMeasurable.integral_prod_right.measurable
  · exact measurable_const

lemma integrable_mass_param {μ : Measure Ω}
    (hi : ∀ x y, Integrable (fun ω => (D ω).value x y) μ)
    (hn : 2 ≤ Fintype.card P) (C : Finset P) :
    Integrable (fun ω => (D ω).mass C) μ := by
  by_cases hC : 2 ≤ C.card
  · obtain ⟨x,hx,y,hy,hxy⟩ := Finset.one_lt_card.mp hC
    apply (integrable_overlapLength_param D hD hi hn x y hxy).mono'
      (measurable_mass_param D hD C).aestronglyMeasurable
    filter_upwards with ω
    simpa only [Real.norm_eq_abs, abs_of_nonneg ((D ω).mass_nonneg C)] using
      (D ω).mass_le_overlap hn C x y hxy hx hy
  · simp only [mass, hC, reduceIte]
    exact integrable_zero _ _ _

lemma averaged_mass_overlap {μ : Measure Ω}
    (hi : ∀ x y, Integrable (fun ω => (D ω).value x y) μ)
    (hn : 2 ≤ Fintype.card P) (x y : P) (hxy : x ≠ y) :
    (∑ C, (∫ ω, (D ω).mass C ∂μ) * (if x ∈ C ∧ y ∈ C then (1 : ℝ) else 0)) =
      ∫ ω, (D ω).overlapLength x y hxy ∂μ := by
  simp_rw [← integral_mul_const]
  rw [← integral_finsetSum _ (fun C _ => (integrable_mass_param D hD hi hn C).mul_const _)]
  exact integral_congr_ae (Filter.Eventually.of_forall (fun ω => (D ω).mass_overlap hn x y hxy))
end Param
end WeakPinned.Hierarchy.Depth

end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQW_WeakPinned.Variance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u1 u2 u3 u4 u5

section
noncomputable section
open NumberField
open scoped BigOperators
noncomputable section
open MeasureTheory
open scoped Topology
noncomputable section
open MeasureTheory
open scoped Topology ENNReal
noncomputable section
open MeasureTheory NumberField
open scoped BigOperators

/- Finite off-diagonal variance. All diagonal terms are identically zero,
   not O(1/n): singleton cells may persist forever. -/
noncomputable section
open scoped BigOperators
open MeasureTheory
namespace WeakPinned.Variance

variable {P : Type u1} [Fintype P] [DecidableEq P]

lemma sum_pairProb (B : Finset P) (hB : 2 ≤ B.card) (x : P) :
    ∑ y, pairProb B x y = prob B x := by
  classical
  by_cases hx : x ∈ B
  · have hk : (B.card : ℝ) ≠ 0 := by exact_mod_cast (by omega : B.card ≠ 0)
    have hk1 : (B.card : ℝ) - 1 ≠ 0 := by
      have : (2 : ℝ) ≤ B.card := by exact_mod_cast hB
      linarith
    have he : ∀ y, pairProb B x y = if y ∈ B.erase x then
        1 / ((B.card : ℝ) * (B.card - 1)) else 0 := by
      intro y
      simp only [pairProb, hx, true_and, Finset.mem_erase, ne_comm (a := y)]
      simp only [and_comm]
    simp_rw [he]
    simp only [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const,
      nsmul_eq_mul, Finset.card_erase_of_mem hx]
    rw [Nat.cast_sub (by omega)]
    simp only [Nat.cast_one, prob, hx, reduceIte]
    field_simp
  · simp [pairProb, prob, hx]

omit [Fintype P] in
lemma pairProb_symm (B : Finset P) (x y : P) : pairProb B x y = pairProb B y x := by
  simp only [pairProb, and_left_comm, ne_comm]

omit [Fintype P] in
lemma pairProb_diag (B : Finset P) (x : P) : pairProb B x x = 0 := by
  simp [pairProb]

omit [Fintype P] in
lemma sum_prob_cell (B C : Finset P) : ∑ x ∈ C, prob B x = cellProb B C := by
  simp only [prob, Finset.sum_ite_mem, Finset.sum_const, nsmul_eq_mul, mul_one_div,
    cellProb, Finset.inter_comm]

omit [Fintype P] in
lemma pairCell_formula (B C : Finset P) :
    pairCell B C = ((B ∩ C).card : ℝ) * ((B ∩ C).card - 1) /
      ((B.card : ℝ) * (B.card - 1)) := by
  classical
  unfold pairCell pairProb
  rw [← Finset.sum_product C C (fun xy : P × P =>
    if xy.1 ∈ B ∧ xy.2 ∈ B ∧ xy.1 ≠ xy.2 then
      1 / ((B.card : ℝ) * (B.card - 1)) else 0), ← Finset.sum_filter]
  have hf : (C ×ˢ C).filter (fun xy => xy.1 ∈ B ∧ xy.2 ∈ B ∧ xy.1 ≠ xy.2) =
      (B ∩ C).offDiag := by
    ext ⟨x,y⟩
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_offDiag, Finset.mem_inter]
    tauto
  rw [hf, Finset.sum_const, nsmul_eq_mul, Finset.offDiag_card, ← Nat.mul_sub_one]
  by_cases hb : (B ∩ C).card = 0
  · simp [hb]
  · rw [Nat.cast_mul, Nat.cast_sub (by omega), Nat.cast_one]
    ring

omit [Fintype P] in
lemma cellProb_nonneg (B C : Finset P) : 0 ≤ cellProb B C := by
  unfold cellProb
  positivity

omit [Fintype P] in
lemma pairCell_nonneg (B C : Finset P) : 0 ≤ pairCell B C := by
  unfold pairCell pairProb
  apply Finset.sum_nonneg
  intro x _
  apply Finset.sum_nonneg
  intro y _
  split_ifs with h
  · have : 2 ≤ B.card := Finset.one_lt_card.mpr ⟨x,h.1,y,h.2.1,h.2.2⟩
    have : (2 : ℝ) ≤ B.card := by exact_mod_cast this
    have : 0 ≤ (B.card : ℝ) - 1 := by linarith
    positivity
  · rfl

private lemma pair_fraction_bounds (n m : ℝ) (hm : 2 ≤ m) (hmn : m ≤ n) :
    (1/2) * (m/n)^2 ≤ m*(m-1)/(n*(n-1)) ∧
      m*(m-1)/(n*(n-1)) ≤ (m/n)^2 := by
  have hn : 0 < n := by linarith
  have hn1 : 0 < n-1 := by linarith
  have hmn0 : 0 ≤ m/n := div_nonneg (by linarith) hn.le
  have hlow : m/(2*n) ≤ (m-1)/(n-1) := by
    apply (div_le_div_iff₀ (by positivity) hn1).mpr
    nlinarith [mul_nonneg hn.le (show 0 ≤ m-2 by linarith)]
  have hupp : (m-1)/(n-1) ≤ m/n := by
    apply (div_le_div_iff₀ hn1 hn).mpr
    nlinarith
  have he : m*(m-1)/(n*(n-1)) = (m/n)*((m-1)/(n-1)) := by
    field_simp
  rw [he]
  constructor
  · calc
      (1/2) * (m/n)^2 = (m/n)*(m/(2*n)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hlow hmn0
  · simpa only [sq] using mul_le_mul_of_nonneg_left hupp hmn0

lemma uniform_pair_comparison (C : Finset P) (hC : 2 ≤ C.card) :
    (1/2) * (cellProb Finset.univ C)^2 ≤ pairCell Finset.univ C ∧
      pairCell Finset.univ C ≤ (cellProb Finset.univ C)^2 := by
  rw [pairCell_formula]
  simp only [cellProb, Finset.univ_inter, Finset.card_univ]
  apply pair_fraction_bounds
  · exact_mod_cast hC
  · exact_mod_cast Finset.card_le_univ C

omit [Fintype P] in
lemma singleton_pairCell (B C : Finset P) (hC : C.card ≤ 1) : pairCell B C = 0 := by
  unfold pairCell
  apply Finset.sum_eq_zero
  intro x hx
  apply Finset.sum_eq_zero
  intro y hy
  have : x = y := Finset.card_le_one.mp hC x hx y hy
  subst y
  exact pairProb_diag B x

omit [Fintype P] in
lemma singleton_fiber_term (B C : Finset P) (hB : 2 ≤ B.card) (hC : C.card ≤ 1) :
    (if 2 / (B.card : ℝ) ≤ cellProb B C then (cellProb B C)^2 else 0) = 0 := by
  have hk : 0 < (B.card : ℝ) := by exact_mod_cast (by omega : 0 < B.card)
  have hi : (B ∩ C).card ≤ 1 := (Finset.card_le_card Finset.inter_subset_right).trans hC
  have hiR : ((B ∩ C).card : ℝ) < 2 := by exact_mod_cast (by omega : (B ∩ C).card < 2)
  have hp : cellProb B C < 2 / (B.card : ℝ) :=
    (div_lt_div_iff_of_pos_right hk).mpr hiR
  simp only [not_le.mpr hp, reduceIte]

section Family
variable {I : Type u2} [Fintype I]
variable (w : I → ℝ) (B : I → Finset P)

lemma mean_cell_bound (C : Finset P) (M : ℝ)
    (hdom : ∀ x, (∑ i, w i * prob (B i) x) ≤ M * prob Finset.univ x) :
    (∑ i, w i * cellProb (B i) C) ≤ M * cellProb Finset.univ C := by
  simp_rw [← sum_prob_cell, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_le_sum fun x _ => hdom x

end Family

section CellIntegral
variable {Ω : Type u3} [MeasurableSpace Ω]

section Quantitative
local instance instMeasurableSpaceFinset_solutions_rdb9730_1 : MeasurableSpace (Finset P) := ⊤
local instance instDiscreteMeasurableSpaceFinset_solutions_rdb9730_1 : DiscreteMeasurableSpace (Finset P) := ⟨fun _ => trivial⟩
variable {I : Type u5} [Fintype I]

lemma varianceCell_singleton (w : I → ℝ) (B : I → Finset P) (T : ℝ)
    (hT : 1 ≤ T) (hB : ∀ i, 2 ≤ (B i).card) (D : Finset P) (hD : D.card ≤ 1) :
    varianceCell w B T D = 0 := by
  have hd : (D.card : ℝ) ≤ T := (by exact_mod_cast hD : (D.card : ℝ) ≤ 1).trans hT
  simp [varianceCell, not_lt.mpr hd, singleton_fiber_term _ _ (hB _) hD]

end Quantitative

end CellIntegral

end WeakPinned.Variance

end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQW_WeakPinned.ArithmeticVariance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u1 u2 u3 u4 u5 u6 u7

section
noncomputable section
open NumberField
open scoped BigOperators
noncomputable section
open MeasureTheory
open scoped Topology
noncomputable section
open MeasureTheory
open scoped Topology ENNReal
noncomputable section
open MeasureTheory NumberField
open scoped BigOperators
noncomputable section
open scoped BigOperators
open MeasureTheory

namespace WeakPinned.Global
open Hierarchy
variable {P : Type u1} [Fintype P] [DecidableEq P]
variable {K : Type u2} [Field K] [NumberField K]
variable (Z : P → K) (hZ : Function.Injective Z)

lemma cellMass_nonneg (C : Finset P) : 0 ≤ cellMass Z hZ C := by
  exact add_nonneg
    (Finset.sum_nonneg (fun v _ => mul_nonneg (Arithmetic.archWeight_nonneg v)
      (integral_nonneg (fun ω => (arch Z v ω).mass_nonneg C))))
    (mul_nonneg (by positivity) (Finset.sum_nonneg (fun v _ => (finite Z hZ v).mass_nonneg C)))

lemma cellMass_overlap (hn : 2 ≤ Fintype.card P) (x y : P) (hxy : x ≠ y) :
    (∑ C, cellMass Z hZ C * (if x ∈ C ∧ y ∈ C then (1 : ℝ) else 0)) = L Z hZ x y hxy := by
  simp only [cellMass, add_mul, Finset.sum_add_distrib, Finset.sum_mul,
    mul_assoc, L]
  rw [← Finset.mul_sum]
  congr 1
  · rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro v _
    rw [← Finset.mul_sum, Depth.averaged_mass_overlap (arch Z v) (arch_measurable Z hZ v)
      (arch_integrable Z hZ v) hn x y hxy]
  · congr 1
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro v _
    exact (finite Z hZ v).mass_overlap hn x y hxy

end WeakPinned.Global

namespace WeakPinned.Global
open Hierarchy Variance
variable {P : Type u5} [Fintype P] [DecidableEq P]
variable {K : Type u6} [Field K] [NumberField K]
variable (Z₁ Z₂ : P → K) (h₁ : Function.Injective Z₁) (h₂ : Function.Injective Z₂)

lemma totalMass_nonneg (C : Finset P) : 0 ≤ totalMass Z₁ Z₂ h₁ h₂ C :=
  add_nonneg (cellMass_nonneg Z₁ h₁ C) (cellMass_nonneg Z₂ h₂ C)

lemma totalPotential_nonneg (x : P) : 0 ≤ totalPotential Z₁ Z₂ h₁ h₂ x :=
  add_nonneg (S_nonneg Z₁ h₁ x) (S_nonneg Z₂ h₂ x)

lemma totalMass_overlap (hn : 2 ≤ Fintype.card P) (x y : P) (hxy : x ≠ y) :
    weightedOverlap (totalMass Z₁ Z₂ h₁ h₂) x y =
      baseConstant Z₁ Z₂ h₁ h₂ + totalPotential Z₁ Z₂ h₁ h₂ x + totalPotential Z₁ Z₂ h₁ h₂ y := by
  simp only [weightedOverlap,weightedIntegral,totalMass,add_mul,Finset.sum_add_distrib]
  rw [cellMass_overlap Z₁ h₁ hn x y hxy,cellMass_overlap Z₂ h₂ hn x y hxy,
    coordinate_overlap_identity Z₁ h₁ hn x y hxy,coordinate_overlap_identity Z₂ h₂ hn x y hxy]
  simp only [baseConstant,totalPotential]
  ring

end WeakPinned.Global

end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQW_WeakPinned.SmallCells
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u1 u2 u3 u4 u5 u6 u7 u8 u9

section
noncomputable section
open NumberField
open scoped BigOperators
noncomputable section
open MeasureTheory
open scoped Topology
noncomputable section
open MeasureTheory
open scoped Topology ENNReal
noncomputable section
open MeasureTheory NumberField
open scoped BigOperators
noncomputable section
open scoped BigOperators
open MeasureTheory

namespace WeakPinned.SmallFiber
open MeasureTheory
variable {P : Type u3} [Fintype P] [DecidableEq P]

omit [Fintype P] [DecidableEq P] in
lemma mass_nonneg {p : P → ℝ} (hp : ∀ y, 0 ≤ p y) (C : Finset P) : 0 ≤ mass p C :=
  Finset.sum_nonneg (fun y _ => hp y)

end WeakPinned.SmallFiber

end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQW_WeakPinned.FiberOverlap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u1 u2 u3 u4 u5 u6 u7 u8 u9 u10

section
noncomputable section
open NumberField
open scoped BigOperators
noncomputable section
open MeasureTheory
open scoped Topology
noncomputable section
open MeasureTheory
open scoped Topology ENNReal
noncomputable section
open MeasureTheory NumberField
open scoped BigOperators
noncomputable section
open scoped BigOperators
open MeasureTheory

namespace WeakPinned.Hierarchy.Depth
variable {P : Type u3} [Fintype P] [DecidableEq P]
variable (d : Depth P)

lemma sumCells_split (f : Finset P → ℝ) (r : ℝ) :
    d.sumCells f r =
      (∑ C ∈ d.cells r, if ¬Fintype.card P < 2*C.card then f C else 0) +
      ∑ C ∈ d.giants r, f Cᶜ := by
  classical
  simp only [sumCells,transformed,Multiset.map_add,Multiset.sum_add,
    Multiset.map_map,Function.comp_def]
  change (∑ C ∈ (d.cells r).filter (fun C => ¬Fintype.card P < 2*C.card), f C) + _ = _
  rw [Finset.sum_filter]
  rfl

end WeakPinned.Hierarchy.Depth

namespace WeakPinned.Hierarchy.Depth
open MeasureTheory
variable {P : Type u6} [Fintype P] [DecidableEq P]
variable (d : Depth P)
lemma integrable_sumCells (hn : 2 ≤ Fintype.card P) (f : Finset P → ℝ)
    (hf : ∀ C, C.card ≤ 1 → f C = 0) : Integrable (d.sumCells f) := by
  change Integrable (fun r => d.sumCells f r)
  simp_rw [d.sumCells_count]
  apply integrable_finsetSum
  intro C _
  by_cases hC : 2 ≤ C.card
  · exact (d.integrable_count hn C hC).mul_const _
  · simp only [hf C (by omega),mul_zero]
    exact integrable_zero _ _ _
end WeakPinned.Hierarchy.Depth

end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQW_WeakPinned.GlobalOverlap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u1 u2 u3

section
noncomputable section
open NumberField
open scoped BigOperators
noncomputable section
open MeasureTheory
open scoped Topology
noncomputable section
open MeasureTheory
open scoped Topology ENNReal
noncomputable section
open MeasureTheory NumberField
open scoped BigOperators
noncomputable section
open scoped BigOperators
open MeasureTheory

namespace WeakPinned.Grid
open MeasureTheory

lemma truncated_error_integrable {z w : ℂ} (hne : z ≠ w) (t : ℝ) :
    Integrable (fun ω => max (|error ω z w|-t) 0) fullLaw :=
  (((error_integrable_full hne).abs.sub (integrable_const t)).sup (integrable_zero _ _ _))

lemma truncated_error_mean {z w : ℂ} (hne : z ≠ w) {t : ℝ} (ht : 0 ≤ t) :
    (∫ ω, max (|error ω z w|-t) 0 ∂fullLaw) ≤ 4*Real.exp (-t) := by
  have hm : Measurable (fun ω => max (|error ω z w|-t) 0) :=
    ((measurable_error hne).abs.sub_const t).max measurable_const
  have hn (ω : FullSample) : 0 ≤ max (|error ω z w|-t) 0 := le_max_right _ _
  have hi := truncated_error_integrable hne t
  have he : IntegrableOn (fun u : ℝ => (4*Real.exp (-t))*Real.exp (-u)) (Set.Ioi 0) volume := by
    simpa only [neg_one_mul, IntegrableOn] using
      (integrableOn_exp_mul_Ioi (by norm_num : (-1:ℝ)<0) 0).const_mul (4*Real.exp (-t))
  have hb : (∫⁻ ω, ENNReal.ofReal (max (|error ω z w|-t) 0) ∂fullLaw) ≤
      ENNReal.ofReal (4*Real.exp (-t)) := by
    rw [lintegral_eq_lintegral_meas_lt fullLaw
      (Filter.Eventually.of_forall hn) hm.aemeasurable]
    calc
      _ ≤ ∫⁻ u : ℝ in Set.Ioi 0, ENNReal.ofReal ((4*Real.exp (-t))*Real.exp (-u)) := by
        apply lintegral_mono_ae
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
        have hu0 : 0 < u := hu
        have hs : {ω : FullSample | u < max (|error ω z w|-t) 0} =
            {ω : FullSample | u+t < |error ω z w|} := by
          ext ω
          simp only [Set.mem_ofPred_eq,lt_max_iff]
          constructor
          · rintro (h | h) <;> linarith
          · intro h; exact Or.inl (by linarith)
        rw [hs, ← ENNReal.ofReal_toReal (measure_ne_top fullLaw _)]
        have hh := abs_error_tail_full hne (add_nonneg hu.le ht)
        apply ENNReal.ofReal_le_ofReal
        calc
          _ ≤ 4*Real.exp (-(u+t)) := hh
          _ = _ := by rw [neg_add,Real.exp_add]; ring
      _ = ENNReal.ofReal (4*Real.exp (-t)) := by
        rw [← ofReal_integral_eq_lintegral_ofReal he (by filter_upwards with u; positivity)]
        congr 1
        rw [integral_const_mul]
        have hz := integral_exp_mul_Ioi (by norm_num : (-1:ℝ)<0) (0:ℝ)
        simp only [neg_one_mul,mul_zero,Real.exp_zero,neg_div_neg_eq,div_one] at hz
        rw [hz,mul_one]
  rw [← ofReal_integral_eq_lintegral_ofReal hi (Filter.Eventually.of_forall hn)] at hb
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hb

lemma truncated_sum_bound (a b H : ℝ) :
    max (|a+b|-H) 0 ≤ 2*max (|a|-H/2) 0 + 2*max (|b|-H/2) 0 := by
  apply max_le
  · have ht := abs_add_le a b
    have h₁ := le_max_left (|a|-H/2) 0
    have h₂ := le_max_left (|b|-H/2) 0
    have h₃ := le_max_right (|a|-H/2) 0
    have h₄ := le_max_right (|b|-H/2) 0
    linarith
  · positivity

lemma paired_error_mean {z₁ w₁ z₂ w₂ : ℂ} (h₁ : z₁ ≠ w₁) (h₂ : z₂ ≠ w₂)
    {H : ℝ} (hH : 0 ≤ H) :
    (∫ ω, max (|error ω z₁ w₁ + error ω z₂ w₂|-H) 0 ∂fullLaw) ≤
      16*Real.exp (-H/2) := by
  have hi : Integrable (fun ω => max (|error ω z₁ w₁ + error ω z₂ w₂|-H) 0) fullLaw := by
    exact Integrable.sup (((error_integrable_full h₁).add (error_integrable_full h₂)).abs.sub
      (integrable_const H)) (integrable_zero _ _ _)
  have hia := truncated_error_integrable h₁ (H/2)
  have hib := truncated_error_integrable h₂ (H/2)
  have hh := integral_mono hi ((hia.const_mul 2).add (hib.const_mul 2))
    (fun ω => truncated_sum_bound (error ω z₁ w₁) (error ω z₂ w₂) H)
  simp only [Pi.add_apply] at hh
  rw [integral_add (hia.const_mul 2) (hib.const_mul 2)] at hh
  simp only [integral_const_mul] at hh
  have hta := truncated_error_mean h₁ (div_nonneg hH (by norm_num : (0:ℝ)≤2))
  have htb := truncated_error_mean h₂ (div_nonneg hH (by norm_num : (0:ℝ)≤2))
  rw [neg_div'] at hta htb
  linarith

end WeakPinned.Grid

namespace WeakPinned.Global
open Hierarchy Variance SmallFiber
variable {P : Type u1} {I : Type u2} [Fintype P] [DecidableEq P] [Fintype I]
variable {K : Type u3} [Field K] [NumberField K]
variable (Z₁ Z₂ : P → K) (h₁ : Function.Injective Z₁) (h₂ : Function.Injective Z₂)
include h₁ h₂

lemma arch_fiber_defect (v : InfinitePlace K) (a b : P) (hab : a ≠ b) (t : K)
    (ht : (Z₁ a-Z₁ b)*(Z₂ a-Z₂ b)=t) :
    (fun ω => (arch Z₁ v ω).value a b+(arch Z₂ v ω).value a b+Real.log (v t)) =ᵐ[Grid.fullLaw]
      (fun ω => Grid.error ω (v.embedding (Z₁ a)) (v.embedding (Z₁ b))+
        Grid.error ω (v.embedding (Z₂ a)) (v.embedding (Z₂ b))) := by
  have he := Arithmetic.raw_fiber_identity v.val (Z₁ a-Z₁ b) (Z₂ a-Z₂ b)
    (sub_ne_zero.mpr (h₁.ne hab)) (sub_ne_zero.mpr (h₂.ne hab))
  rw [ht] at he
  change -Real.log (v (Z₁ a-Z₁ b)) + -Real.log (v (Z₂ a-Z₂ b)) = -Real.log (v t) at he
  filter_upwards [arch_value_ae Z₁ h₁ v hab,arch_value_ae Z₂ h₂ v hab] with ω hA hB
  rw [hA,hB]
  simp only [Grid.error,← map_sub,InfinitePlace.norm_embedding_eq]
  linarith

lemma arch_defect_mean (v : InfinitePlace K) (a b : P) (hab : a ≠ b) (t : K)
    (ht : (Z₁ a-Z₁ b)*(Z₂ a-Z₂ b)=t) (H : ℝ) (hH : 0 ≤ H) :
    (∫ ω, max (|(arch Z₁ v ω).value a b+(arch Z₂ v ω).value a b+Real.log (v t)|-H) 0 ∂Grid.fullLaw) ≤
      16*Real.exp (-H/2) := by
  have he := arch_fiber_defect Z₁ Z₂ h₁ h₂ v a b hab t ht
  have he' : (fun ω => max (|(arch Z₁ v ω).value a b+(arch Z₂ v ω).value a b+Real.log (v t)|-H) 0) =ᵐ[Grid.fullLaw]
      (fun ω => max (|Grid.error ω (v.embedding (Z₁ a)) (v.embedding (Z₁ b))+
        Grid.error ω (v.embedding (Z₂ a)) (v.embedding (Z₂ b))|-H) 0) := by
    filter_upwards [he] with ω hh
    rw [hh]
  rw [integral_congr_ae he']
  exact Grid.paired_error_mean (embedding_ne Z₁ h₁ v hab) (embedding_ne Z₂ h₂ v hab) hH

lemma arch_weighted_defect (v : InfinitePlace K) (w : I → ℝ) (p : I → P → ℝ)
    (x : I → P) (t : I → K) (hw : ∀ i, 0 ≤ w i) (hW : ∑ i, w i=1)
    (hp : ∀ i y, 0 ≤ p i y) (hp1 : ∀ i, ∑ y, p i y=1) (hx : ∀ i, p i (x i)=0)
    (ht : ∀ i y, p i y ≠ 0 → (Z₁ (x i)-Z₁ y)*(Z₂ (x i)-Z₂ y)=t i)
    (H : ℝ) (hH : 0 ≤ H) :
    (∫ ω, ∑ i, w i*∑ y, p i y*max (|(arch Z₁ v ω).value (x i) y+
      (arch Z₂ v ω).value (x i) y+Real.log (v (t i))|-H) 0 ∂Grid.fullLaw) ≤ 16*Real.exp (-H/2) := by
  have hi (i : I) (y : P) : Integrable (fun ω => max (|(arch Z₁ v ω).value (x i) y+
      (arch Z₂ v ω).value (x i) y+Real.log (v (t i))|-H) 0) Grid.fullLaw :=
    ((((arch_integrable Z₁ h₁ v _ _).add (arch_integrable Z₂ h₂ v _ _)).add (integrable_const _)).abs.sub
      (integrable_const H)).sup (integrable_zero _ _ _)
  rw [integral_finsetSum _ (fun i _ => (integrable_finsetSum (s:=Finset.univ)
    (fun y _ => (hi i y).const_mul _)).const_mul _)]
  simp_rw [integral_const_mul,integral_finsetSum _ (fun y _ => (hi _ y).const_mul _),integral_const_mul]
  calc
    _ ≤ ∑ i, w i * ∑ y, p i y*(16*Real.exp (-H/2)) := by
      apply Finset.sum_le_sum
      intro i _
      apply mul_le_mul_of_nonneg_left _ (hw i)
      apply Finset.sum_le_sum
      intro y _
      by_cases hy : p i y=0
      · simp [hy]
      · have hxy : x i ≠ y := by intro he; rw [← he,hx i] at hy; exact hy rfl
        exact mul_le_mul_of_nonneg_left (arch_defect_mean Z₁ Z₂ h₁ h₂ v _ _ hxy _ (ht i y hy) H hH) (hp i y)
    _ = _ := by simp only [← Finset.sum_mul,hp1,one_mul,hW]

omit h₁ h₂ in
lemma finite_zero_outside {Z : P → K} (hZ : Function.Injective Z) (v : FinitePlace K)
    (hv : v ∉ badPlaces Z hZ) : ∀ a b, (finite Z hZ v).value a b=0 := by
  intro a b
  by_cases hab : a=b
  · simp [finite,hab]
  · have hunit : v (Z a-Z b)=1 := by
      by_contra h
      exact hv ((badPlaces_mem Z hZ v).mpr ⟨a,b,hab,h⟩)
    simp [finite,hab,hunit]

omit h₁ h₂ in
lemma finite_mass_zero {Z : P → K} (hZ : Function.Injective Z) (hn : 2 ≤ Fintype.card P)
    (v : FinitePlace K) (hv : v ∉ badPlaces Z hZ) (C : Finset P) : (finite Z hZ v).mass C=0 := by
  have hz := (finite Z hZ v).zero_values hn (finite_zero_outside hZ v hv)
  by_cases hC : C.card ≤ 1
  · exact (finite Z hZ v).mass_singleton C hC
  · obtain ⟨a,ha,b,hb,hab⟩ := Finset.one_lt_card.mp (by omega : 1<C.card)
    have hl := (finite Z hZ v).mass_le_overlap hn C a b hab ha hb
    rw [hz.2.2 a b hab] at hl
    exact le_antisymm hl ((finite Z hZ v).mass_nonneg C)

omit h₁ h₂ in
lemma sum_finite_mass {Z : P → K} (hZ : Function.Injective Z) (hn : 2 ≤ Fintype.card P)
    (V : Finset (FinitePlace K)) (hV : badPlaces Z hZ ⊆ V) (C : Finset P) :
    (∑ v ∈ V, (finite Z hZ v).mass C) = ∑ v ∈ badPlaces Z hZ, (finite Z hZ v).mass C := by
  symm
  exact Finset.sum_subset hV (fun v _ hv => finite_mass_zero hZ hn v hv C)

omit h₁ h₂ in
lemma sum_finite_potential {Z : P → K} (hZ : Function.Injective Z) (hn : 2 ≤ Fintype.card P)
    (V : Finset (FinitePlace K)) (hV : badPlaces Z hZ ⊆ V) (a : P) :
    (∑ v ∈ V, (finite Z hZ v).potential a) = ∑ v ∈ badPlaces Z hZ, (finite Z hZ v).potential a := by
  symm
  exact Finset.sum_subset hV (fun v _ hv =>
    ((finite Z hZ v).zero_values hn (finite_zero_outside hZ v hv)).2.1 a)

omit h₁ h₂ in
lemma placeAverage_mono (V : Finset (FinitePlace K)) {A A' : InfinitePlace K → ℝ} {F F' : FinitePlace K → ℝ}
    (hA : ∀ v, A v ≤ A' v) (hF : ∀ v ∈ V, F v ≤ F' v) : placeAverage V A F ≤ placeAverage V A' F' := by
  apply add_le_add
  · exact Finset.sum_le_sum (fun v _ => mul_le_mul_of_nonneg_left (hA v) (Arithmetic.archWeight_nonneg v))
  · exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum hF) (by positivity)

omit h₁ h₂ in
lemma placeAverage_arch_const (V : Finset (FinitePlace K)) (a : ℝ) :
    placeAverage V (fun _ => a) (fun _ => 0) = a := by
  simp only [placeAverage,Finset.sum_const_zero,mul_zero,add_zero,← Finset.sum_mul,Arithmetic.sum_archWeight,one_mul]

end WeakPinned.Global

end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQW_WeakPinned.ExtremalCore
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u1 u2 u3 u4 u5 u6

section
noncomputable section
open NumberField
open scoped BigOperators
noncomputable section
open MeasureTheory
open scoped Topology
noncomputable section
open MeasureTheory
open scoped Topology ENNReal
noncomputable section
open MeasureTheory NumberField
open scoped BigOperators
noncomputable section
open scoped BigOperators
open MeasureTheory
noncomputable section
open Filter
open scoped Topology

/- Finite extremal core construction. The truncated-fiber score gives the same
   core as pruning while avoiding an arbitrary pruning order. It uses the
   original fibers without a generic-position hypothesis. -/

noncomputable section
open scoped BigOperators
namespace WeakPinned.Core
variable {V : Type u1} {I : Type u2} [Fintype V] [Fintype I] [DecidableEq V]

namespace Fibers
variable (G : Fibers V I)

omit [Fintype V] [Fintype I] in
lemma edge_no_loop (K : ℝ) (C : Finset V) (v : V) : ¬G.edge K C v v := by
  rintro ⟨e,_,he,hv⟩
  exact G.no_loop e (he ▸ (Finset.mem_inter.mp hv).1)

end Fibers
end WeakPinned.Core

end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQW_WeakPinned.IncomingFibers
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u1 u2 u3 u4 u5 u6 u7 u8

section
noncomputable section
open NumberField
open scoped BigOperators
noncomputable section
open MeasureTheory
open scoped Topology
noncomputable section
open MeasureTheory
open scoped Topology ENNReal
noncomputable section
open MeasureTheory NumberField
open scoped BigOperators
noncomputable section
open scoped BigOperators
open MeasureTheory
noncomputable section
open Filter
open scoped Topology
noncomputable section
open scoped BigOperators

namespace WeakPinned.Core.Fibers
open scoped BigOperators
open Variance
variable {V : Type u1} {I : Type u2} [Fintype V] [Fintype I] [DecidableEq V]
variable (G : Fibers V I)

omit [Fintype I] in
lemma edgeLaw_nonneg (x y : V) : 0 ≤ G.edgeLaw x y := by
  unfold edgeLaw edgeCount
  split_ifs <;> positivity

omit [Fintype I] in
lemma edgeLaw_diag (x : V) : G.edgeLaw x x=0 := by
  have hh : (x,x) ∉ G.edges := by
    intro h
    exact G.edge_no_loop (-1) Finset.univ x (Finset.mem_filter.mp h).2
  simp [edgeLaw,hh]

omit [Fintype I] in
lemma fiberWeight_prob (e : I) (y : V) :
    G.fiberWeight e*prob (G.targets e) y = if y ∈ G.targets e then 1/G.edgeCount else 0 := by
  by_cases hy : y ∈ G.targets e
  · have hk : ((G.targets e).card : ℝ) ≠ 0 := by
      exact_mod_cast (Finset.card_ne_zero.mpr ⟨y,hy⟩)
    simp only [fiberWeight,prob,ite_eq_left hy]
    field_simp
  · simp [prob,hy]

lemma sampling_fiber (x y : V) :
    (∑ e, if G.source e=x then G.fiberWeight e * prob (G.targets e) y else 0) =
      G.edgeLaw x y := by
  have he := G.edge_indicator (-1) Finset.univ x y
  simp only [G.active_univ_neg_one,true_and,Finset.mem_inter,Finset.mem_univ,and_true] at he
  have hh : (∑ e, if G.source e=x then G.fiberWeight e * prob (G.targets e) y else 0) =
      (∑ e, if G.source e=x ∧ y ∈ G.targets e then (1:ℝ) else 0)/G.edgeCount := by
    simp only [Finset.sum_div,G.fiberWeight_prob]
    apply Finset.sum_congr rfl
    intro e _
    by_cases hs : G.source e=x <;> by_cases hy : y ∈ G.targets e <;> simp [hs,hy]
  rw [hh,he]
  by_cases he : G.edge (-1) Finset.univ x y <;> simp [edgeLaw,edges,edgeSet,he]

lemma fiber_marginal (y : V) :
    (∑ e, G.fiberWeight e * prob (G.targets e) y) = ∑ x, G.edgeLaw x y := by
  simp_rw [← G.sampling_fiber]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e _
  simp

omit [Fintype I] in
lemma incoming_marginal (y : V) : ∑ x, G.edgeLaw x y=G.incomingWeight y := by
  simp only [edgeLaw,incomingWeight,incoming,← Finset.sum_filter,Finset.sum_const,nsmul_eq_mul]
  simp only [mul_one_div]

omit [Fintype I] in
lemma sampling_incoming (x y : V) :
    G.incomingWeight y*prob (G.incoming y) x=G.edgeLaw x y := by
  by_cases he : (x,y) ∈ G.edges
  · have hm : x ∈ G.incoming y := by simp [incoming,he]
    have hk : ((G.incoming y).card : ℝ) ≠ 0 := by exact_mod_cast (Finset.card_ne_zero.mpr ⟨x,hm⟩)
    simp only [incomingWeight,prob,ite_eq_left hm,edgeLaw,ite_eq_left he]
    field_simp
  · have hm : x ∉ G.incoming y := by simp [incoming,he]
    simp [prob,hm,edgeLaw,he]

omit [Fintype I] in
lemma sum_edgeLaw (hG : 0 < G.edgeCount) : (∑ x, ∑ y, G.edgeLaw x y)=1 := by
  rw [← Fintype.sum_prod_type (f:=fun xy : V × V => G.edgeLaw xy.1 xy.2)]
  simp only [edgeLaw,← Finset.sum_filter,Finset.sum_const,nsmul_eq_mul]
  have he : Finset.univ.filter (fun xy : V × V => xy ∈ G.edges)=G.edges := by simp
  rw [he]
  change G.edgeCount*(1/G.edgeCount)=1
  field_simp

omit [Fintype I] in
lemma sum_incomingWeight (hG : 0 < G.edgeCount) : ∑ y, G.incomingWeight y=1 := by
  simp_rw [← G.incoming_marginal]
  rw [Finset.sum_comm,G.sum_edgeLaw hG]

lemma fiber_domination (B : ℝ) (hdom : ∀ x y, G.edgeLaw x y ≤ B*pairProb Finset.univ x y)
    (hn : 2 ≤ Fintype.card V) (y : V) :
    (∑ e, G.fiberWeight e*prob (G.targets e) y) ≤ B*prob Finset.univ y := by
  rw [G.fiber_marginal]
  have hh := Finset.sum_le_sum (s:=Finset.univ) (fun x _ => hdom x y)
  simpa only [← Finset.mul_sum,pairProb_symm _ _ y,sum_pairProb Finset.univ (by simpa using hn)] using hh

omit [Fintype I] in
lemma incoming_domination (B : ℝ) (hdom : ∀ x y, G.edgeLaw x y ≤ B*pairProb Finset.univ x y)
    (hn : 2 ≤ Fintype.card V) (x : V) :
    (∑ y, G.incomingWeight y*prob (G.incoming y) x) ≤ B*prob Finset.univ x := by
  simp_rw [G.sampling_incoming]
  have hh := Finset.sum_le_sum (s:=Finset.univ) (fun y _ => hdom x y)
  simpa only [← Finset.mul_sum,sum_pairProb Finset.univ (by simpa using hn)] using hh

omit [Fintype I] in
/-- The exact bound on omitted small incoming degrees, not just a formal
    little-o assertion. -/
lemma small_incoming_mass (T : ℝ) (hT : 0 ≤ T) :
    (∑ y, if ((G.incoming y).card : ℝ)<T then G.incomingWeight y else 0) ≤
      (Fintype.card V : ℝ)*T/G.edgeCount := by
  have hn : 0 ≤ G.edgeCount := by unfold edgeCount; positivity
  have hh : ∀ y, (if ((G.incoming y).card : ℝ)<T then G.incomingWeight y else 0) ≤ T/G.edgeCount := by
    intro y
    split_ifs with hy
    · exact div_le_div_of_nonneg_right hy.le hn
    · exact div_nonneg hT hn
  have hs := Finset.sum_le_sum (s:=Finset.univ) (fun y _ => hh y)
  simpa only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_div_assoc] using hs

end WeakPinned.Core.Fibers

end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQW_WeakPinned.ArithmeticGraphs
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u1 u2 u3 u4 u5 u6 u7 u8 u9 u10 u11 u12
universe u13 u14 u15

section
noncomputable section
open NumberField
open scoped BigOperators
noncomputable section
open MeasureTheory
open scoped Topology
noncomputable section
open MeasureTheory
open scoped Topology ENNReal
noncomputable section
open MeasureTheory NumberField
open scoped BigOperators
noncomputable section
open scoped BigOperators
open MeasureTheory
noncomputable section
open Filter
open scoped Topology
noncomputable section
open scoped BigOperators

namespace WeakPinned
open scoped BigOperators
open Variance
variable {V : Type u1} {I : Type u2} [Fintype V] [Fintype I] [DecidableEq V]
variable {G : Core.Fibers V I} {θ γ c η : ℝ}

lemma PreparedGraph.edgeCount_pos (h : PreparedGraph V I G θ γ c η) (hη : η<θ) : 0<G.edgeCount := by
  have hnR : (2:ℝ)≤Fintype.card V := by exact_mod_cast h.card_ge
  have hp : 0<(θ-η)*(Fintype.card V : ℝ)*((Fintype.card V : ℝ)-1) :=
    mul_pos (mul_pos (sub_pos.mpr hη) (by linarith)) (by linarith)
  exact hp.trans_le h.lower

lemma PreparedGraph.edge_domination (h : PreparedGraph V I G θ γ c η) (hη : η<θ) (x y : V) :
    G.edgeLaw x y ≤ (1/(θ-η))*pairProb Finset.univ x y := by
  have hnR : (2:ℝ)≤Fintype.card V := by exact_mod_cast h.card_ge
  have hden : 0<(Fintype.card V : ℝ)*((Fintype.card V : ℝ)-1) := mul_pos (by linarith) (by linarith)
  by_cases hxy : x=y
  · subst y; simp [G.edgeLaw_diag,pairProb]
  · have he : pairProb Finset.univ x y=1/((Fintype.card V : ℝ)*((Fintype.card V : ℝ)-1)) := by simp [pairProb,hxy]
    rw [he]
    unfold Core.Fibers.edgeLaw
    split_ifs
    · have hh := one_div_le_one_div_of_le (mul_pos (sub_pos.mpr hη) hden) (by simpa only [mul_assoc] using h.lower)
      calc
        1 / G.edgeCount ≤ 1 / ((θ-η)*((Fintype.card V : ℝ)*((Fintype.card V : ℝ)-1))) := hh
        _ = _ := by rw [one_div_mul_one_div]
    · positivity

end WeakPinned

namespace WeakPinned.Core.Fibers
open scoped BigOperators
open Variance SmallFiber
variable {V : Type u3} {I : Type u4} [Fintype V] [Fintype I] [DecidableEq V]
variable (G : Fibers V I)

lemma qCell_eq (C : Finset V) : G.qCell C = SmallFiber.edgeCell G.fiberWeight (fun e => prob (G.targets e)) G.source C := by
  unfold qCell SmallFiber.edgeCell SmallFiber.edgeLaw
  simp_rw [G.sampling_fiber]

omit [Fintype I] in
lemma qCell_bound {B : ℝ} (hdom : ∀ x y, G.edgeLaw x y ≤ B*pairProb Finset.univ x y) (C : Finset V) :
    G.qCell C ≤ B*pairCell Finset.univ C := by
  unfold qCell pairCell
  simp only [Finset.mul_sum]
  exact Finset.sum_le_sum (fun x _ => Finset.sum_le_sum (fun y _ => hdom x y))

end WeakPinned.Core.Fibers

namespace WeakPinned.Variance
open scoped BigOperators
variable {V : Type u5} [Fintype V] [DecidableEq V]

lemma weighted_pair (m : Finset V → ℝ) (q : V → V → ℝ) :
    weightedIntegral m (fun C => ∑ x ∈ C, ∑ y ∈ C, q x y)=
      ∑ x, ∑ y, q x y*weightedOverlap m x y := by
  have hc (C : Finset V) : (∑ x ∈ C, ∑ y ∈ C, q x y)=
      ∑ x, ∑ y, q x y*(if x∈C ∧ y∈C then (1:ℝ) else 0) := by
    simp only [mul_ite,mul_one,mul_zero,ite_and,Finset.sum_ite_irrel,Finset.sum_const_zero]
    simp
  simp only [weightedIntegral,hc,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y _
  simp only [weightedOverlap,weightedIntegral,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro C _
  ring

lemma weighted_additive (m : Finset V → ℝ) (b : ℝ) (S : V → ℝ)
    (hL : ∀ x y, x≠y → weightedOverlap m x y=b+S x+S y)
    (q : V → V → ℝ) (hdiag : ∀ x, q x x=0) (h1 : (∑ x, ∑ y, q x y)=1) :
    weightedIntegral m (fun C => ∑ x ∈ C, ∑ y ∈ C, q x y)=
      b+∑ x, ((∑ y, q x y)+(∑ y, q y x))*S x := by
  rw [weighted_pair]
  have hp (x y : V) : q x y*weightedOverlap m x y=q x y*(b+S x+S y) := by
    by_cases hxy : x=y
    · subst y; simp [hdiag]
    · rw [hL x y hxy]
  simp_rw [hp,mul_add,Finset.sum_add_distrib]
  have hb : (∑ x, ∑ y, q x y*b)=b := by
    simp only [← Finset.sum_mul,h1,one_mul]
  rw [hb]
  simp only [← Finset.sum_mul,add_mul,Finset.sum_add_distrib]
  rw [Finset.sum_comm (f:=fun x y => q x y*S y)]
  simp only [← Finset.sum_mul]
  ring

lemma uniform_additive (m : Finset V → ℝ) (b : ℝ) (S : V → ℝ)
    (hL : ∀ x y, x≠y → weightedOverlap m x y=b+S x+S y) (hn : 2≤Fintype.card V) :
    weightedIntegral m (pairCell Finset.univ)=b+2*(∑ x, prob Finset.univ x*S x) := by
  have hsum : (∑ x : V, ∑ y : V, pairProb Finset.univ x y)=1 := by
    simp_rw [sum_pairProb Finset.univ (by simpa using hn)]
    exact sum_prob Finset.univ (Finset.card_pos.mp (by simpa using (show 0<Fintype.card V by omega)))
  have hh := weighted_additive m b S hL (pairProb Finset.univ) (by intro x; simp [pairProb]) hsum
  change weightedIntegral m (fun C => ∑ x ∈ C, ∑ y ∈ C, pairProb Finset.univ x y) = _
  rw [hh]
  simp_rw [pairProb_symm Finset.univ _ _,sum_pairProb Finset.univ (by simpa using hn)]
  simp only [Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro x _
  ring

end WeakPinned.Variance

namespace WeakPinned
open scoped BigOperators
open Variance SmallFiber Global
variable {V : Type u8} {I : Type u9} [Fintype V] [Fintype I] [DecidableEq V]
variable {G : Core.Fibers V I} {θ γ c η : ℝ}
variable {K : Type u10} [Field K] [NumberField K]
variable (Z₁ Z₂ : V → K) (h₁ : Function.Injective Z₁) (h₂ : Function.Injective Z₂)

lemma overlapScale_nonneg : 0 ≤ overlapScale Z₁ Z₂ h₁ h₂ := by
  exact Finset.sum_nonneg (fun C _ => mul_nonneg (totalMass_nonneg Z₁ Z₂ h₁ h₂ C) (pairCell_nonneg _ _))

lemma potentialScale_nonneg : 0 ≤ potentialScale Z₁ Z₂ h₁ h₂ := by
  apply Finset.sum_nonneg
  intro x _
  apply mul_nonneg _ (totalPotential_nonneg Z₁ Z₂ h₁ h₂ x)
  simp only [prob,Finset.mem_univ,ite_true]
  positivity

end WeakPinned

namespace WeakPinned.Variance
open scoped BigOperators
variable {P : Type u11} {I : Type u12} [Fintype P] [DecidableEq P] [Fintype I]
lemma varianceCell_nonneg (w : I → ℝ) (B : I → Finset P) (T : ℝ)
    (hw : ∀ i, 0≤w i) (C : Finset P) : 0≤varianceCell w B T C := by
  unfold varianceCell
  split_ifs
  · exact Finset.sum_nonneg (fun i _ => mul_nonneg (hw i) (sq_nonneg _))
  · apply mul_nonneg (by norm_num)
    apply Finset.sum_nonneg
    intro i _
    apply mul_nonneg (hw i)
    split_ifs <;> positivity

end WeakPinned.Variance

end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQW_WeakPinned.OverlapRates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u1 u2 u3 u4 u5 u6 u7 u8 u9 u10

section
noncomputable section
open NumberField
open scoped BigOperators
noncomputable section
open MeasureTheory
open scoped Topology
noncomputable section
open MeasureTheory
open scoped Topology ENNReal
noncomputable section
open MeasureTheory NumberField
open scoped BigOperators
noncomputable section
open scoped BigOperators
open MeasureTheory
noncomputable section
open Filter
open scoped Topology
noncomputable section
open scoped BigOperators
noncomputable section
open Filter
open scoped Topology

namespace WeakPinned.Core.Fibers
open scoped BigOperators
open Variance
variable {V : Type u4} {I : Type u5} [Fintype V] [Fintype I] [DecidableEq V]
variable (G : Fibers V I)

omit [Fintype I] in
lemma retainedWeight_nonneg (T : ℝ) (y : V) : 0≤G.retainedWeight T y := by
  unfold retainedWeight incomingWeight edgeCount
  split_ifs <;> positivity

omit [Fintype I] in
lemma retainedWeight_le (T : ℝ) (y : V) : G.retainedWeight T y≤G.incomingWeight y := by
  unfold retainedWeight
  split_ifs
  · exact le_rfl
  · unfold incomingWeight edgeCount; positivity

omit [Fintype I] in
lemma sum_retainedWeight (T : ℝ) (hG : 0<G.edgeCount) : (∑ y, G.retainedWeight T y)≤1 := by
  rw [← G.sum_incomingWeight hG]
  exact Finset.sum_le_sum (fun y _ => G.retainedWeight_le T y)

omit [Fintype I] in
lemma retainedSet_size (T : ℝ) (hT : T≤Fintype.card V) (y : V) : T≤((G.retainedSet T y).card:ℝ) := by
  unfold retainedSet
  split_ifs with h
  · exact h
  · simpa using hT

omit [Fintype I] in
lemma retained_domination (T M : ℝ) (hdom : ∀ x y, G.edgeLaw x y≤M*pairProb Finset.univ x y)
    (hn : 2≤Fintype.card V) (x : V) :
    (∑ y, G.retainedWeight T y*prob (G.retainedSet T y) x)≤M*prob Finset.univ x := by
  refine le_trans (Finset.sum_le_sum (fun y _ => ?_)) (G.incoming_domination M hdom hn x)
  unfold retainedWeight retainedSet
  split_ifs
  · exact le_rfl
  · simp only [zero_mul]
    unfold incomingWeight edgeCount prob
    split_ifs <;> positivity
end WeakPinned.Core.Fibers

namespace WeakPinned
open Filter Variance Global
open scoped Topology BigOperators
variable {V : ℕ → Type u6} {I : ℕ → Type u7} {K : ℕ → Type u8} [∀ j, Fintype (V j)] [∀ j, Fintype (I j)] [∀ j, DecidableEq (V j)]
  [∀ j, Field (K j)] [∀ j, NumberField (K j)]
variable (G : ∀ j, Core.Fibers (V j) (I j)) (θ γ c : ℝ) (η : ℕ → ℝ)
  (Z₁ Z₂ : ∀ j, V j → K j) (h₁ : ∀ j, Function.Injective (Z₁ j)) (h₂ : ∀ j, Function.Injective (Z₂ j))

lemma PreparedGraph.uniform_domination {V : Type u9} {I : Type u10} [Fintype V] [Fintype I] [DecidableEq V]
    {G : Core.Fibers V I} {θ γ c η : ℝ} (h : PreparedGraph V I G θ γ c η) (hθ : 0<θ)
    (hη : η≤θ/2) (x y : V) : G.edgeLaw x y≤(2/θ)*pairProb Finset.univ x y := by
  have hh : η<θ := by linarith
  refine (h.edge_domination hh x y).trans (mul_le_mul_of_nonneg_right ?_ (by
    unfold pairProb
    split_ifs
    · have hn : (2:ℝ)≤Fintype.card V := by exact_mod_cast h.card_ge
      simp only [Finset.card_univ]
      exact div_nonneg (by norm_num) (mul_nonneg (by positivity) (by linarith))
    · exact le_rfl))
  apply (div_le_div_iff₀ (by linarith : 0<θ-η) hθ).mpr
  linarith

end WeakPinned

end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQW_WeakPinned.MinPotentials
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u1 u2 u3 u4 u5 u6 u7 u8 u9 u10

section
noncomputable section
open NumberField
open scoped BigOperators
noncomputable section
open MeasureTheory
open scoped Topology
noncomputable section
open MeasureTheory
open scoped Topology ENNReal
noncomputable section
open MeasureTheory NumberField
open scoped BigOperators
noncomputable section
open scoped BigOperators
open MeasureTheory
noncomputable section
open Filter
open scoped Topology
noncomputable section
open scoped BigOperators
noncomputable section
open Filter
open scoped Topology

namespace WeakPinned.Variance
open scoped BigOperators
variable {P : Type u1} {I : Type u2} [Fintype P] [DecidableEq P] [Fintype I]

/-- The giant-complement second moment estimate needed to compare W and W₂.
The linear error, unlike an absolute singleton error, can be integrated. -/
lemma cell_second_moment (w : I → ℝ) (B : I → Finset P) (T M κ : ℝ)
    (hw : ∀ i, 0≤w i) (hW : (∑ i, w i)≤1) (hT : 1≤T) (hκ : 0≤κ)
    (hk : ∀ i, 2/((B i).card:ℝ)≤κ)
    (hdom : ∀ x, (∑ i, w i*prob (B i) x)≤M*prob Finset.univ x) (C : Finset P) :
    (∑ i, w i*(cellProb (B i) C)^2) ≤
      2*varianceCell w B T C + 4*pairCell Finset.univ C + κ*M*cellProb Finset.univ C := by
  have hmean := mean_cell_bound w B C M hdom
  have hm : 0≤M*cellProb Finset.univ C := (Finset.sum_nonneg (fun i _ => mul_nonneg (hw i) (cellProb_nonneg _ _))).trans hmean
  unfold varianceCell
  split_ifs with hlarge
  · have hmC : 2≤C.card := by have : (1:ℝ)<C.card := hT.trans_lt hlarge; exact_mod_cast this
    have hcomp := (uniform_pair_comparison C hmC).1
    have hb : (∑ i, w i*(cellProb Finset.univ C)^2) ≤ (cellProb Finset.univ C)^2 := by
      rw [← Finset.sum_mul]
      nlinarith [sq_nonneg (cellProb Finset.univ C)]
    have hh : (∑ i, w i*(cellProb (B i) C)^2) ≤
        2*(∑ i, w i*(cellProb (B i) C-cellProb Finset.univ C)^2) +
        2*(∑ i, w i*(cellProb Finset.univ C)^2) := by
      simp only [Finset.mul_sum,← Finset.sum_add_distrib]
      apply Finset.sum_le_sum
      intro i _
      have h := mul_le_mul_of_nonneg_left (show (cellProb (B i) C)^2 ≤
        2*(cellProb (B i) C-cellProb Finset.univ C)^2+2*(cellProb Finset.univ C)^2 by
          nlinarith [sq_nonneg (cellProb (B i) C-2*cellProb Finset.univ C)]) (hw i)
      nlinarith
    nlinarith [mul_nonneg hκ hm]
  · have hh : (∑ i, w i*(cellProb (B i) C)^2) ≤
        (∑ i, w i*(if 2/((B i).card:ℝ)≤cellProb (B i) C then (cellProb (B i) C)^2 else 0)) +
        κ*(∑ i, w i*cellProb (B i) C) := by
      simp only [Finset.mul_sum,← Finset.sum_add_distrib]
      apply Finset.sum_le_sum
      intro i _
      split_ifs with hi
      · nlinarith [mul_nonneg hκ (mul_nonneg (hw i) (cellProb_nonneg (B i) C))]
      · have hp : cellProb (B i) C≤κ := (le_of_lt (lt_of_not_ge hi)).trans (hk i)
        have h := mul_le_mul_of_nonneg_left hp (mul_nonneg (hw i) (cellProb_nonneg (B i) C))
        nlinarith
    have hκmean := mul_le_mul_of_nonneg_left hmean hκ
    nlinarith [pairCell_nonneg Finset.univ C]

end WeakPinned.Variance

namespace WeakPinned.Hierarchy.Depth
open MeasureTheory
open scoped BigOperators
variable {P : Type u3} [Fintype P] [DecidableEq P] (d : Depth P)

lemma mem_giant_iff_cell (r : ℝ) (x : P) :
    x ∈ d.giant r ↔ Fintype.card P < 2*(d.cell r x).card := by
  constructor
  · intro hx
    obtain ⟨C,hC,hx⟩ := Finset.mem_biUnion.mp hx
    have hc := (d.mem_giants r C).mp hC
    simpa only [d.cell_of_mem hc.1 hx] using hc.2
  · intro hx
    have hc : d.cell r x ∈ d.giants r := (d.mem_giants r _).mpr ⟨d.cell_mem_cells _ _,hx⟩
    rw [d.giant_eq hc]
    exact d.self_mem_cell r x

lemma mem_giant_exists (r : ℝ) (x : P) :
    x ∈ d.giant r ↔ ∃ C : Finset P, Fintype.card P < 2*C.card ∧ ∀ y ∈ C, d.share r x y := by
  rw [d.mem_giant_iff_cell]
  constructor
  · intro hc
    exact ⟨d.cell r x,hc,fun y hy => (d.mem_cell r x y).mp hy⟩
  · rintro ⟨C,hc,hs⟩
    have hsub : C ⊆ d.cell r x := fun y hy => (d.mem_cell r x y).mpr (hs y hy)
    have := Finset.card_le_card hsub
    omega

lemma mem_giant_mono {r t : ℝ} (htr : t ≤ r) {x : P} (hx : x ∈ d.giant r) : x ∈ d.giant t := by
  rw [d.mem_giant_iff_cell] at hx ⊢
  have := Finset.card_le_card (d.cell_mono htr x)
  omega

lemma isClosed_mem_giant (x : P) : IsClosed {r : ℝ | x ∈ d.giant r} := by
  simp_rw [d.mem_giant_exists,Set.ofPred_exists]
  apply isClosed_iUnion_of_finite
  intro C
  simp only [Set.ofPred_and]
  apply IsClosed.inter
  · by_cases h : Fintype.card P < 2*C.card <;> simp [h]
  · simp_rw [Set.ofPred_forall]
    apply isClosed_iInter
    intro y
    apply isClosed_iInter
    intro hy
    by_cases hxy : x=y
    · simp [share,hxy]
    · simp only [share,hxy,false_or]
      exact isClosed_le continuous_id continuous_const

lemma mem_giant_low (hn : 2 ≤ Fintype.card P) (x : P) : x ∈ d.giant (-d.radius) := by
  rw [d.mem_giant_iff_cell,d.cell_of_low le_rfl,Finset.card_univ]
  omega

lemma mem_giant_le_M (hn : 2 ≤ Fintype.card P) {r : ℝ} {x : P} (hx : x ∈ d.giant r) : r ≤ d.M := by
  obtain ⟨C,hC,_⟩ := Finset.mem_biUnion.mp hx
  exact (d.giants_cutoff hn r).mp ⟨C,hC⟩

lemma departure_cutoff (hn : 2 ≤ Fintype.card P) (x : P) (r : ℝ) :
    x ∈ d.giant r ↔ r ≤ d.departure x := by
  have hne : Set.Nonempty {t : ℝ | x ∈ d.giant t} := ⟨-d.radius,d.mem_giant_low hn x⟩
  have hbd : BddAbove {t : ℝ | x ∈ d.giant t} := ⟨d.M,fun t ht => d.mem_giant_le_M hn ht⟩
  exact ⟨fun hx => le_csSup hbd hx,fun hr => d.mem_giant_mono hr ((d.isClosed_mem_giant x).csSup_mem hne hbd)⟩

lemma departure_le_M (hn : 2 ≤ Fintype.card P) (x : P) : d.departure x ≤ d.M :=
  d.mem_giant_le_M hn ((d.departure_cutoff hn x _).mpr le_rfl)

lemma outside_departure (hn : 2 ≤ Fintype.card P) (x : P) :
    (fun r => d.outsideIndicator r x) = (Set.Ioc (d.departure x) d.M).indicator (fun _ => (1:ℝ)) := by
  funext r
  simp only [outsideIndicator,d.giants_cutoff hn,d.departure_cutoff hn,not_le,Set.indicator,Set.mem_Ioc]
  congr 1
  exact propext and_comm

lemma integral_one_Ioc {a b : ℝ} (hab : a ≤ b) :
    (∫ r : ℝ, (Set.Ioc a b).indicator (fun _ => (1:ℝ)) r)=b-a := by
  rw [integral_indicator measurableSet_Ioc,integral_const]
  simp [Measure.real,Real.volume_Ioc,ENNReal.toReal_ofReal (sub_nonneg.mpr hab)]

lemma potential_departure (hn : 2 ≤ Fintype.card P) (x : P) : d.potential x = d.M-d.departure x := by
  unfold potential
  rw [d.outside_departure hn x,integral_one_Ioc (d.departure_le_M hn x)]

lemma outside_product (hn : 2 ≤ Fintype.card P) (x y : P) :
    (fun r => d.outsideIndicator r x*d.outsideIndicator r y) =
      (Set.Ioc (max (d.departure x) (d.departure y)) d.M).indicator (fun _ => (1:ℝ)) := by
  funext r
  rw [congrFun (d.outside_departure hn x) r,congrFun (d.outside_departure hn y) r]
  simp only [Set.indicator,Set.mem_Ioc,max_lt_iff]
  split_ifs <;> simp_all

/-- Exact layer-cake identity, including the finite set of threshold ties. -/
lemma min_potential (hn : 2 ≤ Fintype.card P) (x y : P) :
    min (d.potential x) (d.potential y) = ∫ r, d.outsideIndicator r x*d.outsideIndicator r y := by
  rw [d.outside_product hn x y,integral_one_Ioc (max_le (d.departure_le_M hn x) (d.departure_le_M hn y)),
    d.potential_departure hn x,d.potential_departure hn y]
  exact min_sub_sub_left d.M (d.departure x) (d.departure y)

end WeakPinned.Hierarchy.Depth

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace WeakPinned.MinKernel
variable {P : Type u4} [Fintype P]

lemma integrable_step (a : ℝ) : Integrable (step a) := by
  rw [step,integrable_indicator_iff measurableSet_Ioc]
  exact integrableOn_const (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top)

lemma step_mul (a b : ℝ) : (fun r => step a r*step b r)=step (min a b) := by
  funext r
  simp only [step,Set.indicator,Set.mem_Ioc,le_min_iff]
  split_ifs <;> simp_all

lemma integral_step (a : ℝ) (ha : 0≤a) : (∫ r, step a r)=a := by
  rw [step,integral_indicator measurableSet_Ioc]
  simp [integral_const,Measure.real,Real.volume_Ioc,ENNReal.toReal_ofReal ha]

lemma tail_product (p a b : P → ℝ) :
    (fun r => tail p a r*tail p b r) = fun r => ∑ x, ∑ y, (p x*p y)*step (min (a x) (b y)) r := by
  funext r
  simp only [tail]
  rw [Finset.sum_mul]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro y _
  rw [← congrFun (step_mul (a x) (b y)) r]
  ring

lemma integrable_tail_product (p a b : P → ℝ) : Integrable (fun r => tail p a r*tail p b r) := by
  rw [tail_product]
  exact integrable_finsetSum _ fun x _ => integrable_finsetSum _ fun y _ =>
    (integrable_step _).const_mul _

lemma energy_integral (p a b : P → ℝ) (ha : ∀ x, 0≤a x) (hb : ∀ x, 0≤b x) :
    energy p a b = ∫ r, tail p a r*tail p b r := by
  rw [tail_product,integral_finsetSum _ (fun x _ => integrable_finsetSum _ fun y _ => (integrable_step _).const_mul _)]
  simp_rw [integral_finsetSum _ (fun y _ => (integrable_step _).const_mul _),integral_const_mul]
  simp only [integral_step _ (le_min (ha _) (hb _)),energy]

lemma energy_cross (p a b : P → ℝ) (ha : ∀ x, 0≤a x) (hb : ∀ x, 0≤b x) :
    2*energy p a b ≤ energy p a a+energy p b b := by
  rw [energy_integral p a b ha hb,energy_integral p a a ha ha,energy_integral p b b hb hb]
  rw [← integral_const_mul,← integral_add (integrable_tail_product p a a) (integrable_tail_product p b b)]
  apply integral_mono ((integrable_tail_product p a b).const_mul 2)
    ((integrable_tail_product p a a).add (integrable_tail_product p b b))
  intro r
  simp only [Pi.add_apply]
  nlinarith [sq_nonneg (tail p a r-tail p b r)]

lemma min_add_four (a b c d : ℝ) (ha : 0≤a) (hb : 0≤b) (hc : 0≤c) (hd : 0≤d) :
    min (a+b) (c+d) ≤ min a c+min a d+min b c+min b d := by
  simp only [min_def]
  split_ifs <;> linarith

lemma energy_sum (p a b : P → ℝ) (hp : ∀ x, 0≤p x) (ha : ∀ x, 0≤a x) (hb : ∀ x, 0≤b x) :
    energy p (a+b) (a+b) ≤ 2*(energy p a a+energy p b b) := by
  have hh : energy p (a+b) (a+b) ≤ energy p a a+energy p a b+energy p b a+energy p b b := by
    unfold energy
    simp only [← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro x _
    apply Finset.sum_le_sum
    intro y _
    have h := mul_le_mul_of_nonneg_left (min_add_four (a x) (b x) (a y) (b y) (ha x) (hb x) (ha y) (hb y))
      (mul_nonneg (hp x) (hp y))
    simpa only [Pi.add_apply,mul_add] using h
  nlinarith [energy_cross p a b ha hb,energy_cross p b a hb ha]
end WeakPinned.MinKernel

namespace WeakPinned.Hierarchy.Depth
open MeasureTheory
open scoped BigOperators
variable {P : Type u5} [Fintype P] [DecidableEq P]
variable (d : Depth P)

lemma integrable_outside_product (hn : 2 ≤ Fintype.card P) (x y : P) :
    Integrable (fun r => d.outsideIndicator r x*d.outsideIndicator r y) := by
  rw [d.outside_product hn x y,integrable_indicator_iff measurableSet_Ioc]
  exact integrableOn_const (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top)

lemma outsideMass_square (p : P → ℝ) (r : ℝ) :
    (d.outsideMass p r)^2 = ∑ x, ∑ y, p x*p y*(d.outsideIndicator r x*d.outsideIndicator r y) := by
  unfold outsideMass
  rw [pow_two,Finset.sum_mul]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro y _
  ring

lemma iid_min_potential (hn : 2 ≤ Fintype.card P) (p : P → ℝ) :
    MinKernel.energy p d.potential d.potential = ∫ r, (d.outsideMass p r)^2 := by
  simp only [d.outsideMass_square]
  rw [integral_finsetSum _ (fun x _ => integrable_finsetSum _ fun y _ => (d.integrable_outside_product hn x y).const_mul _)]
  simp_rw [integral_finsetSum _ (fun y _ => (d.integrable_outside_product hn _ y).const_mul _),integral_const_mul]
  simp only [MinKernel.energy,d.min_potential hn]

/-- The source min-potential upper bound before averaging places and grids. -/

theorem iid_min_two_potentials (d' : Depth P) (hn : 2 ≤ Fintype.card P)
    (p : P → ℝ) (hp : ∀ x, 0≤p x) :
    (∑ x, ∑ y, p x*p y*min (d.potential x+d'.potential x) (d.potential y+d'.potential y)) ≤
      2*((∫ r, (d.outsideMass p r)^2)+(∫ r, (d'.outsideMass p r)^2)) := by
  rw [← d.iid_min_potential hn p,← d'.iid_min_potential hn p]
  exact MinKernel.energy_sum p d.potential d'.potential hp d.potential_nonneg d'.potential_nonneg
end WeakPinned.Hierarchy.Depth

namespace WeakPinned.Hierarchy.Depth
open MeasureTheory Variance
open scoped BigOperators
variable {P : Type u6} {I : Type u7} [Fintype P] [DecidableEq P] [Fintype I]
variable (d : Depth P)

lemma outsideMass_prob (B : Finset P) {r : ℝ} {G : Finset P} (hG : G∈d.giants r) :
    d.outsideMass (prob B) r=cellProb B Gᶜ := by
  have hne : (d.giants r).Nonempty := ⟨G,hG⟩
  have he (x) : prob B x*d.outsideIndicator r x=if x∈Gᶜ then prob B x else 0 := by
    simp only [outsideIndicator,hne,d.giant_eq hG,true_and]
    by_cases hx : x∈G <;> simp [hx]
  simp only [outsideMass,he,Finset.sum_ite_mem,Finset.univ_inter,sum_prob_cell]

lemma outsideMass_zero (p : P → ℝ) {r : ℝ} (hG : ¬(d.giants r).Nonempty) : d.outsideMass p r=0 := by
  simp [outsideMass,outsideIndicator,hG]

lemma sumCells_nonneg (f : Finset P → ℝ) (hf : ∀ C, 0≤f C) (r : ℝ) : 0≤d.sumCells f r := by
  rw [d.sumCells_count]
  exact Finset.sum_nonneg (fun C _ => mul_nonneg (by unfold count; positivity) (hf C))

lemma complement_le_sumCells (f : Finset P → ℝ) (hf : ∀ C, 0≤f C) {r : ℝ} {G : Finset P}
    (hG : G∈d.giants r) : f Gᶜ≤d.sumCells f r := by
  have hs : d.giants r={G} := Finset.ext fun C => by
    simp only [Finset.mem_singleton]
    exact ⟨fun hC => d.giants_unique hC hG,fun h => h ▸ hG⟩
  rw [d.sumCells_split,hs,Finset.sum_singleton]
  exact le_add_of_nonneg_left (Finset.sum_nonneg (fun C _ => by split_ifs <;> simp_all only [le_refl]))

lemma outside_square_bound (w : I → ℝ) (B : I → Finset P) (T M κ : ℝ)
    (hw : ∀ i, 0≤w i) (hW : (∑ i, w i)≤1) (hT : 1≤T) (hκ : 0≤κ)
    (hk : ∀ i, 2/((B i).card:ℝ)≤κ)
    (hdom : ∀ x, (∑ i, w i*prob (B i) x)≤M*prob Finset.univ x) (r : ℝ) :
    (∑ i, w i*(d.outsideMass (prob (B i)) r)^2) ≤
      d.sumCells (fun C => 2*varianceCell w B T C+4*pairCell Finset.univ C) r +
      κ*M*d.outsideMass (prob Finset.univ) r := by
  have hf (C : Finset P) : 0≤2*varianceCell w B T C+4*pairCell Finset.univ C :=
    add_nonneg (mul_nonneg (by norm_num) (varianceCell_nonneg w B T hw C))
      (mul_nonneg (by norm_num) (pairCell_nonneg _ _))
  by_cases hg : (d.giants r).Nonempty
  · obtain ⟨G,hG⟩ := hg
    simp_rw [d.outsideMass_prob _ hG]
    exact (cell_second_moment w B T M κ hw hW hT hκ hk hdom Gᶜ).trans
      (add_le_add (d.complement_le_sumCells _ hf hG) le_rfl)
  · simp only [d.outsideMass_zero _ hg,zero_pow (by norm_num : 2≠0),mul_zero,Finset.sum_const_zero,add_zero]
    exact d.sumCells_nonneg _ hf r

lemma integrable_outsideMass_square (hn : 2≤Fintype.card P) (p : P → ℝ) :
    Integrable (fun r => (d.outsideMass p r)^2) := by
  simp only [d.outsideMass_square]
  exact integrable_finsetSum _ fun x _ => integrable_finsetSum _ fun y _ =>
    (d.integrable_outside_product hn x y).const_mul _

lemma integral_outsideMass (hn : 2≤Fintype.card P) (p : P → ℝ) :
    (∫ r, d.outsideMass p r)=∑ x, p x*d.potential x := by
  simp only [outsideMass]
  rw [integral_finsetSum _ (fun x _ => (d.integrable_outsideIndicator hn x).const_mul _)]
  simp only [integral_const_mul,potential]

/-- The integrable complement second moment estimate. All singleton terms
are charged to the finite potential, not integrated as constant errors. -/
theorem integrated_outside_square (hn : 2≤Fintype.card P)
    (w : I → ℝ) (B : I → Finset P) (T M κ : ℝ)
    (hw : ∀ i, 0≤w i) (hW : (∑ i, w i)≤1) (hT : 1≤T) (hκ : 0≤κ)
    (hB : ∀ i, 2≤(B i).card) (hk : ∀ i, 2/((B i).card:ℝ)≤κ)
    (hdom : ∀ x, (∑ i, w i*prob (B i) x)≤M*prob Finset.univ x) :
    (∑ i, w i*(∫ r, (d.outsideMass (prob (B i)) r)^2)) ≤
      2*weightedIntegral d.mass (varianceCell w B T) +
      4*weightedIntegral d.mass (pairCell Finset.univ) +
      κ*M*(∑ x, prob Finset.univ x*d.potential x) := by
  let f := fun C => 2*varianceCell w B T C+4*pairCell Finset.univ C
  have hf : ∀ C, C.card≤1 → f C=0 := by
    intro C hC
    simp [f,varianceCell_singleton w B T hT hB C hC,singleton_pairCell Finset.univ C hC]
  have hi₁ : Integrable (fun r => ∑ i, w i*(d.outsideMass (prob (B i)) r)^2) :=
    integrable_finsetSum _ (fun i _ => (d.integrable_outsideMass_square hn _).const_mul _)
  have hi₂ : Integrable (fun r => d.sumCells f r) := d.integrable_sumCells hn f hf
  have hi₃ : Integrable (fun r => κ*M*d.outsideMass (prob Finset.univ) r) :=
    (integrable_finsetSum _ (fun x _ => (d.integrable_outsideIndicator hn x).const_mul _)).const_mul _
  have hh := integral_mono hi₁ (hi₂.add hi₃) (d.outside_square_bound w B T M κ hw hW hT hκ hk hdom)
  simp only [Pi.add_apply] at hh
  rw [integral_finsetSum _ (fun i _ => (d.integrable_outsideMass_square hn _).const_mul _),
    integral_add hi₂ hi₃,integral_const_mul,d.integral_outsideMass hn _,d.integral_sumCells hn f hf] at hh
  try simp only [integral_const_mul] at hh
  have he : (∑ C, d.mass C*f C)=
      2*weightedIntegral d.mass (varianceCell w B T)+4*weightedIntegral d.mass (pairCell Finset.univ) := by
    simp only [weightedIntegral,f,mul_add,Finset.sum_add_distrib,Finset.mul_sum]
    apply congrArg₂ (·+·)
    · apply Finset.sum_congr rfl; intro C _; ring
    · apply Finset.sum_congr rfl; intro C _; ring
  rwa [he] at hh

end WeakPinned.Hierarchy.Depth

namespace WeakPinned.MinKernel
open scoped BigOperators
variable {P : Type u8} [Fintype P]

/-- A fiber whose potential is a constant plus nonnegative overlap and a
small signed grid error has a large iid minimum. This preserves self-pairs
in the sampling, exactly as in the unbounded-scale argument. -/
lemma energy_lower (p S L E : P → ℝ) (c : ℝ)
    (hp : ∀ x, 0≤p x) (hsum : (∑ x, p x)=1)
    (hL : ∀ x, 0≤L x)
    (hS : ∀ x, p x≠0 → S x=c+L x-E x) :
    (∑ x, p x*S x)-(∑ x, p x*L x)-(∑ x, p x*|E x|)≤energy p S S := by
  have hpair (x y : P) :
      p x*p y*((S x+S y)/2-(L x+L y+|E x|+|E y|)/2) ≤
        p x*p y*min (S x) (S y) := by
    by_cases hx : p x=0
    · simp [hx]
    by_cases hy : p y=0
    · simp [hy]
    apply mul_le_mul_of_nonneg_left _ (mul_nonneg (hp x) (hp y))
    have hxS := hS x hx
    have hyS := hS y hy
    apply le_min <;> linarith [hL x,hL y,le_abs_self (E x),le_abs_self (E y),neg_abs_le (E x),neg_abs_le (E y)]
  have hh := Finset.sum_le_sum (s:=Finset.univ) (fun x _ =>
    Finset.sum_le_sum (s:=Finset.univ) (fun y _ => hpair x y))
  change _≤energy p S S at hh
  have he : (∑ x, ∑ y, p x*p y*((S x+S y)/2-(L x+L y+|E x|+|E y|)/2))=
      (∑ x, p x*S x)-(∑ x, p x*L x)-(∑ x, p x*|E x|) := by
    have hform (x y : P) : p x*p y*((S x+S y)/2-(L x+L y+|E x|+|E y|)/2)=
        (p x*S x)*p y/2+p x*(p y*S y)/2-
        ((p x*L x)*p y/2+p x*(p y*L y)/2+(p x*|E x|)*p y/2+p x*(p y*|E y|)/2) := by ring
    simp_rw [hform,Finset.sum_sub_distrib,Finset.sum_add_distrib,← Finset.sum_div,
      ← Finset.mul_sum,← Finset.sum_mul,hsum,mul_one,one_mul]
    ring
  rwa [he] at hh
end WeakPinned.MinKernel

namespace WeakPinned.Hierarchy.Depth
open MeasureTheory Variance
open scoped BigOperators
variable {P : Type u9} {I : Type u10} [Fintype P] [DecidableEq P] [Fintype I]

lemma min_upper_family (d d' : Depth P) (hn : 2≤Fintype.card P)
    (w : I → ℝ) (B : I → Finset P) (T M κ : ℝ)
    (hw : ∀ i, 0≤w i) (hW : (∑ i, w i)≤1) (hT : 1≤T) (hκ : 0≤κ)
    (hB : ∀ i, 2≤(B i).card) (hk : ∀ i, 2/((B i).card:ℝ)≤κ)
    (hdom : ∀ x, (∑ i, w i*prob (B i) x)≤M*prob Finset.univ x) :
    (∑ i, w i*MinKernel.energy (prob (B i)) (d.potential+d'.potential) (d.potential+d'.potential)) ≤
      4*(weightedIntegral d.mass (varianceCell w B T)+weightedIntegral d'.mass (varianceCell w B T))+
      8*(weightedIntegral d.mass (pairCell Finset.univ)+weightedIntegral d'.mass (pairCell Finset.univ))+
      2*κ*M*(∑ x, prob Finset.univ x*(d.potential x+d'.potential x)) := by
  have hm (i) := d.iid_min_two_potentials d' hn (prob (B i))
    (fun x => by unfold prob; split_ifs <;> positivity)
  have hsum := Finset.sum_le_sum (s:=Finset.univ) (fun i _ => mul_le_mul_of_nonneg_left (hm i) (hw i))
  change (∑ i, w i*MinKernel.energy (prob (B i)) (d.potential+d'.potential) (d.potential+d'.potential))≤_ at hsum
  have h₁ := d.integrated_outside_square hn w B T M κ hw hW hT hκ hB hk hdom
  have h₂ := d'.integrated_outside_square hn w B T M κ hw hW hT hκ hB hk hdom
  have hr : (∑ i, w i*(2*((∫ r, (d.outsideMass (prob (B i)) r)^2)+
      (∫ r, (d'.outsideMass (prob (B i)) r)^2))))=
      2*((∑ i, w i*(∫ r, (d.outsideMass (prob (B i)) r)^2))+
      (∑ i, w i*(∫ r, (d'.outsideMass (prob (B i)) r)^2))) := by
    simp only [Finset.mul_sum,← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro i _; ring
  rw [hr] at hsum
  simp only [mul_add,Finset.sum_add_distrib]
  linarith

lemma local_potential_fiber_bound (d d' : Depth P) (hn : 2≤Fintype.card P)
    (w : I → ℝ) (B : I → Finset P) (src : I → P) (t : I → ℝ) (T M κ : ℝ)
    (hw : ∀ i, 0≤w i) (hW : (∑ i, w i)≤1) (hT : 1≤T) (hκ : 0≤κ)
    (hB : ∀ i, 2≤(B i).card) (hk : ∀ i, 2/((B i).card:ℝ)≤κ)
    (hsrc : ∀ i, src i∉B i)
    (hdom : ∀ x, (∑ i, w i*prob (B i) x)≤M*prob Finset.univ x) :
    (∑ i, w i*∑ y, prob (B i) y*(d.potential y+d'.potential y)) ≤
      4*(weightedIntegral d.mass (varianceCell w B T)+weightedIntegral d'.mass (varianceCell w B T))+
      8*(weightedIntegral d.mass (pairCell Finset.univ)+weightedIntegral d'.mass (pairCell Finset.univ))+
      2*κ*M*(∑ x, prob Finset.univ x*(d.potential x+d'.potential x))+
      (∑ i, w i*∑ y, prob (B i) y*(weightedOverlap d.mass (src i) y+weightedOverlap d'.mass (src i) y))+
      (∑ i, w i*∑ y, prob (B i) y*|d.value (src i) y+d'.value (src i) y-t i|) := by
  have hp (i : I) (y : P) : 0≤prob (B i) y := by unfold prob; split_ifs <;> positivity
  have hL (dd : Depth P) (x y : P) : 0≤weightedOverlap dd.mass x y := by
    apply Finset.sum_nonneg; intro C _
    exact mul_nonneg (dd.mass_nonneg C) (by dsimp; split_ifs <;> norm_num)
  have hs (i : I) (y : P) (hy : prob (B i) y≠0) : y∈B i := by
    by_contra hh; exact hy (by simp [prob,hh])
  have hv (dd : Depth P) (i : I) (y : P) (hy : prob (B i) y≠0) :
      weightedOverlap dd.mass (src i) y=dd.overlapLength (src i) y (fun he => hsrc i (he ▸ hs i y hy)) :=
    dd.mass_overlap hn _ _ _
  have he (i : I) := MinKernel.energy_lower (prob (B i))
    (d.potential+d'.potential)
    (fun y => weightedOverlap d.mass (src i) y+weightedOverlap d'.mass (src i) y)
    (fun y => d.value (src i) y+d'.value (src i) y-t i)
    (d.M+d'.M-d.potential (src i)-d'.potential (src i)-t i)
    (hp i) (sum_prob (B i) (Finset.card_pos.mp (by have := hB i; omega)))
    (fun y => add_nonneg (hL d _ _) (hL d' _ _)) (by
      intro y hy
      have hxy : src i≠y := fun h => hsrc i (h ▸ hs i y hy)
      have hx := d.depth_identity hn (src i) y hxy
      have hx' := d'.depth_identity hn (src i) y hxy
      rw [hv d i y hy,hv d' i y hy]
      simp only [Pi.add_apply]
      linarith)
  have hh := Finset.sum_le_sum (s:=Finset.univ) (fun i _ => mul_le_mul_of_nonneg_left (he i) (hw i))
  have hu := min_upper_family d d' hn w B T M κ hw hW hT hκ hB hk hdom
  simp only [Pi.add_apply,mul_sub,Finset.sum_sub_distrib] at hh
  linarith

end WeakPinned.Hierarchy.Depth
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQW_WeakPinned.GlobalPotentials
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u1 u2 u3 u4 u5 u6 u7 u8 u9 u10 u11 u12
universe u13 u14 u15 u16

section
noncomputable section
open NumberField
open scoped BigOperators
noncomputable section
open MeasureTheory
open scoped Topology
noncomputable section
open MeasureTheory
open scoped Topology ENNReal
noncomputable section
open MeasureTheory NumberField
open scoped BigOperators
noncomputable section
open scoped BigOperators
open MeasureTheory
noncomputable section
open Filter
open scoped Topology
noncomputable section
open scoped BigOperators
noncomputable section
open Filter
open scoped Topology
noncomputable section
open MeasureTheory
open scoped BigOperators
noncomputable section

namespace WeakPinned.Global
open Hierarchy MeasureTheory Variance
open scoped BigOperators
variable {P : Type u1} [Fintype P] [DecidableEq P]
variable {K : Type u2} [Field K] [NumberField K]
variable (Z₁ Z₂ : P → K) (h₁ : Function.Injective Z₁) (h₂ : Function.Injective Z₂)

lemma average_add {f g : Depth P → Depth P → ℝ}
    (hi : AverageIntegrable Z₁ Z₂ f) (hj : AverageIntegrable Z₁ Z₂ g) :
    average Z₁ Z₂ h₁ h₂ (fun d d' => f d d'+g d d')=
      average Z₁ Z₂ h₁ h₂ f+average Z₁ Z₂ h₁ h₂ g  := by
  classical
  unfold average
  simp only [integral_add (hi _) (hj _),mul_add,Finset.sum_add_distrib]
  ring

lemma average_mul (f : Depth P → Depth P → ℝ) (c : ℝ) :
    average Z₁ Z₂ h₁ h₂ (fun d d' => c*f d d')=c*average Z₁ Z₂ h₁ h₂ f  := by
  classical
  unfold average
  simp only [integral_const_mul,Finset.mul_sum,mul_add]
  congr 1 <;> apply Finset.sum_congr rfl <;> intro v _ <;> ring

lemma average_sum {J : Type u3} [Fintype J] (f : J → Depth P → Depth P → ℝ)
    (hi : ∀ j, AverageIntegrable Z₁ Z₂ (f j)) :
    average Z₁ Z₂ h₁ h₂ (fun d d' => ∑ j, f j d d')=
      ∑ j, average Z₁ Z₂ h₁ h₂ (f j)  := by
  classical
  unfold average
  simp_rw [integral_finsetSum _ (fun j _ => hi j _),Finset.mul_sum]
  rw [Finset.sum_comm,Finset.sum_comm (s:=placeUnion Z₁ Z₂ h₁ h₂)]
  simp only [Finset.sum_add_distrib]

lemma average_potential_left (hn : 2≤Fintype.card P) (x : P) :
    average Z₁ Z₂ h₁ h₂ (fun d _ => d.potential x)=S Z₁ h₁ x  := by
  classical
  unfold average S
  congr 2
  exact sum_finite_potential h₁ hn _ Finset.subset_union_left x

lemma average_potential_right (hn : 2≤Fintype.card P) (x : P) :
    average Z₁ Z₂ h₁ h₂ (fun _ d' => d'.potential x)=S Z₂ h₂ x  := by
  classical
  unfold average S
  congr 2
  exact sum_finite_potential h₂ hn _ Finset.subset_union_right x

lemma average_mass_left (hn : 2≤Fintype.card P) (C : Finset P) :
    average Z₁ Z₂ h₁ h₂ (fun d _ => d.mass C)=cellMass Z₁ h₁ C  := by
  classical
  unfold average cellMass
  congr 2
  exact sum_finite_mass h₁ hn _ Finset.subset_union_left C

lemma average_mass_right (hn : 2≤Fintype.card P) (C : Finset P) :
    average Z₁ Z₂ h₁ h₂ (fun _ d' => d'.mass C)=cellMass Z₂ h₂ C  := by
  classical
  unfold average cellMass
  congr 2
  exact sum_finite_mass h₂ hn _ Finset.subset_union_right C

omit [NumberField K] in
include h₁ in
lemma integrable_potential_left (hn : 2≤Fintype.card P) (x : P) :
    AverageIntegrable Z₁ Z₂ (fun d _ => d.potential x) :=
  fun v => Depth.integrable_potential_param (arch Z₁ v) (arch_measurable Z₁ h₁ v)
    (arch_integrable Z₁ h₁ v) hn x

omit [NumberField K] in
include h₂ in
lemma integrable_potential_right (hn : 2≤Fintype.card P) (x : P) :
    AverageIntegrable Z₁ Z₂ (fun _ d' => d'.potential x) :=
  fun v => Depth.integrable_potential_param (arch Z₂ v) (arch_measurable Z₂ h₂ v)
    (arch_integrable Z₂ h₂ v) hn x

omit [NumberField K] in
include h₁ in
lemma integrable_mass_left (hn : 2≤Fintype.card P) (C : Finset P) :
    AverageIntegrable Z₁ Z₂ (fun d _ => d.mass C) :=
  fun v => Depth.integrable_mass_param (arch Z₁ v) (arch_measurable Z₁ h₁ v)
    (arch_integrable Z₁ h₁ v) hn C

omit [NumberField K] in
include h₂ in
lemma integrable_mass_right (hn : 2≤Fintype.card P) (C : Finset P) :
    AverageIntegrable Z₁ Z₂ (fun _ d' => d'.mass C) :=
  fun v => Depth.integrable_mass_param (arch Z₂ v) (arch_measurable Z₂ h₂ v)
    (arch_integrable Z₂ h₂ v) hn C

end WeakPinned.Global

namespace WeakPinned.Global
open Hierarchy MeasureTheory Variance
open scoped BigOperators
variable {P : Type u4} [Fintype P] [DecidableEq P]
variable {K : Type u5} [Field K] [NumberField K]
variable (Z₁ Z₂ : P → K) (h₁ : Function.Injective Z₁) (h₂ : Function.Injective Z₂)

omit [NumberField K] in
include h₁ h₂ in
lemma integrable_potentialEval (hn : 2≤Fintype.card P) (p : P → ℝ) :
    AverageIntegrable Z₁ Z₂ (potentialEval p) := by
  intro v
  exact integrable_finsetSum (s:=Finset.univ) (fun y _ =>
    ((integrable_potential_left Z₁ Z₂ h₁ hn y v).add
      (integrable_potential_right Z₁ Z₂ h₂ hn y v)).const_mul (p y))

omit [NumberField K] in
include h₁ h₂ in
lemma integrable_massEval (hn : 2≤Fintype.card P) (q : Finset P → ℝ) :
    AverageIntegrable Z₁ Z₂ (massEval q) := by
  intro v
  exact (integrable_finsetSum (s:=Finset.univ) (fun C _ =>
      (integrable_mass_left Z₁ Z₂ h₁ hn C v).mul_const (q C))).add
    (integrable_finsetSum (s:=Finset.univ) (fun C _ =>
      (integrable_mass_right Z₁ Z₂ h₂ hn C v).mul_const (q C)))

lemma average_potentialEval (hn : 2≤Fintype.card P) (p : P → ℝ) :
    average Z₁ Z₂ h₁ h₂ (potentialEval p)=∑ y, p y*totalPotential Z₁ Z₂ h₁ h₂ y := by
  unfold potentialEval
  rw [average_sum Z₁ Z₂ h₁ h₂ _ (fun y v =>
    ((integrable_potential_left Z₁ Z₂ h₁ hn y v).add
      (integrable_potential_right Z₁ Z₂ h₂ hn y v)).const_mul (p y))]
  apply Finset.sum_congr rfl
  intro y _
  rw [average_mul,average_add Z₁ Z₂ h₁ h₂
    (integrable_potential_left Z₁ Z₂ h₁ hn y) (integrable_potential_right Z₁ Z₂ h₂ hn y),
    average_potential_left Z₁ Z₂ h₁ h₂ hn,average_potential_right Z₁ Z₂ h₁ h₂ hn]
  rfl

lemma average_massEval (hn : 2≤Fintype.card P) (q : Finset P → ℝ) :
    average Z₁ Z₂ h₁ h₂ (massEval q)=weightedIntegral (totalMass Z₁ Z₂ h₁ h₂) q := by
  have he : massEval q=(fun d d' => ∑ C, q C*(d.mass C+d'.mass C)) := by
    funext d d'
    simp only [massEval,weightedIntegral,mul_add,Finset.sum_add_distrib]
    congr 1 <;> apply Finset.sum_congr rfl <;> intro C _ <;> ring
  rw [he,average_sum Z₁ Z₂ h₁ h₂ _ (fun C v =>
    ((integrable_mass_left Z₁ Z₂ h₁ hn C v).add
      (integrable_mass_right Z₁ Z₂ h₂ hn C v)).const_mul (q C))]
  apply Finset.sum_congr rfl
  intro C _
  rw [average_mul,average_add Z₁ Z₂ h₁ h₂
    (integrable_mass_left Z₁ Z₂ h₁ hn C) (integrable_mass_right Z₁ Z₂ h₂ hn C),
    average_mass_left Z₁ Z₂ h₁ h₂ hn,average_mass_right Z₁ Z₂ h₁ h₂ hn]
  simp only [totalMass]; ring

omit Z₁ Z₂ h₁ h₂ in
lemma massEval_edge {I : Type u6} [Fintype I] (w : I → ℝ) (p : I → P → ℝ) (x : I → P)
    (d d' : Depth P) :
    massEval (SmallFiber.edgeCell w p x) d d'=
      ∑ i, w i*∑ y, p i y*(weightedOverlap d.mass (x i) y+weightedOverlap d'.mass (x i) y) := by
  have he (m : Finset P → ℝ) : weightedIntegral m (SmallFiber.edgeCell w p x)=
      ∑ i, w i*∑ y, p i y*weightedOverlap m (x i) y := by
    unfold SmallFiber.edgeCell
    rw [weighted_pair]
    unfold SmallFiber.edgeLaw
    simp only [Finset.sum_mul]
    calc
      _ = ∑ a, ∑ i, ∑ y, (if x i=a then w i*p i y else 0)*weightedOverlap m a y := by
        apply Finset.sum_congr rfl
        intro a _
        exact Finset.sum_comm
      _ = ∑ i, ∑ a, ∑ y, (if x i=a then w i*p i y else 0)*weightedOverlap m a y := Finset.sum_comm
      _ = _ := by
        simp only [ite_mul,zero_mul,Finset.sum_ite_irrel,Finset.sum_const_zero]
        simp [Finset.mul_sum,mul_assoc]
  -- commute the source sum after inserting the indicator
  simp only [massEval,he,mul_add,Finset.sum_add_distrib]
end WeakPinned.Global

namespace WeakPinned.Global
open Hierarchy MeasureTheory Variance
open scoped BigOperators
variable {P : Type u7} {I : Type u8} [Fintype P] [DecidableEq P] [Fintype I]
variable {K : Type u9} [Field K] [NumberField K]
variable (Z₁ Z₂ : P → K) (h₁ : Function.Injective Z₁) (h₂ : Function.Injective Z₂)

omit Z₁ Z₂ h₁ h₂ in
lemma potentialEval_mixture (w : I → ℝ) (p : I → P → ℝ) (d d' : Depth P) :
    potentialEval (fun y => ∑ i, w i*p i y) d d'=∑ i, w i*∑ y, p i y*(d.potential y+d'.potential y) := by
  simp only [potentialEval,Finset.sum_mul,Finset.mul_sum,mul_assoc]
  exact Finset.sum_comm

lemma average_sub {f g : Depth P → Depth P → ℝ}
    (hi : AverageIntegrable Z₁ Z₂ f) (hj : AverageIntegrable Z₁ Z₂ g) :
    average Z₁ Z₂ h₁ h₂ (fun d d' => f d d'-g d d')=
      average Z₁ Z₂ h₁ h₂ f-average Z₁ Z₂ h₁ h₂ g := by
  classical
  unfold average
  simp only [integral_sub (hi _) (hj _),mul_sub,Finset.sum_sub_distrib]
  ring

/-- The first-moment raw-depth error is archimedean only. Its global constant
is independent of the degree and all coordinates. -/
lemma arithmetic_potential_fiber_bound (hn : 2≤Fintype.card P)
    (w : I → ℝ) (B : I → Finset P) (src : I → P) (t : I → K) (T M κ : ℝ)
    (hw : ∀ i, 0≤w i) (hW : (∑ i, w i)=1) (hT : 1≤T) (hκ : 0≤κ)
    (hB : ∀ i, 2≤(B i).card) (hk : ∀ i, 2/((B i).card:ℝ)≤κ)
    (hsrc : ∀ i, src i∉B i)
    (hdom : ∀ x, (∑ i, w i*prob (B i) x)≤M*prob Finset.univ x)
    (ht : ∀ i y, y∈B i → (Z₁ (src i)-Z₁ y)*(Z₂ (src i)-Z₂ y)=t i) :
    (∑ y, (∑ i, w i*prob (B i) y)*totalPotential Z₁ Z₂ h₁ h₂ y) ≤
      4*weightedIntegral (totalMass Z₁ Z₂ h₁ h₂) (varianceCell w B T)+
      8*overlapScale Z₁ Z₂ h₁ h₂+
      2*κ*M*potentialScale Z₁ Z₂ h₁ h₂+
      weightedIntegral (totalMass Z₁ Z₂ h₁ h₂) (SmallFiber.edgeCell w (fun i => prob (B i)) src)+16 := by
  classical
  let p : I → P → ℝ := fun i => prob (B i)
  let r : P → ℝ := fun y => ∑ i, w i*p i y
  let q := SmallFiber.edgeCell w p src
  let vcell := varianceCell w B T
  let pc := pairCell (Finset.univ : Finset P)
  let unif := prob (Finset.univ : Finset P)
  let R : Depth P → Depth P → ℝ := fun d d' =>
    4*massEval vcell d d'+8*massEval pc d d'+2*κ*M*potentialEval unif d d'+massEval q d d'
  let f : Depth P → Depth P → ℝ := fun d d' => potentialEval r d d'-R d d'
  have hp (i y) : 0≤p i y := by dsimp [p,prob]; split_ifs <;> positivity
  have hp1 (i) : ∑ y, p i y=1 := sum_prob (B i) (Finset.card_pos.mp (by have := hB i; omega))
  have hx (i) : p i (src i)=0 := by simp [p,prob,hsrc i]
  have ht' (i y) (hy : p i y≠0) : (Z₁ (src i)-Z₁ y)*(Z₂ (src i)-Z₂ y)=t i := by
    apply ht i y
    by_contra hn'; exact hy (by simp [p,prob,hn'])
  have hL := integrable_potentialEval Z₁ Z₂ h₁ h₂ hn r
  have hV := integrable_massEval Z₁ Z₂ h₁ h₂ hn vcell
  have hP := integrable_massEval Z₁ Z₂ h₁ h₂ hn pc
  have hA := integrable_potentialEval Z₁ Z₂ h₁ h₂ hn unif
  have hQ := integrable_massEval Z₁ Z₂ h₁ h₂ hn q
  have hR : AverageIntegrable Z₁ Z₂ R := fun v =>
    ((((hV v).const_mul 4).add ((hP v).const_mul 8)).add ((hA v).const_mul (2*κ*M))).add (hQ v)
  have hf : AverageIntegrable Z₁ Z₂ f := fun v => (hL v).sub (hR v)
  have hb (d d' : Depth P) (a : I → ℝ) :
      f d d'≤∑ i, w i*∑ y, p i y*|d.value (src i) y+d'.value (src i) y-a i| := by
    have hh := d.local_potential_fiber_bound d' hn w B src a T M κ hw hW.le hT hκ hB hk hsrc hdom
    rw [← potentialEval_mixture,← massEval_edge] at hh
    change potentialEval r d d'≤R d d'+_ at hh
    exact sub_le_iff_le_add'.mpr hh
  have ha (v : NumberField.InfinitePlace K) :
      (∫ ω, f (arch Z₁ v ω) (arch Z₂ v ω) ∂Grid.fullLaw)≤16 := by
    let E : Grid.FullSample → ℝ := fun ω => ∑ i, w i*∑ y, p i y*
      |(arch Z₁ v ω).value (src i) y+(arch Z₂ v ω).value (src i) y+Real.log (v (t i))|
    have hi : Integrable E Grid.fullLaw := integrable_finsetSum (s:=Finset.univ) (fun i _ =>
      (integrable_finsetSum (s:=Finset.univ) (fun y _ =>
        ((((arch_integrable Z₁ h₁ v _ _).add (arch_integrable Z₂ h₂ v _ _)).add
          (integrable_const _)).abs.const_mul (p i y)))).const_mul (w i))
    have hu : (∫ ω, E ω ∂Grid.fullLaw)≤16 := by
      simpa only [E,sub_zero,max_eq_left (abs_nonneg (_ : ℝ)),neg_zero,zero_div,Real.exp_zero,mul_one]
        using arch_weighted_defect Z₁ Z₂ h₁ h₂ v w p src t hw hW hp hp1 hx ht' 0 (by norm_num)
    exact (integral_mono (hf v) hi (fun ω => by
      simpa only [sub_neg_eq_add] using hb (arch Z₁ v ω) (arch Z₂ v ω) (fun i => -Real.log (v (t i))))).trans hu
  have hv (v : NumberField.FinitePlace K) : f (finite Z₁ h₁ v) (finite Z₂ h₂ v)≤0 := by
    have he (i y) : p i y*|(finite Z₁ h₁ v).value (src i) y+
        (finite Z₂ h₂ v).value (src i) y-(-Real.log (v (t i)))|=0 := by
      by_cases hy : p i y=0
      · simp [hy]
      · have hxy : src i≠y := by intro hh; exact hsrc i (hh ▸ (by
          by_contra hm; exact hy (by simp [p,prob,hm])))
        have hh := Arithmetic.raw_fiber_identity v.val (Z₁ (src i)-Z₁ y) (Z₂ (src i)-Z₂ y)
          (sub_ne_zero.mpr (h₁.ne hxy)) (sub_ne_zero.mpr (h₂.ne hxy))
        rw [ht' i y hy] at hh
        change -Real.log (v (Z₁ (src i)-Z₁ y)) + -Real.log (v (Z₂ (src i)-Z₂ y)) = -Real.log (v (t i)) at hh
        simp only [finite,ite_eq_right hxy,hh,sub_self,abs_zero,mul_zero]
    simpa only [he,Finset.sum_const_zero,mul_zero] using
      hb (finite Z₁ h₁ v) (finite Z₂ h₂ v) (fun i => -Real.log (v (t i)))
  have hg : average Z₁ Z₂ h₁ h₂ f≤16 := by
    change placeAverage (placeUnion Z₁ Z₂ h₁ h₂) _ _≤16
    have hh := placeAverage_mono (placeUnion Z₁ Z₂ h₁ h₂) ha (fun v _ => hv v)
    rwa [placeAverage_arch_const] at hh
  have hRe : average Z₁ Z₂ h₁ h₂ R =
      4*weightedIntegral (totalMass Z₁ Z₂ h₁ h₂) vcell+
      8*weightedIntegral (totalMass Z₁ Z₂ h₁ h₂) pc+
      2*κ*M*(∑ y, unif y*totalPotential Z₁ Z₂ h₁ h₂ y)+
      weightedIntegral (totalMass Z₁ Z₂ h₁ h₂) q := by
    unfold R
    rw [average_add Z₁ Z₂ h₁ h₂ (fun v => (((hV v).const_mul 4).add ((hP v).const_mul 8)).add ((hA v).const_mul (2*κ*M))) hQ,
      average_add Z₁ Z₂ h₁ h₂ (fun v => ((hV v).const_mul 4).add ((hP v).const_mul 8)) (fun v => (hA v).const_mul (2*κ*M)),
      average_add Z₁ Z₂ h₁ h₂ (fun v => (hV v).const_mul 4) (fun v => (hP v).const_mul 8)]
    simp only [average_mul,average_massEval Z₁ Z₂ h₁ h₂ hn,average_potentialEval Z₁ Z₂ h₁ h₂ hn]
  change average Z₁ Z₂ h₁ h₂ (fun d d' => potentialEval r d d'-R d d')≤16 at hg
  rw [average_sub Z₁ Z₂ h₁ h₂ hL hR,average_potentialEval Z₁ Z₂ h₁ h₂ hn,hRe] at hg
  exact sub_le_iff_le_add'.mp hg
end WeakPinned.Global

namespace WeakPinned.Variance
open scoped BigOperators
variable {P : Type u10} [Fintype P] [DecidableEq P]

/-- Nonnegative additive off-diagonal overlap controls the potential at every
vertex, not merely at vertices typical for the edge marginal. -/
lemma point_potential_lower (m : Finset P → ℝ) (b : ℝ) (S : P → ℝ)
    (hm : ∀ C : Finset P, (0 : ℝ) ≤ m C) (hL : ∀ x y, x≠y → weightedOverlap m x y=b+S x+S y)
    (hn : 3≤Fintype.card P) (x : P) :
    (∑ y, prob Finset.univ y*S y)-2*weightedIntegral m (pairCell Finset.univ)≤S x := by
  let n : ℝ := Fintype.card P
  have hn3 : 3≤n := by dsimp [n]; exact_mod_cast hn
  have hn0 : n≠0 := by linarith
  let A : ℝ := (∑ y, prob Finset.univ y*S y)
  let W : ℝ := weightedIntegral m (pairCell Finset.univ)
  have hW : 0≤W := Finset.sum_nonneg (fun C _ => mul_nonneg (hm C) (pairCell_nonneg _ _))
  have hu : W=b+2*A := uniform_additive m b S hL (by omega)
  have hs : (∑ y, S y)=n*A := by
    dsimp [A,prob,n]
    simp only [Finset.mem_univ,ite_true]
    rw [← Finset.mul_sum]
    have hn0' : (Fintype.card P : ℝ) ≠ 0 := hn0
    field_simp
  have hnn : 0 ≤ ∑ y ∈ Finset.univ.erase x, (b+S x+S y) := by
    apply Finset.sum_nonneg
    intro y hy
    rw [← hL x y (Finset.ne_of_mem_erase hy).symm]
    exact Finset.sum_nonneg (fun C _ => mul_nonneg (hm C) (by dsimp; split_ifs <;> norm_num))
  have hsx : (∑ y ∈ Finset.univ.erase x, S y)=(∑ y, S y)-S x := by
    exact eq_sub_of_add_eq (Finset.sum_erase_add Finset.univ S (Finset.mem_univ x))
  have hcount : ((Finset.univ.erase x).card:ℝ)=n-1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ x),Finset.card_univ,Nat.cast_sub (by omega),Nat.cast_one]
  simp only [Finset.sum_add_distrib,Finset.sum_const,nsmul_eq_mul,hcount,hsx,hs] at hnn
  change A-2*W≤S x
  nlinarith [mul_nonneg (by linarith : 0≤n-3) hW]

end WeakPinned.Variance

namespace WeakPinned
open Global Variance
open scoped BigOperators
variable {P : Type u11} {I : Type u12} [Fintype P] [Fintype I] [DecidableEq P]
variable {K : Type u13} [Field K] [NumberField K]

/-- Quantitative scale balance for arithmetic fibers, without an unboundedness assumption. -/

theorem arithmetic_scale_balance (G : Core.Fibers P I)
    (Z₁ Z₂ : P → K) (h₁ : Function.Injective Z₁) (h₂ : Function.Injective Z₂)
    (hn : 3≤Fintype.card P) (hG : 0<G.edgeCount)
    (T M κ : ℝ) (hT : 1≤T) (hκ : 0≤κ)
    (hB : ∀ i, 2≤(G.targets i).card) (hk : ∀ i, 2/((G.targets i).card:ℝ)≤κ)
    (hdom : ∀ x y, G.edgeLaw x y≤M*pairProb Finset.univ x y)
    (t : I → K) (ht : ∀ i y, y∈G.targets i →
      (Z₁ (G.source i)-Z₁ y)*(Z₂ (G.source i)-Z₂ y)=t i) :
    (1-2*κ*M)*potentialScale Z₁ Z₂ h₁ h₂ ≤
      4*weightedIntegral (totalMass Z₁ Z₂ h₁ h₂) (varianceCell G.fiberWeight G.targets T)+
      (10+M)*overlapScale Z₁ Z₂ h₁ h₂+16 := by
  have hn2 : 2≤Fintype.card P := by omega
  have hh := arithmetic_potential_fiber_bound Z₁ Z₂ h₁ h₂ hn2 G.fiberWeight G.targets G.source t T M κ
    G.fiberWeight_nonneg (G.sum_fiberWeight hG) hT hκ hB hk G.no_loop
    (G.fiber_domination M hdom hn2) ht
  let m := totalMass Z₁ Z₂ h₁ h₂
  let S := totalPotential Z₁ Z₂ h₁ h₂
  let r : P → ℝ := fun y => ∑ i, G.fiberWeight i*prob (G.targets i) y
  have hr0 (y) : 0≤r y := by
    apply Finset.sum_nonneg
    intro i _
    apply mul_nonneg (G.fiberWeight_nonneg i)
    unfold prob; split_ifs <;> positivity
  have hr1 : ∑ y, r y=1 := by
    dsimp [r]
    rw [Finset.sum_comm]
    have hp1 (i : I) : ∑ y, prob (G.targets i) y=1 :=
      sum_prob (G.targets i) (Finset.card_pos.mp (by have := hB i; omega))
    simp_rw [← Finset.mul_sum,hp1,mul_one]
    exact G.sum_fiberWeight hG
  have hl : potentialScale Z₁ Z₂ h₁ h₂-2*overlapScale Z₁ Z₂ h₁ h₂≤∑ y, r y*S y := by
    have hlo (y) := point_potential_lower m (baseConstant Z₁ Z₂ h₁ h₂) S
      (totalMass_nonneg Z₁ Z₂ h₁ h₂) (totalMass_overlap Z₁ Z₂ h₁ h₂ hn2) hn y
    have hu := Finset.sum_le_sum (s:=Finset.univ) (fun y _ => mul_le_mul_of_nonneg_left (hlo y) (hr0 y))
    simpa only [← Finset.sum_mul,hr1,one_mul,potentialScale,overlapScale,m,S] using hu
  have he : SmallFiber.edgeCell G.fiberWeight (fun i => prob (G.targets i)) G.source=G.qCell := by
    funext C; exact (G.qCell_eq C).symm
  have hq : weightedIntegral m G.qCell≤M*overlapScale Z₁ Z₂ h₁ h₂ := by
    simp only [weightedIntegral,Finset.mul_sum,overlapScale]
    calc
      _ ≤ ∑ C, m C*(M*pairCell Finset.univ C) := Finset.sum_le_sum (fun C _ =>
        mul_le_mul_of_nonneg_left (G.qCell_bound hdom C) (totalMass_nonneg Z₁ Z₂ h₁ h₂ C))
      _ = _ := by apply Finset.sum_congr rfl; intro C _; dsimp [m]; ring
  rw [he] at hh
  change (∑ y, r y*S y)≤_ at hh
  change weightedIntegral (totalMass Z₁ Z₂ h₁ h₂) G.qCell≤_ at hq
  nlinarith
end WeakPinned

namespace WeakPinned
open Filter
open scoped Topology

/-- Elementary absorption of the two asymptotically small errors. -/
lemma scale_balance_rate (W A V δ : ℕ → ℝ) (B : ℝ) (hB : 0≤B)
    (hW : ∀ j, 0≤W j) (hA : ∀ j, 0≤A j)
    (hδ : Tendsto δ atTop (𝓝 0))
    (hV : Tendsto (fun j => V j/(W j+A j+1)) atTop (𝓝 0))
    (hbal : ∀ᶠ j in atTop, (1-δ j)*A j≤4*V j+(10+B)*W j+16) :
    ∀ᶠ j in atTop, A j≤(64+4*B)*(W j+1) := by
  filter_upwards [hbal,hδ.eventually (eventually_lt_nhds (by norm_num : (0:ℝ)<1/4)),
    hV.eventually (eventually_lt_nhds (by norm_num : (0:ℝ)<1/16))] with j hb hd hv
  have hden : 0<W j+A j+1 := by linarith [hW j,hA j]
  have hv' := (div_lt_iff₀ hden).mp hv
  nlinarith [hW j,hA j,mul_nonneg (hW j) hB]
end WeakPinned

namespace WeakPinned
open Global Variance Filter
open scoped Topology BigOperators
variable {V : ℕ → Type u14} {I : ℕ → Type u15} {K : ℕ → Type u16} [∀ j, Fintype (V j)] [∀ j, Fintype (I j)] [∀ j, DecidableEq (V j)]
  [∀ j, Field (K j)] [∀ j, NumberField (K j)]
variable (G : ∀ j, Core.Fibers (V j) (I j)) (θ γ c : ℝ) (η : ℕ → ℝ)
  (Z₁ Z₂ : ∀ j, V j → K j) (h₁ : ∀ j, Function.Injective (Z₁ j)) (h₂ : ∀ j, Function.Injective (Z₂ j))

theorem arithmetic_scale_comparison (hθ : 0<θ) (hγ : 0<γ) (hγ1 : γ<1) (hcγ : c<γ)
    (hn : Tendsto (fun j => (Fintype.card (V j):ℝ)) atTop atTop)
    (hη : Tendsto η atTop (𝓝 0)) (hη0 : ∀ j, 0≤η j) (hηb : ∀ j, η j≤θ/2)
    (hG : ∀ j, PreparedGraph (V j) (I j) (G j) θ γ c (η j))
    (t : ∀ j, I j → K j) (ht : ∀ j e y, y ∈ (G j).targets e →
      (Z₁ j ((G j).source e)-Z₁ j y)*(Z₂ j ((G j).source e)-Z₂ j y)=t j e) :
    ∀ᶠ j in atTop, potentialScale (Z₁ j) (Z₂ j) (h₁ j) (h₂ j) ≤
      (64+8/θ)*(overlapScale (Z₁ j) (Z₂ j) (h₁ j) (h₂ j)+1) := by
  let n : ℕ → ℝ := fun j => Fintype.card (V j)
  let κ : ℕ → ℝ := fun j => 2/(n j)^γ
  have hnγ : Tendsto (fun j => (n j)^γ) atTop atTop := (tendsto_rpow_atTop hγ).comp hn
  have hκ : Tendsto κ atTop (𝓝 0) := by
    simpa only [κ,div_eq_mul_inv,mul_zero,Function.comp_def] using tendsto_const_nhds.mul (tendsto_inv_atTop_zero.comp hnγ)
  have hv := (sampling_variance_rates G θ γ c η Z₁ Z₂ h₁ h₂ hθ hγ hγ1 hcγ hn hη hη0 hηb hG t ht).1
  have hs := scale_balance_rate
    (fun j => overlapScale (Z₁ j) (Z₂ j) (h₁ j) (h₂ j))
    (fun j => potentialScale (Z₁ j) (Z₂ j) (h₁ j) (h₂ j))
    (fiberVariance G c Z₁ Z₂ h₁ h₂) (fun j => 2*κ j*(2/θ)) (2/θ) (by positivity)
    (fun j => overlapScale_nonneg _ _ _ _) (fun j => potentialScale_nonneg _ _ _ _)
    (by simpa using (tendsto_const_nhds.mul hκ).mul_const (2/θ)) hv
  have hb : ∀ᶠ j in atTop,
      (1-2*κ j*(2/θ))*potentialScale (Z₁ j) (Z₂ j) (h₁ j) (h₂ j) ≤
      4*fiberVariance G c Z₁ Z₂ h₁ h₂ j+(10+2/θ)*overlapScale (Z₁ j) (Z₂ j) (h₁ j) (h₂ j)+16 := by
    filter_upwards [hn.eventually (eventually_ge_atTop (3:ℝ)),hnγ.eventually (eventually_ge_atTop (2:ℝ))] with j hj hjγ
    have hn3 : 3≤Fintype.card (V j) := by exact_mod_cast hj
    have hne : 0<(G j).edgeCount := (hG j).edgeCount_pos (by linarith [hηb j])
    have hn0 : 0<n j := by change (0:ℝ)<Fintype.card (V j); linarith
    have hBk (i) : (n j)^γ≤((G j).targets i).card := (hG j).fiber i |>.le
    have hBk2 (i) : 2≤((G j).targets i).card := by exact_mod_cast hjγ.trans (hBk i)
    have hk (i) : 2/(((G j).targets i).card:ℝ)≤κ j :=
      div_le_div_of_nonneg_left (by norm_num) (Real.rpow_pos_of_pos hn0 _) (hBk i)
    have hT : 1≤(n j)^(1-c) := Real.one_le_rpow (by linarith) (by linarith)
    exact arithmetic_scale_balance (G j) (Z₁ j) (Z₂ j) (h₁ j) (h₂ j) hn3 hne
      ((n j)^(1-c)) (2/θ) (κ j) hT (by dsimp [κ]; positivity) hBk2 hk
      ((hG j).uniform_domination hθ (hηb j)) (t j) (ht j)
  have hh := hs hb
  convert hh using 1; ring_nf
end WeakPinned

end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQW_WeakPinned.TreeContradiction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u1 u2 u3 u4

section
noncomputable section
open NumberField
open scoped BigOperators
noncomputable section
open MeasureTheory
open scoped Topology
noncomputable section
open MeasureTheory
open scoped Topology ENNReal
noncomputable section
open MeasureTheory NumberField
open scoped BigOperators
noncomputable section
open scoped BigOperators
open MeasureTheory
noncomputable section
open Filter
open scoped Topology
noncomputable section
open scoped BigOperators
noncomputable section
open Filter
open scoped Topology
noncomputable section
open MeasureTheory
open scoped BigOperators
noncomputable section
noncomputable section
open scoped BigOperators
noncomputable section
noncomputable section
noncomputable section

noncomputable section
namespace WeakPinned.Core.Fibers
open MeasureTheory Hierarchy Variance Cuts
open scoped BigOperators
variable {V : Type u3} {I : Type u4} [Fintype V] [Fintype I] [DecidableEq V]
variable (G : Fibers V I)

omit [Fintype I] in
lemma conditionalSource_nonneg (y x : V) : 0≤G.conditionalSource y x := by
  unfold conditionalSource
  split_ifs <;> exact prob_nn _ _

omit [Fintype I] in
lemma conditionalSource_sum (hn : 2≤Fintype.card V) (y : V) : ∑ x, G.conditionalSource y x=1 := by
  unfold conditionalSource
  split_ifs with h
  · exact sum_prob _ h
  · exact sum_prob _ (Finset.univ_nonempty_iff.mpr (Fintype.card_pos_iff.mp (by omega)))

omit [Fintype I] in
lemma incomingWeight_nonneg (y : V) : 0≤G.incomingWeight y := by unfold incomingWeight edgeCount; positivity

omit [Fintype I] in
lemma sampling_conditional (y x : V) : G.incomingWeight y*G.conditionalSource y x=G.edgeLaw x y := by
  by_cases h : (G.incoming y).Nonempty
  · simpa only [conditionalSource,ite_eq_left h] using G.sampling_incoming x y
  · have he : G.incoming y=∅ := Finset.not_nonempty_iff_eq_empty.mp h
    have hh := G.sampling_incoming x y
    have hw : G.incomingWeight y=0 := by simp [incomingWeight,he]
    simp only [hw,zero_mul] at hh ⊢
    exact hh

lemma incoming_eval (F : V → V → ℝ) :
    (∑ y, G.incomingWeight y*∑ x, G.conditionalSource y x*F x y)=
      ∑ e, G.fiberWeight e*∑ y, prob (G.targets e) y*F (G.source e) y := by
  simp only [Finset.mul_sum,← mul_assoc,G.sampling_conditional,← G.sampling_fiber,Finset.sum_mul]
  conv_lhs =>
    arg 2
    ext y
    rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e _
  apply Finset.sum_congr rfl
  intro y _
  simp only [ite_mul,zero_mul]
  simp

omit [Fintype I] in
lemma omittedMass_nonneg (T : ℝ) : 0≤G.omittedMass T := by
  apply Finset.sum_nonneg
  intro y _
  split_ifs
  · exact G.incomingWeight_nonneg y
  · rfl

end WeakPinned.Core.Fibers

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQW_WeakPinned.UnboundedContradiction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u1 u2 u3 u4 u5 u6 u7 u8 u9 u10 u11 u12
universe u13 u14 u15 u16 u17 u18 u19 u20 u21 u22 u23

section
noncomputable section
noncomputable section
namespace WeakPinned
open Filter Variance Core.Fibers
open scoped Topology
variable {V : Type u17} {I : Type u18} [Fintype V] [Fintype I] [DecidableEq V]

lemma PreparedGraph.omitted_bound {G : Core.Fibers V I} {θ γ c η : ℝ}
    (hG : PreparedGraph V I G θ γ c η) (hθ : 0<θ) (hη : η≤θ/2) :
    G.omittedMass ((Fintype.card V:ℝ)^γ) ≤ (4/θ)*(Fintype.card V:ℝ)^(γ-1) := by
  let n : ℝ := Fintype.card V
  have hn : 2≤n := by dsimp only [n]; exact_mod_cast hG.card_ge
  have hn0 : 0<n := by linarith
  have hE := hG.edgeCount_pos (by linarith)
  have hEl : (θ/4)*n^2≤G.edgeCount := by
    have hp : 0≤(n-1)*n := mul_nonneg (by linarith) hn0.le
    have hh := mul_nonneg (show 0≤θ-η-θ/2 by linarith) hp
    have hh' := mul_nonneg (show 0≤θ/4 by positivity) (show 0≤n*(n-2) by positivity)
    dsimp [n] at *
    nlinarith [hG.lower]
  apply (G.small_incoming_mass _ (Real.rpow_nonneg hn0.le γ)).trans
  change n*n^γ/G.edgeCount≤(4/θ)*n^(γ-1)
  rw [Real.rpow_sub hn0,Real.rpow_one]
  apply (div_le_iff₀ hE).mpr
  have hh := mul_le_mul_of_nonneg_left hEl (show 0≤(4/θ)*(n^γ/n) by positivity)
  have he : (4/θ)*(n^γ/n)*((θ/4)*n^2)=n*n^γ := by field_simp
  rw [he] at hh
  exact hh

variable {Vn : ℕ → Type u19} {In : ℕ → Type u20} [∀ j, Fintype (Vn j)] [∀ j, Fintype (In j)] [∀ j, DecidableEq (Vn j)]
lemma omitted_rate (G : ∀ j, Core.Fibers (Vn j) (In j)) (θ γ c : ℝ) (η : ℕ → ℝ)
    (hθ : 0<θ) (hγ1 : γ<1) (hη : ∀ j, η j≤θ/2)
    (hn : Tendsto (fun j => (Fintype.card (Vn j):ℝ)) atTop atTop)
    (hG : ∀ j, PreparedGraph (Vn j) (In j) (G j) θ γ c (η j)) :
    Tendsto (fun j => (G j).omittedMass ((Fintype.card (Vn j):ℝ)^γ)) atTop (𝓝 0) := by
  apply squeeze_zero (fun j => (G j).omittedMass_nonneg _) (fun j => (hG j).omitted_bound hθ (hη j))
  have hh := (tendsto_rpow_neg_atTop (show 0<1-γ by linarith)).comp hn
  have he : -(1-γ)=γ-1 := by ring
  rw [he] at hh
  simpa using hh.const_mul (4/θ)

end WeakPinned
end
end
end

end OAI
end

section
-- module Solutions.OAIQW_WeakPinned.WeightedSelection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u1 u2 u3

section
noncomputable section
open scoped BigOperators Topology
open Filter MeasureTheory
namespace WeakPinned.Bounded

/-- Simultaneous selection from a normalized weighted family. In particular,
there is no required lower bound on a nonzero archimedean-place weight. -/
lemma weighted_select {J : Type u1} [Fintype J] (w T V : J → ℝ) (C ε : ℝ)
    (hw : ∀ j, 0 < w j) (hW : ∑ j, w j = 1)
    (hT : ∀ j, 0 ≤ T j) (hV : ∀ j, 0 ≤ V j)
    (hC : 0 ≤ C) (hε : 0 < ε)
    (hTC : ∑ j, w j * T j ≤ C) (hVE : ∑ j, w j * V j ≤ ε) :
    ∃ j, T j ≤ 2*C+1 ∧ V j ≤ 2*ε := by
  have hne : (Finset.univ : Finset J).Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty.mp h, Finset.sum_empty] at hW
    norm_num at hW
  have hs : ∑ j, w j*(T j+(C+1)/ε*V j) ≤ ∑ j, w j*(2*C+1) := by
    simp only [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul]
    rw [hW, one_mul]
    have hv := mul_le_mul_of_nonneg_left hVE (show 0≤(C+1)/ε by positivity)
    have he : (∑ j, w j*((C+1)/ε*V j)) = (C+1)/ε*(∑ j,w j*V j) := by
      simp only [Finset.mul_sum]; apply Finset.sum_congr rfl; intros; ring
    rw [he]
    have he' : (C+1)/ε*ε=C+1 := by field_simp
    rw [he'] at hv
    linarith
  obtain ⟨j, _, hj⟩ := Finset.exists_le_of_sum_le hne hs
  have hj' : T j+(C+1)/ε*V j ≤ 2*C+1 := (mul_le_mul_iff_right₀ (hw j)).mp hj
  refine ⟨j, (le_add_of_nonneg_right (mul_nonneg (by positivity) (hV j))).trans hj', ?_⟩
  have hv' : (C+1)/ε*V j ≤ 2*C+1 := by linarith [hT j]
  have he : (C+1)/ε*(2*ε) = 2*(C+1) := by field_simp
  by_contra h
  have hh := mul_lt_mul_of_pos_left (lt_of_not_ge h) (show 0 < (C+1)/ε by positivity)
  rw [he] at hh
  linarith

end WeakPinned.Bounded

namespace WeakPinned.Bounded
open Hierarchy Variance Global NumberField
variable {P : Type u2} [Fintype P] [DecidableEq P]
variable {K : Type u3} [Field K] [NumberField K]
variable (Z₁ Z₂ : P → K) (h₁ : Function.Injective Z₁) (h₂ : Function.Injective Z₂)

omit Z₁ Z₂ h₁ h₂ in
lemma massEval_nonneg (q : Finset P → ℝ) (hq : ∀ C, 0≤q C) (d d' : Depth P) :
    0 ≤ massEval q d d' := by
  exact add_nonneg (Finset.sum_nonneg (fun C _ => mul_nonneg (d.mass_nonneg C) (hq C)))
    (Finset.sum_nonneg (fun C _ => mul_nonneg (d'.mass_nonneg C) (hq C)))

omit Z₁ Z₂ h₁ h₂ in
lemma scaleEval_nonneg (d d' : Depth P) : 0 ≤ scaleEval d d' := by
  apply add_nonneg (massEval_nonneg _ (fun C => pairCell_nonneg _ _) _ _)
  apply Finset.sum_nonneg
  intro x _
  apply mul_nonneg _ (add_nonneg (d.potential_nonneg x) (d'.potential_nonneg x))
  simp only [prob,Finset.mem_univ,ite_true]; positivity

omit [NumberField K] in
include h₁ h₂ in
lemma integrable_scaleEval (hn : 2≤Fintype.card P) :
    AverageIntegrable Z₁ Z₂ (scaleEval (P:=P)) := by
  intro v
  exact (integrable_massEval Z₁ Z₂ h₁ h₂ hn _ v).add
    (integrable_potentialEval Z₁ Z₂ h₁ h₂ hn _ v)

lemma average_scaleEval (hn : 2≤Fintype.card P) :
    average Z₁ Z₂ h₁ h₂ scaleEval = overlapScale Z₁ Z₂ h₁ h₂ + potentialScale Z₁ Z₂ h₁ h₂ := by
  unfold scaleEval
  rw [average_add Z₁ Z₂ h₁ h₂
    (integrable_massEval Z₁ Z₂ h₁ h₂ hn _) (integrable_potentialEval Z₁ Z₂ h₁ h₂ hn _),
    average_massEval Z₁ Z₂ h₁ h₂ hn,average_potentialEval Z₁ Z₂ h₁ h₂ hn]
  rfl

omit [Fintype P] [NumberField K] in
lemma archMean_nonneg (f : Depth P → Depth P → ℝ) (hf : ∀ d d', 0≤f d d')
    (v : InfinitePlace K) : 0≤archMean Z₁ Z₂ f v := integral_nonneg (fun _ => hf _ _)

lemma archMean_le_average (f : Depth P → Depth P → ℝ) (hf : ∀ d d', 0≤f d d') :
    (∑ v, Arithmetic.archWeight v * archMean Z₁ Z₂ f v) ≤ average Z₁ Z₂ h₁ h₂ f := by
  apply le_add_of_nonneg_right
  exact mul_nonneg (by positivity) (Finset.sum_nonneg (fun v _ => hf _ _))

omit Z₁ Z₂ h₁ h₂ in
lemma archWeight_pos (v : InfinitePlace K) : 0<Arithmetic.archWeight v := by
  unfold Arithmetic.archWeight
  apply div_pos
  · exact_mod_cast (InfinitePlace.mult_pos (w := v))
  · exact_mod_cast Module.finrank_pos (R:=ℚ) (M:=K)

/-- Both the local scale and any nonnegative sum of variance cells are
controlled at one genuine complex embedding. -/
lemma select_arch (hn : 2≤Fintype.card P) (q : Finset P → ℝ) (hq : ∀ C, 0≤q C)
    (C ε : ℝ) (hC : 0≤C) (hε : 0<ε)
    (hscale : overlapScale Z₁ Z₂ h₁ h₂ + potentialScale Z₁ Z₂ h₁ h₂ ≤ C)
    (hvar : weightedIntegral (totalMass Z₁ Z₂ h₁ h₂) q ≤ ε) :
    ∃ v : InfinitePlace K,
      archMean Z₁ Z₂ scaleEval v ≤ 2*C+1 ∧ archMean Z₁ Z₂ (massEval q) v ≤ 2*ε := by
  apply weighted_select Arithmetic.archWeight _ _ C ε archWeight_pos Arithmetic.sum_archWeight
    (archMean_nonneg Z₁ Z₂ _ scaleEval_nonneg)
    (archMean_nonneg Z₁ Z₂ _ (massEval_nonneg q hq)) hC hε
  · exact (archMean_le_average Z₁ Z₂ h₁ h₂ _ scaleEval_nonneg).trans
      (by rw [average_scaleEval Z₁ Z₂ h₁ h₂ hn]; exact hscale)
  · exact (archMean_le_average Z₁ Z₂ h₁ h₂ _ (massEval_nonneg q hq)).trans
      (by rw [average_massEval Z₁ Z₂ h₁ h₂ hn]; exact hvar)

end WeakPinned.Bounded

end
end

end OAI
end

section
-- module Solutions.OAIQW_WeakPinned.LogBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u1 u2 u3 u4 u5 u6

section
/- Finite log-distance normalization. The diagonal is excluded in the energy
   and counted explicitly, with mass 1/n, in the ball estimate. -/

noncomputable section
open scoped BigOperators
namespace WeakPinned.Bounded
variable {P : Type u1} [Fintype P] [DecidableEq P]

omit [Fintype P] in
lemma logCost_nonneg (u : P → ℂ) (x y : P) : 0 ≤ logCost u x y := by
  unfold logCost; split_ifs <;> positivity

lemma logAverage_sum_bound (u : P → ℂ) (C : ℝ) (hn : 2 ≤ Fintype.card P)
    (hC : logAverage u ≤ C) :
    (∑ x, ∑ y, logCost u x y) ≤ C*(Fintype.card P : ℝ)*((Fintype.card P : ℝ)-1) := by
  have hnR : (2:ℝ) ≤ Fintype.card P := by exact_mod_cast hn
  have hp : 0 < (Fintype.card P : ℝ)*((Fintype.card P : ℝ)-1) := mul_pos (by linarith) (by linarith)
  simpa only [mul_assoc] using (div_le_iff₀ hp).mp hC

lemma logAverage_nonneg (u : P → ℂ) (hn : 2 ≤ Fintype.card P) : 0 ≤ logAverage u := by
  have hnR : (2:ℝ) ≤ Fintype.card P := by exact_mod_cast hn
  exact div_nonneg (Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => logCost_nonneg _ _ _))) (mul_nonneg (by linarith) (by linarith))

/-- One actual vertex serves as a tightness center: a row of the nonnegative
    distance-log matrix has at most the average row energy. -/
lemma log_center (u : P → ℂ) (C : ℝ) (hn : 2 ≤ Fintype.card P) (hC : logAverage u ≤ C) :
    ∃ x : P, (∑ y, logCost u x y) ≤ C*(Fintype.card P : ℝ) := by
  have hnR : (2:ℝ) ≤ Fintype.card P := by exact_mod_cast hn
  have hC0 : 0 ≤ C := (logAverage_nonneg u hn).trans hC
  have hsum := logAverage_sum_bound u C hn hC
  by_contra hnot
  push Not at hnot
  have hpos : Finset.univ.Nonempty (α:=P) := Finset.card_pos.mp (by simpa using (show 0<Fintype.card P by omega))
  have hs := Finset.sum_lt_sum_of_nonempty hpos (fun x _ => hnot x)
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul] at hs
  nlinarith

omit [Fintype P] in
lemma log_cost_large (u : P → ℂ) (R : ℝ) (hR : 1 < R) (x y : P) (hxy : R < ‖u x-u y‖) :
    Real.log R ≤ logCost u x y := by
  have hne : x ≠ y := by intro he; subst y; simp at hxy; linarith
  rw [logCost,ite_eq_right hne]
  have hl := Real.log_le_log (by linarith : 0<R) hxy.le
  exact hl.trans (le_abs_self _)

/-- A normalized empirical tail bound from the average logarithmic cost. -/
lemma normalized_tail_card (u : P → ℂ) (C : ℝ) (x : P)
    (hx : (∑ y, logCost u x y) ≤ C*(Fintype.card P : ℝ))
    (hn : 2 ≤ Fintype.card P) (R : ℝ) (hR : 1 < R) :
    ((Finset.univ.filter (fun y => R < ‖u y-u x‖)).card : ℝ)/(Fintype.card P : ℝ) ≤ C/Real.log R := by
  let A := Finset.univ.filter (fun y => R < ‖u y-u x‖)
  have hlog := Real.log_pos hR
  have hn0 : (0:ℝ)<Fintype.card P := by exact_mod_cast (show 0<Fintype.card P by omega)
  have hs : (A.card : ℝ)*Real.log R ≤ ∑ y, logCost u x y := by
    calc
      (A.card : ℝ)*Real.log R = ∑ y ∈ A, Real.log R := by simp
      _ ≤ ∑ y ∈ A, logCost u x y := by
        apply Finset.sum_le_sum
        intro y hy
        apply log_cost_large u R hR x y
        simpa only [norm_sub_rev] using (Finset.mem_filter.mp hy).2
      _ ≤ ∑ y, logCost u x y := Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.subset_univ _) (fun y _ _ => logCost_nonneg u x y)
  apply (div_le_div_iff₀ hn0 hlog).mpr
  nlinarith

omit [Fintype P] in
lemma log_cost_close (u : P → ℂ) (hu : Function.Injective u) (z : ℂ) (r : ℝ)
    (_hr : 0<r) (_hr2 : r<1/2) (x y : P) (hx : ‖u x-z‖<r) (hy : ‖u y-z‖<r) (hxy : x≠y) :
    -Real.log (2*r) ≤ logCost u x y := by
  have hne : u x-u y ≠ 0 := sub_ne_zero.mpr (fun h => hxy (hu h))
  have hp := norm_pos_iff.mpr hne
  have hd : ‖u x-u y‖<2*r := by
    have hh := norm_sub_le_norm_sub_add_norm_sub (u x) z (u y)
    rw [norm_sub_rev z] at hh
    linarith
  have hh := Real.log_le_log hp hd.le
  rw [logCost,ite_eq_right hxy]
  have habs := neg_le_abs (Real.log ‖u x-u y‖)
  linarith

/-- The true n^-1 diagonal term in the concentration estimate. The points may
    be arbitrarily close; injectivity is the only geometric condition. -/
lemma small_ball_card (u : P → ℂ) (hu : Function.Injective u) (C : ℝ)
    (hn : 2 ≤ Fintype.card P) (hC : logAverage u ≤ C) (z : ℂ) (r : ℝ)
    (hr : 0<r) (hr2 : r<1/2) :
    (((Finset.univ.filter (fun x => ‖u x-z‖<r)).card : ℝ)/(Fintype.card P : ℝ))^2 ≤
      1/(Fintype.card P : ℝ)+C/(-Real.log (2*r)) := by
  let A := Finset.univ.filter (fun x => ‖u x-z‖<r)
  let T := -Real.log (2*r)
  have hT : 0<T := by dsimp [T]; exact neg_pos.mpr (Real.log_neg (by positivity) (by linarith))
  have hnR : (2:ℝ) ≤ Fintype.card P := by exact_mod_cast hn
  have hn0 : (0:ℝ)<Fintype.card P := by linarith
  have hC0 : 0 ≤ C := (logAverage_nonneg u hn).trans hC
  have ha : (A.card : ℝ) ≤ Fintype.card P := by exact_mod_cast Finset.card_le_univ A
  have ha0 : (0:ℝ) ≤ A.card := Nat.cast_nonneg _
  have hsum := logAverage_sum_bound u C hn hC
  have hpoint : ∀ x y : P, (if x∈A ∧ y∈A ∧ x≠y then T else 0) ≤ logCost u x y := by
    intro x y
    split_ifs with h
    · exact log_cost_close u hu z r hr hr2 x y (Finset.mem_filter.mp h.1).2
        (Finset.mem_filter.mp h.2.1).2 h.2.2
    · exact logCost_nonneg _ _ _
  have hs := Finset.sum_le_sum (s:=Finset.univ) (fun x _ =>
    Finset.sum_le_sum (s:=Finset.univ) (fun y _ => hpoint x y))
  have heq : (∑ x : P, ∑ y : P, if x∈A ∧ y∈A ∧ x≠y then T else 0) =
      (A.card : ℝ)*((A.card : ℝ)-1)*T := by
    have hrw (x : P) : (∑ y : P, if x∈A ∧ y∈A ∧ x≠y then T else 0) =
        if x∈A then ((A.card : ℝ)-1)*T else 0 := by
      by_cases hx : x∈A
      · simp only [hx,true_and,ite_eq_left]
        have hf : Finset.univ.filter (fun y => y∈A ∧ x≠y)=A.erase x := by
          ext y; simp [ne_comm, and_comm]
        rw [← Finset.sum_filter,hf,Finset.sum_const,Finset.card_erase_of_mem hx,nsmul_eq_mul]
        rw [Nat.cast_sub (Finset.one_le_card.mpr ⟨x,hx⟩),Nat.cast_one]
      · simp [hx]
    simp_rw [hrw]
    rw [← Finset.sum_filter]
    simp only [Finset.filter_mem_eq_inter,Finset.univ_inter,Finset.sum_const,nsmul_eq_mul]
    ring
  rw [heq] at hs
  have hcub : (A.card : ℝ)^2*T ≤ (Fintype.card P : ℝ)*T+C*(Fintype.card P : ℝ)^2 := by
    have hCT := mul_nonneg hC0 hn0.le
    have hAT := mul_le_mul_of_nonneg_right ha hT.le
    nlinarith
  change ((A.card : ℝ)/(Fintype.card P : ℝ))^2 ≤ 1/(Fintype.card P : ℝ)+C/T
  rw [div_pow]
  apply (div_le_iff₀ (sq_pos_of_pos hn0)).mpr
  apply (mul_le_mul_iff_left₀ hT).mp
  have he : (1/(Fintype.card P : ℝ)+C/T)*(Fintype.card P : ℝ)^2*T =
      (Fintype.card P : ℝ)*T+C*(Fintype.card P : ℝ)^2 := by field_simp [ne_of_gt hn0, ne_of_gt hT]
  rw [he]
  exact hcub

end WeakPinned.Bounded

namespace WeakPinned.Bounded
open Hierarchy Variance Global NumberField MeasureTheory
open scoped BigOperators

lemma weighted_deviation {J : Type u2} [Fintype J] (p f : J → ℝ) (a : ℝ)
    (hp : ∀ j, 0≤ p j) (hs : ∑ j, p j=1) :
    (∑ j, p j*|f j-∑ k, p k*f k|) ≤ 2*∑ j, p j*|f j-a| := by
  have hm : |a-∑ j, p j*f j| ≤ ∑ j, p j*|f j-a| := by
    have he : a-(∑ j,p j*f j) = ∑ j,p j*(a-f j) := by
      simp only [mul_sub,Finset.sum_sub_distrib,← Finset.sum_mul,hs,one_mul]
    rw [he]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    apply Finset.sum_le_sum
    intro j _
    rw [abs_mul,abs_of_nonneg (hp j),abs_sub_comm]
  calc
    _ ≤ ∑ j, p j*(|f j-a|+|a-∑ k,p k*f k|) := by
      apply Finset.sum_le_sum
      intro j _
      exact mul_le_mul_of_nonneg_left (abs_sub_le (f j) a _) (hp j)
    _ = (∑ j,p j*|f j-a|)+|a-∑ k,p k*f k| := by
      simp only [mul_add,Finset.sum_add_distrib,← Finset.sum_mul,hs,one_mul]
    _ ≤ _ := by linarith

variable {P : Type u3} [Fintype P] [DecidableEq P]

lemma pairWeight_nonneg (hn : 2≤ Fintype.card P) (x y : P) : 0 ≤ pairProb Finset.univ x y := by
  have hn' : (2:ℝ)≤ Fintype.card P := by exact_mod_cast hn
  simp only [pairProb,Finset.mem_univ,true_and,Finset.card_univ]
  split_ifs
  · exact div_nonneg zero_le_one (mul_nonneg (by positivity) (by linarith))
  · exact le_rfl

lemma pairMean_one (hn : 2≤ Fintype.card P) : pairMean (fun _ _ : P => 1)=1 := by
  simp only [pairMean,mul_one,sum_pairProb Finset.univ (by simpa using hn)]
  apply sum_prob
  exact Finset.card_pos.mp (by simpa using (show 0<Fintype.card P by omega))

lemma pairMean_mono (hn : 2≤ Fintype.card P) {f g : P → P → ℝ}
    (h : ∀ x y, x≠y → f x y≤ g x y) : pairMean f≤ pairMean g := by
  apply Finset.sum_le_sum
  intro x _
  apply Finset.sum_le_sum
  intro y _
  by_cases hxy : x=y
  · subst y; simp [pairProb]
  · exact mul_le_mul_of_nonneg_left (h x y hxy) (pairWeight_nonneg hn x y)

lemma pairMean_add (f g : P → P → ℝ) : pairMean (fun x y => f x y+g x y)=pairMean f+pairMean g := by
  simp only [pairMean,mul_add,Finset.sum_add_distrib]

lemma pairMean_left (hn : 2≤ Fintype.card P) (f : P → ℝ) :
    pairMean (fun x _ => f x)=∑ x, prob Finset.univ x*f x := by
  simp only [pairMean,← Finset.sum_mul,sum_pairProb Finset.univ (by simpa using hn)]

lemma pairMean_right (hn : 2≤ Fintype.card P) (f : P → ℝ) :
    pairMean (fun _ y => f y)=∑ y, prob Finset.univ y*f y := by
  rw [pairMean,Finset.sum_comm]
  simp_rw [pairProb_symm Finset.univ _ _,← Finset.sum_mul,sum_pairProb Finset.univ (by simpa using hn)]

lemma pairMean_deviation (hn : 2≤ Fintype.card P) (f : P → P → ℝ) (a : ℝ) :
    pairMean (fun x y => |f x y-pairMean f|)≤2*pairMean (fun x y => |f x y-a|) := by
  have h := weighted_deviation (fun z : P×P => pairProb Finset.univ z.1 z.2)
    (fun z => f z.1 z.2) a (fun z => pairWeight_nonneg hn z.1 z.2)
    (by simpa only [Fintype.sum_prod_type,pairMean,mul_one] using pairMean_one (P:=P) hn)
  simpa only [Fintype.sum_prod_type,pairMean] using h

lemma pairMean_overlap (d : Depth P) (_hn : 2≤ Fintype.card P) :
    pairMean (weightedOverlap d.mass)=weightedIntegral d.mass (pairCell Finset.univ) := by
  exact (weighted_pair d.mass (pairProb Finset.univ)).symm

lemma depth_center_bound (d : Depth P) (hn : 2≤ Fintype.card P) :
    pairMean (fun x y => |d.value x y-d.M|) ≤ weightedIntegral d.mass (pairCell Finset.univ)+
      2*(∑ x, prob Finset.univ x*d.potential x) := by
  calc
    _ ≤ pairMean (fun x y => weightedOverlap d.mass x y+d.potential x+d.potential y) := by
      apply pairMean_mono hn
      intro x y hxy
      rw [show weightedOverlap d.mass x y=d.overlapLength x y hxy from d.mass_overlap hn x y hxy,
        d.depth_identity hn x y hxy]
      have hL := d.overlapLength_nonneg x y hxy
      have hx := d.potential_nonneg x
      have hy := d.potential_nonneg y
      exact abs_le.mpr ⟨by linarith,by linarith⟩
    _ = _ := by rw [pairMean_add,pairMean_add,pairMean_overlap d hn,pairMean_left hn,pairMean_right hn]; ring

end WeakPinned.Bounded

namespace WeakPinned.Bounded
open Hierarchy Variance Global NumberField MeasureTheory
open scoped BigOperators
variable {P : Type u4} [Fintype P] [DecidableEq P]

lemma singleScale_nonneg (d : Depth P) : 0 ≤ singleScale d := by
  refine add_nonneg (Finset.sum_nonneg (fun C _ => mul_nonneg (d.mass_nonneg C) (pairCell_nonneg _ _))) ?_
  apply Finset.sum_nonneg
  intro x _
  apply mul_nonneg _ (d.potential_nonneg x)
  simp only [prob,Finset.mem_univ,ite_true]; positivity

lemma scaleEval_eq (d d' : Depth P) : scaleEval d d'=singleScale d+singleScale d' := by
  simp only [scaleEval,singleScale,massEval,potentialEval,mul_add,Finset.sum_add_distrib]; ring

lemma singleScale_le_left (d d' : Depth P) : singleScale d≤ scaleEval d d' := by
  rw [scaleEval_eq]; exact le_add_of_nonneg_right (singleScale_nonneg d')

lemma raw_center_grid_bound (u : P → ℂ) (d : Depth P) (ω : Grid.FullSample)
    (hn : 2≤ Fintype.card P) (hd : ∀ x y, x≠y → d.value x y=Grid.depth ω (u x) (u y)) :
    pairMean (fun x y => |rawDepth u x y-pairMean (rawDepth u)|) ≤
      4*singleScale d+2*pairMean (pairGridError u ω) := by
  have h1 := pairMean_deviation hn (rawDepth u) d.M
  have h2 : pairMean (fun x y => |rawDepth u x y-d.M|) ≤
      pairMean (fun x y => |d.value x y-d.M|)+pairMean (pairGridError u ω) := by
    rw [← pairMean_add]
    apply pairMean_mono hn
    intro x y hxy
    simp only [pairGridError,ite_eq_right hxy]
    have he : rawDepth u x y-d.M=(d.value x y-d.M)-Grid.error ω (u x) (u y) := by
      rw [hd x y hxy]; simp only [rawDepth,Grid.error]; ring
    rw [he]
    exact abs_sub _ _
  have h3 := depth_center_bound d hn
  have hL : 0≤ weightedIntegral d.mass (pairCell Finset.univ) :=
    Finset.sum_nonneg (fun C _ => mul_nonneg (d.mass_nonneg C) (pairCell_nonneg _ _))
  unfold singleScale
  linarith

lemma pairGridError_integrable (u : P → ℂ) (hu : Function.Injective u) :
    Integrable (fun ω => pairMean (pairGridError u ω)) Grid.fullLaw := by
  apply integrable_finsetSum
  intro x _
  apply integrable_finsetSum
  intro y _
  by_cases hxy : x=y
  · simp only [pairGridError,hxy,ite_true,mul_zero]; exact integrable_zero _ _ _
  · simpa only [pairGridError,ite_eq_right hxy] using
      ((Grid.error_integrable_full (hu.ne hxy)).abs.const_mul (pairProb Finset.univ x y))

lemma mean_pairGridError (u : P → ℂ) (hu : Function.Injective u) (hn : 2≤ Fintype.card P) :
    (∫ ω, pairMean (pairGridError u ω) ∂ Grid.fullLaw)≤4 := by
  have hi (x y : P) : Integrable (fun ω => pairProb Finset.univ x y*pairGridError u ω x y) Grid.fullLaw := by
    by_cases hxy : x=y
    · simp only [pairGridError,hxy,ite_true,mul_zero]; exact integrable_zero _ _ _
    · simpa only [pairGridError,ite_eq_right hxy] using
        ((Grid.error_integrable_full (hu.ne hxy)).abs.const_mul (pairProb Finset.univ x y))
  simp only [pairMean]
  rw [integral_finsetSum _ (fun x _ => integrable_finsetSum _ (fun y _ => hi x y))]
  simp_rw [integral_finsetSum _ (fun y _ => hi _ y),integral_const_mul]
  calc
    _ ≤ ∑ x,∑ y,pairProb Finset.univ x y*4 := by
      apply Finset.sum_le_sum; intro x _
      apply Finset.sum_le_sum; intro y _
      apply mul_le_mul_of_nonneg_left _ (pairWeight_nonneg hn x y)
      by_cases hxy : x=y
      · simp only [pairGridError,hxy,ite_true,integral_zero]; norm_num
      · simpa only [pairGridError,ite_eq_right hxy] using Grid.mean_abs_error_full (hu.ne hxy)
    _ = 4 := by
      have h := pairMean_one (P:=P) hn
      simp only [pairMean,mul_one] at h
      simp only [← Finset.sum_mul,h,one_mul]

variable {K : Type u5} [Field K] [NumberField K]
variable (Z₁ Z₂ : P → K) (h₁ : Function.Injective Z₁) (h₂ : Function.Injective Z₂)

omit [NumberField K] in
include h₁ h₂ in
lemma arch_log_center_bound (hn : 2≤ Fintype.card P) (v : InfinitePlace K) :
    pairMean (fun x y => |rawDepth (fun x => v.embedding (Z₁ x)) x y-
      pairMean (rawDepth (fun x => v.embedding (Z₁ x)))|) ≤ 4*archMean Z₁ Z₂ scaleEval v+8 := by
  let u : P → ℂ := fun x => v.embedding (Z₁ x)
  let L := pairMean (fun x y => |rawDepth u x y-pairMean (rawDepth u)|)
  have hu : Function.Injective u := v.embedding.injective.comp h₁
  have he := mean_pairGridError u hu hn
  have hbound : ∀ᵐ ω ∂ Grid.fullLaw, L≤4*scaleEval (arch Z₁ v ω) (arch Z₂ v ω)+2*pairMean (pairGridError u ω) := by
    filter_upwards [good_ae Z₁ h₁ v] with ω hgood
    have h := raw_center_grid_bound u (arch Z₁ v ω) ω hn (fun x y hxy => by simp [arch,hgood,hxy,u])
    have hs := singleScale_le_left (arch Z₁ v ω) (arch Z₂ v ω)
    dsimp only [L]
    linarith
  have hh := integral_mono_ae (integrable_const L)
    (((integrable_scaleEval Z₁ Z₂ h₁ h₂ hn v).const_mul 4).add ((pairGridError_integrable u hu).const_mul 2)) hbound
  simp only [Pi.add_apply] at hh
  rw [integral_add ((integrable_scaleEval Z₁ Z₂ h₁ h₂ hn v).const_mul 4)
    ((pairGridError_integrable u hu).const_mul 2),integral_const_mul,integral_const_mul] at hh
  simp only [integral_const,MeasureTheory.probReal_univ,one_smul] at hh
  change L≤4*archMean Z₁ Z₂ scaleEval v+8
  change L≤4*archMean Z₁ Z₂ scaleEval v+2*(∫ ω,pairMean (pairGridError u ω) ∂ Grid.fullLaw) at hh
  linarith

end WeakPinned.Bounded

namespace WeakPinned.Bounded
open Variance
variable {P : Type u6} [Fintype P] [DecidableEq P]

lemma logNormalize_injective (u : P → ℂ) (hu : Function.Injective u) :
    Function.Injective (logNormalize u) := by
  intro x y h
  apply hu
  exact mul_left_cancel₀ (by exact_mod_cast (Real.exp_ne_zero (pairMean (rawDepth u)))) h

lemma logAverage_pairMean (u : P → ℂ) :
    logAverage u=pairMean (fun x y => |Real.log ‖u x-u y‖|) := by
  unfold logAverage pairMean
  simp only [Finset.sum_div]
  apply Finset.sum_congr rfl; intro x _
  apply Finset.sum_congr rfl; intro y _
  by_cases hxy : x=y
  · simp [pairProb,logCost,hxy]
  · simp [pairProb,logCost,hxy,div_eq_mul_inv,mul_comm]

lemma logNormalize_log (u : P → ℂ) (hu : Function.Injective u) (x y : P) (hxy : x≠y) :
    Real.log ‖logNormalize u x-logNormalize u y‖=pairMean (rawDepth u)+Real.log ‖u x-u y‖ := by
  have hz : ‖u x-u y‖≠0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr (hu.ne hxy))
  simp only [logNormalize,← mul_sub,norm_mul,Complex.norm_real,Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _)]
  rw [Real.log_mul (Real.exp_ne_zero _) hz,Real.log_exp]

lemma logNormalize_bound (u : P → ℂ) (hu : Function.Injective u) (hn : 2≤Fintype.card P) :
    logAverage (logNormalize u)=pairMean (fun x y => |rawDepth u x y-pairMean (rawDepth u)|) := by
  rw [logAverage_pairMean]
  apply le_antisymm
  all_goals
    apply pairMean_mono hn
    intro x y hxy
    rw [logNormalize_log u hu x y hxy]
    have he : |pairMean (rawDepth u)+Real.log ‖u x-u y‖|=|rawDepth u x y-pairMean (rawDepth u)| := by
      rw [← abs_neg]; congr 1; unfold rawDepth; ring
    rw [he]

end WeakPinned.Bounded

end
end

end OAI
end

section
-- module Solutions.OAIQW_WeakPinned.EmpiricalCompactness
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u1 u2 u3 u4

section
noncomputable section
open MeasureTheory Filter Set
open scoped Topology BigOperators ENNReal
namespace WeakPinned.Bounded
attribute [local instance] Classical.propDecidable

attribute [local instance] OAI.WeakPinned.Bounded.instMeasurableSpaceSphere_2
attribute [local instance] OAI.WeakPinned.Bounded.instBorelSpaceSphere_2
variable {V : Type u1} {X : Type u2} [Fintype V] [MeasurableSpace X] [MeasurableSingletonClass X]

lemma uniformLaw_apply (U : V → X) (s : Set X) [DecidablePred (fun x => U x∈s)] :
    uniformLaw U s=ENNReal.ofReal (((Finset.univ.filter (fun x => U x∈s)).card:ℝ)/(Fintype.card V:ℝ)) := by
  simp only [uniformLaw,finiteLaw,Measure.finsetSum_apply,Measure.smul_apply,
    smul_eq_mul,Measure.dirac_apply,Set.indicator_apply,Pi.one_apply,mul_ite,mul_one,mul_zero]
  rw [← Finset.sum_filter,Finset.sum_const,nsmul_eq_mul]
  rw [div_eq_mul_inv,ENNReal.ofReal_mul (Nat.cast_nonneg _),ENNReal.ofReal_natCast]

variable {P : ℕ → Type u4} [∀ n,Fintype (P n)] [∀ n,DecidableEq (P n)]

lemma normalized_empirical_nonatomic (u : ∀ n,P n → ℂ) (x : ∀ n,P n)
    (hu : ∀ n,Function.Injective (u n)) (hn : ∀ n,2≤Fintype.card (P n))
    (hcard : Tendsto (fun n => (Fintype.card (P n):ℝ)) atTop atTop)
    (C : ℝ) (hC : 0≤C) (hlog : ∀ n,logAverage (u n)≤C)
    (hx : ∀ n,(∑ y,logCost (u n) (x n) y)≤C*(Fintype.card (P n):ℝ))
    (β : ProbabilityMeasure Sphere)
    (ht : Tendsto (fun n => uniformProbability (fun y => ((u n y-u n (x n)):Sphere))
      (by have := hn n; omega)) atTop (𝓝 β)) :
    NullSingletonClass (β:Measure Sphere) := by
  apply weak_limit_nonatomic ht
  · intro ε hε
    let R := Real.exp (C/ε+1)
    have hR : 1<R := by dsimp [R]; rw [Real.one_lt_exp_iff]; positivity
    refine ⟨R,Eventually.of_forall (fun n => ?_)⟩
    change uniformLaw (fun y => ((u n y-u n (x n)):Sphere)) _≤_
    rw [uniformLaw_apply]
    apply ENNReal.ofReal_le_ofReal
    have hh := normalized_tail_card (u n) C (x n) (hx n) (hn n) R hR
    have hs : (Finset.univ.filter (fun y => (((u n y-u n (x n)):Sphere))∈
        (OnePoint.some '' Metric.closedBall (0:ℂ) R)ᶜ))=
        Finset.univ.filter (fun y => R<‖u n y-u n (x n)‖) := by
      ext y
      simp [Metric.mem_closedBall,dist_eq_norm]
    change (((Finset.univ.filter (fun y => (((u n y-u n (x n)):Sphere))∈
      (OnePoint.some '' Metric.closedBall (0:ℂ) R)ᶜ)).card:ℝ)/(Fintype.card (P n):ℝ))≤ε
    rw [hs]
    apply hh.trans
    rw [show Real.log R=C/ε+1 by simp [R]]
    apply (div_le_iff₀ (by positivity : 0<C/ε+1)).mpr
    have he : ε*(C/ε+1)=C+ε := by field_simp
    rw [he]
    linarith
  · intro z ε hε
    let T := 2*C/ε^2+1
    let r := Real.exp (-T)/2
    have hT : 0<T := by dsimp [T]; positivity
    have hr : 0<r := by dsimp [r]; positivity
    have hr2 : r<1/2 := by dsimp [r]; have hh := Real.exp_lt_one_iff.mpr (neg_neg_of_pos hT); linarith
    have hsmall : Tendsto (fun n => 1/(Fintype.card (P n):ℝ)) atTop (𝓝 0) := by simpa only [one_div,Function.comp_def] using (tendsto_inv_atTop_zero.comp hcard)
    have hsmall' : ∀ᶠ n in atTop,1/(Fintype.card (P n):ℝ)≤ε^2/2 :=
      hsmall.eventually_le_const (by positivity)
    refine ⟨r,hr,hsmall'.mono (fun n hn' => ?_)⟩
    change uniformLaw (fun y => ((u n y-u n (x n)):Sphere)) _≤_
    rw [uniformLaw_apply]
    apply ENNReal.ofReal_le_ofReal
    have hs : (Finset.univ.filter (fun y => (((u n y-u n (x n)):Sphere))∈
        OnePoint.some '' Metric.ball z r))=
        Finset.univ.filter (fun y => ‖u n y-(z+u n (x n))‖<r) := by
      ext y
      simp only [Finset.mem_filter,Finset.mem_univ,true_and,Set.mem_image,OnePoint.coe_eq_coe,exists_eq_right,
        Metric.mem_ball,dist_eq_norm]
      ring_nf
    rw [hs]
    have hh := small_ball_card (u n) (hu n) C (hn n) (hlog n) (z+u n (x n)) r hr hr2
    have hl : -Real.log (2*r)=T := by
      rw [show 2*r=Real.exp (-T) by dsimp [r]; ring,Real.log_exp,neg_neg]
    rw [hl] at hh
    have hCT : C/T≤ε^2/2 := by
      apply (div_le_iff₀ hT).mpr
      have he : ε^2/2*T=C+ε^2/2 := by dsimp [T]; field_simp
      rw [he]
      linarith [sq_nonneg ε]
    nlinarith

end WeakPinned.Bounded

end
end

end OAI
end

section
-- module Solutions.OAIQW_WeakPinned.FiniteMixtures
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u1 u2 u3 u4 u5 u6 u7

section
noncomputable section
open MeasureTheory Filter
open scoped BigOperators Topology ENNReal
namespace WeakPinned.Bounded

variable {I : Type u1} {V : Type u2} {X : Type u3} {Y : Type u4} [Fintype I] [Fintype V]
  [MeasurableSpace X] [MeasurableSpace Y]

lemma tripleLaw_edge (w : I → ℝ) (p : I → V → ℝ) (U : I × V → X)
    (hw : ∀ i,0≤w i) (hp : ∀ i x,0≤p i x) (hpsum : ∀ i,∑ x,p i x=1) :
    finiteLaw (tripleWeight w p) (fun r => U (r.1,r.2.1))=finiteLaw (edgeWeight w p) U := by
  unfold finiteLaw tripleWeight edgeWeight
  simp only [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro x _
  rw [show (∑ z,∑ t, ENNReal.ofReal (w i*p i x*p i z*p i t) • Measure.dirac (U (i,x))) =
    ∑ z,ENNReal.ofReal (w i*p i x*p i z) • Measure.dirac (U (i,x)) by
      apply Finset.sum_congr rfl
      intro z _
      rw [← Finset.sum_smul,← ENNReal.ofReal_sum_of_nonneg (fun t _ => mul_nonneg (mul_nonneg (mul_nonneg (hw i) (hp i x)) (hp i z)) (hp i t)),
        ← Finset.mul_sum,hpsum,mul_one]]
  rw [← Finset.sum_smul,← ENNReal.ofReal_sum_of_nonneg (fun z _ => mul_nonneg (mul_nonneg (hw i) (hp i x)) (hp i z)),
    ← Finset.mul_sum,hpsum,mul_one]

lemma finiteLaw_mono (w v : I → ℝ) (U : I → X) (hle : ∀ i,w i≤v i) :
    finiteLaw w U≤finiteLaw v U := by
  apply Measure.le_iff.mpr
  intro s hs
  simp only [finiteLaw,Measure.finsetSum_apply,Measure.smul_apply,smul_eq_mul]
  apply Finset.sum_le_sum
  intro i _
  gcongr
  exact hle i

lemma finiteLaw_prod (w : I → ℝ) (v : V → ℝ) (U : I → X) (W : V → Y)
    (hw : ∀ i,0≤w i) :
    (finiteLaw w U).prod (finiteLaw v W)=
      finiteLaw (fun r : I × V => w r.1*v r.2) (fun r => (U r.1,W r.2)) := by
  simp only [finiteLaw,← Measure.sum_fintype,Measure.prod_sum,
    Measure.prod_smul_left,Measure.prod_smul_right,Measure.dirac_prod_dirac,
    smul_smul,ENNReal.ofReal_mul (hw _),mul_comm]

lemma finiteLaw_smul (w : I → ℝ) (U : I → X) (c : ℝ) (hc : 0≤c) :
    finiteLaw (fun i => c*w i) U=ENNReal.ofReal c •finiteLaw w U := by
  simp only [finiteLaw,ENNReal.ofReal_mul hc,Finset.smul_sum,smul_smul]

end WeakPinned.Bounded

end
end
section
noncomputable section
open MeasureTheory Filter
open scoped BigOperators Topology ENNReal
namespace WeakPinned.Bounded
open Variance
variable {V : Type u5} {I : Type u6} {X : Type u7} [Fintype V] [DecidableEq V] [Fintype I]
  [MeasurableSpace X] [MeasurableSingletonClass X]
  [TopologicalSpace X] [BorelSpace X] [HasOuterApproxClosed X]
variable (G : Core.Fibers V I)

lemma graph_edge_eval (F : V → V → ℝ) :
    (∑ e,G.fiberWeight e*∑ y,prob (G.targets e) y*F (G.source e) y)=
      ∑ x,∑ y,G.edgeLaw x y*F x y := by
  rw [← G.incoming_eval]
  simp only [Finset.mul_sum,← mul_assoc,G.sampling_conditional]
  exact Finset.sum_comm

lemma graph_edge_law (U : V → V → X) (hG : 0<G.edgeCount)
    (hB : ∀ e,(G.targets e).Nonempty) :
    finiteLaw (edgeWeight G.fiberWeight (fun e => prob (G.targets e)))
      (fun r => U (G.source r.1) r.2)=
    finiteLaw (fun r : V × V => G.edgeLaw r.1 r.2) (fun r => U r.1 r.2) := by
  have hw (r : I × V) : 0≤edgeWeight G.fiberWeight (fun e => prob (G.targets e)) r :=
    mul_nonneg (G.fiberWeight_nonneg _) (Core.Fibers.prob_nn _ _)
  let : IsProbabilityMeasure (finiteLaw (edgeWeight G.fiberWeight (fun e => prob (G.targets e)))
      (fun r => U (G.source r.1) r.2)) := finiteLaw_probability _ _ hw
        (sum_edgeWeight _ _ (G.sum_fiberWeight hG) (fun e => sum_prob _ (hB e)))
  let : IsProbabilityMeasure (finiteLaw (fun r : V × V => G.edgeLaw r.1 r.2) (fun r => U r.1 r.2)) :=
    finiteLaw_probability _ _ (fun r => G.edgeLaw_nonneg _ _)
      (by simpa only [Fintype.sum_prod_type] using G.sum_edgeLaw hG)
  apply ext_of_forall_integral_eq_of_IsFiniteMeasure
  intro f
  rw [integral_finiteLaw _ _ hw,integral_finiteLaw _ _ (fun r => G.edgeLaw_nonneg _ _)]
  simp only [edgeWeight,Fintype.sum_prod_type,mul_assoc,← Finset.mul_sum]
  exact graph_edge_eval G (fun x y => f (U x y))

omit G in
lemma pairProb_le_uniform (hn : 2≤Fintype.card V) (x y : V) :
    pairProb Finset.univ x y≤2*(Fintype.card V:ℝ)⁻¹*(Fintype.card V:ℝ)⁻¹ := by
  have hnR : (2:ℝ)≤Fintype.card V := by exact_mod_cast hn
  have hn0 : (0:ℝ)<Fintype.card V := by linarith
  simp only [pairProb,Finset.mem_univ,true_and,Finset.card_univ]
  split_ifs
  · field_simp
    apply (div_le_iff₀ (by linarith : 0<(Fintype.card V:ℝ)-1)).mpr
    nlinarith
  · positivity

omit [Fintype I] [MeasurableSingletonClass X] [TopologicalSpace X] [BorelSpace X] [HasOuterApproxClosed X] in
lemma graph_domination (U : V → X) (hn : 2≤Fintype.card V) (M : ℝ) (hM : 0≤M)
    (hdom : ∀ x y,G.edgeLaw x y≤M*pairProb Finset.univ x y) :
    finiteLaw (fun r : V × V => G.edgeLaw r.1 r.2) (fun r => (U r.1,U r.2))≤
      ENNReal.ofReal (2*M) • (uniformLaw U).prod (uniformLaw U) := by
  rw [uniformLaw,finiteLaw_prod _ _ _ _ (fun _ => by positivity),← finiteLaw_smul _ _ _ (by positivity)]
  apply finiteLaw_mono
  intro r
  calc
    _ ≤ M*pairProb Finset.univ r.1 r.2 := hdom _ _
    _ ≤ M*(2*(Fintype.card V:ℝ)⁻¹*(Fintype.card V:ℝ)⁻¹) :=
      mul_le_mul_of_nonneg_left (pairProb_le_uniform hn _ _) hM
    _ = _ := by ring

end WeakPinned.Bounded

end
end

end OAI
end

section
-- module Solutions.OAIQW_WeakPinned.ChartLimits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u1 u2 u3 u4 u5 u6 u7 u8 u9 u10 u11 u12

section
noncomputable section
open MeasureTheory Filter Set
open scoped Topology
namespace WeakPinned.Bounded

variable {X : Type u1} {Y : Type u2} [MeasurableSpace X] [MeasurableSpace Y]

lemma chart_probability (j : X → Y) (hj : MeasurableEmbedding j)
    (μ : Measure Y) [IsProbabilityMeasure μ] (hfin : ∀ᵐ y ∂  μ,y∈range j) :
    IsProbabilityMeasure (μ.comap j) := by
  constructor
  rw [hj.comap_apply,image_univ]
  exact measure_eq_measure_of_null_sdiff (subset_univ _) (by
    convert ae_iff.mp hfin using 2
    ext y
    simp) |>.trans measure_univ

lemma chart_map_comap (j : X → Y) (hj : MeasurableEmbedding j)
    (μ : Measure Y) (hfin : ∀ᵐ y ∂  μ,y∈range j) : (μ.comap j).map j=μ := by
  rw [hj.map_comap]
  exact Measure.restrict_eq_self_of_ae_mem hfin

lemma chart_ae_iff (j : X → Y) (hj : MeasurableEmbedding j) (μ : Measure Y)
    {s : Set X} : (∀ᵐ x ∂  μ.comap j,x∈s) ↔ μ (j '' sᶜ)=0 := by
  rw [ae_iff,hj.comap_apply]
  rfl

variable [TopologicalSpace X] [TopologicalSpace Y] [BorelSpace X] [BorelSpace Y]

lemma weak_chart_closed (j : X → Y) (hj : Topology.IsOpenEmbedding j)
    [HasOuterApproxClosed Y] (α : ℕ → ProbabilityMeasure Y) (β : ProbabilityMeasure Y)
    (ht : Tendsto α atTop (𝓝 β)) (s : Set X) (hs : IsClosed s)
    (hα : ∀ n,(α n : Measure Y) (j '' sᶜ)=0) :
    ∀ᵐ x ∂  (β : Measure Y).comap j,x∈s := by
  rw [chart_ae_iff j hj.measurableEmbedding]
  apply le_antisymm _ zero_le
  apply (ProbabilityMeasure.le_liminf_measure_open_of_tendsto ht
    (hj.isOpenMap _ hs.isOpen_compl)).trans
  apply liminf_le_of_frequently_le'
  exact (Eventually.of_forall (fun n => le_of_eq (hα n))).frequently

end WeakPinned.Bounded

end
end
section
noncomputable section
open MeasureTheory Filter Set
open scoped Topology
namespace WeakPinned.Bounded

lemma map_transport {A : Type u3} {B : Type u4} {X : Type u5} {Y : Type u6} [MeasurableSpace A] [MeasurableSpace B]
    [MeasurableSpace X] [MeasurableSpace Y] (j : A → X) (k : B → Y)
    (hj : Measurable j) (hk : MeasurableEmbedding k)
    (f : A → B) (g : X → Y) (hf : Measurable f) (hg : Measurable g)
    (μ : Measure A) (ν : Measure B) (hcomm : k ∘ f=g ∘ j)
    (hm : (μ.map j).map g=ν.map k) : μ.map f=ν := by
  apply hk.map_injective
  rw [Measure.map_map hk.measurable hf,hcomm,← Measure.map_map hg hj]
  exact hm

lemma map_pull_ac {A : Type u7} {B : Type u8} [MeasurableSpace A] [MeasurableSpace B]
    (j : A → B) (hj : MeasurableEmbedding j) (μ ν : Measure A)
    (h : μ.map j ≪ ν.map j) : μ≪ν := by
  intro s hs
  have hν : ν.map j (j '' s)=0 := by
    rw [hj.map_apply,hj.injective.preimage_image]
    exact hs
  have hμ := h hν
  rwa [hj.map_apply,hj.injective.preimage_image] at hμ

lemma map_full_range {A : Type u9} {B : Type u10} [MeasurableSpace A] [MeasurableSpace B]
    (j : A → B) (hj : MeasurableEmbedding j) (μ : Measure A) :
    ∀ᵐ x ∂ μ.map j,x∈range j := by
  apply (ae_map_iff hj.measurable.aemeasurable hj.measurableSet_range).mpr
  exact Eventually.of_forall (fun _ => mem_range_self _)

lemma pairCoe_open : Topology.IsOpenEmbedding pairCoe :=
  OnePoint.isOpenEmbedding_coe.prodMap OnePoint.isOpenEmbedding_coe

lemma quadCoe_open : Topology.IsOpenEmbedding quadCoe :=
  OnePoint.isOpenEmbedding_coe.prodMap (OnePoint.isOpenEmbedding_coe.prodMap pairCoe_open)

lemma expandedCoe_open : Topology.IsOpenEmbedding expandedCoe :=
  quadCoe_open.prodMap (pairCoe_open.prodMap pairCoe_open)

end WeakPinned.Bounded

end
end
section
noncomputable section
open MeasureTheory Filter
open scoped BigOperators Topology ENNReal
namespace WeakPinned.Bounded
open Variance
variable {V : Type u11} {I : Type u12} [Fintype V] [DecidableEq V] [Fintype I]
variable (G : Core.Fibers V I)
attribute [local instance] OAI.WeakPinned.Bounded.instMeasurableSpaceSphere_3
local instance instBorelSpaceSphere_3 : BorelSpace Sphere := ⟨rfl⟩

lemma expandedProbability_edge (U₁ U₂ : V → Sphere) (hG : 0<G.edgeCount)
    (hB : ∀ e,(G.targets e).Nonempty) :
    (expandedProbability G U₁ U₂ hG hB:Measure (Expanded Sphere)).map Prod.fst=
      (edgeProbability G U₁ U₂ hG hB:Measure (Quad Sphere)) := by
  change (finiteLaw _ _).map _=finiteLaw _ _
  rw [finiteLaw_map _ _ _ measurable_fst]
  exact tripleLaw_edge G.fiberWeight (fun e => prob (G.targets e)) (edgeValue G.source U₁ U₂) G.fiberWeight_nonneg (fun e => Core.Fibers.prob_nn _) (fun e => sum_prob _ (hB e))

lemma edgeProbability_dom₁ (U₁ U₂ : V → Sphere) (hG : 0<G.edgeCount)
    (hB : ∀ e,(G.targets e).Nonempty) (hn : 2≤Fintype.card V) (M : ℝ) (hM : 0≤M)
    (hdom : ∀ x y,G.edgeLaw x y≤M*pairProb Finset.univ x y) :
    (edgeProbability G U₁ U₂ hG hB:Measure (Quad Sphere)).map (fun q => (q.1,q.2.2.1))≤
      ENNReal.ofReal (2*M) • (uniformLaw U₁).prod (uniformLaw U₁) := by
  change (finiteLaw (edgeWeight G.fiberWeight (fun e => prob (G.targets e)))
    (edgeValue G.source U₁ U₂)).map (fun q => (q.1,q.2.2.1))≤_
  rw [finiteLaw_map _ _ (fun q : Quad Sphere => (q.1,q.2.2.1)) (by fun_prop)]
  change finiteLaw (edgeWeight G.fiberWeight (fun e => prob (G.targets e))) (fun r => (U₁ (G.source r.1),U₁ r.2))≤_
  rw [graph_edge_law G (fun x y => (U₁ x,U₁ y)) hG hB]
  exact graph_domination G U₁ hn M hM hdom

lemma edgeProbability_dom₂ (U₁ U₂ : V → Sphere) (hG : 0<G.edgeCount)
    (hB : ∀ e,(G.targets e).Nonempty) (hn : 2≤Fintype.card V) (M : ℝ) (hM : 0≤M)
    (hdom : ∀ x y,G.edgeLaw x y≤M*pairProb Finset.univ x y) :
    (edgeProbability G U₁ U₂ hG hB:Measure (Quad Sphere)).map (fun q => (q.2.1,q.2.2.2))≤
      ENNReal.ofReal (2*M) • (uniformLaw U₂).prod (uniformLaw U₂) := by
  change (finiteLaw (edgeWeight G.fiberWeight (fun e => prob (G.targets e)))
    (edgeValue G.source U₁ U₂)).map (fun q => (q.2.1,q.2.2.2))≤_
  rw [finiteLaw_map _ _ (fun q : Quad Sphere => (q.2.1,q.2.2.2)) (by fun_prop)]
  change finiteLaw (edgeWeight G.fiberWeight (fun e => prob (G.targets e))) (fun r => (U₂ (G.source r.1),U₂ r.2))≤_
  rw [graph_edge_law G (fun x y => (U₂ x,U₂ y)) hG hB]
  exact graph_domination G U₂ hn M hM hdom

end WeakPinned.Bounded

end
end

end OAI
end

section
-- module Solutions.OAIQW_WeakPinned.GridBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u1 u2 u3

section
noncomputable section
open scoped BigOperators Topology
open Filter MeasureTheory
namespace WeakPinned.Grid

lemma regular_pair_ae (z w : ℂ) :
    ∀ᵐ ω ∂ fullLaw,
      (∃ m, shareAt m ω.2 (rotatePair ω.1.1 ω.1.2 z) (rotatePair ω.1.1 ω.1.2 w)) ∧
      (∀ m, shareAt m ω.2 (rotatePair ω.1.1 ω.1.2 z) (rotatePair ω.1.1 ω.1.2 w) →
        shareAt (m+1) ω.2 (rotatePair ω.1.1 ω.1.2 z) (rotatePair ω.1.1 ω.1.2 w)) := by
  have hm (m : ℤ) : MeasurableSet {ω : FullSample | shareAt m ω.2
      (rotatePair ω.1.1 ω.1.2 z) (rotatePair ω.1.1 ω.1.2 w)} :=
    measurableSet_shareAt_param measurable_snd
      ((measurable_rotatePair z).comp measurable_fst) ((measurable_rotatePair w).comp measurable_fst) m
  have hs : MeasurableSet {ω : FullSample |
      (∃ m, shareAt m ω.2 (rotatePair ω.1.1 ω.1.2 z) (rotatePair ω.1.1 ω.1.2 w)) ∧
      (∀ m, shareAt m ω.2 (rotatePair ω.1.1 ω.1.2 z) (rotatePair ω.1.1 ω.1.2 w) →
        shareAt (m+1) ω.2 (rotatePair ω.1.1 ω.1.2 z) (rotatePair ω.1.1 ω.1.2 w))} := by
    simp only [Set.ofPred_and,Set.ofPred_exists,Set.ofPred_forall]
    refine (MeasurableSet.iUnion hm).inter (MeasurableSet.iInter (fun m => ?_))
    convert (hm m).compl.union (hm (m+1)) using 1
    ext ω
    exact imp_iff_not_or
  apply (Measure.ae_prod_iff_ae_ae hs).mpr
  filter_upwards with p
  have hn : ∀ᵐ ω ∂ squareLaw, ∀ m, shareAt m ω (rotatePair p.1 p.2 z) (rotatePair p.1 p.2 w) →
      shareAt (m+1) ω (rotatePair p.1 p.2 z) (rotatePair p.1 p.2 w) := by
    exact eventually_countable_forall.mpr (fun m => shareAt_nested_ae m _ _)
  filter_upwards [share_eventually_exists (rotatePair p.1 p.2 z) (rotatePair p.1 p.2 w),hn] with ω he hn
  obtain ⟨n,he⟩ := he
  exact ⟨⟨(n:ℤ),he⟩,hn⟩

lemma label_eq_iff {ω : FullSample} {z w : ℂ} (hzw : z≠w)
    (he : ∃ m, shareAt m ω.2 (rotatePair ω.1.1 ω.1.2 z) (rotatePair ω.1.1 ω.1.2 w))
    (hn : ∀ m, shareAt m ω.2 (rotatePair ω.1.1 ω.1.2 z) (rotatePair ω.1.1 ω.1.2 w) →
      shareAt (m+1) ω.2 (rotatePair ω.1.1 ω.1.2 z) (rotatePair ω.1.1 ω.1.2 w)) (r : ℝ) :
    label ω r z=label ω r w ↔ r≤depth ω z w := by
  rw [show label ω r z=label ω r w ↔ shareAt (level ω r) ω.2
    (rotatePair ω.1.1 ω.1.2 z) (rotatePair ω.1.1 ω.1.2 w) by simp only [label,Prod.mk.injEq,shareAt]]
  rw [shareAt_iff_minScale_le (rotatePair_ne _ _ hzw) he hn]
  unfold level depth gridDepth
  rw [Int.le_floor,le_div_iff₀ (Real.log_pos (by norm_num : (1:ℝ)<2))]
  constructor <;> intro h <;> linarith

lemma side_pos (ω : FullSample) (r m : ℝ) : 0<side ω r m := by unfold side; positivity

lemma log_side (ω : FullSample) (r m : ℝ) :
    Real.log (side ω r m)=m+ω.1.1+(level ω r:ℝ)*Real.log 2 := by
  unfold side
  rw [Real.log_mul (Real.exp_ne_zero _) (by positivity),Real.log_exp,Real.log_zpow]

lemma side_bounds (ω : FullSample) (r m : ℝ) :
    Real.exp (m-r)/2 < side ω r m ∧ side ω r m ≤ Real.exp (m-r) := by
  have hl := Int.floor_le ((-r-ω.1.1)/Real.log 2)
  have hu := Int.lt_floor_add_one ((-r-ω.1.1)/Real.log 2)
  have hp : 0<Real.log 2 := Real.log_pos (by norm_num)
  have hl' := (le_div_iff₀ hp).mp hl
  have hu' := (div_lt_iff₀ hp).mp hu
  change (level ω r:ℝ)*Real.log 2≤ -r-ω.1.1 at hl'
  change -r-ω.1.1<((level ω r:ℝ)+1)*Real.log 2 at hu'
  constructor
  · rw [← Real.exp_log (by norm_num : (0:ℝ)<2),← Real.exp_sub]
    rw [← Real.exp_log (side_pos ω r m),Real.exp_lt_exp,log_side]
    nlinarith
  · rw [← Real.exp_log (side_pos ω r m),Real.exp_le_exp,log_side]
    linarith

lemma label_diameter {ω : FullSample} {r m : ℝ} {z w : ℂ}
    (h : label ω r z=label ω r w) :
    ‖(Real.exp m:ℂ)*z-(Real.exp m:ℂ)*w‖ < 2*side ω r m := by
  have h₁ := shares_gap (by positivity : 0<(2:ℝ)^level ω r) (congrArg Prod.fst h)
  have h₂ := shares_gap (by positivity : 0<(2:ℝ)^level ω r) (congrArg Prod.snd h)
  have hh := (rotatePair_gaps ω.1.1 ω.1.2 z w).1
  have hm := mul_lt_mul_of_pos_left (show Real.exp (-ω.1.1)*‖z-w‖ < 2*(2:ℝ)^level ω r by linarith)
    (Real.exp_pos (m+ω.1.1))
  have he : Real.exp (m+ω.1.1)*Real.exp (-ω.1.1)=Real.exp m := by rw [← Real.exp_add]; congr 1; ring
  rw [← mul_sub,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
  unfold side
  rw [← mul_assoc,he] at hm
  nlinarith

end WeakPinned.Grid

namespace WeakPinned.Global
open NumberField Hierarchy
variable {P : Type u1} {K : Type u2} [Fintype P] [DecidableEq P] [Field K] [NumberField K]
variable (Z : P → K) (hZ : Function.Injective Z) (v : InfinitePlace K)

omit [NumberField K] in
include hZ in
lemma arch_label_ae : ∀ᵐ ω ∂ Grid.fullLaw, ∀ r x y,
    (arch Z v ω).share r x y ↔ Grid.label ω r (v.embedding (Z x))=Grid.label ω r (v.embedding (Z y)) := by
  have hr : ∀ᵐ ω ∂ Grid.fullLaw, ∀ x y,
      (∃ m, Grid.shareAt m ω.2 (Grid.rotatePair ω.1.1 ω.1.2 (v.embedding (Z x))) (Grid.rotatePair ω.1.1 ω.1.2 (v.embedding (Z y)))) ∧
      (∀ m, Grid.shareAt m ω.2 (Grid.rotatePair ω.1.1 ω.1.2 (v.embedding (Z x))) (Grid.rotatePair ω.1.1 ω.1.2 (v.embedding (Z y))) →
        Grid.shareAt (m+1) ω.2 (Grid.rotatePair ω.1.1 ω.1.2 (v.embedding (Z x))) (Grid.rotatePair ω.1.1 ω.1.2 (v.embedding (Z y)))) := by
    simp only [Filter.eventually_all]
    exact fun x y => Grid.regular_pair_ae _ _
  filter_upwards [good_ae Z hZ v,hr] with ω hg hr
  intro r x y
  by_cases hxy : x=y
  · subst y; simp [Depth.share]
  · rw [Depth.share,or_iff_right hxy]
    change (r ≤ if good Z v ω ∧ x≠y then Grid.depth ω (v.embedding (Z x)) (v.embedding (Z y)) else 0) ↔ _
    rw [ite_eq_left ⟨hg,hxy⟩]
    exact (Grid.label_eq_iff (embedding_ne Z hZ v hxy) (hr x y).1 (hr x y).2 r).symm

end WeakPinned.Global

end
end
section
noncomputable section
open scoped BigOperators Topology
open Filter MeasureTheory
namespace WeakPinned.Grid

lemma bin_gap {l : ℝ} (hl : 0<l) (s x y : ℝ) :
    |(bin l s x : ℝ)-(bin l s y : ℝ)| < |x-y|/l+1 := by
  have hx := Int.floor_le ((x-s)/l)
  have hy := Int.lt_floor_add_one ((y-s)/l)
  have hx' := Int.lt_floor_add_one ((x-s)/l)
  have hy' := Int.floor_le ((y-s)/l)
  have hh : (x-s)/l-(y-s)/l=(x-y)/l := by ring
  have hle := div_le_div_of_nonneg_right (le_abs_self (x-y)) hl.le
  have hge := div_le_div_of_nonneg_right (neg_abs_le (x-y)) hl.le
  rw [neg_div] at hge
  unfold bin
  apply abs_lt.mpr
  constructor <;> linarith

lemma scaled_ratio (ω : FullSample) (r m : ℝ) (z w : ℂ) :
    Real.exp (-ω.1.1)*‖z-w‖/(2:ℝ)^level ω r =
      ‖(Real.exp m:ℂ)*z-(Real.exp m:ℂ)*w‖/side ω r m := by
  rw [← mul_sub,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
  unfold side
  have he : Real.exp (-ω.1.1)*Real.exp (m+ω.1.1)=Real.exp m := by
    rw [← Real.exp_add]; congr 1; ring
  field_simp
  nlinarith [congrArg (fun t : ℝ => ‖z-w‖*t) he]

lemma label_gap (ω : FullSample) (r m : ℝ) (z w : ℂ) :
    |((label ω r z).1:ℝ)-((label ω r w).1:ℝ)| <
      ‖(Real.exp m:ℂ)*z-(Real.exp m:ℂ)*w‖/side ω r m+1 ∧
    |((label ω r z).2:ℝ)-((label ω r w).2:ℝ)| <
      ‖(Real.exp m:ℂ)*z-(Real.exp m:ℂ)*w‖/side ω r m+1 := by
  have h₁ : |(rotatePair ω.1.1 ω.1.2 z).1-(rotatePair ω.1.1 ω.1.2 w).1|≤
      Real.exp (-ω.1.1)*‖z-w‖ := by
    simpa only [← norm_rotateC ω.1.1 ω.1.2 (z-w),rotateC_sub,rotatePair,Complex.sub_re] using
      Complex.abs_re_le_norm (rotateC ω.1.1 ω.1.2 z-rotateC ω.1.1 ω.1.2 w)
  have h₂ : |(rotatePair ω.1.1 ω.1.2 z).2-(rotatePair ω.1.1 ω.1.2 w).2|≤
      Real.exp (-ω.1.1)*‖z-w‖ := by
    simpa only [← norm_rotateC ω.1.1 ω.1.2 (z-w),rotateC_sub,rotatePair,Complex.sub_im] using
      Complex.abs_im_le_norm (rotateC ω.1.1 ω.1.2 z-rotateC ω.1.1 ω.1.2 w)
  have hp : 0<(2:ℝ)^level ω r := by positivity
  constructor
  · exact (bin_gap hp _ _ _).trans_le (add_le_add
      ((div_le_div_of_nonneg_right h₁ hp.le).trans_eq (scaled_ratio ω r m z w)) le_rfl)
  · exact (bin_gap hp _ _ _).trans_le (add_le_add
      ((div_le_div_of_nonneg_right h₂ hp.le).trans_eq (scaled_ratio ω r m z w)) le_rfl)

/-- A uniform bound on the number of occupied squares meeting the disk.
Only the lower bound on the actual side is needed. -/
lemma card_labels_bound {P : Type u3} [DecidableEq P] (A : Finset P) (u : P → ℂ)
    (ω : FullSample) (r m : ℝ) (b : ℂ) (R L : ℝ) (M : ℕ)
    (hR : 0≤R) (hL : 0<L) (hside : L ≤ side ω r m)
    (hM : 2*R/L+1≤M)
    (hA : ∀ x∈A, ‖(Real.exp m:ℂ)*u x+b‖≤R) :
    (A.image (fun x => label ω r (u x))).card ≤ (2*M+1)^2 := by
  classical
  rcases A.eq_empty_or_nonempty with h | ⟨x₀,hx₀⟩
  · simp [h]
  let l₀ := label ω r (u x₀)
  have hd (x : P) (hx : x∈A) :
      ‖(Real.exp m:ℂ)*u x-(Real.exp m:ℂ)*u x₀‖≤2*R := by
    rw [show (Real.exp m:ℂ)*u x-(Real.exp m:ℂ)*u x₀=
      ((Real.exp m:ℂ)*u x+b)-((Real.exp m:ℂ)*u x₀+b) by ring]
    exact (norm_sub_le _ _).trans (by linarith [hA x hx,hA x₀ hx₀])
  have hg (x : P) (hx : x∈A) :
      |((label ω r (u x)).1:ℝ)-(l₀.1:ℝ)|≤M ∧
      |((label ω r (u x)).2:ℝ)-(l₀.2:ℝ)|≤M := by
    have hb : ‖(Real.exp m:ℂ)*u x-(Real.exp m:ℂ)*u x₀‖/side ω r m+1≤M := by
      apply le_trans _ hM
      apply add_le_add _ le_rfl
      exact div_le_div₀ (by positivity) (hd x hx) hL hside
    exact ⟨(label_gap ω r m _ _).1.le.trans hb,(label_gap ω r m _ _).2.le.trans hb⟩
  have hs : A.image (fun x => label ω r (u x)) ⊆
      (Finset.Icc (l₀.1-(M:ℤ)) (l₀.1+(M:ℤ))) ×ˢ
      (Finset.Icc (l₀.2-(M:ℤ)) (l₀.2+(M:ℤ))) := by
    intro p hp
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hp
    have hh := hg x hx
    rcases abs_le.mp hh.1 with ⟨ha,hb⟩
    rcases abs_le.mp hh.2 with ⟨hc,hd⟩
    simp only [Finset.mem_product,Finset.mem_Icc]
    constructor
    · constructor
      · exact_mod_cast (show (l₀.1:ℝ)-(M:ℝ)≤((label ω r (u x)).1:ℝ) by linarith)
      · exact_mod_cast (show ((label ω r (u x)).1:ℝ)≤(l₀.1:ℝ)+(M:ℝ) by linarith)
    · constructor
      · exact_mod_cast (show (l₀.2:ℝ)-(M:ℝ)≤((label ω r (u x)).2:ℝ) by linarith)
      · exact_mod_cast (show ((label ω r (u x)).2:ℝ)≤(l₀.2:ℝ)+(M:ℝ) by linarith)
  calc
    _ ≤ _ := Finset.card_le_card hs
    _ = (2*M+1)^2 := by
      rw [Finset.card_product,Int.card_Icc,Int.card_Icc]
      have he (z : ℤ) : (z+(M:ℤ)+1-(z-(M:ℤ))).toNat=2*M+1 := by omega
      rw [he,he,pow_two]

end WeakPinned.Grid

end
end

end OAI
end

section
-- module Solutions.OAIQW_WeakPinned.PartitionIntegrals
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u1 u2 u3 u4 u5 u6 u7 u8 u9 u10

section
noncomputable section
open scoped BigOperators Topology
open Filter MeasureTheory
namespace WeakPinned.Hierarchy.Depth
variable {P : Type u1} [Fintype P] [DecidableEq P]
variable (d : Depth P)

lemma sum_by_cells (r : ℝ) (f : P → ℝ) :
    (∑ C ∈ d.cells r, ∑ x∈C, f x)=∑ x,f x := by
  have hh (x : P) : (∑ C ∈ d.cells r, if x∈C then f x else 0)=f x := by
    rw [Finset.sum_eq_single (d.cell r x)]
    · simp [d.share_refl]
    · intro C hC hne
      rw [ite_eq_right]
      exact fun hx => hne (d.cell_of_mem hC hx)
    · simp
  calc
    _ = ∑ C ∈ d.cells r, ∑ x, if x∈C then f x else 0 := by simp
    _ = ∑ x, ∑ C ∈ d.cells r, if x∈C then f x else 0 := Finset.sum_comm
    _ = _ := by simp_rw [hh]

lemma sum_cell_value (r : ℝ) (p : P → ℝ) (v : Finset P → ℝ) :
    (∑ x,p x*v (d.cell r x))=∑ C∈d.cells r, v C*(∑ x∈C,p x) := by
  rw [← d.sum_by_cells r (fun x => p x*v (d.cell r x))]
  apply Finset.sum_congr rfl
  intro C hC
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x hx
  rw [← d.cell_of_mem hC hx]
  ring

end WeakPinned.Hierarchy.Depth

namespace WeakPinned.Bounded
open Hierarchy Variance
variable {P : Type u2} [Fintype P] [DecidableEq P]

omit [DecidableEq P] in
lemma weighted_test_bound (p f g : P → ℝ) (hp : ∀ x,0 ≤ p x) (h1 : ∑ x,p x=1)
    (η : ℝ) (hfg : ∀ x,|f x-g x| ≤ η) :
    |(∑ x,p x*f x)-(∑ x,p x*g x)| ≤ η := by
  rw [← Finset.sum_sub_distrib]
  calc
    _  ≤  ∑ x, |p x*f x-p x*g x| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ x,p x*|f x-g x| := by simp_rw [← mul_sub,abs_mul,abs_of_nonneg (hp _)]
    _  ≤  ∑ x,p x*η := Finset.sum_le_sum (fun x _ => mul_le_mul_of_nonneg_left (hfg x) (hp x))
    _ = η := by rw [← Finset.sum_mul,h1,one_mul]

lemma partition_test_bound (d : Depth P) (r : ℝ) (p a f : P → ℝ)
    (hp : ∀ x,0 ≤ p x) (ha : ∀ x,0 ≤ a x) (hp1 : ∑ x,p x=1) (ha1 : ∑ x,a x=1)
    (A : Finset (Finset P)) (hA : A⊆d.cells r) (v : Finset P → ℝ) (η H : ℝ)
    (hf : ∀ x,|f x-v (d.cell r x)| ≤ η)
    (hv : ∀ C∈d.cells r, |v C| ≤ if C∈A then H else 0) :
    |(∑ x,p x*f x)-(∑ x,a x*f x)|  ≤
      2*η+H*(∑ C∈A, |(∑ x∈C,p x)-(∑ x∈C,a x)|) := by
  have hpa : |(∑ x,p x*v (d.cell r x))-(∑ x,a x*v (d.cell r x))| ≤
      H*(∑ C∈A,|(∑ x∈C,p x)-(∑ x∈C,a x)|) := by
    rw [d.sum_cell_value,d.sum_cell_value,← Finset.sum_sub_distrib]
    calc
      _  ≤  ∑ C∈d.cells r, |v C*(∑ x∈C,p x)-v C*(∑ x∈C,a x)| := Finset.abs_sum_le_sum_abs _ _
      _  ≤  ∑ C∈d.cells r, if C∈A then H*|(∑ x∈C,p x)-(∑ x∈C,a x)| else 0 := by
        apply Finset.sum_le_sum
        intro C hC
        rw [← mul_sub,abs_mul]
        simpa only [ite_mul,zero_mul] using mul_le_mul_of_nonneg_right (hv C hC) (abs_nonneg _)
      _ = _ := by rw [Finset.sum_ite_mem,Finset.inter_eq_right.mpr hA,Finset.mul_sum]
  have h₁ := weighted_test_bound p f (fun x => v (d.cell r x)) hp hp1 η hf
  have h₂ := weighted_test_bound a f (fun x => v (d.cell r x)) ha ha1 η hf
  have hh := abs_add_three ((∑ x,p x*f x)-(∑ x,p x*v (d.cell r x)))
    ((∑ x,p x*v (d.cell r x))-(∑ x,a x*v (d.cell r x)))
    ((∑ x,a x*v (d.cell r x))-(∑ x,a x*f x))
  rw [abs_sub_comm (∑ x,a x*v (d.cell r x))] at hh
  convert le_trans hh (by linarith : _ ≤ 2*η+H*(∑ C∈A, |(∑ x∈C,p x)-(∑ x∈C,a x)|)) using 1
  congr 1
  ring

lemma cellProb_compl (B C : Finset P) (hB : B.Nonempty) :
    cellProb B Cᶜ=1-cellProb B C := by
  rw [← sum_prob_cell,← sum_prob_cell,← sum_prob B hB]
  have hh := Finset.sum_compl_add_sum C (prob B)
  linarith

variable {I : Type u3} [Fintype I]

lemma meanCellDiscrep_compl (w : I → ℝ) (B : I → Finset P) (hB : ∀ i,(B i).Nonempty)
    (hn : 0<Fintype.card P) (C : Finset P) :
    meanCellDiscrep w B Cᶜ=meanCellDiscrep w B C := by
  unfold meanCellDiscrep
  apply Finset.sum_congr rfl
  intro i _
  rw [cellProb_compl _ _ (hB i),cellProb_compl _ _ (Finset.univ_nonempty_iff.mpr (Fintype.card_pos_iff.mp hn)),
    sub_sub_sub_cancel_left,abs_sub_comm]

lemma meanCellDiscrep_small (w : I → ℝ) (B : I → Finset P) (M : ℝ)
    (hw : ∀ i,0 ≤ w i) (hW : ∑ i,w i ≤ 1)
    (hdom : ∀ x,(∑ i,w i*prob (B i) x) ≤ M*prob Finset.univ x) (C : Finset P) :
    meanCellDiscrep w B C ≤ (M+1)*cellProb Finset.univ C := by
  have hmean := mean_cell_bound w B C M hdom
  calc
    _  ≤  ∑ i,w i*(cellProb (B i) C+cellProb Finset.univ C) := by
      apply Finset.sum_le_sum
      intro i _
      exact mul_le_mul_of_nonneg_left (abs_sub_le_iff.mpr ⟨by linarith [cellProb_nonneg (Finset.univ : Finset P) C],by linarith [cellProb_nonneg (B i) C]⟩) (hw i)
    _ = (∑ i,w i*cellProb (B i) C)+(∑ i,w i)*cellProb Finset.univ C := by simp [mul_add,Finset.sum_add_distrib,Finset.sum_mul]
    _  ≤  (M+1)*cellProb Finset.univ C := by nlinarith [mul_le_mul_of_nonneg_right hW (cellProb_nonneg (Finset.univ : Finset P) C)]

lemma meanCellDiscrep_young (w : I → ℝ) (B : I → Finset P) (M T δ : ℝ)
    (hw : ∀ i,0 ≤ w i) (hW : ∑ i,w i ≤ 1) (hM : 0 ≤ M) (hT : 0 ≤ T) (hδ : 0<δ)
    (hdom : ∀ x,(∑ i,w i*prob (B i) x) ≤ M*prob Finset.univ x)
    (C : Finset P) :
    meanCellDiscrep w B C  ≤  varianceCell w B T C/δ+δ+(M+1)*T/Fintype.card P := by
  by_cases hC : T<(C.card:ℝ)
  · have hy (t : ℝ) : |t| ≤ t^2/δ+δ := by
      have hh : |t| *δ ≤ t^2+δ*δ := by nlinarith [sq_nonneg (|t| -δ),sq_abs t]
      calc
        |t| = (|t| *δ)/δ := by field_simp
        _ ≤ (t^2+δ*δ)/δ := div_le_div_of_nonneg_right hh hδ.le
        _ = _ := by field_simp
    have hh : meanCellDiscrep w B C ≤ varianceCell w B T C/δ+δ := by
      rw [varianceCell,ite_eq_left hC]
      calc
        _  ≤  ∑ i,w i*((cellProb (B i) C-cellProb Finset.univ C)^2/δ+δ) :=
          Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hy _) (hw i))
        _ = (∑ i,w i*(cellProb (B i) C-cellProb Finset.univ C)^2)/δ+(∑ i,w i)*δ := by
          simp only [mul_add,← mul_div_assoc,Finset.sum_add_distrib,← Finset.sum_div,← Finset.sum_mul]
        _  ≤  _ := by nlinarith [mul_le_mul_of_nonneg_right hW hδ.le]
    exact hh.trans (le_add_of_nonneg_right (by positivity))
  · have hh := meanCellDiscrep_small w B M hw hW hdom C
    have hc : cellProb (Finset.univ : Finset P) C ≤ T/Fintype.card P := by
      simp only [cellProb,Finset.univ_inter,Finset.card_univ]
      exact div_le_div_of_nonneg_right (le_of_not_gt hC) (by positivity)
    have hv := varianceCell_nonneg w B T hw C
    have hm := mul_le_mul_of_nonneg_left hc (show 0 ≤ M+1 by linarith)
    rw [← mul_div_assoc] at hm
    linarith [div_nonneg hv hδ.le]

end WeakPinned.Bounded

end
end
section
noncomputable section
open scoped BigOperators Topology
open Filter MeasureTheory
namespace WeakPinned.Hierarchy.Depth
variable {P : Type u4} [Fintype P] [DecidableEq P]
variable (d : Depth P)

lemma sum_transformCell (r : ℝ) (f : Finset P → ℝ) :
    (∑ C∈d.cells r,f (transformCell C))=d.sumCells f r := by
  classical
  simp only [sumCells,transformed,Multiset.map_add,Multiset.sum_add,Multiset.map_map,
    Function.comp_def,transformCell]
  simp_rw [apply_ite f]
  rw [Finset.sum_ite]
  change (∑ C∈(d.cells r).filter (fun C => Fintype.card P<2*C.card),f Cᶜ)+
    (∑ C∈(d.cells r).filter (fun C => ¬Fintype.card P<2*C.card),f C) =
    (∑ C∈(d.cells r).filter (fun C => ¬Fintype.card P<2*C.card),f C)+
    (∑ C∈(d.cells r).filter (fun C => Fintype.card P<2*C.card),f Cᶜ)
  ring

end WeakPinned.Hierarchy.Depth

namespace WeakPinned.Bounded
open Hierarchy Variance
variable {P : Type u5} {I : Type u6} [Fintype P] [DecidableEq P] [Fintype I]

lemma meanCellDiscrep_transform (w : I → ℝ) (B : I → Finset P) (hB : ∀ i,(B i).Nonempty)
    (hn : 0<Fintype.card P) (C : Finset P) :
    meanCellDiscrep w B (Depth.transformCell C)=meanCellDiscrep w B C := by
  unfold Depth.transformCell
  split_ifs
  · exact meanCellDiscrep_compl w B hB hn C
  · rfl

lemma active_meanDiscrep_bound (d : Depth P) (r : ℝ) (A : Finset (Finset P))
    (N M T δ : ℝ) (w : I → ℝ) (B : I → Finset P)
    (hn : 0<Fintype.card P) (hA : A⊆d.cells r) (hN : (A.card:ℝ) ≤ N)
    (hw : ∀ i,0 ≤ w i) (hW : ∑ i,w i ≤ 1) (hB : ∀ i,(B i).Nonempty)
    (hM : 0 ≤ M) (hT : 0 ≤ T) (hδ : 0<δ)
    (hdom : ∀ x,(∑ i,w i*prob (B i) x) ≤ M*prob Finset.univ x) :
    (∑ C∈A,meanCellDiscrep w B C) ≤
      d.sumCells (varianceCell w B T) r/δ+N*(δ+(M+1)*T/Fintype.card P) := by
  have hv (C) : 0 ≤ varianceCell w B T C := varianceCell_nonneg w B T hw C
  calc
    _ = ∑ C∈A,meanCellDiscrep w B (Depth.transformCell C) := by
      simp_rw [meanCellDiscrep_transform w B hB hn]
    _ ≤ ∑ C∈A,(varianceCell w B T (Depth.transformCell C)/δ+(δ+(M+1)*T/Fintype.card P)) := by
      apply Finset.sum_le_sum
      intro C _
      simpa only [add_assoc] using meanCellDiscrep_young w B M T δ hw hW hM hT hδ hdom (Depth.transformCell C)
    _ = (∑ C∈A,varianceCell w B T (Depth.transformCell C))/δ+
        (A.card:ℝ)*(δ+(M+1)*T/Fintype.card P) := by
      simp [Finset.sum_add_distrib,Finset.sum_div]
      ring
    _ ≤ (∑ C∈d.cells r,varianceCell w B T (Depth.transformCell C))/δ+
        N*(δ+(M+1)*T/Fintype.card P) := by
      apply add_le_add
      · exact div_le_div_of_nonneg_right (Finset.sum_le_sum_of_subset_of_nonneg hA (fun C _ _ => hv _)) hδ.le
      · apply mul_le_mul_of_nonneg_right hN
        positivity
    _ = _ := by rw [d.sum_transformCell]

lemma testDiscrep_nonneg (w : I → ℝ) (B : I → Finset P) (f : P → ℝ) (hw : ∀ i,0 ≤ w i) :
    0 ≤ testDiscrep w B f := Finset.sum_nonneg (fun i _ => mul_nonneg (hw i) (abs_nonneg _))

lemma family_partition_test_bound (d : Depth P) (r : ℝ) (A : Finset (Finset P))
    (N M T δ η H : ℝ) (w : I → ℝ) (B : I → Finset P)
    (hn : 0<Fintype.card P) (hA : A⊆d.cells r) (hN : (A.card:ℝ) ≤ N)
    (hw : ∀ i,0 ≤ w i) (hW : ∑ i,w i ≤ 1) (hB : ∀ i,(B i).Nonempty)
    (hM : 0 ≤ M) (hT : 0 ≤ T) (hδ : 0<δ) (hη : 0 ≤ η) (hH : 0 ≤ H)
    (hdom : ∀ x,(∑ i,w i*prob (B i) x) ≤ M*prob Finset.univ x)
    (f : P → ℝ) (v : Finset P → ℝ)
    (hf : ∀ x,|f x-v (d.cell r x)| ≤ η)
    (hv : ∀ C∈d.cells r,|v C| ≤ if C∈A then H else 0) :
    testDiscrep w B f ≤ 2*η+H*(d.sumCells (varianceCell w B T) r/δ+
      N*(δ+(M+1)*T/Fintype.card P)) := by
  have hp (S : Finset P) (x : P) : 0 ≤ prob S x := by unfold prob; split_ifs <;> positivity
  have hh (i : I) := partition_test_bound d r (prob (B i)) (prob Finset.univ) f
    (hp _) (hp _) (sum_prob _ (hB i))
    (sum_prob _ (Finset.univ_nonempty_iff.mpr (Fintype.card_pos_iff.mp hn))) A hA v η H hf hv
  simp only [sum_prob_cell] at hh
  have hmean := active_meanDiscrep_bound d r A N M T δ w B hn hA hN hw hW hB hM hT hδ hdom
  calc
    _ ≤ ∑ i,w i*(2*η+H*(∑ C∈A,|cellProb (B i) C-cellProb Finset.univ C|)) :=
      Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hh i) (hw i))
    _ = (∑ i,w i)*(2*η)+H*(∑ C∈A,meanCellDiscrep w B C) := by
      simp only [mul_add,Finset.sum_add_distrib,← Finset.sum_mul]
      congr 1
      simp only [meanCellDiscrep,Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro C _
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ ≤ _ := add_le_add (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hW (show 0≤2*η by positivity))
      (mul_le_mul_of_nonneg_left hmean hH)

end WeakPinned.Bounded

end
end
section
noncomputable section
open scoped BigOperators Topology
open Filter MeasureTheory
namespace WeakPinned.Bounded
open Hierarchy
variable {P : Type u7} [Fintype P] [DecidableEq P]

lemma grid_test_data (d : Depth P) (u : P → ℂ) (ω : Grid.FullSample) (r m : ℝ) (b : ℂ)
    (hn : 0<Fintype.card P)
    (hshare : ∀ x y,d.share r x y ↔ Grid.label ω r (u x)=Grid.label ω r (u y))
    (R L η H ε : ℝ) (M : ℕ) (hR : 0≤R) (hL : 0<L)
    (hside : L ≤ Grid.side ω r m) (hupper : Grid.side ω r m ≤ ε)
    (hM : 2*R/L+1≤M)
    (f : ℂ → ℝ) (hbound : ∀ z,|f z|≤H)
    (hcont : ∀ z w,‖z-w‖<2*ε → |f z-f w|≤η)
    (hout : ∀ z,R<‖z‖ → |f z|≤η) :
    ∃ A : Finset (Finset P), ∃ v : Finset P → ℝ,
      A⊆d.cells r ∧ A.card≤(2*M+1)^2 ∧
      (∀ x,|f ((Real.exp m:ℂ)*u x+b)-v (d.cell r x)|≤η) ∧
      (∀ C∈d.cells r,|v C|≤ if C∈A then H else 0) := by
  classical
  let : Nonempty P := Fintype.card_pos_iff.mp hn
  let D : Finset P := Finset.univ.filter (fun x => ‖(Real.exp m:ℂ)*u x+b‖≤R)
  let A := D.image (d.cell r)
  let rep (C : Finset P) : P := if h : C∈A then (Finset.mem_image.mp h).choose else Classical.arbitrary P
  have hr (C : Finset P) (hC : C∈A) : rep C∈D ∧ d.cell r (rep C)=C := by
    simpa only [rep,dite_eq_left hC] using (Finset.mem_image.mp hC).choose_spec
  have hAc : A⊆d.cells r := Finset.image_subset_image (Finset.filter_subset _ _)
  have hcount : A.card≤(2*M+1)^2 := by
    apply le_trans (Finset.card_le_card_of_injOn (fun C => Grid.label ω r (u (rep C)))
      (t:=D.image (fun x => Grid.label ω r (u x))) ?_ ?_)
    · apply Grid.card_labels_bound D u ω r m b R L M hR hL hside hM
      intro x hx
      exact (Finset.mem_filter.mp hx).2
    · intro C hC
      exact Finset.mem_image.mpr ⟨rep C,(hr C hC).1,rfl⟩
    · intro C hC E hE he
      rw [← (hr C hC).2,← (hr E hE).2]
      exact d.cell_eq_of_share ((hshare _ _).mpr he)
  let v (C : Finset P) := if C∈A then f ((Real.exp m:ℂ)*u (rep C)+b) else 0
  refine ⟨A,v,hAc,hcount,?_,?_⟩
  · intro x
    by_cases hx : d.cell r x∈A
    · simp only [v,ite_eq_left hx]
      apply hcont
      have he : d.share r x (rep (d.cell r x)) := by
        rw [← d.mem_cell]
        have hmem := d.self_mem_cell r (rep (d.cell r x))
        rwa [(hr _ hx).2] at hmem
      have hd := Grid.label_diameter (m:=m) ((hshare _ _).mp he)
      have heq : ((Real.exp m:ℂ)*u x+b)-((Real.exp m:ℂ)*u (rep (d.cell r x))+b)=
          (Real.exp m:ℂ)*u x-(Real.exp m:ℂ)*u (rep (d.cell r x)) := by ring
      rw [heq]
      exact hd.trans_le (by linarith)
    · simp only [v,ite_eq_right hx,sub_zero]
      apply hout
      by_contra hh
      have hxD : x∈D := Finset.mem_filter.mpr ⟨Finset.mem_univ x,le_of_not_gt hh⟩
      exact hx (Finset.mem_image.mpr ⟨x,hxD,rfl⟩)
  · intro C _
    by_cases hC : C∈A
    · simpa only [v,ite_eq_left hC] using hbound ((Real.exp m:ℂ)*u (rep C)+b)
    · simp only [v,ite_eq_right hC,abs_zero,le_refl]

end WeakPinned.Bounded

end
end
section
noncomputable section
open scoped BigOperators Topology
open Filter MeasureTheory
namespace WeakPinned.Bounded

lemma le_unit_integral (g : ℝ → ℝ) (hg : Integrable g) (hg0 : ∀ r,0≤g r)
    (t D a b : ℝ) (hb : 0≤b) (h : ∀ r∈Set.Icc t (t+1), D≤a+b*g r) :
    D≤a+b*(∫ r,g r) := by
  have hi (c : ℝ) : IntegrableOn (fun _ : ℝ => c) (Set.Icc t (t+1)) :=
    integrableOn_const isCompact_Icc.measure_lt_top.ne
  have hv : (volume (Set.Icc t (t+1))).toReal=1 := by simp [Real.volume_Icc]
  have hc (c : ℝ) : (∫ r in Set.Icc t (t+1),c)=c := by
    rw [integral_const]
    simp only [Measure.real,Measure.restrict_apply_univ,hv,one_smul]
  have hh := setIntegral_mono_on (hi D) ((hi a).add (hg.integrableOn.const_mul b)) measurableSet_Icc h
  simp only [Pi.add_apply] at hh
  rw [integral_add (hi a) (hg.integrableOn.const_mul b),hc D,hc a,integral_const_mul] at hh
  exact hh.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left
    (setIntegral_le_integral hg (ae_of_all _ hg0)) hb))

end WeakPinned.Bounded

namespace WeakPinned.Grid
lemma side_unit_bounds (ω : FullSample) (m ε r : ℝ) (hε : 0<ε)
    (hr : r∈Set.Icc (m-Real.log ε) (m-Real.log ε+1)) :
    ε/(2*Real.exp 1) ≤ side ω r m ∧ side ω r m ≤ ε := by
  have he : Real.exp (Real.log ε-1)/2=ε/(2*Real.exp 1) := by
    rw [Real.exp_sub,Real.exp_log hε]
    ring
  constructor
  · rw [← he]
    exact (div_le_div_of_nonneg_right (Real.exp_le_exp.mpr (by linarith [hr.2])) (by norm_num)).trans
      (side_bounds ω r m).1.le
  · exact (side_bounds ω r m).2.trans (by rw [← Real.exp_log hε]; exact Real.exp_le_exp.mpr (by linarith [hr.1]))
end WeakPinned.Grid

end
end
section
noncomputable section
open scoped BigOperators Topology
open Filter MeasureTheory
namespace WeakPinned.Bounded
open Hierarchy Variance Global NumberField
variable {P : Type u8} {I : Type u9} [Fintype P] [DecidableEq P] [Fintype I]

lemma grid_test_integrated (d : Depth P) (u : P → ℂ) (ω : Grid.FullSample) (m : ℝ) (b : ℂ)
    (hn : 2≤ Fintype.card P)
    (hshare : ∀ r x y,d.share r x y ↔ Grid.label ω r (u x)=Grid.label ω r (u y))
    (R ε η H M T δ : ℝ) (N : ℕ) (hR : 0≤ R) (hε : 0<ε)
    (hN : 2*R/(ε/(2*Real.exp 1))+1≤ N)
    (hη : 0≤ η) (hH : 0≤ H) (hM : 0≤ M) (hT : 1≤ T) (hδ : 0<δ)
    (w : I → ℝ) (B : I → Finset P)
    (hw : ∀ i,0≤ w i) (hW : ∑ i,w i≤ 1) (hB : ∀ i,2≤ (B i).card)
    (hdom : ∀ x, (∑ i,w i*prob (B i) x)≤ M*prob Finset.univ x)
    (f : ℂ → ℝ) (hbound : ∀ z,|f z|≤ H)
    (hcont : ∀ z z',‖z-z'‖<2*ε → |f z-f z'|≤ η)
    (hout : ∀ z,R<‖z‖ → |f z|≤ η) :
    testDiscrep w B (fun x => f ((Real.exp m:ℂ)*u x+b)) ≤
      2*η+H*(weightedIntegral d.mass (varianceCell w B T)/δ+
        ((2*N+1)^2:ℕ)*(δ+(M+1)*T/Fintype.card P)) := by
  have hq (C) : 0≤ varianceCell w B T C := varianceCell_nonneg w B T hw C
  have hi := d.integrable_sumCells hn _ (varianceCell_singleton w B T hT hB)
  have hsum (r) : 0≤ d.sumCells (varianceCell w B T) r := by
    rw [d.sumCells_count]
    exact Finset.sum_nonneg (fun C _ => mul_nonneg (d.count_nonneg r C) (hq C))
  let a := 2*η+H*((((2*N+1)^2:ℕ):ℝ)*(δ+(M+1)*T/Fintype.card P))
  have hh := le_unit_integral _ hi hsum (m-Real.log ε)
    (testDiscrep w B (fun x => f ((Real.exp m:ℂ)*u x+b))) a (H/δ) (by positivity) ?_
  · rw [d.integral_sumCells hn _ (varianceCell_singleton w B T hT hB)] at hh
    convert hh using 1; simp only [a,weightedIntegral]; ring
  · intro r hr
    have hs := Grid.side_unit_bounds ω m ε r hε hr
    obtain ⟨A,v,hA,hAc,hf,hv⟩ := grid_test_data d u ω r m b (by omega) (hshare r)
      R (ε/(2*Real.exp 1)) η H ε N hR (by positivity) hs.1 hs.2 hN f hbound hcont hout
    have h := family_partition_test_bound d r A (((2*N+1)^2:ℕ):ℝ) M T δ η H w B
      (by omega) hA (by exact_mod_cast hAc) hw hW
      (fun i => Finset.card_pos.mp (by have := hB i; omega)) hM (by linarith) hδ hη hH hdom _ v hf hv
    convert h using 1; simp only [a]; ring

variable {K : Type u10} [Field K] [NumberField K]

omit [NumberField K] in
lemma arch_test_bound (Z₁ Z₂ : P → K) (h₁ : Function.Injective Z₁) (h₂ : Function.Injective Z₂)
    (v : InfinitePlace K) (m : ℝ) (b : ℂ) (hn : 2≤ Fintype.card P)
    (R ε η H M T δ : ℝ) (N : ℕ) (hR : 0≤ R) (hε : 0<ε)
    (hN : 2*R/(ε/(2*Real.exp 1))+1≤ N)
    (hη : 0≤ η) (hH : 0≤ H) (hM : 0≤ M) (hT : 1≤ T) (hδ : 0<δ)
    (w : I → ℝ) (B : I → Finset P)
    (hw : ∀ i,0≤ w i) (hW : ∑ i,w i≤ 1) (hB : ∀ i,2≤ (B i).card)
    (hdom : ∀ x, (∑ i,w i*prob (B i) x)≤ M*prob Finset.univ x)
    (f : ℂ → ℝ) (hbound : ∀ z,|f z|≤ H)
    (hcont : ∀ z z',‖z-z'‖<2*ε → |f z-f z'|≤ η)
    (hout : ∀ z,R<‖z‖ → |f z|≤ η) :
    testDiscrep w B (fun x => f ((Real.exp m:ℂ)*v.embedding (Z₁ x)+b)) ≤
      2*η+H*(archMean Z₁ Z₂ (massEval (varianceCell w B T)) v/δ+
        ((2*N+1)^2:ℕ)*(δ+(M+1)*T/Fintype.card P)) := by
  let D := testDiscrep w B (fun x => f ((Real.exp m:ℂ)*v.embedding (Z₁ x)+b))
  let a := 2*η+H*((((2*N+1)^2:ℕ):ℝ)*(δ+(M+1)*T/Fintype.card P))
  let q := varianceCell w B T
  have hq (C) : 0≤ q C := varianceCell_nonneg w B T hw C
  have hi := integrable_massEval Z₁ Z₂ h₁ h₂ hn q v
  have hh : ∀ᵐ ω ∂ Grid.fullLaw,D≤ a+(H/δ)*massEval q (arch Z₁ v ω) (arch Z₂ v ω) := by
    filter_upwards [arch_label_ae Z₁ h₁ v] with ω hω
    have hh := grid_test_integrated (arch Z₁ v ω) (fun x => v.embedding (Z₁ x)) ω m b hn hω
      R ε η H M T δ N hR hε hN hη hH hM hT hδ w B hw hW hB hdom f hbound hcont hout
    have hmass : weightedIntegral (arch Z₁ v ω).mass q≤ massEval q (arch Z₁ v ω) (arch Z₂ v ω) := by
      apply le_add_of_nonneg_right
      exact Finset.sum_nonneg (fun C _ => mul_nonneg ((arch Z₂ v ω).mass_nonneg C) (hq C))
    have he : 2*η+H*(weightedIntegral (arch Z₁ v ω).mass q/δ+
        ((2*N+1)^2:ℕ)*(δ+(M+1)*T/Fintype.card P))=a+(H/δ)*weightedIntegral (arch Z₁ v ω).mass q := by
      simp only [a]; ring
    rw [show varianceCell w B T=q from rfl,he] at hh
    exact hh.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left hmass (by positivity)))
  have hh' := integral_mono_ae (integrable_const D) ((integrable_const a).add (hi.const_mul (H/δ))) hh
  simp only [Pi.add_apply] at hh'
  rw [integral_add (integrable_const a) (hi.const_mul (H/δ)),integral_const_mul] at hh'
  simp only [integral_const,probReal_univ,one_smul] at hh'
  calc
    _ ≤ a+(H/δ)*archMean Z₁ Z₂ (massEval q) v := hh'
    _ = _ := by dsimp only [a,q]; ring

end WeakPinned.Bounded

end
end

end OAI
end

section
-- module Solutions.OAIQW_WeakPinned.VarianceRates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u1 u2 u3 u4 u5 u6 u7 u8 u9 u10 u11

section
noncomputable section
open scoped BigOperators Topology ZeroAtInfty
open Filter MeasureTheory
namespace WeakPinned.Bounded

lemma test_bound_rate (D V A : ℕ → ℝ) (H M : ℝ)
    (hD : ∀ n,0≤ D n) (hH : 0≤ H)
    (hV : Tendsto V atTop (𝓝 0)) (hA : Tendsto A atTop (𝓝 0))
    (h : ∀ η,0<η → ∃ N : ℝ,0≤ N ∧ ∀ δ,0<δ →
      ∀ n,D n≤ 2*η+H*(V n/δ+N*(δ+(M+1)*A n))) :
    Tendsto D atTop (𝓝 0) := by
  apply tendsto_order.mpr
  constructor
  · intro a ha
    exact Eventually.of_forall (fun n => ha.trans_le (hD n))
  · intro b hb
    obtain ⟨N,hN,h⟩ := h (b/8) (by positivity)
    let δ := b/(4*(H*N+1))
    have hδ : 0<δ := by dsimp [δ]; positivity
    have he : (H*N+1)*δ=b/4 := by dsimp [δ]; field_simp
    have hNd : H*N*δ≤ b/4 := by nlinarith
    have hlt : 2*(b/8)+H*(0/δ+N*(δ+(M+1)*0))<b := by simp only [zero_div,mul_zero,add_zero]; nlinarith
    have ht := (tendsto_const_nhds.add ((hV.div_const δ).add
      ((tendsto_const_nhds.add (hA.const_mul (M+1))).const_mul N) |>.const_mul H)).eventually
      (eventually_lt_nhds hlt)
    exact ht.mono (fun n hn => (h δ hδ n).trans_lt hn)

lemma zeroAtInfty_tail (f : C₀(ℂ,ℝ)) (η : ℝ) (hη : 0<η) :
    ∃ R : ℝ,0≤ R ∧ ∀ z,R<‖z‖ → |f z|≤ η := by
  have hf := (Metric.tendsto_nhds.mp (zero_at_infty f) η hη)
  obtain ⟨K,hK,hsub⟩ := mem_cocompact.mp hf
  obtain ⟨R,hR⟩ := hK.isBounded.subset_closedBall (0:ℂ)
  refine ⟨max R 0,le_max_right _ _,?_⟩
  intro z hz
  have hzK : z∉K := by
    intro hzK
    have hh := Metric.mem_closedBall.mp (hR hzK)
    simp only [dist_zero_right] at hh
    exact (not_le_of_gt (lt_of_le_of_lt (le_max_left _ _) hz)) hh
  simpa only [Real.dist_eq,sub_zero] using (show dist (f z) 0<η from hsub hzK).le

lemma zeroAtInfty_modulus (f : C₀(ℂ,ℝ)) (η : ℝ) (hη : 0<η) :
    ∃ ε : ℝ,0<ε ∧ ∀ z w,‖z-w‖<2*ε → |f z-f w|≤ η := by
  obtain ⟨δ,hδ,hd⟩ := Metric.uniformContinuous_iff.mp (ZeroAtInftyContinuousMap.uniformContinuous f) η hη
  refine ⟨δ/2,by positivity,?_⟩
  intro z w hzw
  have hh := hd (show dist z w<δ by rw [dist_eq_norm]; linarith)
  exact (by simpa only [Real.dist_eq] using hh.le)

local instance instMeasurableSpaceSphere_4_rdb9730_1 : MeasurableSpace Sphere := borel Sphere
local instance instBorelSpaceSphere_4_rdb9730_1 : BorelSpace Sphere := ⟨rfl⟩
lemma sphereTest_bound (f : C(Sphere,ℝ)) (z : ℂ) : |sphereTest f z|≤ 2*‖f‖ := by
  have h₁ := f.norm_coe_le_norm (z:Sphere)
  have h₂ := f.norm_coe_le_norm OnePoint.infty
  change |f (z:Sphere)-f OnePoint.infty|≤ 2*‖f‖
  simpa only [Real.norm_eq_abs,two_mul] using
    (norm_sub_le (f (z:Sphere)) (f OnePoint.infty)).trans (add_le_add h₁ h₂)

end WeakPinned.Bounded

end
end
section
noncomputable section
open scoped BigOperators Topology ZeroAtInfty
open Filter MeasureTheory
namespace WeakPinned.Bounded
open Hierarchy Variance Global NumberField
variable {P : Type u1} {I : Type u2} [Fintype P] [DecidableEq P] [Fintype I]

lemma testDiscrep_sub_const (w : I → ℝ) (B : I → Finset P) (f : P → ℝ) (c : ℝ)
    (hn : 0<Fintype.card P) (hB : ∀ i,(B i).Nonempty) :
    testDiscrep w B (fun x => f x-c)=testDiscrep w B f := by
  have hh (S : Finset P) (hS : S.Nonempty) :
      (∑ x,prob S x*(f x-c))=(∑ x,prob S x*f x)-c := by
    simp_rw [mul_sub]
    rw [Finset.sum_sub_distrib,← Finset.sum_mul,sum_prob S hS,one_mul]
  unfold testDiscrep
  simp_rw [hh _ (hB _),hh Finset.univ (Finset.univ_nonempty_iff.mpr (Fintype.card_pos_iff.mp hn))]
  simp only [sub_sub_sub_cancel_right]

variable {V : ℕ → Type u3} {J : ℕ → Type u4} {K : ℕ → Type u5}
  [∀ n,Fintype (V n)] [∀ n,DecidableEq (V n)] [∀ n,Fintype (J n)]
  [∀ n,Field (K n)] [∀ n,NumberField (K n)]

omit [∀ (n : ℕ), NumberField (K n)] in
lemma C0_arch_test_rate (Z₁ Z₂ : ∀ n,V n → K n)
    (h₁ : ∀ n,Function.Injective (Z₁ n)) (h₂ : ∀ n,Function.Injective (Z₂ n))
    (v : ∀ n,InfinitePlace (K n)) (m : ℕ → ℝ) (b : ℕ → ℂ)
    (w : ∀ n,J n → ℝ) (B : ∀ n,J n → Finset (V n)) (T : ℕ → ℝ) (M H : ℝ)
    (hn : ∀ n,2≤ Fintype.card (V n)) (hT : ∀ n,1≤ T n) (hM : 0≤ M) (hH : 0≤ H)
    (hw : ∀ n i,0≤ w n i) (hW : ∀ n,∑ i,w n i≤ 1) (hB : ∀ n i,2≤ (B n i).card)
    (hdom : ∀ n x,(∑ i,w n i*prob (B n i) x)≤ M*prob Finset.univ x)
    (hvar : Tendsto (fun n => archMean (Z₁ n) (Z₂ n) (massEval (varianceCell (w n) (B n) (T n))) (v n)) atTop (𝓝 0))
    (hsmall : Tendsto (fun n => T n/Fintype.card (V n)) atTop (𝓝 0))
    (f : C₀(ℂ,ℝ)) (hbound : ∀ z,|f z|≤ H) :
    Tendsto (fun n => testDiscrep (w n) (B n)
      (fun x => f ((Real.exp (m n):ℂ)*(v n).embedding (Z₁ n x)+b n))) atTop (𝓝 0) := by
  apply test_bound_rate _ _ _ H M (fun n => testDiscrep_nonneg _ _ _ (hw n)) hH hvar hsmall
  intro η hη
  obtain ⟨R,hR,hout⟩ := zeroAtInfty_tail f η hη
  obtain ⟨ε,hε,hcont⟩ := zeroAtInfty_modulus f η hη
  obtain ⟨N,hN⟩ := exists_nat_ge (2*R/(ε/(2*Real.exp 1))+1)
  refine ⟨((2*N+1)^2:ℕ),by positivity,?_⟩
  intro δ hδ n
  have hh := arch_test_bound (Z₁ n) (Z₂ n) (h₁ n) (h₂ n) (v n) (m n) (b n) (hn n)
    R ε η H M (T n) δ N hR hε hN hη.le hH hM (hT n) hδ
    (w n) (B n) (hw n) (hW n) (hB n) (hdom n) f hbound hcont hout
  convert hh using 1
  ring

local instance instMeasurableSpaceSphere_5_rdb9730_1 : MeasurableSpace Sphere := borel Sphere
local instance instBorelSpaceSphere_5_rdb9730_1 : BorelSpace Sphere := ⟨rfl⟩
omit [∀ (n : ℕ), NumberField (K n)] in
lemma sphere_arch_test_rate (Z₁ Z₂ : ∀ n,V n → K n)
    (h₁ : ∀ n,Function.Injective (Z₁ n)) (h₂ : ∀ n,Function.Injective (Z₂ n))
    (v : ∀ n,InfinitePlace (K n)) (m : ℕ → ℝ) (b : ℕ → ℂ)
    (w : ∀ n,J n → ℝ) (B : ∀ n,J n → Finset (V n)) (T : ℕ → ℝ) (M : ℝ)
    (hn : ∀ n,2≤ Fintype.card (V n)) (hT : ∀ n,1≤ T n) (hM : 0≤ M)
    (hw : ∀ n i,0≤ w n i) (hW : ∀ n,∑ i,w n i≤ 1) (hB : ∀ n i,2≤ (B n i).card)
    (hdom : ∀ n x,(∑ i,w n i*prob (B n i) x)≤ M*prob Finset.univ x)
    (hvar : Tendsto (fun n => archMean (Z₁ n) (Z₂ n) (massEval (varianceCell (w n) (B n) (T n))) (v n)) atTop (𝓝 0))
    (hsmall : Tendsto (fun n => T n/Fintype.card (V n)) atTop (𝓝 0))
    (f : C(Sphere,ℝ)) :
    Tendsto (fun n => testDiscrep (w n) (B n)
      (fun x => f (((Real.exp (m n):ℂ)*(v n).embedding (Z₁ n x)+b n):Sphere))) atTop (𝓝 0) := by
  have ht := C0_arch_test_rate Z₁ Z₂ h₁ h₂ v m b w B T M (2*‖f‖) hn hT hM (by positivity)
    hw hW hB hdom hvar hsmall (sphereTest f) (sphereTest_bound f)
  convert ht using 1
  funext n
  symm
  apply testDiscrep_sub_const _ _ _ _ (by have := hn n; omega)
  intro i
  exact Finset.card_pos.mp (by have := hB n i; omega)

end WeakPinned.Bounded

end
end
section
noncomputable section
open MeasureTheory Filter
open scoped BigOperators Topology
namespace WeakPinned.Bounded
open Variance
variable {V : Type u6} {I : Type u7} [Fintype V] [DecidableEq V] [Fintype I]
variable (G : Core.Fibers V I)

omit [Fintype I] in
lemma incoming_discrep_bound (T H : ℝ) (hT : 0<T) (hn : 2≤Fintype.card V)
    (f : V → ℝ) (hf : ∀ x,|f x|≤H) :
    (∑ y,G.incomingWeight y*|(∑ x,G.conditionalSource y x*f x)-∑ x,prob Finset.univ x*f x|)≤
      testDiscrep (G.retainedWeight T) (G.retainedSet T) f+2*H*G.omittedMass T := by
  have hA : |∑ x,prob (Finset.univ : Finset V) x*f x|≤H :=
    avg_abs_bound _ _ _ (Core.Fibers.prob_nn _) (sum_prob _
      (Finset.univ_nonempty_iff.mpr (Fintype.card_pos_iff.mp (by omega)))) hf
  unfold testDiscrep Core.Fibers.omittedMass
  rw [Finset.mul_sum,← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro y _
  by_cases hy : T≤((G.incoming y).card:ℝ)
  · have hne : (G.incoming y).Nonempty := Finset.card_pos.mp (by exact_mod_cast hT.trans_le hy)
    simp only [Core.Fibers.retainedWeight,Core.Fibers.retainedSet,Core.Fibers.conditionalSource,
      ite_eq_left hy,ite_eq_left hne,not_lt_of_ge hy,ite_false,mul_zero,add_zero]
    exact le_rfl
  · have hbound : |(∑ x,G.conditionalSource y x*f x)-∑ x,prob Finset.univ x*f x|≤2*H := by
      have hh := avg_abs_bound _ _ _ (G.conditionalSource_nonneg y) (G.conditionalSource_sum hn y) hf
      exact (abs_sub _ _).trans (by linarith)
    simp only [Core.Fibers.retainedWeight,ite_eq_right hy,lt_of_not_ge hy,ite_true,zero_mul,zero_add]
    nlinarith [mul_le_mul_of_nonneg_left hbound (G.incomingWeight_nonneg y)]

lemma incoming_test_bound (T H C : ℝ) (hT : 0<T) (hn : 2≤Fintype.card V)
    (f g : V → ℝ) (hf : ∀ x,|f x|≤H) (hg : ∀ y,|g y|≤C) :
    |(∑ e,G.fiberWeight e*∑ y,prob (G.targets e) y*(f (G.source e)*g y))-
      (∑ x,prob Finset.univ x*f x)*(∑ y,G.incomingWeight y*g y)|≤
      C*(testDiscrep (G.retainedWeight T) (G.retainedSet T) f+2*H*G.omittedMass T) := by
  have hC : 0≤C := (abs_nonneg (g (Classical.choice (Fintype.card_pos_iff.mp (by omega))))).trans (hg _)
  rw [← G.incoming_eval (fun x y => f x*g y)]
  have he : (∑ y,G.incomingWeight y*∑ x,G.conditionalSource y x*(f x*g y))-
      (∑ x,prob Finset.univ x*f x)*(∑ y,G.incomingWeight y*g y)=
      ∑ y,G.incomingWeight y*((∑ x,G.conditionalSource y x*f x)-∑ x,prob Finset.univ x*f x)*g y := by
    simp only [Finset.mul_sum,Finset.sum_mul,← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro y _
    apply Finset.sum_congr rfl
    intro x _
    ring
  rw [he]
  calc
    _ ≤ ∑ y,|G.incomingWeight y*((∑ x,G.conditionalSource y x*f x)-∑ x,prob Finset.univ x*f x)*g y| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ C*(∑ y,G.incomingWeight y*|(∑ x,G.conditionalSource y x*f x)-∑ x,prob Finset.univ x*f x|) := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro y _
      rw [abs_mul,abs_mul,abs_of_nonneg (G.incomingWeight_nonneg y)]
      nlinarith [mul_le_mul_of_nonneg_left (hg y) (mul_nonneg (G.incomingWeight_nonneg y) (abs_nonneg ((∑ x,G.conditionalSource y x*f x)-∑ x,prob Finset.univ x*f x)))]
    _ ≤ _ := mul_le_mul_of_nonneg_left (incoming_discrep_bound G T H hT hn f hf) hC

end WeakPinned.Bounded

end
end
section
noncomputable section
open MeasureTheory Filter
open scoped BigOperators Topology BoundedContinuousFunction
namespace WeakPinned.Bounded
open Variance
attribute [local instance] OAI.WeakPinned.Bounded.instMeasurableSpaceSphere_6
local instance instBorelSpaceSphere_6 : BorelSpace Sphere := ⟨rfl⟩
local instance instMeasurableSingletonClassQuadSphere : MeasurableSingletonClass (Quad Sphere) := inferInstance
local instance instMeasurableSingletonClassProdSphere : MeasurableSingletonClass ((Sphere × Sphere) × (Sphere × Sphere)) := inferInstance
local instance instMeasurableSingletonClassExpandedSphere : MeasurableSingletonClass (Expanded Sphere) := Prod.instMeasurableSingletonClass
variable {V : Type u8} {I : Type u9} [Fintype V] [DecidableEq V] [Fintype I]
variable (G : Core.Fibers V I)

omit G [Fintype I] in
lemma integral_uniformLaw (U : V → Sphere) (f : Sphere → ℝ) :
    (∫ z,f z ∂  uniformLaw U)=∑ x,prob Finset.univ x*f (U x) := by
  rw [uniformLaw,integral_finiteLaw _ _ (fun _ => inv_nonneg.mpr (Nat.cast_nonneg _))]
  simp only [prob,Finset.mem_univ,ite_true,Finset.card_univ,one_div]

lemma integral_edgeProbability (U₁ U₂ : V → Sphere) (hG : 0<G.edgeCount)
    (hB : ∀ e,(G.targets e).Nonempty) (f : Quad Sphere → ℝ) :
    (∫ q,f q ∂ (edgeProbability G U₁ U₂ hG hB:Measure (Quad Sphere)))=
      ∑ e,G.fiberWeight e*∑ y,prob (G.targets e) y*f (edgeValue G.source U₁ U₂ (e,y)) := by
  change (∫ q,f q ∂ finiteLaw _ _)=_
  rw [integral_finiteLaw _ _ (graph_edgeWeight_nonneg G)]
  simp only [edgeWeight,Fintype.sum_prod_type,mul_assoc,← Finset.mul_sum]

lemma integral_expandedProbability (U₁ U₂ : V → Sphere) (hG : 0<G.edgeCount)
    (hB : ∀ e,(G.targets e).Nonempty) (f : Expanded Sphere → ℝ) :
    (∫ r,f r ∂ (expandedProbability G U₁ U₂ hG hB:Measure (Expanded Sphere)))=
      ∑ r,tripleWeight G.fiberWeight (fun e => prob (G.targets e)) r*f (tripleValue G.source U₁ U₂ r) := by
  change (∫ r,f r ∂ finiteLaw (tripleWeight G.fiberWeight (fun e => prob (G.targets e))) (tripleValue G.source U₁ U₂))=_
  exact integral_finiteLaw _ _ (graph_tripleWeight_nonneg G) f

lemma expanded_test_bound (U₁ U₂ : V → Sphere) (hG : 0<G.edgeCount)
    (hB : ∀ e,(G.targets e).Nonempty) (hn : 2≤Fintype.card V)
    (π : Sphere × Sphere → Sphere) (f : Quad Sphere → ℝ) (g h : Sphere → ℝ) (C H₁ H₂ : ℝ)
    (hC : 0≤C) (hf : ∀ q,|f q|≤C) (hg : ∀ z,|g z|≤H₁) (hh : ∀ z,|h z|≤H₂) :
    |(∫ r,f r.1*g (π r.2.1)*h (π r.2.2) ∂ (expandedProbability G U₁ U₂ hG hB:Measure (Expanded Sphere)))-
      (∫ q,f q ∂ (edgeProbability G U₁ U₂ hG hB:Measure (Quad Sphere)))*
        (∫ z,g z ∂ uniformLaw (fun x => π (U₁ x,U₂ x)))*(∫ z,h z ∂ uniformLaw (fun x => π (U₁ x,U₂ x)))|≤
      C*(H₂*testDiscrep G.fiberWeight G.targets (fun x => g (π (U₁ x,U₂ x)))+
        H₁*testDiscrep G.fiberWeight G.targets (fun x => h (π (U₁ x,U₂ x)))) := by
  rw [integral_expandedProbability,integral_edgeProbability,integral_uniformLaw,integral_uniformLaw]
  have hA : |∑ x,prob (Finset.univ : Finset V) x*g (π (U₁ x,U₂ x))|≤H₁ := by
    exact avg_abs_bound _ _ _ (Core.Fibers.prob_nn _) (sum_prob _
      (Finset.univ_nonempty_iff.mpr (Fintype.card_pos_iff.mp (by omega)))) (fun x => hg _)
  have hb := mixture_pair_test_bound G.fiberWeight (fun e => prob (G.targets e))
    (fun e y => f (edgeValue G.source U₁ U₂ (e,y))) (fun x => g (π (U₁ x,U₂ x))) (fun x => h (π (U₁ x,U₂ x)))
    (∑ x,prob Finset.univ x*g (π (U₁ x,U₂ x))) (∑ x,prob Finset.univ x*h (π (U₁ x,U₂ x)))
    C H₁ H₂ G.fiberWeight_nonneg (fun e => Core.Fibers.prob_nn _) (fun e => sum_prob _ (hB e))
    hC (fun e y => hf _) (fun x => hh _) hA
  simpa only [tripleValue,testDiscrep,edgeWeight,Fintype.sum_prod_type,mul_assoc,← Finset.mul_sum] using hb

lemma integral_target (U₁ U₂ : V → Sphere) (hG : 0<G.edgeCount)
    (hB : ∀ e,(G.targets e).Nonempty) (g : Sphere × Sphere → ℝ) :
    (∫ q,g q.2.2 ∂ (edgeProbability G U₁ U₂ hG hB:Measure (Quad Sphere)))=
      ∑ y,G.incomingWeight y*g (U₁ y,U₂ y) := by
  rw [integral_edgeProbability]
  simp only [edgeValue,Finset.mul_sum,← mul_assoc]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y _
  rw [← Finset.sum_mul,G.fiber_marginal,G.incoming_marginal]

lemma incoming_law_test_bound (U₁ U₂ : V → Sphere) (hG : 0<G.edgeCount)
    (hB : ∀ e,(G.targets e).Nonempty) (hn : 2≤Fintype.card V) (T H C : ℝ) (hT : 0<T)
    (f : Sphere → ℝ) (g : Sphere × Sphere → ℝ) (hf : ∀ z,|f z|≤H) (hg : ∀ z,|g z|≤C) :
    |(∫ q,f q.1*g q.2.2 ∂ (edgeProbability G U₁ U₂ hG hB:Measure (Quad Sphere)))-
      (∫ z,f z ∂ uniformLaw U₁)*(∫ q,g q.2.2 ∂ (edgeProbability G U₁ U₂ hG hB:Measure (Quad Sphere)))|≤
      C*(testDiscrep (G.retainedWeight T) (G.retainedSet T) (fun x => f (U₁ x))+2*H*G.omittedMass T) := by
  rw [integral_target,integral_edgeProbability,integral_uniformLaw]
  exact incoming_test_bound G T H C hT hn (fun x => f (U₁ x)) (fun x => g (U₁ x,U₂ x))
    (fun x => hf _) (fun x => hg _)

end WeakPinned.Bounded

end
end
section
noncomputable section
open MeasureTheory Filter
open scoped BigOperators Topology BoundedContinuousFunction
namespace WeakPinned.Bounded
attribute [local instance] OAI.WeakPinned.Bounded.instMeasurableSpaceSphere_7
local instance instBorelSpaceSphere_7_rdb9730_1 : BorelSpace Sphere := ⟨rfl⟩
variable {V : ℕ → Type u10} {I : ℕ → Type u11} [∀ n,Fintype (V n)] [∀ n,DecidableEq (V n)] [∀ n,Fintype (I n)]
variable (G : ∀ n,Core.Fibers (V n) (I n)) (U₁ U₂ : ∀ n,V n → Sphere)
  (hG : ∀ n,0<(G n).edgeCount) (hB : ∀ n e,((G n).targets e).Nonempty)
  (hn : ∀ n,2≤Fintype.card (V n))

include hn
lemma expanded_test_rate (π : Sphere × Sphere → Sphere)
    (hd : ∀ f : C(Sphere,ℝ),Tendsto (fun n => testDiscrep (G n).fiberWeight (G n).targets
      (fun x => f (π (U₁ n x,U₂ n x)))) atTop (𝓝 0))
    (f : Quad Sphere →ᵇ ℝ) (g h : Sphere →ᵇ ℝ) :
    Tendsto (fun n => (∫ r,f r.1*g (π r.2.1)*h (π r.2.2)
      ∂ (expandedProbability (G n) (U₁ n) (U₂ n) (hG n) (hB n):Measure (Expanded Sphere)))-
      (∫ q,f q ∂ (edgeProbability (G n) (U₁ n) (U₂ n) (hG n) (hB n):Measure (Quad Sphere)))*
        (∫ z,g z ∂ uniformLaw (fun x => π (U₁ n x,U₂ n x)))*
        (∫ z,h z ∂ uniformLaw (fun x => π (U₁ n x,U₂ n x)))) atTop (𝓝 0) := by
  apply (tendsto_zero_iff_abs_tendsto_zero _).mpr
  have ht := ((hd g.toContinuousMap).const_mul ‖h‖ |>.add
    ((hd h.toContinuousMap).const_mul ‖g‖)).const_mul ‖f‖
  simp only [mul_zero,zero_add] at ht
  apply squeeze_zero (fun n => abs_nonneg _) (fun n => ?_) ht
  exact expanded_test_bound (G n) (U₁ n) (U₂ n) (hG n) (hB n) (hn n) π f g h
    ‖f‖ ‖g‖ ‖h‖ (norm_nonneg _) (fun q => by simpa only [Real.norm_eq_abs] using f.norm_coe_le_norm q)
    (fun z => by simpa only [Real.norm_eq_abs] using g.norm_coe_le_norm z)
    (fun z => by simpa only [Real.norm_eq_abs] using h.norm_coe_le_norm z)

lemma incoming_law_test_rate (T : ℕ → ℝ) (hT : ∀ n,0<T n)
    (hd : ∀ f : C(Sphere,ℝ),Tendsto (fun n => testDiscrep ((G n).retainedWeight (T n))
      ((G n).retainedSet (T n)) (fun x => f (U₁ n x))) atTop (𝓝 0))
    (ho : Tendsto (fun n => (G n).omittedMass (T n)) atTop (𝓝 0))
    (f : Sphere →ᵇ ℝ) (g : Sphere × Sphere →ᵇ ℝ) :
    Tendsto (fun n => (∫ q,f q.1*g q.2.2 ∂ (edgeProbability (G n) (U₁ n) (U₂ n) (hG n) (hB n):Measure (Quad Sphere)))-
      (∫ z,f z ∂ uniformLaw (U₁ n))*(∫ q,g q.2.2 ∂ (edgeProbability (G n) (U₁ n) (U₂ n) (hG n) (hB n):Measure (Quad Sphere))))
      atTop (𝓝 0) := by
  apply (tendsto_zero_iff_abs_tendsto_zero _).mpr
  have ht := ((hd f.toContinuousMap).add (ho.const_mul (2*‖f‖))).const_mul ‖g‖
  simp only [mul_zero,zero_add] at ht
  apply squeeze_zero (fun n => abs_nonneg _) (fun n => ?_) ht
  exact incoming_law_test_bound (G n) (U₁ n) (U₂ n) (hG n) (hB n) (hn n) (T n) ‖f‖ ‖g‖ (hT n) f g
    (fun z => by simpa only [Real.norm_eq_abs] using f.norm_coe_le_norm z)
    (fun z => by simpa only [Real.norm_eq_abs] using g.norm_coe_le_norm z)

end WeakPinned.Bounded

end
end

end OAI
end

section
-- module Solutions.OAIQW_WeakPinned.ProductLimits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u1 u2 u3 u4 u5 u6 u7 u8 u9 u10 u11 u12
universe u13 u14

section
noncomputable section
open MeasureTheory Filter
open scoped Topology BigOperators BoundedContinuousFunction
namespace WeakPinned.Bounded

variable {E : Type u1} {X : Type u2} {J : Type u3} [MeasurableSpace E] [MeasurableSpace X]
  [TopologicalSpace E] [TopologicalSpace X] [BorelSpace E] [BorelSpace X]
  [SecondCountableTopology E] [SecondCountableTopology X]
  [HasOuterApproxClosed E] [HasOuterApproxClosed X] [Fintype J]

omit [SecondCountableTopology E] in
lemma weak_product_limit
    (Rn : ℕ → ProbabilityMeasure (E × (J → X))) (R : ProbabilityMeasure (E × (J → X)))
    (Qn : ℕ → ProbabilityMeasure E) (Q : ProbabilityMeasure E)
    (αn : ℕ → J → ProbabilityMeasure X) (β : J → ProbabilityMeasure X)
    (hR : Tendsto Rn atTop (𝓝 R)) (hQ : Tendsto Qn atTop (𝓝 Q))
    (hα : ∀ j,Tendsto (fun n => αn n j) atTop (𝓝 (β j)))
    (herr : ∀ (f : E →ᵇ ℝ) (g : J → X →ᵇ ℝ),
      Tendsto (fun n => (∫ p,f p.1*(∏ j,g j (p.2 j)) ∂ (Rn n : Measure (E × (J → X))))-
        (∫ e,f e ∂ (Qn n : Measure E))*(∏ j,∫ x,g j x ∂ (αn n j : Measure X))) atTop (𝓝 0)) :
    (R : Measure (E × (J → X)))=(Q : Measure E).prod (Measure.pi (fun j => (β j : Measure X))) := by
  apply Measure.eq_prod_of_integral_mul_prod_boundedContinuousFunction
  intro f g
  let F : E × (J → X) →ᵇ ℝ :=
    f.compContinuous ⟨Prod.fst,continuous_fst⟩ *
      ∏ j,(g j).compContinuous ⟨fun p : E × (J → X) => p.2 j,by fun_prop⟩
  have hRf := ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hR F
  have hQf := ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hQ f
  have hβg (j) := ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp (hα j) (g j)
  have ht := hRf.sub (hQf.mul (tendsto_finsetProd Finset.univ (fun j _ => hβg j)))
  have hF (p : E × (J → X)) : F p=f p.1 * ∏ j,g j (p.2 j) := by simp [F]
  simp only [hF] at ht
  have he := tendsto_nhds_unique ht (herr f g)
  rw [integral_fintype_prod_eq_prod]
  exact sub_eq_zero.mp he

end WeakPinned.Bounded

end
end
section
noncomputable section
open MeasureTheory Filter
open scoped Topology BigOperators BoundedContinuousFunction
namespace WeakPinned.Bounded

lemma weak_pair_product_limit {X : Type u4} {Y : Type u5} [MeasurableSpace X] [MeasurableSpace Y]
    [TopologicalSpace X] [TopologicalSpace Y] [BorelSpace X] [BorelSpace Y]
    [HasOuterApproxClosed X] [HasOuterApproxClosed Y]
    [SecondCountableTopology X] [SecondCountableTopology Y]
    (Rn : ℕ → ProbabilityMeasure (X × Y)) (R : ProbabilityMeasure (X × Y))
    (μn : ℕ → ProbabilityMeasure X) (μ : ProbabilityMeasure X)
    (νn : ℕ → ProbabilityMeasure Y) (ν : ProbabilityMeasure Y)
    (hR : Tendsto Rn atTop (𝓝 R)) (hμ : Tendsto μn atTop (𝓝 μ)) (hν : Tendsto νn atTop (𝓝 ν))
    (herr : ∀ (f : X →ᵇ ℝ) (g : Y →ᵇ ℝ),
      Tendsto (fun n => (∫ p,f p.1*g p.2 ∂ (Rn n : Measure (X × Y)))-
        (∫ x,f x ∂ (μn n : Measure X))*(∫ y,g y ∂ (νn n : Measure Y))) atTop (𝓝 0)) :
    (R : Measure (X × Y))=(μ : Measure X).prod (ν : Measure Y) := by
  apply Measure.eq_prod_of_integral_mul_boundedContinuousFunction
  intro f g
  let F : X × Y →ᵇ ℝ := f.compContinuous ⟨Prod.fst,continuous_fst⟩ *
    g.compContinuous ⟨Prod.snd,continuous_snd⟩
  have ht := (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hR F).sub
    ((ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hμ f).mul
      (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hν g))
  exact sub_eq_zero.mp (tendsto_nhds_unique ht (herr f g))

lemma pair_of_pi_map {T : Type u6} {E : Type u7} {X : Type u8} [MeasurableSpace T] [MeasurableSpace E] [MeasurableSpace X]
    (R : Measure T) (Q : Measure E) (μ : Measure X) [SFinite Q] [IsFiniteMeasure μ]
    (e : T → E) (z w : T → X) (he : Measurable e) (hz : Measurable z) (hw : Measurable w)
    (hm : R.map (fun r => (e r,![z r,w r]))=Q.prod (Measure.pi (fun _ : Fin 2 => μ))) :
    R.map (fun r => (e r,(z r,w r)))=Q.prod (μ.prod μ) := by
  have hp : Measurable (fun r => (e r,![z r,w r])) := by
    apply he.prodMk
    apply Measurable.of_eval
    intro j
    fin_cases j
    · exact hz
    · exact hw
  let hme := MeasurableEquiv.finTwoArrow (α:=X)
  have hm2 : Measurable (Prod.map (id : E → E) hme) := measurable_id.prodMap hme.measurable
  have hh := congrArg (fun m : Measure (E × (Fin 2 → X)) => m.map (Prod.map id hme)) hm
  rw [Measure.map_map hm2 hp,← Measure.map_prod_map _ _ measurable_id hme.measurable,
    Measure.map_id,(measurePreserving_finTwoArrow μ).map_eq] at hh
  exact hh

end WeakPinned.Bounded

end
end
section
noncomputable section
open MeasureTheory Filter
open scoped Topology BigOperators BoundedContinuousFunction
namespace WeakPinned.Bounded

variable {E : Type u9} {X : Type u10} {T : Type u11} [MeasurableSpace E] [MeasurableSpace X] [MeasurableSpace T]
  [TopologicalSpace E] [TopologicalSpace X] [TopologicalSpace T]
  [BorelSpace E] [BorelSpace X] [BorelSpace T]
  [SecondCountableTopology E] [SecondCountableTopology X]
  [HasOuterApproxClosed E] [HasOuterApproxClosed X]

lemma weak_double_product_limit (Rn : ℕ → ProbabilityMeasure T) (R : ProbabilityMeasure T)
    (Qn : ℕ → ProbabilityMeasure E) (Q : ProbabilityMeasure E)
    (αn : ℕ → ProbabilityMeasure X) (β : ProbabilityMeasure X)
    (e : T → E) (z w : T → X) (he : Continuous e) (hz : Continuous z) (hw : Continuous w)
    (hR : Tendsto Rn atTop (𝓝 R)) (hQ : Tendsto Qn atTop (𝓝 Q)) (hα : Tendsto αn atTop (𝓝 β))
    (herr : ∀ (f : E →ᵇ ℝ) (g h : X →ᵇ ℝ),
      Tendsto (fun n => (∫ r,f (e r)*g (z r)*h (w r) ∂ (Rn n : Measure T))-
        (∫ q,f q ∂ (Qn n : Measure E))*(∫ x,g x ∂ (αn n : Measure X))*
          (∫ x,h x ∂ (αn n : Measure X))) atTop (𝓝 0)) :
    (R:Measure T).map (fun r => (e r,(z r,w r)))=(Q:Measure E).prod ((β:Measure X).prod β) := by
  let k : T → E × (Fin 2 → X) := fun r => (e r,![z r,w r])
  have hk : Continuous k := by
    apply he.prodMk
    apply continuous_pi
    intro i
    fin_cases i
    · exact hz
    · exact hw
  have hRm := ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous Rn R hR hk
  have hh := weak_product_limit (fun n => (Rn n).map hk.measurable.aemeasurable)
    (R.map hk.measurable.aemeasurable) Qn Q (fun n _ => αn n) (fun _ : Fin 2 => β) hRm hQ (fun _ => hα) ?_
  · exact pair_of_pi_map (R:Measure T) (Q:Measure E) (β:Measure X) e z w he.measurable hz.measurable hw.measurable hh
  · intro f g
    have hl := herr f (g 0) (g 1)
    convert hl using 1
    funext n
    rw [show ((Rn n).map hk.measurable.aemeasurable : Measure (E × (Fin 2 → X)))=(Rn n:Measure T).map k from rfl]
    rw [integral_map_of_stronglyMeasurable hk.measurable (by fun_prop)]
    simp only [Fin.prod_univ_two,k,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_fin_one,mul_assoc]

end WeakPinned.Bounded

end
end
section
noncomputable section
open MeasureTheory Filter
open scoped Topology ENNReal NNReal BoundedContinuousFunction
namespace WeakPinned.Bounded

variable {X : Type u12} [MeasurableSpace X] [TopologicalSpace X] [BorelSpace X]
  [TopologicalSpace.PseudoMetrizableSpace X]

lemma measure_le_of_continuous_lintegral (μ ν : Measure X) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h : ∀ f : X →ᵇ ℝ≥0,(∫⁻ x,f x ∂ μ)≤∫⁻ x,f x ∂ ν) : μ≤ν := by
  have hclosed (K : Set X) (hK : IsClosed K) : μ K≤ν K := by
    exact le_of_tendsto_of_tendsto
      (HasOuterApproxClosed.tendsto_lintegral_apprSeq hK μ)
      (HasOuterApproxClosed.tendsto_lintegral_apprSeq hK ν)
      (Eventually.of_forall (fun n => h (hK.apprSeq n)))
  apply Measure.le_iff.mpr
  intro s hs
  rw [hs.measure_eq_iSup_isClosed_of_ne_top (measure_ne_top μ s)]
  exact iSup_le (fun K => iSup_le (fun hKs => iSup_le (fun hK => (hclosed K hK).trans (measure_mono hKs))))

lemma weak_domination (μn νn : ℕ → ProbabilityMeasure X) (μ ν : ProbabilityMeasure X)
    (hμ : Tendsto μn atTop (𝓝 μ)) (hν : Tendsto νn atTop (𝓝 ν)) (c : ℝ≥0)
    (hle : ∀ n,(μn n : Measure X)≤(c:ℝ≥0∞) • (νn n : Measure X)) :
    (μ : Measure X)≤(c:ℝ≥0∞) • (ν : Measure X) := by
  have : IsFiniteMeasure ((c:ℝ≥0∞) • (ν:Measure X)) := (ν:Measure X).smul_finite ENNReal.coe_ne_top
  apply measure_le_of_continuous_lintegral
  intro f
  have hμf := ProbabilityMeasure.tendsto_iff_forall_lintegral_tendsto.mp hμ f
  have hνf := ProbabilityMeasure.tendsto_iff_forall_lintegral_tendsto.mp hν f
  rw [lintegral_smul_measure]
  apply le_of_tendsto_of_tendsto hμf
    (ENNReal.Tendsto.const_mul hνf (Or.inr ENNReal.coe_ne_top))
  filter_upwards [] with n
  simpa only [lintegral_smul_measure,smul_eq_mul] using lintegral_mono' (hle n) (le_refl (fun x => (f x:ℝ≥0∞)))

end WeakPinned.Bounded

end
end
section
noncomputable section
open MeasureTheory Filter
open scoped Topology NNReal ENNReal
namespace WeakPinned.Bounded
variable {X : Type u13} {Y : Type u14} [MeasurableSpace X] [MeasurableSpace Y]
  [TopologicalSpace X] [TopologicalSpace Y] [BorelSpace X] [BorelSpace Y]
  [HasOuterApproxClosed Y]

lemma weak_map_eq (αn : ℕ → ProbabilityMeasure X) (α : ProbabilityMeasure X)
    (βn : ℕ → ProbabilityMeasure Y) (β : ProbabilityMeasure Y)
    (f : X → Y) (hf : Continuous f) (hα : Tendsto αn atTop (𝓝 α))
    (hβ : Tendsto βn atTop (𝓝 β)) (hm : ∀ n,(αn n:Measure X).map f=(βn n:Measure Y)) :
    (α:Measure X).map f=(β:Measure Y) := by
  have he (n) : (αn n).map hf.measurable.aemeasurable=βn n := ProbabilityMeasure.toMeasure_injective (hm n)
  have hl := ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous αn α hα hf
  simp only [he] at hl
  exact congrArg ProbabilityMeasure.toMeasure (tendsto_nhds_unique hl hβ)

omit [HasOuterApproxClosed Y] in
lemma weak_map_domination [TopologicalSpace.PseudoMetrizableSpace Y]
    (αn : ℕ → ProbabilityMeasure X) (α : ProbabilityMeasure X)
    (βn : ℕ → ProbabilityMeasure Y) (β : ProbabilityMeasure Y)
    (f : X → Y) (hf : Continuous f) (hα : Tendsto αn atTop (𝓝 α))
    (hβ : Tendsto βn atTop (𝓝 β)) (c : ℝ≥0)
    (hm : ∀ n,(αn n:Measure X).map f≤(c:ℝ≥0∞) • (βn n:Measure Y)) :
    (α:Measure X).map f≪(β:Measure Y) := by
  have hl := weak_domination (fun n => (αn n).map hf.measurable.aemeasurable)
    βn (α.map hf.measurable.aemeasurable) β
    (ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous αn α hα hf) hβ c hm
  exact Measure.absolutelyContinuous_of_le_smul hl

end WeakPinned.Bounded

end
end

end OAI
end

section
-- module Solutions.OAIQW_WeakPinned.MeasureLimits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u1 u2 u3 u4 u5 u6

section
noncomputable section
open MeasureTheory Filter
open scoped BigOperators Topology BoundedContinuousFunction NNReal ENNReal
namespace WeakPinned.Bounded
attribute [local instance] OAI.WeakPinned.Bounded.instMeasurableSpaceSphere_8
attribute [local instance] OAI.WeakPinned.Bounded.instBorelSpaceSphere_8
variable {V : ℕ → Type u1} {I : ℕ → Type u2} [∀ n,Fintype (V n)] [∀ n,DecidableEq (V n)] [∀ n,Fintype (I n)]
variable (G : ∀ n,Core.Fibers (V n) (I n)) (U₁ U₂ : ∀ n,V n → Sphere)
  (hG : ∀ n,0<(G n).edgeCount) (hB : ∀ n e,((G n).targets e).Nonempty)
  (hn : ∀ n,2≤Fintype.card (V n))

lemma expanded_marginal_limit (π : Sphere × Sphere → Sphere) (hπ : Continuous π)
    (β : ProbabilityMeasure Sphere) (Q : ProbabilityMeasure (Quad Sphere))
    (R : ProbabilityMeasure (Expanded Sphere))
    (hα : Tendsto (fun n => uniformProbability (fun x => π (U₁ n x,U₂ n x)) (by have:=hn n;omega)) atTop (𝓝 β))
    (hQ : Tendsto (fun n => edgeProbability (G n) (U₁ n) (U₂ n) (hG n) (hB n)) atTop (𝓝 Q))
    (hR : Tendsto (fun n => expandedProbability (G n) (U₁ n) (U₂ n) (hG n) (hB n)) atTop (𝓝 R))
    (hd : ∀ f : C(Sphere,ℝ),Tendsto (fun n => testDiscrep (G n).fiberWeight (G n).targets
      (fun x => f (π (U₁ n x,U₂ n x)))) atTop (𝓝 0)) :
    (R:Measure (Expanded Sphere)).map (fun r => (r.1,(π r.2.1,π r.2.2)))=
      (Q:Measure (Quad Sphere)).prod ((β:Measure Sphere).prod β) := by
  apply weak_double_product_limit (fun n => expandedProbability (G n) (U₁ n) (U₂ n) (hG n) (hB n)) R
    (fun n => edgeProbability (G n) (U₁ n) (U₂ n) (hG n) (hB n)) Q
    (fun n => uniformProbability (fun x => π (U₁ n x,U₂ n x)) (by have:=hn n;omega)) β
    Prod.fst (fun r => π r.2.1) (fun r => π r.2.2) continuous_fst
    (hπ.comp (continuous_fst.comp continuous_snd)) (hπ.comp (continuous_snd.comp continuous_snd)) hR hQ hα
  exact expanded_test_rate G U₁ U₂ hG hB hn π hd

lemma incoming_limit (T : ℕ → ℝ) (hT : ∀ n,0<T n)
    (β : ProbabilityMeasure Sphere) (Q : ProbabilityMeasure (Quad Sphere))
    (hα : Tendsto (fun n => uniformProbability (U₁ n) (by have:=hn n;omega)) atTop (𝓝 β))
    (hQ : Tendsto (fun n => edgeProbability (G n) (U₁ n) (U₂ n) (hG n) (hB n)) atTop (𝓝 Q))
    (hd : ∀ f : C(Sphere,ℝ),Tendsto (fun n => testDiscrep ((G n).retainedWeight (T n))
      ((G n).retainedSet (T n)) (fun x => f (U₁ n x))) atTop (𝓝 0))
    (ho : Tendsto (fun n => (G n).omittedMass (T n)) atTop (𝓝 0)) :
    (Q:Measure (Quad Sphere)).map (fun q => (q.1,q.2.2))=
      (β:Measure Sphere).prod ((Q:Measure (Quad Sphere)).map (fun q => q.2.2)) := by
  let Qn := fun n => edgeProbability (G n) (U₁ n) (U₂ n) (hG n) (hB n)
  have hc : Continuous (fun q : Quad Sphere => (q.1,q.2.2)) := by fun_prop
  have ht : Continuous (fun q : Quad Sphere => q.2.2) := by fun_prop
  apply weak_pair_product_limit (fun n => (Qn n).map hc.measurable.aemeasurable)
    (Q.map hc.measurable.aemeasurable)
    (fun n => uniformProbability (U₁ n) (by have:=hn n;omega)) β
    (fun n => (Qn n).map ht.measurable.aemeasurable) (Q.map ht.measurable.aemeasurable)
    (ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous Qn Q hQ hc) hα
    (ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous Qn Q hQ ht)
  intro f g
  have hh := incoming_law_test_rate G U₁ U₂ hG hB hn T hT hd ho f g
  convert hh using 1
  funext n
  change (∫ q,f q.1*g q.2 ∂ (Qn n:Measure (Quad Sphere)).map (fun q => (q.1,q.2.2)))-
    (∫ z,f z ∂ uniformLaw (U₁ n))*(∫ p,g p ∂ (Qn n:Measure (Quad Sphere)).map (fun q => q.2.2))=_
  rw [integral_map_of_stronglyMeasurable hc.measurable (by fun_prop),
    integral_map_of_stronglyMeasurable ht.measurable g.continuous.stronglyMeasurable]

lemma edge_ac_limit (β₁ β₂ : ProbabilityMeasure Sphere) (Q : ProbabilityMeasure (Quad Sphere))
    (hα₁ : Tendsto (fun n => uniformProbability (U₁ n) (by have:=hn n;omega)) atTop (𝓝 β₁))
    (hα₂ : Tendsto (fun n => uniformProbability (U₂ n) (by have:=hn n;omega)) atTop (𝓝 β₂))
    (hQ : Tendsto (fun n => edgeProbability (G n) (U₁ n) (U₂ n) (hG n) (hB n)) atTop (𝓝 Q))
    (M : ℝ) (hM : 0≤M) (hdom : ∀ n x y,(G n).edgeLaw x y≤M*Variance.pairProb Finset.univ x y) :
    (Q:Measure (Quad Sphere)).map (fun q => (q.1,q.2.2.1))≪(β₁:Measure Sphere).prod β₁ ∧
    (Q:Measure (Quad Sphere)).map (fun q => (q.2.1,q.2.2.2))≪(β₂:Measure Sphere).prod β₂ := by
  let c : ℝ≥0 := ⟨2*M,by positivity⟩
  have hc : (c:ℝ≥0∞)=ENNReal.ofReal (2*M) := by
    rw [ENNReal.ofReal_eq_coe_nnreal (by positivity)]
    rfl
  constructor
  · apply weak_map_domination
      (fun n => edgeProbability (G n) (U₁ n) (U₂ n) (hG n) (hB n)) Q
      (fun n => (uniformProbability (U₁ n) (by have:=hn n;omega)).prod
        (uniformProbability (U₁ n) (by have:=hn n;omega))) (β₁.prod β₁)
      (fun q => (q.1,q.2.2.1)) (by fun_prop) hQ
      (ProbabilityMeasure.continuous_prod.tendsto (β₁,β₁) |>.comp (hα₁.prodMk_nhds hα₁)) c
    intro n
    rw [hc]
    exact edgeProbability_dom₁ (G n) (U₁ n) (U₂ n) (hG n) (hB n) (hn n) M hM (hdom n)
  · apply weak_map_domination
      (fun n => edgeProbability (G n) (U₁ n) (U₂ n) (hG n) (hB n)) Q
      (fun n => (uniformProbability (U₂ n) (by have:=hn n;omega)).prod
        (uniformProbability (U₂ n) (by have:=hn n;omega))) (β₂.prod β₂)
      (fun q => (q.2.1,q.2.2.2)) (by fun_prop) hQ
      (ProbabilityMeasure.continuous_prod.tendsto (β₂,β₂) |>.comp (hα₂.prodMk_nhds hα₂)) c
    intro n
    rw [hc]
    exact edgeProbability_dom₂ (G n) (U₁ n) (U₂ n) (hG n) (hB n) (hn n) M hM (hdom n)

end WeakPinned.Bounded

end
end
section
noncomputable section
open MeasureTheory Filter Set
open scoped Topology
namespace WeakPinned.Bounded

attribute [local instance] OAI.WeakPinned.Bounded.instMeasurableSpaceSphere_9
local instance instBorelSpaceSphere_9 : BorelSpace Sphere := ⟨rfl⟩

lemma quadCoe_range (q : Quad Sphere)
    (h₁ : (q.1,q.2.2.1)∈range pairCoe) (h₂ : (q.2.1,q.2.2.2)∈range pairCoe) :
    q∈range quadCoe := by
  obtain ⟨⟨a,c⟩,ha⟩ := h₁
  obtain ⟨⟨b,d⟩,hb⟩ := h₂
  exact ⟨(a,b,c,d),by ext <;> simp_all [pairCoe,quadCoe,Prod.mk.injEq]⟩

lemma expandedCoe_range (r : Expanded Sphere)
    (h₁ : (r.1,(r.2.1.1,r.2.2.1))∈range (Prod.map quadCoe pairCoe))
    (h₂ : (r.1,(r.2.1.2,r.2.2.2))∈range (Prod.map quadCoe pairCoe)) :
    r∈range expandedCoe := by
  obtain ⟨⟨q,z,w⟩,hz⟩ := h₁
  obtain ⟨⟨q',v,t⟩,hv⟩ := h₂
  refine ⟨(q,((z,v),(w,t))),?_⟩
  have he : quadCoe q=r.1 := congrArg Prod.fst hz
  have hz' := congrArg Prod.snd hz
  have hv' := congrArg Prod.snd hv
  apply Prod.ext he
  dsimp [expandedCoe]
  ext <;> simp_all [pairCoe,Prod.mk.injEq]

lemma map_transport_ac {A : Type u3} {B : Type u4} {X : Type u5} {Y : Type u6} [MeasurableSpace A] [MeasurableSpace B]
    [MeasurableSpace X] [MeasurableSpace Y] (j : A → X) (k : B → Y)
    (hj : Measurable j) (hk : MeasurableEmbedding k)
    (f : A → B) (g : X → Y) (hf : Measurable f) (hg : Measurable g)
    (μ : Measure A) (ν : Measure B) (hcomm : k ∘ f=g ∘ j)
    (hm : (μ.map j).map g≪ν.map k) : μ.map f≪ν := by
  apply map_pull_ac k hk
  rw [Measure.map_map hk.measurable hf,hcomm,← Measure.map_map hg hj]
  exact hm

lemma sphere_quad_finite (μ ν : Measure ℂ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (Q : Measure (Quad Sphere))
    (h₁ : Q.map (fun q => (q.1,q.2.2.1))≪(μ.map OnePoint.some).prod (μ.map OnePoint.some))
    (h₂ : Q.map (fun q => (q.2.1,q.2.2.2))≪(ν.map OnePoint.some).prod (ν.map OnePoint.some)) :
    ∀ᵐ q ∂ Q,q∈range quadCoe := by
  have hpμ := map_full_range pairCoe pairCoe_open.measurableEmbedding (μ.prod μ)
  have hpν := map_full_range pairCoe pairCoe_open.measurableEmbedding (ν.prod ν)
  rw [← Measure.map_prod_map _ _ measurableEmbedding_sphere_coe.measurable
    measurableEmbedding_sphere_coe.measurable] at hpμ hpν
  have hq₁ := (ae_map_iff (by fun_prop) pairCoe_open.measurableEmbedding.measurableSet_range).mp
    (h₁.ae_le hpμ)
  have hq₂ := (ae_map_iff (by fun_prop) pairCoe_open.measurableEmbedding.measurableSet_range).mp
    (h₂.ae_le hpν)
  exact (hq₁.and hq₂).mono (fun q h => quadCoe_range q h.1 h.2)

lemma sphere_expanded_finite (μ ν : Measure ℂ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (Q : Measure (Quad ℂ)) (R : Measure (Expanded Sphere)) [IsProbabilityMeasure Q]
    (h₁ : R.map (fun r => (r.1,(r.2.1.1,r.2.2.1)))=
      (Q.map quadCoe).prod ((μ.map OnePoint.some).prod (μ.map OnePoint.some)))
    (h₂ : R.map (fun r => (r.1,(r.2.1.2,r.2.2.2)))=
      (Q.map quadCoe).prod ((ν.map OnePoint.some).prod (ν.map OnePoint.some))) :
    ∀ᵐ r ∂ R,r∈range expandedCoe := by
  have hj := quadCoe_open.measurableEmbedding.prodMap pairCoe_open.measurableEmbedding
  have hpμ := map_full_range _ hj (Q.prod (μ.prod μ))
  have hpν := map_full_range _ hj (Q.prod (ν.prod ν))
  rw [← Measure.map_prod_map _ _ quadCoe_open.measurableEmbedding.measurable
    pairCoe_open.measurableEmbedding.measurable,
    ← Measure.map_prod_map _ _ measurableEmbedding_sphere_coe.measurable
    measurableEmbedding_sphere_coe.measurable,← h₁] at hpμ
  rw [← Measure.map_prod_map _ _ quadCoe_open.measurableEmbedding.measurable
    pairCoe_open.measurableEmbedding.measurable,
    ← Measure.map_prod_map _ _ measurableEmbedding_sphere_coe.measurable
    measurableEmbedding_sphere_coe.measurable,← h₂] at hpν
  have hq₁ := (ae_map_iff (by fun_prop) hj.measurableSet_range).mp hpμ
  have hq₂ := (ae_map_iff (by fun_prop) hj.measurableSet_range).mp hpν
  exact (hq₁.and hq₂).mono (fun r h => expandedCoe_range r h.1 h.2)

end WeakPinned.Bounded

end
end

end OAI
end

section
-- module Solutions.OAIQW_WeakPinned.FiniteObstruction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u1 u2

section
noncomputable section
open MeasureTheory Filter
namespace WeakPinned.Bounded
lemma no_finite_expanded (μ ν : Measure ℂ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    [NullSingletonClass μ] [NullSingletonClass ν]
    (Q : Measure (Quad ℂ)) (R : Measure (Expanded ℂ))
    [IsProbabilityMeasure Q] [IsProbabilityMeasure R]
    (he : R.map Prod.fst=Q)
    (hm₁ : R.map (fun r => (r.1,(r.2.1.1,r.2.2.1)))=Q.prod (μ.prod μ))
    (hm₂ : R.map (fun r => (r.1,(r.2.1.2,r.2.2.2)))=Q.prod (ν.prod ν))
    (hind : Q.map (fun q => (q.1,q.2.2))=μ.prod (Q.map (fun q => q.2.2)))
    (hac₁ : Q.map (fun q => (q.1,q.2.2.1))≪μ.prod μ)
    (hac₂ : Q.map (fun q => (q.2.1,q.2.2.2))≪ν.prod ν)
    (hz : ∀ᵐ r ∂  R,(r.2.1.1-r.1.1)*(r.2.1.2-r.1.2.1)=
      (r.1.2.2.1-r.1.1)*(r.1.2.2.2-r.1.2.1))
    (hw : ∀ᵐ r ∂  R,(r.2.2.1-r.1.1)*(r.2.2.2-r.1.2.1)=
      (r.1.2.2.1-r.1.1)*(r.1.2.2.2-r.1.2.1)) : False := by
  have hbd : ∀ᵐ q ∂  Q,q.2.1≠q.2.2.2 :=
    (ae_map_iff (μ:=Q) (f:=fun q => (q.2.1,q.2.2.2)) (p:=fun p : ℂ × ℂ => p.1≠p.2) (by fun_prop)
      (measurableSet_eq_fun measurable_fst measurable_snd).compl).mp (hac₂.ae_le (ae_distinct_pair ν))
  have hsupp : ∀ᵐ q ∂  Q,q.2.2.1∈μ.support := by
    have hs : ∀ᵐ p ∂  μ.prod μ,p.2∈μ.support := by
      rw [Measure.ae_prod_iff_ae_ae (μ.isClosed_support.measurableSet.preimage measurable_snd)]
      exact Eventually.of_forall (fun _ => μ.support_mem_ae)
    exact (ae_map_iff (μ:=Q) (f:=fun q => (q.1,q.2.2.1)) (p:=fun p : ℂ × ℂ => p.2∈μ.support) (by fun_prop)
      (μ.isClosed_support.measurableSet.preimage measurable_snd)).mp (hac₁.ae_le hs)
  exact no_energy_law μ ν Q hind hsupp
    (expanded_energy_eq μ ν Q R hm₁ hm₂ (expanded_kernel_eq μ ν Q R he hm₁ hbd hz hw))
end WeakPinned.Bounded

end
end
section
noncomputable section
open MeasureTheory Filter Set
open scoped Topology
namespace WeakPinned.Bounded
attribute [local instance] OAI.WeakPinned.Bounded.instMeasurableSpaceSphere_10
local instance instBorelSpaceSphere_10 : BorelSpace Sphere := ⟨rfl⟩

lemma no_sphere_expanded (β₁ β₂ : ProbabilityMeasure Sphere)
    [NullSingletonClass (β₁ : Measure Sphere)] [NullSingletonClass (β₂ : Measure Sphere)]
    (Q : Measure (Quad Sphere)) (R : Measure (Expanded Sphere))
    [IsProbabilityMeasure Q] [IsProbabilityMeasure R]
    (he : R.map Prod.fst=Q)
    (hm₁ : R.map (fun r => (r.1,(r.2.1.1,r.2.2.1)))=Q.prod ((β₁:Measure Sphere).prod β₁))
    (hm₂ : R.map (fun r => (r.1,(r.2.1.2,r.2.2.2)))=Q.prod ((β₂:Measure Sphere).prod β₂))
    (hind : Q.map (fun q => (q.1,q.2.2))=(β₁:Measure Sphere).prod (Q.map (fun q => q.2.2)))
    (hac₁ : Q.map (fun q => (q.1,q.2.2.1))≪(β₁:Measure Sphere).prod β₁)
    (hac₂ : Q.map (fun q => (q.2.1,q.2.2.2))≪(β₂:Measure Sphere).prod β₂)
    (hz : ∀ᵐ r ∂ R.comap expandedCoe,(r.2.1.1-r.1.1)*(r.2.1.2-r.1.2.1)=
      (r.1.2.2.1-r.1.1)*(r.1.2.2.2-r.1.2.1))
    (hw : ∀ᵐ r ∂ R.comap expandedCoe,(r.2.2.1-r.1.1)*(r.2.2.2-r.1.2.1)=
      (r.1.2.2.1-r.1.1)*(r.1.2.2.2-r.1.2.1)) : False := by
  let μ := finitePart β₁
  let ν := finitePart β₂
  have hμ : μ.map OnePoint.some=(β₁:Measure Sphere) := finitePart_map β₁ (measure_singleton _)
  have hν : ν.map OnePoint.some=(β₂:Measure Sphere) := finitePart_map β₂ (measure_singleton _)
  let : IsProbabilityMeasure μ := finitePart_probability β₁ (measure_singleton _)
  let : IsProbabilityMeasure ν := finitePart_probability β₂ (measure_singleton _)
  let : NullSingletonClass μ := finitePart_nonatomic β₁
  let : NullSingletonClass ν := finitePart_nonatomic β₂
  have hQfin : ∀ᵐ q ∂ Q,q∈range quadCoe := sphere_quad_finite μ ν Q
    (by simpa only [hμ] using hac₁) (by simpa only [hν] using hac₂)
  let Qc := Q.comap quadCoe
  let : IsProbabilityMeasure Qc := chart_probability _ quadCoe_open.measurableEmbedding Q hQfin
  have hQ : Qc.map quadCoe=Q := chart_map_comap _ quadCoe_open.measurableEmbedding Q hQfin
  have hRfin : ∀ᵐ r ∂ R,r∈range expandedCoe := sphere_expanded_finite μ ν Qc R
    (by simpa only [hQ,hμ] using hm₁) (by simpa only [hQ,hν] using hm₂)
  let Rc := R.comap expandedCoe
  let : IsProbabilityMeasure Rc := chart_probability _ expandedCoe_open.measurableEmbedding R hRfin
  have hR : Rc.map expandedCoe=R := chart_map_comap _ expandedCoe_open.measurableEmbedding R hRfin
  have hec : Rc.map Prod.fst=Qc := by
    apply map_transport expandedCoe quadCoe expandedCoe_open.measurableEmbedding.measurable
      quadCoe_open.measurableEmbedding Prod.fst Prod.fst measurable_fst measurable_fst Rc Qc rfl
    rw [hR,hQ,he]
  have hm₁c : Rc.map (fun r => (r.1,(r.2.1.1,r.2.2.1)))=Qc.prod (μ.prod μ) := by
    apply map_transport expandedCoe (Prod.map quadCoe pairCoe)
      expandedCoe_open.measurableEmbedding.measurable
      (quadCoe_open.measurableEmbedding.prodMap pairCoe_open.measurableEmbedding)
      (fun r => (r.1,(r.2.1.1,r.2.2.1))) (fun r => (r.1,(r.2.1.1,r.2.2.1)))
      (by fun_prop) (by fun_prop) Rc (Qc.prod (μ.prod μ)) rfl
    rw [hR,hm₁,← Measure.map_prod_map _ _ quadCoe_open.measurableEmbedding.measurable
      pairCoe_open.measurableEmbedding.measurable,← Measure.map_prod_map _ _
      measurableEmbedding_sphere_coe.measurable measurableEmbedding_sphere_coe.measurable,hQ,hμ]
  have hm₂c : Rc.map (fun r => (r.1,(r.2.1.2,r.2.2.2)))=Qc.prod (ν.prod ν) := by
    apply map_transport expandedCoe (Prod.map quadCoe pairCoe)
      expandedCoe_open.measurableEmbedding.measurable
      (quadCoe_open.measurableEmbedding.prodMap pairCoe_open.measurableEmbedding)
      (fun r => (r.1,(r.2.1.2,r.2.2.2))) (fun r => (r.1,(r.2.1.2,r.2.2.2)))
      (by fun_prop) (by fun_prop) Rc (Qc.prod (ν.prod ν)) rfl
    rw [hR,hm₂,← Measure.map_prod_map _ _ quadCoe_open.measurableEmbedding.measurable
      pairCoe_open.measurableEmbedding.measurable,← Measure.map_prod_map _ _
      measurableEmbedding_sphere_coe.measurable measurableEmbedding_sphere_coe.measurable,hQ,hν]
  have htarget : (Qc.map (fun q => q.2.2)).map pairCoe=Q.map (fun q => q.2.2) := by
    rw [Measure.map_map pairCoe_open.measurableEmbedding.measurable (by fun_prop)]
    change Qc.map ((fun q : Quad Sphere => q.2.2) ∘ quadCoe)=_
    rw [← Measure.map_map (by fun_prop) quadCoe_open.measurableEmbedding.measurable,hQ]
  have hindc : Qc.map (fun q => (q.1,q.2.2))=μ.prod (Qc.map (fun q => q.2.2)) := by
    apply map_transport quadCoe (Prod.map OnePoint.some pairCoe)
      quadCoe_open.measurableEmbedding.measurable
      (measurableEmbedding_sphere_coe.prodMap pairCoe_open.measurableEmbedding)
      (fun q => (q.1,q.2.2)) (fun q => (q.1,q.2.2))
      (by fun_prop) (by fun_prop) Qc (μ.prod (Qc.map (fun q => q.2.2))) rfl
    rw [hQ,hind,← Measure.map_prod_map _ _ measurableEmbedding_sphere_coe.measurable
      pairCoe_open.measurableEmbedding.measurable,hμ,htarget]
  have hac₁c : Qc.map (fun q => (q.1,q.2.2.1))≪μ.prod μ := by
    apply map_transport_ac quadCoe pairCoe quadCoe_open.measurableEmbedding.measurable
      pairCoe_open.measurableEmbedding (fun q => (q.1,q.2.2.1)) (fun q => (q.1,q.2.2.1))
      (by fun_prop) (by fun_prop) Qc (μ.prod μ) rfl
    rw [hQ,← Measure.map_prod_map _ _ measurableEmbedding_sphere_coe.measurable
      measurableEmbedding_sphere_coe.measurable,hμ]
    exact hac₁
  have hac₂c : Qc.map (fun q => (q.2.1,q.2.2.2))≪ν.prod ν := by
    apply map_transport_ac quadCoe pairCoe quadCoe_open.measurableEmbedding.measurable
      pairCoe_open.measurableEmbedding (fun q => (q.2.1,q.2.2.2)) (fun q => (q.2.1,q.2.2.2))
      (by fun_prop) (by fun_prop) Qc (ν.prod ν) rfl
    rw [hQ,← Measure.map_prod_map _ _ measurableEmbedding_sphere_coe.measurable
      measurableEmbedding_sphere_coe.measurable,hν]
    exact hac₂
  exact no_finite_expanded μ ν Qc Rc hec hm₁c hm₂c hindc hac₁c hac₂c hz hw

end WeakPinned.Bounded

end
end
section
noncomputable section
open MeasureTheory Filter Set
open scoped BigOperators Topology
namespace WeakPinned.Bounded
open Variance
attribute [local instance] OAI.WeakPinned.Bounded.instMeasurableSpaceSphere_11
local instance instBorelSpaceSphere_11 : BorelSpace Sphere := ⟨rfl⟩
local instance instMeasurableSingletonClassQuadSphere_1 : MeasurableSingletonClass (Quad Sphere) := inferInstance
local instance instMeasurableSingletonClassProdSphere_1 : MeasurableSingletonClass ((Sphere × Sphere) × (Sphere × Sphere)) := inferInstance
local instance instMeasurableSingletonClassExpandedSphere_1 : MeasurableSingletonClass (Expanded Sphere) := Prod.instMeasurableSingletonClass
variable {V : Type u1} {I : Type u2} [Fintype V] [DecidableEq V] [Fintype I]
variable (G : Core.Fibers V I)

lemma zEquation_closed : IsClosed zEquation := isClosed_eq (by fun_prop) (by fun_prop)
lemma wEquation_closed : IsClosed wEquation := isClosed_eq (by fun_prop) (by fun_prop)

omit [Fintype I] in
lemma tripleWeight_mem {r : I × V × V × V}
    (hr : tripleWeight G.fiberWeight (fun e => prob (G.targets e)) r≠0) :
    r.2.1∈G.targets r.1 ∧ r.2.2.1∈G.targets r.1 ∧ r.2.2.2∈G.targets r.1 := by
  refine ⟨?_,?_,?_⟩
  all_goals
    by_contra h
    simp [tripleWeight,prob,h] at hr

lemma expanded_chart_zero (U₁ U₂ : V → ℂ) (hG : 0<G.edgeCount)
    (hB : ∀ e,(G.targets e).Nonempty)
    (hrel : ∀ e y z,y∈G.targets e → z∈G.targets e →
      (U₁ y-U₁ (G.source e))*(U₂ y-U₂ (G.source e))=
      (U₁ z-U₁ (G.source e))*(U₂ z-U₂ (G.source e))) :
    (expandedProbability G (fun x => (U₁ x:Sphere)) (fun x => (U₂ x:Sphere)) hG hB :
      Measure (Expanded Sphere)) (expandedCoe '' zEquationᶜ)=0 ∧
    (expandedProbability G (fun x => (U₁ x:Sphere)) (fun x => (U₂ x:Sphere)) hG hB :
      Measure (Expanded Sphere)) (expandedCoe '' wEquationᶜ)=0 := by
  have hzero (s : Set (Expanded ℂ))
      (hs : ∀ r,tripleWeight G.fiberWeight (fun e => prob (G.targets e)) r≠0 →
        tripleValue G.source U₁ U₂ r∈s) :
      (expandedProbability G (fun x => (U₁ x:Sphere)) (fun x => (U₂ x:Sphere)) hG hB :
        Measure (Expanded Sphere)) (expandedCoe '' sᶜ)=0 := by
    have hh : ∀ᵐ r ∂  finiteLaw (tripleWeight G.fiberWeight (fun e => prob (G.targets e)))
        (tripleValue G.source (fun x => (U₁ x:Sphere)) (fun x => (U₂ x:Sphere))),
        r∉expandedCoe '' sᶜ := by
      apply finiteLaw_ae
      intro r hr
      rintro ⟨q,hq,hqe⟩
      have he : q=tripleValue G.source U₁ U₂ r := expandedCoe_open.injective hqe
      subst q
      exact hq (hs r hr)
    change (finiteLaw (tripleWeight G.fiberWeight (fun e => prob (G.targets e)))
      (tripleValue G.source (fun x => (U₁ x:Sphere)) (fun x => (U₂ x:Sphere)))) (expandedCoe '' sᶜ)=0
    simpa only [not_not, Set.ofPred_mem_eq] using ae_iff.mp hh
  constructor
  · apply hzero
    intro r hr
    have hm := tripleWeight_mem G hr
    exact hrel r.1 r.2.2.1 r.2.1 hm.2.1 hm.1
  · apply hzero
    intro r hr
    have hm := tripleWeight_mem G hr
    exact hrel r.1 r.2.2.2 r.2.1 hm.2.2 hm.1

end WeakPinned.Bounded

end
end

end OAI
end

section
-- module Solutions.OAIQW_WeakPinned.LimitObstruction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u1 u2

section
noncomputable section
open MeasureTheory Filter Set
open scoped Topology
namespace WeakPinned.Bounded
attribute [local instance] OAI.WeakPinned.Bounded.instMeasurableSpaceSphere_12
attribute [local instance] OAI.WeakPinned.Bounded.instBorelSpaceSphere_12
variable {V : ℕ → Type u1} {I : ℕ → Type u2} [∀ n,Fintype (V n)] [∀ n,DecidableEq (V n)] [∀ n,Fintype (I n)]

/-- The actual finite expanded graph laws cannot have nonatomic coordinate limits
and the two test-independence properties supplied by the variance estimates. -/
theorem graph_limit_impossible
    (G : ∀ n,Core.Fibers (V n) (I n)) (U₁ U₂ : ∀ n,V n → ℂ)
    (hG : ∀ n,0<(G n).edgeCount) (hB : ∀ n e,((G n).targets e).Nonempty)
    (hn : ∀ n,2≤Fintype.card (V n))
    (β₁ β₂ : ProbabilityMeasure Sphere) (Q : ProbabilityMeasure (Quad Sphere))
    (R : ProbabilityMeasure (Expanded Sphere))
    [NullSingletonClass (β₁:Measure Sphere)] [NullSingletonClass (β₂:Measure Sphere)]
    (hα₁ : Tendsto (fun n => uniformProbability (fun x => (U₁ n x:Sphere)) (by have:=hn n;omega)) atTop (𝓝 β₁))
    (hα₂ : Tendsto (fun n => uniformProbability (fun x => (U₂ n x:Sphere)) (by have:=hn n;omega)) atTop (𝓝 β₂))
    (hQ : Tendsto (fun n => edgeProbability (G n) (fun x => (U₁ n x:Sphere))
      (fun x => (U₂ n x:Sphere)) (hG n) (hB n)) atTop (𝓝 Q))
    (hR : Tendsto (fun n => expandedProbability (G n) (fun x => (U₁ n x:Sphere))
      (fun x => (U₂ n x:Sphere)) (hG n) (hB n)) atTop (𝓝 R))
    (hd₁ : ∀ f : C(Sphere,ℝ),Tendsto (fun n => testDiscrep (G n).fiberWeight (G n).targets
      (fun x => f (U₁ n x:Sphere))) atTop (𝓝 0))
    (hd₂ : ∀ f : C(Sphere,ℝ),Tendsto (fun n => testDiscrep (G n).fiberWeight (G n).targets
      (fun x => f (U₂ n x:Sphere))) atTop (𝓝 0))
    (T : ℕ → ℝ) (hT : ∀ n,0<T n)
    (hdR : ∀ f : C(Sphere,ℝ),Tendsto (fun n => testDiscrep ((G n).retainedWeight (T n))
      ((G n).retainedSet (T n)) (fun x => f (U₁ n x:Sphere))) atTop (𝓝 0))
    (ho : Tendsto (fun n => (G n).omittedMass (T n)) atTop (𝓝 0))
    (M : ℝ) (hM : 0≤M) (hdom : ∀ n x y,(G n).edgeLaw x y≤M*Variance.pairProb Finset.univ x y)
    (hrel : ∀ n e y z,y∈(G n).targets e → z∈(G n).targets e →
      (U₁ n y-U₁ n ((G n).source e))*(U₂ n y-U₂ n ((G n).source e))=
      (U₁ n z-U₁ n ((G n).source e))*(U₂ n z-U₂ n ((G n).source e))) : False := by
  let : TopologicalSpace.PseudoMetrizableSpace Sphere := inferInstance
  let : TopologicalSpace.PseudoMetrizableSpace (Quad Sphere) := inferInstance
  let : TopologicalSpace.PseudoMetrizableSpace (Sphere × Sphere) := inferInstance
  let : TopologicalSpace.PseudoMetrizableSpace (Expanded Sphere) := inferInstance
  let S₁ := fun n x => (U₁ n x:Sphere)
  let S₂ := fun n x => (U₂ n x:Sphere)
  have hm₁ := expanded_marginal_limit G S₁ S₂ hG hB hn Prod.fst continuous_fst β₁ Q R hα₁ hQ hR hd₁
  have hm₂ := expanded_marginal_limit G S₁ S₂ hG hB hn Prod.snd continuous_snd β₂ Q R hα₂ hQ hR hd₂
  have he := weak_map_eq
    (fun n => expandedProbability (G n) (S₁ n) (S₂ n) (hG n) (hB n)) R
    (fun n => edgeProbability (G n) (S₁ n) (S₂ n) (hG n) (hB n)) Q
    Prod.fst continuous_fst hR hQ
    (fun n => expandedProbability_edge (G n) (S₁ n) (S₂ n) (hG n) (hB n))
  have hi := incoming_limit G S₁ S₂ hG hB hn T hT β₁ Q hα₁ hQ hdR ho
  have hac := edge_ac_limit G S₁ S₂ hG hB hn β₁ β₂ Q hα₁ hα₂ hQ M hM hdom
  have hz := weak_chart_closed expandedCoe expandedCoe_open
    (fun n => expandedProbability (G n) (S₁ n) (S₂ n) (hG n) (hB n)) R hR
    zEquation zEquation_closed
    (fun n => (expanded_chart_zero (G n) (U₁ n) (U₂ n) (hG n) (hB n) (hrel n)).1)
  have hw := weak_chart_closed expandedCoe expandedCoe_open
    (fun n => expandedProbability (G n) (S₁ n) (S₂ n) (hG n) (hB n)) R hR
    wEquation wEquation_closed
    (fun n => (expanded_chart_zero (G n) (U₁ n) (U₂ n) (hG n) (hB n) (hrel n)).2)
  exact no_sphere_expanded β₁ β₂ Q R he hm₁ hm₂ hi hac.1 hac.2 hz hw

end WeakPinned.Bounded

end
end

end OAI
end

section
-- module Solutions.OAIQW_WeakPinned.NormalizedGraphs
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u1 u2

section
noncomputable section
open MeasureTheory Filter Set
open scoped Topology BigOperators
namespace WeakPinned.Bounded
attribute [local instance] OAI.WeakPinned.Bounded.instMeasurableSpaceSphere_13
local instance instBorelSpaceSphere_13 : BorelSpace Sphere := ⟨rfl⟩
variable {V : ℕ → Type u1} {I : ℕ → Type u2} [∀ n,Fintype (V n)] [∀ n,DecidableEq (V n)] [∀ n,Fintype (I n)]

/-- Compactness is applied to the four genuine empirical graph laws together.
The only asymptotic hypotheses are the proved test-discrepancy estimates. -/
theorem normalized_graph_impossible
    (G : ∀ n,Core.Fibers (V n) (I n)) (u₁ u₂ : ∀ n,V n → ℂ)
    (x₁ x₂ : ∀ n,V n) (hu₁ : ∀ n,Function.Injective (u₁ n)) (hu₂ : ∀ n,Function.Injective (u₂ n))
    (hG : ∀ n,0<(G n).edgeCount) (hB : ∀ n e,((G n).targets e).Nonempty)
    (hn : ∀ n,2≤Fintype.card (V n))
    (hcard : Tendsto (fun n => (Fintype.card (V n):ℝ)) atTop atTop)
    (C : ℝ) (hC : 0≤C) (hlog₁ : ∀ n,logAverage (u₁ n)≤C) (hlog₂ : ∀ n,logAverage (u₂ n)≤C)
    (hx₁ : ∀ n,(∑ y,logCost (u₁ n) (x₁ n) y)≤C*(Fintype.card (V n):ℝ))
    (hx₂ : ∀ n,(∑ y,logCost (u₂ n) (x₂ n) y)≤C*(Fintype.card (V n):ℝ))
    (hd₁ : ∀ f : C(Sphere,ℝ),Tendsto (fun n => testDiscrep (G n).fiberWeight (G n).targets
      (fun x => f ((u₁ n x-u₁ n (x₁ n)):Sphere))) atTop (𝓝 0))
    (hd₂ : ∀ f : C(Sphere,ℝ),Tendsto (fun n => testDiscrep (G n).fiberWeight (G n).targets
      (fun x => f ((u₂ n x-u₂ n (x₂ n)):Sphere))) atTop (𝓝 0))
    (T : ℕ → ℝ) (hT : ∀ n,0<T n)
    (hdR : ∀ f : C(Sphere,ℝ),Tendsto (fun n => testDiscrep ((G n).retainedWeight (T n))
      ((G n).retainedSet (T n)) (fun x => f ((u₁ n x-u₁ n (x₁ n)):Sphere))) atTop (𝓝 0))
    (ho : Tendsto (fun n => (G n).omittedMass (T n)) atTop (𝓝 0))
    (M : ℝ) (hM : 0≤M) (hdom : ∀ n x y,(G n).edgeLaw x y≤M*Variance.pairProb Finset.univ x y)
    (hrel : ∀ n e y z,y∈(G n).targets e → z∈(G n).targets e →
      (u₁ n y-u₁ n ((G n).source e))*(u₂ n y-u₂ n ((G n).source e))=
      (u₁ n z-u₁ n ((G n).source e))*(u₂ n z-u₂ n ((G n).source e))) : False := by
  let : TopologicalSpace.PseudoMetrizableSpace Sphere := inferInstance
  let : TopologicalSpace.PseudoMetrizableSpace (Quad Sphere) := inferInstance
  let : TopologicalSpace.PseudoMetrizableSpace (Sphere × Sphere) := inferInstance
  let : TopologicalSpace.PseudoMetrizableSpace (Expanded Sphere) := inferInstance
  let : TopologicalSpace (ProbabilityMeasure Sphere) := inferInstance
  let : TopologicalSpace (ProbabilityMeasure (Quad Sphere)) := inferInstance
  let : TopologicalSpace (ProbabilityMeasure (Expanded Sphere)) := inferInstance
  let : CompactSpace (Quad Sphere) := inferInstance
  let : CompactSpace (Expanded Sphere) := inferInstance
  let : CompactSpace (ProbabilityMeasure Sphere) := inferInstance
  let : CompactSpace (ProbabilityMeasure (Quad Sphere)) := inferInstance
  let : CompactSpace (ProbabilityMeasure (Expanded Sphere)) := inferInstance
  let U₁ := fun n x => u₁ n x-u₁ n (x₁ n)
  let U₂ := fun n x => u₂ n x-u₂ n (x₂ n)
  let α₁ := fun n => uniformProbability (fun x => (U₁ n x:Sphere)) (by have:=hn n;omega)
  let α₂ := fun n => uniformProbability (fun x => (U₂ n x:Sphere)) (by have:=hn n;omega)
  let Qn := fun n => edgeProbability (G n) (fun x => (U₁ n x:Sphere))
    (fun x => (U₂ n x:Sphere)) (hG n) (hB n)
  let Rn := fun n => expandedProbability (G n) (fun x => (U₁ n x:Sphere))
    (fun x => (U₂ n x:Sphere)) (hG n) (hB n)
  let L := fun n => (α₁ n,α₂ n,Qn n,Rn n)
  obtain ⟨l,_,φ,hφ,hl⟩ := isCompact_univ.tendsto_subseq (fun n => mem_univ (L n))
  have ha₁ : Tendsto (α₁ ∘ φ) atTop (𝓝 l.1) := continuous_fst.tendsto l |>.comp hl
  have ha₂ : Tendsto (α₂ ∘ φ) atTop (𝓝 l.2.1) :=
    (continuous_fst.comp continuous_snd).tendsto l |>.comp hl
  have hq : Tendsto (Qn ∘ φ) atTop (𝓝 l.2.2.1) :=
    (continuous_fst.comp (continuous_snd.comp continuous_snd)).tendsto l |>.comp hl
  have hr : Tendsto (Rn ∘ φ) atTop (𝓝 l.2.2.2) :=
    (continuous_snd.comp (continuous_snd.comp continuous_snd)).tendsto l |>.comp hl
  let : NullSingletonClass (l.1:Measure Sphere) := normalized_empirical_nonatomic
    (fun n => u₁ (φ n)) (fun n => x₁ (φ n)) (fun n => hu₁ (φ n)) (fun n => hn (φ n))
    (hcard.comp hφ.tendsto_atTop) C hC (fun n => hlog₁ (φ n)) (fun n => hx₁ (φ n)) l.1 ha₁
  let : NullSingletonClass (l.2.1:Measure Sphere) := normalized_empirical_nonatomic
    (fun n => u₂ (φ n)) (fun n => x₂ (φ n)) (fun n => hu₂ (φ n)) (fun n => hn (φ n))
    (hcard.comp hφ.tendsto_atTop) C hC (fun n => hlog₂ (φ n)) (fun n => hx₂ (φ n)) l.2.1 ha₂
  apply graph_limit_impossible (fun n => G (φ n)) (fun n => U₁ (φ n)) (fun n => U₂ (φ n))
    (fun n => hG (φ n)) (fun n => hB (φ n)) (fun n => hn (φ n))
    l.1 l.2.1 l.2.2.1 l.2.2.2 ha₁ ha₂ hq hr
    (fun f => (hd₁ f).comp hφ.tendsto_atTop) (fun f => (hd₂ f).comp hφ.tendsto_atTop)
    (T ∘ φ) (fun n => hT (φ n)) (fun f => (hdR f).comp hφ.tendsto_atTop)
    (ho.comp hφ.tendsto_atTop) M hM (fun n => hdom (φ n))
  intro n e y z hy hz
  simpa only [U₁,U₂,sub_sub_sub_cancel_right] using hrel (φ n) e y z hy hz

end WeakPinned.Bounded

end
end

end OAI
end

section
-- module Solutions.OAIQW_WeakPinned.BoundedRates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u1 u2 u3 u4

section
noncomputable section
open MeasureTheory Filter
open scoped Topology BigOperators
namespace WeakPinned.Bounded
open Hierarchy Global Variance NumberField

lemma bounded_denominator_rate (x w : ℕ → ℝ) (C : ℝ)
    (hx : ∀ n,0≤x n) (hw : ∀ n,0≤w n) (hC : ∀ n,w n≤C)
    (ht : Tendsto (fun n => x n/(w n+1)) atTop (𝓝 0)) :
    Tendsto x atTop (𝓝 0) := by
  apply squeeze_zero hx _ (by simpa only [mul_zero] using tendsto_const_nhds.mul ht (a:=C+1))
  intro n
  have hp : 0<w n+1 := by linarith [hw n]
  calc
    x n = (w n+1)*(x n/(w n+1)) := by field_simp
    _ ≤ (C+1)*(x n/(w n+1)) :=
      mul_le_mul_of_nonneg_right (by linarith [hC n]) (div_nonneg (hx n) hp.le)

variable {P : Type u1} [Fintype P] [DecidableEq P]
variable {K : Type u2} [Field K] [NumberField K]

lemma massEval_add (q r : Finset P → ℝ) (d d' : Depth P) :
    massEval (fun C => q C+r C) d d'=massEval q d d'+massEval r d d' := by
  simp only [massEval,weightedIntegral,mul_add,Finset.sum_add_distrib]
  ring

omit [NumberField K] in
lemma archMean_mass_add (Z₁ Z₂ : P → K) (h₁ : Function.Injective Z₁) (h₂ : Function.Injective Z₂)
    (hn : 2≤Fintype.card P) (q r : Finset P → ℝ) (v : InfinitePlace K) :
    archMean Z₁ Z₂ (massEval (fun C => q C+r C)) v=
      archMean Z₁ Z₂ (massEval q) v+archMean Z₁ Z₂ (massEval r) v := by
  unfold archMean
  simp only [massEval_add]
  exact integral_add (integrable_massEval Z₁ Z₂ h₁ h₂ hn q v)
    (integrable_massEval Z₁ Z₂ h₁ h₂ hn r v)

omit [NumberField K] in
lemma archMean_mass_swap (Z₁ Z₂ : P → K) (q : Finset P → ℝ) (v : InfinitePlace K) :
    archMean Z₂ Z₁ (massEval q) v=archMean Z₁ Z₂ (massEval q) v := by
  unfold archMean
  congr 1
  funext ω
  exact add_comm _ _

omit [NumberField K] in
lemma archMean_scale_swap (Z₁ Z₂ : P → K) (v : InfinitePlace K) :
    archMean Z₂ Z₁ scaleEval v=archMean Z₁ Z₂ scaleEval v := by
  unfold archMean
  congr 1
  funext ω
  simp only [scaleEval,massEval,potentialEval]
  congr 1
  · exact add_comm _ _
  · apply Finset.sum_congr rfl
    intro x _
    rw [add_comm ((arch Z₂ v ω).potential x)]

omit [DecidableEq P] in
lemma weightedIntegral_add (m q r : Finset P → ℝ) :
    weightedIntegral m (fun C => q C+r C)=weightedIntegral m q+weightedIntegral m r := by
  simp only [weightedIntegral,mul_add,Finset.sum_add_distrib]

variable {V : ℕ → Type u3} {L : ℕ → Type u4} [∀ n,Fintype (V n)] [∀ n,DecidableEq (V n)]
  [∀ n,Field (L n)] [∀ n,NumberField (L n)]

lemma bounded_place_selection (Z₁ Z₂ : ∀ n,V n → L n)
    (h₁ : ∀ n,Function.Injective (Z₁ n)) (h₂ : ∀ n,Function.Injective (Z₂ n))
    (hn : ∀ n,2≤Fintype.card (V n)) (q r : ∀ n,Finset (V n) → ℝ)
    (hq : ∀ n C,0≤q n C) (hr : ∀ n C,0≤r n C)
    (C : ℝ) (hC : 0≤C)
    (hscale : ∀ n,overlapScale (Z₁ n) (Z₂ n) (h₁ n) (h₂ n)+
      potentialScale (Z₁ n) (Z₂ n) (h₁ n) (h₂ n)≤C)
    (hqt : Tendsto (fun n => weightedIntegral (totalMass (Z₁ n) (Z₂ n) (h₁ n) (h₂ n)) (q n)) atTop (𝓝 0))
    (hrt : Tendsto (fun n => weightedIntegral (totalMass (Z₁ n) (Z₂ n) (h₁ n) (h₂ n)) (r n)) atTop (𝓝 0)) :
    ∃ v : ∀ n,InfinitePlace (L n),
      (∀ n,archMean (Z₁ n) (Z₂ n) scaleEval (v n)≤2*C+1) ∧
      Tendsto (fun n => archMean (Z₁ n) (Z₂ n) (massEval (q n)) (v n)) atTop (𝓝 0) ∧
      Tendsto (fun n => archMean (Z₁ n) (Z₂ n) (massEval (r n)) (v n)) atTop (𝓝 0) := by
  let m := fun n => totalMass (Z₁ n) (Z₂ n) (h₁ n) (h₂ n)
  let ε := fun n => weightedIntegral (m n) (q n)+weightedIntegral (m n) (r n)+1/((n:ℝ)+1)
  have hq0 (n) : 0≤weightedIntegral (m n) (q n) :=
    Finset.sum_nonneg (fun D _ => mul_nonneg (totalMass_nonneg _ _ _ _ _) (hq n D))
  have hr0 (n) : 0≤weightedIntegral (m n) (r n) :=
    Finset.sum_nonneg (fun D _ => mul_nonneg (totalMass_nonneg _ _ _ _ _) (hr n D))
  have he (n) : 0<ε n := by
    have hh : 0<1/((n:ℝ)+1) := by positivity
    dsimp only [ε]
    linarith [hq0 n,hr0 n]
  have het : Tendsto ε atTop (𝓝 0) := by
    have hi : Tendsto (fun n : ℕ => 1/((n:ℝ)+1)) atTop (𝓝 0) := by
      simpa only [one_div,Function.comp_def] using tendsto_inv_atTop_zero.comp (tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop)
    simpa only [add_zero] using (hqt.add hrt).add hi
  have hs (n) := select_arch (Z₁ n) (Z₂ n) (h₁ n) (h₂ n) (hn n)
    (fun D => q n D+r n D) (fun D => add_nonneg (hq n D) (hr n D)) C (ε n) hC (he n) (hscale n)
    (by rw [weightedIntegral_add]; dsimp [ε,m]; linarith [show 0≤1/((n:ℝ)+1) by positivity])
  choose v hvscale hv using hs
  have hvq (n) : 0≤archMean (Z₁ n) (Z₂ n) (massEval (q n)) (v n) :=
    archMean_nonneg _ _ _ (massEval_nonneg _ (hq n)) _
  have hvr (n) : 0≤archMean (Z₁ n) (Z₂ n) (massEval (r n)) (v n) :=
    archMean_nonneg _ _ _ (massEval_nonneg _ (hr n)) _
  have hsum (n) := hv n
  simp only [archMean_mass_add _ _ (h₁ _) (h₂ _) (hn _)] at hsum
  refine ⟨v,hvscale,?_,?_⟩
  · apply squeeze_zero hvq _ (by simpa only [mul_zero] using het.const_mul 2)
    intro n
    linarith [hsum n,hvr n]
  · apply squeeze_zero hvr _ (by simpa only [mul_zero] using het.const_mul 2)
    intro n
    linarith [hsum n,hvq n]

lemma power_fraction_rate (n : ℕ → ℝ) (hn : ∀ j,0<n j)
    (ht : Tendsto n atTop atTop) (c : ℝ) (hc : 0<c) :
    Tendsto (fun j => (n j)^(1-c)/n j) atTop (𝓝 0) := by
  have hh := (tendsto_rpow_neg_atTop hc).comp ht
  convert hh using 1
  funext j
  rw [show 1-c=1+(-c) by ring,Real.rpow_add (hn j),Real.rpow_one]
  simp only [Function.comp_apply]
  exact mul_div_cancel_left₀ _ (hn j).ne'

end WeakPinned.Bounded

end
end

end OAI
end

section
-- module Solutions.OAIQW_WeakPinned.BoundedContradiction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u1 u2 u3

section
noncomputable section
open Filter MeasureTheory
open scoped Topology BigOperators
namespace WeakPinned
open Bounded Global Variance Hierarchy NumberField

variable {V : ℕ → Type u1} {I : ℕ → Type u2} {K : ℕ → Type u3} [∀ j,Fintype (V j)] [∀ j,Fintype (I j)] [∀ j,DecidableEq (V j)]
  [∀ j,Field (K j)] [∀ j,NumberField (K j)]
variable (G : ∀ j,Core.Fibers (V j) (I j)) (θ γ c : ℝ) (η : ℕ → ℝ)
  (Z₁ Z₂ : ∀ j,V j → K j) (h₁ : ∀ j,Function.Injective (Z₁ j)) (h₂ : ∀ j,Function.Injective (Z₂ j))

/-- The bounded arithmetic regime is impossible as well. The embedding and
normalization are chosen from the actual global mass and finite graph laws. -/
theorem arithmetic_no_bounded (hθ : 0<θ) (hγ : 0<γ) (hγ1 : γ<1) (hc : 0<c) (hcγ : c<γ)
    (hn : Tendsto (fun j => (Fintype.card (V j):ℝ)) atTop atTop)
    (hη : Tendsto η atTop (𝓝 0)) (hη0 : ∀ j,0≤η j) (hηb : ∀ j,η j≤θ/2)
    (hG : ∀ j,PreparedGraph (V j) (I j) (G j) θ γ c (η j))
    (t : ∀ j,I j → K j) (ht : ∀ j e y,y∈(G j).targets e →
      (Z₁ j ((G j).source e)-Z₁ j y)*(Z₂ j ((G j).source e)-Z₂ j y)=t j e)
    (C : ℝ) (hC : 0≤C) (hscale : ∀ j,overlapScale (Z₁ j) (Z₂ j) (h₁ j) (h₂ j)+
      potentialScale (Z₁ j) (Z₂ j) (h₁ j) (h₂ j)≤C) : False := by
  let n := fun j => (Fintype.card (V j):ℝ)
  let T := fun j => n j^(1-c)
  let S := fun j => n j^γ
  let q := fun j => varianceCell (G j).fiberWeight (G j).targets (T j)
  let r := fun j => varianceCell ((G j).retainedWeight (S j)) ((G j).retainedSet (S j)) (T j)
  have hq (j D) : 0≤q j D := varianceCell_nonneg _ _ _ (G j).fiberWeight_nonneg D
  have hr (j D) : 0≤r j D := varianceCell_nonneg _ _ _ ((G j).retainedWeight_nonneg _) D
  have h2 (j) : 2≤Fintype.card (V j) := (hG j).card_ge
  have hn2 (j) : (2:ℝ)≤n j := by dsimp only [n]; exact_mod_cast h2 j
  have hn0 (j) : 0<n j := by linarith [hn2 j]
  have hpos (j) : 0<(G j).edgeCount := (hG j).edgeCount_pos (by linarith [hηb j])
  have hdom (j x y) := (hG j).uniform_domination hθ (hηb j) x y
  have hT (j) : 1≤T j := Real.one_le_rpow (by linarith [hn2 j]) (by linarith)
  have hS (j) : 1<S j := Real.one_lt_rpow (by linarith [hn2 j]) hγ
  have hSn (j) : S j≤n j := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le (show 1≤n j by linarith [hn2 j]) hγ1.le
  have hB (j e) : 2≤((G j).targets e).card := by
    have hh := (hS j).trans ((hG j).fiber e)
    exact_mod_cast hh
  have hR (j y) : 2≤((G j).retainedSet (S j) y).card := by
    have hh := (hS j).trans_le ((G j).retainedSet_size (S j) (hSn j) y)
    exact_mod_cast hh
  have hvar := sampling_variance_rates G θ γ c η Z₁ Z₂ h₁ h₂ hθ hγ hγ1 hcγ hn hη hη0 hηb hG t ht
  let W := fun j => overlapScale (Z₁ j) (Z₂ j) (h₁ j) (h₂ j)+potentialScale (Z₁ j) (Z₂ j) (h₁ j) (h₂ j)
  have hW (j) : 0≤W j := add_nonneg (overlapScale_nonneg _ _ _ _) (potentialScale_nonneg _ _ _ _)
  have hf0 (j) : 0≤fiberVariance G c Z₁ Z₂ h₁ h₂ j :=
    Finset.sum_nonneg (fun D _ => mul_nonneg (totalMass_nonneg _ _ _ _ D) (hq j D))
  have hr0 (j) : 0≤ incomingVariance G γ c Z₁ Z₂ h₁ h₂ j :=
    Finset.sum_nonneg (fun D _ => mul_nonneg (totalMass_nonneg _ _ _ _ D) (hr j D))
  have hft := bounded_denominator_rate _ W C hf0 hW hscale hvar.1
  have hrt := bounded_denominator_rate _ W C hr0 hW hscale hvar.2
  obtain ⟨v,hv,hvf,hvr⟩ := bounded_place_selection Z₁ Z₂ h₁ h₂ h2 q r hq hr C hC hscale hft hrt
  let z₁ := fun j x => (v j).embedding (Z₁ j x)
  let z₂ := fun j x => (v j).embedding (Z₂ j x)
  have hz₁ (j) : Function.Injective (z₁ j) := (v j).embedding.injective.comp (h₁ j)
  have hz₂ (j) : Function.Injective (z₂ j) := (v j).embedding.injective.comp (h₂ j)
  let u₁ := fun j => logNormalize (z₁ j)
  let u₂ := fun j => logNormalize (z₂ j)
  let D : ℝ := 4*(2*C+1)+8
  have hD : 0≤D := by dsimp [D]; positivity
  have hlog₁ (j) : logAverage (u₁ j)≤D := by
    rw [logNormalize_bound _ (hz₁ j) (h2 j)]
    exact (arch_log_center_bound (Z₁ j) (Z₂ j) (h₁ j) (h₂ j) (h2 j) (v j)).trans (by dsimp [D]; linarith [hv j])
  have hlog₂ (j) : logAverage (u₂ j)≤D := by
    rw [logNormalize_bound _ (hz₂ j) (h2 j)]
    have hh := arch_log_center_bound (Z₂ j) (Z₁ j) (h₂ j) (h₁ j) (h2 j) (v j)
    rw [archMean_scale_swap] at hh
    exact hh.trans (by dsimp [D]; linarith [hv j])
  choose x₁ hx₁ using (fun j => log_center (u₁ j) D (h2 j) (hlog₁ j))
  choose x₂ hx₂ using (fun j => log_center (u₂ j) D (h2 j) (hlog₂ j))
  have hsmall := power_fraction_rate n hn0 hn c hc
  let m₁ := fun j => pairMean (rawDepth (z₁ j))
  let m₂ := fun j => pairMean (rawDepth (z₂ j))
  have hd₁ := sphere_arch_test_rate Z₁ Z₂ h₁ h₂ v m₁ (fun j => -u₁ j (x₁ j))
    (fun j => (G j).fiberWeight) (fun j => (G j).targets) T (2/θ) h2 hT (by positivity)
    (fun j => (G j).fiberWeight_nonneg) (fun j => (G j).sum_fiberWeight (hpos j) |>.le) hB
    (fun j => (G j).fiber_domination _ (hdom j) (h2 j)) hvf hsmall
  have hvf₂ : Tendsto (fun j => archMean (Z₂ j) (Z₁ j) (massEval (q j)) (v j)) atTop (𝓝 0) := by
    simpa only [archMean_mass_swap] using hvf
  have hd₂ := sphere_arch_test_rate Z₂ Z₁ h₂ h₁ v m₂ (fun j => -u₂ j (x₂ j))
    (fun j => (G j).fiberWeight) (fun j => (G j).targets) T (2/θ) h2 hT (by positivity)
    (fun j => (G j).fiberWeight_nonneg) (fun j => (G j).sum_fiberWeight (hpos j) |>.le) hB
    (fun j => (G j).fiber_domination _ (hdom j) (h2 j)) hvf₂ hsmall
  have hdR := sphere_arch_test_rate Z₁ Z₂ h₁ h₂ v m₁ (fun j => -u₁ j (x₁ j))
    (fun j => (G j).retainedWeight (S j)) (fun j => (G j).retainedSet (S j)) T (2/θ) h2 hT (by positivity)
    (fun j => (G j).retainedWeight_nonneg _) (fun j => (G j).sum_retainedWeight _ (hpos j)) hR
    (fun j => (G j).retained_domination _ _ (hdom j) (h2 j)) hvr hsmall
  apply normalized_graph_impossible G u₁ u₂ x₁ x₂
    (fun j => logNormalize_injective _ (hz₁ j)) (fun j => logNormalize_injective _ (hz₂ j))
    hpos (fun j e => Finset.card_pos.mp (by have := hB j e; omega)) h2 hn D hD hlog₁ hlog₂ hx₁ hx₂
    (by simpa only [sub_eq_add_neg,u₁,logNormalize,z₁,m₁] using hd₁)
    (by simpa only [sub_eq_add_neg,u₂,logNormalize,z₂,m₂] using hd₂)
    S (fun j => Real.rpow_pos_of_pos (hn0 j) γ)
    (by simpa only [sub_eq_add_neg,u₁,logNormalize,z₁,m₁] using hdR)
    (omitted_rate G θ γ c η hθ hγ1 hηb hn hG) (2/θ) (by positivity) hdom
  intro j e y z hy hz
  have he := (ht j e y hy).trans (ht j e z hz).symm
  have hem := congrArg (v j).embedding he
  simp only [map_mul,map_sub] at hem
  dsimp only [u₁,u₂,logNormalize,z₁,z₂]
  linear_combination (Real.exp (pairMean (rawDepth (z₁ j))):ℂ)*
    (Real.exp (pairMean (rawDepth (z₂ j))):ℂ)*hem

end WeakPinned

end
end

end OAI
end

section
-- module Solutions.OAIQW_WeakPinned.ArithmeticContradiction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u1 u2 u3

section
noncomputable section
open Filter
open scoped Topology
namespace WeakPinned

lemma sequence_bounded_subsequence (W : ℕ → ℝ) (hW : ¬Tendsto W atTop atTop)
    (p : ℕ → Prop) (hp : ∀ᶠ n in atTop,p n) :
    ∃ (φ : ℕ → ℕ) (C : ℝ),Tendsto φ atTop atTop ∧ 0≤C ∧ ∀ n,W (φ n)≤C ∧ p (φ n) := by
  rw [tendsto_atTop] at hW
  push Not at hW
  obtain ⟨C,hC⟩ := hW
  obtain ⟨φ,hφ,hφC⟩ := exists_seq_forall_of_frequently (hC.and_eventually hp)
  exact ⟨φ,max C 0,hφ,le_max_right _ _,fun n => ⟨(hφC n).1.le.trans (le_max_left _ _),(hφC n).2⟩⟩

end WeakPinned

end
end
section
noncomputable section
open Filter
open scoped Topology
namespace WeakPinned
open Global

variable {V : ℕ → Type u1} {I : ℕ → Type u2} {K : ℕ → Type u3} [∀ j,Fintype (V j)] [∀ j,Fintype (I j)] [∀ j,DecidableEq (V j)]
  [∀ j,Field (K j)] [∀ j,NumberField (K j)]

/-- Both alternatives of the genuine arithmetic sequence have been eliminated. -/
theorem arithmetic_sequence_impossible_oai
    (G : ∀ j,Core.Fibers (V j) (I j)) (θ γ c : ℝ) (η : ℕ → ℝ)
    (Z₁ Z₂ : ∀ j,V j → K j) (h₁ : ∀ j,Function.Injective (Z₁ j)) (h₂ : ∀ j,Function.Injective (Z₂ j))
    (hθ : 0<θ) (hγ : 0<γ) (hγ1 : γ<1) (hc : 0<c) (hcγ : c<γ)
    (hn : Tendsto (fun j => (Fintype.card (V j):ℝ)) atTop atTop)
    (hη : Tendsto η atTop (𝓝 0)) (hη0 : ∀ j,0≤η j) (hηb : ∀ j,η j≤θ/2)
    (hG : ∀ j,PreparedGraph (V j) (I j) (G j) θ γ c (η j))
    (t : ∀ j,I j → K j) (ht : ∀ j e y,y∈(G j).targets e →
      (Z₁ j ((G j).source e)-Z₁ j y)*(Z₂ j ((G j).source e)-Z₂ j y)=t j e) : False := by
  let W := fun j => overlapScale (Z₁ j) (Z₂ j) (h₁ j) (h₂ j)
  let A := fun j => potentialScale (Z₁ j) (Z₂ j) (h₁ j) (h₂ j)
  by_cases htop : Tendsto W atTop atTop
  · exact arithmetic_no_unbounded G θ γ c η Z₁ Z₂ h₁ h₂ hθ hγ hγ1 hc hcγ hn hη hη0 hηb hG t ht htop
  have hcomp := arithmetic_scale_comparison G θ γ c η Z₁ Z₂ h₁ h₂ hθ hγ hγ1 hcγ hn hη hη0 hηb hG t ht
  obtain ⟨φ,C,hφ,hC,hbound⟩ := sequence_bounded_subsequence W htop
    (fun j => A j≤(64+8/θ)*(W j+1)) hcomp
  apply arithmetic_no_bounded (fun j => G (φ j)) θ γ c (η ∘ φ)
    (fun j => Z₁ (φ j)) (fun j => Z₂ (φ j)) (fun j => h₁ (φ j)) (fun j => h₂ (φ j))
    hθ hγ hγ1 hc hcγ (hn.comp hφ) (hη.comp hφ) (fun j => hη0 (φ j)) (fun j => hηb (φ j))
    (fun j => hG (φ j)) (fun j => t (φ j)) (fun j => ht (φ j))
    (C+(64+8/θ)*(C+1)) (by positivity)
  intro j
  change W (φ j)+A (φ j)≤_
  have hA := (hbound j).2.trans (mul_le_mul_of_nonneg_left
    (show W (φ j)+1≤C+1 by linarith [(hbound j).1]) (by positivity : 0≤64+8/θ))
  linarith [(hbound j).1]

end WeakPinned

end
end

end OAI
end

theorem solution.{u1, u2, u3} : type_of% @OAI.WeakPinned.arithmetic_sequence_impossible_oai.{u1, u2, u3} := @OAI.WeakPinned.arithmetic_sequence_impossible_oai.{u1, u2, u3}
