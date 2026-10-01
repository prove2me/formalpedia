-- Prove2me | solution 1 for TierneyMH.Mixture.proposition5_mixture
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T12:26:35.894891+00:00
-- url     : https://prove2.me/submissions/47114feb-60fa-410c-aa42-91fefd9500d4

import Definitions.Def_TierneyMH_Mixture_maxMHKernel
import Definitions.Def_TierneyMH_Shared_OffDiagDominates
import Definitions.Def_TierneyMH_Mixture_mixKernel
import Mathlib.Probability.Kernel.CompProdEqIff
import Definitions.Def_TierneyMH_Shared_IsSymmetricSplit
import Definitions.Def_TierneyMH_Shared_IsRatioVersion
import Definitions.Def_TierneyMH_Mixture_alphaMH
import Mathlib.Tactic

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal
open TierneyMH.Mixture

namespace TierneyProof
variable {E : Type*} [MeasurableSpace E] (π : Measure E) (Q : Kernel E E)

theorem density_measurable : Measurable (canonDensity π Q) :=
  Measure.measurable_rnDeriv _ _

theorem R_measurable : MeasurableSet (canonR π Q) :=
  (measurableSet_lt measurable_const (density_measurable π Q)).inter
    (measurableSet_lt measurable_const ((density_measurable π Q).comp measurable_swap))

theorem R_swap (p : E × E) : p.swap ∈ canonR π Q ↔ p ∈ canonR π Q := by
  simp [canonR,and_comm]

theorem ratio_pos (p : E × E) : 0 < canonRatio π Q p ∧ canonRatio π Q p ≠ ⊤ := by
  unfold canonRatio
  split_ifs with h
  · exact ⟨ENNReal.div_pos_iff.mpr ⟨ne_of_gt h.1.1,h.2.2⟩,
      ENNReal.div_ne_top h.2.1 (ne_of_gt h.1.2)⟩
  · simp

theorem ratio_inv (p : E × E) : canonRatio π Q p.swap = (canonRatio π Q p)⁻¹ := by
  classical
  have hs : (p.swap ∈ canonR π Q ∧ canonDensity π Q p.swap ≠ ⊤ ∧ canonDensity π Q p.swap.swap ≠ ⊤) ↔
      (p ∈ canonR π Q ∧ canonDensity π Q p ≠ ⊤ ∧ canonDensity π Q p.swap ≠ ⊤) := by
    simp [R_swap π Q,and_left_comm,and_comm,and_assoc]
  unfold canonRatio
  rw [if_congr hs rfl rfl]
  split_ifs with h
  · simpa using (ENNReal.inv_div (Or.inl h.2.2) (Or.inr (ne_of_gt h.1.1))).symm
  · simp

theorem alpha_identity (p : E × E) :
    alphaMH π Q p * canonRatio π Q p = alphaMH π Q p.swap := by
  by_cases hp : p ∈ canonR π Q
  · have hs := (R_swap π Q p).mpr hp
    simp only [alphaMH,Set.indicator_of_mem hp,Set.indicator_of_mem hs,Prod.swap_swap]
    rw [ratio_inv π Q p,min_mul,one_mul,
      ENNReal.inv_mul_cancel (ne_of_gt (ratio_pos π Q p).1) (ratio_pos π Q p).2,min_comm]
  · have hs : p.swap ∉ canonR π Q := fun h => hp ((R_swap π Q p).mp h)
    simp [alphaMH,hp,hs]
end TierneyProof


namespace TierneyMeasure
open MeasureTheory.Measure
variable {E : Type*} [MeasurableSpace E]

theorem sum_swap_symmetric (μ : Measure (E × E)) :
    (μ + μ.map Prod.swap).map Prod.swap = μ + μ.map Prod.swap := by
  rw [Measure.map_add _ _ measurable_swap,Measure.map_map measurable_swap measurable_swap]
  simp [Function.comp_def,add_comm]

theorem swap_density (μ ν : Measure (E × E)) [SigmaFinite μ] [SigmaFinite ν]
    (hν : ν.map Prod.swap = ν) (hμν : μ ≪ ν) :
    ν.withDensity (fun p => μ.rnDeriv ν p.swap) = μ.map Prod.swap := by
  have hswap : MeasurableEmbedding (Prod.swap : E × E → E × E) := MeasurableEquiv.prodComm.measurableEmbedding
  have h := hswap.rnDeriv_map μ ν
  change (fun p => (μ.map Prod.swap).rnDeriv (ν.map Prod.swap) p.swap) =ᵐ[ν] μ.rnDeriv ν at h
  rw [hν] at h
  have hm : ∀ᵐ p ∂ν.map Prod.swap,
      (μ.map Prod.swap).rnDeriv ν p.swap = μ.rnDeriv ν p := by rw [hν]; exact h
  rw [hswap.ae_map_iff] at hm
  have he : (μ.map Prod.swap).rnDeriv ν =ᵐ[ν] fun p => μ.rnDeriv ν p.swap := by
    filter_upwards [hm] with p hp
    exact hp
  rw [← withDensity_congr_ae he]
  apply withDensity_rnDeriv_eq
  simpa only [hν] using hswap.absolutelyContinuous_map hμν

theorem density_ac_on_positive {α : Type*} [MeasurableSpace α] (ν : Measure α)
    (f g : α → ℝ≥0∞) (hf : Measurable f) (hg : Measurable g)
    (R : Set α) (hR : MeasurableSet R) (hgR : ∀ x ∈ R, 0 < g x) :
    (ν.withDensity f).restrict R ≪ (ν.withDensity g).restrict R := by
  rw [restrict_withDensity hR,restrict_withDensity hR]
  apply (withDensity_absolutelyContinuous _ _).trans
  apply withDensity_absolutelyContinuous' hg.aemeasurable.restrict
  filter_upwards [self_mem_ae_restrict hR] with x hx
  exact ne_of_gt (hgR x hx)

theorem density_singular_off_overlap {α : Type*} [MeasurableSpace α] (ν : Measure α)
    (f g : α → ℝ≥0∞) (hf : Measurable f) (hg : Measurable g) :
    (ν.withDensity f).restrict {x | ¬ (0 < f x ∧ 0 < g x)} ⟂ₘ
      (ν.withDensity g).restrict {x | ¬ (0 < f x ∧ 0 < g x)} := by
  let R : Set α := {x | ¬ (0 < f x ∧ 0 < g x)}
  let Z : Set α := {x | f x = 0}
  have hR : MeasurableSet R := ((measurableSet_lt measurable_const hf).inter
    (measurableSet_lt measurable_const hg)).compl
  have hZ : MeasurableSet Z := measurableSet_eq_fun hf measurable_const
  refine ⟨Z,hZ,?_,?_⟩
  · rw [Measure.restrict_apply hZ,withDensity_apply _ (hZ.inter hR)]
    apply (lintegral_eq_zero_iff' hf.aemeasurable.restrict).mpr
    filter_upwards [self_mem_ae_restrict (hZ.inter hR)] with x hx
    exact hx.1
  · rw [Measure.restrict_apply hZ.compl,withDensity_apply _ (hZ.compl.inter hR)]
    apply (lintegral_eq_zero_iff' hg.aemeasurable.restrict).mpr
    filter_upwards [self_mem_ae_restrict (hZ.compl.inter hR)] with x hx
    have hfpos : 0 < f x := pos_iff_ne_zero.mpr hx.1
    exact nonpos_iff_eq_zero.mp (le_of_not_gt (fun hgpos => hx.2 ⟨hfpos,hgpos⟩))
end TierneyMeasure

namespace TierneyProof
open TierneyMH.Shared
open MeasureTheory.Measure
variable {E : Type*} [MeasurableSpace E] (π : Measure E) (Q : Kernel E E)

theorem ratio_measurable : Measurable (canonRatio π Q) := by
  classical
  have hf := density_measurable π Q
  have hg := hf.comp measurable_swap
  have hR := R_measurable π Q
  unfold canonRatio
  apply Measurable.ite
    (hR.inter ((measurableSet_eq_fun hf measurable_const).compl.inter
      (measurableSet_eq_fun hg measurable_const).compl))
  · exact hf.div hg
  · exact measurable_const

variable [IsProbabilityMeasure π] [IsMarkovKernel Q]

theorem canonical_split :
    IsSymmetricSplit (π ⊗ₘ Q) (canonR π Q) ∧
      IsRatioVersion (π ⊗ₘ Q) (canonR π Q) (canonRatio π Q) := by
  let μ := π ⊗ₘ Q
  let ν := μ + μ.map Prod.swap
  let f := canonDensity π Q
  let g := fun p : E × E => f p.swap
  have hν : ν.map Prod.swap = ν := TierneyMeasure.sum_swap_symmetric μ
  have hμν : μ ≪ ν := Measure.AbsolutelyContinuous.rfl.add_right _
  have hf : Measurable f := density_measurable π Q
  have hg : Measurable g := hf.comp measurable_swap
  have he1 : ν.withDensity f = μ := Measure.withDensity_rnDeriv_eq μ ν hμν
  have he2 : ν.withDensity g = μ.map Prod.swap := TierneyMeasure.swap_density μ ν hν hμν
  have hR := R_measurable π Q
  have hfR : ∀ p ∈ canonR π Q, 0 < f p := fun p hp => hp.1
  have hgR : ∀ p ∈ canonR π Q, 0 < g p := fun p hp => hp.2
  constructor
  · refine ⟨hR,?_,?_,?_,?_⟩
    · ext p
      exact R_swap π Q p
    · change μ.restrict (canonR π Q) ≪ (μ.map Prod.swap).restrict (canonR π Q)
      rw [← he2,← he1]
      exact TierneyMeasure.density_ac_on_positive ν f g hf hg _ hR hgR
    · change (μ.map Prod.swap).restrict (canonR π Q) ≪ μ.restrict (canonR π Q)
      rw [← he2,← he1]
      exact TierneyMeasure.density_ac_on_positive ν g f hg hf _ hR hfR
    · change μ.restrict (canonR π Q)ᶜ ⟂ₘ (μ.map Prod.swap).restrict (canonR π Q)ᶜ
      rw [← he2,← he1]
      exact TierneyMeasure.density_singular_off_overlap ν f g hf hg
  · refine ⟨ratio_measurable π Q,fun p => ⟨(ratio_pos π Q p).1,lt_top_iff_ne_top.mpr (ratio_pos π Q p).2⟩,
      ratio_inv π Q,?_⟩
    have hfin : ∀ᵐ p ∂ν, f p ≠ ⊤ := (Measure.rnDeriv_lt_top μ ν).mono (fun _ h => h.ne)
    have hfin' : ∀ᵐ p ∂ν, g p ≠ ⊤ := by
      have hm : ∀ᵐ p ∂ν.map Prod.swap, f p ≠ ⊤ := by simpa only [hν] using hfin
      exact (MeasurableEquiv.prodComm : E × E ≃ᵐ E × E).measurableEmbedding.ae_map_iff.mp hm
    change μ.restrict (canonR π Q) = ((μ.map Prod.swap).restrict (canonR π Q)).withDensity (canonRatio π Q)
    rw [← he2,← he1,restrict_withDensity hR,restrict_withDensity hR,
      ← withDensity_mul _ hg (ratio_measurable π Q)]
    apply withDensity_congr_ae
    filter_upwards [self_mem_ae_restrict hR,ae_restrict_of_ae hfin,ae_restrict_of_ae hfin'] with p hp hfp hgp
    have he : p ∈ canonR π Q ∧ canonDensity π Q p ≠ ⊤ ∧ canonDensity π Q p.swap ≠ ⊤ := ⟨hp,hfp,hgp⟩
    change f p = g p * canonRatio π Q p
    rw [canonRatio,if_pos he]
    exact (ENNReal.mul_div_cancel (ne_of_gt hp.2) hgp).symm
end TierneyProof

set_option maxHeartbeats 800000

namespace TierneyMeasure
open MeasureTheory.Measure
variable {α : Type*} [MeasurableSpace α]

theorem greatest_density_lower_bound (ν σ : Measure α) [SigmaFinite ν] [SigmaFinite σ]
    (f g : α → ℝ≥0∞) (hf : Measurable f) (hg : Measurable g)
    (hσf : σ ≤ ν.withDensity f) (hσg : σ ≤ ν.withDensity g) :
    σ ≤ ν.withDensity (fun x => min (f x) (g x)) := by
  have hσν : σ ≪ ν := hσf.absolutelyContinuous.trans (withDensity_absolutelyContinuous _ _)
  have hr (k : α → ℝ≥0∞) (hk : Measurable k) (hσk : σ ≤ ν.withDensity k) :
      σ.rnDeriv ν ≤ᵐ[ν] k := by
    apply ae_le_of_forall_setLIntegral_le_of_sigmaFinite (σ.measurable_rnDeriv ν)
    intro s hs hsfin
    rw [Measure.setLIntegral_rnDeriv hσν s,← withDensity_apply _ hs]
    exact hσk s
  rw [← Measure.withDensity_rnDeriv_eq σ ν hσν]
  apply withDensity_mono
  filter_upwards [hr f hf hσf,hr g hg hσg] with x h1 h2
  exact le_min h1 h2
end TierneyMeasure

namespace TierneyProof
open MeasureTheory.Measure
variable {E : Type*} [MeasurableSpace E] (π : Measure E) [IsProbabilityMeasure π]
    (Q : Kernel E E) [IsMarkovKernel Q]

theorem flow_canonical :
    (π ⊗ₘ Q).withDensity (alphaMH π Q) =
      ((π ⊗ₘ Q)+(π ⊗ₘ Q).map Prod.swap).withDensity
        (fun p => min (canonDensity π Q p) (canonDensity π Q p.swap)) := by
  let μ := π ⊗ₘ Q
  let ν := μ+μ.map Prod.swap
  let f := canonDensity π Q
  have hν : ν.map Prod.swap = ν := TierneyMeasure.sum_swap_symmetric μ
  have hμν : μ ≪ ν := Measure.AbsolutelyContinuous.rfl.add_right _
  have he : ν.withDensity f = μ := Measure.withDensity_rnDeriv_eq μ ν hμν
  have hf := density_measurable π Q
  have hα : Measurable (alphaMH π Q) :=
    ((measurable_const.min ((ratio_measurable π Q).comp measurable_swap)).indicator (R_measurable π Q))
  have hfin : ∀ᵐ p ∂ν, f p ≠ ⊤ := (Measure.rnDeriv_lt_top μ ν).mono (fun _ h => h.ne)
  have hfin' : ∀ᵐ p ∂ν, f p.swap ≠ ⊤ := by
    have hm : ∀ᵐ p ∂ν.map Prod.swap, f p ≠ ⊤ := by rw [hν]; exact hfin
    have hs : MeasurableEmbedding (Prod.swap : E × E → E × E) := MeasurableEquiv.prodComm.measurableEmbedding
    exact hs.ae_map_iff.mp hm
  change μ.withDensity (alphaMH π Q) = ν.withDensity (fun p => min (f p) (f p.swap))
  rw [← he,← withDensity_mul _ hf hα]
  apply withDensity_congr_ae
  filter_upwards [hfin,hfin'] with p hfp hgp
  change f p*alphaMH π Q p = min (f p) (f p.swap)
  by_cases hp : p ∈ canonR π Q
  · have hs := (R_swap π Q p).mpr hp
    have hc : p.swap ∈ canonR π Q ∧ canonDensity π Q p.swap ≠ ⊤ ∧ canonDensity π Q p.swap.swap ≠ ⊤ :=
      ⟨hs,hgp,hfp⟩
    rw [alphaMH,Set.indicator_of_mem hp,canonRatio,if_pos hc]
    change f p*min 1 (f p.swap/f p) = min (f p) (f p.swap)
    rw [mul_min,mul_one,ENNReal.mul_div_cancel (ne_of_gt hp.1) hfp]
  · rw [alphaMH,Set.indicator_of_notMem hp,mul_zero]
    by_cases hf0 : f p = 0
    · simp [hf0]
    · have hg0 : f p.swap = 0 := not_lt.mp (fun h => hp ⟨pos_iff_ne_zero.mpr hf0,h⟩) |>.antisymm bot_le
      simp [hg0]

theorem flow_le : (π ⊗ₘ Q).withDensity (alphaMH π Q) ≤ (π ⊗ₘ Q) ∧
    (π ⊗ₘ Q).withDensity (alphaMH π Q) ≤ (π ⊗ₘ Q).map Prod.swap := by
  let μ := π ⊗ₘ Q
  let ν := μ+μ.map Prod.swap
  have hμν : μ ≪ ν := Measure.AbsolutelyContinuous.rfl.add_right _
  have h1 : ν.withDensity (canonDensity π Q) = μ := Measure.withDensity_rnDeriv_eq μ ν hμν
  have h2 : ν.withDensity (fun p => canonDensity π Q p.swap) = μ.map Prod.swap :=
    TierneyMeasure.swap_density μ ν (TierneyMeasure.sum_swap_symmetric μ) hμν
  rw [flow_canonical]
  change ν.withDensity (fun p => min (canonDensity π Q p) (canonDensity π Q p.swap)) ≤ μ ∧
    ν.withDensity (fun p => min (canonDensity π Q p) (canonDensity π Q p.swap)) ≤ μ.map Prod.swap
  constructor
  · apply le_trans _ h1.le
    exact withDensity_mono (Eventually.of_forall fun _ => min_le_left _ _)
  · apply le_trans _ h2.le
    exact withDensity_mono (Eventually.of_forall fun _ => min_le_right _ _)

theorem le_flow (σ : Measure (E × E)) [SigmaFinite σ]
    (h1 : σ ≤ π ⊗ₘ Q) (h2 : σ ≤ (π ⊗ₘ Q).map Prod.swap) :
    σ ≤ (π ⊗ₘ Q).withDensity (alphaMH π Q) := by
  let μ := π ⊗ₘ Q
  let ν := μ+μ.map Prod.swap
  have hμν : μ ≪ ν := Measure.AbsolutelyContinuous.rfl.add_right _
  have he1 : ν.withDensity (canonDensity π Q) = μ := Measure.withDensity_rnDeriv_eq μ ν hμν
  have he2 : ν.withDensity (fun p => canonDensity π Q p.swap) = μ.map Prod.swap :=
    TierneyMeasure.swap_density μ ν (TierneyMeasure.sum_swap_symmetric μ) hμν
  rw [flow_canonical]
  change σ ≤ ν.withDensity (fun p => min (canonDensity π Q p) (canonDensity π Q p.swap))
  apply TierneyMeasure.greatest_density_lower_bound ν σ (canonDensity π Q)
    (fun p => canonDensity π Q p.swap) (density_measurable π Q)
    ((density_measurable π Q).comp measurable_swap)
  · rwa [he1]
  · rwa [he2]

theorem density_form (ν : Measure (E × E)) [SigmaFinite ν] (hν : ν.map Prod.swap = ν)
    (hμν : π ⊗ₘ Q ≪ ν) :
    (π ⊗ₘ Q).withDensity (alphaMH π Q) =
      ν.withDensity (fun p => min ((π ⊗ₘ Q).rnDeriv ν p.swap) ((π ⊗ₘ Q).rnDeriv ν p)) := by
  let μ := π ⊗ₘ Q
  have hf : Measurable (μ.rnDeriv ν) := Measure.measurable_rnDeriv _ _
  have hg := hf.comp measurable_swap
  have he1 : ν.withDensity (μ.rnDeriv ν) = μ := Measure.withDensity_rnDeriv_eq μ ν hμν
  have he2 : ν.withDensity (fun p => μ.rnDeriv ν p.swap) = μ.map Prod.swap :=
    TierneyMeasure.swap_density μ ν hν hμν
  have hleft : ν.withDensity (fun p => min (μ.rnDeriv ν p.swap) (μ.rnDeriv ν p)) ≤ μ := by
    apply le_trans _ he1.le
    exact withDensity_mono (Eventually.of_forall fun _ => min_le_right _ _)
  have hright : ν.withDensity (fun p => min (μ.rnDeriv ν p.swap) (μ.rnDeriv ν p)) ≤ μ.map Prod.swap := by
    apply le_trans _ he2.le
    exact withDensity_mono (Eventually.of_forall fun _ => min_le_left _ _)
  apply le_antisymm
  · haveI : IsFiniteMeasure ((π ⊗ₘ Q).withDensity (alphaMH π Q)) := isFiniteMeasure_of_le (π ⊗ₘ Q) (flow_le π Q).1
    apply TierneyMeasure.greatest_density_lower_bound ν _
      (fun p => μ.rnDeriv ν p.swap) (μ.rnDeriv ν) hg hf
    · rw [he2]
      exact (flow_le π Q).2
    · rw [he1]
      exact (flow_le π Q).1
  · haveI : IsFiniteMeasure (ν.withDensity (fun p => min (μ.rnDeriv ν p.swap) (μ.rnDeriv ν p))) :=
      isFiniteMeasure_of_le μ hleft
    exact le_flow π Q _ hleft hright
end TierneyProof

open scoped NNReal
namespace TierneyProof
open MeasureTheory.Measure
variable {E : Type*} [MeasurableSpace E] {ι : Type*} [Countable ι]

theorem mix_apply (β : ι → ℝ≥0) (K : ι → Kernel E E) [∀ i, IsSFiniteKernel (K i)]
    (x : E) : mixKernel β K x = Measure.sum (fun i => (β i : ℝ≥0∞) • K i x) := by
  unfold mixKernel
  rw [Kernel.sum_apply]
  congr 1
  funext i
  rw [Kernel.withDensity_apply _ measurable_const, withDensity_const]

theorem mix_markov (β : ι → ℝ≥0) (hβ : HasSum β 1)
    (Q : ι → Kernel E E) [∀ i, IsMarkovKernel (Q i)] : IsMarkovKernel (mixKernel β Q) := by
  constructor
  intro x
  constructor
  rw [mix_apply, Measure.sum_apply _ MeasurableSet.univ]
  simpa using ENNReal.tsum_coe_eq hβ

theorem compProd_mix (π : Measure E) [SFinite π] (β : ι → ℝ≥0)
    (K : ι → Kernel E E) [∀ i, IsSFiniteKernel (K i)] :
    π ⊗ₘ mixKernel β K = Measure.sum (fun i => (β i : ℝ≥0∞) • (π ⊗ₘ K i)) := by
  haveI : ∀ i, IsSFiniteKernel ((K i).withDensity fun _ _ => (β i : ℝ≥0∞)) :=
    fun i => Kernel.IsSFiniteKernel.withDensity (K i) fun _ _ => ENNReal.coe_ne_top
  unfold mixKernel
  rw [Measure.compProd_sum_right]
  congr 1
  funext i
  rw [Measure.compProd_withDensity measurable_const, withDensity_const]

theorem weighted_sum_mono {α : Type*} [MeasurableSpace α] (β : ι → ℝ≥0)
    (μ ν : ι → Measure α) (h : ∀ i, μ i ≤ ν i) :
    Measure.sum (fun i => (β i : ℝ≥0∞) • μ i) ≤
      Measure.sum (fun i => (β i : ℝ≥0∞) • ν i) := by
  apply Measure.le_iff.mpr
  intro s hs
  simp only [Measure.sum_apply _ hs, Measure.smul_apply, smul_eq_mul]
  apply ENNReal.tsum_le_tsum
  intro i
  simpa only [mul_comm] using mul_le_mul_left (h i s) (β i : ℝ≥0∞)

theorem mixture_flow (π : Measure E) [IsProbabilityMeasure π]
    (Q : ι → Kernel E E) [∀ i, IsMarkovKernel (Q i)] (β : ι → ℝ≥0) (hβ : HasSum β 1) :
    Measure.sum (fun i => (β i : ℝ≥0∞) • ((π ⊗ₘ Q i).withDensity (alphaMH π (Q i)))) ≤
      (π ⊗ₘ mixKernel β Q).withDensity (alphaMH π (mixKernel β Q)) := by
  haveI := mix_markov β hβ Q
  let σ := Measure.sum (fun i => (β i : ℝ≥0∞) • ((π ⊗ₘ Q i).withDensity (alphaMH π (Q i))))
  have hl : σ ≤ π ⊗ₘ mixKernel β Q := by
    rw [compProd_mix]
    exact weighted_sum_mono β _ _ fun i => (flow_le π (Q i)).1
  have hr : σ ≤ (π ⊗ₘ mixKernel β Q).map Prod.swap := by
    rw [compProd_mix, Measure.map_sum measurable_swap.aemeasurable]
    simp only [Measure.map_smul]
    exact weighted_sum_mono β _ _ fun i => (flow_le π (Q i)).2
  haveI : IsFiniteMeasure σ := isFiniteMeasure_of_le (π ⊗ₘ mixKernel β Q) hl
  exact le_flow π (mixKernel β Q) σ hl hr
end TierneyProof

namespace TierneyMeasure
open MeasureTheory.Measure
variable {E : Type*} [MeasurableSpace E]

theorem kernel_le_of_compProd_le [MeasurableSpace.CountablyGenerated E]
    (π : Measure E) [IsFiniteMeasure π] (κ η : Kernel E E)
    [IsFiniteKernel κ] [IsFiniteKernel η] (h : π ⊗ₘ κ ≤ π ⊗ₘ η) :
    ∀ᵐ x ∂π, κ x ≤ η x := by
  have hac : ∀ᵐ x ∂π, κ x ≪ η x := h.absolutelyContinuous.kernel_of_compProd
  have he : ∀ᵐ x ∂π, κ x = η.withDensity (κ.rnDeriv η) x := by
    filter_upwards [hac] with x hx using (Kernel.withDensity_rnDeriv_eq hx).symm
  have hl : ∀ᵐ x ∂π, ∀ᵐ y ∂η x, κ.rnDeriv η x y ≤ 1 := by
    apply Measure.ae_ae_of_ae_compProd (p := fun p => κ.rnDeriv η p.1 p.2 ≤ 1)
    apply ae_le_of_forall_setLIntegral_le_of_sigmaFinite (by fun_prop)
    intro s hs hfin
    simp only [lintegral_const, Measure.restrict_apply, MeasurableSet.univ, Set.univ_inter, one_mul]
    calc
      ∫⁻ p in s, κ.rnDeriv η p.1 p.2 ∂π ⊗ₘ η = (π ⊗ₘ κ) s := by
        rw [Measure.compProd_congr he, Measure.compProd_withDensity, withDensity_apply _ hs]
        fun_prop
      _ ≤ (π ⊗ₘ η) s := h s
  filter_upwards [he,hl] with x hx hxl
  rw [hx, Kernel.withDensity_apply _ (by fun_prop)]
  calc
    (η x).withDensity (κ.rnDeriv η x) ≤ (η x).withDensity (fun _ => 1) := withDensity_mono hxl
    _ = η x := by simp
end TierneyMeasure

namespace TierneyProof
open MeasureTheory.Measure
variable {E : Type*} [MeasurableSpace E]

theorem alpha_measurable (π : Measure E) (Q : Kernel E E) : Measurable (alphaMH π Q) :=
  (measurable_const.min ((ratio_measurable π Q).comp measurable_swap)).indicator (R_measurable π Q)

noncomputable def accepted (π : Measure E) (Q : Kernel E E) [IsSFiniteKernel Q] : Kernel E E :=
  Q.withDensity (fun x y => alphaMH π Q (x,y))

instance accepted_finite (π : Measure E) (Q : Kernel E E) [IsFiniteKernel Q] :
    IsFiniteKernel (accepted π Q) :=
  Kernel.isFiniteKernel_withDensity_of_bounded Q ENNReal.one_ne_top (fun _ _ => alphaMH_le_one π Q _)

theorem accepted_le (π : Measure E) (Q : Kernel E E) [IsFiniteKernel Q] : accepted π Q ≤ Q := by
  intro x
  rw [accepted]
  rw [Kernel.withDensity_apply _ (show Measurable (fun p : E × E => alphaMH π Q (p.1,p.2)) from alpha_measurable π Q)]
  calc
    (Q x).withDensity (fun y => alphaMH π Q (x,y)) ≤ (Q x).withDensity (fun _ => 1) :=
      withDensity_mono (Eventually.of_forall fun y => alphaMH_le_one π Q (x,y))
    _ = Q x := by simp

theorem accepted_compProd (π : Measure E) [SFinite π] (Q : Kernel E E) [IsFiniteKernel Q] :
    π ⊗ₘ accepted π Q = (π ⊗ₘ Q).withDensity (alphaMH π Q) := by
  haveI : IsFiniteKernel (Q.withDensity (fun x y => alphaMH π Q (x,y))) := accepted_finite π Q
  exact Measure.compProd_withDensity (alpha_measurable π Q)

theorem mix_kernel_mono {ι : Type*} [Countable ι] (β : ι → ℝ≥0)
    (K L : ι → Kernel E E) [∀ i, IsSFiniteKernel (K i)] [∀ i, IsSFiniteKernel (L i)]
    (h : ∀ i, K i ≤ L i) : mixKernel β K ≤ mixKernel β L := by
  intro x
  rw [mix_apply, mix_apply]
  exact weighted_sum_mono β _ _ (fun i => h i x)

theorem mixture_accepted_le [MeasurableSpace.CountablyGenerated E]
    (π : Measure E) [IsProbabilityMeasure π]
    {ι : Type*} [Countable ι] (Q : ι → Kernel E E) [∀ i, IsMarkovKernel (Q i)]
    (β : ι → ℝ≥0) (hβ : HasSum β 1) :
    ∀ᵐ x ∂π, mixKernel β (fun i => accepted π (Q i)) x ≤ accepted π (mixKernel β Q) x := by
  haveI := mix_markov β hβ Q
  haveI : IsFiniteKernel (mixKernel β (fun i => accepted π (Q i))) :=
    isFiniteKernel_of_le (mix_kernel_mono β _ _ (fun i => accepted_le π (Q i)))
  apply TierneyMeasure.kernel_le_of_compProd_le
  rw [accepted_compProd, compProd_mix]
  simp_rw [accepted_compProd]
  exact mixture_flow π Q β hβ

theorem flow_symmetric (π : Measure E) [IsProbabilityMeasure π]
    (Q : Kernel E E) [IsMarkovKernel Q] :
    ((π ⊗ₘ Q).withDensity (alphaMH π Q)).map Prod.swap = (π ⊗ₘ Q).withDensity (alphaMH π Q) := by
  let σ := (π ⊗ₘ Q).withDensity (alphaMH π Q)
  haveI : IsFiniteMeasure σ := isFiniteMeasure_of_le (π ⊗ₘ Q) (flow_le π Q).1
  have hl : σ.map Prod.swap ≤ σ := by
    apply le_flow π Q
    · simpa only [Measure.map_map measurable_swap measurable_swap, Prod.swap_swap_eq, Measure.map_id] using
        Measure.map_mono (flow_le π Q).2 measurable_swap
    · exact Measure.map_mono (flow_le π Q).1 measurable_swap
  apply le_antisymm hl
  simpa only [Measure.map_map measurable_swap measurable_swap, Prod.swap_swap_eq, Measure.map_id] using
    Measure.map_mono hl measurable_swap
end TierneyProof

namespace TierneyProof
open MeasureTheory.Measure
open TierneyMH.Shared
variable {E : Type*} [MeasurableSpace E]

theorem max_offdiag [MeasurableSingletonClass E] (π : Measure E)
    (Q : Kernel E E) [IsFiniteKernel Q] (x : E) (A : Set E) (hA : MeasurableSet A) :
    maxMHKernel π Q x (A \ {x}) = accepted π Q x (A \ {x}) := by
  let r : E → ℝ≥0∞ := fun x => ∫⁻ u, (1-alphaMH π Q (x,u)) ∂Q x
  have hr : Measurable r :=
    (measurable_const.sub (alpha_measurable π Q)).lintegral_kernel_prod_right' (κ := Q)
  change (Q.withDensity (fun x y => alphaMH π Q (x,y)) +
    Kernel.id.withDensity (fun x (_ : E) => r x)) x (A \ {x}) = _
  rw [Kernel.add_apply, Measure.add_apply]
  have hz : (Kernel.id.withDensity (fun x (_ : E) => r x)) x (A \ {x}) = 0 := by
    rw [Kernel.withDensity_apply _ (show Measurable (fun p : E × E => r p.1) from hr.comp measurable_fst), Kernel.id_apply,
      withDensity_const, Measure.smul_apply, Measure.dirac_apply' _ (hA.diff (measurableSet_singleton x))]
    simp
  rw [hz, add_zero]
  rfl

theorem mix_max_offdiag [MeasurableSingletonClass E] (π : Measure E)
    {ι : Type*} [Countable ι] (Q : ι → Kernel E E) [∀ i, IsFiniteKernel (Q i)]
    (β : ι → ℝ≥0) (x : E) (A : Set E) (hA : MeasurableSet A) :
    mixKernel β (fun i => maxMHKernel π (Q i)) x (A \ {x}) =
      mixKernel β (fun i => accepted π (Q i)) x (A \ {x}) := by
  rw [mix_apply, mix_apply]
  simp only [Measure.sum_apply _ (hA.diff (measurableSet_singleton x)), Measure.smul_apply, smul_eq_mul]
  apply tsum_congr
  intro i
  rw [max_offdiag π (Q i) x A hA]

theorem mixture_offdiag [MeasurableSingletonClass E] [MeasurableSpace.CountablyGenerated E]
    (π : Measure E) [IsProbabilityMeasure π]
    {ι : Type*} [Countable ι] (Q : ι → Kernel E E) [∀ i, IsMarkovKernel (Q i)]
    (β : ι → ℝ≥0) (hβ : HasSum β 1) :
    OffDiagDominates π (maxMHKernel π (mixKernel β Q))
      (mixKernel β fun i => maxMHKernel π (Q i)) := by
  haveI := mix_markov β hβ Q
  filter_upwards [mixture_accepted_le π Q β hβ] with x hx
  intro A hA
  rw [max_offdiag π (mixKernel β Q) x A hA, mix_max_offdiag π Q β x A hA]
  exact hx (A \ {x})
end TierneyProof

open TierneyMH.Mixture TierneyMH.Shared

/-- **Proposition 5** (Tierney 1998, p. 7). Let `Qᵢ` be a (countable) sequence of Markov
proposal kernels and `βᵢ ≥ 0` with `∑ βᵢ = 1`. Let `Pᵢ` be the maximal Metropolis–Hastings
kernel for `Qᵢ` and `P` the maximal Metropolis–Hastings kernel for the mixture proposal
`Q = ∑ βᵢ Qᵢ`, all for the target `π`. Then `P ⪰ ∑ βᵢ Pᵢ`: for `π`-almost every `x`,
`P(x, A \ {x}) ≥ ∑ βᵢ Pᵢ(x, A \ {x})` for all measurable `A`.

Added hypotheses: measurable singletons (implicit in the paper's `A \ {x}`), and a countably
generated σ-algebra on `E`, which makes the exceptional `π`-null set uniform over `A`. -/
theorem solution {E : Type*} [MeasurableSpace E] [MeasurableSingletonClass E]
    [MeasurableSpace.CountablyGenerated E]
    (π : Measure E) [IsProbabilityMeasure π]
    {ι : Type*} [Countable ι] (Q : ι → Kernel E E) [∀ i, IsMarkovKernel (Q i)]
    (β : ι → ℝ≥0) (hβ : HasSum β 1) :
    OffDiagDominates π (maxMHKernel π (mixKernel β Q))
      (mixKernel β fun i => maxMHKernel π (Q i)) := by
  exact TierneyProof.mixture_offdiag π Q β hβ


