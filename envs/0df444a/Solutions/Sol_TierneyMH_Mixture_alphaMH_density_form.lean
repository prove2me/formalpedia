-- Prove2me | solution 1 for TierneyMH.Mixture.alphaMH_density_form
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T12:17:54.463743+00:00
-- url     : https://prove2.me/submissions/1e42b1dc-d6a2-4e78-9d5a-a10486b0657b

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

open TierneyMH.Mixture

/-- **Density form of `μ α_MH`** (Tierney 1998, proof of Proposition 5, p. 8, first two lines
of the display). Let `ν` be any σ-finite symmetric measure on `E × E` (`ν(dx, dy) = ν(dy, dx)`)
dominating `μ(dx, dy) = π(dx) Q(x, dy)`, and let `h = dμ/dν`. Then
`π(dx) Q(x, dy) α_MH(x, y) = min{h(y, x), h(x, y)} ν(dx, dy)`
as measures on `E × E`. -/
theorem solution {E : Type*} [MeasurableSpace E]
    (π : Measure E) [IsProbabilityMeasure π] (Q : Kernel E E) [IsMarkovKernel Q]
    (ν : Measure (E × E)) [SigmaFinite ν] (hν_symm : ν.map Prod.swap = ν)
    (hμν : π ⊗ₘ Q ≪ ν) :
    (π ⊗ₘ Q).withDensity (alphaMH π Q) =
      ν.withDensity (fun p => min ((π ⊗ₘ Q).rnDeriv ν p.swap) ((π ⊗ₘ Q).rnDeriv ν p)) := by
  exact TierneyProof.density_form π Q ν hν_symm hμν


