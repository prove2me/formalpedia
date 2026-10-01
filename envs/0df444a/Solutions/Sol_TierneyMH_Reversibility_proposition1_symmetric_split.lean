-- Prove2me | solution 1 for TierneyMH.Reversibility.proposition1_symmetric_split
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T12:18:43.043812+00:00
-- url     : https://prove2.me/submissions/84ef2ff7-9003-4527-be8c-dc79beae92ad

import Definitions.Def_TierneyMH_Shared_IsSymmetricSplit
import Definitions.Def_TierneyMH_Shared_IsRatioVersion
import Mathlib.Tactic
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal
open TierneyMH.Shared
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

namespace ProofBTierney

noncomputable def density {E : Type*} [MeasurableSpace E] (μ : Measure (E × E)) := μ.rnDeriv (μ+μ.map Prod.swap)
def overlap {E : Type*} [MeasurableSpace E] (μ : Measure (E × E)) : Set (E × E) := {p | 0<density μ p ∧ 0<density μ p.swap}
open Classical in
noncomputable def ratio {E : Type*} [MeasurableSpace E] (μ : Measure (E × E)) (p : E × E) : ℝ≥0∞ :=
  if p∈overlap μ ∧ density μ p ≠ ⊤ ∧ density μ p.swap ≠ ⊤ then density μ p/density μ p.swap else 1

variable {E : Type*} [MeasurableSpace E] (μ : Measure (E × E))

theorem density_measurable : Measurable (density μ) :=
  Measure.measurable_rnDeriv _ _

theorem R_measurable : MeasurableSet (overlap μ) :=
  (measurableSet_lt measurable_const (density_measurable μ)).inter
    (measurableSet_lt measurable_const ((density_measurable μ).comp measurable_swap))

theorem R_swap (p : E × E) : p.swap ∈ overlap μ ↔ p ∈ overlap μ := by
  simp [overlap,and_comm]

theorem ratio_pos (p : E × E) : 0 < ratio μ p ∧ ratio μ p ≠ ⊤ := by
  unfold ratio
  split_ifs with h
  · exact ⟨ENNReal.div_pos_iff.mpr ⟨ne_of_gt h.1.1,h.2.2⟩,
      ENNReal.div_ne_top h.2.1 (ne_of_gt h.1.2)⟩
  · simp

theorem ratio_inv (p : E × E) : ratio μ p.swap = (ratio μ p)⁻¹ := by
  classical
  have hs : (p.swap ∈ overlap μ ∧ density μ p.swap ≠ ⊤ ∧ density μ p.swap.swap ≠ ⊤) ↔
      (p ∈ overlap μ ∧ density μ p ≠ ⊤ ∧ density μ p.swap ≠ ⊤) := by
    simp [R_swap μ,and_left_comm,and_comm,and_assoc]
  unfold ratio
  rw [if_congr hs rfl rfl]
  split_ifs with h
  · simpa using (ENNReal.inv_div (Or.inl h.2.2) (Or.inr (ne_of_gt h.1.1))).symm
  · simp

end ProofBTierney
namespace ProofBTierney
open TierneyMH.Shared
open MeasureTheory.Measure
variable {E : Type*} [MeasurableSpace E] (μ : Measure (E × E))

theorem ratio_measurable : Measurable (ratio μ) := by
  classical
  have hf := density_measurable μ
  have hg := hf.comp measurable_swap
  have hR := R_measurable μ
  unfold ratio
  apply Measurable.ite
    (hR.inter ((measurableSet_eq_fun hf measurable_const).compl.inter
      (measurableSet_eq_fun hg measurable_const).compl))
  · exact hf.div hg
  · exact measurable_const

variable [SigmaFinite μ]

theorem canonical_split :
    IsSymmetricSplit μ (overlap μ) ∧
      IsRatioVersion μ (overlap μ) (ratio μ) := by
  letI : SigmaFinite (μ.map Prod.swap) := (MeasurableEquiv.prodComm : E × E ≃ᵐ E × E).sigmaFinite_map
  let R0 := overlap μ
  let r := ratio μ
  change IsSymmetricSplit μ R0 ∧ IsRatioVersion μ R0 r
  let ν := μ + μ.map Prod.swap
  let f := density μ
  let g := fun p : E × E => f p.swap
  have hν : ν.map Prod.swap = ν := TierneyMeasure.sum_swap_symmetric μ
  have hμν : μ ≪ ν := Measure.AbsolutelyContinuous.rfl.add_right _
  have hf : Measurable f := density_measurable μ
  have hg : Measurable g := hf.comp measurable_swap
  have he1 : ν.withDensity f = μ := Measure.withDensity_rnDeriv_eq μ ν hμν
  have he2 : ν.withDensity g = μ.map Prod.swap := TierneyMeasure.swap_density μ ν hν hμν
  have hR := R_measurable μ
  have hfR : ∀ p ∈ overlap μ, 0 < f p := fun p hp => hp.1
  have hgR : ∀ p ∈ overlap μ, 0 < g p := fun p hp => hp.2
  constructor
  · refine ⟨hR,?_,?_,?_,?_⟩
    · ext p
      exact R_swap μ p
    · change μ.restrict R0 ≪ (μ.map Prod.swap).restrict R0
      rw [← he2,← he1]
      exact TierneyMeasure.density_ac_on_positive ν f g hf hg _ hR hgR
    · change (μ.map Prod.swap).restrict R0 ≪ μ.restrict R0
      rw [← he2,← he1]
      exact TierneyMeasure.density_ac_on_positive ν g f hg hf _ hR hfR
    · change μ.restrict R0ᶜ ⟂ₘ (μ.map Prod.swap).restrict R0ᶜ
      rw [← he2,← he1]
      exact TierneyMeasure.density_singular_off_overlap ν f g hf hg
  · refine ⟨ratio_measurable μ,fun p => ⟨(ratio_pos μ p).1,lt_top_iff_ne_top.mpr (ratio_pos μ p).2⟩,
      ratio_inv μ,?_⟩
    have hfin : ∀ᵐ p ∂ν, f p ≠ ⊤ := (Measure.rnDeriv_lt_top μ ν).mono (fun _ h => h.ne)
    have hfin' : ∀ᵐ p ∂ν, g p ≠ ⊤ := by
      have hm : ∀ᵐ p ∂ν.map Prod.swap, f p ≠ ⊤ := by simpa only [hν] using hfin
      exact (MeasurableEquiv.prodComm : E × E ≃ᵐ E × E).measurableEmbedding.ae_map_iff.mp hm
    change μ.restrict R0 = ((μ.map Prod.swap).restrict R0).withDensity r
    rw [← he2,← he1,restrict_withDensity hR,restrict_withDensity hR,
      ← withDensity_mul _ hg (ratio_measurable μ)]
    apply withDensity_congr_ae
    filter_upwards [self_mem_ae_restrict hR,ae_restrict_of_ae hfin,ae_restrict_of_ae hfin'] with p hp hfp hgp
    have he : p ∈ overlap μ ∧ density μ p ≠ ⊤ ∧ density μ p.swap ≠ ⊤ := ⟨hp,hfp,hgp⟩
    change f p = g p * ratio μ p
    rw [ratio,if_pos he]
    exact (ENNReal.mul_div_cancel (ne_of_gt hp.2) hgp).symm
end ProofBTierney

namespace ProofBTierney
open MeasureTheory.Measure
private theorem diff_null {α : Type*} [MeasurableSpace α] (μ ν : Measure α)
    (S T : Set α) (hS : MeasurableSet S) (hT : MeasurableSet T)
    (hac : μ.restrict S ≪ ν.restrict S) (hsing : μ.restrict Tᶜ ⟂ₘ ν.restrict Tᶜ) :
    μ (S\T)=0 := by
  have ha : μ.restrict (S\T) ≪ ν.restrict (S\T) := by
    simpa only [restrict_restrict hT.compl,sdiff_eq_compl_inter,inter_comm] using hac.restrict Tᶜ
  have hs : μ.restrict (S\T) ⟂ₘ ν.restrict (S\T) := by
    simpa only [restrict_restrict hS,sdiff_eq_compl_inter,inter_comm] using ((hsing.restrict S).symm.restrict S).symm
  have hz:=eq_zero_of_absolutelyContinuous_of_mutuallySingular ha hs
  exact Measure.restrict_eq_zero.mp hz

private theorem split_unique {E : Type*} [MeasurableSpace E] (μ : Measure (E × E))
    (R R' : Set (E × E)) (hR : IsSymmetricSplit μ R) (hR' : IsSymmetricSplit μ R') :
    μ (symmDiff R R')=0 ∧ (μ.map Prod.swap) (symmDiff R R')=0 := by
  have h1:=diff_null μ (μ.map Prod.swap) R R' hR.1 hR'.1 hR.2.2.1 hR'.2.2.2.2
  have h2:=diff_null μ (μ.map Prod.swap) R' R hR'.1 hR.1 hR'.2.2.1 hR.2.2.2.2
  have h3:=diff_null (μ.map Prod.swap) μ R R' hR.1 hR'.1 hR.2.2.2.1 hR'.2.2.2.2.symm
  have h4:=diff_null (μ.map Prod.swap) μ R' R hR'.1 hR.1 hR'.2.2.2.1 hR.2.2.2.2.symm
  exact ⟨by simpa only [symmDiff_def,Set.sup_eq_union] using measure_union_null h1 h2,
    by simpa only [symmDiff_def,Set.sup_eq_union] using measure_union_null h3 h4⟩
end ProofBTierney

open ProofBTierney in
theorem solution {E : Type*} [MeasurableSpace E] (μ : Measure (E × E)) [SigmaFinite μ] :
    (∃ R, IsSymmetricSplit μ R) ∧
    (∀ R R', IsSymmetricSplit μ R → IsSymmetricSplit μ R' →
      μ (symmDiff R R') = 0 ∧ (μ.map Prod.swap) (symmDiff R R') = 0) ∧
    (∀ R, IsSymmetricSplit μ R → ∃ r : E × E → ℝ≥0∞, IsRatioVersion μ R r) := by
  obtain ⟨hR0,hr0⟩:=canonical_split μ
  refine ⟨⟨overlap μ,hR0⟩,split_unique μ,?_⟩
  intro R hR
  obtain ⟨hm,hn⟩:=split_unique μ R (overlap μ) hR hR0
  have hm' := Measure.restrict_congr_set (measure_symmDiff_eq_zero_iff.mp hm)
  have hn' := Measure.restrict_congr_set (measure_symmDiff_eq_zero_iff.mp hn)
  refine ⟨ratio μ,hr0.1,hr0.2.1,hr0.2.2.1,?_⟩
  rw [hm',hn']
  exact hr0.2.2.2
