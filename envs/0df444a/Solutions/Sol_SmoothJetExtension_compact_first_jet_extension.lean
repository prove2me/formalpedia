-- Prove2me | solution 1 for SmoothJetExtension.compact_first_jet_extension
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-29T20:32:38.865273+00:00
-- url     : https://prove2.me/submissions/90acbf37-b872-49d2-ab7a-6073d9e7451b

import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Tactic.FunProp

open Set Filter Function
open scoped ContDiff Topology Manifold
namespace SmoothJetExtension
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- Compatible local scalar first jets on a closed set glue to a globally smooth
function. The hypotheses require actual local extensions, not arbitrary Whitney data. -/
lemma exists_global_of_local_first_jet (C : Set E) (hC : IsClosed C)
    (h : E → ℝ) (L : E → (E →L[ℝ] ℝ))
    (hloc : ∀ p ∈ C, ∃ U : Set E, IsOpen U ∧ p ∈ U ∧
      ∃ g : E → ℝ, ContDiffOn ℝ ∞ g U ∧
        ∀ q ∈ C ∩ U, g q = h q ∧ fderiv ℝ g q = L q) :
    ∃ H : E → ℝ, ContDiff ℝ ∞ H ∧
      ∀ p ∈ C, H p = h p ∧ fderiv ℝ H p = L p := by
  classical
  have hlocal : ∀ p : E, ∃ U : Set E, IsOpen U ∧ p ∈ U ∧
      ∃ g : E → ℝ, ContDiffOn ℝ ∞ g U ∧
        ∀ q ∈ C ∩ U, g q = h q ∧ fderiv ℝ g q = L q := by
    intro p
    by_cases hp : p ∈ C
    · exact hloc p hp
    · refine ⟨Cᶜ, hC.isOpen_compl, hp, fun _ => 0, contDiffOn_const, ?_⟩
      intro q hq
      exact (hq.2 hq.1).elim
  choose U hU hpU g hg hj using hlocal
  obtain ⟨ρ, hρ⟩ := SmoothPartitionOfUnity.exists_isSubordinate (𝓘(ℝ, E))
    isClosed_univ U hU (fun p _ => mem_iUnion.mpr ⟨p, hpU p⟩)
  let H : E → ℝ := fun p => ∑ᶠ i, ρ i p • g i p
  have hρc : ∀ i, ContDiff ℝ ∞ (ρ i) := fun i => contMDiff_iff_contDiff.mp (ρ i).contMDiff
  have hH : ContDiff ℝ ∞ H := by
    apply contDiff_iff_contDiffAt.mpr
    intro p
    apply ρ.contDiffAt_finsum
    intro i hi
    exact (hg i).contDiffAt ((hU i).mem_nhds (hρ i hi))
  refine ⟨H, hH, ?_⟩
  intro p hp
  let S := ρ.fintsupport p
  have hnear : (fun q => H q) =ᶠ[𝓝 p] (fun q => ∑ i ∈ S, ρ i q • g i q) := by
    filter_upwards [ρ.eventually_fintsupport_subset p] with q hq
    apply finsum_eq_sum_of_support_subset
    intro i hi
    have hni : ρ i q ≠ 0 := left_ne_zero_of_smul (mem_support.mp hi)
    exact hq (ρ.finsupport_subset_fintsupport q ((ρ.mem_finsupport q).mpr hni))
  have hWnear : (fun q => ∑ i ∈ S, ρ i q) =ᶠ[𝓝 p] (fun _ => (1 : ℝ)) := by
    filter_upwards [ρ.eventually_finsupport_subset p] with q hq
    exact ρ.sum_finsupport' q (mem_univ q) hq
  have hjp : ∀ i ∈ S, g i p = h p ∧ HasFDerivAt (g i) (L p) p := by
    intro i hi
    have hi' : p ∈ tsupport (ρ i) := (ρ.mem_fintsupport_iff p i).mp hi
    have hpU' := hρ i hi'
    have he := hj i p ⟨hp, hpU'⟩
    refine ⟨he.1, ?_⟩
    rw [← he.2]
    exact ((hg i).contDiffAt ((hU i).mem_nhds hpU')).differentiableAt (by simp) |>.hasFDerivAt
  have hWd := HasFDerivAt.fun_sum (u := S) (fun i _ =>
    ((hρc i).differentiable (by simp) p).hasFDerivAt)
  have hWzero : (∑ i ∈ S, fderiv ℝ (ρ i) p) = 0 :=
    (hWd.congr_of_eventuallyEq hWnear.symm).unique (hasFDerivAt_const (1 : ℝ) p)
  have hWone : ∑ i ∈ S, ρ i p = 1 := hWnear.eq_of_nhds
  have hHd := HasFDerivAt.fun_sum (u := S) (fun i hi =>
    (((hρc i).differentiable (by simp) p).hasFDerivAt.smul (hjp i hi).2))
  have hDeriv : (∑ i ∈ S,
      (ρ i p • L p + (fderiv ℝ (ρ i) p).smulRight (g i p))) = L p := by
    ext v
    simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
    calc (∑ i ∈ S, (ρ i p * L p v + fderiv ℝ (ρ i) p v * g i p))
        = (∑ i ∈ S, ρ i p) * L p v + (∑ i ∈ S, fderiv ℝ (ρ i) p v) * h p := by
          simp only [Finset.sum_add_distrib, Finset.sum_mul]
          congr 1
          apply Finset.sum_congr rfl
          intro i hi
          rw [(hjp i hi).1]
      _ = L p v := by
        have he := congrArg (fun A : E →L[ℝ] ℝ => A v) hWzero
        simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.zero_apply] at he
        rw [he, hWone]; simp
  constructor
  · rw [hnear.eq_of_nhds]
    calc (∑ i ∈ S, ρ i p • g i p) = (∑ i ∈ S, ρ i p) * h p := by
           simp only [smul_eq_mul, Finset.sum_mul]
           apply Finset.sum_congr rfl
           intro i hi
           rw [(hjp i hi).1]
         _ = h p := by rw [hWone, one_mul]
  · have hd : HasFDerivAt H (L p) p := by
      rw [← hDeriv]
      exact hHd.congr_of_eventuallyEq hnear
    exact hd.fderiv

end SmoothJetExtension

namespace SmoothJetExtension
open Set Filter Function
open scoped ContDiff Topology Manifold
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

lemma compact_cutoff_preserves_first_jet (C : Set E) (hC : IsCompact C)
    (H : E → ℝ) (hH : ContDiff ℝ ∞ H) :
    ∃ G : E → ℝ, ContDiff ℝ ∞ G ∧ HasCompactSupport G ∧
      ∀ p ∈ C, G p = H p ∧ fderiv ℝ G p = fderiv ℝ H p := by
  obtain ⟨R, hR⟩ := hC.isBounded.subset_ball (0 : E)
  have hCR : C ⊆ interior (Metric.closedBall (0 : E) R) :=
    hR.trans Metric.ball_subset_interior_closedBall
  obtain ⟨χ, hχC, hχout, -⟩ := exists_contMDiffMap_one_nhds_of_subset_interior
    (𝓘(ℝ, E)) hC.isClosed hCR (n := (⊤ : ℕ∞))
  have hχ : ContDiff ℝ ∞ (χ : E → ℝ) := contMDiff_iff_contDiff.mp χ.contMDiff
  have hχcomp : HasCompactSupport (χ : E → ℝ) := by
    apply (isCompact_closedBall (0 : E) R).of_isClosed_subset isClosed_closure
    apply closure_minimal _ Metric.isClosed_closedBall
    intro p hp
    by_contra hn
    exact hp (hχout p hn)
  refine ⟨fun p => χ p * H p, hχ.mul hH, hχcomp.mul_right, ?_⟩
  intro p hp
  have he : (fun q => χ q * H q) =ᶠ[𝓝 p] H := by
    filter_upwards [hχC.filter_mono (nhds_le_nhdsSet hp)] with q hq
    rw [hq, one_mul]
  exact ⟨he.eq_of_nhds, he.fderiv_eq⟩

lemma exists_compact_of_local_first_jet (C : Set E) (hC : IsCompact C)
    (h : E → ℝ) (L : E → (E →L[ℝ] ℝ))
    (hloc : ∀ p ∈ C, ∃ U : Set E, IsOpen U ∧ p ∈ U ∧
      ∃ g : E → ℝ, ContDiffOn ℝ ∞ g U ∧
        ∀ q ∈ C ∩ U, g q = h q ∧ fderiv ℝ g q = L q) :
    ∃ H : E → ℝ, ContDiff ℝ ∞ H ∧ HasCompactSupport H ∧
      ∀ p ∈ C, H p = h p ∧ fderiv ℝ H p = L p := by
  obtain ⟨H, hH, hjet⟩ := exists_global_of_local_first_jet C hC.isClosed h L hloc
  obtain ⟨G, hG, hGc, hGjet⟩ := compact_cutoff_preserves_first_jet C hC H hH
  exact ⟨G, hG, hGc, fun p hp => ⟨(hGjet p hp).1.trans (hjet p hp).1,
    (hGjet p hp).2.trans (hjet p hp).2⟩⟩

end SmoothJetExtension

open Set Function
open scoped ContDiff
theorem solution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (C : Set E) (hC : IsCompact C)
    (h : E → ℝ) (L : E → (E →L[ℝ] ℝ))
    (hloc : ∀ p ∈ C, ∃ U : Set E, IsOpen U ∧ p ∈ U ∧
      ∃ g : E → ℝ, ContDiffOn ℝ ∞ g U ∧
        ∀ q ∈ C ∩ U, g q = h q ∧ fderiv ℝ g q = L q) :
    ∃ H : E → ℝ, ContDiff ℝ ∞ H ∧ HasCompactSupport H ∧
      ∀ p ∈ C, H p = h p ∧ fderiv ℝ H p = L p := by
  exact SmoothJetExtension.exists_compact_of_local_first_jet C hC h L hloc
