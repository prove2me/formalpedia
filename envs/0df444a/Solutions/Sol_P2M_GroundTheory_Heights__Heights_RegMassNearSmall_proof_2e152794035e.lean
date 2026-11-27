-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RegMassNearSmall_proof_2e152794035e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T05:08:14.440075+00:00
-- url     : https://prove2.me/submissions/ced8bb7e-02cd-4038-b907-c462b41165ba

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StRegMassNearSmall
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StRegFormCompare
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StRegBallMass
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSmallSetBallCover
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PVarIntAdd
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PRegMassNearSmall
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ComplexSets_FibreBound_proof_4038dff927b3
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_SheetSumMeasurable_proof_de88497bcca1
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_VarIntAdd_abs_chartDens_le_0d8d1be60cc4
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_VarIntAdd_proof_5f0bc402ccc8


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets
namespace GroundTheory.Heights₂.Heights
namespace RegMassNearSmall
theorem _root_.solution (hCmp : RegFormCompare.Statement) (hBall : RegBallMass.Statement)
    (hCov : SmallSetBallCover.Statement) : RegMassNearSmall.Statement := by
  classical
  intro n d J I u φ f hJ hdim hu hφ hIdim hf hfc δ hδ
  by_cases h : ∃ A : Matrix (Fin (d + 1)) (Fin n) ℂ, IsFiniteProjection J A
  swap
  · exact ⟨Set.univ, isOpen_univ, Set.subset_univ _, fun χ _ _ _ ε _ => by simp [varInt, h, hδ.le]⟩
  set A := h.choose
  have hA : IsFiniteProjection J A := h.choose_spec
  have hfin : ∀ y, (fibre J A y).Finite := fun y => (FibreBound.proof n (d + 1) J A hJ hdim hA y).2.1
  set K := tsupport f
  obtain ⟨C₁, hC₁, h₁⟩ := hCmp n d J A φ f hJ hdim hA hφ hf hfc
  obtain ⟨C₂, hC₂, h₂⟩ := hBall n d J A u K hJ hdim hA hu hfc
  obtain ⟨C₃, hC₃, h₃⟩ := hCov n d I K hIdim hfc
  have hM : 0 ≤ C₁ * C₂ * C₃ := by positivity
  set r := min 1 (δ / (C₁ * C₂ * C₃ + 1))
  have hr : r ∈ Set.Ioc (0 : ℝ) 1 := ⟨lt_min one_pos (by positivity), min_le_left _ _⟩
  obtain ⟨T, hTK, hcov, hcard⟩ := h₃ r hr
  have hUo : IsOpen ((⋃ c ∈ T, Metric.ball c r) ∪ Kᶜ) :=
    (isOpen_biUnion fun (c : Fin n → ℂ) _ => Metric.isOpen_ball).union hfc.isClosed.isOpen_compl
  refine ⟨(⋃ c ∈ T, Metric.ball c r) ∪ Kᶜ, hUo, fun x hx => ?_, fun χ _ hχ1 hχU ε hε => ?_⟩
  · by_cases hxK : x ∈ K
    · exact Or.inl (hcov ⟨hx, hxK⟩)
    · exact Or.inr hxK
  set ψ : Fin (d + 1) → (Fin n → ℂ) → ℝ := vecCons (logReg u ε) fun _ => euclPot
  set w : (Fin n → ℂ) → ℝ := fun x => ∑ c ∈ T, (Metric.ball c r).indicator (fun _ => (1 : ℝ)) x with hw
  have hi0 : ∀ c x : Fin n → ℂ, 0 ≤ (Metric.ball c r).indicator (fun _ => (1 : ℝ)) x :=
    fun c x => Set.indicator_nonneg (fun _ _ => zero_le_one) x
  have hw0 : ∀ x, 0 ≤ w x := fun x => Finset.sum_nonneg fun c _ => hi0 c x
  have hvw : ∀ x ∈ K, |χ x| ≤ w x := by
    intro x hxK
    by_cases h0 : χ x = 0
    · rw [h0, abs_zero]
      exact hw0 x
    rcases hχU (subset_tsupport χ h0) with hxB | hxK'
    · obtain ⟨c, hc, hxc⟩ := Set.mem_iUnion₂.1 hxB
      calc |χ x| ≤ 1 := hχ1 x
        _ = (Metric.ball c r).indicator (fun _ => (1 : ℝ)) x := (Set.indicator_of_mem hxc (fun _ => (1 : ℝ))).symm
        _ ≤ w x := Finset.single_le_sum (f := fun c => (Metric.ball c r).indicator (fun _ => (1 : ℝ)) x)
            (fun c _ => hi0 c x) hc
    · exact absurd hxK hxK'
  have hsum : chartDens J A w ψ =
      fun y => ∑ c ∈ T, chartDens J A ((Metric.ball c r).indicator fun _ => 1) ψ y := by
    funext y
    simp only [chartDens, sheetSum]
    simp_rw [finsum_mem_eq_finite_toFinset_sum _ (hfin y)]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun x _ => ?_
    split_ifs <;> simp [hw, Finset.sum_mul]
  have hball := fun c (hc : c ∈ T) => h₂ ε hε c (hTK hc).2 r hr
  have hint : Integrable (chartDens J A w ψ) := by
    rw [hsum]
    exact integrable_finsetSum _ fun c hc => (hball c hc).1
  have hT : ∫ y, chartDens J A w ψ y ≤ T.card * (C₂ * r ^ (2 * d)) := by
    rw [hsum, integral_finsetSum _ fun c hc => (hball c hc).1, ← nsmul_eq_mul, ← Finset.sum_const]
    exact Finset.sum_le_sum fun c hc => (hball c hc).2
  rw [varInt, dif_pos h]
  calc |chartInt J A (fun x => χ x * f x) (vecCons (logReg u ε) φ)|
      ≤ ∫ y, C₁ * chartDens J A w ψ y := by
        refine abs_integral_le_integral_abs.trans (integral_mono_of_nonneg
          (Eventually.of_forall fun y => abs_nonneg _) (hint.const_mul C₁) (Eventually.of_forall fun y => ?_))
        exact (VarIntAdd.abs_chartDens_le hfin _ _ y).trans (h₁ u ε hε.1 χ w hw0 hvw y)
    _ = C₁ * ∫ y, chartDens J A w ψ y := integral_const_mul _ _
    _ ≤ C₁ * (T.card * (C₂ * r ^ (2 * d))) := mul_le_mul_of_nonneg_left hT hC₁
    _ = C₁ * C₂ * (T.card * r ^ (2 * d)) := by ring
    _ ≤ C₁ * C₂ * (C₃ * r ^ 2) := mul_le_mul_of_nonneg_left hcard (by positivity)
    _ ≤ (C₁ * C₂ * C₃ + 1) * r := by
        nlinarith [mul_le_mul_of_nonneg_left hr.2 (mul_nonneg hM hr.1.le), hr.1]
    _ ≤ (C₁ * C₂ * C₃ + 1) * (δ / (C₁ * C₂ * C₃ + 1)) :=
        mul_le_mul_of_nonneg_left (min_le_right _ _) (by positivity)
    _ = δ := mul_div_cancel₀ _ (by positivity)
end RegMassNearSmall
end GroundTheory.Heights₂.Heights
