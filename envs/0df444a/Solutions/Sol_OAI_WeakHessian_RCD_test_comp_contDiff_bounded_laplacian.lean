-- Prove2me | solution 1 for OAI.WeakHessian.RCD.test_comp_contDiff_bounded_laplacian
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T19:00:50.987905+00:00
-- url     : https://prove2.me/submissions/ee714b2c-ec20-4ed1-b671-77c9ccffd734

import Mathlib
import Definitions.Def_WeakHessian
import Definitions.Def_OAIQ52Wh007
import Theorems.Thm_OAI_WeakHessian_RCD_test_gradientSquare_sobolev

section
-- module Solutions.OAIQ52_WH.WeakHessian_Sobolev_CompContDiffLipschitz
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile0
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
open scoped ENNReal NNReal Topology BoundedContinuousFunction CompactlySupported
open scoped ENNReal NNReal Topology BoundedContinuousFunction
open scoped NNReal
open MeasureTheory Set Filter
open scoped Topology NNReal ENNReal
open scoped ENNReal NNReal Topology InnerProductSpace
open Set Filter Bornology
open MeasureTheory
open scoped ENNReal InnerProductSpace ComplexConjugate
open Set Filter
open scoped Topology ENNReal NNReal
open Set
open Set MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped Topology ENNReal NNReal InnerProductSpace
open scoped BoundedContinuousFunction
open Set MeasureTheory Filter
open Set Filter MeasureTheory Topology TopologicalSpace
open scoped ENNReal NNReal
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal MeasureTheory ProbabilityTheory
open Set Filter Topology Bornology
open scoped InnerProductSpace
open Filter
open scoped Topology
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

attribute [local instance] Classical.propDecidable
namespace WeakHessian
open MeasureTheory Set Filter WeakHessianFunctional
open scoped Topology InnerProductSpace NNReal

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompleteSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X}

lemma Sobolev.comp_contDiff_lipschitz (hfinite : FiniteOnBoundedSets m)
    {f : X → ℝ} (hf : Sobolev m f) {φ : ℝ → ℝ} (hφ : ContDiff ℝ 1 φ)
    {L : ℝ≥0} (hLip : LipschitzWith L φ) (hzero : φ 0 = 0) :
    Sobolev m (φ ∘ f) := by
  have hB : ∀ᵐ x ∂m, |deriv φ (f x)| ≤ (L:ℝ) :=
    ae_of_all _ (fun x => norm_deriv_le_of_lipschitz hLip)
  have hmeas : AEStronglyMeasurable (fun x => |deriv φ (f x)|) m :=
    ((hφ.continuous_deriv le_rfl).measurable.comp_aemeasurable hf.1.aemeasurable).abs.aestronglyMeasurable
  apply Sobolev.of_upperGradient hfinite (hLip.comp_memLp hzero hf.1)
    ((weakGradient_isMinimal hf.2.1.2).1.comp_contDiff hf.1.aemeasurable hφ hB)
  simpa only [mul_comm] using memLp_mul_bounded hf.2.2 hmeas (by simpa only [abs_abs] using hB)

end WeakHessian

end
end InlinedFile0

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_Sobolev_LaplacianChain
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile120
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X}

lemma IsLaplacian.comp_contDiff (hfin : FiniteOnBoundedSets m)
    (hpar : LocalGradientParallelogram m) {u A : X → ℝ} (hu : IsLaplacian m u A)
    {L : ℝ≥0} (hLip : LipschitzWith L u) {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ)
    {C D : ℝ≥0} (hC : LipschitzWith C φ) (hD : LipschitzWith D (deriv φ)) (h0 : φ 0 = 0) :
    IsLaplacian m (φ ∘ u) (fun x => deriv φ (u x)*A x+deriv (deriv φ) (u x)*gamma m u u x) := by
  have hc : ContDiff ℝ 1 φ := hφ.of_le (by norm_num)
  have hd : ContDiff ℝ 1 (deriv φ) := hφ.deriv'
  have hη : LipschitzWith (D*L) (deriv φ ∘ u) := hD.comp hLip
  have hηS := localSobolev_of_lipschitz hfin hη
  have hηB : ∀ᵐ x ∂m,|(deriv φ ∘ u) x| ≤ C := ae_of_all _ fun _ => norm_deriv_le_of_lipschitz hC
  have hηG : ∀ᵐ x ∂m,|weakGradient m (deriv φ ∘ u) x| ≤ (D*L:ℝ≥0) := by
    filter_upwards [weakGradient_nonneg (m := m) (deriv φ ∘ u),weakGradient_le_lipschitz hfin hη] with x hn hb
    simpa only [abs_of_nonneg hn] using hb
  have hη2B : ∀ᵐ x ∂m,|deriv (deriv φ) (u x)| ≤ D := ae_of_all _ fun _ => norm_deriv_le_of_lipschitz hD
  have hη2M := hd.continuous_deriv le_rfl |>.comp hLip.continuous |>.aestronglyMeasurable (μ := m)
  have hterm1 : MemLp (fun x => deriv φ (u x)*A x) 2 m := by
    simpa only [mul_comm,Function.comp_def] using memLp_mul_bounded hu.2.1 hη.continuous.aestronglyMeasurable hηB
  have hterm2 : MemLp (fun x => deriv (deriv φ) (u x)*gamma m u u x) 2 m := by
    simpa only [mul_comm,Function.comp_def] using memLp_mul_bounded (memLp_gamma_lipschitz hfin hpar hu.1 hLip) hη2M hη2B
  have hφS := hu.1.comp_contDiff_lipschitz hfin hc hC h0
  refine ⟨hφS,hterm1.add hterm2,?_⟩
  intro v hv
  have hvη := hv.mul_bounded hfin hηS hηB hηG
  have hform := hu.2.2 (fun x => v x*(deriv φ ∘ u) x) hvη
  have hmul := gamma_mul_left hfin hpar hv.2.1 hηS hu.1.2.1 hηB hηG
  have hchain1 := gamma_comp_contDiff hfin hpar hu.1.2.1 hu.1.2.1 hd hηS.1 hη2B
  have hchain0 := gamma_comp_contDiff hfin hpar hu.1.2.1 hv.2.1 hc hφS.2.1.1 hηB
  have hi1 : Integrable (fun x => deriv φ (u x)*A x*v x) m := hterm1.integrable_mul hv.1
  have hi2 : Integrable (fun x => deriv (deriv φ) (u x)*gamma m u u x*v x) m := hterm2.integrable_mul hv.1
  have hi3 : Integrable (fun x => deriv φ (u x)*gamma m u v x) m :=
    (integrable_gamma hfin hu.1 hv).bdd_mul hη.continuous.aestronglyMeasurable hηB
  have he : (∫ x,gamma m u (fun y => v y*(deriv φ ∘ u) y) x ∂m) =
      (∫ x,deriv (deriv φ) (u x)*gamma m u u x*v x ∂m)+
      (∫ x,deriv φ (u x)*gamma m u v x ∂m) := by
    rw [← integral_add hi2 hi3]
    apply integral_congr_ae
    filter_upwards [hmul,hchain1,gamma_comm (m := m) u (fun y => v y*(deriv φ ∘ u) y),gamma_comm (m := m) v u] with x hm hc hc1 hc2
    rw [hc1,hm,hc,hc2]
    dsimp only [Function.comp_def]
    ring
  rw [he] at hform
  have heR : (∫ x,A x*(v x*(deriv φ ∘ u) x) ∂m) = ∫ x,deriv φ (u x)*A x*v x ∂m :=
    integral_congr_ae (ae_of_all _ fun x => by dsimp only [Function.comp_def]; ring)
  rw [heR] at hform
  have heL : (∫ x,gamma m (φ ∘ u) v x ∂m) = ∫ x,deriv φ (u x)*gamma m u v x ∂m := integral_congr_ae hchain0
  rw [heL]
  simp_rw [add_mul]
  rw [integral_add hi1 hi2]
  linarith
end WeakHessian

end
end InlinedFile120

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_LocalBounds_TestChain
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile121
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X} [SigmaFinite m]

lemma RCD.test_comp_contDiff {K N : ℝ} (hN : 1 < N)
    (hrcd : RCD m K N) (hfull : FullSupport m) (hfin : FiniteOnBoundedSets m)
    (o : X) {g : X → ℝ} (hg : IsTestFunction m g)
    {φ : ℝ → ℝ} (hφ : ContDiff ℝ 3 φ) {C D E : ℝ≥0}
    (hC : LipschitzWith C φ) (hD : LipschitzWith D (deriv φ))
    (hE : LipschitzWith E (deriv (deriv φ))) (h0 : φ 0 = 0) :
    IsTestFunction m (φ ∘ g) := by
  obtain ⟨L,hL⟩ := hg.2.2.1
  obtain ⟨B,hB⟩ := hg.2.1
  have hpar := hrcd.1.global_localGradientParallelogram hfin o hrcd.2
  have hgen := (laplacian_isLaplacian hg.1).comp_contDiff hfin hpar hL (hφ.of_le (by norm_num)) hC hD h0
  have hsquare : Sobolev m (gamma m g g) :=
    (sobolev_congr_ae (gamma_self (m := m) g)).mpr (hrcd.test_gradientSquare_sobolev hN hfull hfin o hg)
  have hηB : ∀ᵐ x ∂m,|(deriv φ ∘ g) x| ≤ C := ae_of_all _ fun _ => norm_deriv_le_of_lipschitz hC
  have hη2B : ∀ᵐ x ∂m,|(deriv (deriv φ) ∘ g) x| ≤ D := ae_of_all _ fun _ => norm_deriv_le_of_lipschitz hD
  have gradbd {V : X → ℝ} {A : ℝ≥0} (hV : LipschitzWith A V) :
      ∀ᵐ x ∂m,|weakGradient m V x| ≤ A := by
    filter_upwards [weakGradient_nonneg (m := m) V,weakGradient_le_lipschitz hfin hV] with x hx hy
    simpa only [abs_of_nonneg hx] using hy
  have hs1 := hg.2.2.2.mul_bounded hfin (localSobolev_of_lipschitz hfin (hD.comp hL)) hηB (gradbd (hD.comp hL))
  have hs2 := hsquare.mul_bounded hfin (localSobolev_of_lipschitz hfin (hE.comp hL)) hη2B (gradbd (hE.comp hL))
  have hs : Sobolev m (fun x => deriv φ (g x)*laplacian m g x+deriv (deriv φ) (g x)*gamma m g g x) := by
    simpa only [Function.comp_def,mul_comm] using hs1.add hfin hs2
  refine ⟨⟨_,hgen⟩,⟨(C:ℝ)*B,fun x => ?_⟩,⟨C*L,hC.comp hL⟩,(sobolev_congr_ae (hgen.ae_laplacian hfin)).mpr hs⟩
  have HH := hC.dist_le_mul (g x) 0
  rw [h0,Real.dist_eq,sub_zero,Real.dist_eq,sub_zero] at HH
  exact HH.trans (mul_le_mul_of_nonneg_left (hB x) C.coe_nonneg)

lemma RCD.test_comp_contDiff_bounded_laplacian_oai {K N : ℝ} (hN : 1 < N)
    (hrcd : RCD m K N) (hfull : FullSupport m) (hfin : FiniteOnBoundedSets m)
    (o : X) {g : X → ℝ} (hg : IsTestFunction m g) {B : ℝ}
    (hB : ∀ᵐ x ∂m,|laplacian m g x| ≤ B)
    {φ : ℝ → ℝ} (hφ : ContDiff ℝ 3 φ) {C D E : ℝ≥0}
    (hC : LipschitzWith C φ) (hD : LipschitzWith D (deriv φ))
    (hE : LipschitzWith E (deriv (deriv φ))) (h0 : φ 0 = 0) :
    IsTestFunction m (φ ∘ g) ∧ ∃ A : ℝ,∀ᵐ x ∂m,|laplacian m (φ ∘ g) x| ≤ A := by
  refine ⟨hrcd.test_comp_contDiff hN hfull hfin o hg hφ hC hD hE h0,?_⟩
  obtain ⟨L,hL⟩ := hg.2.2.1
  have hpar := hrcd.1.global_localGradientParallelogram hfin o hrcd.2
  have hlap := ((laplacian_isLaplacian hg.1).comp_contDiff hfin hpar hL (hφ.of_le (by norm_num)) hC hD h0).ae_laplacian hfin
  refine ⟨(C:ℝ)*B+(D:ℝ)*(L:ℝ)^2,?_⟩
  filter_upwards [hlap,hB,gamma_self (m := m) g,weakGradient_nonneg (m := m) g,weakGradient_le_lipschitz hfin hL] with x hh hb hs hn hle
  rw [hh,hs]
  calc
    |deriv φ (g x)*laplacian m g x+deriv (deriv φ) (g x)*(weakGradient m g x)^2| ≤
        |deriv φ (g x)| *|laplacian m g x|+|deriv (deriv φ) (g x)| *(weakGradient m g x)^2 := by
      calc _ ≤ |deriv φ (g x)*laplacian m g x|+|deriv (deriv φ) (g x)*(weakGradient m g x)^2| := abs_add_le _ _
           _ = _ := by rw [abs_mul (deriv φ (g x)) (laplacian m g x),abs_mul (deriv (deriv φ) (g x)) ((weakGradient m g x)^2),abs_of_nonneg (sq_nonneg (weakGradient m g x))]
    _ ≤ (C:ℝ)*B+(D:ℝ)*(L:ℝ)^2 := add_le_add
      (mul_le_mul (norm_deriv_le_of_lipschitz hC) hb (abs_nonneg _) C.coe_nonneg)
      (mul_le_mul (norm_deriv_le_of_lipschitz hD) (pow_le_pow_left₀ hn hle 2) (sq_nonneg _) D.coe_nonneg)
end WeakHessian

end
end InlinedFile121

end OAI
end

theorem solution.{u_1} : type_of% @OAI.WeakHessian.RCD.test_comp_contDiff_bounded_laplacian_oai.{u_1} := @OAI.WeakHessian.RCD.test_comp_contDiff_bounded_laplacian_oai.{u_1}
