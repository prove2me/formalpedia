-- Prove2me | solution 1 for PositivityTheory.ThKEst.CS.Dual.eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:07:58.383824+00:00
-- url     : https://prove2.me/submissions/0a6b2140-d062-4fa1-a22b-5738a3415724

import Mathlib
import Definitions.Def_Development_WeilBound_ThetaLifts_FrameEstimates_CoefSumA
import Theorems.Thm_PositivityTheory_ThKEst_CS_Dual_compactQ
import Theorems.Thm_PositivityTheory_ThKEst_CS_Dual_separates
import Theorems.Thm_PositivityTheory_ThKEst_CS_Dual_bdd
import Theorems.Thm_PositivityTheory_ThKEst_CS_Dual_lint
import Theorems.Thm_PositivityTheory_ThKEst_CS_Dual_fin
import Theorems.Thm_PositivityTheory_ThKEst_CS_Dual_intOn

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Topology Filter
open scoped ENNReal ComplexConjugate Pointwise
open PositivityTheory PositivityTheory.ThKEst PositivityTheory.ThKEst.CS
variable {G Γ : Type} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G] [AddCommGroup Γ]
variable {r : Γ →+ G} {e : Γ → G → ℂ}
variable [MeasurableSpace G] [BorelSpace G] [Countable Γ] {μ : Measure G} [μ.IsAddHaarMeasure] {D : Set G}
namespace PositivityTheory.ThKEst.CS
namespace Dual
theorem _root_.solution (h : Dual r e) (hD : IsAddFundamentalDomain r.range D μ) {P : G → ℂ} (hPc : Continuous P)
    (hPp : ∀ ξ u, P (r ξ + u) = P u) (hcoef : ∀ ξ, ∫ u in D, e ξ u * P u ∂μ = 0) : P = 0 := by
  have := h.compactQ
  have hDf := h.fin hD
  obtain ⟨C, hC⟩ := h.bdd hPc hPp
  have hint : ∀ g : C(G ⧸ r.range, ℂ), IntegrableOn (fun u : G => g (u : G ⧸ r.range) * P u) D μ := fun g =>
    h.intOn hD ((g.continuous.comp continuous_quotient_mk').mul hPc) fun ξ u => by
      rw [hPp]
      congr 2
      rw [QuotientAddGroup.eq, show -(r ξ + u) + u = -r ξ by abel]
      exact neg_mem ⟨ξ, rfl⟩
  let L₀ : C(G ⧸ r.range, ℂ) →ₗ[ℂ] ℂ :=
    { toFun := fun g => ∫ u in D, g (u : G ⧸ r.range) * P u ∂μ
      map_add' := fun x y => by
        simp only [ContinuousMap.add_apply, add_mul]
        exact integral_add (hint x) (hint y)
      map_smul' := fun c x => by
        simp only [ContinuousMap.smul_apply, smul_eq_mul, mul_assoc, RingHom.id_apply]
        exact integral_const_mul _ _ }
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0)
  let L : C(G ⧸ r.range, ℂ) →L[ℂ] ℂ := L₀.mkContinuous (C * μ.real D) fun g => by
    refine (norm_setIntegral_le_of_norm_le_const (C := ‖g‖ * C) hDf.lt_top fun u _ => ?_).trans (le_of_eq (by ring))
    rw [norm_mul]
    exact mul_le_mul (g.norm_coe_le_norm _) (hC u) (norm_nonneg _) (norm_nonneg _)
  have hvan : (Achar h : Set C(G ⧸ r.range, ℂ)) ⊆ {g | L g = 0} := by
    intro g hg
    have : Submodule.span ℂ (Set.range (chiC h)) ≤ LinearMap.ker L₀ :=
      Submodule.span_le.2 (by rintro _ ⟨ξ, rfl⟩; exact hcoef ξ)
    exact this hg
  have hclos := ContinuousMap.starSubalgebra_topologicalClosure_eq_top_of_separatesPoints (Achar h) h.separates
  let Pb : C(G ⧸ r.range, ℂ) := liftC (fun u => conj (P u)) (fun ξ u => by rw [hPp]) (Complex.continuous_conj.comp hPc)
  have hmem : Pb ∈ closure ((Achar h : Set C(G ⧸ r.range, ℂ))) := by
    have : Pb ∈ (Achar h).topologicalClosure := by rw [hclos]; exact StarSubalgebra.mem_top
    exact this
  have hint0 : ∫ u in D, conj (P u) * P u ∂μ = 0 :=
    closure_minimal hvan (isClosed_eq L.continuous continuous_const) hmem
  have hsq : ∫ u in D, ‖P u‖ ^ 2 ∂μ = 0 := by
    have e : (fun u => conj (P u) * P u) = fun u => ((‖P u‖ ^ 2 : ℝ) : ℂ) := by
      funext u; rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    rw [e, integral_complex_ofReal] at hint0
    exact_mod_cast hint0
  have hInt : IntegrableOn (fun u => ‖P u‖ ^ 2) D μ := by
    refine Measure.integrableOn_of_bounded hDf (hPc.norm.pow 2).aestronglyMeasurable (M := C ^ 2)
      (Eventually.of_forall fun u => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact pow_le_pow_left₀ (norm_nonneg _) (hC u) 2
  have hae := (integral_eq_zero_iff_of_nonneg (fun u => by positivity) hInt).1 hsq
  have h0 : ∫⁻ u, ‖P u‖ₑ ∂μ = 0 := by
    rw [h.lint hD]
    simp only [hPp]
    have : ∫⁻ u in D, ‖P u‖ₑ ∂μ = 0 := by
      rw [← lintegral_zero (μ := μ.restrict D)]
      refine lintegral_congr_ae (hae.mono fun u hu => ?_)
      simpa using hu
    simp [this]
  rw [lintegral_eq_zero_iff hPc.enorm.measurable] at h0
  refine (hPc.ae_eq_iff_eq μ continuous_zero).1 (h0.mono fun u hu => ?_)
  simpa using hu
end Dual
end PositivityTheory.ThKEst.CS
