-- Prove2me | solution 1 for ZetaZeros.D.EllReg.symbolLowerBound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T16:01:04.401844+00:00
-- url     : https://prove2.me/submissions/92966904-3abe-4f92-b84a-416d5bee5d52

import Definitions.Def_Formalism_UnipotentAdelicQuotients_EllRegCut
import Definitions.Def_Formalism_UnipotentAdelicQuotients_EllipticRegularity_SymbLower
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace ZetaZeros.D.EllReg
open MeasureTheory Metric Filter Topology
open scoped ContDiff FourierTransform ENNReal
noncomputable section
private theorem symb_smul_covector_eq_pow_ord_mul {d : ℕ} {ι : Type} (P : Sys d ι) (i : ι)
    (x ξ : E d) (t : ℝ) :
    P.symb i x (t • ξ) = (t : ℂ) ^ (P.ord i) * P.symb i x ξ := by
  unfold ZetaZeros.D.EllReg.Sys.symb
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun w _ => ?_
  have hc : ∀ l, (((t • ξ) (w l) : ℝ) : ℂ) = (t : ℂ) * ((ξ (w l) : ℝ) : ℂ) := fun l => by simp
  simp only [hc, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  ring
private theorem continuous_symb_covector {d : ℕ} {ι : Type} (P : Sys d ι) (i : ι)
    (x : E d) : Continuous fun ξ : E d => P.symb i x ξ := by
  unfold ZetaZeros.D.EllReg.Sys.symb
  fun_prop
end
end ZetaZeros.D.EllReg
end

set_option autoImplicit false
open ZetaZeros ZetaZeros.D ZetaZeros.D.EllReg
open MeasureTheory Metric Filter Topology
open scoped ContDiff FourierTransform ENNReal
noncomputable section
namespace ZetaZeros.D.EllReg
theorem _root_.solution : SymbLower := by
  intro d ι _ P x0 k hk hell
  obtain ⟨f, hf⟩ : ∃ f : E d → ℝ,
      f = fun ξ => ∑ i, ‖ξ‖ ^ (2 * (k - P.ord i)) * ‖P.symb i x0 ξ‖ ^ 2 := ⟨_, rfl⟩
  have hfξ : ∀ ξ, f ξ = ∑ i, ‖ξ‖ ^ (2 * (k - P.ord i)) * ‖P.symb i x0 ξ‖ ^ 2 := by
    intro ξ; rw [hf]
  have hcont : Continuous f := by
    rw [hf]
    refine continuous_finsetSum _ fun i _ => ?_
    exact (continuous_norm.pow _).mul
      ((continuous_symb_covector P i x0).norm.pow 2)
  have hhom : ∀ t : ℝ, 0 ≤ t → ∀ ξ : E d, f (t • ξ) = t ^ (2 * k) * f ξ := by
    intro t ht ξ
    rw [hfξ, hfξ, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    have h1 : ‖t • ξ‖ = t * ‖ξ‖ := by rw [norm_smul, Real.norm_of_nonneg ht]
    have h2 : ‖(t : ℂ) ^ (P.ord i) * P.symb i x0 ξ‖
        = t ^ (P.ord i) * ‖P.symb i x0 ξ‖ := by
      rw [norm_mul, norm_pow, Complex.norm_of_nonneg ht]
    rw [symb_smul_covector_eq_pow_ord_mul, h1, h2]
    have hk' : 2 * k = 2 * (k - P.ord i) + 2 * P.ord i := by have := hk i; omega
    rw [hk', pow_add]
    ring
  rcases (sphere (0 : E d) 1).eq_empty_or_nonempty with hS | hS
  · refine ⟨1, one_pos, fun ξ hξ => ?_⟩
    exfalso
    have hmem : ‖ξ‖⁻¹ • ξ ∈ sphere (0 : E d) 1 := by
      rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm,
        inv_mul_cancel₀ (norm_ne_zero_iff.mpr hξ)]
    rw [hS] at hmem
    exact hmem
  · obtain ⟨η0, hη0S, hmin⟩ := (isCompact_sphere (0 : E d) 1).exists_isMinOn hS hcont.continuousOn
    have hη0n : ‖η0‖ = 1 := mem_sphere_zero_iff_norm.mp hη0S
    have hne : η0 ≠ 0 := by
      intro h
      rw [h, norm_zero] at hη0n
      exact zero_ne_one hη0n
    obtain ⟨i, hi⟩ := hell η0 hne
    have hpos : 0 < f η0 := by
      have hle : ‖η0‖ ^ (2 * (k - P.ord i)) * ‖P.symb i x0 η0‖ ^ 2 ≤ f η0 := by
        rw [hfξ]
        exact Finset.single_le_sum
          (f := fun j => ‖η0‖ ^ (2 * (k - P.ord j)) * ‖P.symb j x0 η0‖ ^ 2)
          (fun j _ => by positivity) (Finset.mem_univ i)
      have hlt : 0 < ‖η0‖ ^ (2 * (k - P.ord i)) * ‖P.symb i x0 η0‖ ^ 2 := by
        rw [hη0n, one_pow, one_mul]
        exact pow_pos (norm_pos_iff.mpr hi) 2
      linarith
    refine ⟨f η0, hpos, fun ξ hξ => ?_⟩
    have ht : 0 < ‖ξ‖ := norm_pos_iff.mpr hξ
    have hηS : ‖ξ‖⁻¹ • ξ ∈ sphere (0 : E d) 1 := by
      rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ ht.ne']
    have hξη : ξ = ‖ξ‖ • (‖ξ‖⁻¹ • ξ) := by
      rw [smul_smul, mul_inv_cancel₀ ht.ne', one_smul]
    have hle : f η0 ≤ f (‖ξ‖⁻¹ • ξ) := hmin hηS
    have hfx : f ξ = ‖ξ‖ ^ (2 * k) * f (‖ξ‖⁻¹ • ξ) := by
      conv_lhs => rw [hξη]
      exact hhom _ ht.le _
    rw [← hfξ, hfx, mul_comm]
    exact mul_le_mul_of_nonneg_left hle (by positivity)
end ZetaZeros.D.EllReg
