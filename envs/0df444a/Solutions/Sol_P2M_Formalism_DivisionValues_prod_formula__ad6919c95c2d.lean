-- Prove2me | solution 1 for P2M_Formalism_DivisionValues_prod_formula__ad6919c95c2d
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:26:40.64887+00:00
-- url     : https://prove2.me/submissions/6c362f13-fdd4-4ea1-8e85-22e960bace4b

import Definitions.Def_Formalism_QuotientMetricDivisors_ProdFormula
import Definitions.Def_Formalism_LogFactorialIndices_SignedSubspaceIndex_LogProductFormula
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ProdFormula
import Theorems.Thm_Formalism_DivisionValues_log_abs_norm_eq_two_sum

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
noncomputable section
open Formalism Formalism.DivisionValues
namespace Formalism.DivisionValues
theorem _root_.solution : ProdFormula := by
  intro K _ _ _ _ a ha
  set I : FractionalIdeal (nonZeroDivisors (𝓞 K)) K := FractionalIdeal.spanSingleton _ a with hIdef
  have hI : I ≠ 0 := by
    rw [hIdef, Ne, FractionalIdeal.spanSingleton_eq_zero_iff]
    exact ha
  have hfin : {w : HeightOneSpectrum (𝓞 K) | FractionalIdeal.count K w I ≠ 0}.Finite :=
    Filter.eventually_cofinite.mp (FractionalIdeal.finite_factors I)
  have hvw : ∀ w : HeightOneSpectrum (𝓞 K), vw w a = FractionalIdeal.count K w I := fun w => rfl
  have hsupp : (Function.support fun w : HeightOneSpectrum (𝓞 K) => lw w * (vw w a : ℝ)) ⊆
      (hfin.toFinset : Set (HeightOneSpectrum (𝓞 K))) := by
    intro w hw
    simp only [Function.mem_support, Set.Finite.coe_toFinset, Set.mem_setOf_eq] at hw ⊢
    intro h0
    apply hw
    simp [hvw, h0]
  refine ⟨hfin.subset (by simpa using hsupp), ?_⟩
  rw [finsum_eq_sum_of_support_subset _ hsupp]
  have hpos : ∀ w : HeightOneSpectrum (𝓞 K), (Ideal.absNorm w.asIdeal : ℝ) ≠ 0 := fun w => by
    rw [Nat.cast_ne_zero, Ne, Ideal.absNorm_eq_zero_iff]
    exact w.ne_bot
  have hN : (|Algebra.norm ℚ a| : ℚ) = ∏ w ∈ hfin.toFinset,
      ((Ideal.absNorm w.asIdeal : ℚ)) ^ FractionalIdeal.count K w I := by
    rw [← FractionalIdeal.absNorm_span_singleton (𝓞 K), ← hIdef]
    conv_lhs => rw [← FractionalIdeal.finprod_heightOneSpectrum_factorization' K hI]
    rw [finprod_eq_prod_of_mulSupport_subset _ (s := hfin.toFinset) ?_, map_prod]
    · refine Finset.prod_congr rfl fun w _ => ?_
      rw [map_zpow₀, FractionalIdeal.coeIdeal_absNorm]
    · intro w hw
      simp only [Function.mem_mulSupport, Set.Finite.coe_toFinset, Set.mem_setOf_eq] at hw ⊢
      intro h0
      apply hw
      rw [h0, zpow_zero]
  have hlog : Real.log |((Algebra.norm ℚ a : ℚ) : ℝ)| = ∑ w ∈ hfin.toFinset,
      (FractionalIdeal.count K w I : ℝ) * Real.log (Ideal.absNorm w.asIdeal : ℝ) := by
    have h1 : |((Algebra.norm ℚ a : ℚ) : ℝ)| = ∏ w ∈ hfin.toFinset,
        ((Ideal.absNorm w.asIdeal : ℝ)) ^ FractionalIdeal.count K w I := by
      rw [← Rat.cast_abs, hN]
      push_cast
      rfl
    rw [h1, Real.log_prod (fun w _ => zpow_ne_zero _ (hpos w))]
    exact Finset.sum_congr rfl fun w _ => Real.log_zpow _ _
  have hB := log_abs_norm_eq_two_sum K a ha
  have hn : (finrank ℚ K : ℝ) ≠ 0 := by
    have := Module.finrank_pos (R := ℚ) (M := K)
    positivity
  calc (2 / (finrank ℚ K : ℝ)) * ∑ v : InfinitePlace K, Real.log ‖v.embedding a‖
      = Real.log |((Algebra.norm ℚ a : ℚ) : ℝ)| / finrank ℚ K := by
        rw [hB]
        field_simp
    _ = ∑ w ∈ hfin.toFinset, lw w * (vw w a : ℝ) := by
        rw [hlog, Finset.sum_div]
        refine Finset.sum_congr rfl fun w _ => ?_
        rw [hvw, lw]
        ring
end Formalism.DivisionValues
