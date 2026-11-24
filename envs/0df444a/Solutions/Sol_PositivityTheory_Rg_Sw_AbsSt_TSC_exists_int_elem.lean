-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.AbsSt.TSC.exists_int_elem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:07:28.069573+00:00
-- url     : https://prove2.me/submissions/7bb57ff6-3132-48b1-8ed7-0af003a7d552

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AbsoluteConvergence_IteratedDerivSumOn

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Topology
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.AbsSt PositivityTheory.Rg.Sw.AbsSt.TSC
namespace PositivityTheory.Rg.Sw.AbsSt.TSC
theorem _root_.solution {X : Type} [MeasurableSpace X] (ν : Measure X) {V : Type} [AddCommGroup V] [Module ℂ V]
    (W : Submodule ℂ V) [FiniteDimensional ℂ W] (φ : X → V) (hφ : ∀ x, φ x ∈ W)
    (hint : ∀ l : V →ₗ[ℂ] ℂ, Integrable (fun x => l (φ x)) ν) :
    ∃ Φ ∈ W, ∀ l : V →ₗ[ℂ] ℂ, l Φ = ∫ x, l (φ x) ∂ν := by
  classical
  let b := Module.finBasis ℂ W
  choose cl hcl using fun j => LinearMap.exists_extend (b.coord j)
  have hc : ∀ j x, cl j (φ x) = b.repr ⟨φ x, hφ x⟩ j := by
    intro j x
    have := LinearMap.congr_fun (hcl j) ⟨φ x, hφ x⟩
    simpa using this
  have hrepr : ∀ x, φ x = ∑ j, cl j (φ x) • (b j : V) := by
    intro x
    have h1 := b.sum_repr ⟨φ x, hφ x⟩
    have h2 := congrArg (fun w : W => (w : V)) h1
    simp only [Submodule.coe_sum, Submodule.coe_smul] at h2
    simp only [hc]
    exact h2.symm
  refine ⟨∑ j, (∫ x, cl j (φ x) ∂ν) • (b j : V), Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (b j).2,
    fun l => ?_⟩
  have e1 : ∀ x, l (φ x) = ∑ j, cl j (φ x) * l (b j) := by
    intro x
    conv_lhs => rw [hrepr x]
    simp [map_sum, map_smul, smul_eq_mul]
  simp only [map_sum, map_smul, smul_eq_mul]
  simp_rw [e1]
  rw [integral_finsetSum]
  · refine Finset.sum_congr rfl fun j _ => ?_
    rw [integral_mul_const]
  · intro j _
    exact (hint (cl j)).mul_const _
end PositivityTheory.Rg.Sw.AbsSt.TSC
