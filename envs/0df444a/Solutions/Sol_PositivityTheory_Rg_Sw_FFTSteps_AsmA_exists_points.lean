-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.FFTSteps.AsmA.exists_points
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:09:54.932308+00:00
-- url     : https://prove2.me/submissions/ab010436-b478-4147-9c5f-6359e8239ede

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_GaussianPlaneIntegrals_AssemblyTA
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_GaussianPlaneIntegrals_AssemblyTB

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory MvPolynomial
open scoped ComplexOrder
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.FFTSteps PositivityTheory.Rg.Sw.FFTSteps.AsmA
variable {ι A B : Type} [Fintype ι] [DecidableEq ι]
namespace PositivityTheory.Rg.Sw.FFTSteps.AsmA
theorem _root_.solution {σ : Type} [Fintype σ] (W : Submodule ℂ (MvPolynomial σ ℂ)) [FiniteDimensional ℂ W]
    (ℓ : W →ₗ[ℂ] ℂ) : ∃ c : (σ → ℂ) →₀ ℂ, ∀ q : W, ℓ q = c.sum fun z a => a * eval z (q : MvPolynomial σ ℂ) := by
  let ev : (σ → ℂ) → Module.Dual ℂ W := fun z => (MvPolynomial.aeval z).toLinearMap.comp W.subtype
  have hev : ∀ z (q : W), ev z q = eval z (q : MvPolynomial σ ℂ) := fun z q => by
    simp [ev]
  set S := Submodule.span ℂ (Set.range ev)
  have hco : S.dualCoannihilator = ⊥ := by
    rw [eq_bot_iff]
    intro w hw
    rw [Submodule.mem_dualCoannihilator] at hw
    have h0 : (w : MvPolynomial σ ℂ) = 0 := MvPolynomial.funext fun z => by
      rw [map_zero, ← hev]
      exact hw _ (Submodule.subset_span ⟨z, rfl⟩)
    rw [Submodule.mem_bot]
    exact Subtype.ext h0
  have hS : S = ⊤ := by
    have h := Subspace.finrank_add_finrank_dualCoannihilator_eq S
    rw [hco, finrank_bot, add_zero] at h
    exact Submodule.eq_top_of_finrank_eq (h.trans (Subspace.dual_finrank_eq).symm)
  have hℓ : ℓ ∈ S := hS ▸ Submodule.mem_top
  obtain ⟨c, hc⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp hℓ
  refine ⟨c, fun q => ?_⟩
  rw [← hc, Finsupp.sum, Finsupp.sum, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun z _ => ?_
  rw [LinearMap.smul_apply, hev, smul_eq_mul]
end PositivityTheory.Rg.Sw.FFTSteps.AsmA
