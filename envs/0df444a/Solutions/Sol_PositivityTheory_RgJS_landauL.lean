-- Prove2me | solution 1 for PositivityTheory.RgJS.landauL
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T05:21:50.592468+00:00
-- url     : https://prove2.me/submissions/16c28a55-ea98-4c78-9580-88a1d3403617

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_JacquetShalikaBounds_AbsoluteRigidity_NewtonLow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_LandauSummableOfExpDirichletSeriesEntire
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_JacquetShalikaBounds_AbsoluteRigidity_LandauIteratedDerivatives_LandauL
import Theorems.Thm_PositivityTheory_RgJS_LandauNonnegativeDirichletSeries_linL
import Theorems.Thm_GlobalTheory_hasSum_tuple_prod_exp


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Complex Filter Topology
open PositivityTheory PositivityTheory.RgJS
open LandauNonnegativeDirichletSeries
namespace PositivityTheory.RgJS
theorem _root_.solution : LandauL := by
  intro I c l σ₀ σ₁ F hc hl hF hS hE
  set P := Σ n : ℕ, Fin n → I
  set C : P → ℝ := fun p => (∏ k, c (p.2 k)) / (p.1.factorial : ℝ) with hC
  set L : P → ℝ := fun p => ∑ k, l (p.2 k) with hL
  have hC0 : ∀ p, 0 ≤ C p := fun p => div_nonneg (Finset.prod_nonneg fun k _ => hc _) (Nat.cast_nonneg _)
  have hL0 : ∀ p, 0 ≤ L p := fun p => Finset.sum_nonneg fun k _ => hl _
  have hterm : ∀ σ : ℝ, ∀ p : P, (∏ k, (((c (p.2 k) * Real.exp (-(l (p.2 k) * σ)) : ℝ)) : ℂ)) / (p.1.factorial : ℂ) =
      ((C p * Real.exp (-(L p * σ)) : ℝ) : ℂ) := by
    intro σ p
    simp only [hC, hL]
    push_cast
    rw [Finset.prod_mul_distrib, ← Complex.exp_sum, Finset.sum_mul, Finset.sum_neg_distrib]
    ring
  have hexp : ∀ σ : ℝ, σ₁ < σ → HasSum (fun p : P => ((C p * Real.exp (-(L p * σ)) : ℝ) : ℂ))
      ((Real.exp (∑' i, c i * Real.exp (-(l i * σ))) : ℝ) : ℂ) := by
    intro σ hσ
    have h1 : HasSum (fun i => ((c i * Real.exp (-(l i * σ)) : ℝ) : ℂ)) ((∑' i, c i * Real.exp (-(l i * σ)) : ℝ) : ℂ) :=
      (Complex.hasSum_ofReal).2 (hS σ hσ).hasSum
    have h2 := GlobalTheory.hasSum_tuple_prod_exp _ _ h1
    rw [← Complex.ofReal_exp] at h2
    simpa only [hterm σ] using h2
  have key := linL P C L σ₀ σ₁ F hC0 hL0 hF
    (fun σ hσ => (Complex.hasSum_ofReal.1 (hexp σ hσ)).summable)
    (fun σ hσ => by rw [hE σ hσ]; exact (hexp σ hσ).tsum_eq.symm)
  intro σ hσ
  have hinj : Function.Injective (fun i : I => (⟨1, fun _ => i⟩ : P)) := by
    intro i j hij
    have := eq_of_heq (Sigma.mk.inj hij).2
    exact congrFun this 0
  have := (key σ hσ).comp_injective hinj
  refine this.congr fun i => ?_
  simp [hC, hL]
end PositivityTheory.RgJS
