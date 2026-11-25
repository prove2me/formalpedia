-- Prove2me | solution 1 for ReciprocityTheory.AnForm.maDens_comp_eq_zero_of_rank_lt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:28:21.80533+00:00
-- url     : https://prove2.me/submissions/284e4ff8-cf5b-49d6-b930-ac68dce6d3b2

import Definitions.Def_ReciprocityTheory_AnalyticForms_MaIntEmpty
import Definitions.Def_ReciprocityTheory_AnalyticForms_AnalyticCharts_MaDensCompEqZeroOfRankLt
import Theorems.Thm_ReciprocityTheory_AnForm_vecMul_hessC_comp_eq_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm
open Complex Filter Topology
open scoped Matrix
noncomputable section
namespace ReciprocityTheory.AnForm
theorem _root_.solution {N e : ℕ} (φ : Fin e → (Fin N → ℂ) → ℝ)
    (τ : (Fin e → ℂ) → (Fin N → ℂ)) (z : Fin e → ℂ) (hτ : AnalyticAt ℂ τ z)
    (hφ : ∀ k, ContDiffAt ℝ 2 (φ k) (τ z))
    (hrk : Module.finrank ℂ (LinearMap.range (fderiv ℂ τ z).toLinearMap) < e) :
    maDens (fun k => φ k ∘ τ) z = 0 := by
  obtain ⟨v, hv0, hv⟩ : ∃ v : Fin e → ℂ, v ≠ 0 ∧ fderiv ℂ τ z v = 0 := by
    have h1 := LinearMap.finrank_range_add_finrank_ker (fderiv ℂ τ z).toLinearMap
    rw [Module.finrank_fin_fun] at h1
    have h2 : 0 < Module.finrank ℂ (LinearMap.ker (fderiv ℂ τ z).toLinearMap) := by omega
    obtain ⟨x, hx⟩ := Module.finrank_pos_iff_exists_ne_zero.mp h2
    exact ⟨x, fun h => hx (Subtype.ext h), x.2⟩
  have hvm : ∀ S : Finset (Fin e), v ᵥ* (∑ k ∈ S, hessC (φ k ∘ τ) z) = 0 := by
    intro S
    refine Finset.induction_on S ?_ ?_
    · simp
    · intro k S hk ih
      rw [Finset.sum_insert hk, Matrix.vecMul_add, ih,
        vecMul_hessC_comp_eq_zero (φ k) τ z hτ (hφ k) v hv, add_zero]
  have hdet : ∀ S : Finset (Fin e), (∑ k ∈ S, hessC (φ k ∘ τ) z).det = 0 := fun S =>
    Matrix.exists_vecMul_eq_zero_iff.mp ⟨v, hv0, hvm S⟩
  unfold maDens mdisc
  simp [hdet]
end ReciprocityTheory.AnForm
