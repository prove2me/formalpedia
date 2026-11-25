-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LVs.TC.top_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:45:10.19681+00:00
-- url     : https://prove2.me/submissions/267b1d12-14f9-4f2e-825a-f973a2773a9b

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_TopCompB
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_TopCompC
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_TCCalc
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_TCBlock
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_TopComp
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_TC_detD_affine
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_TC_inG_inv
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_TC_inG_mul
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_TC_rotL_apply
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_TC_rotL_single
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_TC_rot_inG
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_TC_rot_nU
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_TC_topL_single
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_TC_top_vanish
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] PositivityTheory.Rg.Sw.LVs.TC.rotL_apply



set_option autoImplicit false
noncomputable section
open Matrix
open scoped ContDiff Topology
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs PositivityTheory.Rg.Sw.LVs.TC
open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ}
namespace PositivityTheory.Rg.Sw.LVs.TC
theorem _root_.solution (hA : IterAffine) {j : ℕ} {F : M2 n → ℂ} {Ω : Set (M2 n)} (hΩ : IsOpen Ω) (hG : GSet n ⊆ Ω)
    (hF : ContDiffOn ℂ ∞ F Ω) (hhyp : ∀ a b, InG a → InG b → detD (fun H => F (a * nU H * b)) = 0)
    {g : M2 n} (hg : InG g) : detD (fun t => F (g + topL g j t)) = 0 := by
  have hgΩ : g ∈ Ω := hG hg
  have key : ∀ θ : ℝ, ∑ σ : Equiv.Perm (Fin n), (Equiv.Perm.sign σ : ℂ) *
      iteratedFDeriv ℂ (Fintype.card (Fin n)) F g (fun i => rotL g j θ
        (single ((Fintype.equivFin (Fin n)).symm i) (σ ((Fintype.equivFin (Fin n)).symm i)) 1)) = 0 := by
    intro θ
    have h0 := hhyp (g * rot j θ) (rot j θ)⁻¹ (TC.inG_mul hg (rot_inG j θ)) (inG_inv (rot_inG j θ))
    simp only [rot_nU] at h0
    rwa [detD_affine hA hΩ hF hgΩ] at h0
  rw [detD_affine hA hΩ hF hgΩ]
  simp only [topL_single]
  have hv := top_vanish (iteratedFDeriv ℂ (Fintype.card (Fin n)) F g)
    (fun σ : Equiv.Perm (Fin n) => (Equiv.Perm.sign σ : ℂ))
    (fun σ i m => g * (Cm n * (![zLow j, zMid j, zTop j] m) ((Fintype.equivFin (Fin n)).symm i)
      (σ ((Fintype.equivFin (Fin n)).symm i)) * CmI n)) ?_
  · simpa using hv
  intro θ
  have h1 : ∀ σ : Equiv.Perm (Fin n), (Equiv.Perm.sign σ : ℂ) *
      iteratedFDeriv ℂ (Fintype.card (Fin n)) F g (fun i =>
        g * (Cm n * zLow j ((Fintype.equivFin (Fin n)).symm i) (σ ((Fintype.equivFin (Fin n)).symm i)) * CmI n)
        + Complex.exp (2 * ↑θ * Complex.I) • (g * (Cm n * zMid j ((Fintype.equivFin (Fin n)).symm i)
          (σ ((Fintype.equivFin (Fin n)).symm i)) * CmI n))
        + Complex.exp (2 * ↑θ * Complex.I) ^ 2 • (g * (Cm n * zTop j ((Fintype.equivFin (Fin n)).symm i)
          (σ ((Fintype.equivFin (Fin n)).symm i)) * CmI n)))
      = Complex.exp (2 * ↑θ * Complex.I) ^ Fintype.card (Fin n) * ((Equiv.Perm.sign σ : ℂ) *
        iteratedFDeriv ℂ (Fintype.card (Fin n)) F g (fun i => rotL g j θ
          (single ((Fintype.equivFin (Fin n)).symm i) (σ ((Fintype.equivFin (Fin n)).symm i)) 1))) := by
    intro σ
    simp_rw [← rotL_single]
    rw [ContinuousMultilinearMap.map_smul_univ, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
      smul_eq_mul]
    ring
  refine (Finset.sum_congr rfl fun σ _ => h1 σ).trans ?_
  rw [← Finset.mul_sum, key θ, mul_zero]
end PositivityTheory.Rg.Sw.LVs.TC
