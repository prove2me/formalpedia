-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HilbertSamuel_ComponentResFibreFinite_smul_segre_mem_fibre_954212387671
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T16:21:24.535813+00:00
-- url     : https://prove2.me/submissions/5efa8b0b-07ee-4579-9dd5-5174e650867c

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsComponentResFibreFinite
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterBridgeB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterFib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PComponentResFibreFinite
import Theorems.Thm_ReciprocityTheory_AnForm_M_ima_apply
import Theorems.Thm_ReciprocityTheory_AnForm_M_rea_apply
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_mcPts_smul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_segre_smul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.AnForm.M.ima_apply
attribute [local simp] ReciprocityTheory.AnForm.M.rea_apply



set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.HilbertSamuel
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
noncomputable section
open GroundTheory.Heights₂.Heights.HilbertSamuel.ComponentResFibreFinite
variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {W : Ideal (MvPolynomial (Σ k, ι k) ℂ)} {e : ℕ}
namespace GroundTheory.Heights₂.Heights.HilbertSamuel.ComponentResFibreFinite
theorem _root_.solution {P : Ideal (MRing ι)} (hK : Nonempty K) (hPh : IsMultiHomogIdeal P)
    (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) {z : (Σ k, ι k) → ℂ} (hz : z ∈ mcPts P)
    (h0 : Ψ (segre z) 0 ≠ 0) :
    (Ψ (segre z) 0)⁻¹ • segre z ∈
      fibre P Ψ (fun i : Fin e => Ψ (segre z) i.succ / Ψ (segre z) 0) := by
  obtain ⟨k0⟩ := hK
  let c : K → ℂ := Function.update (fun _ => (1 : ℂ)) k0 (Ψ (segre z) 0)⁻¹
  have hc : ∀ k, c k ≠ 0 := by
    intro k
    by_cases hk : k = k0
    · subst hk; simp [c, h0]
    · simp [c, Function.update_of_ne hk]
  have hpc : ∏ k, c k = (Ψ (segre z) 0)⁻¹ := by
    simp [c, Finset.prod_update_of_mem (Finset.mem_univ k0)]
  refine ⟨fun p => c p.1 * z p, mcPts_smul hPh c hc hz, ?_, ?_⟩
  · rw [segre_smul, hpc]
  · funext i
    refine Fin.cases ?_ (fun i => ?_) i
    · simp [h0]
    · simp only [map_smul, Pi.smul_apply, smul_eq_mul, Fin.cons_succ]
      rw [div_eq_inv_mul]
end GroundTheory.Heights₂.Heights.HilbertSamuel.ComponentResFibreFinite
