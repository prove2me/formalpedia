-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HilbertSamuel_ComponentResFibreFinite_proof_6307d8f24e4d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T04:57:49.71952+00:00
-- url     : https://prove2.me/submissions/49d88884-4877-4351-b7aa-a79d99fc8b36

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsComponentResFibreFinite
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterBridgeB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterFib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PComponentResFibreFinite
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_ComponentResFibreFinite_pt_mem_conePts_b7c8ef543411
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_ComponentResFibreFinite_mem_mcPts_of_conePts_d1e60471d38c
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_ComponentResFibreFinite_smul_segre_mem_fibre_954212387671
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_ComponentResFibreFinite_resW_injOn_d99cf9f5d8b5
import Theorems.Thm_ReciprocityTheory_CA_ModDepthGE_mono
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_fibreFinite


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.HilbertSamuel
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
noncomputable section
open GroundTheory.Heights₂.Heights.HilbertSamuel.ComponentResFibreFinite
variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {W : Ideal (MvPolynomial (Σ k, ι k) ℂ)} {e : ℕ}
namespace GroundTheory.Heights₂.Heights.HilbertSamuel.ComponentResFibreFinite
theorem _root_.solution : ComponentResFibreFinite.Statement := by
  intro K _ _ ι _ P e W R Ψ hP hW hΨ y
  have hle : P.map (MvPolynomial.map (Int.castRingHom ℂ)) ≤ W := hW.1.2
  have hbad : ∀ x ∉ resBad R Ψ,
      R.pt x ∉ ReciprocityTheory.AnForm.R.conePts R.D ∧ Ψ (segre (R.pt x)) 0 ≠ 0 :=
    fun x hx => ⟨fun h => hx (Or.inl (Or.inl h)), fun h => hx (Or.inl (Or.inr h))⟩
  refine Set.Finite.of_finite_image (f := resW R Ψ)
    ((fibreFinite K ι P e Ψ hP hΨ y).subset ?_) ((resW_injOn R Ψ).mono fun x hx => hbad x hx.2)
  rintro _ ⟨x, hx, rfl⟩
  have := smul_segre_mem_fibre hP.1 hP.2.1.2.1 Ψ
    (mem_mcPts_of_conePts hle (pt_mem_conePts R x)) (hbad x hx.2).2
  have hy : resProj R Ψ x = y := hx.1
  rw [← hy]
  exact this
end GroundTheory.Heights₂.Heights.HilbertSamuel.ComponentResFibreFinite
