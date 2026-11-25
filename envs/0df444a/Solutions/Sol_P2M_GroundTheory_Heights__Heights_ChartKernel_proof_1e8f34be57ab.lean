-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ChartKernel_proof_1e8f34be57ab
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T07:06:03.479951+00:00
-- url     : https://prove2.me/submissions/fa0e0cbd-f3a4-475f-88a6-a08914c58782

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_ImportsBis
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_PChartKernel
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartKernel_map_eq_zero_iff_of_ker_eq_37e7c33f1f68
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartKernel_ker_aeval_chart_24e855cde06c
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartKernel_aeval_genPt_eq_zero_iff_029d581182e3
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartKernel_aeval_genSubst_scale_287273e9ddd5
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartKernel_chartSubst_inr_48e68431394d
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartKernel_chartIncIdeal_le_ker_044de4c79fd0
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartKernel_chartEv_chartSubst_0bbd94b367c7

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial
noncomputable section
open GroundTheory.Heights₂.Heights.ChartKernel
variable {F : Type} [Field F] {n : ℕ}
variable (I : Ideal (MvPolynomial (Fin n) F)) (t : Fin n → F) (e : ℕ)
variable {I t e}
namespace GroundTheory.Heights₂.Heights.ChartKernel
theorem _root_.solution (h₁ : IncidenceGeneric.Statement) (h₂ : ChartIncDomain.Statement) : ChartKernel.Statement := by
  intro F _ n e I t hI ht
  haveI := hI.isPrime
  obtain ⟨-, hX⟩ := h₂ F n e I t hI ht
  have hτ : aeval (genPt I) (linForm t) ≠ 0 := fun h => ht ((aeval_genPt_eq_zero_iff I _).mp h)
  have hc : ∑ j, (aeval (genPt I) (linForm t))⁻¹ *
      algebraMap F (FractionRing (MvPolynomial (Fin n) F ⧸ I)) (t j) * genPt I j = 1 := by
    simp only [mul_assoc, ← Finset.mul_sum]
    rw [show ∑ j, algebraMap F (FractionRing (MvPolynomial (Fin n) F ⧸ I)) (t j) * genPt I j =
      aeval (genPt I) (linForm t) by simp [linForm], inv_mul_cancel₀ hτ]
  ext g
  rw [RingHom.mem_ker, h₁ F n e I _ hc g, aeval_genSubst_scale,
    ← map_eq_zero_iff_of_ker_eq (hX.trans (ker_aeval_chart I hI.isHomog t hτ).symm), ← chartSubst_inr]
  change Ideal.Quotient.mk (chartIncIdeal I t e) (rename Sum.inr g) = 0 ↔ _
  constructor
  · intro h
    rw [Ideal.Quotient.eq_zero_iff_mem] at h
    exact chartIncIdeal_le_ker I t e h
  · intro h
    have := chartEv_chartSubst I t e (rename Sum.inr g)
    rw [h, map_zero] at this
    exact this.symm
end GroundTheory.Heights₂.Heights.ChartKernel
