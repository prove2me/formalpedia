-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.WR.G.GI.integP
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:14:43.370676+00:00
-- url     : https://prove2.me/submissions/65532609-e5f9-482b-a8b6-261e854bd6fe

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_GaussS
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_NormMono
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_G_GI_prodG
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_G_GI_continuous_evX
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_G_GI_continuous_gs
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_G_GI_norm_gs
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_G_GI_norm_mono

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Matrix MvPolynomial
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR PositivityTheory.Rg.Sw.WR.G PositivityTheory.Rg.Sw.WR.G.GI
open PositivityTheory.Rg.Sw
namespace PositivityTheory.Rg.Sw.WR.G.GI
theorem _root_.solution : IntegP := by
  intro m n c hc P
  have key : ∀ d : (Fin m × Fin n × Bool) →₀ ℕ,
      Integrable fun x : Fin m → Fin n → ℂ => evX (monomial d 1) x * gs c x := by
    intro d
    refine (prodG m n c hc (fun a i => d (a, i, false) + d (a, i, true))).mono'
      ((continuous_evX _).mul (continuous_gs c)).aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => le_of_eq ?_)
    rw [norm_mul, norm_mono, norm_gs, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun a _ => ?_
    rw [← Finset.prod_mul_distrib]
  have hP : (fun x => evX P x * gs c x) =
      fun x => ∑ d ∈ P.support, coeff d P * (evX (monomial d 1) x * gs c x) := by
    funext x
    simp only [evX]
    rw [MvPolynomial.eval_eq, Finset.sum_mul]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [MvPolynomial.eval_monomial, one_mul, Finsupp.prod, mul_assoc]
  rw [hP]
  exact integrable_finsetSum _ fun d _ => (key d).const_mul _
end PositivityTheory.Rg.Sw.WR.G.GI
