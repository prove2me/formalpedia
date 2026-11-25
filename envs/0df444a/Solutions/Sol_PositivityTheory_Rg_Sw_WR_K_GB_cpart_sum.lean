-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.WR.K.GB.cpart_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T11:58:46.986204+00:00
-- url     : https://prove2.me/submissions/8ebfdf1e-52c3-45d6-8e38-c66f9f8ccfd1

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ClsGainBSt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_GBLink
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_K_GB_differentiableAt_of_cdo

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR PositivityTheory.Rg.Sw.WR.K PositivityTheory.Rg.Sw.WR.K.GB
open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ}
variable {F G : Mc n → ℂ} {U : Set (Mc n)}
namespace PositivityTheory.Rg.Sw.WR.K.GB
theorem _root_.solution {ι : Type} (s : Finset ι) (c : ι → ℂ) (f : ι → Mc n → ℂ) (i j : Fin n) (hU : IsOpen U)
    (hf : ∀ t, ContDiffOn ℂ (⊤ : ℕ∞) (f t) U) :
    Set.EqOn (cpart i j (fun x => ∑ t ∈ s, c t * f t x)) (fun x => ∑ t ∈ s, c t * cpart i j (f t) x) U := by
  intro b hb
  have hd : ∀ t ∈ s, DifferentiableAt ℂ (fun x => c t * f t x) b := fun t _ =>
    (differentiableAt_of_cdo hU (hf t) hb).const_mul (c t)
  simp only [cpart]
  have hs : HasFDerivAt (fun x => ∑ t ∈ s, c t * f t x) (∑ t ∈ s, fderiv ℂ (fun x => c t * f t x) b) b :=
    HasFDerivAt.fun_sum (fun t ht => (hd t ht).hasFDerivAt)
  rw [hs.fderiv, _root_.sum_apply]
  refine Finset.sum_congr rfl fun t _ => ?_
  have h1 : HasFDerivAt (fun x => c t * f t x) (c t • fderiv ℂ (f t) b) b :=
    (differentiableAt_of_cdo hU (hf t) hb).hasFDerivAt.const_mul (c t)
  rw [h1.fderiv, ContinuousLinearMap.smul_apply, smul_eq_mul]
end PositivityTheory.Rg.Sw.WR.K.GB
