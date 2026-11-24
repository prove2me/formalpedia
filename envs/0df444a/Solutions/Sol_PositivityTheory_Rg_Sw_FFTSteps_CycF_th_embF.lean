-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.FFTSteps.CycF.th_embF
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T14:20:16.777774+00:00
-- url     : https://prove2.me/submissions/be20b802-58cc-4945-8db8-cfcf54cdd717

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_GaussianPlaneIntegrals_CycFFTB
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_GaussianPlaneIntegrals_CycFFTC
import Theorems.Thm_PositivityTheory_Rg_Sw_FFTSteps_CycF_th_X

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.FFTSteps PositivityTheory.Rg.Sw.FFTSteps.CycF
variable {m n : ℕ} (ε : Fin m → Bool)
variable {ε}
namespace PositivityTheory.Rg.Sw.FFTSteps.CycF
theorem _root_.solution (t : PV (Rw ε false) (Fin n) (Fin n)) :
    Th ε (emb ε false t) = map (algebraMap ℂ (PV (Rw ε true) (Fin n) (Fin n))) t := by
  induction t using MvPolynomial.induction_on with
  | C a =>
    simp [emb, Th]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p v hp =>
    have e : eqv ε (jv ε false v) = Sum.inl v := (eqv ε).apply_symm_apply (Sum.inl v)
    have hx : Th ε (emb ε false (X v)) = X v := by
      simp only [emb, rename_X]
      rw [th_X, e]
      exact sumRingEquiv_X_inl ℂ _ _ v
    rw [map_mul, map_mul, hp, hx, map_mul, map_X]
end PositivityTheory.Rg.Sw.FFTSteps.CycF
