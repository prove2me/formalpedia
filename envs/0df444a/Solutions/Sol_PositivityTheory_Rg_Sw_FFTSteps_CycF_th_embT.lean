-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.FFTSteps.CycF.th_embT
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T14:02:41.868799+00:00
-- url     : https://prove2.me/submissions/66dd3663-7cb1-44e0-ac19-7e568a11ce3f

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
theorem _root_.solution (c : PV (Rw ε true) (Fin n) (Fin n)) : Th ε (emb ε true c) = C c := by
  induction c using MvPolynomial.induction_on with
  | C a =>
    simp [emb, Th]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p v hp =>
    have e : eqv ε (jv ε true v) = Sum.inr v := (eqv ε).apply_symm_apply (Sum.inr v)
    have hx : Th ε (emb ε true (X v)) = C (X v) := by
      simp only [emb, rename_X]
      rw [th_X, e]
      exact sumRingEquiv_X_inr ℂ _ _ v
    rw [map_mul, map_mul, hp, hx, C_mul]
end PositivityTheory.Rg.Sw.FFTSteps.CycF
