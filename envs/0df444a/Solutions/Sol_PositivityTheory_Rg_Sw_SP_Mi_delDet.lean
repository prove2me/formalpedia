-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.SP.Mi.delDet
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:05:43.402249+00:00
-- url     : https://prove2.me/submissions/eb37a6c9-c258-46d7-905f-9f64ce98c23f

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MinorFormulas_MinorDefs
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MinorFormulas_MinorB
import Theorems.Thm_PositivityTheory_Rg_Sw_SP_Mi_deriv_det

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
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.SP PositivityTheory.Rg.Sw.SP.Mi
namespace PositivityTheory.Rg.Sw.SP.Mi
theorem _root_.solution : DelDet := by
  intro R _ ρ p q
  rw [deriv_det]
  have h1 : ∀ c, Matrix.updateCol (Xm R ρ) c (fun a => del p q (Xm R ρ a c)) =
      Matrix.updateCol (Xm R ρ) c (fun a => X (q, c) * X (a, p)) := by
    intro c
    congr 1
    funext a
    simp only [Xm, del, mkDerivation_X]
    ring
  simp only [h1]
  have h2 : ∀ c, (Matrix.updateCol (Xm R ρ) c (fun a => X (q, c) * X (a, p))).det =
      X (q, c) * (Matrix.updateCol (Xm R ρ) c (fun a => Xm R ρ a p)).det := by
    intro c
    have : (fun a => (X (q, c) * X (a, p) : Pm R ρ)) = (X (q, c) : Pm R ρ) • fun a => Xm R ρ a p := by
      funext a; simp [Xm]
    rw [this, Matrix.det_updateCol_smul]
  simp only [h2]
  rw [Finset.sum_eq_single p]
  · congr 1
    congr 1
    ext a d
    by_cases hd : d = p
    · subst hd; simp [Matrix.updateCol_self]
    · simp [Matrix.updateCol_ne hd]
  · intro c _ hc
    rw [Matrix.det_zero_of_column_eq (i := c) (j := p) hc, mul_zero]
    · simp [Matrix.updateCol_self, Matrix.updateCol_ne (Ne.symm hc)]
  · intro h; exact absurd (Finset.mem_univ p) h
end PositivityTheory.Rg.Sw.SP.Mi
