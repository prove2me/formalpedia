-- Prove2me | solution 1 for P2M_ReciprocityTheory_MultiplicativeHeights_eval_bind__scale_2138dfaeca51
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T09:01:21.119463+00:00
-- url     : https://prove2.me/submissions/4e9e044b-fd0c-4c0d-966a-f8a4a1d641be

import Definitions.Def_ReciprocityTheory_SemistableReduction_SphereTorusA
import Definitions.Def_ReciprocityTheory_SemistableReduction_SphereTorusB

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights
open MeasureTheory
namespace ReciprocityTheory.MultiplicativeHeights
theorem _root_.solution {ι : Type*} (r w : ι → ℂ) (f : MvPolynomial ι ℂ) :
    MvPolynomial.eval w
        (MvPolynomial.bind₁ (fun j => MvPolynomial.C (r j) * MvPolynomial.X j) f) =
      MvPolynomial.eval (fun j => r j * w j) f := by
  induction f using MvPolynomial.induction_on
  · simp
  · simp_all
  · simp_all
end ReciprocityTheory.MultiplicativeHeights
