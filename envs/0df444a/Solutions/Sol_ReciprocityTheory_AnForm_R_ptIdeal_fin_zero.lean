-- Prove2me | solution 1 for ReciprocityTheory.AnForm.R.ptIdeal_fin_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:15:31.143179+00:00
-- url     : https://prove2.me/submissions/303da6b7-375a-4a88-b4f1-81dec83bc860

import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_IsOpenAlt
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_IfaceInh

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.R
open MvPolynomial
noncomputable section
namespace ReciprocityTheory.AnForm.R
theorem _root_.solution (p : Fin 0 → ℂ) : ptIdeal p = ⊥ := by
  ext f
  simp only [ptIdeal, RingHom.mem_ker, Ideal.mem_bot]
  constructor
  · intro h
    rw [MvPolynomial.eq_C_of_isEmpty f] at h ⊢
    simpa using h
  · rintro rfl
    simp
end ReciprocityTheory.AnForm.R
