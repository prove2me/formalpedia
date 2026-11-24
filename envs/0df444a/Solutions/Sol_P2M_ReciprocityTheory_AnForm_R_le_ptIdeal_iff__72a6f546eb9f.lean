-- Prove2me | solution 1 for P2M_ReciprocityTheory_AnForm_R_le_ptIdeal_iff__72a6f546eb9f
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:58:52.676905+00:00
-- url     : https://prove2.me/submissions/1dac9a59-ad43-4217-a855-e6ed3b6f212b

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_JacChart
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_StalkLocA

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
variable {n : ℕ}
namespace ReciprocityTheory.AnForm.R
theorem _root_.solution (K : Ideal (MvPolynomial (Fin n) ℂ)) (p : Fin n → ℂ) :
    K ≤ ptIdeal p ↔ ∀ h ∈ K, eval p h = 0 := by
  simp [ptIdeal, SetLike.le_def, RingHom.mem_ker]
end ReciprocityTheory.AnForm.R
