-- Prove2me | solution 1 for ReciprocityTheory.AnForm.R.mk_mem_ptQ
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:36:27.806533+00:00
-- url     : https://prove2.me/submissions/5422e20b-02f4-4245-a3fc-655452781c89

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
theorem _root_.solution {K : Ideal (MvPolynomial (Fin n) ℂ)} {p : Fin n → ℂ} (hK : K ≤ ptIdeal p)
    (f : MvPolynomial (Fin n) ℂ) : Ideal.Quotient.mk K f ∈ ptQ K p ↔ f ∈ ptIdeal p := by
  exact Ideal.mem_quotient_iff_mem hK
end ReciprocityTheory.AnForm.R
