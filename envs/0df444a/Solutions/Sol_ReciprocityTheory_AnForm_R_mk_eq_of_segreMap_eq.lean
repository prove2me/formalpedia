-- Prove2me | solution 1 for ReciprocityTheory.AnForm.R.mk_eq_of_segreMap_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:00:40.160387+00:00
-- url     : https://prove2.me/submissions/18914c7c-9165-437a-8a5b-b3f4ebb5d265

import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_SegreIdealIsHomogeneous
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ProjDehomA

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
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
namespace ReciprocityTheory.AnForm.R
theorem _root_.solution (P : Ideal (MvPolynomial (Σ k, ι k) ℂ))
    {φ ψ : MvPolynomial ((k : K) → ι k) ℂ} (h : segreMap φ = segreMap ψ) :
    Ideal.Quotient.mk (segreIdeal P) φ = Ideal.Quotient.mk (segreIdeal P) ψ := by
  rw [Ideal.Quotient.eq, segreIdeal, Ideal.mem_comap, map_sub, h, sub_self]
  exact P.zero_mem
end ReciprocityTheory.AnForm.R
