-- Prove2me | solution 1 for ReciprocityTheory.AnForm.R.isLocalization_locRing
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:48:48.286969+00:00
-- url     : https://prove2.me/submissions/628c2891-03f3-4673-a457-d42b3dd7682d

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_JacChart
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_StalkLocA
import Theorems.Thm_ReciprocityTheory_AnForm_R_mk_mem_ptQ

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
theorem _root_.solution {K : Ideal (MvPolynomial (Fin n) ℂ)} {p : Fin n → ℂ}
    (hK : K ≤ ptIdeal p) :
    letI := ptQ_isPrime hK; IsLocalization.AtPrime (locRing K p) (ptQ K p) := by
  letI := ptQ_isPrime hK
  have hM : Algebra.algebraMapSubmonoid (MvPolynomial (Fin n) ℂ ⧸ K) (ptIdeal p).primeCompl =
      (ptQ K p).primeCompl := by
    ext x
    constructor
    · rintro ⟨f, hf, rfl⟩
      rw [Ideal.mem_primeCompl_iff, Ideal.Quotient.algebraMap_eq, mk_mem_ptQ hK]
      exact hf
    · intro hx
      obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective x
      rw [Ideal.mem_primeCompl_iff, mk_mem_ptQ hK] at hx
      exact ⟨f, hx, rfl⟩
  have h := IsLocalization.instQuotientIdealAlgebraMapSubmonoidMapRingHomAlgebraMap
    (ptIdeal p).primeCompl (locPt p) K
  rw [hM] at h
  exact h
end ReciprocityTheory.AnForm.R
