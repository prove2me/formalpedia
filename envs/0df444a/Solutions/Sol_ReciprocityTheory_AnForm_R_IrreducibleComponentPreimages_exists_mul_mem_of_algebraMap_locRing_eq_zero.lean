-- Prove2me | solution 1 for ReciprocityTheory.AnForm.R.IrreducibleComponentPreimages.exists_mul_mem_of_algebraMap_locRing_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:46:40.406669+00:00
-- url     : https://prove2.me/submissions/e0ad080b-135c-4a15-bc51-f05be265408f

import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ClosureFromSpecMemCompsH
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_StalkLoc
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_IsOpenAlt
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ExistsMulMemOfAlgebraMapLocRingEqZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.R ReciprocityTheory.AnForm.R.IrreducibleComponentPreimages
open AlgebraicGeometry CategoryTheory MvPolynomial TopologicalSpace
noncomputable section
variable {m : ℕ}
namespace ReciprocityTheory.AnForm.R.IrreducibleComponentPreimages
theorem _root_.solution (K : Ideal (MvPolynomial (Fin m) ℂ))
    (p : Fin m → ℂ) {t : MvPolynomial (Fin m) ℂ} (ht : algebraMap _ (locRing K p) t = 0) :
    ∃ s, eval p s ≠ 0 ∧ s * t ∈ K := by
  change Ideal.Quotient.mk (Ideal.map (algebraMap (MvPolynomial (Fin m) ℂ) (locPt p)) K)
    (algebraMap _ (locPt p) t) = 0 at ht
  rw [Ideal.Quotient.eq_zero_iff_mem] at ht
  obtain ⟨⟨⟨a, ha⟩, ⟨s, hs⟩⟩, h⟩ :=
    (IsLocalization.mem_map_algebraMap_iff (ptIdeal p).primeCompl (locPt p)).1 ht
  simp only at h
  rw [← map_mul] at h
  obtain ⟨⟨c, hc⟩, hc'⟩ := (IsLocalization.eq_iff_exists (ptIdeal p).primeCompl (locPt p)).1 h
  simp only at hc'
  refine ⟨c * s, ?_, ?_⟩
  · have h1 : eval p c ≠ 0 := fun h0 => Ideal.mem_primeCompl_iff.1 hc ((RingHom.mem_ker).2 h0)
    have h2 : eval p s ≠ 0 := fun h0 => Ideal.mem_primeCompl_iff.1 hs ((RingHom.mem_ker).2 h0)
    rw [map_mul]
    exact mul_ne_zero h1 h2
  · have h3 : c * s * t = c * a := by rw [← hc']; ring
    rw [h3]
    exact Ideal.mul_mem_left _ _ ha
end ReciprocityTheory.AnForm.R.IrreducibleComponentPreimages
