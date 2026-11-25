-- Prove2me | solution 1 for ReciprocityTheory.AnForm.R.IrreducibleComponentPreimages.exists_unit_mul_mem_of_germ_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:41:30.999931+00:00
-- url     : https://prove2.me/submissions/674a0d7c-98eb-43a7-8ffc-73d2f3470ef2

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
variable {W : Scheme.{0}}
namespace ReciprocityTheory.AnForm.R.IrreducibleComponentPreimages
theorem _root_.solution {V : W.Opens} (hV : IsAffineOpen V) (x : W) (hx : x ∈ V)
    (I : Ideal Γ(W, V)) {t : Γ(W, V)} (ht : W.presheaf.germ V x hx t ∈ I.map (W.presheaf.germ V x hx).hom) :
    ∃ d : Γ(W, V), IsUnit (W.presheaf.germ V x hx d) ∧ d * t ∈ I := by
  letI := TopCat.Presheaf.algebra_section_stalk W.presheaf (⟨x, hx⟩ : V)
  haveI := hV.isLocalization_stalk ⟨x, hx⟩
  have ht' : algebraMap Γ(W, V) (W.presheaf.stalk x) t ∈
      Ideal.map (algebraMap Γ(W, V) (W.presheaf.stalk x)) I := ht
  obtain ⟨⟨⟨a, ha⟩, ⟨s, hs⟩⟩, h⟩ := (IsLocalization.mem_map_algebraMap_iff
    (hV.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl (W.presheaf.stalk x)).1 ht'
  simp only at h
  rw [← map_mul] at h
  obtain ⟨⟨c, hc⟩, hc'⟩ := (IsLocalization.eq_iff_exists
    (hV.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl (W.presheaf.stalk x)).1 h
  simp only at hc'
  refine ⟨c * s, ?_, ?_⟩
  · have hu : IsUnit (algebraMap Γ(W, V) (W.presheaf.stalk x) (c * s)) :=
      (IsLocalization.AtPrime.isUnit_to_map_iff (W.presheaf.stalk x) _ (c * s)).2
        ((hV.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl.mul_mem hc hs)
    exact hu
  · have h3 : c * s * t = c * a := by rw [← hc']; ring
    rw [h3]
    exact Ideal.mul_mem_left _ _ ha
end ReciprocityTheory.AnForm.R.IrreducibleComponentPreimages
