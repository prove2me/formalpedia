-- Prove2me | solution 1 for ReciprocityTheory.AnForm.R.chartOpen_cover
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:01:32.878996+00:00
-- url     : https://prove2.me/submissions/ea4cbb91-2b34-492b-bad3-02282096dd68

import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_MemConePtsIffChartIdeal
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_SegreIdealIsHomogeneous

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.R
open MvPolynomial AlgebraicGeometry
noncomputable section
variable {K : Type} [Fintype K] [Nonempty K] {ι : K → Type} [∀ k, Fintype (ι k)]
namespace ReciprocityTheory.AnForm.R
theorem _root_.solution {P : Ideal (MvPolynomial (Σ k, ι k) ℂ)} (hP : IsMultiHomogIdeal P)
    (x : projX P hP) : ∃ p, x ∈ (chartOpen hP p).1 := by
  classical
  letI := segreGraded hP
  by_contra hcon
  push_neg at hcon
  have hall : ∀ p, segreW P p ∈ x.asHomogeneousIdeal := by
    intro p
    by_contra h
    exact hcon p ((Proj.mem_basicOpen (segreGrading P) (segreW P p) x).mpr h)
  have key : ∀ f ∈ Ideal.span (MvPolynomial.X '' (Set.univ : Set ((k : K) → ι k))),
      Ideal.Quotient.mk (segreIdeal P) f ∈ x.asHomogeneousIdeal.toIdeal := by
    intro f hf
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hf
    · rintro _ ⟨p, -, rfl⟩
      exact hall p
    · simp
    · intro a b _ _ ha hb
      rw [map_add]
      exact add_mem ha hb
    · intro a b _ hb
      rw [smul_eq_mul, map_mul]
      exact Ideal.mul_mem_left _ _ hb
  apply ProjectiveSpectrum.not_irrelevant_le x
  intro a ha
  rw [HomogeneousIdeal.mem_irrelevant_iff, GradedRing.proj_apply] at ha
  change a ∈ x.asHomogeneousIdeal.toIdeal
  rw [x.asHomogeneousIdeal.isHomogeneous.mem_iff]
  intro i
  rcases Nat.eq_zero_or_pos i with hi | hi
  · subst hi
    rw [ha]
    exact zero_mem _
  · obtain ⟨f, hf, hfa⟩ := (DirectSum.decompose (segreGrading P) a i).2
    rw [← hfa]
    apply key
    rw [MvPolynomial.mem_ideal_span_X_image]
    intro m hm
    by_contra hne
    push_neg at hne
    have hm0 : m = 0 := Finsupp.ext fun p => hne p (Set.mem_univ p)
    have hw := ((mem_homogeneousSubmodule i f).mp hf) (MvPolynomial.mem_support_iff.mp hm)
    rw [hm0, map_zero] at hw
    omega
end ReciprocityTheory.AnForm.R
