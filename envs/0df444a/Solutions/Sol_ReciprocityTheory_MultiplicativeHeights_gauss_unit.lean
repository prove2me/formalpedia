-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.gauss_unit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T15:13:20.28277+00:00
-- url     : https://prove2.me/submissions/25699394-3f41-49d5-83d5-e2a5c7fdc572

import Mathlib
import Definitions.Def_ReciprocityTheory_SemistableReduction_ComapInclusionIsLocalHom
import Definitions.Def_ReciprocityTheory_SemistableReduction_GaussValExists
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_gaussRed_coeff
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_gaussRed_eval
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace ReciprocityTheory.MultiplicativeHeights
open MvPolynomial
private theorem residue_ne_zero_of_isUnit {R : Type*} [CommRing R] [IsLocalRing R] {x : R}
    (hx : IsUnit x) : IsLocalRing.residue R x ≠ 0 := by
  intro h
  have hm : x ∈ IsLocalRing.maximalIdeal R := by
    exact (IsLocalRing.residue_eq_zero_iff x).1 h
  exact mem_nonunits_iff.1 ((IsLocalRing.mem_maximalIdeal x).1 hm) hx
private theorem isUnit_of_residue_ne_zero' {R : Type*} [CommRing R] [IsLocalRing R] {x : R}
    (h : IsLocalRing.residue R x ≠ 0) : IsUnit x := by
  by_contra hx
  apply h
  have hm : x ∈ IsLocalRing.maximalIdeal R :=
    (IsLocalRing.mem_maximalIdeal x).2 (mem_nonunits_iff.2 hx)
  exact (IsLocalRing.residue_eq_zero_iff x).2 hm
private theorem eq_zero_of_aeval_eq_zero_of_algebraicIndependent {R A ι : Type*} [CommRing R] [CommRing A] [Algebra R A]
    {x : ι → A} (hx : AlgebraicIndependent R x) {q : MvPolynomial ι R}
    (h : MvPolynomial.aeval x q = 0) : q = 0 := by
  exact (algebraicIndependent_iff.1 hx) q h
end ReciprocityTheory.MultiplicativeHeights
end

set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights
open MvPolynomial
namespace ReciprocityTheory.MultiplicativeHeights
theorem _root_.solution {Ω U : Type} [Field Ω] [Field U] [Algebra Ω U] {σ : Type}
    (t : σ → U) (V : ValuationSubring U) (ht : ∀ s, t s ∈ V)
    (hind : letI := residueAlgebra V (algebraMap Ω U)
      AlgebraicIndependent (IsLocalRing.ResidueField (V.comap (algebraMap Ω U)))
        (fun s => IsLocalRing.residue V ⟨t s, ht s⟩))
    (p : MvPolynomial σ Ω) (hc : ∀ α, p.coeff α ∈ V.comap (algebraMap Ω U))
    (α₀ : σ →₀ ℕ) (hα₀ : (p.coeff α₀)⁻¹ ∈ V.comap (algebraMap Ω U)) (h0 : p.coeff α₀ ≠ 0) :
    V.valuation (aeval t p) = 1 := by
  letI := residueAlgebra V (algebraMap Ω U)
  have hind' : AlgebraicIndependent (IsLocalRing.ResidueField (V.comap (algebraMap Ω U)))
      (fun s => IsLocalRing.residue V ⟨t s, ht s⟩) := hind
  obtain ⟨hmem, hres⟩ := gaussRed_eval t V ht p hc
  have hu0 : IsUnit (⟨p.coeff α₀, hc α₀⟩ : V.comap (algebraMap Ω U)) :=
    isUnit_iff_exists_inv.mpr ⟨⟨(p.coeff α₀)⁻¹, hα₀⟩, Subtype.ext (mul_inv_cancel₀ h0)⟩
  have hq : gaussRed V p hc ≠ 0 := by
    intro h
    have h1 := gaussRed_coeff V p hc α₀
    rw [h, MvPolynomial.coeff_zero] at h1
    exact residue_ne_zero_of_isUnit hu0 h1.symm
  have hne : IsLocalRing.residue V ⟨aeval t p, hmem⟩ ≠ 0 := by
    rw [hres]
    intro h
    exact hq (eq_zero_of_aeval_eq_zero_of_algebraicIndependent hind' h)
  have hunit := isUnit_of_residue_ne_zero' hne
  exact (V.valuation_eq_one_iff _).1 hunit
end ReciprocityTheory.MultiplicativeHeights
