-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.PullbackSections.isLocalHom_jetTan
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T16:22:29.238867+00:00
-- url     : https://prove2.me/submissions/b4a12a84-ef90-4eb2-b691-3befc1726e18

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_HolJetE
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_HolJetF
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_aeval_tan

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.PullbackSections
open AlgebraicGeometry CategoryTheory Opposite Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.TB.ValAt
open scoped ContDiff
variable {Y : Scheme.{0}}
variable {g : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.PullbackSections
theorem _root_.solution (ℓ : Fin 1 × Fin g) :
    IsLocalHom ((jetTan ℓ : Jet ℂ (Fin 1 × Fin g) (0 + 1) →ₐ[ℂ] DualNumber ℂ) :
      Jet ℂ (Fin 1 × Fin g) (0 + 1) →+* DualNumber ℂ) := by
  constructor
  intro x hx
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
  have hx' : IsUnit (MvPolynomial.aeval
      (fun i => if i = ℓ then (DualNumber.eps : DualNumber ℂ) else 0) p) := hx
  rw [aeval_tan] at hx'
  have hc : MvPolynomial.constantCoeff p ≠ 0 := by
    intro h0
    obtain ⟨u, hu⟩ := hx'
    have := congrArg TrivSqZeroExt.fst u.mul_inv
    rw [TrivSqZeroExt.fst_mul, hu] at this
    simp [h0] at this
  have hq : p - MvPolynomial.C (MvPolynomial.constantCoeff p) ∈ orig ℂ (Fin 1 × Fin g) := by
    unfold orig
    rw [← Set.image_univ, MvPolynomial.mem_ideal_span_X_image]
    intro m hm
    have hm0 : m ≠ 0 := by
      rintro rfl
      rw [MvPolynomial.mem_support_iff] at hm
      apply hm
      rw [MvPolynomial.coeff_sub, MvPolynomial.coeff_C, if_pos rfl]
      exact sub_self _
    obtain ⟨i, hi⟩ : ∃ i, m i ≠ 0 := by
      by_contra hne
      push_neg at hne
      exact hm0 (Finsupp.ext hne)
    exact ⟨i, Set.mem_univ _, hi⟩
  have hnil : IsNilpotent (Ideal.Quotient.mk (orig ℂ (Fin 1 × Fin g) ^ (0 + 1 + 1))
      (p - MvPolynomial.C (MvPolynomial.constantCoeff p))) := by
    refine ⟨0 + 1 + 1, ?_⟩
    rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.pow_mem_pow hq _
  have hu : IsUnit (Ideal.Quotient.mk (orig ℂ (Fin 1 × Fin g) ^ (0 + 1 + 1))
      (MvPolynomial.C (MvPolynomial.constantCoeff p))) :=
    ((isUnit_iff_ne_zero.2 hc).map MvPolynomial.C).map _
  have := hnil.isUnit_add_left_of_commute hu (Commute.all _ _)
  simpa using this
end ReciprocityTheory.ChartRestriction.G.PullbackSections
