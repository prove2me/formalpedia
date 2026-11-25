-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.PullbackSections.isUnit_of_jetAug
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T15:52:30.388896+00:00
-- url     : https://prove2.me/submissions/4d266f41-bdaa-4bc4-ac5c-fb7b2b81b64f

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_HolJetC
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_TaylorComp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_HolJetD
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_jetAug_mk

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
variable {K : Type} [Field K] {ι : Type} {m : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.PullbackSections
theorem _root_.solution (a : Jet K ι m) (h : (jetAug : Jet K ι m →ₐ[K] K) a ≠ 0) : IsUnit a := by
  classical
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective a
  rw [jetAug_mk] at h
  set c := MvPolynomial.constantCoeff p with hc

  have hq : p - MvPolynomial.C c ∈ orig K ι := by
    rw [orig, ← Set.image_univ, MvPolynomial.mem_ideal_span_X_image]
    intro mo hmo
    have hmo0 : mo ≠ 0 := by
      intro h0
      subst h0
      rw [MvPolynomial.mem_support_iff, MvPolynomial.coeff_sub, MvPolynomial.coeff_C, if_pos rfl,
        ← MvPolynomial.constantCoeff_eq, ← hc, sub_self] at hmo
      exact hmo rfl
    obtain ⟨i, hi⟩ := Finsupp.ne_iff.1 hmo0
    exact ⟨i, Set.mem_univ _, hi⟩
  have hnil : IsNilpotent (Ideal.Quotient.mk (orig K ι ^ (m + 1)) (p - MvPolynomial.C c)) := by
    refine ⟨m + 1, ?_⟩
    rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.pow_mem_pow hq _
  have hu : IsUnit (Ideal.Quotient.mk (orig K ι ^ (m + 1)) (MvPolynomial.C c)) :=
    (isUnit_iff_ne_zero.2 h).map (Ideal.Quotient.mk (orig K ι ^ (m + 1)) |>.comp MvPolynomial.C)
  have hsplit : Ideal.Quotient.mk (orig K ι ^ (m + 1)) p =
      Ideal.Quotient.mk (orig K ι ^ (m + 1)) (MvPolynomial.C c) +
        Ideal.Quotient.mk (orig K ι ^ (m + 1)) (p - MvPolynomial.C c) := by
    rw [← map_add, add_sub_cancel]
  rw [hsplit]
  exact hnil.isUnit_add_left_of_commute hu (Commute.all _ _)
end ReciprocityTheory.ChartRestriction.G.PullbackSections
