-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L1.rootPoly_inter_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T14:20:29.234556+00:00
-- url     : https://prove2.me/submissions/f5465670-d17f-49fc-8a5d-8ebcd88594b1

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_RedDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_RedGcd
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_L1_rootPoly_monic__823c582ccd94
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_rootPoly_inter_mul_sdiff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_rootPoly_isCoprime_of_disjoint
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_exists_poly_map_subfield
import Theorems.Thm_Formalism_ELL_FormalGroupQuadraticJets_hb


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical
open Formalism.L2.Th1.CM Formalism.L2.Th1.F Polynomial
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.L1
namespace ReciprocityTheory.ChartRestriction.L1
theorem _root_.solution {E : Type} [Field E] (k : Subfield E) (xs ys : Finset E)
    (hx : ∀ i, (rootPoly xs).coeff i ∈ k) (hy : ∀ i, (rootPoly ys).coeff i ∈ k) :
    ∀ i, (rootPoly (xs ∩ ys)).coeff i ∈ k := by
  obtain ⟨p, hp⟩ := exists_poly_map_subfield k _ hx
  obtain ⟨q, hq⟩ := exists_poly_map_subfield k _ hy
  set R := rootPoly (xs ∩ ys) with hR
  set g0 := EuclideanDomain.gcd p q with hg0
  set g := g0.map k.subtype with hg
  have hgP : g ∣ rootPoly xs := by
    rw [← hp]; exact Polynomial.map_dvd _ (EuclideanDomain.gcd_dvd_left p q)
  have hgQ : g ∣ rootPoly ys := by
    rw [← hq]; exact Polynomial.map_dvd _ (EuclideanDomain.gcd_dvd_right p q)
  have hA := rootPoly_inter_mul_sdiff xs ys
  have hB := rootPoly_inter_mul_sdiff ys xs
  rw [Finset.inter_comm ys xs] at hB
  have hdisj : Disjoint (xs \ ys) (ys \ xs) := by
    rw [Finset.disjoint_left]
    intro a ha hb
    exact (Finset.mem_sdiff.1 hb).2 (Finset.mem_sdiff.1 ha).1
  obtain ⟨u, v, huv⟩ := rootPoly_isCoprime_of_disjoint _ _ hdisj
  have hgR : g ∣ R := by
    have : R = u * rootPoly xs + v * rootPoly ys := by
      rw [← hA, ← hB]
      linear_combination (-R) * huv
    rw [this]
    exact dvd_add (hgP.mul_left _) (hgQ.mul_left _)
  have hRg : R ∣ g := by
    have e : g = EuclideanDomain.gcd (rootPoly xs) (rootPoly ys) := by
      rw [← hp, ← hq, Polynomial.gcd_map]
    rw [e]
    exact EuclideanDomain.dvd_gcd ⟨_, hA.symm⟩ ⟨_, hB.symm⟩
  have hRm : R.Monic := rootPoly_monic' _
  have hg0' : g ≠ 0 := fun e => hRm.ne_zero (by simpa [e] using hgR)
  have hg00 : g0 ≠ 0 := fun e => hg0' (by rw [hg, e, Polynomial.map_zero])
  have hmon : (g0 * C g0.leadingCoeff⁻¹).Monic := monic_mul_leadingCoeff_inv hg00
  have hmon' : ((g0 * C g0.leadingCoeff⁻¹).map k.subtype).Monic := hmon.map _
  have hassoc : Associated ((g0 * C g0.leadingCoeff⁻¹).map k.subtype) R := by
    have h1 : Associated g R := associated_of_dvd_dvd hgR hRg
    refine Associated.trans ?_ h1
    rw [Polynomial.map_mul, Polynomial.map_C]
    refine (associated_mul_unit_left g _ ?_).symm.symm
    refine Polynomial.isUnit_C.2 (IsUnit.mk0 _ ?_)
    simpa using hg00
  have heq := eq_of_monic_of_associated hmon' hRm hassoc
  intro i
  rw [← heq, Polynomial.coeff_map]
  exact (((g0 * C g0.leadingCoeff⁻¹).coeff i)).2
end ReciprocityTheory.ChartRestriction.L1
