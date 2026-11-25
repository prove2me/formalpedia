-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FieldNumbers_RelevantPrimeDimGe_proof_f3a1f51a2659
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T06:28:01.816526+00:00
-- url     : https://prove2.me/submissions/3f026a2e-0d2d-4dfb-8bc0-6b0d915e3db8

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsDegreeBound
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_JacobianSmoothness_RingKrullDimLeRingKrullDimQuotientAddOne
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PRelevantPrimeDimGe
import Theorems.Thm_GroundTheory_Arith_Abelian_Jacobian_ringKrullDim_eq_trdeg
import Theorems.Thm_GroundTheory_Arith_Toric_LowerBound_sum


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FieldNumbers
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR
noncomputable section
universe u
namespace GroundTheory.Heights₂.Heights.FieldNumbers
namespace RelevantPrimeDimGe
theorem _root_.solution : RelevantPrimeDimGe.Statement.{u} := by
  intro F _ K _ _ ι _ P hP
  have := hP.isPrime
  classical
  choose i hi using hP.relevant
  let j : K → (Σ k, ι k) := fun k => ⟨k, i k⟩
  let x : K → MRing ι F ⧸ P := fun k => Ideal.Quotient.mk P (X (j k))
  have key : ∀ p : MvPolynomial K F, aeval x p = Ideal.Quotient.mk P (rename j p) := by
    intro p
    induction p using MvPolynomial.induction_on with
    | C a =>
      simp only [aeval_C, rename_C]
      rfl
    | add p q hp hq => simp [hp, hq]
    | mul_X p k hp => simp [hp, x]
  have hw : ∀ β : K →₀ ℕ, Finsupp.weight (blockWeight ι) (Finsupp.mapDomain j β) = ⇑β := by
    intro β
    rw [Finsupp.weight_apply, Finsupp.sum_mapDomain_index (by simp) (by simp [add_smul])]
    funext k'
    simp [Finsupp.sum, Finset.sum_apply, blockWeight, j, Pi.single_apply]
    exact fun h => h.symm
  have hind : AlgebraicIndependent F x := by
    rw [algebraicIndependent_iff]
    intro G hG
    rw [key] at hG
    have hmem : rename j G ∈ P := Ideal.Quotient.eq_zero_iff_mem.mp hG
    ext α
    rw [coeff_zero]
    have hcomp := hP.multiHomog _ hmem ⇑α
    have hsum : rename j G = ∑ β ∈ G.support, monomial (Finsupp.mapDomain j β) (coeff β G) := by
      calc rename j G = rename j (∑ β ∈ G.support, monomial β (coeff β G)) := by
            congr 1; exact G.as_sum
        _ = _ := by rw [map_sum]; simp only [rename_monomial]
    have hc : weightedHomogeneousComponent (blockWeight ι) (⇑α) (rename j G) =
        rename j (monomial α (coeff α G)) := by
      rw [hsum, map_sum, rename_monomial]
      rw [Finset.sum_eq_single α]
      · rw [weightedHomogeneousComponent_of_mem (isWeightedHomogeneous_monomial _ _ _ (hw α)),
          if_pos rfl]
      · intro β _ hβ
        rw [weightedHomogeneousComponent_of_mem (isWeightedHomogeneous_monomial _ _ _ (hw β)),
          if_neg]
        exact fun h => hβ (DFunLike.coe_injective h).symm
      · intro hα
        rw [notMem_support_iff.mp hα]
        simp
    rw [hc, ← Ideal.Quotient.eq_zero_iff_mem, ← key, aeval_monomial] at hcomp
    rcases mul_eq_zero.mp hcomp with h | h
    · exact (map_eq_zero_iff _ (algebraMap F _).injective).mp h
    · exfalso
      rw [Finsupp.prod] at h
      obtain ⟨k, -, hk⟩ := Finset.prod_eq_zero_iff.mp h
      exact hi k (Ideal.Quotient.eq_zero_iff_mem.mp (pow_eq_zero_iff'.mp hk).1)
  have h1 := hind.lift_cardinalMk_le_trdeg
  simp only [Cardinal.mk_fintype, Cardinal.lift_natCast, Cardinal.lift_uzero] at h1
  rw [GroundTheory.Arith.Abelian.Jacobian.ringKrullDim_eq_trdeg F]
  have h2 : (Fintype.card K : ℕ∞) ≤ (Algebra.trdeg F (MRing ι F ⧸ P)).toENat :=
    Cardinal.natCast_le_toENat.mpr h1
  exact_mod_cast h2
end RelevantPrimeDimGe
end GroundTheory.Heights₂.Heights.FieldNumbers
