-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FieldNumbers_ConeVarUnit_proof_10ecc2f1f6fa
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T04:54:38.555831+00:00
-- url     : https://prove2.me/submissions/7ef46dec-eb63-4cab-bab8-3f6948b2bbc6

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsConeVarUnit
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsConeVarNumerator
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsDegZeroLocQuot
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PConeVarUnit
import Theorems.Thm_GroundTheory_Arith_Toric_LowerBound_mul
import Theorems.Thm_GroundTheory_Arith_Toric_LowerBound_pow


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
namespace ConeVarUnit
theorem _root_.solution (hDZ : DegZeroLocQuot.Statement.{u})
    (hNum : ConeVarNumerator.Statement.{u}) : ConeVarUnit.Statement.{u} := by
  intro F _ K _ _ ι _ P hP W hW hPW v hv
  have := hP.isPrime
  have := hW.isPrime
  intro p e he
  obtain ⟨b, g, h, hg, hgW, hh, hcoeff, himg⟩ := hNum F K ι P hP W hW hPW v hv p
  have hne : ∀ x : MRing ι F, x ∉ W →
      algebraMap (MRing ι F ⧸ P) (FractionRing (MRing ι F ⧸ P)) (Ideal.Quotient.mk P x) ≠ 0 :=
    fun x hx h0 => hx (hPW ((Ideal.Quotient.eq_zero_iff_mem).mp
      ((IsFractionRing.to_map_eq_zero_iff).mp h0)))

  have heW : h e ∉ W := by
    intro heW
    obtain ⟨y, hy⟩ := he.exists_right_inv
    obtain ⟨b', f', g', -, -, -, hg'W, hy'⟩ :=
      hDZ F K ι P {W} (fun W' hW' => (Set.mem_singleton_iff.mp hW') ▸ hW.isPrime) y y.2
    have h1 : ((p.coeff e : degZeroLoc P {W}) : FractionRing (MRing ι F ⧸ P)) * y = 1 := by
      rw [← Subalgebra.coe_mul, hy, Subalgebra.coe_one]
    rw [hcoeff e, hy', div_mul_div_comm, div_eq_one_iff_eq (mul_ne_zero (hne g hgW)
      (hne g' (hg'W W rfl))), ← map_mul, ← map_mul, ← map_mul, ← map_mul] at h1
    have h2 := Ideal.Quotient.eq.mp (IsFractionRing.injective _ _ h1)
    have h3 : g * g' ∈ W := by
      have := W.sub_mem (W.mul_mem_right f' heW) (hPW h2)
      rwa [sub_sub_cancel] at this
    rcases hW.isPrime.mem_or_mem h3 with h4 | h4
    exacts [hgW h4, hg'W W rfl h4]

  have hu : ∀ d : K →₀ ℕ, IsMultiHomog (∏ k, (X ⟨k, v k⟩ : MRing ι F) ^ d k) (⇑d) := by
    intro d
    have := IsWeightedHomogeneous.prod Finset.univ (fun k => (X ⟨k, v k⟩ : MRing ι F) ^ d k)
      (fun k => d k • blockWeight ι ⟨k, v k⟩) (fun k _ => (isWeightedHomogeneous_X F _ _).pow _)
    have hdeg : (∑ k, d k • blockWeight ι ⟨k, v k⟩) = ⇑d := by
      ext j
      simp [blockWeight, Finset.sum_apply, Pi.single_apply]
    rw [hdeg] at this
    exact this
  have huW : ∀ d : K →₀ ℕ, (∏ k, (X ⟨k, v k⟩ : MRing ι F) ^ d k) ∉ W := by
    intro d hd
    obtain ⟨k, -, hk⟩ := Ideal.IsPrime.prod_mem_iff.mp hd
    exact hv k (hW.isPrime.mem_of_pow_mem _ hk)

  set N := ∑ d ∈ p.support, h d * ∏ k, (X ⟨k, v k⟩ : MRing ι F) ^ d k with hNdef
  have hcomp : weightedHomogeneousComponent (blockWeight ι) (b + ⇑e) N =
      h e * ∏ k, (X ⟨k, v k⟩ : MRing ι F) ^ e k := by
    rw [hNdef, map_sum, Finset.sum_eq_single e]
    · exact ((hh e).mul (hu e)).weightedHomogeneousComponent_same
    · intro d _ hde
      refine weightedHomogeneousComponent_eq_zero' _ _ fun c hc hw => hde ?_
      rw [((hh d).mul (hu d)) (mem_support_iff.mp hc)] at hw
      exact DFunLike.coe_injective (add_left_cancel hw)
    · intro hes
      exact absurd (notMem_support_iff.mp hes) he.ne_zero
  have hNW : N ∉ W := fun hN => by
    have := hW.multiHomog N hN (b + ⇑e)
    rw [hcomp] at this
    rcases hW.isPrime.mem_or_mem this with h4 | h4
    exacts [heW h4, huW e h4]

  have hunit : ∀ x : MRing ι F, x ∉ W →
      IsUnit (algebraMap (MRing ι F ⧸ P) (coneLocal P W hPW) (Ideal.Quotient.mk P x)) :=
    fun x hx => IsLocalization.map_units (coneLocal P W hPW)
      (⟨_, Submonoid.mem_map_of_mem _ hx⟩ : W.primeCompl.map (Ideal.Quotient.mk P))
  have heq : coneVarMap P W hPW v p *
      algebraMap (MRing ι F ⧸ P) (coneLocal P W hPW) (Ideal.Quotient.mk P g) =
      algebraMap (MRing ι F ⧸ P) (coneLocal P W hPW) (Ideal.Quotient.mk P N) := by
    apply Subtype.ext
    rw [Subalgebra.coe_mul, Subalgebra.coe_algebraMap, Subalgebra.coe_algebraMap, himg,
      div_mul_cancel₀ _ (hne g hgW)]
  exact isUnit_of_mul_isUnit_left (heq ▸ hunit N hNW)
end ConeVarUnit
end GroundTheory.Heights₂.Heights.FieldNumbers
