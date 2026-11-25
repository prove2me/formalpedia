-- Prove2me | solution 1 for P2M_UpperTheory_Reformulated_B_CoerciveOfPositiveDefinite_exists_coercive_of_posDef__05ec9a5f4d38
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T09:00:13.315721+00:00
-- url     : https://prove2.me/submissions/380a94c5-2c01-4b16-9d1d-a67669dff0eb

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_CoerciveOfPositiveDefinite

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

namespace UpperTheory.Reformulated.B.CoerciveOfPositiveDefinite.exists_coercive_of_posDef
theorem _root_.solution.{u_1} :
    ∀ {ι : Type u_1} [inst : Fintype ι] {P : Matrix ι ι Complex},
      @Matrix.PosDef ι Complex Complex.instRing Complex.partialOrder Complex.instStarRing P →
        ∃ (c : Real),
          And (@LT.lt Real Real.instLT (@OfNat.ofNat Real (nat_lit 0) (@Zero.toOfNat0 Real Real.instZero)) c)
            (∀ (z : ι → Complex) (j : ι),
              @LE.le Real Real.instLE
                (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) c
                  (@HPow.hPow Real Nat Real (@instHPow Real Nat (@NPow.toPow Real (@Monoid.toNPow Real Real.instMonoid)))
                    (@Norm.norm Complex Complex.instNorm (z j)) (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                (@dotProduct ι Complex inst Complex.instMul Complex.instAddCommMonoid
                    (@Star.star (ι → Complex)
                      (@Pi.instStarForall ι (fun (a : ι) ↦ Complex) fun (i : ι) ↦
                        @InvolutiveStar.toStar Complex
                          (@StarAddMonoid.toInvolutiveStar Complex
                            (@AddCommMonoid.toAddMonoid Complex
                              (@NonUnitalNonAssocSemiring.toAddCommMonoid Complex
                                (@NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring Complex
                                  (@NonUnitalNonAssocCommRing.toNonUnitalNonAssocRing Complex
                                    (@NonUnitalCommRing.toNonUnitalNonAssocCommRing Complex
                                      Complex.instNonUnitalCommRing)))))
                            (@StarRing.toStarAddMonoid Complex
                              (@NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring Complex
                                (@NonUnitalNonAssocCommRing.toNonUnitalNonAssocRing Complex
                                  (@NonUnitalCommRing.toNonUnitalNonAssocCommRing Complex Complex.instNonUnitalCommRing)))
                              Complex.instStarRing)))
                      z)
                    (@Matrix.mulVec ι ι Complex
                      (@NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring Complex
                        (@NonUnitalNonAssocCommRing.toNonUnitalNonAssocRing Complex
                          (@NonUnitalCommRing.toNonUnitalNonAssocCommRing Complex Complex.instNonUnitalCommRing)))
                      inst P z)).re) := by
  intro ι _ P hP
  rcases isEmpty_or_nonempty ι with hι | hι
  · exact ⟨1, one_pos, fun _ j => (hι.false j).elim⟩
  have hcont : Continuous fun z : ι → ℂ => (star z ⬝ᵥ P.mulVec z).re := by
    unfold dotProduct Matrix.mulVec dotProduct
    fun_prop
  have hne : (Metric.sphere (0 : ι → ℂ) 1).Nonempty :=
    NormedSpace.sphere_nonempty.mpr zero_le_one
  obtain ⟨u, hu, hmin⟩ := (isCompact_sphere (0 : ι → ℂ) 1).exists_isMinOn hne hcont.continuousOn
  have hu0 : u ≠ 0 := by
    rintro rfl
    simp at hu
  have hc : 0 < (star u ⬝ᵥ P.mulVec u).re := hP.re_dotProduct_pos hu0
  refine ⟨_, hc, fun z j => ?_⟩
  rcases eq_or_ne z 0 with rfl | hz
  · simp
  have hr : 0 < ‖z‖ := norm_pos_iff.mpr hz
  have hw : (‖z‖⁻¹ • z) ∈ Metric.sphere (0 : ι → ℂ) 1 := by
    rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hr.ne']
  have h1 : (star u ⬝ᵥ P.mulVec u).re ≤ (star (‖z‖⁻¹ • z) ⬝ᵥ P.mulVec (‖z‖⁻¹ • z)).re := hmin hw
  have h2 : (star (‖z‖⁻¹ • z) ⬝ᵥ P.mulVec (‖z‖⁻¹ • z)).re
      = ‖z‖⁻¹ * (‖z‖⁻¹ * (star z ⬝ᵥ P.mulVec z).re) := by
    rw [star_smul, star_trivial, Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul,
      Complex.smul_re, Complex.smul_re, smul_eq_mul, smul_eq_mul]
  have h3 : (star u ⬝ᵥ P.mulVec u).re * ‖z‖ ^ 2 ≤ (star z ⬝ᵥ P.mulVec z).re := by
    rw [h2] at h1
    calc (star u ⬝ᵥ P.mulVec u).re * ‖z‖ ^ 2
        ≤ ‖z‖⁻¹ * (‖z‖⁻¹ * (star z ⬝ᵥ P.mulVec z).re) * ‖z‖ ^ 2 :=
          mul_le_mul_of_nonneg_right h1 (sq_nonneg _)
      _ = (star z ⬝ᵥ P.mulVec z).re := by field_simp
  exact (mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (norm_nonneg _) (norm_le_pi_norm z j) 2) hc.le).trans h3
end UpperTheory.Reformulated.B.CoerciveOfPositiveDefinite.exists_coercive_of_posDef
