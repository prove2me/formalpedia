-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Vertical_GenSecDomain_secIdeal_le_ker_859e8674bf60
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T08:36:37.77524+00:00
-- url     : https://prove2.me/submissions/e6153fd0-f527-4233-882e-299c8d51d3db

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_StatementsChowNorm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_ComapMaximalIdealParDVR
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_StatementsSectionOrder
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_PGenSecDomain
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Vertical_GenSecDomain_eval__mul_of_isHomogeneous_9f11237f1c08
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Vertical_GenSecDomain___X_inl_2c246884c5aa
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Vertical_GenSecDomain___X_inr_ff9d3e0fb1c3
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Vertical_GenSecDomain___C_7487438d7ef4
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Vertical_GenSecDomain_eval__genPt_36e565ff3fc1

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Vertical
open MvPolynomial
noncomputable section
open GroundTheory.Heights₂.Heights.Vertical.GenSecDomain
variable {k : Type} [Field k] {n : ℕ}
variable (Q : Ideal (MvPolynomial (Fin n) k)) [Q.IsPrime] (e : ℕ)
namespace GroundTheory.Heights₂.Heights.Vertical.GenSecDomain
theorem _root_.solution (hQh : IsHomogIdeal Q) (c : Fin n → Fn Q) (hc : ∑ j, c j * genPt Q j = 1)
    (hs : sT Q e ≠ 0) :
    secIdeal (Q.map (MvPolynomial.map (C : k →+* MvPolynomial (Par e n) k)))
      (X : Par e n → MvPolynomial (Par e n) k) ≤ RingHom.ker (Ψt Q e c) := by
  have hs' : algebraMap (Tgt Q e) (Om Q e) (sT Q e) ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective (Tgt Q e) (Om Q e))).mpr hs
  refine sup_le (sup_le ?_ ?_) ?_
  · rw [Ideal.map_le_iff_le_comap]
    intro q hq
    rw [Ideal.mem_comap, RingHom.mem_ker, Ψt, coe_eval₂Hom, eval₂_map]
    have hcoef : ((algebraMap (Tgt Q e) (Om Q e)).comp (ρ Q e c)).comp C =
        (ι Q e).comp (algebraMap k (Fn Q)) := by
      ext a
      simp [ι, ρ_C]
    rw [hcoef, ← sum_homogeneousComponent q, eval₂_sum]
    refine Finset.sum_eq_zero fun d _ => ?_
    have hx : xs Q e = fun l => ι Q e (genPt Q l) * (algebraMap _ (Om Q e) (sT Q e))⁻¹ := rfl
    rw [hx, eval₂_mul_of_isHomogeneous _ _ _ (homogeneousComponent_isHomogeneous d q)]
    have h2 : eval₂ ((ι Q e).comp (algebraMap k (Fn Q))) (fun l => ι Q e (genPt Q l))
        (homogeneousComponent d q) =
        ι Q e (eval₂ (algebraMap k (Fn Q)) (genPt Q) (homogeneousComponent d q)) :=
      (eval₂_comp_left _ _ _ _).symm
    rw [h2, eval₂_genPt, Ideal.Quotient.eq_zero_iff_mem.mpr (hQh q hq d), map_zero, map_zero, mul_zero]
  · rw [Ideal.span_le, Set.range_subset_iff]
    intro i
    have h1 : ∑ l, C (c l) * C (genPt Q l) = (1 : MvPolynomial (Fin e × Fin n) (Fn Q)) := by
      rw [← C_1, ← hc, map_sum]
      simp_rw [C_mul]
    have key : ∑ l, genSubst (genPt Q) c (i, l) * C (genPt Q l) = 0 := by
      simp only [genSubst]
      rw [show ∑ l, (X (i, l) - (∑ m, X (i, m) * C (genPt Q m)) * C (c l)) * C (genPt Q l) =
          ∑ l, X (i, l) * C (genPt Q l) - (∑ m, X (i, m) * C (genPt Q m)) * ∑ l, C (c l) * C (genPt Q l) by
        rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun l _ => by ring]
      rw [h1, mul_one, sub_self]
    rw [SetLike.mem_coe, RingHom.mem_ker, secForm, linForm, map_sum]
    simp only [map_mul, Ψt, coe_eval₂Hom, eval₂_C, eval₂_X, RingHom.comp_apply, ρ_X_inl, xs, ι]
    simp_rw [← mul_assoc, ← map_mul]
    rw [← Finset.sum_mul, ← map_sum, ← map_sum, key, map_zero, map_zero, zero_mul]
  · rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, RingHom.mem_ker, chartForm, linForm]
    simp only [map_sub, map_one, map_sum, map_mul, Ψt, coe_eval₂Hom, eval₂_C, eval₂_X, RingHom.comp_apply,
      ρ_X_inr, xs, ι]
    simp_rw [← mul_assoc, ← map_mul]
    rw [← Finset.sum_mul, ← map_sum]
    have : ∑ l, X l * (C (C (genPt Q l)) : Tgt Q e) = sT Q e := rfl
    rw [this, mul_inv_cancel₀ hs', sub_self]
end GroundTheory.Heights₂.Heights.Vertical.GenSecDomain
