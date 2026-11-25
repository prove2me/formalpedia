-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HilbertSamuel_PieceRootProductPolynomial_coeff_bound_37ce09f513ed
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T03:27:55.244363+00:00
-- url     : https://prove2.me/submissions/160044a7-cf8b-4f44-9365-9520175fcdee

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_IrreducibleConnected_StPieceRootProductPolynomial
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_IrreducibleConnected_StPieceCoefficientsHolomorphic
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_IrreducibleConnected_StMonicRootGrowth
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_IrreducibleConnected_StGrowthOffHypersurfacePolynomial
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_IrreducibleConnected_PPieceRootProductPolynomial

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.HilbertSamuel
open MvPolynomial Matrix
namespace GroundTheory.Heights₂.Heights.HilbertSamuel
namespace PieceRootProductPolynomial
theorem _root_.solution {ι : Type*} (s : Finset ι) (r : ι → ℂ) (B : ℝ)
    (hB : ∀ x ∈ s, ‖r x‖ ≤ B) (i : ℕ) :
    ‖(∏ x ∈ s, (Polynomial.X - Polynomial.C (r x))).coeff i‖ ≤ B ^ (s.card - i) * (s.card.choose i) := by
  have hm : (∏ x ∈ s, (Polynomial.X - Polynomial.C (r x))).Monic :=
    Polynomial.monic_prod_of_monic _ _ (fun x _ => Polynomial.monic_X_sub_C _)
  have hdeg : (∏ x ∈ s, (Polynomial.X - Polynomial.C (r x))).natDegree = s.card := by
    rw [Polynomial.natDegree_prod_of_monic _ _ (fun x _ => Polynomial.monic_X_sub_C _),
      Finset.sum_congr rfl (fun x _ => Polynomial.natDegree_X_sub_C _), Finset.sum_const, smul_eq_mul, mul_one]
  have hs : Polynomial.Splits ((∏ x ∈ s, (Polynomial.X - Polynomial.C (r x))).map (RingHom.id ℂ)) := by
    rw [Polynomial.map_id]
    exact Polynomial.Splits.prod (fun x _ => Polynomial.Splits.X_sub_C _)
  have h := Polynomial.coeff_le_of_roots_le (f := RingHom.id ℂ) (B := B) i hm hs (by
    intro z hz
    rw [Polynomial.map_id] at hz
    have hz' := (Polynomial.mem_roots hm.ne_zero).1 hz
    rw [Polynomial.IsRoot, Polynomial.eval_prod, Finset.prod_eq_zero_iff] at hz'
    obtain ⟨x, hx, hx0⟩ := hz'
    rw [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, sub_eq_zero] at hx0
    rw [hx0]
    exact hB x hx)
  rwa [Polynomial.map_id, hdeg] at h
end PieceRootProductPolynomial
end GroundTheory.Heights₂.Heights.HilbertSamuel
