-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_DimTie_ringKrullDim_eq_62996ccb0278
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T08:50:58.805797+00:00
-- url     : https://prove2.me/submissions/f9bc33b3-ee7f-439b-87dc-70c6eaa5ba5c

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_JacobianSmoothness_RingKrullDimLeRingKrullDimQuotientAddOne
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_GenericPointSectionHypotheses
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_PDimTie
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_DimTie_trdeg_funField_2422b22669ab
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_DimTie_primeOf_eq_ker_7df1ef8391e4
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_DimTie_trdeg_range_544901a4c07b
import Theorems.Thm_GroundTheory_Arith_Abelian_Jacobian_ringKrullDim_eq_trdeg


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman
open MvPolynomial Algebra Cardinal
noncomputable section
universe u w
open GroundTheory.Heights₂.Heights.Kleiman.DimTie
variable {k : Type u} [Field k] {Ω : Type w} [Field Ω] [Algebra k Ω] {N : ℕ}
namespace GroundTheory.Heights₂.Heights.Kleiman.DimTie
theorem _root_.solution (y : Fin (N + 1) → Ω) (hy : y ≠ 0) :
    ringKrullDim (Poly k N ⧸ primeOf (S := k) y) =
      (((trdeg k (funField (k := k) y)).toENat + 1 : ℕ∞) : WithBot ℕ∞) := by
  obtain ⟨i₀, hi₀⟩ := Function.ne_iff.mp hy
  have hi₀ : y i₀ ≠ 0 := hi₀
  have : Algebra.FiniteType k (Poly k N ⧸ primeOf (S := k) y) :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ k _)
      (Ideal.Quotient.mkₐ_surjective k _)
  rw [GroundTheory.Arith.Abelian.Jacobian.ringKrullDim_eq_trdeg k]
  have hk : primeOf (S := k) y = RingHom.ker (dehom (k := k) y hi₀).rangeRestrict := by
    rw [primeOf_eq_ker (k := k) y hi₀]
    ext f
    simp only [RingHom.mem_ker]
    exact ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩
  let e : (Poly k N ⧸ primeOf (S := k) y) ≃ₐ[k] (dehom (k := k) y hi₀).range :=
    (Ideal.quotientEquivAlgOfEq k hk).trans
      (Ideal.quotientKerAlgEquivOfSurjective (dehom (k := k) y hi₀).rangeRestrict_surjective)
  have h := AlgEquiv.lift_trdeg_eq (R := k) (A := Poly k N ⧸ primeOf (S := k) y)
    (A' := (dehom (k := k) y hi₀).range) e
  rw [trdeg_range (k := k) y hi₀, ← trdeg_funField] at h
  have h2 := congrArg Cardinal.toENat h
  simp only [toENat_lift, map_add, map_one] at h2
  rw [h2]
end GroundTheory.Heights₂.Heights.Kleiman.DimTie
