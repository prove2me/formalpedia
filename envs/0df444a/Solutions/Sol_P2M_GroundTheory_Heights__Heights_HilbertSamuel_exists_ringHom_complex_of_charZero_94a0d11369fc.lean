-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HilbertSamuel_exists_ringHom_complex_of_charZero_94a0d11369fc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T03:55:14.831693+00:00
-- url     : https://prove2.me/submissions/3600cf29-d0a8-41e0-b237-332f6e9e34d9

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_IsIntersectionFamily
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_GenericComplexPoint

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
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Cardinal
noncomputable section
namespace GroundTheory.Heights₂.Heights.HilbertSamuel
theorem _root_.solution (F : Type) [Field F] [CharZero F] (hF : #F ≤ 𝔠) :
    Nonempty (F →+* ℂ) := by
  let M := MvPolynomial ℂ F
  let E := FractionRing M
  let L := AlgebraicClosure E
  have : CharZero M := charZero_of_injective_algebraMap (R := F) (MvPolynomial.C_injective _ _)
  have : CharZero E := charZero_of_injective_algebraMap (R := M) (IsFractionRing.injective M E)
  have : CharZero L := charZero_of_injective_algebraMap (R := E) (algebraMap E L).injective
  have hM : #M ≤ 𝔠 := by
    refine MvPolynomial.cardinalMk_le_max.trans ?_
    rw [mk_complex]
    exact max_le (max_le hF le_rfl) aleph0_le_continuum
  have hE : #E = #M := Cardinal.mk_fractionRing M
  have hL : #L ≤ 𝔠 :=
    (Algebra.IsAlgebraic.cardinalMk_le_max E L).trans (max_le (hE ▸ hM) aleph0_le_continuum)
  have hinj : Function.Injective (fun c : ℂ => algebraMap E L (algebraMap M E (X c))) :=
    (algebraMap E L).injective.comp ((IsFractionRing.injective M E).comp MvPolynomial.X_injective)
  have hLc : #L = #ℂ :=
    le_antisymm (hL.trans_eq mk_complex.symm) (Cardinal.mk_le_of_injective hinj)
  obtain ⟨σ⟩ := IsAlgClosed.ringEquiv_of_equiv_of_charZero (K := L) (L := ℂ)
    (by rw [hLc, mk_complex]; exact aleph0_lt_continuum) (Cardinal.eq.1 hLc)
  exact ⟨σ.toRingHom.comp ((algebraMap E L).comp ((algebraMap M E).comp C))⟩
end GroundTheory.Heights₂.Heights.HilbertSamuel
