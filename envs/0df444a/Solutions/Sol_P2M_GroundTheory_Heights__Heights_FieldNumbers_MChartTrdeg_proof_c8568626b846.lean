-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FieldNumbers_MChartTrdeg_proof_c8568626b846
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T04:55:41.596592+00:00
-- url     : https://prove2.me/submissions/b46725fd-d7cd-4f11-8f65-0252df186448

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsMChart
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_JacobianSmoothness_RingKrullDimLeRingKrullDimQuotientAddOne
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PMChartTrdeg
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_MChartTrdeg_algebraicIndependent_6f697c3a467f
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_MChartTrdeg_isAlgebraic_adjoin_8f5520555759
import Theorems.Thm_GroundTheory_Arith_Abelian_Jacobian_trdeg_eq_of_isFractionRing


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
namespace MChartTrdeg
theorem _root_.solution (hH : MChartHomog.Statement.{u}) : MChartTrdeg.Statement.{u} := by
  intro F _ K _ _ ι _ P _ hP u hu
  set R := MRing ι F ⧸ P
  set L := FractionRing R
  set A₀ := (chartMap P u).range
  have hb : IsTranscendenceBasis A₀ (fun k => algebraMap R L (Ideal.Quotient.mk P (X ⟨k, u k⟩))) :=
    (MChartTrdeg.algebraicIndependent P hH hP u hu).isTranscendenceBasis_iff_isAlgebraic.mpr
      (MChartTrdeg.isAlgebraic_adjoin P u hu)
  have h1 : Algebra.trdeg A₀ L = Fintype.card K := by
    simpa using hb.lift_cardinalMk_eq_trdeg.symm
  have : FaithfulSMul A₀ L :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 Subtype.val_injective
  have : FaithfulSMul F A₀ :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 (algebraMap F A₀).injective
  rw [show Algebra.trdeg F (MRing ι F ⧸ chartIdeal P u) = Algebra.trdeg F A₀ from
      (Ideal.quotientKerEquivRange (chartMap P u)).trdeg_eq, ← h1, trdeg_add_eq F A₀ (A := L),
    GroundTheory.Arith.Abelian.Jacobian.trdeg_eq_of_isFractionRing (k := F) (A := R) L]
end MChartTrdeg
end GroundTheory.Heights₂.Heights.FieldNumbers
