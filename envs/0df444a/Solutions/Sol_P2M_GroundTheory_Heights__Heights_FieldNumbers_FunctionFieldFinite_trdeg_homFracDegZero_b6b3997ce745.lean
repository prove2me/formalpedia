-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FieldNumbers_FunctionFieldFinite_trdeg_homFracDegZero_b6b3997ce745
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T08:03:40.285453+00:00
-- url     : https://prove2.me/submissions/15a40cf1-92cf-48ba-aeba-e4830a153167

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsFunctionFieldFinite
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsMChart
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PPFDegree
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_JacobianSmoothness_RingKrullDimLeRingKrullDimQuotientAddOne
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PFunctionFieldFinite
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_FunctionFieldFinite_range_chartMap_599b5829d5e9
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_FunctionFieldFinite_homFracDegZero_eq_1e90cfbe461b
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
open GroundTheory.Heights₂.Heights.FieldNumbers.FunctionFieldFinite
variable {F : Type u} [Field F] {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type}
open IntermediateField.algebraAdjoinAdjoin
namespace GroundTheory.Heights₂.Heights.FieldNumbers.FunctionFieldFinite
theorem _root_.solution (hD : MChartDehomog.Statement.{u}) (hT : MChartTrdeg.Statement.{u})
    [∀ k, Fintype (ι k)] (P : Ideal (MRing ι F)) [P.IsPrime] (hP : IsMultiHomogIdeal P)
    (u : ∀ k, ι k) (hu : ∀ k, (X ⟨k, u k⟩ : MRing ι F) ∉ P) :
    Algebra.trdeg F (homFracDegZero P) + Fintype.card K = Algebra.trdeg F (MRing ι F ⧸ P) := by
  rw [← hT F K ι P hP u hu, homFracDegZero_eq hD P u hu,
    GroundTheory.Arith.Abelian.Jacobian.trdeg_eq_of_isFractionRing (k := F)
      (A := Algebra.adjoin F (chartGens P u)), ← range_chartMap]
  exact congrArg (· + _) (Ideal.quotientKerEquivRange (chartMap P u)).trdeg_eq.symm
end GroundTheory.Heights₂.Heights.FieldNumbers.FunctionFieldFinite
