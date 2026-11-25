-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FieldNumbers_FunctionFieldFinite_relDim_eq_trdeg_c42302537785
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T08:18:21.819494+00:00
-- url     : https://prove2.me/submissions/fdf840af-55e8-409f-b910-ac35a85e9604

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsFunctionFieldFinite
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsMChart
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PPFDegree
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_JacobianSmoothness_RingKrullDimLeRingKrullDimQuotientAddOne
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PFunctionFieldFinite
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_FunctionFieldFinite_trdeg_homFracDegZero_b6b3997ce745
import Theorems.Thm_GroundTheory_Arith_Abelian_Jacobian_exists_ringKrullDim_eq_trdeg


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
namespace GroundTheory.Heights₂.Heights.FieldNumbers.FunctionFieldFinite
theorem _root_.solution (hD : MChartDehomog.Statement.{u}) (hT : MChartTrdeg.Statement.{u})
    [∀ k, Fintype (ι k)] (P : Ideal (MRing ι F)) [P.IsPrime] (hP : IsMultiProjPrime P) :
    ∃ n : ℕ, Algebra.trdeg F (homFracDegZero P) = n ∧
      relDim P = (((n : ℤ) : WithTop ℤ) : WithBot (WithTop ℤ)) := by
  choose u hu using hP.relevant
  have h1 := trdeg_homFracDegZero hD hT P hP.multiHomog u hu
  obtain ⟨m, hdim, htr⟩ :=
    GroundTheory.Arith.Abelian.Jacobian.exists_ringKrullDim_eq_trdeg (k := F) (A := MRing ι F ⧸ P)
  rw [htr] at h1
  have hlt : Algebra.trdeg F (homFracDegZero P) < Cardinal.aleph0 :=
    lt_of_le_of_lt (h1 ▸ self_le_add_right _ _) (Cardinal.natCast_lt_aleph0 (n := m))
  obtain ⟨n, hn⟩ := Cardinal.lt_aleph0.mp hlt
  rw [hn] at h1
  have hnm : n + Fintype.card K = m := by exact_mod_cast h1
  refine ⟨n, hn, ?_⟩
  have hz : (((n + Fintype.card K : ℕ) : ℤ) - Fintype.card K : ℤ) = n := by push_cast; ring
  rw [relDim, hdim, ← hnm, ← hz]
  rfl
end GroundTheory.Heights₂.Heights.FieldNumbers.FunctionFieldFinite
