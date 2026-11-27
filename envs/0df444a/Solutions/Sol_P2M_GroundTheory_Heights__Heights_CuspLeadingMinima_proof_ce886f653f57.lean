-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_CuspLeadingMinima_proof_ce886f653f57
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T04:55:30.971495+00:00
-- url     : https://prove2.me/submissions/58d746b2-37df-4395-a020-b5427a7fac25

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_StatementsCusp
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_TransposeEqOfPosSemidef
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_PCuspLeadingMinima
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_CuspLeadingMinima_single_mem_leadingLattice_83159460311d
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_CuspLeadingMinima_single_linearIndependent_7ac4c2702ca9
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_CuspLeadingMinima_hermValue_single_36ddafe20269
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_MCCusp_inv_diag_le_31afacab59f5


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open Matrix
noncomputable section
namespace GroundTheory.Heights₂.Heights
namespace CuspLeadingMinima
theorem _root_.solution (hImPos : ChartPeriodImPos.Statement) :
    CuspLeadingMinima.Statement := by
  intro D T p _ hp ℓ hℓ
  obtain ⟨hpd, hge⟩ := hImPos D p.1 hp ℓ hℓ
  set Y := (D.period p.1 ℓ).map Complex.im
  refine ⟨fun j => (Pi.single (Fin.castLE T.r_le j) (1 : ℂ) : Fin D.g → ℂ),
    fun j => CuspLeadingMinima.single_mem_leadingLattice T.r_le j,
    CuspLeadingMinima.single_linearIndependent T.r_le, fun j => ?_⟩
  set k := Fin.castLE T.r_le j
  have hc := D.c_pos
  have hdiag : Y⁻¹ k k ≤ 1 / D.c := by
    refine MCCusp.inv_diag_le hpd k hc fun x => ?_
    have h1 : x k ^ 2 ≤ ∑ l, x l ^ 2 :=
      Finset.single_le_sum (f := fun l => x l ^ 2) (fun l _ => sq_nonneg (x l))
        (Finset.mem_univ k)
    calc D.c * x k ^ 2 ≤ D.c * ∑ l, x l ^ 2 := mul_le_mul_of_nonneg_left h1 hc.le
      _ ≤ _ := hge x
  unfold metricLength
  rw [CuspLeadingMinima.hermValue_single]
  calc Real.sqrt (Y⁻¹ k k) ≤ Real.sqrt (1 / D.c) := Real.sqrt_le_sqrt hdiag
    _ = D.c ^ (-(1 / 2 : ℝ)) := by
      rw [Real.sqrt_eq_rpow, Real.rpow_neg hc.le, one_div, Real.inv_rpow hc.le]
end CuspLeadingMinima
end GroundTheory.Heights₂.Heights
