-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_TranslateEq_mul_eq_twist_18fb89964ed5
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T01:35:54.586945+00:00
-- url     : https://prove2.me/submissions/43e9d725-99e5-48fc-b214-500c06bcac94

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_Objects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_CoordIdealIsMultiProjPrime
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_EqZeroOrIsHomogeneousOfMemPolyPiece

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman GroundTheory.Heights₂.Heights.Kleiman.TranslateEq
open MvPolynomial
noncomputable section
variable {S : Type} [CommRing S] {N : ℕ} {Ω : Type} [Field Ω] [Algebra S Ω] {x : Fin (N + 1) → Ω}
variable {E : Type} [AddCommGroup E] [Module Ω E] [Module S E] [IsScalarTower S Ω E]
namespace GroundTheory.Heights₂.Heights.Kleiman.TranslateEq
theorem _root_.solution (P Q : Kleiman.SubSystem S x Ω) (I : Kleiman.Chart x) :
    (P.sub I).restrictScalars S * (Q.sub I).restrictScalars S = ((P.twist Q).sub I).restrictScalars S := by
  apply le_antisymm
  · rw [Submodule.mul_le]
    intro p hp q hq
    exact Submodule.subset_span ⟨q, hq, p, hp, by rw [smul_eq_mul, mul_comm]⟩
  · intro z hz
    rw [Submodule.restrictScalars_mem] at hz
    induction hz using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨q, hq, y, hy, rfl⟩ := hz
      rw [show q • y = y * q from mul_comm q y]
      exact Submodule.mul_mem_mul hy hq
    | zero => exact zero_mem _
    | add u v _ _ hu hv => exact add_mem hu hv
    | smul a w hw0 hw =>
      clear hw0
      refine Submodule.mul_induction_on hw (fun p hp q hq => ?_) (fun u v hu hv => ?_)
      · have : a • (p * q) = (a • p) * q := by
          rw [Kleiman.chartRing_smul_def, Kleiman.chartRing_smul_def, mul_assoc]
        rw [this]
        exact Submodule.mul_mem_mul (Submodule.smul_mem _ a hp) hq
      · rw [smul_add]; exact add_mem hu hv
end GroundTheory.Heights₂.Heights.Kleiman.TranslateEq
