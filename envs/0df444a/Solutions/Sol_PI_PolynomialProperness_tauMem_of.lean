-- Prove2me | solution 1 for PI.PolynomialProperness.tauMem_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:19:23.215397+00:00
-- url     : https://prove2.me/submissions/631a7032-5271-416b-9466-092df303338a

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialProperness_TauDefs
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HermitianFormFlagVector
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialProperness_FvecCastSucc
import Theorems.Thm_PI_PolynomialProperness_TauW_xiV_eq_sum
import Theorems.Thm_P2M_PI_PolynomialProperness_TauW_fvec_castSucc__9e5f4a85106f
import Theorems.Thm_P2M_PI_PolynomialProperness_TauW_fvec_last__592450600e93
import Theorems.Thm_P2M_PI_PolynomialProperness_TauW_frame_sum__1ea5ca424290
import Theorems.Thm_PI_PolynomialProperness_TauW_bvec_eq_xiV
import Theorems.Thm_Formalism_FourierDecayAlt_P_C2x5_uMap_eq
import Theorems.Thm_Formalism_QuantumDeterminants_WeylGroupFacts_mem_n_mul


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C2
noncomputable section
open PI PI.PolynomialProperness
open TauW
namespace PI.PolynomialProperness
theorem _root_.solution (hMX : MXFacts) (hNE : NEFacts) : TauMem := by
  intro k r z hz v hv
  have hvX : v.submatrix Fin.castSucc Fin.castSucc ∈ UTset r :=
    ⟨fun i j hij => hv.1 _ _ (Fin.castSucc_lt_castSucc_iff.2 hij), fun i => hv.2 _⟩
  obtain ⟨hm1, hm2, hm3⟩ := hMX k r _ hvX
  obtain ⟨hn1, hn2, hn3⟩ := hNE k r z hz (fun a => v a.castSucc (Fin.last r))
  have hfr : ∀ b, tauM k r z v *ᵥ fvec k r z b = ∑ a, v a b • fvec k r z a := by
    intro b
    simp only [tauM]
    rw [← Matrix.mulVec_mulVec]
    refine Fin.lastCases ?_ (fun b' => ?_) b
    · rw [fvec_last', hm3 z hz.1, hn3, frame_sum', hv.2 (Fin.last r), one_smul, xiV_eq_sum]
      exact add_comm _ _
    · have h0 : v (Fin.last r) b'.castSucc = 0 := hv.1 _ _ (Fin.castSucc_lt_last b')
      rw [fvec_castSucc', bvec_eq_xiV, hm2, hn2, frame_sum', xiV_eq_sum, h0, zero_smul, add_zero]
      refine Finset.sum_congr rfl fun a _ => ?_
      simp [Matrix.mulVec_single]
  exact ⟨WeylGroupFacts.mem_n_mul hn1 hm1, hfr, P.C2x5.uMap_eq hz _ _ hfr⟩
end PI.PolynomialProperness
