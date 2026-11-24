-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_TwistFin_psi_mem_tgr_ca561eb3db71
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:31:56.641131+00:00
-- url     : https://prove2.me/submissions/bc402327-029e-460e-807d-7d25ca4ebfc5

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TwistFiniteness_PsiOfIsHomogeneous
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_TwistFin_psi_X_102517a1af24
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_TwistFin_single_mem_tgr_1d4f2bbc1844
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_TwistFin_algebraMap_LA_e2e747c45c95

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
open MvPolynomial AddMonoidAlgebra
noncomputable section
universe u w
open GroundTheory.Heights₂.Heights.Kleiman.TwistFin
variable {Ω : Type w} [Field Ω] {N r : ℕ}
variable (x : Fin (N + 1) → Ω) (η : Fin (r + 1) → Ω)
variable (S : Type u) [CommRing S] [Algebra S Ω]
namespace GroundTheory.Heights₂.Heights.Kleiman.TwistFin
theorem _root_.solution (s : Sy S r) : psi η S s ∈ tgr 0 := by
  induction s using MvPolynomial.induction_on with
  | C a =>
    rw [psi, aeval_C, algebraMap_LA]
    exact single_mem_tgr 0 0 _
  | add p q hp hq => rw [map_add]; exact add_mem hp hq
  | mul_X p j hp =>
    rw [map_mul, psi_X]
    simpa using SetLike.mul_mem_graded hp (single_mem_tgr 0 1 (η j))
end GroundTheory.Heights₂.Heights.Kleiman.TwistFin
