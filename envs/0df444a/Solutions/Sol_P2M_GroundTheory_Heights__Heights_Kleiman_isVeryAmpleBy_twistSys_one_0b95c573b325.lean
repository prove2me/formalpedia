-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_isVeryAmpleBy_twistSys_one_0b95c573b325
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T08:20:53.811672+00:00
-- url     : https://prove2.me/submissions/4532a93d-a8a9-4c96-9e51-1abd7bc1be74

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_AlgebraMapMemChartRingLine
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_mem_secs_twistBundle_one_62fb03cd3d01
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_span_range_eq_twistMod_one_cf9eb67143e0


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
open MvPolynomial Filter
noncomputable section
universe u v w
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω}
namespace GroundTheory.Heights₂.Heights.Kleiman
theorem _root_.solution : IsVeryAmpleBy (twistSys S x 1) x where
  mem_secs := mem_secs_twistBundle_one
  generates := span_range_eq_twistMod_one
  closed j hj a ha := by
    obtain ⟨n, hn⟩ := Set.mem_iInter.mp ha (singleChart hj)
    rw [one_mul] at hn
    obtain ⟨b, hb⟩ := Submodule.mem_span_singleton.mp
      (pow_twistSys_one_le n (singleChart hj) (Finset.mem_singleton_self j) hn)
    rw [chartRing_smul_def] at hb
    have hab : a = b := (mul_right_cancel₀ (pow_ne_zero n hj) hb).symm
    rw [hab]
    exact mem_ampleBase_of_mem_chartRing hj b.2
  affine j hj := (twistAmple S x).affine j hj
end GroundTheory.Heights₂.Heights.Kleiman
