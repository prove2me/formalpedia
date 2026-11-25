-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_StrongApprox_PlaceMaps_singleV_mul_inclV_1e030e3a01ff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T05:20:33.422452+00:00
-- url     : https://prove2.me/submissions/c4b50da6-aa4f-44ea-8944-955261219db5

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_StrongApproximation_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_StrongApproximation_PPlaceMaps
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_StrongApprox_PlaceMaps_singleV_tmul_ed4fb72a7896
import Theorems.Thm_GroundTheory_Automorphic_conj_conj
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_StrongApprox_singleV_tmul_6c18ac5465de
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Automorphic.conj_conj



set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open GroundTheory.Heights₂.Heights.StrongApprox
open Matrix NumberField IsDedekindDomain TensorProduct ReciprocityTheory.ChartRestriction.G.SA
open GroundTheory.Heights₂.Heights.StrongApprox.PlaceMaps
variable {F : Type} [Field F] [NumberField F] {E : Type} [Field E] [Algebra F E]
namespace GroundTheory.Heights₂.Heights.StrongApprox.PlaceMaps
theorem _root_.solution (v : HeightOneSpectrum (𝓞 F)) (x : Kv E v) (y : E) :
    singleV E v (x * inclV E v y) = singleV E v x * inclA F E y := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x x' hx hx' => rw [add_mul, map_add, map_add, hx, hx', add_mul]
  | tmul a b =>
    show singleV E v (a ⊗ₜ b * 1 ⊗ₜ y) = singleV E v (a ⊗ₜ b) * (1 ⊗ₜ y)
    rw [Algebra.TensorProduct.tmul_mul_tmul, singleV_tmul, singleV_tmul,
      Algebra.TensorProduct.tmul_mul_tmul, mul_one, mul_one]
end GroundTheory.Heights₂.Heights.StrongApprox.PlaceMaps
