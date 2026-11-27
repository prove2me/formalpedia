-- Prove2me | solution 1 for UpperTheory.V.W.toT_ofT
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T05:33:47.116231+00:00
-- url     : https://prove2.me/submissions/718eb970-3326-42dc-9021-4d2acef1b091

import Definitions.Def_Development_AutomorphicArithmetic_AutomorphicVarieties_WeilGroupCharacters_RepAlg
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_UnopSMul
import Definitions.Def_Development_AutomorphicArithmetic_AutomorphicVarieties_CommutativeAlgebraHeight_OfDetToDet
import Theorems.Thm_UpperTheory_V_Alg_Lift_map_hom
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] UpperTheory.V.Alg.Lift.map_hom



set_option autoImplicit false
noncomputable section
open TensorProduct IsLocalRing
open UpperTheory UpperTheory.V UpperTheory.V.W
variable (A G S : Type) [CommRing A] [Group G] [CommRing S] [Algebra A S]
variable {A G S}
namespace UpperTheory.V.W
theorem _root_.solution (x : S ⊗[A] MonoidAlgebra A G) : toT A G S (ofT A G S x) = x := by
  induction x with
  | zero => simp
  | add a b ha hb => simp only [map_add, ha, hb]
  | tmul s y =>
    induction y using MonoidAlgebra.induction_linear with
    | zero => simp
    | add a b ha hb => simp only [tmul_add, map_add, ha, hb]
    | single g a =>
      rw [ofT_tmul, map_smul, MonoidAlgebra.mapRingHom_single, toT_single, smul_tmul', smul_eq_mul, mul_comm,
        ← Algebra.smul_def, smul_tmul, MonoidAlgebra.smul_single, smul_eq_mul, mul_one]
end UpperTheory.V.W
