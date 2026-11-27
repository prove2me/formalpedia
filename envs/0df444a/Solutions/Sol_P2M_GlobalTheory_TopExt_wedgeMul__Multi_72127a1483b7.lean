-- Prove2me | solution 1 for P2M_GlobalTheory_TopExt_wedgeMul__Multi_72127a1483b7
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T04:53:08.3698+00:00
-- url     : https://prove2.me/submissions/c127dc49-5cfc-4488-bc69-9c7b2eb0d6db

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_MemHomogIffIsHomogeneous
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_ExistsDetEquivOfSubsingleton
import Theorems.Thm_GlobalTheory_SymAlg_baseChangeEquiv_tmul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.SymAlg.baseChangeEquiv_tmul



set_option autoImplicit false
open TensorProduct Module Function
open GlobalTheory
open GlobalTheory.TopExt
variable {R F H L : Type*} [CommRing R] [AddCommGroup F] [Module R F] [AddCommGroup H] [Module R H]
  [AddCommGroup L] [Module R L]
namespace GlobalTheory.TopExt
theorem _root_.solution {a b : ℕ} (x : Fin a → H) (y : Fin b → H) :
    wedgeMul R H a b (exteriorPower.ιMulti R a x ⊗ₜ exteriorPower.ιMulti R b y) =
      exteriorPower.ιMulti R (a + b) (Fin.append x y) :=
  Subtype.ext (by simp [ExteriorAlgebra.ιMulti_mul_ιMulti])
end GlobalTheory.TopExt
