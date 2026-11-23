-- Prove2me | solution 1 for PI.VolSemiDirect.W.stabilizer_fixes_frame_vector
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T00:34:47.916685+00:00
-- url     : https://prove2.me/submissions/22a1129d-87b4-48e9-8251-ae59c45e8834

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_SemiDefs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_StabilizerFixesFrameVector
import Theorems.Thm_Formalism_L2_SG_Sub_mem_stabT


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolSemiDirect PI.VolSemiDirect.W
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain
open scoped TensorProduct
variable {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
  (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)
namespace PI.VolSemiDirect.W
theorem _root_.solution {r : ℕ} (P : Frame E M r) {g : HA R σ J} (hg : g ∈ S0 R σ J P) (a : Fin r) :
    lin R σ J g (ratV (F := F) R (P.e a)) = ratV (F := F) R (P.e a) := by
  rw [S0, mem_stabT] at hg
  have := hg (Fin.castSucc a)
  simpa [F0, Fin.snoc_castSucc] using this
end PI.VolSemiDirect.W
