-- Prove2me | solution 1 for PI.VolSemiDirect.W.continuous_piMat_inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:27:08.141855+00:00
-- url     : https://prove2.me/submissions/f2f90123-c38c-4e2a-a7d9-12980a896719

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_ProjHA
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_ProjCont
import Theorems.Thm_PI_VolSemiDirect_W_piMat_eq
import Theorems.Thm_PI_VolSemiDirect_W_mat_inv

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
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub
open scoped TensorProduct
variable {F E : Type} [Field F] [Field E] [Algebra F E] {R : Type} [CommRing R] [Algebra F R]
  {σ : E →ₐ[F] E} {M : ℕ} {J : Matrix (Fin M) (Fin M) E} {r : ℕ} {P : Frame E M r} {T : F}
namespace PI.VolSemiDirect.W
theorem _root_.solution [TopologicalSpace R] [IsTopologicalRing (R ⊗[F] E)] :
    Continuous fun g : HA R σ J => piMat (P := P) (T := T) g⁻¹ := by
  have hm : Continuous fun g : HA R σ J =>
      (((HA.mat R σ J g)⁻¹ : GL (Fin M) (R ⊗[F] E)) : Matrix (Fin M) (Fin M) (R ⊗[F] E)) :=
    Units.continuous_coe_inv.comp continuous_subtype_val
  simp only [piMat_eq, mat_inv]
  exact continuous_const.add ((continuous_const.matrix_mul hm).matrix_mul continuous_const)
end PI.VolSemiDirect.W
