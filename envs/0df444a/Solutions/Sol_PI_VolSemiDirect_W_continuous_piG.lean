-- Prove2me | solution 1 for PI.VolSemiDirect.W.continuous_piG
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T05:18:39.771507+00:00
-- url     : https://prove2.me/submissions/58423382-c285-4519-96a9-159ce93b7c98

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_ProjHA
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_ProjCont
import Theorems.Thm_PI_VolSemiDirect_W_continuous_piMat_inv
import Theorems.Thm_PI_VolSemiDirect_W_continuous_piMat

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
variable (hσσ : ∀ x, σ (σ x) = x) (hJ : IsHermND σ J) (hP : P.IsStd σ J T)
namespace PI.VolSemiDirect.W
theorem _root_.solution [TopologicalSpace R] [IsTopologicalRing (R ⊗[F] E)] :
    Continuous fun s : S0 R σ J P => piG hσσ hJ hP (s : HA R σ J) s.2 := by
  apply Continuous.subtype_mk
  rw [Units.continuous_iff]
  exact ⟨(continuous_piMat (P := P) (T := T)).comp continuous_subtype_val,
    (continuous_piMat_inv (P := P) (T := T)).comp continuous_subtype_val⟩
end PI.VolSemiDirect.W
