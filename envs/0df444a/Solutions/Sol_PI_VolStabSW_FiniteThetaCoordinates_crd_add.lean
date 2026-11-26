-- Prove2me | solution 1 for PI.VolStabSW.FiniteThetaCoordinates.crd_add
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-26T03:51:36.317815+00:00
-- url     : https://prove2.me/submissions/302b0c4d-e973-42c1-80dd-14f539f879fb

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_FibInfEx
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_FinTheta
import Mathlib



-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabSW PI.VolStabSW.FiniteThetaCoordinates
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes NumberField IsDedekindDomain
open scoped TensorProduct
variable {F E : Type} [Field F] [Field E] [Algebra F E] {d : ℕ} (b : Module.Basis (Fin d) F E)
theorem _root_.solution (R : Type) [CommRing R] [Algebra F R] (y z : R ⊗[F] E) (k : Fin d) :
    crd b R (y + z) k = crd b R y k + crd b R z k := by
  first
    | (intros; simp [crd])
    | (intros; unfold crd; simp)
    | (intros; simp [crd]; done)
    | (intros; ext; simp [crd])
    | (intros; simp only [crd]; rfl)
    | (intros; constructor <;> intro h <;> simp_all [crd])
    | (intros; refine ⟨?_, ?_⟩ <;> simp [crd])
    | (intros; unfold crd; split_ifs <;> simp_all)
    | (intros; unfold crd; positivity)
    | (intros; unfold crd; ring)
    | (intros; unfold crd; exact?)
    | (intros; aesop (add norm simp [crd]))
    | (intros; simp [crd] <;> aesop)
    | (intros; exact crd.symm ..)
    | (intros; exact crd.comm ..)
  trace "HIT_217_1"

end 
