-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.LocJacTyp.alp_last
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-26T03:51:33.309421+00:00
-- url     : https://prove2.me/submissions/04721cc8-52d2-4990-aa03-87559aa6efc3

import Definitions.Def_Formalism_PeriodIntegrals_LocJacTyp
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalJacobianType_KitAbs
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
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.LocJacTyp
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes NumberField IsDedekindDomain PI.LocJacTyp
variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
theorem _root_.solution (r : ℕ) : alp v r (Fin.last r) = 1 := by
  first
    | (intros; simp [alp, LocJacTyp])
    | (intros; unfold alp LocJacTyp; simp)
    | (intros; simp [alp, LocJacTyp]; done)
    | (intros; ext; simp [alp, LocJacTyp])
    | (intros; simp only [alp, LocJacTyp]; rfl)
    | (intros; constructor <;> intro h <;> simp_all [alp, LocJacTyp])
    | (intros; refine ⟨?_, ?_⟩ <;> simp [alp, LocJacTyp])
    | (intros; unfold alp LocJacTyp; split_ifs <;> simp_all)
    | (intros; unfold alp LocJacTyp; positivity)
    | (intros; unfold alp LocJacTyp; ring)
    | (intros; unfold alp LocJacTyp; exact?)
    | (intros; aesop (add norm simp [alp, LocJacTyp]))
    | (intros; simp [alp, LocJacTyp] <;> aesop)
    | (intros; exact alp.symm ..)
    | (intros; exact alp.comm ..)
    | (intros; exact LocJacTyp.symm ..)
    | (intros; exact LocJacTyp.comm ..)
  trace "HIT_167_0"

end 
