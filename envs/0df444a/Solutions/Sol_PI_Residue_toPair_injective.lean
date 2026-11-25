-- Prove2me | solution 1 for PI.Residue.toPair_injective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:13:45.10026+00:00
-- url     : https://prove2.me/submissions/0e6562a0-821a-4220-a64a-fd29affdb29d

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ResidueLatticeCount_UnitPreserving
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ResidueLatticeCount_DvdSpanOfIdealSet

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField NumberField.mixedEmbedding NumberField.mixedEmbedding.fundamentalCone
  NumberField.Units
open scoped nonZeroDivisors ENNReal Classical
noncomputable section
open PI PI.Residue
variable {K : Type} [Field K] [NumberField K]
namespace PI.Residue
theorem _root_.solution (J : (Ideal (𝓞 K))⁰) (C : ClassGroup (𝓞 K))
    (hJ : ClassGroup.mk0 J = C⁻¹) : Function.Injective (toPair J C hJ) := by
  intro x y h
  have h1 : cof J x = cof J y := by
    have := congrArg (fun p => ((p.1 : (Ideal (𝓞 K))⁰) : Ideal (𝓞 K))) h
    exact this
  have h2 : (integerSetEquiv K (idealSetMap K J x)).2 = (integerSetEquiv K (idealSetMap K J y)).2 :=
    congrArg (fun p : {I : (Ideal (𝓞 K))⁰ // ClassGroup.mk0 I = C} × torsion K => p.2) h
  have h3 : (integerSetEquiv K (idealSetMap K J x)).1 = (integerSetEquiv K (idealSetMap K J y)).1 := by
    apply Subtype.ext
    apply Subtype.ext
    rw [integerSetEquiv_apply_fst, integerSetEquiv_apply_fst, cof_spec, cof_spec, h1]
  have h4 : idealSetMap K J x = idealSetMap K J y := (integerSetEquiv K).injective (Prod.ext h3 h2)
  apply Subtype.ext
  rw [← idealSetMap_apply K J x, ← idealSetMap_apply K J y, h4]
end PI.Residue
