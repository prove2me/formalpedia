-- Prove2me | solution 1 for PI.VolStabW.IdxHW.crdS_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T11:13:28.039854+00:00
-- url     : https://prove2.me/submissions/50ae02ee-dc9b-4ac1-a7cd-1b9e67455d75

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_LocDensHI
import Definitions.Def_ReciprocityTheory_Automorphisms_InstMainA
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_LocDensIdxH
import Theorems.Thm_PI_VolStabW_coe_hermSMul


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabW
open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Topology Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes PI.VolFromSW
  IsLocalRing
open PI.VolStabW.IdxHW
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {d : ℕ}
  (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F)) (σ : E →ₐ[F] E) (a : ℕ)
namespace PI.VolStabW.IdxHW
theorem _root_.solution (t : Fv F v) (S : HermR (Fv F v) σ a) (i j : Fin a) (k : Fin d) :
    crdS b v σ a (t • S) i j k = t * crdS b v σ a S i j k := by
  simp only [crdS, coe_hermSMul, Matrix.smul_apply, map_smul, Finsupp.smul_apply, smul_eq_mul]
end PI.VolStabW.IdxHW
