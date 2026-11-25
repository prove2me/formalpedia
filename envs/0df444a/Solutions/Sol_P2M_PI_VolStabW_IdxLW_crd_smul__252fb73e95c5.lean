-- Prove2me | solution 1 for P2M_PI_VolStabW_IdxLW_crd_smul__252fb73e95c5
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T08:51:10.459257+00:00
-- url     : https://prove2.me/submissions/8f167416-c129-4ac9-a1f9-b1cc49c97c72

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_LocDensHI
import Definitions.Def_ReciprocityTheory_Automorphisms_InstMainA
import Definitions.Def_ReciprocityTheory_ResidueCardinality_ArtinOntoB
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_LocDensHIL

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
open PI.VolStabW.IdxLW
open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Topology Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsLocalRing
variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
variable {E : Type} [Field E] [Algebra F E] {d : ℕ} (b : Module.Basis (Fin d) F E) (a M : ℕ)
namespace PI.VolStabW.IdxLW
theorem _root_.solution (s : Fv F v) (y : Fv F v ⊗[F] E) (k : Fin d) :
    (Algebra.TensorProduct.basis (Fv F v) b).repr (s • y) k =
      s * (Algebra.TensorProduct.basis (Fv F v) b).repr y k := by
  simp [map_smul, Finsupp.smul_apply, smul_eq_mul]
end PI.VolStabW.IdxLW
