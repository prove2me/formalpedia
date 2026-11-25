-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.AdIndexEq.small_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:52:33.913922+00:00
-- url     : https://prove2.me/submissions/b632267c-c0d2-4968-b12f-301900cd457e

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicIndexEquality_InertPowDefs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicIndexEquality_ChiEqOneOfClosure
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicIndexEquality_Reduce
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicUnimodularity_CartierFrobeniusFormLocal
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicIndexEquality_InertPow
import Theorems.Thm_PI_UnitaryGroupMassFormula_AdIndexEq_incL_smul_mem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.AdIndexEq
open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum Matrix
open scoped TensorProduct
open Formalism.MainNotions.S
namespace PI.UnitaryGroupMassFormula.AdIndexEq
theorem _root_.solution (I : AutInst) (v : HeightOneSpectrum (𝓞 I.F)) (α : Av I v)
    (P : Matrix (Fin I.n) (Fin I.n) (Av I v)) (N : ℕ)
    (h1 : ∀ z ∈ Formalism.L2.SG.Sub.latLoc v (I.L : Set (Fin I.n → I.E)),
      N • (P *ᵥ z) ∈ Formalism.L2.SG.Sub.latLoc v (I.L : Set (Fin I.n → I.E)))
    (h2 : ∀ z ∈ Formalism.L2.SG.Sub.latLoc v (I.L : Set (Fin I.n → I.E)),
      N • ((α • P) *ᵥ z) ∈ Formalism.L2.SG.Sub.latLoc v (I.L : Set (Fin I.n → I.E)))
    {w : Av I v} (hw : InR I v α w) (z : Fin I.n → Av I v)
    (hz : z ∈ Formalism.L2.SG.Sub.latLoc v (I.L : Set (Fin I.n → I.E))) :
    (incL I v N * w) • (P *ᵥ z) ∈ Formalism.L2.SG.Sub.latLoc v (I.L : Set (Fin I.n → I.E)) := by
  obtain ⟨a, b, ha, hb, rfl⟩ := hw
  have e : (incL I v N * (incL I v a + incL I v b * α)) • (P *ᵥ z) =
      incL I v a • (N • (P *ᵥ z)) + incL I v b • (N • ((α • P) *ᵥ z)) := by
    rw [Matrix.smul_mulVec, ← Nat.cast_smul_eq_nsmul (Av I v), ← Nat.cast_smul_eq_nsmul (Av I v),
      smul_smul, smul_smul, smul_smul, ← add_smul, map_natCast]
    congr 1
    ring
  rw [e]
  exact add_mem (incL_smul_mem I v ha (h1 z hz)) (incL_smul_mem I v hb (h2 z hz))
end PI.UnitaryGroupMassFormula.AdIndexEq
