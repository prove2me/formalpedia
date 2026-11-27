-- Prove2me | solution 1 for PI.WAU.Cpt.bound_K
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T05:19:31.818825+00:00
-- url     : https://prove2.me/submissions/d8d96ae8-81a2-40f4-b2df-5bf4546272c1

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicUnimodularity_LamAfLeOhatL
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicUnimodularity_KCountable
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicUnimodularity_MulVecMemLf
import Theorems.Thm_PI_WAU_stab_mem
import Theorems.Thm_PI_WAU_Cpt_intC_single
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
noncomputable section
open PI PI.WAU
open IsDedekindDomain NumberField Formalism.MainNotions.S Topology
open scoped TensorProduct Matrix
open PI.WAU.Cpt
variable (I : AutInst)
namespace PI.WAU.Cpt
theorem _root_.solution (d D D1 : ℕ)
    (hlow : ∀ y : Fin I.n → I.E ⊗[I.F] Af I.F, (∀ j, IntC (bs I) (y j)) → d • y ∈ I.Lf)
    (hup : ∀ y ∈ I.Lf, ∀ j, IntC (bs I) (D • y j)) (h1 : IntC (bs I) (D1 • (1 : I.E ⊗[I.F] Af I.F)))
    {x : I.Gf} (hx : x ∈ I.Kset) (i j : Fin I.n) : IntC (bs I) ((D * (d * D1)) • I.fmat x i j) := by
  have hl := hlow _ (intC_single I D1 h1 j)
  have hxl := stab_mem hx hl
  have := hup _ hxl i
  have e : (I.fmat x *ᵥ (d • (Pi.single j (D1 • (1 : I.E ⊗[I.F] Af I.F)) : Fin I.n → I.E ⊗[I.F] Af I.F))) i =
      (d * D1) • I.fmat x i j := by
    rw [Matrix.mulVec_smul, Pi.smul_apply]
    simp [Matrix.mulVec, dotProduct, Pi.single_apply, mul_smul_comm, smul_smul, mul_comm]
    ring
  rw [e, smul_smul] at this
  exact this
end PI.WAU.Cpt
