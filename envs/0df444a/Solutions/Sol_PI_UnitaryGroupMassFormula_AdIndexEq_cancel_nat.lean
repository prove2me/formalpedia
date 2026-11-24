-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.AdIndexEq.cancel_nat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T15:03:55.636401+00:00
-- url     : https://prove2.me/submissions/4bf6b170-beaf-4eb0-9f3a-2a0d538fd22d

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicIndexEquality_LiftMatMapSame
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicUnimodularity_ConstructionB
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Levelaf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicIndexEquality_Reduce
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
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.AdIndexEq
open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum Matrix
open scoped TensorProduct
open Formalism.MainNotions.S
namespace PI.UnitaryGroupMassFormula.AdIndexEq
theorem _root_.solution {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) {N : ℕ}
    (hN : Valued.v ((N : v.adicCompletion F)) = 1) {M : Type} [AddCommGroup M]
    [Module (v.adicCompletionIntegers F) M] (P : Submodule (v.adicCompletionIntegers F) M) {y : M}
    (h : N • y ∈ P) : y ∈ P := by
  have ha : (N : v.adicCompletion F) ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hN
    exact zero_ne_one hN
  let c : v.adicCompletionIntegers F :=
    ⟨(N : v.adicCompletion F)⁻¹, by rw [mem_adicCompletionIntegers, map_inv₀, hN, inv_one]⟩
  have hc : c * (N : v.adicCompletionIntegers F) = 1 := by
    apply Subtype.ext
    simp [c, ha]
  have h' : (N : v.adicCompletionIntegers F) • y ∈ P := by
    rwa [Nat.cast_smul_eq_nsmul]
  have := P.smul_mem c h'
  rwa [smul_smul, hc, one_smul] at this
end PI.UnitaryGroupMassFormula.AdIndexEq
