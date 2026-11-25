-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.IAT.loc_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T11:37:03.321488+00:00
-- url     : https://prove2.me/submissions/6b3aaa1c-1617-44fc-a930-cc474a1922ac

import Definitions.Def_Formalism_LocalToGlobal_LatticeGeometry_GeometryDefinitions_PClassE
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Levelv
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_AdelstabL
import Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_EqGlobOfHat
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IntegralityAtPrimeLattices_AwayLoc
import Theorems.Thm_PI_UnitaryGroupMassFormula_IAT_locv_upper
import Theorems.Thm_PI_UnitaryGroupMassFormula_IAT_locv_lower
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
import Theorems.Thm_Formalism_UG_P_levelv_denom_family
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
open Matrix TensorProduct NumberField IsDedekindDomain Formalism.UG Formalism.UG.P
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.IAT
namespace PI.UnitaryGroupMassFormula.IAT
theorem _root_.solution {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) (Λ : Submodule (𝓞 E) (Fin n → E)) (hΛ : Formalism.L2.GlobalTheoryTheory.Comp.IsLat Λ)
    (M : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) :
    ∃ N : ℤ, N ≠ 0 ∧ ∀ z ∈ Formalism.L2.Geo.Def.PC.latV v Λ,
      (fun i => inclE (F := F) (v.adicCompletion F) ((N : ℤ) : E) * (M *ᵥ z) i) ∈ Formalism.L2.Geo.Def.PC.latV v Λ := by
  obtain ⟨mu, hmu, hu⟩ := locv_upper v Λ hΛ.1
  obtain ⟨ml, hml, hl⟩ := locv_lower v Λ hΛ.2
  obtain ⟨N0, hN0, hN⟩ := levelv_denom_family v (fun p : Fin n × Fin n => M p.1 p.2)
  refine ⟨ml * (N0 : ℤ) * mu, mul_ne_zero (mul_ne_zero hml (by exact_mod_cast hN0)) hmu, fun z hz => ?_⟩
  set w : Fin n → E ⊗[F] v.adicCompletion F :=
    fun i => N0 • (M *ᵥ fun j => inclE (F := F) (v.adicCompletion F) (mu : E) * z j) i with hw
  have hwS : ∀ i, w i ∈ Formalism.L2.Geo.Def.PC.SV E v := by
    intro i
    simp only [hw, Matrix.mulVec, dotProduct, Finset.smul_sum]
    exact sum_mem fun j _ => by rw [← smul_mul_assoc]; exact mul_mem (hN (i, j)) (hu z hz j)
  have e : (fun i => inclE (F := F) (v.adicCompletion F) (((ml * (N0 : ℤ) * mu : ℤ)) : E) * (M *ᵥ z) i) =
      fun i => inclE (F := F) (v.adicCompletion F) (ml : E) * w i := by
    funext i
    simp only [hw, Matrix.mulVec, dotProduct, Finset.mul_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [nsmul_eq_mul]
    push_cast
    simp only [map_mul, map_natCast]
    ring
  rw [e]
  exact hl w hwS
end PI.UnitaryGroupMassFormula.IAT
