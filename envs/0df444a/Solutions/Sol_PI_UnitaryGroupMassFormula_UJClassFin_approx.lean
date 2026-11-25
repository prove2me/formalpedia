-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UJClassFin.approx
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T11:45:55.97413+00:00
-- url     : https://prove2.me/submissions/2e58cb76-a097-4e6d-9bee-f2c0e272261e

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassFiniteness_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_DictRing
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassFiniteness_IsIntegralOfIntOE
import Theorems.Thm_PI_UnitaryGroupMassFormula_UJClassFin_tmul_mem_Oh
import Theorems.Thm_PI_UnitaryGroupMassFormula_UJClassFin_isIntegral_of_intOE
import Theorems.Thm_PI_UnitaryGroupMassFormula_UJClassFin_alg_tmul
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_PIW_AdelClassFin_DictRing_af_approx
import Theorems.Thm_PIW_AdelClassFin_DictRing_af_denom
import Theorems.Thm_PIW_AdelClassFin_DictRing_e_denom
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks



set_option autoImplicit false
noncomputable section
open Matrix NumberField IsDedekindDomain
open scoped TensorProduct
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.UJClassFin
open PI.UJClassFin
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
namespace PI.UnitaryGroupMassFormula.UJClassFin
theorem _root_.solution (N : ℕ) (hN : 0 < N) (r : Af F ⊗[F] E) :
    ∃ e : E, ∃ o ∈ Oh F E, r = inclR (Af F) e + N • o := by
  induction r using TensorProduct.induction_on with
  | zero => exact ⟨0, 0, zero_mem _, by simp⟩
  | tmul a e =>
    obtain ⟨d, hd, hde⟩ := PIW.AdelClassFin.DictRing.e_denom e
    have hdF : (d : F) ≠ 0 := by exact_mod_cast hd.ne'
    set a' : Af F := algebraMap F (Af F) (d : F)⁻¹ * a with ha'
    have h1 : a ⊗ₜ[F] e = a' ⊗ₜ[F] ((d : E) * e) := by
      rw [ha', alg_tmul]
      congr 1
      rw [Algebra.smul_def, ← mul_assoc, map_inv₀, map_natCast,
        inv_mul_cancel₀ (by exact_mod_cast hd.ne' : (d : E) ≠ 0), one_mul]
    obtain ⟨m, hm, hma⟩ := PIW.AdelClassFin.DictRing.af_denom a'
    obtain ⟨β, y, hy, hβ⟩ := PIW.AdelClassFin.DictRing.af_approx _ hma (N * m) (Nat.mul_pos hN hm)
    have hmF : (m : F) ≠ 0 := by exact_mod_cast hm.ne'
    have h2 : a' = algebraMap F (Af F) ((m : F)⁻¹ * algebraMap (𝓞 F) F β) + (N : Af F) * y := by
      have hinv : algebraMap F (Af F) (m : F)⁻¹ * (m : Af F) = 1 := by
        rw [← map_natCast (algebraMap F (Af F)) m, ← map_mul, inv_mul_cancel₀ hmF, map_one]
      have e1 : algebraMap F (Af F) (m : F)⁻¹ * algebraMap (𝓞 F) (Af F) β =
          algebraMap F (Af F) ((m : F)⁻¹ * algebraMap (𝓞 F) F β) := by
        rw [map_mul, ← IsScalarTower.algebraMap_apply]
      have e2 : algebraMap F (Af F) (m : F)⁻¹ * (((N * m : ℕ) : Af F) * y) = (N : Af F) * y := by
        rw [Nat.cast_mul, mul_comm (N : Af F) (m : Af F), mul_assoc (m : Af F),
          ← mul_assoc (algebraMap F (Af F) (m : F)⁻¹), hinv, one_mul]
      calc a' = algebraMap F (Af F) (m : F)⁻¹ * ((m : Af F) * a') := by rw [← mul_assoc, hinv, one_mul]
        _ = _ := by rw [hβ, mul_add, e1, e2]
    refine ⟨((m : F)⁻¹ * algebraMap (𝓞 F) F β) • ((d : E) * e), y ⊗ₜ[F] ((d : E) * e),
      tmul_mem_Oh hy (isIntegral_of_intOE hde), ?_⟩
    rw [h1, h2, TensorProduct.add_tmul, ← mul_one (algebraMap F (Af F) _), alg_tmul, ← nsmul_eq_mul,
      TensorProduct.smul_tmul']
    simp only [nsmul_eq_mul]
    rfl
  | add x y hx hy =>
    obtain ⟨e1, o1, ho1, rfl⟩ := hx
    obtain ⟨e2, o2, ho2, rfl⟩ := hy
    refine ⟨e1 + e2, o1 + o2, add_mem ho1 ho2, ?_⟩
    rw [map_add, smul_add]; abel
end PI.UnitaryGroupMassFormula.UJClassFin
