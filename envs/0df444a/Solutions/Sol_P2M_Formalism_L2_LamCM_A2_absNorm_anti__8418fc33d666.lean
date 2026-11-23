-- Prove2me | solution 1 for P2M_Formalism_L2_LamCM_A2_absNorm_anti__8418fc33d666
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:04:56.832236+00:00
-- url     : https://prove2.me/submissions/f6c8b4b8-ee6c-41a7-b470-8ad422782dbe

import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_StatementA
import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_CMIdealValuations_ProdMulLeDetIdeal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.LamCM
open NumberField IsDedekindDomain
open scoped nonZeroDivisors ComplexOrder
open Formalism.L2.LamCM.A2
variable {K : Type} [Field K] [NumberField K]
namespace Formalism.L2.LamCM.A2
theorem _root_.solution {I J : FractionalIdeal (𝓞 K)⁰ K} (hIJ : I ≤ J) (hI : I ≠ 0) :
    FractionalIdeal.absNorm J ≤ FractionalIdeal.absNorm I := by
  have hJ : J ≠ 0 := by
    rintro rfl
    exact hI (FractionalIdeal.le_zero_iff.1 hIJ)
  have hX : I * J⁻¹ ≤ 1 := by
    calc I * J⁻¹ ≤ J * J⁻¹ := mul_le_mul' hIJ le_rfl
      _ = 1 := mul_inv_cancel₀ hJ
  obtain ⟨X, hX'⟩ := FractionalIdeal.le_one_iff_exists_coeIdeal.1 hX
  have hdec : I = J * (I * J⁻¹) := by
    rw [mul_comm I, ← mul_assoc, mul_inv_cancel₀ hJ, one_mul]
  have hIJ0 : I * J⁻¹ ≠ 0 := mul_ne_zero hI (inv_ne_zero hJ)
  have hX0 : X ≠ ⊥ := by
    rintro rfl
    apply hIJ0
    rw [← hX']
    exact FractionalIdeal.coeIdeal_bot
  have hN : (1 : ℚ) ≤ FractionalIdeal.absNorm (I * J⁻¹) := by
    rw [← hX', FractionalIdeal.coeIdeal_absNorm]
    have : Ideal.absNorm X ≠ 0 := fun e => hX0 (Ideal.absNorm_eq_zero_iff.1 e)
    exact_mod_cast Nat.one_le_iff_ne_zero.2 this
  calc FractionalIdeal.absNorm J = FractionalIdeal.absNorm J * 1 := (mul_one _).symm
    _ ≤ FractionalIdeal.absNorm J * FractionalIdeal.absNorm (I * J⁻¹) :=
        mul_le_mul_of_nonneg_left hN (FractionalIdeal.absNorm_nonneg _)
    _ = FractionalIdeal.absNorm I := by rw [← map_mul, ← hdec]
end Formalism.L2.LamCM.A2
