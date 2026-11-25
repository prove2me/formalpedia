-- Prove2me | solution 1 for PI.LocFramePrimWork.DiffLoc_neg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:21:28.365439+00:00
-- url     : https://prove2.me/submissions/148f3520-6382-492b-a1c0-89b2f32c6f9c

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalPrimitiveFrame_StepsTop
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalPrimitiveFrame_DiffLoc
import Theorems.Thm_PI_LocFramePrimWork_DiffLoc_psi_mul
import Theorems.Thm_PI_LocFramePrimWork_DiffLoc_psi_one
import Theorems.Thm_PI_LocFramePrimWork_DiffLoc_isDiffVal
import Theorems.Thm_PI_LocFramePrimWork_DiffLoc_sc_eq
import Theorems.Thm_PI_LocFramePrimWork_DiffLoc_sc_mul
import Theorems.Thm_PI_LocFramePrimWork_DiffLoc_pow_nat
import Theorems.Thm_PI_LocFramePrimWork_DiffLoc_ddE_ne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.LocFramePrimWork
open NumberField IsDedekindDomain PI.LocFramePrim
open scoped TensorProduct Pointwise
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (v : HeightOneSpectrum (𝓞 F))
namespace PI.LocFramePrimWork
theorem _root_.solution (k : ℕ) :
    DiffLoc_psi v (((ddE (E := E) F) ^ (-(k : ℤ)) : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) : Set E) =
      Submodule.span (v.adicCompletionIntegers F) {sc (E := E) v (dV v)⁻¹} ^ k * DiffLoc_P (E := E) v := by
  have h1 : DiffLoc_psi v (((ddE (E := E) F) ^ (-(k : ℤ)) : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) : Set E) *
      (Submodule.span (v.adicCompletionIntegers F) {sc (E := E) v (dV v)} ^ k * DiffLoc_P (E := E) v) =
      DiffLoc_P (E := E) v := by
    rw [← DiffLoc_pow_nat, ← DiffLoc_psi_mul, zpow_neg, zpow_natCast,
      inv_mul_cancel₀ (pow_ne_zero _ DiffLoc_ddE_ne), DiffLoc_psi_one]
  have h2 : DiffLoc_psi v (((ddE (E := E) F) ^ (-(k : ℤ)) : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) : Set E) *
      DiffLoc_P (E := E) v =
      DiffLoc_psi v (((ddE (E := E) F) ^ (-(k : ℤ)) : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) : Set E) := by
    rw [← DiffLoc_psi_one, ← DiffLoc_psi_mul, mul_one]
  have h3 : Submodule.span (v.adicCompletionIntegers F) {sc (E := E) v (dV v)⁻¹} ^ k *
      Submodule.span (v.adicCompletionIntegers F) {sc (E := E) v (dV v)} ^ k = 1 := by
    rw [← mul_pow, Submodule.span_mul_span, Set.singleton_mul_singleton, ← DiffLoc_sc_mul,
      inv_mul_cancel₀ (DiffLoc_isDiffVal v).1, DiffLoc_sc_eq, map_one, ← Submodule.one_eq_span, one_pow]
  generalize DiffLoc_psi v (((ddE (E := E) F) ^ (-(k : ℤ)) : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) :
    Set E) = Q at h1 h2 ⊢
  calc Q = Q * DiffLoc_P (E := E) v * (Submodule.span (v.adicCompletionIntegers F) {sc (E := E) v (dV v)⁻¹} ^ k *
        Submodule.span (v.adicCompletionIntegers F) {sc (E := E) v (dV v)} ^ k) := by rw [h3, mul_one, h2]
    _ = Q * (Submodule.span (v.adicCompletionIntegers F) {sc (E := E) v (dV v)} ^ k * DiffLoc_P (E := E) v) *
        Submodule.span (v.adicCompletionIntegers F) {sc (E := E) v (dV v)⁻¹} ^ k := by ring
    _ = _ := by rw [h1, mul_comm]
end PI.LocFramePrimWork
