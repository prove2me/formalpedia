-- Prove2me | solution 1 for ReciprocityTheory.Gal.smul_le_one_of_isIntegral
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T05:28:27.5052+00:00
-- url     : https://prove2.me/submissions/acb07849-3a2f-4aed-92a9-7b1c4380768b

import Definitions.Def_ReciprocityTheory_GaloisValuations_GlobalA
import Definitions.Def_ReciprocityTheory_GaloisValuations_GlobalB

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option linter.style.haveILetI false
noncomputable section
open NumberField IsDedekindDomain Pointwise
open scoped nonZeroDivisors
open ReciprocityTheory ReciprocityTheory.Gal
variable {F Ω : Type*} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
omit [NumberField F] [IsAlgClosure F Ω]
namespace ReciprocityTheory.Gal
theorem _root_.solution (g : Ω ≃ₐ[F] Ω) {A : ValuationSubring Ω}
    (hA : ∀ b : Ω, IsIntegral ℤ b → b ∈ A) {b : Ω} (hb : IsIntegral ℤ b) : b ∈ g • A := by
  rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, AlgEquiv.smul_def]
  exact hA _ (hb.map ((g⁻¹ : Ω ≃ₐ[F] Ω).toAlgHom.restrictScalars ℤ))
end ReciprocityTheory.Gal
