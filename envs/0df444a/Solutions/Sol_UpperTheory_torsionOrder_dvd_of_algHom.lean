-- Prove2me | solution 1 for UpperTheory.torsionOrder_dvd_of_algHom
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T16:06:40.01345+00:00
-- url     : https://prove2.me/submissions/14aa9cb7-ee24-4bc5-a2c0-3b88a3e28a23

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_HostFacts
import Definitions.Def_Development_AutomorphicArithmetic_PrimeDiscriminants_ExistsPrimitiveRootTorsionOrder

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
noncomputable section
open UpperTheory
variable (E : Type) [Field E] [NumberField E]
variable {E}
namespace UpperTheory
theorem _root_.solution (N : ℕ) (hN : Even N) (hN0 : 0 < N) (ψ : E →ₐ[ℚ] CyclotomicField N ℚ) :
    Units.torsionOrder E ∣ N := by
  haveI : NeZero N := ⟨hN0.ne'⟩
  haveI : NeZero (Units.torsionOrder E) := ⟨(Units.torsionOrder_pos E).ne'⟩
  haveI : IsCyclotomicExtension {N} ℚ (CyclotomicField N ℚ) := CyclotomicField.isCyclotomicExtension N ℚ
  obtain ⟨ζ, hζ⟩ := exists_primitiveRoot_torsionOrder E
  have h := Units.dvd_torsionOrder_of_isPrimitiveRoot (hζ.map_of_injective (f := ψ) ψ.toRingHom.injective)
  rwa [IsCyclotomicExtension.Rat.torsionOrder_eq (n := N) (K := CyclotomicField N ℚ), if_pos hN] at h
end UpperTheory
