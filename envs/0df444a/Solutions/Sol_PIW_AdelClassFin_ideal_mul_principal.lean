-- Prove2me | solution 1 for PIW.AdelClassFin.ideal_mul_principal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T05:18:35.712191+00:00
-- url     : https://prove2.me/submissions/2f072949-56af-4732-93b8-1628ffc2367b

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_IdealMulPrincipal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PIW PIW.AdelClassFin
open NumberField
open scoped nonZeroDivisors
namespace PIW.AdelClassFin
theorem _root_.solution {E : Type} [Field E] [NumberField E] (I : Ideal (𝓞 E)) (hI0 : I ∈ (Ideal (𝓞 E))⁰)
    (A : (Ideal (𝓞 E))⁰) (hA : ClassGroup.mk0 A = (ClassGroup.mk0 (⟨I, hI0⟩ : (Ideal (𝓞 E))⁰))⁻¹) :
    ∃ c : 𝓞 E, I * (A : Ideal (𝓞 E)) = Ideal.span {c} := by
  have h1 : ClassGroup.mk0 ((⟨I, hI0⟩ : (Ideal (𝓞 E))⁰) * A) = 1 := by
    rw [map_mul, hA, mul_inv_cancel]
  obtain ⟨c, hc⟩ := ((ClassGroup.mk0_eq_one_iff (((⟨I, hI0⟩ : (Ideal (𝓞 E))⁰) * A).2)).mp h1).principal
  exact ⟨c, hc⟩
end PIW.AdelClassFin
