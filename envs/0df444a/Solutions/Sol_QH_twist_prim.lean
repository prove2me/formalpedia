-- Prove2me | solution 1 for QH.twist_prim
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:05:58.2788+00:00
-- url     : https://prove2.me/submissions/1cba6cd1-ccbd-4dfb-b057-366096caac40

import Definitions.Def_Development_AutomorphicArithmetic_MeanSquareBounds_PrimeSetTwoBounds
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_TwistIsPrimitiveCharacter
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_WeightedVonMangoldtSumIdentity
import Definitions.Def_Development_AutomorphicArithmetic_MeanSquareBounds_TwistPrim
import Theorems.Thm_Formalism_HermitianLattices_ThinSetIntegral_twist_is_primitive_character
import Theorems.Thm_Formalism_HermitianLattices_ZeroFreeRegionGL2_twist_evaluation_formula


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Formalism.HermitianLattices.ZeroFreeRegionGL2 Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds
open QH
namespace QH
theorem _root_.solution :
    ∀ (f q : ℕ) [NeZero f] (ξ : DirichletCharacter ℂ f), ξ.IsPrimitive → q.Prime → q ≠ 2 → ¬ q ∣ f →
      ∃ ψ : DirichletCharacter ℂ (f * q), ψ.IsPrimitive ∧ ψ ≠ 1 ∧ ∀ n : ℕ, ψ (n : ZMod (f * q)) = ξ (n : ZMod f) * J q n := by
  intro f q _ ξ hξ hq hq2 hqf
  haveI : Fact q.Prime := ⟨hq⟩
  have hcop : q.Coprime f := (Nat.Prime.coprime_iff_not_dvd hq).mpr hqf
  obtain ⟨hp, hne, -⟩ := Formalism.HermitianLattices.ThinSetIntegral.twist_is_primitive_character.2 f ξ q hξ hq2 hcop
  refine ⟨tw ξ q, hp, hne, fun n => ?_⟩
  rw [Formalism.HermitianLattices.ZeroFreeRegionGL2.twist_evaluation_formula f ξ q n]
  rfl
end QH
