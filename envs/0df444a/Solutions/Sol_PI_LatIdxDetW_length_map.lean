-- Prove2me | solution 1 for PI.LatIdxDetW.length_map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T09:48:58.382174+00:00
-- url     : https://prove2.me/submissions/95b13582-6ff6-4bc4-869a-5091e618db77

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_LatIdxDet
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_IdxChange
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeIndexDeterminant_NegLogValuation

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module IsDedekindDomain Formalism.HermitianLatticesTheory Formalism.DivisionValues
open scoped nonZeroDivisors
noncomputable section
open PI PI.LatIdxDetW
variable {R W W' : Type*} [CommRing R] [AddCommGroup W] [Module R W] [AddCommGroup W'] [Module R W']
namespace PI.LatIdxDetW
theorem _root_.solution (φ : W ≃ₗ[R] W') (X Y : Submodule R W) :
    Module.length R (↥(X.map (φ : W →ₗ[R] W')) ⧸
        (Y.map (φ : W →ₗ[R] W')).comap (X.map (φ : W →ₗ[R] W')).subtype) =
      Module.length R (↥X ⧸ Y.comap X.subtype) := by
  have e : (↥X ⧸ Y.comap X.subtype) ≃ₗ[R] (↥(X.map (φ : W →ₗ[R] W')) ⧸
      (Y.map (φ : W →ₗ[R] W')).comap (X.map (φ : W →ₗ[R] W')).subtype) :=
    Submodule.Quotient.equiv _ _ (φ.submoduleMap X) (by
      ext ⟨y, hy⟩
      simp only [Submodule.mem_map, Submodule.mem_comap, Submodule.subtype_apply]
      constructor
      · rintro ⟨⟨x, hx⟩, hxY, hxy⟩
        refine ⟨x, hxY, ?_⟩
        simpa using congrArg Subtype.val hxy
      · rintro ⟨x, hxY, hxy⟩
        obtain ⟨x', hx', hx'y⟩ := hy
        have hxx : x = x' := φ.injective (hxy.trans hx'y.symm)
        refine ⟨⟨x, hxx ▸ hx'⟩, hxY, ?_⟩
        apply Subtype.ext
        simpa using hxy)
  exact e.length_eq.symm
end PI.LatIdxDetW
