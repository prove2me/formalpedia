-- Prove2me | solution 1 for P2M_PI_LatIdxDetW_localization_map__381d41331f98
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T08:45:50.471823+00:00
-- url     : https://prove2.me/submissions/569c6984-66bf-4fb9-b524-5cfe1f8dd299

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
section
open Module IsDedekindDomain Formalism.HermitianLatticesTheory Formalism.DivisionValues
open scoped nonZeroDivisors
noncomputable section
namespace PI.LatIdxDetW
section Gen
variable {R W W' : Type*} [CommRing R] [AddCommGroup W] [Module R W] [AddCommGroup W'] [Module R W']
private theorem mem_localization_iff_exists_smul_mem (p : Ideal R) [p.IsPrime] (L : Submodule R W) (x : W) :
    x ∈ localization₂ p L ↔ ∃ s ∈ p.primeCompl, s • x ∈ L := Iff.rfl
end Gen
section Lat
variable {R K V : Type*} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K] [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V]
variable [FiniteDimensional K V]
end Lat
end PI.LatIdxDetW
end
end

set_option autoImplicit false
open Module IsDedekindDomain Formalism.HermitianLatticesTheory Formalism.DivisionValues
open scoped nonZeroDivisors
noncomputable section
open PI PI.LatIdxDetW
variable {R W W' : Type*} [CommRing R] [AddCommGroup W] [Module R W] [AddCommGroup W'] [Module R W']
namespace PI.LatIdxDetW
theorem _root_.solution (p : Ideal R) [p.IsPrime] (φ : W ≃ₗ[R] W') (L : Submodule R W) :
    localization₂ p (L.map (φ : W →ₗ[R] W')) = (localization₂ p L).map (φ : W →ₗ[R] W') := by
  ext x
  simp only [mem_localization_iff_exists_smul_mem, Submodule.mem_map_equiv, LinearEquiv.map_smul]
end PI.LatIdxDetW
