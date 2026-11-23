-- Prove2me | solution 1 for PI.IsoDetW.Loc.sat_of_linear
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:33:37.238013+00:00
-- url     : https://prove2.me/submissions/788f39e6-ecaf-4234-82f8-855925533d55

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_IsoDet
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IsometryDeterminant_LidxAntisymm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.IsoDetW PI.IsoDetW.Loc
open PI.IsoDetDefs
variable {R K : Type*} [CommRing R] [Field K] [Algebra R K] [FaithfulSMul R K]
variable {W W' : Type*} [AddCommGroup W] [Module K W] [Module R W] [IsScalarTower R K W]
  [AddCommGroup W'] [Module K W'] [Module R W'] [IsScalarTower R K W']
namespace PI.IsoDetW.Loc
theorem _root_.solution (p : Ideal R) [p.IsPrime] (f : W →ₗ[K] W') (s : R) (y : W')
    (hs : s ∈ p.primeCompl) (hy : s • y ∈ LinearMap.range (f.restrictScalars R)) :
    y ∈ LinearMap.range (f.restrictScalars R) := by
  have hs0 : algebraMap R K s ≠ 0 := by
    intro h
    have : s = 0 := (FaithfulSMul.algebraMap_injective R K) (by simpa using h)
    exact hs (this ▸ p.zero_mem)
  obtain ⟨x, hx⟩ := hy
  refine ⟨(algebraMap R K s)⁻¹ • x, ?_⟩
  simp only [LinearMap.coe_restrictScalars, map_smul] at hx ⊢
  rw [hx, ← algebraMap_smul K s y, smul_smul, inv_mul_cancel₀ hs0, one_smul]
end PI.IsoDetW.Loc
