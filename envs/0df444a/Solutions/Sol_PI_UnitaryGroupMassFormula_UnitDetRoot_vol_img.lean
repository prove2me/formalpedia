-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UnitDetRoot.vol_img
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T11:00:36.037237+00:00
-- url     : https://prove2.me/submissions/012516ac-9e88-4772-9e34-fcde8bf0f3bc

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitDeterminantRoot_IdealPowPrincipal
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitDeterminantRoot_GlobVol
import Theorems.Thm_PI_UnitaryGroupMassFormula_UnitDetRoot_det_rows_map

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped NumberField ComplexConjugate
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.UnitDetRoot
open PI
variable (F : IntermediateField ℚ ℂ) {m : Type} [Fintype m] [DecidableEq m]
namespace PI.UnitaryGroupMassFormula.UnitDetRoot
theorem _root_.solution (δ : (m → ℂ) ≃ₗ[ℂ] (m → ℂ)) (Λ : AddSubgroup (m → ℂ)) :
    vol F (UnitDetRootDefs.imgLat (δ : (m → ℂ) →ₗ[ℂ] (m → ℂ)) Λ)
      = Submodule.span (𝓞 F) {LinearMap.det (δ : (m → ℂ) →ₗ[ℂ] (m → ℂ))} * vol F Λ := by
  unfold UnitDetRootDefs.imgLat vol volSet
  rw [Submodule.span_mul_span]
  congr 1
  ext z
  constructor
  · rintro ⟨v, hv, rfl⟩
    choose w hw hwv using fun j => AddSubgroup.mem_map.mp (hv j)
    refine Set.mem_mul.mpr ⟨_, Set.mem_singleton _, _, ⟨w, hw, rfl⟩, ?_⟩
    have hv' : v = fun j => (δ : (m → ℂ) →ₗ[ℂ] (m → ℂ)) (w j) := funext fun j => (hwv j).symm
    rw [hv', det_rows_map]
  · intro hz
    obtain ⟨_, h1, _, ⟨w, hw, rfl⟩, rfl⟩ := Set.mem_mul.mp hz
    obtain rfl := Set.mem_singleton_iff.mp h1
    refine ⟨fun j => (δ : (m → ℂ) →ₗ[ℂ] (m → ℂ)) (w j), fun j => AddSubgroup.mem_map.mpr ⟨w j, hw j, rfl⟩, ?_⟩
    rw [det_rows_map]
end PI.UnitaryGroupMassFormula.UnitDetRoot
