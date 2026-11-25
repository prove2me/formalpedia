-- Prove2me | solution 1 for PI.KerIso.DetOrdW.detOrdIndep
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:07:13.83448+00:00
-- url     : https://prove2.me/submissions/c75adb91-ddf8-42e5-b8d1-cfb36fbd9cf4

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_KerIso
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DeterminantKernelOrder_ValNatCastEqOne
import Theorems.Thm_PI_KerIso_DetOrdW_val_det_le_one
import Theorems.Thm_PI_KerIso_DetOrdW_comp_integral

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open NumberField
open PI PI.KerIso PI.KerIso.DetOrdW
open IsDedekindDomain
variable {K : Type} [Field K] [NumberField K]
variable {E : Type} [Field E] [Algebra K E] {n : Type} [Fintype n]
namespace PI.KerIso.DetOrdW
theorem _root_.solution : DetOrdIndep := by
  intro K E _ _ _ _ n _ M p 𝔭 g g' g₀ hp hp𝔭 hg hg'
  classical
  let u : (Fin 4 × n → K) →ₗ[K] (Fin 4 × n → K) :=
    ((g.symm.trans g' : (Fin 4 × n → K) ≃ₗ[K] (Fin 4 × n → K)) : (Fin 4 × n → K) →ₗ[K] (Fin 4 × n → K))
  let u' : (Fin 4 × n → K) →ₗ[K] (Fin 4 × n → K) :=
    ((g'.symm.trans g : (Fin 4 × n → K) ≃ₗ[K] (Fin 4 × n → K)) : (Fin 4 × n → K) →ₗ[K] (Fin 4 × n → K))
  have h1 : 𝔭.valuation K (LinearMap.det u) ≤ 1 :=
    val_det_le_one 𝔭 hp𝔭 u (fun v hv => comp_integral hg hg' v hv)
  have h2 : 𝔭.valuation K (LinearMap.det u') ≤ 1 :=
    val_det_le_one 𝔭 hp𝔭 u' (fun v hv => comp_integral hg' hg v hv)
  have hprod : LinearMap.det u' * LinearMap.det u = 1 := by
    rw [← LinearMap.det_comp]
    have hid : u' ∘ₗ u = LinearMap.id := LinearMap.ext fun x => by simp [u, u']
    rw [hid, LinearMap.det_id]
  have hv1 : 𝔭.valuation K (LinearMap.det u) = 1 := by
    refine le_antisymm h1 ?_
    by_contra hlt
    push_neg at hlt
    have h3 : 𝔭.valuation K (LinearMap.det u) * 𝔭.valuation K (LinearMap.det u') ≤ 𝔭.valuation K (LinearMap.det u) :=
      mul_le_of_le_one_right' h2
    rw [mul_comm, ← map_mul, hprod, map_one] at h3
    exact absurd h3 (not_le.2 hlt)
  have hrel : detRel g' g₀ = LinearMap.det u * detRel g g₀ := by
    unfold detRel
    rw [← LinearMap.det_comp]
    congr 1
    exact LinearMap.ext fun x => by simp [u]
  unfold ordK
  rw [hrel, map_mul, hv1, one_mul]
end PI.KerIso.DetOrdW
