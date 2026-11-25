-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ChartKernel_aeval_genSubst_scale_287273e9ddd5
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T05:09:43.93189+00:00
-- url     : https://prove2.me/submissions/19db6849-79b4-452f-a3b8-15c0aabef516

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_ImportsBis
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_PChartKernel
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartKernel_eval__genSubst_eq_map_1ab8fb3a62a0
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartKernel_genSubst_scale_558405ff26bb

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial
noncomputable section
open GroundTheory.Heights₂.Heights.ChartKernel
variable {F : Type} [Field F] {n : ℕ}
namespace GroundTheory.Heights₂.Heights.ChartKernel
theorem _root_.solution {K : Type*} [Field K] [Algebra F K] {e : ℕ} (ξ : Fin n → K) (τ : K) (t : Fin n → F)
    (g : MvPolynomial (Fin e × Fin n) F) :
    aeval (genSubst ξ (fun m => τ⁻¹ * algebraMap F K (t m))) g =
      map (aeval (τ⁻¹ • ξ)).toRingHom
        (aeval (genSubst (fun m => (X m : MvPolynomial (Fin n) F)) (fun m => C (t m))) g) := by
  have h1 : (genSubst ξ (fun m => τ⁻¹ * algebraMap F K (t m)) : Fin e × Fin n → MvPolynomial (Fin e × Fin n) K) =
      genSubst (τ⁻¹ • ξ) (fun m => algebraMap F K (t m)) := funext fun ij => genSubst_scale _ _ _ ij
  have h2 : (fun m => (aeval (τ⁻¹ • ξ)).toRingHom (X m : MvPolynomial (Fin n) F)) = τ⁻¹ • ξ := funext fun m => by simp
  have h3 : (fun m => (aeval (τ⁻¹ • ξ)).toRingHom (C (t m) : MvPolynomial (Fin n) F)) = fun m => algebraMap F K (t m) :=
    funext fun m => by simp
  have h4 : C.comp ((aeval (τ⁻¹ • ξ)).toRingHom.comp C) = algebraMap F (MvPolynomial (Fin e × Fin n) K) :=
    RingHom.ext fun r => by simp [MvPolynomial.algebraMap_apply]
  rw [← eval₂_genSubst_eq_map, h2, h3, h4, h1, aeval_def]
end GroundTheory.Heights₂.Heights.ChartKernel
