-- Prove2me | solution 1 for PositivityTheory.SiegelWeilFormula.KMain.schwartz_gs
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T11:57:30.896381+00:00
-- url     : https://prove2.me/submissions/71492b60-036d-47bb-8a31-2af13edf3cd8

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_NullSec
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_GaussianSchwartz
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_SiegelWeilFormula_ThetaSchwartzSums_SchwartzPolyGauss
import Theorems.Thm_GroundTheory_Global_gaussianSchwartz_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Global.gaussianSchwartz_apply



set_option autoImplicit false
noncomputable section
open scoped SchwartzMap
open PositivityTheory PositivityTheory.SiegelWeilFormula PositivityTheory.SiegelWeilFormula.KMain
open PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.KMain
theorem _root_.solution {m n : ℕ} (c : ℝ) (hc : 0 < c) : ∃ φ : 𝓢(Fin m → Fin n → ℂ, ℂ), ⇑φ = gs c := by
  have hs : 0 < Real.sqrt (c / Real.pi) := Real.sqrt_pos.mpr (div_pos hc Real.pi_pos)
  have hs2 : Real.sqrt (c / Real.pi) ^ 2 = c / Real.pi := Real.sq_sqrt (div_pos hc Real.pi_pos).le
  let L : (Fin m → Fin n → ℂ) ≃ₗ[ℝ] EuclideanSpace ℝ (Fin m × Fin n × Bool) :=
    { toFun := fun x => WithLp.toLp 2 (fun p => Real.sqrt (c / Real.pi) *
        (if p.2.2 then (x p.1 p.2.1).im else (x p.1 p.2.1).re))
      invFun := fun y => fun a i => ⟨(Real.sqrt (c / Real.pi))⁻¹ * y (a, i, false),
        (Real.sqrt (c / Real.pi))⁻¹ * y (a, i, true)⟩
      map_add' := fun x y => by
        ext p
        rcases p with ⟨a, i, β⟩
        cases β <;> simp <;> ring
      map_smul' := fun r x => by
        ext p
        rcases p with ⟨a, i, β⟩
        cases β <;> simp <;> ring
      left_inv := fun x => by
        funext a i
        apply Complex.ext <;> simp [hs.ne']
      right_inv := fun y => by
        ext p
        rcases p with ⟨a, i, β⟩
        cases β <;> simp [hs.ne'] }
  refine ⟨SchwartzMap.compCLMOfContinuousLinearEquiv ℂ L.toContinuousLinearEquiv
    (GroundTheory.Global.gaussianSchwartz _), ?_⟩
  rw [SchwartzMap.compCLMOfContinuousLinearEquiv_apply]
  funext x
  simp only [Function.comp_apply, GroundTheory.Global.gaussianSchwartz_apply, gs]
  rw [Complex.ofReal_exp]
  congr 1
  rw [EuclideanSpace.norm_sq_eq]
  simp [L, Fintype.sum_prod_type, Fintype.sum_bool, mul_pow, hs2, Complex.sq_norm, Complex.normSq_apply]
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  simp only [Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun i _ => ?_
  field_simp
  ring
end PositivityTheory.SiegelWeilFormula.KMain
