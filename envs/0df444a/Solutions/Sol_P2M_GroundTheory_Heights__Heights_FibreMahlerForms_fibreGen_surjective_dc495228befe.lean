-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FibreMahlerForms_fibreGen_surjective_dc495228befe
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T09:40:34.608935+00:00
-- url     : https://prove2.me/submissions/6cceee0a-2d22-4467-810a-60b23855cfe0

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_StatementsFibreMahler
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_PDiagonalChange
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_MahlerMul
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_SphereMean
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_ContinuousHermNormGroup
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_PFibreMahlerForms

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
open MvPolynomial NumberField TensorProduct ComplexAt
noncomputable section
open GroundTheory.Heights₂.Heights.FibreMahlerForms
variable {F : Type} [Field F] [NumberField F] {W : Type} [AddCommGroup W] [Module (𝓞 F) W]
  [Module.Finite (𝓞 F) W] [Module.Projective (𝓞 F) W]
namespace GroundTheory.Heights₂.Heights.FibreMahlerForms
theorem _root_.solution (h : HermitianMetric F W) (σ : F →+* ℂ) {n : ℕ} (w : Fin n → W)
    (hw : Submodule.span (𝓞 F) (Set.range w) = ⊤) : Function.Surjective (fibreGen h σ w) := by
  set T := Submodule.span ℂ (Set.range fun k ↦ fibreVec h σ (w k))
  have hvec : ∀ e : W, fibreVec h σ e ∈ T := by
    intro e
    have he : e ∈ Submodule.span (𝓞 F) (Set.range w) := hw ▸ Submodule.mem_top
    obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun (𝓞 F)).mp he
    rw [fibreVec_sum]
    exact Submodule.sum_mem _ fun k _ ↦ T.smul_mem _ (Submodule.subset_span ⟨k, rfl⟩)
  intro ξ
  have hξ : ξ ∈ T := by
    obtain ⟨y, rfl⟩ := (FibreSpace.equiv h σ).surjective ξ
    induction y using TensorProduct.induction_on with
    | zero => rw [map_zero]; exact T.zero_mem
    | tmul z e =>
      have : FibreSpace.equiv h σ (z ⊗ₜ e) = ((ofComplex σ).symm z) • fibreVec h σ e := by
        rw [fibreVec, ← map_smul, smul_tmul', complex_smul_def, mul_one, AlgEquiv.apply_symm_apply]
      rw [this]
      exact T.smul_mem _ (hvec e)
    | add x y hx hy => rw [map_add]; exact T.add_mem hx hy
  obtain ⟨x, hx⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp hξ
  exact ⟨x, hx⟩
end GroundTheory.Heights₂.Heights.FibreMahlerForms
