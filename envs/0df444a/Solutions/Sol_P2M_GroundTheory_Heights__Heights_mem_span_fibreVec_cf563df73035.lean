-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_mem_span_fibreVec_cf563df73035
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T08:35:51.629806+00:00
-- url     : https://prove2.me/submissions/dfb2da1c-b432-47bd-8f3b-b786eb2e45fd

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithDegree
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_Slopes
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithDegreeExact

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open NumberField NumberField.ComplexEmbedding TensorProduct ComplexAt Matrix
noncomputable section
variable {K : Type*} [Field K] [NumberField K]
variable {E : Type*} [AddCommGroup E] [Module (𝓞 K) E] [Module.Finite (𝓞 K) E]
  [Module.Projective (𝓞 K) E] (h : HermitianMetric K E) (σ : K →+* ℂ)
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution {ι : Type*} [Fintype ι] {s : ι → E} (hs : LinearIndependent (𝓞 K) s)
    (hcard : Fintype.card ι = Module.finrank (𝓞 K) E) (y : Fibre σ E) :
    FibreSpace.equiv h σ y ∈ Submodule.span ℂ (Set.range fun i ↦ fibreVec h σ (s i)) := by
  have hfin := finite_quotient_span hs hcard
  set n := Nat.card (E ⧸ Submodule.span (𝓞 K) (Set.range s))
  have hn : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  set W := Submodule.span ℂ (Set.range fun i ↦ fibreVec h σ (s i))
  have key : ∀ e : E, fibreVec h σ e ∈ W := by
    intro e
    have hmem : (n : 𝓞 K) • e ∈ Submodule.span (𝓞 K) (Set.range s) := by
      have := card_nsmul_eq_zero' (G := E ⧸ Submodule.span (𝓞 K) (Set.range s))
        (x := Submodule.Quotient.mk e)
      rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at this
      rwa [Nat.cast_smul_eq_nsmul]
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun (𝓞 K)).mp hmem
    have h1 : fibreVec h σ ((n : 𝓞 K) • e) = (n : ℂ) • fibreVec h σ e := by
      rw [fibreVec_smul]
      congr 1
      simp
    have h2 : fibreVec h σ ((n : 𝓞 K) • e) ∈ W := by
      rw [← hc, fibreVec_sum]
      exact Submodule.sum_mem _ fun i _ ↦ W.smul_mem _ (Submodule.subset_span ⟨i, rfl⟩)
    rw [h1] at h2
    have := W.smul_mem ((n : ℂ)⁻¹) h2
    rwa [smul_smul, inv_mul_cancel₀ hn, one_smul] at this
  induction y using TensorProduct.induction_on with
  | zero => rw [map_zero]; exact W.zero_mem
  | tmul z e =>
    have : FibreSpace.equiv h σ (z ⊗ₜ e) = ((ofComplex σ).symm z) • fibreVec h σ e := by
      rw [fibreVec, ← map_smul, smul_tmul', complex_smul_def, mul_one, AlgEquiv.apply_symm_apply]
    rw [this]
    exact W.smul_mem _ (key e)
  | add x y hx hy => rw [map_add]; exact W.add_mem hx hy
end GroundTheory.Heights₂.Heights
