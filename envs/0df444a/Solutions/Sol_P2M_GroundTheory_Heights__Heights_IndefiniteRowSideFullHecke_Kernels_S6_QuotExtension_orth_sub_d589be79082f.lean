-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Kernels_S6_QuotExtension_orth_sub_d589be79082f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T11:12:03.321283+00:00
-- url     : https://prove2.me/submissions/6fb829a5-49c1-4f61-b303-7286a8a90e45

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_ImportsTer
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_ExistsSmulMemIdealLattice
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Kernels_S6_QuotExtension_exists_smul_mem_idealLattice_af18f1878ef1

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kernels
open NumberField NumberField.ComplexEmbedding TensorProduct Matrix GroundTheory.Heights₂.Heights
open GroundTheory.Heights₂.Heights.ComplexAt
open scoped nonZeroDivisors ComplexOrder
noncomputable section
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kernels.S6 GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kernels.S6.QuotExtension
variable {K : Type} [Field K] [NumberField K]
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kernels.S6.QuotExtension
theorem _root_.solution {n m : ℕ} {a : Fin n → FractionalIdeal (𝓞 K)⁰ K} (ha : ∀ x, a x ≠ 0)
    {d : (K →+* ℂ) → Fin n → ℝ} (hd : ∀ σ x, 0 < d σ x) (hc : ∀ σ x, d (conjugate σ) x = d σ x)
    (b : Fin m → Fin n → K) (σ : K →+* ℂ) (y : Fibre σ (idealLattice a))
    (hy : ∀ w : Fibre σ (subLattice a b), ((latticeBundle a d hd hc).metric.form σ).inner
      ((subLattice a b).subtype.lTensor (ComplexAt σ) w) y = 0) (i : Fin m) :
    star (embVec σ (b i)) ⬝ᵥ (diagMetric d σ *ᵥ latticeCoord σ (idealLattice a) y) = 0 := by
  obtain ⟨t, ht, htv⟩ := exists_smul_mem_idealLattice ha (b i)
  have hW : (⟨t • b i, htv⟩ : idealLattice a) ∈ subLattice a b :=
    Submodule.smul_of_tower_mem (Submodule.span K (Set.range b)) t
      (Submodule.subset_span ⟨i, rfl⟩)
  have h := hy ((1 : ComplexAt σ) ⊗ₜ ⟨_, hW⟩)
  rw [LinearMap.lTensor_tmul] at h
  have h' : star (latticeCoord σ (idealLattice a) ((1 : ComplexAt σ) ⊗ₜ[𝓞 K]
      (⟨t • b i, htv⟩ : idealLattice a))) ⬝ᵥ
      (diagMetric d σ *ᵥ latticeCoord σ (idealLattice a) y) = 0 := h
  have hl : latticeCoord σ (idealLattice a) ((1 : ComplexAt σ) ⊗ₜ[𝓞 K]
      (⟨t • b i, htv⟩ : idealLattice a)) = σ (t : K) • embVec σ (b i) := by
    funext r
    rw [latticeCoord_tmul]
    simp [embVec, Algebra.smul_def]
  have hσt : σ (t : K) ≠ 0 := by
    rw [map_ne_zero]
    exact_mod_cast ht
  rw [hl, star_smul, smul_dotProduct, smul_eq_mul] at h'
  exact (mul_eq_zero.mp h').resolve_left (by simpa using hσt)
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kernels.S6.QuotExtension
