-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Kernels_S6_QuotExtension_exists_smul_mem_idealLattice_af18f1878ef1
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T11:03:56.362178+00:00
-- url     : https://prove2.me/submissions/907959e6-485e-4400-9b35-747bad29c111

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_ImportsTer
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_ExistsSmulMemIdealLattice
import Theorems.Thm_P2M_GroundTheory_Variant__N1_exists_common_denominator_214cd264a479


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
theorem _root_.solution {n : ℕ} {a : Fin n → FractionalIdeal (𝓞 K)⁰ K}
    (ha : ∀ x, a x ≠ 0) (v : Fin n → K) : ∃ t : 𝓞 K, t ≠ 0 ∧ t • v ∈ idealLattice a := by
  classical
  choose e he0 hea using fun x => FractionalIdeal.exists_ne_zero_mem_isInteger (ha x)
  obtain ⟨c, hc0, hc⟩ := exists_common_denominator (M := Submodule.span (𝓞 K) {v})
    (Submodule.fg_span_singleton v)
  refine ⟨c * ∏ x, e x, mul_ne_zero hc0 (Finset.prod_ne_zero_iff.mpr fun x _ => he0 x), ?_⟩
  rw [idealLattice, Submodule.mem_pi]
  intro x _
  obtain ⟨w, hw⟩ := hc v (Submodule.mem_span_singleton_self v) x
  rw [← Finset.mul_prod_erase Finset.univ e (Finset.mem_univ x)]
  have hx : ((c * (e x * ∏ y ∈ Finset.univ.erase x, e y)) • v) x =
      (w * ∏ y ∈ Finset.univ.erase x, e y) • algebraMap (𝓞 K) K (e x) := by
    rw [Pi.smul_apply, Algebra.smul_def, Algebra.smul_def, map_mul, map_mul, map_mul, hw]
    ring
  rw [hx]
  exact Submodule.smul_mem _ _ (hea x)
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kernels.S6.QuotExtension
