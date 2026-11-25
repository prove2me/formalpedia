-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_StandardModelDualRank_linIndep_05cf3734c663
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T08:55:24.378307+00:00
-- url     : https://prove2.me/submissions/75b1b58a-5246-49d8-8412-35e84def9ad5

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_DualStdModelField
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PDualArithVar
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StandardModelDualRank
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_StandardModelDualRank_exists_den_fin_194c4bd4e0e9
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_StandardModelDualRank_indep_int_3d1823af2d86

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
open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I4 MvPolynomial NumberField DualArithmeticVariety
noncomputable section
open GroundTheory.Heights₂.Heights.StandardModelDualRank
variable {K : Type} [Field K] {i : ℕ}
variable [NumberField K]
variable {T : Type}
namespace GroundTheory.Heights₂.Heights.StandardModelDualRank
theorem _root_.solution {n : ℕ} (B : Module.Basis (Fin n) ℚ K) (Φ₀ : Type) [Field Φ₀]
    [Algebra Φ₀ (dualStdModelField K i)]
    (hΦ : (algebraMap Φ₀ (dualStdModelField K i)).fieldRange = Subfield.closure (Set.range (u K i))) :
    LinearIndependent Φ₀ fun k => embK K i (B k) := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  have hf : ∀ k, algebraMap Φ₀ _ (g k) ∈ Subfield.closure (Set.range (u K i)) := fun k => by
    rw [← hΦ]; exact RingHom.mem_fieldRange.mpr ⟨g k, rfl⟩
  obtain ⟨D, -, hD0, hD⟩ := exists_den_fin _ hf
  choose q hq using fun k => RingHom.mem_range.mp (hD k)
  simp only [Algebra.smul_def] at hg
  have hsum : ∑ k, embK K i (B k) * psiZ K i (q k) = 0 := by
    calc ∑ k, embK K i (B k) * psiZ K i (q k)
        = D * ∑ k, algebraMap Φ₀ _ (g k) * embK K i (B k) := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun k _ => by rw [hq]; ring
      _ = 0 := by rw [hg, mul_zero]
  have h0 := indep_int B q hsum
  intro k
  have hk : D * algebraMap Φ₀ (dualStdModelField K i) (g k) = 0 := by rw [← hq, h0, map_zero]
  exact (algebraMap Φ₀ (dualStdModelField K i)).injective
    (((mul_eq_zero.mp hk).resolve_left hD0).trans (map_zero _).symm)
end GroundTheory.Heights₂.Heights.StandardModelDualRank
