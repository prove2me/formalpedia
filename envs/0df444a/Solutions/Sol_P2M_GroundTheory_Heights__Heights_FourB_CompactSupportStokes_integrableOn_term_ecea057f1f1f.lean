-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FourB_CompactSupportStokes_integrableOn_term_ecea057f1f1f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:53:25.230556+00:00
-- url     : https://prove2.me/submissions/6eed6778-be80-4bb3-9809-2a3570354a79

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_Stokes
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LocalDensities_CompactSupportStokes
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FourB_CompactSupportStokes_chi_contOn_1d11afa1a450
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FourB_CompactSupportStokes_integrableOn_target_0b55a0c19207
import Theorems.Thm_ReciprocityTheory_AnForm_M_locDensCont
import Theorems.Thm_ReciprocityTheory_AnForm_M_st_isPotential_cons
import Theorems.Thm_ReciprocityTheory_AnForm_M_st_locDens_cons_eq_zero


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FourB GroundTheory.Heights₂.Heights.FourB.CompactSupportStokes
open MeasureTheory Filter Topology Set ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M FinHolAtlas
open scoped ContDiff Manifold
variable {e : ℕ} {X : Type} [TopologicalSpace X]
namespace GroundTheory.Heights₂.Heights.FourB.CompactSupportStokes
theorem _root_.solution (A : FinHolAtlas (e + 1) X) (χ : ChartPartition A)
    (Φ : Fin e → LocPot X) (hΦ : ∀ i, IsPotential A (Φ i)) (k j : Fin A.n) (w : X → ℝ)
    (hw : A.Smooth w) {L : Set X} (hL : IsCompact L) (hwL : tsupport w ⊆ L)
    (hLj : k = j ∨ L ⊆ (A.chart j).source) :
    IntegrableOn (fun y => χ.χ k ((A.chart j).symm y) * 1 *
      locDens A (Fin.cons (LocPot.ofFun w) Φ) j y) (A.chart j).target := by
  have hF : ContinuousOn (fun y => χ.χ k ((A.chart j).symm y) * 1 *
      locDens A (Fin.cons (LocPot.ofFun w) Φ) j y) (A.chart j).target :=
    ((chi_contOn A χ k j).mul continuousOn_const).mul
      (locDensCont A _ (st_isPotential_cons A hw hΦ) j)
  rcases hLj with rfl | hLj
  · refine integrableOn_target A k hF (hL.inter_left (isClosed_tsupport (χ.χ k)))
      (inter_subset_left.trans (χ.tsupport_subset k)) ?_
    intro y hy hyS
    by_cases h1 : (A.chart k).symm y ∈ tsupport (χ.χ k)
    · have h2 : (A.chart k).symm y ∉ tsupport w := fun h => hyS ⟨h1, hwL h⟩
      rw [st_locDens_cons_eq_zero A k w Φ hy h2, mul_zero]
    · rw [image_eq_zero_of_notMem_tsupport h1, zero_mul, zero_mul]
  · refine integrableOn_target A j hF hL hLj ?_
    intro y hy hyL
    rw [st_locDens_cons_eq_zero A j w Φ hy (fun h => hyL (hwL h)), mul_zero]
end GroundTheory.Heights₂.Heights.FourB.CompactSupportStokes
