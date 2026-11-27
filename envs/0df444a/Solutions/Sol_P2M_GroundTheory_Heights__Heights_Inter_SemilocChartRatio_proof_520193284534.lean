-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_SemilocChartRatio_proof_520193284534
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T05:02:27.204989+00:00
-- url     : https://prove2.me/submissions/7db4493d-7197-4bd8-a8ce-f6ca27dfc8e6

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StSemilocChartRatio
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StFibreOverFinite
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_AvoidRing
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PSemilocChartRatio
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_AvoidRing_coordProd_not_mem_ea4019939c96
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_AvoidRing_exists_form_avoid_7ec45983efdd
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_AvoidRing_isMultiHomog_X_cf870dae9c4f
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_AvoidRing_isMultiHomog_coordProd_8cb4f1e2e87b
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_AvoidRing_isMultiHomog_mul_92fa4aba8533
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_isMultiHomog_X


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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4 IndefiniteRowSideFullHecke.Inter
namespace GroundTheory.Heights₂.Heights.Inter
namespace SemilocChartRatio
theorem _root_.solution (hF : FibreOverFinite.Statement) : SemilocChartRatio.Statement := by
  classical
  intro K _ ι _ K' _ ι' _ κ v P' n s α W i' hv hP' hZ hs hsn hW hi' q
  have hSf : (insert P' (fibreOver v P' W)).Finite :=
    (hF K ι K' ι' κ v P' n s α W hv hP' hZ hs hsn hW).insert P'
  have hSp : ∀ V ∈ insert P' (fibreOver v P' W), IsMultiProjPrime V := by
    rintro V (rfl | hV)
    · exact hP'.2.1
    · exact hV.1
  obtain ⟨d₀, hd₀⟩ := AvoidRing.exists_form_avoid _ hSf hSp
  obtain ⟨w, hwd, hwS⟩ := hd₀ (Pi.single q.1 1 + d₀) le_add_self
  have hPp : P'.IsPrime := hP'.2.1.1
  have hwP' : w ∉ P' := hwS P' (Set.mem_insert _ _)
  have hwnz : Ideal.Quotient.mk P' w ∈ nonZeroDivisors (MRing ι' ⧸ P') :=
    mem_nonZeroDivisors_of_ne_zero (by rwa [Ne, Ideal.Quotient.eq_zero_iff_mem])
  set N : MRing ι' := ∏ k, (X ⟨k, i' k⟩ : MRing ι') ^ d₀ k with hN
  have hNd : IsMultiHomog N d₀ := AvoidRing.isMultiHomog_coordProd i' d₀
  have hNP : N ∉ P' := AvoidRing.coordProd_not_mem hPp i' hi' d₀
  have hwW : ∀ W' ∈ fibreOver v P' W, w ∉ W' := fun W' hW' => hwS W' (Set.mem_insert_of_mem _ hW')
  have gen : ∀ u : MRing ι', IsMultiHomog u (Pi.single q.1 1 + d₀) →
      IsLocalization.mk' (FractionRing (MRing ι' ⧸ P')) (Ideal.Quotient.mk P' u) ⟨_, hwnz⟩ ∈
        semiLocRing P' (fibreOver v P' W) := fun u hu =>
    Subring.subset_closure ⟨u, w, _, hwnz, hwW, hu, hwd, rfl⟩
  have hq : IsMultiHomog (X q * N) (Pi.single q.1 1 + d₀) :=
    AvoidRing.isMultiHomog_mul (AvoidRing.isMultiHomog_X q.1 q.2) hNd
  have hc : IsMultiHomog (X ⟨q.1, i' q.1⟩ * N) (Pi.single q.1 1 + d₀) :=
    AvoidRing.isMultiHomog_mul (AvoidRing.isMultiHomog_X q.1 (i' q.1)) hNd
  refine ⟨⟨_, gen _ hq⟩, ⟨_, gen _ hc⟩, ?_, ?_⟩
  · show IsLocalization.mk' _ _ _ ≠ (0 : FractionRing (MRing ι' ⧸ P'))
    rw [Ne, IsFractionRing.mk'_eq_zero_iff_eq_zero, Ideal.Quotient.eq_zero_iff_mem]
    intro h
    rcases hPp.mem_or_mem h with h | h
    · exact hi' q.1 h
    · exact hNP h
  · show IsLocalization.mk' _ _ _ * _ = IsLocalization.mk' _ _ _ * _
    rw [mul_comm, IsLocalization.mul_mk'_eq_mk'_of_mul, mul_comm (IsLocalization.mk' _ _ _),
      IsLocalization.mul_mk'_eq_mk'_of_mul]
    congr 1
    simp only [map_mul]
    ring
end SemilocChartRatio
end GroundTheory.Heights₂.Heights.Inter
