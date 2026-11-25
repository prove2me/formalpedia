-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_TranslateEq_bundleA_equiv_9a6f65d8882f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T06:16:55.82316+00:00
-- url     : https://prove2.me/submissions/fe458d5b-f33b-4a2e-a6e7-a825298dcff8

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_Objects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_CoordIdealIsMultiProjPrime
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_EqZeroOrIsHomogeneousOfMemPolyPiece
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_TranslateEq_GradedMod_equiv_bab59235570c
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_TranslateEq_polyGraded_equiv_07714b7c3c16
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_TranslateEq_IsGradedHom_equiv_a15063e9bd3b
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_TranslateEq_chartRingI_equiv_6c221ab935ac
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_TranslateEq_chartRing_equiv_3295007ad279
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_TranslateEq_dimCl_equiv_c39cbd206b03
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_TranslateEq_lineX_equiv_6acfbe997019
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_TranslateEq_chartModule_of_ne_zero_902c51d3fd20
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_TranslateEq_secs_equiv_51d02eb19002
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_TranslateEq_twist_equiv_61178bbb85a9
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_TranslateEq_Generated_equiv_67711faab90f

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman GroundTheory.Heights₂.Heights.Kleiman.TranslateEq
open MvPolynomial
noncomputable section
variable {S : Type} [CommRing S] {N : ℕ} {Ω : Type} [Field Ω] [Algebra S Ω] {x : Fin (N + 1) → Ω}
variable {E : Type} [AddCommGroup E] [Module Ω E] [Module S E] [IsScalarTower S Ω E]
namespace GroundTheory.Heights₂.Heights.Kleiman.TranslateEq
namespace bundleA
theorem _root_.solution {i : Fin (N + 1)} (h : x i ≠ 0) :
    (IndefiniteRowSideFullHecke.Kleiman.bundleA S x).mods i = toIndefiniteRowSideFullHecke (Kleiman.twistSys S x 1) i := by
  ext z
  rw [chartModule_of_ne_zero _ h, Submodule.restrictScalars_mem]
  change z ∈ Submodule.span S (((Subalgebra.toSubmodule (ReciprocityTheory.ChartRestriction.G.Geo.chartRing S x i)).map
      (LinearMap.mulRight S (x i ^ (1 : ℕ))) : Submodule S Ω) : Set Ω) ↔
    z ∈ Kleiman.twistMod S x 1 (Kleiman.singleChart h)
  rw [Submodule.span_eq, Kleiman.twistMod_eq_span 1 _ (Finset.mem_singleton_self i), zpow_one,
    Submodule.mem_span_singleton, Submodule.mem_map, chartRing.equiv S x h]
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact ⟨⟨a, ha⟩, by simp [Kleiman.chartRing_smul_def]⟩
  · rintro ⟨a, rfl⟩
    exact ⟨a, a.2, by simp [Kleiman.chartRing_smul_def]⟩
end bundleA
end GroundTheory.Heights₂.Heights.Kleiman.TranslateEq
