-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_SnapperQuotFilt_fg_of_single_1e4a4c3ee91c
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T08:19:28.946939+00:00
-- url     : https://prove2.me/submissions/3c80cbba-c14a-49cb-8b23-746856c47286

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_SnapperQuotFiltSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TwistAlg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PDomination
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_HomogeneousComponentMulForm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman
open MvPolynomial
noncomputable section
universe u v w
open GroundTheory.Heights₂.Heights.Kleiman.SnapperQuotFilt
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ} {x : Fin (N + 1) → Ω}
  {E : Type v} [AddCommGroup E] [Module Ω E] [Module S E] [IsScalarTower S Ω E]
omit [Module S E] [IsScalarTower S Ω E]
namespace GroundTheory.Heights₂.Heights.Kleiman.SnapperQuotFilt
theorem _root_.solution (F : SubFamily S x E) (I : Chart x) {i : Fin (N + 1)} (hi : i ∈ I.1) (hxi : x i ≠ 0)
    (hfg : (F.sub (singleChart hxi)).FG) : (F.sub I).FG := by
  obtain ⟨T, hT⟩ := hfg
  have hsub : (singleChart hxi).1 ⊆ I.1 := Finset.singleton_subset_iff.mpr hi
  have key : ∀ z, z ∈ Submodule.span (chartRing S x (singleChart hxi)) (T : Set E) →
      z ∈ Submodule.span (chartRing S x I) (T : Set E) := fun z hz => by
    induction hz using Submodule.span_induction with
    | mem z hz => exact Submodule.subset_span hz
    | zero => exact Submodule.zero_mem _
    | add a b _ _ ha hb => exact Submodule.add_mem _ ha hb
    | smul b z _ hz => exact Submodule.smul_mem _ (chartIncl hsub b) hz
  refine ⟨T, le_antisymm ?_ ?_⟩
  · rw [Submodule.span_le]
    intro y hy
    exact F.mono _ I hsub y (hT ▸ Submodule.subset_span hy)
  · intro y hy
    obtain ⟨a, ⟨u, hu⟩, hay⟩ := (F.mem_iff _ I hsub y).mp hy
    rw [← hT] at hay
    have h2 := key _ hay
    have hinv : ((↑u⁻¹ : chartRing S x I) : Ω) * (a : Ω) = 1 := by
      have := congrArg Subtype.val (Units.inv_mul u)
      rw [hu] at this
      exact this
    have hy' : y = (↑u⁻¹ : chartRing S x I) • ((a : Ω) • y) := by
      change y = ((↑u⁻¹ : chartRing S x I) : Ω) • ((a : Ω) • y)
      rw [smul_smul, hinv, one_smul]
    rw [hy']
    exact Submodule.smul_mem _ _ h2
end GroundTheory.Heights₂.Heights.Kleiman.SnapperQuotFilt
