-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_KHPrimeFilt_isGradedSub_sup_span_587463f0741f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T04:07:14.607778+00:00
-- url     : https://prove2.me/submissions/1392b243-063c-4b9e-8a2e-7f38b30cf3f7

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_KleimanNefness_AlgFiltSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PKHPrimeFilt
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_KHPrimeFilt_decompose_smul_mem_span_363f58496da1

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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH
open GroundTheory.Heights₂.Heights.Kleiman.KHPrimeFilt
variable {S : Type} [CommRing S] {K : Type} [Fintype K] [LinearOrder K] {ι : K → Type}
  [∀ k, Fintype (ι k)] {M : Type} [AddCommGroup M] [Module (MRingOver S ι) M] [Module S M]
  [IsScalarTower S (MRingOver S ι) M] {𝓜 : (K → ℤ) → Submodule S M} [DirectSum.Decomposition 𝓜]
namespace GroundTheory.Heights₂.Heights.Kleiman.KHPrimeFilt
theorem _root_.solution (hgr : IsMGraded S ι 𝓜) {A : Submodule (MRingOver S ι) M}
    (hA : IsGradedSub 𝓜 A) {g : M} {e : K → ℤ} (hg : g ∈ 𝓜 e) :
    IsGradedSub 𝓜 (A ⊔ Submodule.span (MRingOver S ι) {g}) := by
  intro m hm c
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hm
  obtain ⟨r, rfl⟩ := Submodule.mem_span_singleton.mp hb
  rw [DirectSum.decompose_add, DirectSum.add_apply, Submodule.coe_add]
  exact Submodule.add_mem _ (Submodule.mem_sup_left (hA a ha c))
    (Submodule.mem_sup_right (decompose_smul_mem_span hgr hg r c))
end GroundTheory.Heights₂.Heights.Kleiman.KHPrimeFilt
