-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Targets_Relabel_isMultiHomog_map_ac9cb8581cea
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T05:21:42.335843+00:00
-- url     : https://prove2.me/submissions/68b78d25-b9a9-415f-8ea8-a0c9a8754fe8

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_ExistsUniqueStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_MemMinimalPrimesOfMemDivSuppDivSupp
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Antisymmetric_PNefOnFibresRelabel
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_RelabelTransport
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_Relabel_ringEquiv_apply_1be400d6f15c

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
set_option linter.unusedSectionVars false
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Targets GroundTheory.Heights₂.Heights.Targets.Relabel
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 GroundTheory.Heights₂.Heights
variable {F : Type*} [Field F] {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]
  {K' : Type*} [Fintype K'] {ι' : K' → Type*} [∀ k, Fintype (ι' k)]
  (e : K ≃ K') (h : ∀ k, ι k ≃ ι' (e k))
namespace GroundTheory.Heights₂.Heights.Targets.Relabel
theorem _root_.solution {f : MRingOver F ι} {d : K → ℕ} (hf : IsMultiHomog f d) :
    IsMultiHomog (ringEquiv F e h f) (d ∘ e.symm) := by
  classical
  intro m hm k'
  rw [ringEquiv_apply, support_rename_of_injective (vars e h).injective, Finset.mem_image] at hm
  obtain ⟨m₀, hm₀, rfl⟩ := hm
  obtain ⟨k, rfl⟩ := e.surjective k'
  rw [Function.comp_apply, e.symm_apply_apply, ← hf m₀ hm₀ k, ← (h k).sum_comp]
  exact Finset.sum_congr rfl fun i _ =>
    Finsupp.mapDomain_apply (vars e h).injective m₀ ⟨k, i⟩
end GroundTheory.Heights₂.Heights.Targets.Relabel
