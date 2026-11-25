-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Targets_Relabel_isMultiHomog_symm_3e327dafea17
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T05:29:05.002012+00:00
-- url     : https://prove2.me/submissions/3096cddb-eb10-4358-b905-b97aba6adede

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_ExistsUniqueStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_MemMinimalPrimesOfMemDivSuppDivSupp
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Antisymmetric_PNefOnFibresRelabel
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_RelabelTransport
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_Relabel_ringEquiv_symm_apply_adf9a25eb4eb

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
theorem _root_.solution {g : MRingOver F ι'} {d : K' → ℕ} (hg : IsMultiHomog g d) :
    IsMultiHomog ((ringEquiv F e h).symm g) (d ∘ e) := by
  classical
  intro m hm k
  rw [ringEquiv_symm_apply, support_rename_of_injective (vars e h).symm.injective,
    Finset.mem_image] at hm
  obtain ⟨m₀, hm₀, rfl⟩ := hm
  rw [Function.comp_apply, ← hg m₀ hm₀ (e k), ← (h k).sum_comp]
  refine Finset.sum_congr rfl fun i _ => ?_
  have := Finsupp.mapDomain_apply (vars e h).symm.injective m₀ (vars e h ⟨k, i⟩)
  rw [Equiv.symm_apply_apply] at this
  exact this
end GroundTheory.Heights₂.Heights.Targets.Relabel
