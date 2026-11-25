-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_isMultiHomog_relabel_symm_5fefe4430c04
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T08:47:40.177061+00:00
-- url     : https://prove2.me/submissions/181507d6-e63e-407d-8c81-093e46093728

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Antisymmetric_StatementsNefRelabel
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Antisymmetric_PNefOnFibresRelabel
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_relabelRingEquiv_symm_apply_679901b5bc6a

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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial
set_option linter.unusedSectionVars false
variable {K K' : Type} [Fintype K] [Fintype K'] {ι : K → Type} {ι' : K' → Type}
  [∀ k, Fintype (ι k)] [∀ k, Fintype (ι' k)] (ε : K ≃ K') (h : ∀ k, ι k = ι' (ε k))
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution {g : MRing ι'} {d : K' → ℕ} (hg : IsMultiHomog g d) :
    IsMultiHomog ((relabelRingEquiv ε h).symm g) (fun k => d (ε k)) := by
  classical
  intro m hm k
  rw [relabelRingEquiv_symm_apply, support_rename_of_injective (relabelBlocks ε h).symm.injective,
    Finset.mem_image] at hm
  obtain ⟨m₀, hm₀, rfl⟩ := hm
  dsimp only
  rw [← hg m₀ hm₀ (ε k), ← (Equiv.cast (h k)).sum_comp]
  refine Finset.sum_congr rfl fun i _ => ?_
  have := Finsupp.mapDomain_apply (relabelBlocks ε h).symm.injective m₀ (relabelBlocks ε h ⟨k, i⟩)
  rw [Equiv.symm_apply_apply] at this
  exact this
end GroundTheory.Heights₂.Heights
