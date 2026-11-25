-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_isMultiHomog_relabel_154a322e1b11
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T08:33:03.567659+00:00
-- url     : https://prove2.me/submissions/7103906e-6c88-4327-98cd-0c79eab878a9

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Antisymmetric_StatementsNefRelabel
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Antisymmetric_PNefOnFibresRelabel
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_relabelRingEquiv_apply_281506490fa6

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
theorem _root_.solution {f : MRing ι} {d : K → ℕ} (hf : IsMultiHomog f d) :
    IsMultiHomog (relabelRingEquiv ε h f) (fun k' => d (ε.symm k')) := by
  classical
  intro m hm k'
  rw [relabelRingEquiv_apply, support_rename_of_injective (relabelBlocks ε h).injective,
    Finset.mem_image] at hm
  obtain ⟨m₀, hm₀, rfl⟩ := hm
  obtain ⟨k, rfl⟩ := ε.surjective k'
  dsimp only
  rw [ε.symm_apply_apply, ← hf m₀ hm₀ k, ← (Equiv.cast (h k)).sum_comp]
  exact Finset.sum_congr rfl fun i _ =>
    Finsupp.mapDomain_apply (relabelBlocks ε h).injective m₀ ⟨k, i⟩
end GroundTheory.Heights₂.Heights
