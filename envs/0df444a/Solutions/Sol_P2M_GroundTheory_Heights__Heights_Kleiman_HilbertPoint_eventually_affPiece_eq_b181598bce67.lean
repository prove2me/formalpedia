-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_HilbertPoint_eventually_affPiece_eq_b181598bce67
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T08:30:55.82108+00:00
-- url     : https://prove2.me/submissions/0eb335ee-b7cb-45ab-a628-0664deb11bcc

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_GenericPointSectionHypotheses
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PHilbertPoint
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_HilbertPoint_finiteDimensional_affField_410254da17a8
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_HilbertPoint_affPiece_le_b8daa26183c8
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_HilbertPoint_affPiece_mono_5e45ec9ecaad
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_HilbertPoint_aeval_mem_affPiece_0c0745e4a5a8

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
open MvPolynomial Filter
noncomputable section
universe u w
open GroundTheory.Heights₂.Heights.Kleiman.HilbertPoint
variable {k : Type u} [Field k] {Ω : Type w} [Field Ω] [Algebra k Ω] {N : ℕ}
variable {y : Fin (N + 1) → Ω} {j : Fin (N + 1)}
namespace GroundTheory.Heights₂.Heights.Kleiman.HilbertPoint
theorem _root_.solution (hy : IsSubvar y (primeOf (S := k) y) 0) (hj : y j ≠ 0) :
    ∀ᶠ n : ℕ in atTop, affPiece k y j n = Subalgebra.toSubmodule (affRing k y j) := by
  have := finiteDimensional_affField hy hj
  have hfin : (Subalgebra.toSubmodule (affRing k y j)).FG := by
    rw [← Module.Finite.iff_fg]
    exact inferInstanceAs (Module.Finite k ((affRing k y j).toIntermediateField' (isField_affRing hy hj)))
  obtain ⟨s, hs⟩ := hfin
  have hex : ∀ z ∈ s, ∃ n, z ∈ affPiece k y j n := fun z hz => by
    have : z ∈ affRing k y j := by
      rw [← Subalgebra.mem_toSubmodule, ← hs]; exact Submodule.subset_span hz
    obtain ⟨f, rfl⟩ := this
    exact ⟨_, aeval_mem_affPiece hj f⟩
  choose! m hm using hex
  refine eventually_atTop.mpr ⟨s.sup m, fun n hn => le_antisymm (affPiece_le n) ?_⟩
  rw [← hs, Submodule.span_le]
  intro z hz
  exact affPiece_mono hj ((Finset.le_sup hz).trans hn) (hm z hz)
end GroundTheory.Heights₂.Heights.Kleiman.HilbertPoint
