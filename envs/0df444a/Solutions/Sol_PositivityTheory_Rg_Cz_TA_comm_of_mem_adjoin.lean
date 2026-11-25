-- Prove2me | solution 1 for PositivityTheory.Rg.Cz.TA.comm_of_mem_adjoin
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T11:37:27.38603+00:00
-- url     : https://prove2.me/submissions/19006ea2-e68b-405e-b2e7-b68b0520e6e6

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_LiftCommEAt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PTransAllA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism.REAL Matrix
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Cz PositivityTheory.Rg.Cz.TA
variable {n : ℕ} {M : Type} [AddCommGroup M] [Module ℂ M]
namespace PositivityTheory.Rg.Cz.TA
theorem _root_.solution {A : Type*} [Ring A] [Algebra ℂ A] {s : Set A} {X Z : A}
    (hX : X ∈ Algebra.adjoin ℂ s) (h : ∀ T ∈ s, Commute T Z) : Commute X Z := by
  have hs : s ⊆ Subalgebra.centralizer ℂ {Z} := fun T hT => by
    rw [SetLike.mem_coe, Subalgebra.mem_centralizer_iff]
    intro g hg
    rw [Set.mem_singleton_iff] at hg
    rw [hg]
    exact (h T hT).symm.eq
  have hX' := Algebra.adjoin_le hs hX
  rw [Subalgebra.mem_centralizer_iff] at hX'
  exact (hX' Z rfl).symm
end PositivityTheory.Rg.Cz.TA
