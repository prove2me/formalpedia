-- Prove2me | solution 1 for PositivityTheory.Rg.Cz.ChainP.adjoin_commute
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T11:32:22.727123+00:00
-- url     : https://prove2.me/submissions/0edc7924-d2b0-4060-a793-750fde9cd6b7

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_LiftCommEAt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PChainA

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
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Cz
open PositivityTheory.Rg.Cz.ChainP
variable {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
namespace PositivityTheory.Rg.Cz.ChainP
theorem _root_.solution {A : Type} [Ring A] [Algebra ℂ A] (s : Set A) (T : A) (hs : ∀ x ∈ s, Commute x T) :
    ∀ g ∈ Algebra.adjoin ℂ s, Commute g T := by
  intro g hg
  have hle : Algebra.adjoin ℂ s ≤ Subalgebra.centralizer ℂ {T} :=
    Algebra.adjoin_le fun x hx => by
      rw [SetLike.mem_coe, Subalgebra.mem_centralizer_iff]
      intro y hy
      rw [Set.mem_singleton_iff.1 hy]
      exact (hs x hx).symm.eq
  have h2 := hle hg
  rw [Subalgebra.mem_centralizer_iff] at h2
  exact (h2 T (Set.mem_singleton T)).symm
end PositivityTheory.Rg.Cz.ChainP
