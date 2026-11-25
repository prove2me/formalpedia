-- Prove2me | solution 1 for PositivityTheory.Rg.Cz.JMA.pair_comm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T11:35:15.906257+00:00
-- url     : https://prove2.me/submissions/758affcb-3834-47b3-a691-ce7e70934f53

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_LiftCommEAt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PJmComm

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
open PositivityTheory.Rg.Cz.JMA
variable {n : ℕ} {M : Type} [AddCommGroup M] [Module ℂ M]
namespace PositivityTheory.Rg.Cz.JMA
theorem _root_.solution {A : Type} [Ring A] [Algebra ℂ A] (u : ℂ) (a b p : A) (hab : Commute a b)
    (h1 : b * p = p * a + 1) (h2 : p * b = a * p + 1) :
    Commute ((algebraMap ℂ A u + a) * (algebraMap ℂ A u + b)) p := by
  have hU : ∀ z : A, Commute (algebraMap ℂ A u) z := fun z => Algebra.commutes u z
  have hs : Commute (a + b) p := by
    show (a + b) * p = p * (a + b)
    rw [add_mul, mul_add, h1, h2]
    abel
  have hp : Commute (a * b) p := by
    show a * b * p = p * (a * b)
    calc a * b * p = a * (p * a + 1) := by rw [mul_assoc, h1]
      _ = (a * p + 1) * a := by noncomm_ring
      _ = p * b * a := by rw [h2]
      _ = p * (a * b) := by rw [mul_assoc, hab.eq]
  have he : (algebraMap ℂ A u + a) * (algebraMap ℂ A u + b) =
      algebraMap ℂ A u * algebraMap ℂ A u + algebraMap ℂ A u * (a + b) + a * b := by
    rw [add_mul, mul_add, mul_add, ← (hU a).eq, mul_add]
    abel
  rw [he]
  exact (((hU p).mul_left (hU p)).add_left ((hU p).mul_left hs)).add_left hp
end PositivityTheory.Rg.Cz.JMA
