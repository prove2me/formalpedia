-- Prove2me | solution 1 for ReciprocityTheory.PGsh.Up.RankA.factor_of_basis
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T15:34:27.852561+00:00
-- url     : https://prove2.me/submissions/82a4d23f-fd6d-4cf6-84e7-c60363480098

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_RankMapLeRank

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open ReciprocityTheory ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Up.RankA
variable {S : Type} [CommRing S]
namespace ReciprocityTheory.PGsh.Up.RankA
theorem _root_.solution {m n ι : Type} [Fintype ι] (A : Matrix m n S)
    (M : Submodule S (m → S)) (b : Module.Basis ι S M) (hA : ∀ y, (fun x => A x y) ∈ M) :
    A = (Matrix.of fun x l => (b l : m → S) x) *
      Matrix.of fun l y => b.repr ⟨fun x => A x y, hA y⟩ l := by
  ext x y
  have h := congrArg (fun z : M => (z : m → S) x) (b.sum_repr ⟨fun x => A x y, hA y⟩)
  simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply,
    smul_eq_mul] at h
  rw [Matrix.mul_apply]
  simp only [Matrix.of_apply]
  rw [← h]
  exact Finset.sum_congr rfl fun l _ => mul_comm _ _
end ReciprocityTheory.PGsh.Up.RankA
