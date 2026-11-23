-- Prove2me | solution 1 for ReciprocityTheory.PGsh.Ainf.root_pow
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:37:01.44986+00:00
-- url     : https://prove2.me/submissions/c49a94af-553f-4c60-9ea2-fe988beda904

import Definitions.Def_ReciprocityTheory_DualLattices_Imports
import Definitions.Def_ReciprocityTheory_DualLattices_ATowerInh
import Definitions.Def_ReciprocityTheory_DualLattices_AinfFacts

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open WittVector Ideal
open ReciprocityTheory ReciprocityTheory.PGsh
open ReciprocityTheory.PGsh.Ainf
variable (p : ℕ) [hp : Fact p.Prime] {C : Type} [Field C] [IsAlgClosed C] [CharZero C]
  {v : Valuation C NNReal} (O : Type) [CommRing O] [Algebra O C]
  [Fact ¬IsUnit (p : O)] [IsAdicComplete (span {(p : O)}) O]
namespace ReciprocityTheory.PGsh.Ainf
theorem _root_.solution (ε : PreTilt O p) (k : ℕ) : root p O ε k ^ p ^ k = ε := by
  have hsp : ∀ x : PreTilt O p, ((frobeniusEquiv (PreTilt O p) p).symm x) ^ p = x := fun x => by
    rw [← frobenius_def, ← _root_.frobeniusEquiv_apply, RingEquiv.apply_symm_apply]
  induction k with
  | zero => simp [root]
  | succ k ih =>
    simp only [root] at ih ⊢
    rw [Function.iterate_succ_apply', pow_succ', pow_mul, hsp]
    exact ih
end ReciprocityTheory.PGsh.Ainf
