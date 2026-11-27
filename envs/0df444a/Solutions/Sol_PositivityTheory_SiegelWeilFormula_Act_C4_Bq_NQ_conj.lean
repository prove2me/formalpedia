-- Prove2me | solution 1 for PositivityTheory.SiegelWeilFormula.Act.C4.Bq.NQ.conj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T05:20:55.86492+00:00
-- url     : https://prove2.me/submissions/823c277f-f72c-4b72-97d6-ae4e8b3a4a22

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_SiegelWeilFormula_ParabolicBlockForms_UpperBlockRankOneUpdate

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PositivityTheory PositivityTheory.SiegelWeilFormula PositivityTheory.SiegelWeilFormula.Act PositivityTheory.SiegelWeilFormula.Act.C4 PositivityTheory.SiegelWeilFormula.Act.C4.Bq
open Matrix
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
variable {ι R : Type} [Fintype ι] [DecidableEq ι] [CommRing R]
namespace PositivityTheory.SiegelWeilFormula.Act.C4.Bq
namespace NQ
theorem _root_.solution {x y : ι} (hxy : x ≠ y) {J J' M : Matrix ι ι R} (hJ : Pad x y J) (hJ' : Pad x y J')
    (hJJ : J * J' = 1) (hM : NQ x y M) : NQ x y (J * M * J') := by
  have e : J * M * J' - 1 = J * (M - 1) * J' := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hJJ]
  have hJx : ∀ r, r ≠ x → J r x = 0 := fun r hr => by
    rw [hJ r x (Or.inr (Or.inr (Or.inl rfl))), Matrix.one_apply_ne hr]
  have hJ'x : ∀ l, l ≠ x → J' l x = 0 := fun l hl => by
    rw [hJ' l x (Or.inr (Or.inr (Or.inl rfl))), Matrix.one_apply_ne hl]
  have hJ'y : ∀ c, c ≠ y → J' y c = 0 := fun c hc => by
    rw [hJ' y c (Or.inr (Or.inl rfl)), Matrix.one_apply_ne (Ne.symm hc)]
  refine ⟨fun k => ?_, fun k l hlx hly hkx => ?_⟩
  · rw [e, Matrix.mul_apply]
    refine Finset.sum_eq_zero fun m _ => ?_
    rw [Matrix.mul_apply, Finset.sum_mul]
    refine Finset.sum_eq_zero fun m' _ => ?_
    by_cases hm : m = x
    · subst hm; rw [hM.1 m', mul_zero, zero_mul]
    · rw [hJ'x m hm, mul_zero]
  · rw [e, Matrix.mul_apply]
    refine Finset.sum_eq_zero fun m _ => ?_
    rw [Matrix.mul_apply, Finset.sum_mul]
    refine Finset.sum_eq_zero fun m' _ => ?_
    by_cases hm : m = y
    · subst hm; rw [hJ'y l hly, mul_zero]
    · by_cases hmx : m = x
      · subst hmx; rw [hM.1 m', mul_zero, zero_mul]
      · by_cases hm'x : m' = x
        · subst hm'x; rw [hJx k hkx, zero_mul, zero_mul]
        · rw [hM.2 m' m hmx hm hm'x, mul_zero, zero_mul]
end NQ
end PositivityTheory.SiegelWeilFormula.Act.C4.Bq
