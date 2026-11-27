-- Prove2me | solution 1 for PositivityTheory.SiegelWeilFormula.KAway.det_idem_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T05:24:24.546667+00:00
-- url     : https://prove2.me/submissions/a6c95178-b6c2-4e9f-aeb2-06ea4849d64c

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_SiegelWeilFormula_AwayActions_DecAlg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped Matrix
open Matrix
open PositivityTheory PositivityTheory.SiegelWeilFormula PositivityTheory.SiegelWeilFormula.KAway
variable {R : Type} [CommRing R] {n : ℕ}
variable (c : R →+* R) (ε : ℤ)
namespace PositivityTheory.SiegelWeilFormula.KAway
theorem _root_.solution {ι : Type} [Fintype ι] (f : ι → R) (hf : ∀ i, f i * f i = f i) (ho : ∀ i j, i ≠ j → f i * f j = 0)
    (h1 : ∑ i, f i = 1) (M : ι → Matrix (Fin n) (Fin n) R) : (∑ i, f i • M i).det = ∑ i, f i * (M i).det := by
  cases n with
  | zero => simp [Matrix.det_fin_zero, h1]
  | succ m =>
    have hX : ∀ i, f i • (∑ j, f j • M j) = f i • M i := by
      intro i
      rw [Finset.smul_sum, Finset.sum_eq_single i]
      · rw [smul_smul, hf]
      · intro j _ hj
        rw [smul_smul, ho i j (Ne.symm hj), zero_smul]
      · intro h
        exact absurd (Finset.mem_univ i) h
    have hd : ∀ i (Y : Matrix (Fin (m + 1)) (Fin (m + 1)) R), (f i • Y).det = f i * Y.det := by
      intro i Y
      rw [Matrix.det_smul, Fintype.card_fin, IsIdempotentElem.pow_succ_eq m (hf i)]
    calc (∑ i, f i • M i).det = (∑ i, f i) * (∑ i, f i • M i).det := by rw [h1, one_mul]
      _ = ∑ i, f i * (∑ j, f j • M j).det := Finset.sum_mul _ _ _
      _ = ∑ i, f i * (M i).det := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [← hd, hX, hd]
end PositivityTheory.SiegelWeilFormula.KAway
