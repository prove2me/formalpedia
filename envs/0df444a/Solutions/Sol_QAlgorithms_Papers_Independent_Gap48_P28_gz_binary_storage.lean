-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Gap48.P28.gz_binary_storage
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T23:58:35.545499+00:00
-- url     : https://prove2.me/submissions/e11cc049-2622-42a0-89d4-afbcb66816de

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P28
noncomputable section

open QAlgorithms.Papers.Independent.Gap48.P28

open scoped Matrix Kronecker ComplexConjugate

theorem g74l_natToBits_inj {m a b : ℕ} (ha : a < 2 ^ m) (hb : b < 2 ^ m)
    (h : QAlgorithms.natToBits m a = QAlgorithms.natToBits m b) : a = b := by
  unfold QAlgorithms.natToBits at h
  have := congrArg Fin.val ((QAlgorithms.bitsEquivFin m).symm.injective h)
  simpa [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] using this

theorem solution (n d : ℕ) (hn : 1 ≤ n) (hd : 1 ≤ d) :
    Function.Injective (@gzBinaryCode n d) ∧
    Fintype.card (Fin d × Fin d × Fin (Nat.clog 2 (n + 1))) =
      d ^ 2 * Nat.clog 2 (n + 1) := by
  refine ⟨?_, by simp [Fintype.card_prod]; ring⟩
  intro p q hpq
  apply Subtype.ext
  funext r c
  apply Fin.ext
  have hlt : ∀ x : Fin (n + 1), x.val < 2 ^ Nat.clog 2 (n + 1) := fun x =>
    lt_of_lt_of_le x.isLt (Nat.le_pow_clog (by norm_num) _)
  apply g74l_natToBits_inj (hlt _) (hlt _)
  funext b
  exact congrFun hpq (r, c, b)

end
