-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Dependency50.P26.network_recursiveNormalization
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T19:09:59.057404+00:00
-- url     : https://prove2.me/submissions/e2f2fbaa-85ac-4587-97cd-436d4607cd0b

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P26
import Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P26_network_lastNormalization
noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

open QAlgorithms

attribute [local instance] Classical.decEq Classical.propDecidable

namespace QAlgorithms.Papers.Independent.Dependency50.P26

lemma S173B_all (s : Signature) (net : MemoryNetwork s) :
    ∀ j, Normalized s j (net.choi j) := by
  intro j
  induction j with
  | zero =>
    show net.choi 0 = 1
    ext a b
    have h1 := net.initial_memory
    simp only [MemoryNetwork.choi, traceLeft, MemoryNetwork.retained, Matrix.of_apply, and_self]
    have : ∀ x : Fin (net.memory 0), x.val = 0 := fun x => by have := x.isLt; omega
    simp only [this, if_true, Finset.sum_const, Finset.card_univ, Fintype.card_fin, h1]
    have hab : a = b := Subsingleton.elim (α := Unit) a b
    simp [Matrix.one_apply, hab]
  | succ n ih =>
    obtain ⟨hp, ht⟩ := network_lastNormalization s net n
    exact ⟨hp, net.choi n, ih, ht⟩

end QAlgorithms.Papers.Independent.Dependency50.P26

open QAlgorithms.Papers.Independent.Dependency50.P26 in
theorem solution (s : QAlgorithms.Papers.Independent.Dependency50.P26.Signature)
    (net : QAlgorithms.Papers.Independent.Dependency50.P26.MemoryNetwork s)
    (n : ℕ) (hn : 0 < n) :
    Normalized s n (net.choi n) ∧
      ∀ j, j ≤ n → Normalized s j (net.choi j) :=
  ⟨S173B_all s net n, fun j _ => S173B_all s net j⟩
