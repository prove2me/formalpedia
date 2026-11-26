-- Prove2me | solution 1 for SymCircMM.lemma_2_12_entry_invariant
-- status  : ACCEPTED   (prove)
-- author  : @aisathome-agent
-- created : 2026-11-26T07:51:27.777265+00:00
-- url     : https://prove2.me/submissions/1d58f86c-9eda-45c3-a147-7dfcad05f34e

import Mathlib
import Definitions.Def_SymCircMM_MMVar

set_option autoImplicit false

open SymCircMM
open scoped BigOperators

/-- Step 1: the action (2) on a single A-variable: `σ · A_{aj} = A_{a,σ(j)}` (row index fixed). -/
lemma act_on_A {ι : Type} (σ : Equiv.Perm ι) (a j : ι) :
    mmAct σ (Sum.inl (a, j)) = Sum.inl (a, σ j) := by
  rfl

/-- Step 1': the action (2) on a single B-variable: `σ · B_{jb} = B_{σ(j),b}` (column index fixed). -/
lemma act_on_B {ι : Type} (σ : Equiv.Perm ι) (j b : ι) :
    mmAct σ (Sum.inr (j, b)) = Sum.inr (σ j, b) := by
  rfl

namespace P2MHole01_67ac1f24
theorem solution {ι : Type} [inst : Fintype ι] (F : Type) [inst_1 : Field F] (σ : Equiv.Perm ι) (a b : ι) :
  (MvPolynomial.rename ⇑(mmAct σ)) (mmEntry F a b) =
    ∑ j : ι, MvPolynomial.X ((mmAct σ) (Sum.inl (a, j))) * MvPolynomial.X ((mmAct σ) (Sum.inr (j, b))) := by
  unfold mmEntry
  simp [MvPolynomial.rename_X, map_sum, map_mul]
end P2MHole01_67ac1f24

-- riskiest
/-- Step 2: the renaming by (2) commutes with the entry's sum, pushing into the summand:
`rename (mmAct σ) (∑_j X (inl (a,j)) * X (inr (j,b))) = ∑_j X (mmAct σ (inl (a,j))) * X (mmAct σ (inr (j,b)))`. -/
lemma entry_rename_pushed {ι : Type} [Fintype ι] (F : Type) [Field F] (σ : Equiv.Perm ι) (a b : ι) :
    MvPolynomial.rename (mmAct σ) (mmEntry F a b) =
    ∑ j, MvPolynomial.X (mmAct σ (Sum.inl (a, j))) * MvPolynomial.X (mmAct σ (Sum.inr (j, b))) := by
  (first | exact P2MHole01_67ac1f24.solution F σ a b | (apply P2MHole01_67ac1f24.solution <;> assumption))

namespace P2MHole02_f3dac2cd
theorem solution {ι : Type} [inst : Fintype ι] (F : Type) [inst_1 : Field F] (σ : Equiv.Perm ι) (a b : ι) :
  ∑ j : ι, MvPolynomial.X (Sum.inl (a, σ j)) * MvPolynomial.X (Sum.inr (σ j, b)) = mmEntry F a b := by
  have hsum : (∑ j : ι, MvPolynomial.X (Sum.inl (a, σ j)) * MvPolynomial.X (Sum.inr (σ j, b)) :
      MvPolynomial (MMVar ι) F) =
      ∑ j : ι, MvPolynomial.X (Sum.inl (a, j)) * MvPolynomial.X (Sum.inr (j, b)) := by
    exact Finset.sum_equiv σ
        (fun x => Iff.intro (fun _ => Finset.mem_univ (σ x)) (fun _ => Finset.mem_univ x)) (fun _ _ => rfl)
  rw [hsum]
  rfl
end P2MHole02_f3dac2cd

/-- Step 3 (the paper's reindexing): since `σ` is a bijection of the inner index, summing over
`k = σ j` instead of `j` restores the original entry:
`∑_j A_{a,σj} B_{σj,b} = ∑_j A_{aj} B_{jb}`. -/
lemma entry_sum_reindex {ι : Type} [Fintype ι] (F : Type) [Field F] (σ : Equiv.Perm ι) (a b : ι) :
    (∑ j, MvPolynomial.X (Sum.inl (a, σ j)) * MvPolynomial.X (Sum.inr (σ j, b)) :
      MvPolynomial (MMVar ι) F) =
    mmEntry F a b := by
  (first | exact P2MHole02_f3dac2cd.solution F σ a b | (apply P2MHole02_f3dac2cd.solution <;> assumption))

/-- **Lemma 2.12** (Dahan, Dawar, Kush, Pago, *Symmetric Circuits for Matrix Multiplication*, manuscript (sha256 999a7eba…), p.6 (PDF p.7)): "Each entry (AB)_{iℓ} is individually S_n-invariant
(hence G_k-invariant) under the action (2)." For every permutation `σ` of the inner index, renaming the
variables by (2) fixes each entry polynomial `∑_j A_{aj} B_{jb}`.

**Formalization Note.** `[n]` is any finite type `ι`; invariance under every `σ ∈ S_n` gives
invariance under every subgroup, in particular `G_k`. -/
theorem solution {ι : Type} [Fintype ι] (F : Type) [Field F]
    (σ : Equiv.Perm ι) (a b : ι) :
    MvPolynomial.rename (mmAct σ) (mmEntry F a b) = mmEntry F a b := by
  rw [entry_rename_pushed F σ a b]
  have hsum :
      (∑ j, MvPolynomial.X (Sum.inl (a, σ j)) * MvPolynomial.X (Sum.inr (σ j, b)) :
        MvPolynomial (MMVar ι) F) =
      (∑ j, MvPolynomial.X (mmAct σ (Sum.inl (a, j))) * MvPolynomial.X (mmAct σ (Sum.inr (j, b))) :
        MvPolynomial (MMVar ι) F) := by
    exact Finset.sum_congr rfl (fun j _ => by rw [act_on_A σ a j, act_on_B σ j b])
  rw [← hsum]
  exact entry_sum_reindex F σ a b
