-- Prove2me | solution 1 for ShiTensor.accept_weight_or_form_eq_count_form_three_copies
-- status  : ACCEPTED   (prove)
-- author  : @Goku
-- created : 2026-09-15T02:43:26.563575+00:00
-- url     : https://prove2.me/submissions/5cf7aa64-6e6b-4e3a-a784-9303bbc610a8

/-
# Bridge: three-copy majority accept weight, `(M+M)+M` OR-form = `M+(M+M)` count-form

A standalone index-bookkeeping identity.  Its left sum is the right-hand side of
`ShiTensor.accept_weight_majority_readout_three_copies` (association `(M + M) + M`, acceptance
predicate spelled as the OR of the three pairwise ANDs).  Its right sum is the left-hand side of
`ShiTensor.tensor_majority_three_accept_weight_closed_form` specialised to `P = Q = M`,
`psi = phi = chi = A`, `f = g = h = fun a => a out` (association `M + (M + M)`, acceptance
predicate spelled as `2 <= card`).

Three mismatches are bridged: the associativity of the wire count, the three block wire
addresses, and the shape of the majority predicate.  Nothing here assumes normalisation,
unitarity, or any circuit structure: `A` is an arbitrary `QState M`.
-/
import Definitions.Def_ShiTensor_Core

set_option autoImplicit false

open ShiShallow ShiTensor

/-! ### The reindexing of joint bit strings along `Nat.add_assoc M M M` -/

/-- Read a `(M + M) + M` bit string as a `M + (M + M)` bit string. -/
private def shiAmpB_map (M : ℕ) (v : Bits (M + M + M)) : Bits (M + (M + M)) :=
  fun x => v (Fin.cast (Nat.add_assoc M M M).symm x)

private lemma shiAmpB_bij (M : ℕ) : Function.Bijective (shiAmpB_map M) := by
  constructor
  · intro v w hvw
    funext i
    exact congrFun hvw (Fin.cast (Nat.add_assoc M M M) i)
  · intro w
    refine ⟨fun i => w (Fin.cast (Nat.add_assoc M M M) i), ?_⟩
    funext x
    rfl

/-! ### The three block wire addresses -/

private lemma shiAmpB_i1 (M : ℕ) (i : Fin M) :
    Fin.cast (Nat.add_assoc M M M).symm (Fin.castAdd (M + M) i)
      = Fin.castAdd M (Fin.castAdd M i) := by
  first
  | rfl
  | (apply Fin.ext
     first
     | (simp; done)
     | (simp only [Fin.val_cast, Fin.val_castAdd]; done)
     | omega)

private lemma shiAmpB_i2 (M : ℕ) (i : Fin M) :
    Fin.cast (Nat.add_assoc M M M).symm (Fin.natAdd M (Fin.castAdd M i))
      = Fin.castAdd M (Fin.natAdd M i) := by
  first
  | rfl
  | (apply Fin.ext
     first
     | (simp; done)
     | (simp only [Fin.val_cast, Fin.val_natAdd, Fin.val_castAdd]; done)
     | omega)

private lemma shiAmpB_i3 (M : ℕ) (i : Fin M) :
    Fin.cast (Nat.add_assoc M M M).symm (Fin.natAdd M (Fin.natAdd M i))
      = Fin.natAdd (M + M) i := by
  apply Fin.ext
  first
  | (simp; done)
  | (simp; omega)
  | (simp only [Fin.val_cast, Fin.val_natAdd]; omega)
  | (simp [Nat.add_assoc]; done)
  | omega

/-! ### The three block projections agree under the reindexing -/

private lemma shiAmpB_b1 (M : ℕ) (v : Bits (M + M + M)) :
    leftBits (shiAmpB_map M v) = leftBits (leftBits v) := by
  funext i
  exact congrArg v (shiAmpB_i1 M i)

private lemma shiAmpB_b2 (M : ℕ) (v : Bits (M + M + M)) :
    leftBits (rightBits (shiAmpB_map M v)) = rightBits (leftBits v) := by
  funext i
  exact congrArg v (shiAmpB_i2 M i)

private lemma shiAmpB_b3 (M : ℕ) (v : Bits (M + M + M)) :
    rightBits (rightBits (shiAmpB_map M v)) = rightBits v := by
  funext i
  exact congrArg v (shiAmpB_i3 M i)

/-! ### The majority truth table -/

private lemma shiAmpB_truth (a b c : Bool) :
    (((a && b) || ((b && c) || (a && c))) = true)
      ↔ 2 ≤ (if a then (1 : ℕ) else 0) + (if b then (1 : ℕ) else 0)
            + (if c then (1 : ℕ) else 0) := by
  cases a <;> cases b <;> cases c <;> (first | decide | simp | rfl)

/-! ### The amplitude of the reindexed string -/

private lemma shiAmpB_amp (M : ℕ) (A : QState M) (v : Bits (M + M + M)) :
    tensor (tensor A A) A v = tensor A (tensor A A) (shiAmpB_map M v) := by
  first
  | (simp only [ShiTensor.tensor, shiAmpB_b1 M v, shiAmpB_b2 M v, shiAmpB_b3 M v]
     all_goals (first | ring | rw [mul_assoc] | rfl | ac_rfl))
  | (unfold ShiTensor.tensor
     dsimp only
     rw [shiAmpB_b1 M v, shiAmpB_b2 M v, shiAmpB_b3 M v]
     ring)

/-! ### The bridge -/

/-- **Bridge.**  The three-copy majority accept weight computed on `(M + M) + M` wires with the
acceptance event spelled as the OR of the three pairwise ANDs of the readout wire equals the same
weight computed on `M + (M + M)` wires with the acceptance event spelled as "at least two of the
three readouts are `true`".

The left sum is the right-hand side of
`ShiTensor.accept_weight_majority_readout_three_copies` (with `A = runLayered c Φ`).
The right sum is the left-hand side of
`ShiTensor.tensor_majority_three_accept_weight_closed_form` at `P = Q = M`,
`ψ = φ = χ = A` and `f = g = h = fun a => a out`.

No normalisation or unitarity hypothesis is needed: `A : QState M` is arbitrary. -/
theorem solution {M : ℕ} (out : Fin M) (A : QState M) :
    (∑ v : Bits (M + M + M),
        if ((v (Fin.castAdd M (Fin.castAdd M out)) && v (Fin.castAdd M (Fin.natAdd M out)))
            || ((v (Fin.castAdd M (Fin.natAdd M out)) && v (Fin.natAdd (M + M) out))
              || (v (Fin.castAdd M (Fin.castAdd M out)) && v (Fin.natAdd (M + M) out))))
        then ‖tensor (tensor A A) A v‖ ^ 2 else 0)
      = ∑ y : Bits (M + (M + M)),
          (if 2 ≤ (if leftBits y out then (1 : ℕ) else 0)
                + (if leftBits (rightBits y) out then (1 : ℕ) else 0)
                + (if rightBits (rightBits y) out then (1 : ℕ) else 0)
            then ‖tensor A (tensor A A) y‖ ^ 2 else 0) := by
  refine Fintype.sum_bijective (shiAmpB_map M) (shiAmpB_bij M) _ _ ?_
  intro v
  have e1 : v (Fin.castAdd M (Fin.castAdd M out)) = leftBits (leftBits v) out := rfl
  have e2 : v (Fin.castAdd M (Fin.natAdd M out)) = rightBits (leftBits v) out := rfl
  have e3 : v (Fin.natAdd (M + M) out) = rightBits v out := rfl
  simp only [e1, e2, e3, shiAmpB_b1 M v, shiAmpB_b2 M v, shiAmpB_b3 M v]
  refine if_congr (shiAmpB_truth _ _ _) ?_ rfl
  first
  | (rw [shiAmpB_amp M A v]; done)
  | (exact congrArg (fun z : ℂ => ‖z‖ ^ 2) (shiAmpB_amp M A v))
