-- Prove2me | solution 1 for ThreeSum.LocalCoverBounds.pow_le_choose_mul
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-10-14T14:43:48.06983+00:00
-- url     : https://prove2.me/submissions/ca3a1c50-8b41-4956-a248-ef6d263b307b

import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.Floor.Div
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.NumberTheory.Bertrand
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false

section


/-!
# Finite numerical bounds for the local cover

The graph degree bound follows from exact finite cardinalities: the degree
is no larger than the number of vertices, while vertices times degree equal
outputs times representations per output.  This avoids any approximation
of factorials.  The prime-interval and normalized first-moment estimates
are stated explicitly in terms of the concrete binomial coefficients.
-/

namespace ThreeSum.LocalCoverBounds

open scoped BigOperators






/-- Choose one coordinate from each of `r` disjoint blocks of size `c`. This
is a direct finite injection giving an exact binomial lower bound. -/
theorem pow_le_choose_mul_sourceProof (c r : ℕ) : c ^ r ≤ (c * r).choose r := by
  let graph (f : Fin r → Fin c) : Finset (Fin r × Fin c) :=
    Finset.univ.image (fun i => (i, f i))
  have hgcard (f : Fin r → Fin c) : (graph f).card = r := by
    change (Finset.univ.image (fun i : Fin r => (i, f i))).card = r
    rw [Finset.card_image_of_injective]
    · simp
    · intro i j he
      exact congrArg Prod.fst he
  have hginj : Function.Injective graph := by
    intro f g he
    funext i
    have hm : (i, f i) ∈ graph g := by
      rw [← he]
      exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
    obtain ⟨j, _, hj⟩ := Finset.mem_image.mp hm
    have hji : j = i := congrArg Prod.fst hj
    subst j
    exact (congrArg Prod.snd hj).symm
  have hcount : (Finset.univ : Finset (Fin r → Fin c)).card ≤
      ((Finset.univ : Finset (Fin r × Fin c)).powersetCard r).card := by
    apply Finset.card_le_card_of_injOn graph
    · intro f _
      exact Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hgcard f⟩
    · intro f _ g _ he
      exact hginj he
  simpa [Finset.card_powersetCard, Nat.mul_comm] using hcount
































































































/-! ## A deterministic selected prime -/















































































/-! ## Exact integer rounding of the separable bucket cap -/































/-! ## The actual local parameters at `L=512*h` -/





























































end ThreeSum.LocalCoverBounds

end


theorem solution : ∀ (c r : Nat),
  @LE.le.{0} Nat instLENat
    (@HPow.hPow.{0, 0, 0} Nat Nat Nat
      (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid))) c r)
    ((@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) c r).choose r) := by
  exact @ThreeSum.LocalCoverBounds.pow_le_choose_mul_sourceProof

#print axioms solution
