-- Prove2me | solution 1 for ShiShallow.exists_layout_bijection
-- status  : ACCEPTED   (prove)
-- author  : @Goku
-- created : 2026-09-14T06:25:27.332823+00:00
-- url     : https://prove2.me/submissions/93363cc5-09d1-4993-879c-b9dda84dabf5

import Definitions.Def_ShiShallow_Core

set_option autoImplicit false

open ShiShallow

/-!
# The copy-major / role-major wire bijection

`W := n + (wit + (anc + 1))` is one verifier copy (`input | witness | ancilla | output`).
The copy-major register is `Fin (3 * W + 1)` (`copy1 | copy2 | copy3 | scratch`), the
role-major register is `Fin (n + (3 * wit + ((2 * n + 3 * anc + 3) + 1)))`
(`input | witness | ancilla | output`).  The two have the same cardinality, but a bare
cardinality bijection is useless: what the three-copy majority verifier needs is a bijection
that carries every copy-major block onto a *contiguous* role-major block at a *named* offset.

`solution` produces such a bijection together with the exact image of each of the thirteen
copy-major blocks.  The role-major ancilla block is laid out as
`anc1 | out1 | in2 | anc2 | out2 | in3 | anc3 | out3`, of total size `2 * n + 3 * anc + 3`.

The map is defined on `Fin.val` by a seven-piece affine formula (no `/`, no `%`); the
thirteen block laws are restrictions of those seven pieces.
-/

/-- The copy-major → role-major wire relabelling, at the level of `Nat`.

The seven pieces are, in order: `in1 ++ wit1`; `anc1 ++ out1 ++ in2`; `wit2`;
`anc2 ++ out2 ++ in3`; `wit3`; `anc3 ++ out3`; `scratch`. -/
private def shiBij_f (n wit anc v : ℕ) : ℕ :=
  if v < n + wit then
    v
  else if v < 2 * n + wit + anc + 1 then
    (n + 3 * wit) + (v - (n + wit))
  else if v < 2 * n + 2 * wit + anc + 1 then
    (n + wit) + (v - (2 * n + wit + anc + 1))
  else if v < 3 * n + 2 * wit + 2 * anc + 2 then
    (2 * n + 3 * wit + anc + 1) + (v - (2 * n + 2 * wit + anc + 1))
  else if v < 3 * n + 3 * wit + 2 * anc + 2 then
    (n + 2 * wit) + (v - (3 * n + 2 * wit + 2 * anc + 2))
  else if v < 3 * n + 3 * wit + 3 * anc + 3 then
    (3 * n + 3 * wit + 2 * anc + 2) + (v - (3 * n + 3 * wit + 2 * anc + 2))
  else
    3 * n + 3 * wit + 3 * anc + 3

private theorem shiBij_f_lt (n wit anc v : ℕ)
    (hv : v < 3 * (n + (wit + (anc + 1))) + 1) :
    shiBij_f n wit anc v < n + (3 * wit + ((2 * n + 3 * anc + 3) + 1)) := by
  first
    | (unfold shiBij_f
       split_ifs <;> omega
       done)
    | (simp only [shiBij_f]
       split_ifs <;> omega
       done)

private theorem shiBij_f_inj (n wit anc : ℕ) {a b : ℕ}
    (ha : a < 3 * (n + (wit + (anc + 1))) + 1)
    (hb : b < 3 * (n + (wit + (anc + 1))) + 1)
    (hab : shiBij_f n wit anc a = shiBij_f n wit anc b) : a = b := by
  first
    | (unfold shiBij_f at hab
       split_ifs at hab <;> omega
       done)
    | (simp only [shiBij_f] at hab
       split_ifs at hab <;> omega
       done)

/-- The relabelling itself. -/
private def shiBij_sigma (n wit anc : ℕ) :
    Fin (3 * (n + (wit + (anc + 1))) + 1) →
      Fin (n + (3 * wit + ((2 * n + 3 * anc + 3) + 1))) :=
  fun v => ⟨shiBij_f n wit anc v.val, shiBij_f_lt n wit anc v.val v.isLt⟩

private theorem shiBij_sigma_val (n wit anc : ℕ)
    (v : Fin (3 * (n + (wit + (anc + 1))) + 1)) :
    (shiBij_sigma n wit anc v).val = shiBij_f n wit anc v.val := rfl

private theorem shiBij_sigma_bijective (n wit anc : ℕ) :
    Function.Bijective (shiBij_sigma n wit anc) := by
  rw [Fintype.bijective_iff_injective_and_card]
  refine ⟨?_, ?_⟩
  · intro a b hab
    have hv : shiBij_f n wit anc a.val = shiBij_f n wit anc b.val := by
      first
        | (exact congrArg Fin.val hab
           done)
        | (rw [← shiBij_sigma_val, ← shiBij_sigma_val, hab]
           done)
        | (simpa only [shiBij_sigma_val] using congrArg Fin.val hab
           done)
    have hval : a.val = b.val := shiBij_f_inj n wit anc a.isLt b.isLt hv
    first
      | (exact Fin.val_injective hval
         done)
      | (exact Fin.ext hval
         done)
      | (exact Fin.eq_of_val_eq hval
         done)
  · simp only [Fintype.card_fin]
    omega

/-- **Block-respecting copy-major → role-major wire bijection.**

There is a bijection `σ` from the copy-major register
`Fin (3 * W + 1)`, `W = n + (wit + (anc + 1))`, onto the role-major register
`Fin (n + (3 * wit + ((2 * n + 3 * anc + 3) + 1)))`, which maps each of the thirteen
copy-major blocks onto a contiguous role-major block, order-preservingly inside the block,
at the offsets listed below.  In particular copy `k`'s witness block lands on the role-major
witness block at offset `k * wit` (`k = 0, 1, 2`), copy 1's input block is the role-major
input block, and the scratch wire is the role-major output wire. -/
theorem solution (n wit anc : ℕ) :
    ∃ σ : Fin (3 * (n + (wit + (anc + 1))) + 1)
        → Fin (n + (3 * wit + ((2 * n + 3 * anc + 3) + 1))),
      Function.Bijective σ
      -- copy 1 input  ↦ role input block, offset 0
      ∧ (∀ (v : Fin (3 * (n + (wit + (anc + 1))) + 1)) (j : ℕ), j < n →
          v.val = j → (σ v).val = j)
      -- copy 1 witness ↦ role witness block, offset 0 * wit
      ∧ (∀ (v : Fin (3 * (n + (wit + (anc + 1))) + 1)) (j : ℕ), j < wit →
          v.val = n + j → (σ v).val = n + j)
      -- copy 1 ancilla ↦ role ancilla block, offset 0
      ∧ (∀ (v : Fin (3 * (n + (wit + (anc + 1))) + 1)) (j : ℕ), j < anc →
          v.val = n + wit + j → (σ v).val = n + 3 * wit + j)
      -- copy 1 output  ↦ role ancilla block, offset anc
      ∧ (∀ v : Fin (3 * (n + (wit + (anc + 1))) + 1),
          v.val = n + wit + anc → (σ v).val = n + 3 * wit + anc)
      -- copy 2 input   ↦ role ancilla block, offset anc + 1
      ∧ (∀ (v : Fin (3 * (n + (wit + (anc + 1))) + 1)) (j : ℕ), j < n →
          v.val = (n + (wit + (anc + 1))) + j →
          (σ v).val = n + 3 * wit + anc + 1 + j)
      -- copy 2 witness ↦ role witness block, offset 1 * wit
      ∧ (∀ (v : Fin (3 * (n + (wit + (anc + 1))) + 1)) (j : ℕ), j < wit →
          v.val = (n + (wit + (anc + 1))) + n + j → (σ v).val = n + wit + j)
      -- copy 2 ancilla ↦ role ancilla block, offset n + anc + 1
      ∧ (∀ (v : Fin (3 * (n + (wit + (anc + 1))) + 1)) (j : ℕ), j < anc →
          v.val = (n + (wit + (anc + 1))) + n + wit + j →
          (σ v).val = 2 * n + 3 * wit + anc + 1 + j)
      -- copy 2 output  ↦ role ancilla block, offset n + 2 * anc + 1
      ∧ (∀ v : Fin (3 * (n + (wit + (anc + 1))) + 1),
          v.val = (n + (wit + (anc + 1))) + n + wit + anc →
          (σ v).val = 2 * n + 3 * wit + 2 * anc + 1)
      -- copy 3 input   ↦ role ancilla block, offset n + 2 * anc + 2
      ∧ (∀ (v : Fin (3 * (n + (wit + (anc + 1))) + 1)) (j : ℕ), j < n →
          v.val = 2 * (n + (wit + (anc + 1))) + j →
          (σ v).val = 2 * n + 3 * wit + 2 * anc + 2 + j)
      -- copy 3 witness ↦ role witness block, offset 2 * wit
      ∧ (∀ (v : Fin (3 * (n + (wit + (anc + 1))) + 1)) (j : ℕ), j < wit →
          v.val = 2 * (n + (wit + (anc + 1))) + n + j → (σ v).val = n + 2 * wit + j)
      -- copy 3 ancilla ↦ role ancilla block, offset 2 * n + 2 * anc + 2
      ∧ (∀ (v : Fin (3 * (n + (wit + (anc + 1))) + 1)) (j : ℕ), j < anc →
          v.val = 2 * (n + (wit + (anc + 1))) + n + wit + j →
          (σ v).val = 3 * n + 3 * wit + 2 * anc + 2 + j)
      -- copy 3 output  ↦ role ancilla block, offset 2 * n + 3 * anc + 2
      ∧ (∀ v : Fin (3 * (n + (wit + (anc + 1))) + 1),
          v.val = 2 * (n + (wit + (anc + 1))) + n + wit + anc →
          (σ v).val = 3 * n + 3 * wit + 3 * anc + 2)
      -- scratch wire   ↦ role output wire
      ∧ (∀ v : Fin (3 * (n + (wit + (anc + 1))) + 1),
          v.val = 3 * (n + (wit + (anc + 1))) →
          (σ v).val = 3 * n + 3 * wit + 3 * anc + 3) := by
  refine ⟨shiBij_sigma n wit anc, shiBij_sigma_bijective n wit anc,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals
    first
      | (intro v j hj hv
         rw [shiBij_sigma_val]
         unfold shiBij_f
         split_ifs <;> omega
         done)
      | (intro v j hj hv
         show shiBij_f n wit anc v.val = _
         unfold shiBij_f
         split_ifs <;> omega
         done)
      | (intro v j hj hv
         rw [shiBij_sigma_val]
         simp only [shiBij_f]
         split_ifs <;> omega
         done)
      | (intro v hv
         rw [shiBij_sigma_val]
         unfold shiBij_f
         split_ifs <;> omega
         done)
      | (intro v hv
         show shiBij_f n wit anc v.val = _
         unfold shiBij_f
         split_ifs <;> omega
         done)
      | (intro v hv
         rw [shiBij_sigma_val]
         simp only [shiBij_f]
         split_ifs <;> omega
         done)
