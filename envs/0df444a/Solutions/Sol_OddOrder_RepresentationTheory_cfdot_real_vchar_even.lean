-- Prove2me | solution 1 for OddOrder.RepresentationTheory.cfdot_real_vchar_even
-- status  : ACCEPTED   (prove)
-- author  : @burkh4rt
-- created : 2026-11-12T06:19:44.972927+00:00
-- url     : https://prove2.me/submissions/154edf74-5881-4c89-a70d-68ce1b13f361

/-
Copyright (c) 2026 Yawara ISHIDA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Peterfalvi/S09_ParityPrimitive.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_BrauerPermutationUnconditional
import Definitions.Def_OddOrder_Peterfalvi_S08_CoherenceCorePart1

-- ===== OddOrder/Peterfalvi/S09_ParityPrimitive.lean =====
namespace OddOrder.RepresentationTheory

variable {G : Type*} [Group G] [Finite G]

/-- **The conjugation involution's only fixed point is the trivial character** (odd order).
Combines
`IrreducibleCharacter.conjPerm_eq_self_iff` (fixed point ↔ real) with Peterfalvi (1.1)
`not_isReal_of_ne_trivial_of_odd_card'` (odd order ⟹ only the trivial irreducible is real).  This is
the self-conjugate case in the (7.9) parity `cfdot_real_vchar_even` orbit-pairing argument. -/
theorem conjPerm_eq_self_iff_eq_trivial_of_odd (hodd : Odd (Nat.card G))
    (χ : IrreducibleCharacter G) :
    IrreducibleCharacter.conjPerm G χ = χ ↔ χ = trivialIrreducibleCharacter G := by
  rw [IrreducibleCharacter.conjPerm_eq_self_iff]
  constructor
  · intro hreal
    by_contra hne
    exact not_isReal_of_ne_trivial_of_odd_card' hodd hne hreal
  · rintro rfl
    have : (trivialIrreducibleCharacter G : ClassFunction G ℂ) = trivialClassFunction G := rfl
    rw [this]
    exact trivialClassFunction_isReal

section InnerConj

variable [Fintype G] [Invertible (Nat.card G : ℂ)]

omit [Finite G] in
/-- **Conjugation identity for the inner product**: `⟨φ, ψ̄⟩ = star ⟨φ̄, ψ⟩`.  Both sides equal
`⅟|G| ∑_g φ(g) ψ(g)` (unfolding `star` on the conjugates).  For **real** `φ` (`φ̄ = φ`) this gives
`⟨φ, ψ̄⟩ = star ⟨φ, ψ⟩`, the Fourier-coefficient symmetry used in the (7.9) parity argument. -/
theorem inner_conj_right (φ ψ : ClassFunction G ℂ) :
    ClassFunction.inner φ ψ.conj = star (ClassFunction.inner φ.conj ψ) := by
  have hstar_inv : star (⅟(Nat.card G : ℂ)) = ⅟(Nat.card G : ℂ) := by
    rw [invOf_eq_inv, star_inv₀, star_natCast]
  simp only [ClassFunction.inner_eq_inv_card_mul_innerSum, ClassFunction.innerSum,
    ClassFunction.conj_apply, star_mul', star_sum, hstar_inv, star_star]

/-- For a **real** virtual character `φ` and `χ ∈ Irr G`, the Fourier coefficient of the conjugate
`⟨φ, χ̄⟩` equals `⟨φ, χ⟩` (real, since `φ ∈ ℤ[Irr]`).  This makes the summand `⟨φ,χ⟩⟨ψ,χ⟩` invariant
under the conjugation involution `χ ↦ χ̄`. -/
theorem inner_conjPerm_eq_of_real {φ : ClassFunction G ℂ} (hφZ : φ ∈ ZIrr G)
    (hφR : ClassFunction.IsReal φ) (χ : IrreducibleCharacter G) :
    ClassFunction.inner φ (IrreducibleCharacter.conjPerm G χ : ClassFunction G ℂ) =
      ClassFunction.inner φ (χ : ClassFunction G ℂ) := by
  rw [IrreducibleCharacter.conjPerm_apply_coe, inner_conj_right, hφR]
  -- `⟨φ, χ⟩` is a real integer, so `star ⟨φ, χ⟩ = ⟨φ, χ⟩`.
  obtain ⟨m, hm⟩ := ClassFunction.inner_mem_ZIrr_int hφZ χ.property.mem_ZIrr
  rw [hm, star_intCast]

end InnerConj

section InvolutionParity

/-- **Parity via the conjugation involution.**  For an integer-valued function `h` on `Irr G`
invariant under the conjugation involution `χ ↦ χ̄`, the full sum `∑_χ h χ` is congruent mod `2` to
its value at the unique fixed point — the trivial character (`G` odd) — because every non-trivial
`χ` pairs with a distinct `χ̄` contributing `2 h χ ≡ 0`.  Formally `∑_χ h χ − h(1_G)` is even. -/
theorem sum_conjPerm_invariant_sub_trivial_even (hodd : Odd (Nat.card G))
    (h : IrreducibleCharacter G → ℤ)
    (hinv : ∀ χ, h (IrreducibleCharacter.conjPerm G χ) = h χ) :
    Even ((∑ χ : IrreducibleCharacter G, h χ) - h (trivialIrreducibleCharacter G)) := by
  classical
  -- `conjPerm` fixes the trivial character (it is real).
  have htriv_fix : IrreducibleCharacter.conjPerm G (trivialIrreducibleCharacter G) =
      trivialIrreducibleCharacter G :=
    (conjPerm_eq_self_iff_eq_trivial_of_odd hodd _).mpr rfl
  -- `conjPerm` is an involution: `conjPerm (conjPerm χ) = χ`.
  have hinvol : ∀ χ : IrreducibleCharacter G,
      IrreducibleCharacter.conjPerm G (IrreducibleCharacter.conjPerm G χ) = χ :=
    fun χ => IrreducibleCharacter.ext (by simp)
  -- `conjPerm χ = trivial ↔ χ = trivial` (involution).
  have hconj_triv : ∀ χ, IrreducibleCharacter.conjPerm G χ = trivialIrreducibleCharacter G ↔
      χ = trivialIrreducibleCharacter G := by
    intro χ
    constructor
    · intro hχ
      have h2 := congrArg (IrreducibleCharacter.conjPerm G) hχ
      rwa [hinvol, htriv_fix] at h2
    · rintro rfl; exact htriv_fix
  -- The difference is the sum over the non-trivial irreducibles.
  have hsplit : (∑ χ : IrreducibleCharacter G, h χ) - h (trivialIrreducibleCharacter G)
      = ∑ χ ∈ Finset.univ.erase (trivialIrreducibleCharacter G), h χ := by
    have hadd := Finset.sum_erase_add Finset.univ h
      (Finset.mem_univ (trivialIrreducibleCharacter G))
    linarith [hadd]
  rw [hsplit]
  -- In `ZMod 2`, the sum over non-trivial `χ` vanishes by the fixed-point-free involution `χ ↦ χ̄`.
  have h0 : ((∑ χ ∈ Finset.univ.erase (trivialIrreducibleCharacter G), h χ : ℤ) : ZMod 2) = 0 := by
    rw [Int.cast_sum]
    refine Finset.sum_involution (fun χ _ => IrreducibleCharacter.conjPerm G χ) ?_ ?_ ?_ ?_
    · intro χ _
      rw [hinv χ]
      exact CharTwo.add_self_eq_zero _
    · intro χ hχ _
      rw [Finset.mem_erase] at hχ
      exact fun heq => hχ.1 ((conjPerm_eq_self_iff_eq_trivial_of_odd hodd χ).mp heq)
    · intro χ hχ
      rw [Finset.mem_erase] at hχ ⊢
      exact ⟨fun heq => hχ.1 ((hconj_triv χ).mp heq), Finset.mem_univ _⟩
    · intro χ _
      exact hinvol χ
  rw [even_iff_two_dvd]
  exact_mod_cast (ZMod.intCast_zmod_eq_zero_iff_dvd _ 2).mp h0

end InvolutionParity

section Main

variable [Fintype G] [Invertible (Nat.card G : ℂ)]

open scoped Classical in
/-- **Peterfalvi (7.9) parity primitive** `cfdot_real_vchar_even`.  For two **real** virtual
characters `φ, ψ ∈ ℤ[Irr G]` over a group of **odd** order, the integer inner product `⟨φ, ψ⟩`
is congruent mod `2` to `⟨φ, 1_G⟩·⟨ψ, 1_G⟩`.  Via the Fourier expansion
`⟨φ, ψ⟩ = ∑_χ ⟨φ,χ⟩⟨ψ,χ⟩` (integer coefficients, `star` trivial), the summand is invariant under the
conjugation involution `χ ↦ χ̄` (`inner_conjPerm_eq_of_real`), whose only fixed point is the trivial
character (`conjPerm_eq_self_iff_eq_trivial_of_odd`); the involution-pairing parity
(`sum_conjPerm_invariant_sub_trivial_even`) leaves only the trivial term.

Returned in bundled form: the integer values `m = ⟨φ,ψ⟩`, `a = ⟨φ,1_G⟩`, `b = ⟨ψ,1_G⟩` together with
`Even (m − a·b)`.  In the (7.9) `hdelta_even` application `a = ⟨δ_i, 1_G⟩ = 0`, giving `Even m`. -/
theorem _root_.solution (hodd : Odd (Nat.card G))
    {φ ψ : ClassFunction G ℂ} (hφZ : φ ∈ ZIrr G) (hφR : ClassFunction.IsReal φ)
    (hψZ : ψ ∈ ZIrr G) (hψR : ClassFunction.IsReal ψ) :
    ∃ m a b : ℤ, (m : ℂ) = ClassFunction.inner φ ψ ∧
      (a : ℂ) = ClassFunction.inner φ (trivialIrreducibleCharacter G : ClassFunction G ℂ) ∧
      (b : ℂ) = ClassFunction.inner ψ (trivialIrreducibleCharacter G : ClassFunction G ℂ) ∧
      Even (m - a * b) := by
  classical
  choose p hp using fun χ : IrreducibleCharacter G =>
    ClassFunction.inner_mem_ZIrr_int hφZ χ.property.mem_ZIrr
  choose q hq using fun χ : IrreducibleCharacter G =>
    ClassFunction.inner_mem_ZIrr_int hψZ χ.property.mem_ZIrr
  obtain ⟨m, hm⟩ := ClassFunction.inner_mem_ZIrr_int hφZ hψZ
  refine ⟨m, p (trivialIrreducibleCharacter G), q (trivialIrreducibleCharacter G), hm.symm,
    (hp (trivialIrreducibleCharacter G)).symm, (hq (trivialIrreducibleCharacter G)).symm, ?_⟩
  -- Cross-Parseval: `⟨φ, ψ⟩ = ∑_χ (p χ · q χ)`.
  have hfourier : ClassFunction.inner φ ψ =
      ∑ χ : IrreducibleCharacter G, ((p χ * q χ : ℤ) : ℂ) := by
    conv_lhs => rw [classFunction_eq_sum_inner_smul ψ]
    rw [inner_sum_right]
    refine Finset.sum_congr rfl fun χ _ => ?_
    rw [ClassFunction.inner_smul_right, hp χ, hq χ, star_intCast]
    push_cast; ring
  have hmsum : m = ∑ χ : IrreducibleCharacter G, p χ * q χ := by
    have hcast := hm.symm.trans hfourier
    rw [← Int.cast_sum] at hcast
    exact_mod_cast hcast
  rw [hmsum]
  -- Parity via the conjugation involution: the summand `p χ · q χ` is invariant.
  exact sum_conjPerm_invariant_sub_trivial_even hodd (fun χ => p χ * q χ) fun χ => by
    have hpinv : p (IrreducibleCharacter.conjPerm G χ) = p χ := by
      have : (p (IrreducibleCharacter.conjPerm G χ) : ℂ) = (p χ : ℂ) := by
        rw [← hp (IrreducibleCharacter.conjPerm G χ), ← hp χ]
        exact inner_conjPerm_eq_of_real hφZ hφR χ
      exact_mod_cast this
    have hqinv : q (IrreducibleCharacter.conjPerm G χ) = q χ := by
      have : (q (IrreducibleCharacter.conjPerm G χ) : ℂ) = (q χ : ℂ) := by
        rw [← hq (IrreducibleCharacter.conjPerm G χ), ← hq χ]
        exact inner_conjPerm_eq_of_real hψZ hψR χ
      exact_mod_cast this
    change p (IrreducibleCharacter.conjPerm G χ) * q (IrreducibleCharacter.conjPerm G χ) = p χ * q χ
    rw [hpinv, hqinv]

end Main

end OddOrder.RepresentationTheory
