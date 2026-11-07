-- Prove2me | solution 1 for RockafellianRelax.proposition_3_2
-- status  : ACCEPTED   (prove)
-- author  : @涼宮 ハルヒ
-- created : 2026-11-06T12:10:23.835274+00:00
-- url     : https://prove2.me/submissions/47c3f8a9-5e11-4c1b-b7d2-5cee6922517b

import Definitions.Def_RockafellianRelax_IsExact
import Definitions.Def_RockafellianRelax_conj

open RockafellianRelax

private lemma n06_neg_iSup {α : Type*} (g : α → EReal) :
    -(⨆ a, g a) = ⨅ a, -g a := by
  apply le_antisymm
  · exact le_iInf fun a => EReal.neg_le_neg_iff.mpr (le_iSup g a)
  · apply EReal.le_neg.mpr
    apply iSup_le
    intro a
    exact EReal.le_neg.mpr (iInf_le (fun a => -g a) a)

private lemma n06_neg_coe_sub (c : ℝ) (a : EReal) :
    -((c : EReal) - a) = a - (c : EReal) := by
  rw [EReal.neg_sub (Or.inl (EReal.coe_ne_bot c)) (Or.inl (EReal.coe_ne_top c)),
    add_comm, sub_eq_add_neg]

theorem solution {m n : ℕ} (f : (Fin m → ℝ) × (Fin n → ℝ) → EReal)
    (φ : (Fin n → ℝ) → EReal) (hf : IsRockafellian f φ) (ybar : Fin m → ℝ) :
    IsExact f φ ybar ↔ minValue f 0 = -(conj (minValue f) ybar) := by
  have heq : -(conj (minValue f) ybar) =
      ⨅ u : Fin m → ℝ, minValue f u - ((ybar ⬝ᵥ u : ℝ) : EReal) := by
    unfold conj
    rw [n06_neg_iSup]
    exact iInf_congr fun u => by rw [n06_neg_coe_sub, dotProduct_comm]
  rw [heq]
  constructor
  · intro hex
    apply le_antisymm
    · apply le_iInf
      intro u
      exact (EReal.le_sub_iff_add_le (Or.inl (EReal.coe_ne_bot _))
        (Or.inl (EReal.coe_ne_top _))).mpr (hex.2 u)
    · simpa using iInf_le (fun u : Fin m → ℝ => minValue f u -
        ((ybar ⬝ᵥ u : ℝ) : EReal)) 0
  · intro h
    refine ⟨hf, fun u => ?_⟩
    apply EReal.add_le_of_le_sub
    rw [h]
    exact iInf_le _ u

#print axioms solution
