-- Prove2me | solution 1 for RockafellianRelax.neg_conj_minValue_eq_inf_tilt
-- status  : ACCEPTED   (prove)
-- author  : @涼宮 ハルヒ
-- created : 2026-11-04T12:30:47.731751+00:00
-- url     : https://prove2.me/submissions/6299bae1-74d5-4815-877b-2e565aca4d5e

import Definitions.Def_RockafellianRelax_conj
import Definitions.Def_RockafellianRelax_minValue
import Definitions.Def_RockafellianRelax_tilt

open RockafellianRelax

private lemma inf_sub_real {α : Type*} (g : α → EReal) (c : ℝ) :
    (⨅ a, g a) - (c : EReal) = ⨅ a, g a - (c : EReal) := by
  apply le_antisymm
  · exact le_iInf fun a => EReal.sub_le_sub (iInf_le g a) le_rfl
  · apply (EReal.le_sub_iff_add_le (Or.inl (EReal.coe_ne_bot c))
      (Or.inl (EReal.coe_ne_top c))).mpr
    apply le_iInf
    intro a
    exact EReal.add_le_of_le_sub (iInf_le (fun a => g a - (c : EReal)) a)

private lemma neg_coe_sub (c : ℝ) (a : EReal) :
    -((c : EReal) - a) = a - (c : EReal) := by
  rw [EReal.neg_sub (Or.inl (EReal.coe_ne_bot c)) (Or.inl (EReal.coe_ne_top c)),
    add_comm, sub_eq_add_neg]

private lemma n04_neg_iSup {α : Type*} (g : α → EReal) :
    -(⨆ a, g a) = ⨅ a, -g a := by
  apply le_antisymm
  · exact le_iInf fun a => EReal.neg_le_neg_iff.mpr (le_iSup g a)
  · apply EReal.le_neg.mpr
    apply iSup_le
    intro a
    exact EReal.le_neg.mpr (iInf_le (fun a => -g a) a)

theorem solution {m n : ℕ} (f : (Fin m → ℝ) × (Fin n → ℝ) → EReal)
    (ybar : Fin m → ℝ) :
    -(conj (minValue f) ybar) = (⨅ p : (Fin m → ℝ) × (Fin n → ℝ), tilt f ybar p) ∧
      -(conj (minValue f) ybar) ≤ minValue f 0 := by
  have heq : -(conj (minValue f) ybar) =
      ⨅ u : Fin m → ℝ, minValue f u - ((ybar ⬝ᵥ u : ℝ) : EReal) := by
    unfold conj
    rw [n04_neg_iSup]
    exact iInf_congr fun u => by rw [neg_coe_sub, dotProduct_comm]
  have hjoint : (⨅ u : Fin m → ℝ, minValue f u - ((ybar ⬝ᵥ u : ℝ) : EReal)) =
      ⨅ p : (Fin m → ℝ) × (Fin n → ℝ), tilt f ybar p := by
    simp_rw [minValue, inf_sub_real]
    apply le_antisymm
    · apply le_iInf
      rintro ⟨u, x⟩
      exact (iInf_le _ u).trans (iInf_le _ x)
    · apply le_iInf
      intro u
      apply le_iInf
      intro x
      exact iInf_le _ (u, x)
  refine ⟨heq.trans hjoint, ?_⟩
  rw [heq]
  simpa using iInf_le (fun u : Fin m → ℝ => minValue f u -
    ((ybar ⬝ᵥ u : ℝ) : EReal)) 0

#print axioms solution
