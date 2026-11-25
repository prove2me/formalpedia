-- Prove2me | solution 1 for PretorsionImageClosed.LinearQuiver.colCount_glue_castSucc
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T06:50:25.18838+00:00
-- url     : https://prove2.me/submissions/f5e2af1b-5245-4d15-a29c-9bae7760b496

module
public import Definitions.Def_PretorsionImageClosed_LinearQuiver_CutoffWeights
public import Definitions.Def_PretorsionImageClosed_Gandhi_ColumnSum
public import Definitions.Def_PretorsionImageClosed_LinearQuiver_CutoffRestriction
public import Theorems.Thm_PretorsionImageClosed_Statement_PretorsionTheory_ext


set_option autoImplicit true
@[expose] public section
public section
set_option autoImplicit false
noncomputable section
open PretorsionImageClosed
open Statement Polynomial Finset
open PretorsionImageClosed.LinearQuiver
variable {n : ℕ}
namespace PretorsionImageClosed.LinearQuiver
theorem _root_.solution (p : CutoffPair n) (Cont : Finset (Fin (n + 1)))
    (c : Option (Fin (n + 1))) (hC : Cont ⊆ candRows p) (d : Fin n) :
    colCount (glueRow p Cont) (glueCol p c) d.castSucc = colCount p.1.1 p.1.2 d := by
  unfold colCount
  conv_rhs => rw [← Finset.card_map Fin.castSuccEmb]
  apply congrArg Finset.card
  ext a
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map, Fin.val_castSucc,
    glueCol_castSucc]
  induction a using Fin.lastCases with
  | last =>
    constructor
    · rintro ⟨h, -⟩
      exact absurd h (not_le.2 (Fin.castSucc_lt_last d))
    · rintro ⟨a', -, ha'⟩
      exact absurd ha' (Fin.castSucc_lt_last a').ne
  | cast a =>
    constructor
    · rintro ⟨h1, h2, h3⟩
      refine ⟨a, ⟨Fin.castSucc_le_castSucc_iff.1 h1, ?_, h3⟩, rfl⟩
      by_cases haC : a.castSucc ∈ Cont
      · have := mem_candRows.1 (hC haC)
        rw [βext_castSucc] at this
        rw [this]
        exact d.isLt
      · rwa [glueRow_apply_of_notMem haC, βext_castSucc] at h2
    · rintro ⟨a', ⟨h1, h2, h3⟩, ha'⟩
      have : a' = a := Fin.castSucc_injective _ ha'
      subst this
      refine ⟨Fin.castSucc_le_castSucc_iff.2 h1, ?_, h3⟩
      by_cases haC : a'.castSucc ∈ Cont
      · rw [glueRow_apply_of_mem haC]
        have := d.isLt
        omega
      · rwa [glueRow_apply_of_notMem haC, βext_castSucc]
end PretorsionImageClosed.LinearQuiver
