-- Prove2me | solution 1 for OAI.UniversalTensorSquare.eight_positive10
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-16T02:40:15.463577+00:00
-- url     : https://prove2.me/submissions/9c685890-8557-4313-a36f-2facf4d19401

import Mathlib
import Definitions.Def_UniversalTensorSquares
import Definitions.Def_OAIQ259US006
import Definitions.Def_OAIQ259US012
import Theorems.Thm_OAI_Saxl_Columns_polytabloid_placed_expansion
import Theorems.Thm_OAI_Saxl_kronecker_pos_of_contraction
import Theorems.Thm_OAI_UniversalTensorSquare_eightCertificate10

section
-- module Solutions.OAIQ259_US.UniversalSquare_Contraction_ColumnCertificates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Column Certificates. -/

section

noncomputable section
open scoped TensorProduct
namespace Saxl

namespace Columns

lemma sgInteger_cast {rs : List ℕ} (π : Perms rs) : (sgInteger π : ℂ) = sg π := by
  induction rs with
  | nil => simp [sgInteger, sg]
  | cons r rs ih => simp only [sgInteger, sg, Int.cast_mul, ih]

lemma contractionInteger_correct {n : ℕ} (α β μ : YoungDiagram)
    (rsA rsB rsT : List ℕ) (ha : α.transpose.rowLens = rsA)
    (hb : β.transpose.rowLens = rsB) (ht : μ.transpose.rowLens = rsT)
    (ea : Fin n ≃ Fin rsA.sum) (eb : Fin n ≃ Fin rsB.sum) (et : Fin n ≃ Fin rsT.sum)
    (L : ℕ → ℕ → ℕ → ℤ) :
    dotProduct (wordMap (pairFlag L) (polytabloid (tableFor μ rsT ht et)))
      (wordTensor _ _ _ (polytabloid (tableFor α rsA ha ea) ⊗ₜ[ℂ]
        polytabloid (tableFor β rsB hb eb))) =
      (contractionInteger rsA rsB rsT ea eb et L : ℂ) := by
  subst rsA rsB rsT
  simp only [tableFor, polytabloid_placed_expansion, map_sum, map_smul,
    sum_dotProduct, smul_dotProduct]
  simp only [TensorProduct.sum_tmul, TensorProduct.tmul_sum,
    TensorProduct.smul_tmul_smul, map_sum, map_smul, wordTensor_single,
    dotProduct_sum, dotProduct_smul, smul_eq_mul,
    dotProduct_single_one, wordMap_single,
    contractionInteger, Int.cast_sum, Int.cast_mul, Int.cast_prod, sgInteger_cast]
  apply Finset.sum_congr rfl
  intro π hπ
  conv_lhs => arg 2; rw [Finset.sum_comm]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro σ hσ
  apply Finset.sum_congr rfl
  intro τ hτ
  simp only [mul_assoc]
  congr 3
  apply Finset.prod_congr rfl
  intro q hq
  simp only [pairFlag, mergeWords, Equiv.symm_apply_apply, signedRowWord, Function.comp_apply]

theorem kronecker_pos_of_integer_certificate {n : ℕ} {α β μ : YoungDiagram}
    (a : Tableau n α) (b : Tableau n β) (t : Tableau n μ)
    (rsA rsB rsT : List ℕ) (ha : α.transpose.rowLens = rsA)
    (hb : β.transpose.rowLens = rsB) (ht : μ.transpose.rowLens = rsT)
    (ea : Fin n ≃ Fin rsA.sum) (eb : Fin n ≃ Fin rsB.sum) (et : Fin n ≃ Fin rsT.sum)
    (L : ℕ → ℕ → ℕ → ℤ) (hcert : contractionInteger rsA rsB rsT ea eb et L ≠ 0) :
    0 < kronecker a b t := by
  apply kronecker_pos_of_contraction a (tableFor α rsA ha ea)
    b (tableFor β rsB hb eb) t (tableFor μ rsT ht et) (pairFlag L)
  rw [contractionInteger_correct]
  exact_mod_cast hcert

end Columns
end Saxl
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Support_FiniteDiagrams
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite Diagrams. -/

section

namespace UniversalTensorSquare

lemma diagramOfCols_cols (rs : List ℕ) (hs : rs.SortedGE)
    (hp : ∀ a ∈ rs, 0 < a) : (diagramOfCols rs hs).transpose.rowLens = rs := by
  simp only [diagramOfCols, YoungDiagram.transpose_transpose]
  exact YoungDiagram.rowLens_ofRowLens_eq_self hp

end UniversalTensorSquare
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_DegreeEight
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Degree Eight. -/

section

open Saxl Saxl.Columns
namespace UniversalTensorSquare

lemma eightWitness_cols : eightWitness.transpose.rowLens = [4,2,1,1] :=
  diagramOfCols_cols _ _ (by simp)

noncomputable section

lemma eight_positive_certificate (rs : List ℕ) (hs : rs.SortedGE)
    (hp : ∀ a ∈ rs, 0 < a) (hn : rs.sum = 8)
    (eb : Equiv.Perm (Fin 8)) (et : Fin 8 ≃ Fin rs.sum)
    (L : ℕ → ℕ → ℕ → ℤ)
    (hc : contractionInteger [4,2,1,1] [4,2,1,1] rs (Equiv.refl _) eb et L ≠ 0) :
    0 < kronecker (canonicalTableau eightWitness eightWitness_card)
      (canonicalTableau eightWitness eightWitness_card)
      (canonicalTableau (diagramOfCols rs hs) ((diagramOfCols_card rs hs hp).trans hn)) := by
  exact kronecker_pos_of_integer_certificate _ _ _ [4,2,1,1] [4,2,1,1] rs
    eightWitness_cols eightWitness_cols (diagramOfCols_cols _ _ hp)
    (Equiv.refl _) eb et L hc

lemma eight_positive10_oai :
    0 < kronecker (canonicalTableau eightWitness eightWitness_card)
      (canonicalTableau eightWitness eightWitness_card)
      (canonicalTableau (diagramOfCols [4,2,1,1] (by decide))
        (by exact diagramOfCols_card _ _ (by simp))) := by
  apply eight_positive_certificate [4,2,1,1] (by decide) (by simp) rfl
    eightPlaceB10 eightPlaceT10 eightFlag10
  intro hz
  have hh : (-4 : ℤ) = 0 := eightCertificate10.symm.trans hz
  norm_num at hh

universe u

end
end UniversalTensorSquare
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.eight_positive10_oai := @OAI.UniversalTensorSquare.eight_positive10_oai
