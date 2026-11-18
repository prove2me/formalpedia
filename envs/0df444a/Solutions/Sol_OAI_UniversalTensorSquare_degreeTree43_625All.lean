-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degreeTree43_625All
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T23:08:46.525266+00:00
-- url     : https://prove2.me/submissions/876d6c95-506f-40bb-954d-e3288a3ab095
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_UniversalTensorSquares
import Definitions.Def_OAIQ259US021
import Theorems.Thm_OAI_Saxl_kronecker_pos_of_contraction
import Theorems.Thm_OAI_UniversalTensorSquare_eightCertificate0
import Theorems.Thm_OAI_UniversalTensorSquare_eightCertificate10
import Theorems.Thm_OAI_UniversalTensorSquare_eightCertificate5
import Theorems.Thm_OAI_UniversalTensorSquare_eightCertificate7
import Theorems.Thm_OAI_UniversalTensorSquare_eight_positive1
import Theorems.Thm_OAI_UniversalTensorSquare_eight_positive11
import Theorems.Thm_OAI_UniversalTensorSquare_eight_positive2
import Theorems.Thm_OAI_UniversalTensorSquare_eight_positive3
import Theorems.Thm_OAI_UniversalTensorSquare_eight_positive4
import Theorems.Thm_OAI_UniversalTensorSquare_eight_positive6
import Theorems.Thm_OAI_UniversalTensorSquare_eight_positive8
import Theorems.Thm_OAI_UniversalTensorSquare_eight_positive9
import Theorems.Thm_OAI_UniversalTensorSquare_eq_diagramOfCols
import Theorems.Thm_OAI_UniversalTensorSquare_kronecker_pos_transpose
import Theorems.Thm_OAI_UniversalTensorSquare_rowDiagram_eq
import Theorems.Thm_OAI_UniversalTensorSquare_rowLens_mem_partitionLists
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_short
import Theorems.Thm_OAI_UniversalTensorSquare_seven_kronecker_pos
import Theorems.Thm_OAI_UniversalTensorSquare_sg0
import Theorems.Thm_OAI_UniversalTensorSquare_sg10027
import Theorems.Thm_OAI_UniversalTensorSquare_sg10036
import Theorems.Thm_OAI_UniversalTensorSquare_sg1041
import Theorems.Thm_OAI_UniversalTensorSquare_sg13
import Theorems.Thm_OAI_UniversalTensorSquare_sg17
import Theorems.Thm_OAI_UniversalTensorSquare_sg1754
import Theorems.Thm_OAI_UniversalTensorSquare_sg2
import Theorems.Thm_OAI_UniversalTensorSquare_sg2626
import Theorems.Thm_OAI_UniversalTensorSquare_sg315
import Theorems.Thm_OAI_UniversalTensorSquare_sg31678
import Theorems.Thm_OAI_UniversalTensorSquare_sg31681
import Theorems.Thm_OAI_UniversalTensorSquare_sg31682
import Theorems.Thm_OAI_UniversalTensorSquare_sg31683
import Theorems.Thm_OAI_UniversalTensorSquare_sg31684
import Theorems.Thm_OAI_UniversalTensorSquare_sg31688
import Theorems.Thm_OAI_UniversalTensorSquare_sg31692
import Theorems.Thm_OAI_UniversalTensorSquare_sg31693
import Theorems.Thm_OAI_UniversalTensorSquare_sg32
import Theorems.Thm_OAI_UniversalTensorSquare_sg34
import Theorems.Thm_OAI_UniversalTensorSquare_sg371
import Theorems.Thm_OAI_UniversalTensorSquare_sg373
import Theorems.Thm_OAI_UniversalTensorSquare_sg535
import Theorems.Thm_OAI_UniversalTensorSquare_sg5735
import Theorems.Thm_OAI_UniversalTensorSquare_sg68
import Theorems.Thm_OAI_UniversalTensorSquare_sg7
import Theorems.Thm_OAI_UniversalTensorSquare_sg7454
import Theorems.Thm_OAI_UniversalTensorSquare_sg910

section
-- module Solutions.OAIQ259_US.Saxl_PathAlternation
attribute [-instance] _root_.OAI.Saxl.Columns.cellsDecEq _root_.OAI.Saxl.Columns.cellsFintype _root_.OAI.Saxl.Columns.permsFintype
attribute [-simp] _root_.OAI.Saxl.Balance.cyclicSquareMap_tmul _root_.OAI.Saxl.orbitTensorEval_tmul _root_.OAI.Saxl.positionTensor_tmul _root_.OAI.Saxl.relabelWord_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped TensorProduct

universe uAlpha

namespace Saxl

lemma altWord_fiber_relabel {n m d : ℕ} {α : Type uAlpha}
    (e : Fin n ≃ Fin m) (c : Fin m → α) (a : Fin m → Fin d) (w : Fin n → Fin d) :
    altWord (fiberGroup c) a (w ∘ e.symm) =
      altWord (fiberGroup (c ∘ e)) (a ∘ e) w := by
  classical
  let := Fintype.ofFinite (fiberGroup c)
  let := Fintype.ofFinite (fiberGroup (c ∘ e))
  unfold altWord
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  symm
  apply Fintype.sum_equiv (fiberRelabel e c)
  intro g
  have hs : signC ((fiberRelabel e c g).val) = signC g.val := by
    change signC (e.permCongr g.val) = _
    simp only [signC_def, Equiv.Perm.sign_permCongr]
  rw [hs]
  congr 1
  change (Pi.single (a ∘ e) (1:ℂ) : WordSpace n d) (w ∘ g.val) =
    (Pi.single a (1:ℂ) : WordSpace m d) ((w ∘ e.symm) ∘ (e.permCongr g.val))
  simp only [Pi.single_apply]
  congr 1
  apply propext
  constructor
  · intro h
    funext i
    obtain ⟨j,rfl⟩ := e.surjective i
    simpa [Equiv.permCongr] using congrFun h j
  · intro h
    funext i
    simpa [Equiv.permCongr] using congrFun h (e i)

end Saxl

end

end OAI
end

section
-- module Solutions.OAIQ259_US.Saxl_ColumnContraction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped TensorProduct

namespace Saxl.Columns
/- A concrete ordered disjoint union of consecutive columns. -/

lemma columnPerm_sign (μ : YoungDiagram) (π : Perms μ.transpose.rowLens) :
    signC (columnPerm μ π).val = sg π := by
  change (((Equiv.Perm.sign ((enumerate μ.transpose.rowLens).symm.permCongr (perm π)) : ℤ) : ℂ)) = sg π
  rw [Equiv.Perm.sign_permCongr]
  exact sign_perm π

end Saxl.Columns

end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Contraction_ColumnCertificates
attribute [-simp] _root_.OAI.Saxl.orbitTensorEval_tmul
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

lemma polytabloid_reindex {n m : ℕ} {μ : YoungDiagram} (t : Tableau m μ)
    (e : Fin n ≃ Fin m) (w : Fin n → Fin (μ.colLen 0)) :
    polytabloid (e.trans t) w = polytabloid t (w ∘ e.symm) := by
  rw [polytabloid_eq_altWord, polytabloid_eq_altWord]
  exact (altWord_fiber_relabel e (fun i => (t i).val.2) (rowWord t) w).symm

namespace Columns

lemma polytabloid_column_expansion (μ : YoungDiagram) :
    polytabloid (columnTableau μ) =
      ∑ π : Perms μ.transpose.rowLens, sg π • Pi.single (signedRowWord μ π) 1 := by
  classical
  let := Fintype.ofFinite (columnGroup (columnTableau μ))
  rw [polytabloid_eq_altWord, altWord_inverse_sum]
  symm
  apply Fintype.sum_equiv (columnEquiv μ)
  intro π
  rw [← columnPerm_sign μ π]
  congr 2
  funext q
  apply Fin.ext
  change row (perm π (enumerate μ.transpose.rowLens q)) =
    ((columnTableau μ) ((columnEquiv μ π).val q)).val.1
  rw [columnTableau_val]
  simp only [columnEquiv, Equiv.ofBijective_apply, columnPerm, Equiv.permCongr_apply,
    Equiv.symm_symm, Equiv.apply_symm_apply]

lemma polytabloid_placed_expansion {n : ℕ} (μ : YoungDiagram)
    (e : Fin n ≃ Fin μ.transpose.rowLens.sum) :
    polytabloid (e.trans (columnTableau μ)) =
      ∑ π : Perms μ.transpose.rowLens, sg π • Pi.single (signedRowWord μ π ∘ e) 1 := by
  classical
  funext w
  rw [polytabloid_reindex, polytabloid_column_expansion]
  simp only [Finset.sum_apply, Pi.smul_apply]
  apply Finset.sum_congr rfl
  intro π hπ
  congr 1
  simp only [Pi.single_apply]
  congr 1
  apply propext
  constructor
  · intro hw
    funext q
    have h := congrFun hw (e q)
    simpa using h
  · intro hw
    funext q
    have h := congrFun hw (e.symm q)
    simpa using h

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

lemma eightWitness_self : eightWitness.transpose = eightWitness := by
  apply YoungDiagram.ext
  decide

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

lemma eight_positive0 :
    0 < kronecker (canonicalTableau eightWitness eightWitness_card)
      (canonicalTableau eightWitness eightWitness_card)
      (canonicalTableau (diagramOfCols [1,1,1,1,1,1,1,1] (by decide))
        (by exact diagramOfCols_card _ _ (by simp))) := by
  apply eight_positive_certificate [1,1,1,1,1,1,1,1] (by decide) (by simp) rfl
    eightPlaceB0 eightPlaceT0 eightFlag0
  intro hz
  have hh : (6 : ℤ) = 0 := eightCertificate0.symm.trans hz
  norm_num at hh

lemma eight_positive5 :
    0 < kronecker (canonicalTableau eightWitness eightWitness_card)
      (canonicalTableau eightWitness eightWitness_card)
      (canonicalTableau (diagramOfCols [3,2,1,1,1] (by decide))
        (by exact diagramOfCols_card _ _ (by simp))) := by
  apply eight_positive_certificate [3,2,1,1,1] (by decide) (by simp) rfl
    eightPlaceB5 eightPlaceT5 eightFlag5
  intro hz
  have hh : (2 : ℤ) = 0 := eightCertificate5.symm.trans hz
  norm_num at hh

lemma eight_positive7 :
    0 < kronecker (canonicalTableau eightWitness eightWitness_card)
      (canonicalTableau eightWitness eightWitness_card)
      (canonicalTableau (diagramOfCols [2,2,2,2] (by decide))
        (by exact diagramOfCols_card _ _ (by simp))) := by
  apply eight_positive_certificate [2,2,2,2] (by decide) (by simp) rfl
    eightPlaceB7 eightPlaceT7 eightFlag7
  intro hz
  have hh : (2 : ℤ) = 0 := eightCertificate7.symm.trans hz
  norm_num at hh

lemma eight_positive10 :
    0 < kronecker (canonicalTableau eightWitness eightWitness_card)
      (canonicalTableau eightWitness eightWitness_card)
      (canonicalTableau (diagramOfCols [4,2,1,1] (by decide))
        (by exact diagramOfCols_card _ _ (by simp))) := by
  apply eight_positive_certificate [4,2,1,1] (by decide) (by simp) rfl
    eightPlaceB10 eightPlaceT10 eightFlag10
  intro hz
  have hh : (-4 : ℤ) = 0 := eightCertificate10.symm.trans hz
  norm_num at hh

lemma eight_positive_target_eq {μ ν : YoungDiagram} (hμ : μ.card = 8) (hν : ν.card = 8)
    (he : μ = ν)
    (hp : 0 < kronecker (canonicalTableau eightWitness eightWitness_card)
      (canonicalTableau eightWitness eightWitness_card) (canonicalTableau ν hν)) :
    0 < kronecker (canonicalTableau eightWitness eightWitness_card)
      (canonicalTableau eightWitness eightWitness_card) (canonicalTableau μ hμ) := by
  subst ν
  exact hp

lemma partitionLists_eight : partitionLists 8 8 8 =
    {[8],[7,1],[6,2],[6,1,1],[5,3],[5,2,1],[5,1,1,1],[4,4],[4,3,1],[4,2,2],[4,2,1,1],[4,1,1,1,1],[3,3,2],[3,3,1,1],[3,2,2,1],[3,2,1,1,1],[3,1,1,1,1,1],[2,2,2,2],[2,2,2,1,1],[2,2,1,1,1,1],[2,1,1,1,1,1,1],[1,1,1,1,1,1,1,1]} := by decide

theorem eight_kronecker_pos (ν : YoungDiagram) (hν : ν.card = 8) :
    0 < kronecker (canonicalTableau eightWitness eightWitness_card)
      (canonicalTableau eightWitness eightWitness_card) (canonicalTableau ν hν) := by
  have hc := rowLens_mem_partitionLists ν.transpose
  rw [transpose_card, hν, partitionLists_eight] at hc
  simp only [Finset.mem_insert, Finset.mem_singleton] at hc
  rcases hc with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · have he := eq_diagramOfCols ν [8] (by decide) h
    have ht : diagramOfCols [8] (by decide) =
        (diagramOfCols [1,1,1,1,1,1,1,1] (by decide)).transpose := by
      apply YoungDiagram.ext
      decide
    have hh := kronecker_pos_transpose eightWitness eightWitness_card eightWitness_self
      _ _ eight_positive0
    exact eight_positive_target_eq hν _ (he.trans ht) hh
  · have he := eq_diagramOfCols ν [7,1] (by decide) h
    have ht : diagramOfCols [7,1] (by decide) =
        (diagramOfCols [2,1,1,1,1,1,1] (by decide)).transpose := by
      apply YoungDiagram.ext
      decide
    have hh := kronecker_pos_transpose eightWitness eightWitness_card eightWitness_self
      _ _ eight_positive1
    exact eight_positive_target_eq hν _ (he.trans ht) hh
  · have he := eq_diagramOfCols ν [6,2] (by decide) h
    have ht : diagramOfCols [6,2] (by decide) =
        (diagramOfCols [2,2,1,1,1,1] (by decide)).transpose := by
      apply YoungDiagram.ext
      decide
    have hh := kronecker_pos_transpose eightWitness eightWitness_card eightWitness_self
      _ _ eight_positive2
    exact eight_positive_target_eq hν _ (he.trans ht) hh
  · have he := eq_diagramOfCols ν [6,1,1] (by decide) h
    have ht : diagramOfCols [6,1,1] (by decide) =
        (diagramOfCols [3,1,1,1,1,1] (by decide)).transpose := by
      apply YoungDiagram.ext
      decide
    have hh := kronecker_pos_transpose eightWitness eightWitness_card eightWitness_self
      _ _ eight_positive3
    exact eight_positive_target_eq hν _ (he.trans ht) hh
  · have he := eq_diagramOfCols ν [5,3] (by decide) h
    have ht : diagramOfCols [5,3] (by decide) =
        (diagramOfCols [2,2,2,1,1] (by decide)).transpose := by
      apply YoungDiagram.ext
      decide
    have hh := kronecker_pos_transpose eightWitness eightWitness_card eightWitness_self
      _ _ eight_positive4
    exact eight_positive_target_eq hν _ (he.trans ht) hh
  · have he := eq_diagramOfCols ν [5,2,1] (by decide) h
    have ht : diagramOfCols [5,2,1] (by decide) =
        (diagramOfCols [3,2,1,1,1] (by decide)).transpose := by
      apply YoungDiagram.ext
      decide
    have hh := kronecker_pos_transpose eightWitness eightWitness_card eightWitness_self
      _ _ eight_positive5
    exact eight_positive_target_eq hν _ (he.trans ht) hh
  · have he := eq_diagramOfCols ν [5,1,1,1] (by decide) h
    have ht : diagramOfCols [5,1,1,1] (by decide) =
        (diagramOfCols [4,1,1,1,1] (by decide)).transpose := by
      apply YoungDiagram.ext
      decide
    have hh := kronecker_pos_transpose eightWitness eightWitness_card eightWitness_self
      _ _ eight_positive6
    exact eight_positive_target_eq hν _ (he.trans ht) hh
  · have he := eq_diagramOfCols ν [4,4] (by decide) h
    have ht : diagramOfCols [4,4] (by decide) =
        (diagramOfCols [2,2,2,2] (by decide)).transpose := by
      apply YoungDiagram.ext
      decide
    have hh := kronecker_pos_transpose eightWitness eightWitness_card eightWitness_self
      _ _ eight_positive7
    exact eight_positive_target_eq hν _ (he.trans ht) hh
  · have he := eq_diagramOfCols ν [4,3,1] (by decide) h
    have ht : diagramOfCols [4,3,1] (by decide) =
        (diagramOfCols [3,2,2,1] (by decide)).transpose := by
      apply YoungDiagram.ext
      decide
    have hh := kronecker_pos_transpose eightWitness eightWitness_card eightWitness_self
      _ _ eight_positive8
    exact eight_positive_target_eq hν _ (he.trans ht) hh
  · have he := eq_diagramOfCols ν [4,2,2] (by decide) h
    have ht : diagramOfCols [4,2,2] (by decide) =
        (diagramOfCols [3,3,1,1] (by decide)).transpose := by
      apply YoungDiagram.ext
      decide
    have hh := kronecker_pos_transpose eightWitness eightWitness_card eightWitness_self
      _ _ eight_positive9
    exact eight_positive_target_eq hν _ (he.trans ht) hh
  · have he := eq_diagramOfCols ν [4,2,1,1] (by decide) h
    subst ν
    exact eight_positive10
  · have he := eq_diagramOfCols ν [4,1,1,1,1] (by decide) h
    subst ν
    exact eight_positive6
  · have he := eq_diagramOfCols ν [3,3,2] (by decide) h
    subst ν
    exact eight_positive11
  · have he := eq_diagramOfCols ν [3,3,1,1] (by decide) h
    subst ν
    exact eight_positive9
  · have he := eq_diagramOfCols ν [3,2,2,1] (by decide) h
    subst ν
    exact eight_positive8
  · have he := eq_diagramOfCols ν [3,2,1,1,1] (by decide) h
    subst ν
    exact eight_positive5
  · have he := eq_diagramOfCols ν [3,1,1,1,1,1] (by decide) h
    subst ν
    exact eight_positive3
  · have he := eq_diagramOfCols ν [2,2,2,2] (by decide) h
    subst ν
    exact eight_positive7
  · have he := eq_diagramOfCols ν [2,2,2,1,1] (by decide) h
    subst ν
    exact eight_positive4
  · have he := eq_diagramOfCols ν [2,2,1,1,1,1] (by decide) h
    subst ν
    exact eight_positive2
  · have he := eq_diagramOfCols ν [2,1,1,1,1,1,1] (by decide) h
    subst ν
    exact eight_positive1
  · have he := eq_diagramOfCols ν [1,1,1,1,1,1,1,1] (by decide) h
    subst ν
    exact eight_positive0

universe u

end
end UniversalTensorSquare
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupLocalLeaves
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Local Leaves. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg16 : RowSquare [3,1] [2,1,1] := by
  exact rowSquare_short 1 2 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)

lemma sg39 : RowSquare [3,2] [2,1,1,1] := by
  exact rowSquare_short 2 1 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)

lemma sg179 : RowSquare [4,1,1,1] [2,1,1,1,1,1] := by
  have he : rowDiagram [4,1,1,1] = sevenWitness := by
    rw [rowDiagram_eq _ (by decide)]
    apply YoungDiagram.ext
    decide
  change SquareOccurs (rowDiagram [4,1,1,1]) (rowDiagram [2,1,1,1,1,1])
  have hh : SquareOccurs sevenWitness (rowDiagram [2,1,1,1,1,1]) :=
    ⟨7,canonicalTableau _ sevenWitness_card,canonicalTableau _ (rowDiagram_card [2,1,1,1,1,1]),
      seven_kronecker_pos _ (rowDiagram_card [2,1,1,1,1,1])⟩
  exact Eq.mpr (congrArg (fun α => SquareOccurs α (rowDiagram [2,1,1,1,1,1])) he) hh

lemma sg180 : RowSquare [4,1,1,1] [2,2,1,1,1] := by
  have he : rowDiagram [4,1,1,1] = sevenWitness := by
    rw [rowDiagram_eq _ (by decide)]
    apply YoungDiagram.ext
    decide
  change SquareOccurs (rowDiagram [4,1,1,1]) (rowDiagram [2,2,1,1,1])
  have hh : SquareOccurs sevenWitness (rowDiagram [2,2,1,1,1]) :=
    ⟨7,canonicalTableau _ sevenWitness_card,canonicalTableau _ (rowDiagram_card [2,2,1,1,1]),
      seven_kronecker_pos _ (rowDiagram_card [2,2,1,1,1])⟩
  exact Eq.mpr (congrArg (fun α => SquareOccurs α (rowDiagram [2,2,1,1,1])) he) hh

lemma sg181 : RowSquare [4,1,1,1] [2,2,2,1] := by
  have he : rowDiagram [4,1,1,1] = sevenWitness := by
    rw [rowDiagram_eq _ (by decide)]
    apply YoungDiagram.ext
    decide
  change SquareOccurs (rowDiagram [4,1,1,1]) (rowDiagram [2,2,2,1])
  have hh : SquareOccurs sevenWitness (rowDiagram [2,2,2,1]) :=
    ⟨7,canonicalTableau _ sevenWitness_card,canonicalTableau _ (rowDiagram_card [2,2,2,1]),
      seven_kronecker_pos _ (rowDiagram_card [2,2,2,1])⟩
  exact Eq.mpr (congrArg (fun α => SquareOccurs α (rowDiagram [2,2,2,1])) he) hh

lemma sg330 : RowSquare [4,2,1,1] [1,1,1,1,1,1,1,1] := by
  have he : rowDiagram [4,2,1,1] = eightWitness := by
    rw [rowDiagram_eq _ (by decide)]
    apply YoungDiagram.ext
    decide
  change SquareOccurs (rowDiagram [4,2,1,1]) (rowDiagram [1,1,1,1,1,1,1,1])
  have hh : SquareOccurs eightWitness (rowDiagram [1,1,1,1,1,1,1,1]) :=
    ⟨8,canonicalTableau _ eightWitness_card,canonicalTableau _ (rowDiagram_card [1,1,1,1,1,1,1,1]),
      eight_kronecker_pos _ (rowDiagram_card [1,1,1,1,1,1,1,1])⟩
  exact Eq.mpr (congrArg (fun α => SquareOccurs α (rowDiagram [1,1,1,1,1,1,1,1])) he) hh

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes0
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 0. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg136 : RowSquare [3,1,1,1,1] [4,2,1] := by
  exact rowSquare_join (by decide) sg2 sg34

lemma sg264 : RowSquare [3,1,1,1,1,1] [5,2,1] := by
  exact rowSquare_join (by decide) sg7 sg34

lemma sg376 : RowSquare [5,1,1,1] [3,2,2,1] := by
  exact rowSquare_join (by decide) sg0 sg181

lemma sg413 : RowSquare [6,1,1] [4,1,1,1,1] := by
  exact rowSquare_join (by decide) sg7 sg32

lemma sg532 : RowSquare [4,1,1,1,1,1] [6,2,1] := by
  exact rowSquare_join (by decide) sg0 sg264

lemma sg534 : RowSquare [4,2,1,1,1] [2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg330

lemma sg674 : RowSquare [6,1,1,1] [3,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg371

lemma sg678 : RowSquare [6,1,1,1] [4,2,1,1,1] := by
  exact rowSquare_join (by decide) sg2 sg180

lemma sg684 : RowSquare [6,1,1,1] [5,2,2] := by
  exact rowSquare_join (by decide) sg7 sg68

lemma sg694 : RowSquare [6,2,1] [3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg17 sg32

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 2. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg1371 : RowSquare [6,2,1,1,1] [2,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg910

lemma sg1404 : RowSquare [6,2,1,1,1] [6,3,2] := by
  exact rowSquare_join (by decide) sg16 sg136

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes11
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 11. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg5171 : RowSquare [4,4,1,1,1,1,1,1,1,1,1,1] [8,4,2,2,2] := by
  exact rowSquare_join (by decide) sg678 sg678

lemma sg5172 : RowSquare [4,4,1,1,1,1,1,1,1,1,1,1] [8,4,3,1,1,1] := by
  exact rowSquare_join (by decide) sg674 sg684

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes8
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 8. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg3889 : RowSquare [4,4,1,1,1,1,1,1,1,1] [5,4,4,3] := by
  exact rowSquare_join (by decide) sg373 sg376

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes10
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 10. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg4556 : RowSquare [3,3,2,1,1,1,1,1,1,1,1,1] [7,4,2,2,2] := by
  exact rowSquare_join (by decide) sg413 sg694

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes18
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 18. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg7786 : RowSquare [6,5,2,1,1,1,1,1,1,1] [3,3,3,3,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg315 sg1754

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes13
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 13. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg5871 : RowSquare [4,4,2,1,1,1,1,1,1,1,1,1] [6,5,4,2,1,1] := by
  exact rowSquare_join (by decide) sg674 sg1041

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes19
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 19. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg8416 : RowSquare [6,4,3,2,1,1,1,1,1,1] [3,2,2,2,2,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg179 sg2626

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes24
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 24. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg10519 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [9,5,3,3,2] := by
  exact rowSquare_join (by decide) sg13 sg5171

lemma sg10520 : RowSquare [6,6,1,1,1,1,1,1,1,1,1,1] [9,5,4,2,1,1] := by
  exact rowSquare_join (by decide) sg13 sg5172

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes23
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 23. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg10035 : RowSquare [6,5,2,1,1,1,1,1,1,1,1,1] [9,5,3,3,2] := by
  exact rowSquare_join (by decide) sg39 sg4556

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes20
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 20. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg8647 : RowSquare [6,5,2,2,1,1,1,1,1,1] [3,2,2,2,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg534 sg1754

lemma sg8649 : RowSquare [6,5,2,2,1,1,1,1,1,1] [3,3,2,2,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg535 sg1754

lemma sg8811 : RowSquare [7,5,2,1,1,1,1,1,1,1] [4,3,3,3,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg7786

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes27
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 27. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg11353 : RowSquare [6,6,2,1,1,1,1,1,1,1,1,1] [7,6,5,3,1,1] := by
  exact rowSquare_join (by decide) sg13 sg5871

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes22
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 22. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg9392 : RowSquare [5,5,2,2,1,1,1,1,1,1,1,1] [8,4,3,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1371 sg1404

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes34
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 34. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg14522 : RowSquare [8,6,3,2,1,1,1,1,1,1,1,1] [7,3,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg532 sg5735

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes77
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 77. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg31679 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [12,7,5,5,4,2,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8416 sg10519

lemma sg31680 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [12,7,5,5,4,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8647 sg10035

lemma sg31685 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [12,7,5,5,5,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8649 sg10027

lemma sg31686 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [12,7,6,4,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3889 sg14522

lemma sg31687 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [12,7,6,4,2,2,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg7454 sg11353

lemma sg31689 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [12,7,6,4,2,2,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg8811 sg9392

lemma sg31690 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [12,7,6,4,3,3,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8416 sg10520

lemma sg31691 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [12,7,6,4,3,3,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8647 sg10036

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_DegreeTreeProof43
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Degree Tree Proof 43. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

lemma degreeTree43_625All_oai : degreeTree43_625.All (RowSquare [12,10,4,3,2,2,2,2,2,2,1,1]) := by
  exact ⟨sg31686,⟨sg31682,⟨sg31680,⟨sg31679,⟨sg31678,True.intro,True.intro⟩,True.intro⟩,⟨sg31681,True.intro,True.intro⟩⟩,⟨sg31684,⟨sg31683,True.intro,True.intro⟩,⟨sg31685,True.intro,True.intro⟩⟩⟩,⟨sg31690,⟨sg31688,⟨sg31687,True.intro,True.intro⟩,⟨sg31689,True.intro,True.intro⟩⟩,⟨sg31692,⟨sg31691,True.intro,True.intro⟩,⟨sg31693,True.intro,True.intro⟩⟩⟩⟩

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degreeTree43_625All_oai := @OAI.UniversalTensorSquare.degreeTree43_625All_oai
