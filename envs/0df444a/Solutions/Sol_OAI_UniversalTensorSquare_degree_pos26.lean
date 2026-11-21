-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degree_pos26
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T04:12:45.924536+00:00
-- url     : https://prove2.me/submissions/7d5a4721-9a64-4f02-9e6e-a5a5d65304e4

import Mathlib
import Definitions.Def_UniversalTensorSquares
import Definitions.Def_OAIQ259US004
import Definitions.Def_OAIQ259US021
import Definitions.Def_OAIQ259US022
import Definitions.Def_OAIQ259US000
import Definitions.Def_OAIQ259US001
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US006
import Theorems.Thm_OAI_UniversalTensorSquare_band_kronecker_pos
import Theorems.Thm_OAI_UniversalTensorSquare_candidate_rowLens
import Theorems.Thm_OAI_UniversalTensorSquare_checkedRegion_diagram
import Theorems.Thm_OAI_UniversalTensorSquare_degreeTree26_14All
import Theorems.Thm_OAI_UniversalTensorSquare_degreeTree26_21All
import Theorems.Thm_OAI_UniversalTensorSquare_degreeTree26_28All
import Theorems.Thm_OAI_UniversalTensorSquare_degreeTree26_61All
import Theorems.Thm_OAI_UniversalTensorSquare_degreeUnionCheck26
import Theorems.Thm_OAI_UniversalTensorSquare_kronecker_pos_transpose
import Theorems.Thm_OAI_UniversalTensorSquare_packingPlan_pos
import Theorems.Thm_OAI_UniversalTensorSquare_residualProperty_sound
import Theorems.Thm_OAI_UniversalTensorSquare_rowDiagram_eq
import Theorems.Thm_OAI_UniversalTensorSquare_rowSquare_join
import Theorems.Thm_OAI_UniversalTensorSquare_semantic_capacity_dichotomy
import Theorems.Thm_OAI_UniversalTensorSquare_sg0
import Theorems.Thm_OAI_UniversalTensorSquare_sg1
import Theorems.Thm_OAI_UniversalTensorSquare_sg32
import Theorems.Thm_OAI_UniversalTensorSquare_sg33
import Theorems.Thm_OAI_UniversalTensorSquare_sg34
import Theorems.Thm_OAI_UniversalTensorSquare_sg586
import Theorems.Thm_OAI_UniversalTensorSquare_sg68
import Theorems.Thm_OAI_UniversalTensorSquare_sg768
import Theorems.Thm_OAI_UniversalTensorSquare_sg88
import Theorems.Thm_OAI_UniversalTensorSquare_sg89
import Theorems.Thm_OAI_UniversalTensorSquare_sg91
import Definitions.Def_OAIQ259US002
import Theorems.Thm_OAI_UniversalTensorSquare_transposeRows_eq

section
-- module Solutions.OAIQ259_US.Saxl_Basic
attribute [-instance] _root_.OAI.Saxl.Columns.cellsFintype _root_.OAI.Saxl.Columns.permsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped TensorProduct

universe uG uV uW

namespace Saxl

/- The genuine finite-dimensional Hom criterion; no simplicity hypothesis. -/
theorem intertwining_finrank_pos_iff {G : Type uG} {V : Type uV} {W : Type uW} [Group G]
    [AddCommGroup V] [AddCommGroup W] [Module ℂ V] [Module ℂ W]
    [Module.Finite ℂ V] [Module.Finite ℂ W]
    (ρ : Representation ℂ G V) (σ : Representation ℂ G W) :
    0 < Module.finrank ℂ (Representation.IntertwiningMap ρ σ) ↔
      ∃ f : Representation.IntertwiningMap ρ σ, f ≠ 0 :=
  Module.finrank_pos_iff_exists_ne_zero (R := ℂ) (M := Representation.IntertwiningMap ρ σ)

theorem kronecker_pos_iff {n : ℕ} {α β μ : YoungDiagram}
    (a : Tableau n α) (b : Tableau n β) (t : Tableau n μ) :
    0 < kronecker a b t ↔
      ∃ f : Representation.IntertwiningMap (spechtRep t)
        ((spechtRep a).tprod (spechtRep b)), f ≠ 0 := by
  exact @intertwining_finrank_pos_iff (Equiv.Perm (Fin n)) (Specht t)
    (Specht a ⊗[ℂ] Specht b) _ _ _ _ _ _ _
    (spechtRep t) ((spechtRep a).tprod (spechtRep b))

/- Column permutations cannot also fix the row word unless they are identity. -/

end Saxl

end

end OAI
end

section
-- module Solutions.OAIQ259_US.Saxl_HorizontalRemoval
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped TensorProduct

namespace Saxl

lemma rowPrefix_mono (μ : YoungDiagram) {k l : ℕ} (h : k ≤ l) :
    rowPrefix μ k ≤ rowPrefix μ l :=
  Finset.sum_le_sum_of_subset (Finset.range_mono h)

end Saxl

end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Band_TwoStrip
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Two Strip. -/

section

noncomputable section

namespace Saxl.Balance

lemma ofRowLens_height (A : List ℕ) (hA : A.SortedGE) :
    (YoungDiagram.ofRowLens A hA).colLen 0 ≤ A.length := by
  by_contra hh
  have h := YoungDiagram.mem_iff_lt_colLen.mpr
    (show A.length < (YoungDiagram.ofRowLens A hA).colLen 0 by omega)
  obtain ⟨h',_⟩ := YoungDiagram.mem_ofRowLens.mp h
  exact (Nat.lt_irrefl _) h'

lemma ofRowLens_rowLen (A : List ℕ) (hA : A.SortedGE) (i : ℕ) :
    (YoungDiagram.ofRowLens A hA).rowLen i = A[i]?.getD 0 := by
  by_cases hi : i < A.length
  · simpa [hi] using YoungDiagram.rowLen_ofRowLens (hw := hA) ⟨i,hi⟩
  · rw [rowLen_zero_of_height_le _ ((ofRowLens_height A hA).trans (by omega))]
    simp [List.getElem?_eq_none (by omega : A.length ≤ i)]

end Saxl.Balance
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Specht_ZeroColumns
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Zero Columns. -/

section

noncomputable section
namespace Saxl.Columns

lemma sum_fin_val_ite (r i : ℕ) :
    (∑ j : Fin r, if j.val = i then (1:ℕ) else 0) = if i < r then 1 else 0 := by
  classical
  by_cases hi : i < r
  · rw [ite_eq_left hi, Finset.sum_eq_single (⟨i,hi⟩ : Fin r)]
    · simp
    · intro j hj hji
      exact ite_eq_right (fun h => hji (Fin.ext h))
    · simp
  · rw [ite_eq_right hi]
    apply Finset.sum_eq_zero
    intro j hj
    exact ite_eq_right (fun h : (j : ℕ) = i => hi (h ▸ j.isLt))

lemma cells_row_count (rs : List ℕ) (i : ℕ) :
    (∑ c : Cells rs, if row c = i then (1:ℕ) else 0) = rs.countP (fun h => i < h) := by
  classical
  induction rs with
  | nil => simp [Cells]
  | cons h rs ih =>
    rw [show (∑ c : Cells (h :: rs), if row c = i then (1:ℕ) else 0) =
      (∑ c : Fin h, if c.val = i then (1:ℕ) else 0) +
        (∑ c : Cells rs, if row c = i then (1:ℕ) else 0) from
      Fintype.sum_sum_type _]
    rw [sum_fin_val_ite, ih, List.countP_cons]
    split_ifs <;> simp_all <;> omega

lemma placed_rowLen {rs : List ℕ} {μ : YoungDiagram} (e : Cells rs ≃ μ.cells)
    (hr : ∀ c, (e c).val.1 = row c) (i : ℕ) :
    μ.rowLen i = rs.countP (fun h => i < h) := by
  classical
  let E : {c : Cells rs // row c = i} ≃ {c : μ.cells // c.val.1 = i} :=
    e.subtypeEquiv (fun c => by rw [hr])
  have hc := Fintype.card_congr (E.trans (rowFiberEquiv μ i))
  rw [Fintype.card_fin, Fintype.card_subtype, Finset.card_filter, cells_row_count] at hc
  exact hc.symm

lemma columnShape_rowLen (rs : List ℕ) (i : ℕ) :
    (columnShape rs).rowLen i = rs.countP (fun h => i < h) := by
  obtain ⟨e,hr,_⟩ := columnShape_placement rs
  exact placed_rowLen e hr i

end Saxl.Columns
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Support_TransposeSupport
attribute [-simp] _root_.OAI.Saxl.Balance.cyclicSquareMap_tmul _root_.OAI.Saxl.orbitTensorEval_tmul _root_.OAI.Saxl.relabelWord_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Transpose Support. -/

section

noncomputable section
open scoped TensorProduct

namespace UniversalTensorSquare

theorem kronecker_pos_transpose_iff {n : ℕ} (lam : YoungDiagram) (hlam : lam.card = n)
    (hself : lam.transpose = lam) (ν : YoungDiagram) (hν : ν.card = n) :
    (0 < Saxl.kronecker (Saxl.canonicalTableau lam hlam)
      (Saxl.canonicalTableau lam hlam) (Saxl.canonicalTableau ν hν)) ↔
    (0 < Saxl.kronecker (Saxl.canonicalTableau lam hlam)
      (Saxl.canonicalTableau lam hlam)
      (Saxl.canonicalTableau ν.transpose ((Saxl.transpose_card ν).trans hν))) := by
  constructor
  · exact kronecker_pos_transpose lam hlam hself ν hν
  · intro h
    have ht := kronecker_pos_transpose lam hlam hself ν.transpose
      ((Saxl.transpose_card ν).trans hν) h
    obtain ⟨f, hf⟩ := (Saxl.kronecker_pos_iff _ _ _).mp ht
    let e := spechtShapeEquiv (YoungDiagram.transpose_transpose ν).symm
      (Saxl.canonicalTableau ν hν)
      (Saxl.canonicalTableau ν.transpose.transpose
        ((Saxl.transpose_card ν.transpose).trans ((Saxl.transpose_card ν).trans hν)))
    apply (Saxl.kronecker_pos_iff _ _ _).mpr
    refine ⟨f.comp e.toIntertwiningMap, ?_⟩
    intro hz
    apply hf
    ext x
    have hh := congrArg (fun F => F (e.symm x)) hz
    change f (e (e.symm x)) = 0 at hh
    simpa using hh

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Support_KroneckerSemigroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Kronecker Semigroup. -/

section

noncomputable section
open scoped TensorProduct
namespace Saxl
open Columns FlagColumns

lemma tableau_card_eq {n : ℕ} {μ : YoungDiagram} (t : Tableau n μ) : μ.card = n := by
  have h := Fintype.card_congr t
  simpa only [Fintype.card_fin,Fintype.card_coe,YoungDiagram.card] using h.symm

end Saxl
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Support_SquareSemigroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Square Semigroup. -/

section

noncomputable section
open scoped TensorProduct
namespace UniversalTensorSquare
open Saxl Columns

lemma kronecker_pos_of_shapes {n : ℕ} {α β μ A B T : YoungDiagram}
    (ha : α = A) (hb : β = B) (ht : μ = T)
    (a : Tableau n α) (b : Tableau n β) (t : Tableau n μ)
    (c : Tableau n A) (d : Tableau n B) (u : Tableau n T)
    (h : 0 < kronecker a b t) : 0 < kronecker c d u := by
  let : AddCommGroup (Specht a ⊗[ℂ] Specht b) := Module.addCommMonoidToAddCommGroup ℂ
  let : AddCommGroup (Specht c ⊗[ℂ] Specht d) := Module.addCommMonoidToAddCommGroup ℂ
  obtain ⟨F,hF⟩ := (kronecker_pos_iff a b t).mp h
  let e := tensorRepEquiv (spechtShapeEquiv ha a c) (spechtShapeEquiv hb b d)
  let f := spechtShapeEquiv ht.symm u t
  apply (kronecker_pos_iff c d u).mpr
  refine ⟨e.toIntertwiningMap.comp (F.comp f.toIntertwiningMap),?_⟩
  intro hz
  apply hF
  ext x
  apply e.injective
  have hh := congrArg (fun H => H (f.symm x)) hz
  change e (F (f (f.symm x))) = 0 at hh
  change e (F x) = e (0 : Specht a ⊗[ℂ] Specht b)
  have hx : e (F x) = 0 := by simpa only [f.apply_symm_apply] using hh
  exact hx.trans e.toIntertwiningMap.toLinearMap.map_zero.symm

lemma SquareOccurs.card_eq {α μ : YoungDiagram} (h : SquareOccurs α μ) :
    α.card = μ.card := by
  obtain ⟨n,a,t,_⟩ := h
  exact (tableau_card_eq a).trans (tableau_card_eq t).symm

lemma SquareOccurs.pos {n : ℕ} {α μ : YoungDiagram} (h : SquareOccurs α μ)
    (a : Tableau n α) (t : Tableau n μ) : 0 < kronecker a a t := by
  obtain ⟨m,b,u,hu⟩ := h
  have he : m = n := (tableau_card_eq b).symm.trans (tableau_card_eq a)
  subst m
  exact kronecker_pos_of_shapes rfl rfl rfl b b u a a t hu

lemma SquareOccurs.target_transpose {α μ : YoungDiagram}
    (hs : α.transpose = α) (h : SquareOccurs α μ) : SquareOccurs α μ.transpose := by
  have he := h.card_eq
  let a := canonicalTableau α rfl
  let t := canonicalTableau μ he.symm
  exact ⟨α.card,a,transposeTableau t,kronecker_pos_of_shapes rfl rfl rfl _ _ _ _ _ _
    (kronecker_pos_transpose α rfl hs μ he.symm (h.pos a t))⟩

lemma columnShape_perm {rs ss : List ℕ} (h : rs.Perm ss) :
    columnShape rs = columnShape ss := by
  apply YoungDiagram.ext
  ext ⟨i,j⟩
  simp only [YoungDiagram.mem_cells,YoungDiagram.mem_iff_lt_rowLen]
  rw [columnShape_rowLen,columnShape_rowLen,h.countP_eq]

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Contraction_RowCertificates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Row Certificates. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma rowDiagram_rows {rs : List ℕ} (h : GoodRows rs) : (rowDiagram rs).rowLens = rs := by
  rw [rowDiagram_eq rs h,YoungDiagram.rowLens_ofRowLens_eq_self h.2]

lemma rowDiagram_rowLens (μ : YoungDiagram) : rowDiagram μ.rowLens = μ := by
  rw [rowDiagram_eq _ ⟨μ.rowLens_sorted,μ.pos_of_mem_rowLens⟩,
    YoungDiagram.ofRowLens_to_rowLens_eq_self]

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Support_NumericalSupport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Numerical Support. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

lemma headD_rowLens (μ : YoungDiagram) : μ.rowLens.headD 0 = μ.rowLen 0 := by
  have h (xs : List ℕ) : xs.headD 0 = xs[0]?.getD 0 := by cases xs <;> rfl
  rw [h, ← ofRowLens_rowLen μ.rowLens μ.rowLens_sorted,
    YoungDiagram.ofRowLens_to_rowLens_eq_self]

lemma transposeRows_rowLens (μ : YoungDiagram) :
    transposeRows μ.rowLens = μ.transpose.rowLens := by
  unfold transposeRows
  rw [headD_rowLens]
  conv_rhs => rw [YoungDiagram.rowLens,YoungDiagram.colLen_transpose]
  apply List.map_congr_left
  intro j _
  rw [YoungDiagram.rowLen_transpose]
  have he := congrArg (fun θ : YoungDiagram => θ.colLen j) (rowDiagram_rowLens μ)
  simpa only [rowDiagram,YoungDiagram.colLen_transpose,columnShape_rowLen] using he

lemma rowDiagram_transposeRows {rs : List ℕ} (h : GoodRows rs) :
    rowDiagram (transposeRows rs) = (rowDiagram rs).transpose := by
  rw [transposeRows_eq h,rowDiagram_rowLens]

end UniversalTensorSquare

end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Capacity_RegionExhaustion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Region Exhaustion. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

lemma boundsEntail_sound {A B : List (ℕ × ℕ)} (h : boundsEntail A B)
    (μ : YoungDiagram) (ha : RowBounds μ A) : RowBounds μ B := by
  intro p hp
  obtain ⟨hpos,q,hq,hk,hv⟩ := h p hp
  exact ⟨hpos,((rowPrefix_mono μ hk).trans (ha q hq).2).trans hv⟩

theorem candidate_semantic_pos {n M b δ r : ℕ} (hM : 4 ≤ M)
    (hδ : δ ≤ 1) (hr : r = 2*b+δ) (hrpos : 0 < r)
    (hn : (candidate M b δ).card = n)
    (q : List ℕ) (hq : GoodRows q) (hqn : q.sum = n)
    (p : PackingPlan) (hv : p.Valid (M+b+δ)) (hbands : BandsValid p.bands)
    (hcols : p.columns.Perm ([M+b+δ,M-1+b] ++
      (List.range' 3 (M-4)).reverse ++ List.replicate (b+1) 2 ++ List.replicate (1+δ) 1))
    (hparts : p.parts.Perm q) (P : List ℕ → Prop)
    (hP : ∀ rs, GoodRows rs → rs.sum = n → P rs → SquareOccurs (candidate M b δ) (rowDiagram rs))
    (check : ∀ d ∈ List.range 5, ∀ e ∈ List.range 5,
      ∀ a ∈ List.range q.length, ∀ c ∈ List.range q.length,
        semanticResidualCheck n M r (d+1) (e+1) (a+1) (c+1) q P)
    (μ : YoungDiagram) (hμ : μ.card = n) :
    0 < kronecker (canonicalTableau (candidate M b δ) hn)
      (canonicalTableau (candidate M b δ) hn) (canonicalTableau μ hμ) := by
  have hposn : 0 < n := by rw [← hn,candidate_card _ _ _ (by omega)]; omega
  have hp : ∀ a ∈ p.parts, 0 < a := fun a ha => hq.2 a (hparts.mem_iff.mp ha)
  have hshape : (columnShape p.parts).transpose = rowDiagram q := by
    rw [columnShape_perm hparts]; rfl
  have hh : (candidate M b δ).colLen 0 = M+b+δ := by
    rw [candidate_colLen _ _ _ _ hM]; simp [candidateLengths]
  have hc : p.columns.Perm (candidate M b δ).transpose.rowLens := by
    rw [candidate_transpose,candidate_rowLens hM]; exact hcols
  have cone (ν : YoungDiagram) (hν : ν.card = n) (hd : Dominates ν (rowDiagram q)) :
      0 < kronecker (canonicalTableau (candidate M b δ) hn)
        (canonicalTableau (candidate M b δ) hn) (canonicalTableau ν hν) := by
    apply packingPlan_pos p hv hbands hh hc hp
    simpa only [hshape] using hd
  have htcheck : ∀ d ∈ List.range 5, ∀ e ∈ List.range 5,
      ∀ a ∈ List.range (rowDiagram q).rowLens.length, ∀ c ∈ List.range (rowDiagram q).rowLens.length,
        semanticResidualCheck n M r (d+1) (e+1) (a+1) (c+1) (rowDiagram q).rowLens P := by
    simpa only [rowDiagram_rows hq] using check
  rcases semantic_capacity_dichotomy μ (rowDiagram q) hposn (by omega) hrpos hμ
    ((rowDiagram_card q).trans hqn) P htcheck with h | h | h | h | h
  · exact band_kronecker_pos hM hδ hr _ μ _ h
  · apply (kronecker_pos_transpose_iff _ hn (candidate_transpose M b δ) μ hμ).mpr
    exact band_kronecker_pos hM hδ hr _ μ.transpose _ h
  · exact cone μ hμ h
  · apply (kronecker_pos_transpose_iff _ hn (candidate_transpose M b δ) μ hμ).mpr
    exact cone μ.transpose ((transpose_card μ).trans hμ) h
  · have ht := hP μ.rowLens ⟨μ.rowLens_sorted,μ.pos_of_mem_rowLens⟩
      ((card_eq_sum_rowLens μ).symm.trans hμ) h
    rw [rowDiagram_rowLens] at ht
    exact ht.pos _ _

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Support_ResidualTrees
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Residual Trees. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

namespace RowTree

lemma find_sound {P : List ℕ → Prop} {t : RowTree} (h : t.All P)
    {rs : List ℕ} (hf : t.find rs = true) : P rs := by
  induction t with
  | empty => simp [find] at hf
  | node key l r hl hr =>
    simp only [find] at hf
    obtain ⟨hk,hL,hR⟩ := h
    split_ifs at hf with he hc
    · simpa only [he] using hk
    · exact hl hL hf
    · exact hr hR hf

end RowTree

lemma treeResidual_sound {n M b δ r : ℕ} (hM : 4 ≤ M) (hδ : δ ≤ 1)
    (hn : (candidate M b δ).card = n) (hre : r = 2*b+δ)
    {qs : List (List ℕ)} {t : RowTree}
    (hcones : ∀ q ∈ qs, ∀ μ : YoungDiagram, μ.card = n →
      RowsDom μ.rowLens q → SquareOccurs (candidate M b δ) μ)
    (htree : t.All (fun rs => SquareOccurs (candidate M b δ) (rowDiagram rs)))
    {rs : List ℕ} (hgood : GoodRows rs) (hsum : rs.sum = n)
    (h : TreeResidual M r qs t rs) : SquareOccurs (candidate M b δ) (rowDiagram rs) := by
  rcases h with h | h | h
  · exact residualProperty_sound hM hδ hn hre hcones (by simp) hgood hsum h
  · exact RowTree.find_sound htree h
  · have hh := RowTree.find_sound htree h
    rw [rowDiagram_transposeRows hgood] at hh
    simpa only [YoungDiagram.transpose_transpose] using
      hh.target_transpose (candidate_transpose M b δ)

lemma rowDiagram_candidate {M b δ : ℕ} (hM : 4 ≤ M) :
    rowDiagram ([M+b+δ,M-1+b] ++ (List.range' 3 (M-4)).reverse ++
      List.replicate (b+1) 2 ++ List.replicate (1+δ) 1) = candidate M b δ := by
  rw [← candidate_rowLens hM, rowDiagram_rowLens]

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_DegreePlans26
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Degree Plans 26. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

lemma degreeCones26 : ∀ q ∈ degreeQs26, ∀ μ : YoungDiagram, μ.card = 26 →
    RowsDom μ.rowLens q → SquareOccurs (candidate 4 4 0) μ := by
  intro q hq
  simp only [degreeQs26,List.not_mem_nil] at hq

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_DegreeCover26
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Degree Cover 26. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

lemma degreeCover26_0_0 :
    ∀ a ∈ List.range degreeRows26_0.length, ∀ c ∈ List.range degreeRows26_0.length,
      regionCheck 26 4 8 1 1 (a+1) (c+1) degreeRows26_0 degreeRegions26 := by
  decide +kernel

lemma degreeCover26_0_1 :
    ∀ a ∈ List.range degreeRows26_0.length, ∀ c ∈ List.range degreeRows26_0.length,
      regionCheck 26 4 8 1 2 (a+1) (c+1) degreeRows26_0 degreeRegions26 := by
  decide +kernel

lemma degreeCover26_0_2 :
    ∀ a ∈ List.range degreeRows26_0.length, ∀ c ∈ List.range degreeRows26_0.length,
      regionCheck 26 4 8 1 3 (a+1) (c+1) degreeRows26_0 degreeRegions26 := by
  decide +kernel

lemma degreeCover26_0_3 :
    ∀ a ∈ List.range degreeRows26_0.length, ∀ c ∈ List.range degreeRows26_0.length,
      regionCheck 26 4 8 1 4 (a+1) (c+1) degreeRows26_0 degreeRegions26 := by
  decide +kernel

lemma degreeCover26_0_4 :
    ∀ a ∈ List.range degreeRows26_0.length, ∀ c ∈ List.range degreeRows26_0.length,
      regionCheck 26 4 8 1 5 (a+1) (c+1) degreeRows26_0 degreeRegions26 := by
  decide +kernel

lemma degreeCover26_1_0 :
    ∀ a ∈ List.range degreeRows26_0.length, ∀ c ∈ List.range degreeRows26_0.length,
      regionCheck 26 4 8 2 1 (a+1) (c+1) degreeRows26_0 degreeRegions26 := by
  decide +kernel

lemma degreeCover26_1_1 :
    ∀ a ∈ List.range degreeRows26_0.length, ∀ c ∈ List.range degreeRows26_0.length,
      regionCheck 26 4 8 2 2 (a+1) (c+1) degreeRows26_0 degreeRegions26 := by
  decide +kernel

lemma degreeCover26_1_2 :
    ∀ a ∈ List.range degreeRows26_0.length, ∀ c ∈ List.range degreeRows26_0.length,
      regionCheck 26 4 8 2 3 (a+1) (c+1) degreeRows26_0 degreeRegions26 := by
  decide +kernel

lemma degreeCover26_1_3 :
    ∀ a ∈ List.range degreeRows26_0.length, ∀ c ∈ List.range degreeRows26_0.length,
      regionCheck 26 4 8 2 4 (a+1) (c+1) degreeRows26_0 degreeRegions26 := by
  decide +kernel

lemma degreeCover26_1_4 :
    ∀ a ∈ List.range degreeRows26_0.length, ∀ c ∈ List.range degreeRows26_0.length,
      regionCheck 26 4 8 2 5 (a+1) (c+1) degreeRows26_0 degreeRegions26 := by
  decide +kernel

lemma degreeCover26_2_0 :
    ∀ a ∈ List.range degreeRows26_0.length, ∀ c ∈ List.range degreeRows26_0.length,
      regionCheck 26 4 8 3 1 (a+1) (c+1) degreeRows26_0 degreeRegions26 := by
  decide +kernel

lemma degreeCover26_2_1 :
    ∀ a ∈ List.range degreeRows26_0.length, ∀ c ∈ List.range degreeRows26_0.length,
      regionCheck 26 4 8 3 2 (a+1) (c+1) degreeRows26_0 degreeRegions26 := by
  decide +kernel

lemma degreeCover26_2_2 :
    ∀ a ∈ List.range degreeRows26_0.length, ∀ c ∈ List.range degreeRows26_0.length,
      regionCheck 26 4 8 3 3 (a+1) (c+1) degreeRows26_0 degreeRegions26 := by
  decide +kernel

lemma degreeCover26_2_3 :
    ∀ a ∈ List.range degreeRows26_0.length, ∀ c ∈ List.range degreeRows26_0.length,
      regionCheck 26 4 8 3 4 (a+1) (c+1) degreeRows26_0 degreeRegions26 := by
  decide +kernel

lemma degreeCover26_2_4 :
    ∀ a ∈ List.range degreeRows26_0.length, ∀ c ∈ List.range degreeRows26_0.length,
      regionCheck 26 4 8 3 5 (a+1) (c+1) degreeRows26_0 degreeRegions26 := by
  decide +kernel

lemma degreeCover26_3_0 :
    ∀ a ∈ List.range degreeRows26_0.length, ∀ c ∈ List.range degreeRows26_0.length,
      regionCheck 26 4 8 4 1 (a+1) (c+1) degreeRows26_0 degreeRegions26 := by
  decide +kernel

lemma degreeCover26_3_1 :
    ∀ a ∈ List.range degreeRows26_0.length, ∀ c ∈ List.range degreeRows26_0.length,
      regionCheck 26 4 8 4 2 (a+1) (c+1) degreeRows26_0 degreeRegions26 := by
  decide +kernel

lemma degreeCover26_3_2 :
    ∀ a ∈ List.range degreeRows26_0.length, ∀ c ∈ List.range degreeRows26_0.length,
      regionCheck 26 4 8 4 3 (a+1) (c+1) degreeRows26_0 degreeRegions26 := by
  decide +kernel

lemma degreeCover26_3_3 :
    ∀ a ∈ List.range degreeRows26_0.length, ∀ c ∈ List.range degreeRows26_0.length,
      regionCheck 26 4 8 4 4 (a+1) (c+1) degreeRows26_0 degreeRegions26 := by
  decide +kernel

lemma degreeCover26_3_4 :
    ∀ a ∈ List.range degreeRows26_0.length, ∀ c ∈ List.range degreeRows26_0.length,
      regionCheck 26 4 8 4 5 (a+1) (c+1) degreeRows26_0 degreeRegions26 := by
  decide +kernel

lemma degreeCover26_4_0 :
    ∀ a ∈ List.range degreeRows26_0.length, ∀ c ∈ List.range degreeRows26_0.length,
      regionCheck 26 4 8 5 1 (a+1) (c+1) degreeRows26_0 degreeRegions26 := by
  decide +kernel

lemma degreeCover26_4_1 :
    ∀ a ∈ List.range degreeRows26_0.length, ∀ c ∈ List.range degreeRows26_0.length,
      regionCheck 26 4 8 5 2 (a+1) (c+1) degreeRows26_0 degreeRegions26 := by
  decide +kernel

lemma degreeCover26_4_2 :
    ∀ a ∈ List.range degreeRows26_0.length, ∀ c ∈ List.range degreeRows26_0.length,
      regionCheck 26 4 8 5 3 (a+1) (c+1) degreeRows26_0 degreeRegions26 := by
  decide +kernel

lemma degreeCover26_4_3 :
    ∀ a ∈ List.range degreeRows26_0.length, ∀ c ∈ List.range degreeRows26_0.length,
      regionCheck 26 4 8 5 4 (a+1) (c+1) degreeRows26_0 degreeRegions26 := by
  decide +kernel

lemma degreeCover26_4_4 :
    ∀ a ∈ List.range degreeRows26_0.length, ∀ c ∈ List.range degreeRows26_0.length,
      regionCheck 26 4 8 5 5 (a+1) (c+1) degreeRows26_0 degreeRegions26 := by
  decide +kernel

lemma degreeCover26 : ∀ d ∈ List.range 5, ∀ e ∈ List.range 5,
    ∀ a ∈ List.range degreeRows26_0.length, ∀ c ∈ List.range degreeRows26_0.length,
      regionCheck 26 4 8 (d+1) (e+1) (a+1) (c+1) degreeRows26_0 degreeRegions26 := by
  intro d hd e he
  have hd' : d < 5 := List.mem_range.mp hd
  have he' : e < 5 := List.mem_range.mp he
  interval_cases d <;> interval_cases e
  · exact degreeCover26_0_0
  · exact degreeCover26_0_1
  · exact degreeCover26_0_2
  · exact degreeCover26_0_3
  · exact degreeCover26_0_4
  · exact degreeCover26_1_0
  · exact degreeCover26_1_1
  · exact degreeCover26_1_2
  · exact degreeCover26_1_3
  · exact degreeCover26_1_4
  · exact degreeCover26_2_0
  · exact degreeCover26_2_1
  · exact degreeCover26_2_2
  · exact degreeCover26_2_3
  · exact degreeCover26_2_4
  · exact degreeCover26_3_0
  · exact degreeCover26_3_1
  · exact degreeCover26_3_2
  · exact degreeCover26_3_3
  · exact degreeCover26_3_4
  · exact degreeCover26_4_0
  · exact degreeCover26_4_1
  · exact degreeCover26_4_2
  · exact degreeCover26_4_3
  · exact degreeCover26_4_4

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_DegreeUnionData26
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Degree Union Data 26. -/

section

namespace UniversalTensorSquare

lemma degreeHalfHeight26 : ∀ R ∈ degreeHalfRegions26, firstBound 26 R.1 ≤ 25 := by decide +kernel

lemma degreeHalfWidth26 : ∀ R ∈ degreeHalfRegions26, firstBound 26 R.2 ≤ 25 := by decide +kernel

end UniversalTensorSquare
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Support_SymmetricRegions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Symmetric Regions. -/

section

namespace UniversalTensorSquare

lemma treeResidual_transpose {M r : ℕ} {qs : List (List ℕ)} {t : RowTree}
    {μ : YoungDiagram} (h : TreeResidual M r qs t μ.transpose.rowLens) :
    TreeResidual M r qs t μ.rowLens := by
  rcases h with h | h | h
  · rcases h with h | h | ⟨q,hq,h | h⟩ | h | h
    · exact Or.inl (Or.inr (Or.inl (by simpa only [transposeRows_rowLens] using h)))
    · exact Or.inl (Or.inl (by simpa only [transposeRows_rowLens,
        YoungDiagram.transpose_transpose] using h))
    · exact Or.inl (Or.inr (Or.inr (Or.inl ⟨q,hq,Or.inr (by
        simpa only [transposeRows_rowLens] using h)⟩)))
    · exact Or.inl (Or.inr (Or.inr (Or.inl ⟨q,hq,Or.inl (by
        simpa only [transposeRows_rowLens,YoungDiagram.transpose_transpose] using h)⟩)))
    · simp at h
    · simp at h
  · exact Or.inr (Or.inr (by simpa only [transposeRows_rowLens] using h))
  · exact Or.inr (Or.inl (by simpa only [transposeRows_rowLens,
      YoungDiagram.transpose_transpose] using h))

lemma regionCheck_sound_diagram {n M r d e a b : ℕ} {q : List ℕ}
    {regions : List PrefixRegion} {P : List ℕ → Prop}
    (hc : ∀ R ∈ regions, ∀ μ : YoungDiagram, μ.card = n →
      RowBounds μ.transpose R.1 → RowBounds μ R.2 → P μ.rowLens)
    (h : regionCheck n M r d e a b q regions) :
    semanticResidualCheck n M r d e a b q P := by
  rcases h with h | h | h | ⟨R,hR,hA,hB⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · refine Or.inr (Or.inr (Or.inr ?_))
    intro μ hμ ha hb
    exact hc R hR μ hμ (boundsEntail_sound hA _ ha) (boundsEntail_sound hB _ hb)

end UniversalTensorSquare
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Support_CheckedUnionSymmetry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Checked Union Symmetry. -/

section

namespace UniversalTensorSquare

lemma checkedUnion_symmetric {n M r H W : ℕ} {qs : List (List ℕ)} {t : RowTree}
    {regions allRegions : List PrefixRegion}
    (check : ∀ h ≤ H, checkRegionPrefixes (quickResidual M r qs t) h n W regions [] = true)
    (height : ∀ R ∈ regions, firstBound n R.1 ≤ H)
    (width : ∀ R ∈ regions, firstBound n R.2 ≤ W)
    (cover : ∀ R ∈ allRegions, R ∈ regions ∨ (R.2,R.1) ∈ regions) :
    ∀ R ∈ allRegions, ∀ μ : YoungDiagram, μ.card = n →
      RowBounds μ.transpose R.1 → RowBounds μ R.2 → TreeResidual M r qs t μ.rowLens := by
  intro R hR μ hμ hA hB
  rcases cover R hR with h | h
  · exact checkedRegion_diagram check μ hμ h hA hB (height R h) (width R h)
  · apply treeResidual_transpose
    apply checkedRegion_diagram check μ.transpose ((Saxl.transpose_card μ).trans hμ) h
    · simpa only [YoungDiagram.transpose_transpose] using hB
    · exact hA
    · exact height _ h
    · exact width _ h

end UniversalTensorSquare
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_DegreeRegions26
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Degree Regions 26. -/

section

namespace UniversalTensorSquare

lemma degreeHalfCover26 : ∀ R ∈ degreeRegions26,
    R ∈ degreeHalfRegions26 ∨ (R.2,R.1) ∈ degreeHalfRegions26 := by decide +kernel

lemma degreeDiagramRegionsChecked26 : ∀ R ∈ degreeRegions26,
    ∀ μ : YoungDiagram, μ.card = 26 → RowBounds μ.transpose R.1 →
      RowBounds μ R.2 → degreeP26 μ.rowLens :=
  checkedUnion_symmetric degreeUnionCheck26 degreeHalfHeight26 degreeHalfWidth26
    degreeHalfCover26

end UniversalTensorSquare
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_DegreeChecks26
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Degree Checks 26. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

lemma degreeCheck26 : ∀ d ∈ List.range 5, ∀ e ∈ List.range 5,
    ∀ a ∈ List.range degreeRows26_0.length, ∀ c ∈ List.range degreeRows26_0.length,
      semanticResidualCheck 26 4 8 (d+1) (e+1) (a+1) (c+1) degreeRows26_0 degreeP26 := by
  intro d hd e he a ha c hc
  exact regionCheck_sound_diagram degreeDiagramRegionsChecked26 (degreeCover26 d hd e he a ha c hc)

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

lemma sg69 : RowSquare [3,1,1,1] [3,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg33

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 1. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg1147 : RowSquare [3,3,1,1,1,1,1] [3,3,2,2,1] := by
  exact rowSquare_join (by decide) sg32 sg88

lemma sg1154 : RowSquare [3,3,1,1,1,1,1] [4,3,3,1] := by
  exact rowSquare_join (by decide) sg33 sg89

lemma sg1163 : RowSquare [3,3,1,1,1,1,1] [5,4,2] := by
  exact rowSquare_join (by decide) sg34 sg91

lemma sg1213 : RowSquare [4,3,1,1,1,1] [4,3,3,1] := by
  exact rowSquare_join (by decide) sg0 sg768

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes6
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 6. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg3278 : RowSquare [5,4,1,1,1,1,1,1] [3,3,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg68 sg586

lemma sg3280 : RowSquare [5,4,1,1,1,1,1,1] [4,2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg69 sg586

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes25
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 25. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg10901 : RowSquare [7,6,2,2,2,2,1] [4,3,3,3,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg1213 sg1163

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes28
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 28. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg11783 : RowSquare [7,6,2,2,2,2,2,1] [6,3,3,3,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg1 sg10901

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Semigroup_SemigroupNodes31
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Semigroup Nodes 31. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma sg13103 : RowSquare [8,7,2,2,2,2,2,1] [7,5,4,4,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1147 sg3280

lemma sg13169 : RowSquare [8,7,2,2,2,2,2,1] [7,6,6,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1154 sg3278

lemma sg13235 : RowSquare [8,7,2,2,2,2,2,1] [8,3,3,3,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg1 sg11783

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_DegreeTreeProof26
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Degree Tree Proof 26. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

lemma degreeTree26_29All : degreeTree26_29.All (RowSquare [8,7,2,2,2,2,2,1]) := by
  exact ⟨sg13169,degreeTree26_21All,degreeTree26_28All⟩

lemma degreeTree26_30All : degreeTree26_30.All (RowSquare [8,7,2,2,2,2,2,1]) := by
  exact ⟨sg13103,degreeTree26_14All,degreeTree26_29All⟩

lemma degreeTree26_62All : degreeTree26_62.All (RowSquare [8,7,2,2,2,2,2,1]) := by
  exact ⟨sg13235,degreeTree26_30All,degreeTree26_61All⟩

lemma degreeTreeAll26 : degreeTree26.All
    (fun rs => SquareOccurs (candidate 4 4 0) (rowDiagram rs)) := by
  have hp : rowDiagram [8,7,2,2,2,2,2,1] = candidate 4 4 0 := rowDiagram_candidate (M := 4) (b := 4) (δ := 0) (by decide)
  rw [← hp]
  exact degreeTree26_62All

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_NumericalDegree26
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Numerical Degree 26. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

lemma degree_pos26_oai (μ : YoungDiagram) (hμ : μ.card = 26) :
    0 < kronecker (canonicalTableau (candidate 4 4 0) degreeCard26)
      (canonicalTableau (candidate 4 4 0) degreeCard26) (canonicalTableau μ hμ) := by
  apply candidate_semantic_pos (r := 8) (by decide) (by decide) rfl (by decide)
    degreeCard26 degreeRows26_0 (by decide) (by decide)
    degreePlan26_0 (by decide) (by decide) (by decide) (by decide) degreeP26 ?_
    degreeCheck26 μ hμ
  intro rs hr hn hh
  exact treeResidual_sound (by decide) (by decide) degreeCard26 rfl degreeCones26
    degreeTreeAll26 hr hn hh

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degree_pos26_oai := @OAI.UniversalTensorSquare.degree_pos26_oai
