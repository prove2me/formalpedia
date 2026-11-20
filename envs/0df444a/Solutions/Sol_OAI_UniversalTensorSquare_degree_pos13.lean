-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degree_pos13
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T04:12:39.786208+00:00
-- url     : https://prove2.me/submissions/cebe648f-fa56-4bdc-8cec-fbc901bd87b9

import Mathlib
import Definitions.Def_UniversalTensorSquares
import Definitions.Def_OAIQ259US004
import Definitions.Def_OAIQ259US021
import Definitions.Def_OAIQ259US022
import Definitions.Def_OAIQ259US001
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US006
import Theorems.Thm_OAI_UniversalTensorSquare_kronecker_pos_transpose
import Theorems.Thm_OAI_UniversalTensorSquare_rowDiagram_eq
import Theorems.Thm_OAI_UniversalTensorSquare_smallSupports13
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


lemma rowPrefix_succ (μ : YoungDiagram) (k : ℕ) :
    rowPrefix μ (k+1) = rowPrefix μ k + μ.rowLen k := by
  simp [rowPrefix, Finset.sum_range_succ]

lemma rowPrefix_le_card (μ : YoungDiagram) (k : ℕ) : rowPrefix μ k ≤ μ.card := by
  rw [← rowPrefix_eq_card μ (Nat.le_max_left _ k)]
  exact Finset.sum_le_sum_of_subset (Finset.range_mono (Nat.le_max_right _ _))

lemma rowPrefix_mono (μ : YoungDiagram) {k l : ℕ} (h : k ≤ l) :
    rowPrefix μ k ≤ rowPrefix μ l :=
  Finset.sum_le_sum_of_subset (Finset.range_mono h)

end Saxl

end

end OAI
end

section
-- module Solutions.OAIQ259_US.Saxl_DominatedSupport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped TensorProduct

universe uX uY

namespace Saxl

lemma colTruncate_rowLen (μ : YoungDiagram) (k i : ℕ) :
    (colTruncate μ k).rowLen i = min k (μ.rowLen i) := by
  have hh : ∀ j, j < (colTruncate μ k).rowLen i ↔ j < min k (μ.rowLen i) := by
    intro j
    rw [← YoungDiagram.mem_iff_lt_rowLen]
    change (i,j) ∈ (rowTruncate μ.transpose k).transpose ↔ _
    rw [YoungDiagram.mem_transpose]
    change (j,i) ∈ rowTruncate μ.transpose k ↔ _
    rw [mem_rowTruncate, YoungDiagram.mem_transpose]
    simp only [Prod.swap_prod_mk, YoungDiagram.mem_iff_lt_rowLen, lt_min_iff]
    omega
  have h₁ := hh ((colTruncate μ k).rowLen i)
  have h₂ := hh (min k (μ.rowLen i))
  omega

lemma colTruncate_height (μ : YoungDiagram) (k : ℕ) :
    (colTruncate μ k).colLen 0 ≤ μ.colLen 0 := by
  by_contra h
  have hm : (μ.colLen 0,0) ∈ colTruncate μ k := YoungDiagram.mem_iff_lt_colLen.mpr (by omega)
  have hr := YoungDiagram.mem_iff_lt_rowLen.mp hm
  rw [colTruncate_rowLen, rowLen_zero_of_height_le μ le_rfl] at hr
  simp at hr

open scoped MonoidAlgebra

end Saxl

end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Capacity_Capacity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Capacity. -/

section

noncomputable section

namespace UniversalTensorSquare

open Saxl

lemma colTruncate_card (μ : YoungDiagram) (i : ℕ) :
    (colTruncate μ i).card = colPrefix μ i := by
  rw [colTruncate, Saxl.transpose_card, rowTruncate_card, colPrefix]

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Balance_BalanceDominance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Balance Dominance. -/

section

noncomputable section

namespace UniversalTensorSquare
open Saxl

lemma colPrefix_eq_min_sum (μ : YoungDiagram) (k : ℕ) :
    colPrefix μ k = ∑ i ∈ Finset.range (μ.colLen 0), min k (μ.rowLen i) := by
  rw [← colTruncate_card, ← rowPrefix_eq_card _ (colTruncate_height μ k)]
  exact Finset.sum_congr rfl (fun i _ => colTruncate_rowLen μ k i)

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Capacity_RefinedExhaustion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Refined Exhaustion. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl

lemma minHeight_sound {n : ℕ} (hn : 0 < n) (μ : YoungDiagram)
    (hcard : μ.card = n) {B : List (ℕ × ℕ)} (hb : RowBounds μ B) :
    minHeight n B ≤ μ.colLen 0 := by
  have hpos : 0 < μ.colLen 0 := by
    have hc := rowPrefix_eq_card μ (k := 0)
    by_contra h
    have hz := hc (by omega)
    simp only [rowPrefix,Finset.range_zero,Finset.sum_empty] at hz
    omega
  induction B with
  | nil => exact hpos
  | cons p B ih =>
    have hp := hb p (by simp)
    have htail : RowBounds μ B := fun q hq => hb q (by simp [hq])
    simp only [minHeight,List.foldr_cons]
    split_ifs with hh
    · apply max_le _ (ih htail)
      by_contra h
      have := rowPrefix_eq_card μ (show μ.colLen 0 ≤ p.1 by omega)
      omega
    · exact ih htail

lemma rowLen_first_le_prefix (μ : YoungDiagram) {i : ℕ} (hi : 0 < i) :
    μ.rowLen 0 ≤ rowPrefix μ i := by
  have h := rowPrefix_mono μ (show 1 ≤ i from hi)
  simpa [rowPrefix] using h

lemma rowPrefix_eq_take (μ : YoungDiagram) (k : ℕ) :
    rowPrefix μ k = (μ.rowLens.take k).sum := by
  induction k with
  | zero => simp [rowPrefix]
  | succ k ih =>
    rw [rowPrefix_succ,ih]
    by_cases hk : k < μ.rowLens.length
    · rw [List.take_succ_eq_append_getElem hk, List.sum_append, List.sum_singleton]
      congr 1
      exact YoungDiagram.get_rowLens.symm
    · have hh : μ.colLen 0 ≤ k := by simpa only [YoungDiagram.length_rowLens] using Nat.le_of_not_gt hk
      rw [rowLen_zero_of_height_le μ hh,add_zero]
      rw [List.take_of_length_le (Nat.le_of_not_gt hk),
        List.take_of_length_le (by omega : μ.rowLens.length ≤ k+1)]

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Support_ConstrainedRows
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Constrained Rows. -/

section

namespace UniversalTensorSquare

lemma list_sum_le_mul_length {rs : List ℕ} {b : ℕ} (h : ∀ a ∈ rs, a ≤ b) :
    rs.sum ≤ rs.length*b := by
  induction rs with
  | nil => simp
  | cons a rs ih =>
    have ha := h a (by simp)
    have hr := ih (fun x hx => h x (by simp [hx]))
    simp only [List.sum_cons,List.length_cons]
    nlinarith

lemma clippedSum_length_le {rs : List ℕ} (hp : ∀ a ∈ rs, 0 < a) {k : ℕ} (hk : 0 < k) :
    rs.length ≤ clippedSum rs k := by
  induction rs with
  | nil => simp [clippedSum]
  | cons a rs ih =>
    have ha := hp a (by simp)
    have ht := ih (fun x hx => hp x (by simp [hx]))
    simp only [clippedSum,List.map_cons,List.sum_cons,List.length_cons] at *
    have : 1 ≤ min k a := le_min hk ha
    omega

lemma clippedSum_proportion {rs : List ℕ} {upper k : ℕ}
    (hu : ∀ a ∈ rs, a ≤ upper) : rs.sum * min k upper ≤ clippedSum rs k * upper := by
  induction rs with
  | nil => simp [clippedSum]
  | cons a rs ih =>
    have ha := hu a (by simp)
    have ht := ih (fun x hx => hu x (by simp [hx]))
    have hm : a * min k upper ≤ min k a * upper := by
      by_cases hk : k ≤ a
      · rw [min_eq_left hk, min_eq_left (hk.trans ha)]
        exact Nat.mul_le_mul_right k ha |>.trans_eq (Nat.mul_comm upper k)
      · rw [min_eq_right (by omega : a ≤ k)]
        exact Nat.mul_le_mul_left a (min_le_right _ _)
    simp only [clippedSum,List.map_cons,List.sum_cons] at *
    nlinarith

lemma cross_product_bound (xs ys : List ℕ)
    (h : ∀ a ∈ xs, ∀ b ∈ ys, b ≤ a) : ys.sum*xs.length ≤ xs.sum*ys.length := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
    have ha := list_sum_le_mul_length (fun b hb => h a (by simp) b hb)
    have ht := ih (fun c hc b hb => h c (by simp [hc]) b hb)
    simp only [List.sum_cons,List.length_cons]
    nlinarith

lemma rowSum_proportion {rs : List ℕ} (hs : rs.SortedGE) (k : ℕ) :
    rs.sum * min k rs.length ≤ (rs.take k).sum * rs.length := by
  have he : (rs.take k ++ rs.drop k).Pairwise (· ≥ ·) := by
    simpa only [List.take_append_drop] using hs.pairwise
  have hh := cross_product_bound (rs.take k) (rs.drop k) (List.pairwise_append.mp he).2.2
  have hl : (rs.take k).length + (rs.drop k).length = rs.length := by
    rw [← List.length_append,List.take_append_drop]
  have ht : (rs.take k).sum + (rs.drop k).sum = rs.sum := by
    rw [← List.sum_append,List.take_append_drop]
  rw [List.length_take] at hh hl
  calc
    rs.sum * min k rs.length = ((rs.take k).sum + (rs.drop k).sum)*min k rs.length := by rw [ht]
    _ = (rs.take k).sum*min k rs.length + (rs.drop k).sum*min k rs.length := by ring
    _ ≤ (rs.take k).sum*min k rs.length + (rs.take k).sum*(rs.drop k).length := Nat.add_le_add_left hh _
    _ = (rs.take k).sum*(min k rs.length+(rs.drop k).length) := by ring
    _ = _ := by rw [hl]

lemma rejectedRows_false {rs : List ℕ} {fuel n upper : ℕ} {A B : List (ℕ × ℕ)}
    (hlen : rs.length = fuel) (hsum : rs.sum = n) (hp : ∀ a ∈ rs, 0 < a)
    (hu : ∀ a ∈ rs, a ≤ upper) (hs : rs.SortedGE)
    (ha : ListColBounds rs A) (hb : ListRowBounds rs B) :
    ¬rejectedRows fuel n upper A B := by
  intro hh
  have hlo : fuel ≤ n := by
    rw [← hlen,← hsum]
    exact List.length_le_sum_of_one_le _ hp
  have hhi : n ≤ fuel*upper := by rw [← hsum,← hlen]; exact list_sum_le_mul_length hu
  rcases hh with h | h | ⟨p,hp',hpk,hpU⟩ | ⟨p,hp',hpk,hpU⟩ | ⟨p,hp',hpU⟩ | ⟨p,hp',hpU⟩
  · omega
  · omega
  · have hw := (clippedSum_length_le hp hpk).trans (ha p hp')
    omega
  · have hw := hb p hp'
    rw [List.take_of_length_le (hlen ▸ hpk),hsum] at hw
    omega
  · have hh := (clippedSum_proportion (k := p.1) hu).trans
      (Nat.mul_le_mul_right upper (ha p hp'))
    rw [hsum] at hh
    omega
  · have hh := (rowSum_proportion hs p.1).trans (Nat.mul_le_mul_right rs.length (hb p hp'))
    rw [hsum,hlen] at hh
    omega

lemma allowedRow_cons {a : ℕ} {rs : List ℕ} {A B : List (ℕ × ℕ)}
    (ha : ListColBounds (a::rs) A) (hb : ListRowBounds (a::rs) B) :
    allowedRow a A B := by
  constructor
  · intro p hp
    have hh := ha p hp
    simp only [clippedSum,List.map_cons,List.sum_cons] at hh
    omega
  · intro p hp hk
    have hh := hb p hp
    obtain ⟨k,hk'⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : p.1 ≠ 0)
    simp only [hk',List.take_succ_cons,List.sum_cons] at hh
    omega

lemma clipBudget_cons {a : ℕ} {rs : List ℕ} {A : List (ℕ × ℕ)}
    (ha : ListColBounds (a::rs) A) : ListColBounds rs (clipBudget A a) := by
  intro p hp
  obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hp
  have hh := ha q hq
  simp only [clippedSum,List.map_cons,List.sum_cons] at hh ⊢
  omega

lemma rowBudget_cons {a : ℕ} {rs : List ℕ} {B : List (ℕ × ℕ)}
    (hb : ListRowBounds (a::rs) B) : ListRowBounds rs (rowBudget B a) := by
  intro p hp
  obtain ⟨q,hq,he⟩ := List.mem_filterMap.mp hp
  split_ifs at he with hk
  · have hh := hb q hq
    have heq := Option.some.inj he
    subst p
    have ht : q.1 = (q.1-1)+1 := by omega
    rw [ht,List.take_succ_cons,List.sum_cons] at hh
    dsimp only
    omega

lemma mem_constrainedRows (fuel : ℕ) (rs : List ℕ) (n upper : ℕ) (A B : List (ℕ × ℕ))
    (hlen : rs.length = fuel) (hsum : rs.sum = n) (hp : ∀ a ∈ rs, 0 < a)
    (hu : ∀ a ∈ rs, a ≤ upper) (hs : rs.SortedGE)
    (ha : ListColBounds rs A) (hb : ListRowBounds rs B) :
    rs ∈ constrainedRows fuel n upper A B := by
  have hr := rejectedRows_false hlen hsum hp hu hs ha hb
  induction fuel generalizing rs n upper A B with
  | zero =>
    have he : rs = [] := List.length_eq_zero_iff.mp hlen
    subst rs
    simp only [List.sum_nil] at hsum
    subst n
    simp [constrainedRows,hr]
  | succ fuel ih =>
    cases rs with
    | nil => simp at hlen
    | cons a rs =>
      rw [constrainedRows,ite_eq_right hr]
      apply List.mem_flatMap.mpr
      have hap := hp a (by simp)
      have hau := hu a (by simp)
      have han : a ≤ n := by simp only [List.sum_cons] at hsum; omega
      refine ⟨a,?_,?_⟩
      · simp only [List.mem_range'_1]
        omega
      · have haall : ∀ x ∈ a::rs, x ≤ a := by
          intro x hx
          rcases List.mem_cons.mp hx with rfl | hx
          · exact le_rfl
          · exact (List.pairwise_cons.mp hs.pairwise).1 x hx
        have hlim : n ≤ (fuel+1)*a := by
          have hh := list_sum_le_mul_length haall
          rw [hsum,hlen] at hh
          exact hh
        rw [ite_eq_left ⟨allowedRow_cons ha hb,hlim⟩]
        apply List.mem_map.mpr
        refine ⟨rs,ih rs (n-a) a (clipBudget A a) (rowBudget B a) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_,rfl⟩
        · simpa only [List.length_cons,Nat.succ.injEq] using hlen
        · simp only [List.sum_cons] at hsum; omega
        · exact fun x hx => hp x (by simp [hx])
        · exact fun x hx => (List.pairwise_cons.mp hs.pairwise).1 x hx
        · exact (List.pairwise_cons.mp hs.pairwise).2.sortedGE
        · exact clipBudget_cons ha
        · exact rowBudget_cons hb
        · apply rejectedRows_false
          · simpa only [List.length_cons,Nat.succ.injEq] using hlen
          · simp only [List.sum_cons] at hsum; omega
          · exact fun x hx => hp x (by simp [hx])
          · exact fun x hx => (List.pairwise_cons.mp hs.pairwise).1 x hx
          · exact (List.pairwise_cons.mp hs.pairwise).2.sortedGE
          · exact clipBudget_cons ha
          · exact rowBudget_cons hb

end UniversalTensorSquare
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

lemma rowDiagram_rowLens (μ : YoungDiagram) : rowDiagram μ.rowLens = μ := by
  rw [rowDiagram_eq _ ⟨μ.rowLens_sorted,μ.pos_of_mem_rowLens⟩,
    YoungDiagram.ofRowLens_to_rowLens_eq_self]

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Support_ConstrainedDiagrams
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Constrained Diagrams. -/

section

namespace UniversalTensorSquare
open Saxl

lemma firstBound_sound {n : ℕ} (μ : YoungDiagram) (hc : μ.card = n)
    {B : List (ℕ × ℕ)} (hb : RowBounds μ B) : μ.rowLen 0 ≤ firstBound n B := by
  induction B with
  | nil =>
    have hh := rowPrefix_le_card μ 1
    simpa [firstBound,rowPrefix,hc] using hh
  | cons p B ih =>
    have hp := hb p (by simp)
    simp only [firstBound,List.foldr_cons,ite_eq_left hp.1]
    exact le_min ((rowLen_first_le_prefix μ hp.1).trans hp.2)
      (ih (fun q hq => hb q (by simp [hq])))

lemma clippedSum_rowLens (μ : YoungDiagram) (k : ℕ) :
    clippedSum μ.rowLens k = colPrefix μ k := by
  rw [colPrefix_eq_min_sum]
  rw [YoungDiagram.rowLens]
  simp only [clippedSum,List.map_map,Function.comp_def]
  rw [← List.sum_toFinset _ List.nodup_range, List.toFinset_range]

lemma rowLens_mem_rowsWithin {n : ℕ} (hn : 0 < n) (μ : YoungDiagram)
    (hc : μ.card = n) {A B : List (ℕ × ℕ)}
    (ha : RowBounds μ.transpose A) (hb : RowBounds μ B) :
    μ.rowLens ∈ rowsWithin n A B := by
  apply List.mem_flatMap.mpr
  refine ⟨μ.rowLens.length,?_,?_⟩
  · have hlo := minHeight_sound hn μ hc hb
    have hhi := firstBound_sound μ.transpose ((transpose_card μ).trans hc) ha
    simp only [YoungDiagram.rowLen_transpose] at hhi
    simp only [List.mem_range'_1,YoungDiagram.length_rowLens]
    omega
  · apply mem_constrainedRows _ _ _ _ _ _ rfl
    · exact (card_eq_sum_rowLens μ).symm.trans hc
    · exact μ.pos_of_mem_rowLens
    · intro a ha'
      obtain ⟨i,hi,he⟩ := List.getElem_of_mem ha'
      rw [← he, YoungDiagram.get_rowLens]
      exact (μ.rowLen_anti _ _ (Nat.zero_le _)).trans (firstBound_sound μ hc hb)
    · exact μ.rowLens_sorted
    · intro p hp
      rw [clippedSum_rowLens]
      exact (ha p hp).2
    · intro p hp
      rw [← rowPrefix_eq_take]
      exact (hb p hp).2

lemma rowsWithin_sound {n : ℕ} (hn : 0 < n) (μ : YoungDiagram)
    (hc : μ.card = n) {A B : List (ℕ × ℕ)}
    (ha : RowBounds μ.transpose A) (hb : RowBounds μ B)
    {P : List ℕ → Prop} (h : ∀ rs ∈ rowsWithin n A B, P rs) : P μ.rowLens :=
  h _ (rowLens_mem_rowsWithin hn μ hc ha hb)

end UniversalTensorSquare
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

lemma rowDiagram_transposeRows {rs : List ℕ} (h : GoodRows rs) :
    rowDiagram (transposeRows rs) = (rowDiagram rs).transpose := by
  rw [transposeRows_eq h,rowDiagram_rowLens]

end UniversalTensorSquare

end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Support_FiniteRowSquares
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite Row Squares. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

lemma rowSquare_of_exhaustion {n : ℕ} {p : List ℕ} (hp : GoodRows p)
    (hs : transposeRows p = p) (hn : 0 < n) (keys : List (List ℕ))
    (hkeys : ∀ q ∈ keys, RowSquare p q)
    (hcover : ∀ rs ∈ rowsWithin n [] [], rs ∈ keys ∨ transposeRows rs ∈ keys)
    (μ : YoungDiagram) (hμ : μ.card = n) : SquareOccurs (rowDiagram p) μ := by
  have hc := rowsWithin_sound hn μ hμ (by simp [RowBounds]) (by simp [RowBounds]) hcover
  rcases hc with hc | hc
  · simpa only [RowSquare,rowDiagram_rowLens] using hkeys _ hc
  · have hh := hkeys _ hc
    rw [RowSquare,rowDiagram_transposeRows ⟨μ.rowLens_sorted, μ.pos_of_mem_rowLens⟩,
      rowDiagram_rowLens] at hh
    have he : (rowDiagram p).transpose = rowDiagram p := by
      rw [← rowDiagram_transposeRows hp, hs]
    simpa only [YoungDiagram.transpose_transpose] using hh.target_transpose he

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_NumericalDegree13
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Numerical Degree 13. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma smallCover13 : ∀ rs ∈ rowsWithin 13 [] [],
    rs ∈ smallKeys13 ∨ transposeRows rs ∈ smallKeys13 := by
  decide +kernel

lemma degree_pos13_oai (μ : YoungDiagram) (hμ : μ.card = 13) :
    0 < kronecker (canonicalTableau (rowDiagram [4,4,3,2]) degreeCard13)
      (canonicalTableau (rowDiagram [4,4,3,2]) degreeCard13) (canonicalTableau μ hμ) := by
  exact (rowSquare_of_exhaustion (by decide) (by decide) (by decide)
    smallKeys13 smallSupports13 smallCover13 μ hμ).pos _ _

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degree_pos13_oai := @OAI.UniversalTensorSquare.degree_pos13_oai
