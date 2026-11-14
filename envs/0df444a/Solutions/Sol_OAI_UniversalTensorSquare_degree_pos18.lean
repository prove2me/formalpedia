-- Prove2me | solution 1 for OAI.UniversalTensorSquare.degree_pos18
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T13:05:00.466286+00:00
-- url     : https://prove2.me/submissions/76ec999f-ef82-4aeb-b5f9-81d39f695912
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_UniversalTensorSquares
import Definitions.Def_OAIQ259US004
import Definitions.Def_OAIQ259US021
import Definitions.Def_OAIQ259US022
import Theorems.Thm_OAI_UniversalTensorSquare_band_kronecker_pos
import Theorems.Thm_OAI_UniversalTensorSquare_degreeTreeAll18
import Theorems.Thm_OAI_UniversalTensorSquare_packingPlan_pos
import Theorems.Thm_OAI_UniversalTensorSquare_residualProperty_sound

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
-- module Solutions.OAIQ259_US.Saxl_HighProjection
attribute [-instance] _root_.OAI.Saxl.Columns.cellsDecEq _root_.OAI.Saxl.Columns.cellsFintype _root_.OAI.Saxl.Columns.permsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped TensorProduct

namespace Saxl
/- Translate the high part of each row to the smaller staircase. -/


lemma columnAlt_left {n d : ℕ} {μ : YoungDiagram} (t : Tableau n μ)
    (h : columnGroup t) :
    wordRep n d (h : Equiv.Perm (Fin n)) * columnAlt (d := d) t =
      signC (h : Equiv.Perm (Fin n)) • columnAlt t := by
  classical
  let := Fintype.ofFinite (columnGroup t)
  unfold columnAlt
  simp only [Finset.mul_sum, mul_smul_comm, Finset.smul_sum]
  symm
  apply (Equiv.sum_comp (Equiv.mulLeft h) _).symm.trans
  apply Finset.sum_congr rfl
  intro g hg
  change signC (h : Equiv.Perm (Fin n)) •
    signC ((h * g : columnGroup t) : Equiv.Perm (Fin n)) •
      wordRep n d ((h * g : columnGroup t) : Equiv.Perm (Fin n)) = _
  simp only [Subgroup.coe_mul, map_mul, smul_smul]
  rw [← mul_assoc, signC_mul_self, one_mul]

lemma polytabloid_alternating {n : ℕ} {μ : YoungDiagram} (t : Tableau n μ)
    (h : columnGroup t) : wordRep n (μ.colLen 0) (h : Equiv.Perm (Fin n))
      (polytabloid t) = signC (h : Equiv.Perm (Fin n)) • polytabloid t := by
  rw [← columnAlt_row]
  exact congrArg (fun L : Module.End ℂ (WordSpace n (μ.colLen 0)) =>
    L (Pi.single (rowWord t) 1)) (columnAlt_left t h)

/- Move low row letters to the band and high row letters to B_h. -/

end Saxl

end

end OAI
end

section
-- module Solutions.OAIQ259_US.Saxl_SignEquivalence
attribute [-simp] _root_.OAI.Saxl.Balance.cyclicSquareMap_tmul _root_.OAI.Saxl.orbitTensorEval_tmul _root_.OAI.Saxl.relabelWord_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped TensorProduct

universe uV

namespace Saxl

lemma signTwist_irreducible {n : ℕ} {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (Equiv.Perm (Fin n)) V) [Representation.IsIrreducible ρ] :
    Representation.IsIrreducible (signTwist ρ) := by
  let cv : Subrepresentation (signTwist ρ) ≃o Subrepresentation ρ :=
    { toFun := fun S =>
        { toSubmodule := S.toSubmodule
          apply_mem_toSubmodule := by
            intro g x hx
            have h := S.toSubmodule.smul_mem (signC g) (S.apply_mem_toSubmodule g hx)
            change signC g • (signC g • (ρ g x)) ∈ S.toSubmodule at h
            simpa only [smul_smul, signC_mul_self, one_smul] using h }
      invFun := fun S =>
        { toSubmodule := S.toSubmodule
          apply_mem_toSubmodule := by
            intro g x hx
            exact S.toSubmodule.smul_mem (signC g) (S.apply_mem_toSubmodule g hx) }
      left_inv := by intro S; rfl
      right_inv := by intro S; rfl
      map_rel_iff' := by intros; rfl }
  exact cv.isSimpleOrder_iff.mpr inferInstance

lemma orbitAverage_base {n d : ℕ} {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (Equiv.Perm (Fin n)) V) (a : Fin n → Fin d) (y : V)
    (hy : ∀ g : Equiv.Perm (Fin n), a ∘ g = a → ρ g y = y) :
    orbitAverage ρ a y (Pi.single a 1) =
      ((Finset.univ.filter (fun g : Equiv.Perm (Fin n) => a ∘ g = a)).card : ℂ) • y := by
  classical
  change (∑ g : Equiv.Perm (Fin n), (Pi.single a (1 : ℂ) : WordSpace n d) (a ∘ (g⁻¹ : Equiv.Perm (Fin n))) • ρ g y) = _
  have hi (g : Equiv.Perm (Fin n)) : a ∘ (g⁻¹ : Equiv.Perm (Fin n)) = a ↔ a ∘ g = a := by
    constructor <;> intro hh <;> funext i
    · have he := congrFun hh (g i); simpa using he.symm
    · have he := congrFun hh (g⁻¹ i); simpa using he.symm
  simp only [Pi.single_apply, hi]
  simp only [ite_smul, one_smul, zero_smul, Finset.sum_ite, Finset.sum_const_zero, add_zero]
  rw [Finset.sum_congr rfl (fun g hg => hy g (Finset.mem_filter.mp hg).2)]
  simp [Nat.cast_smul_eq_nsmul]

end Saxl

namespace Saxl
/- Sign-conjugacy proved using the column-antisymmetrized row tabloids. -/
theorem specht_sign_transpose {n : ℕ} {μ : YoungDiagram} (t : Tableau n μ) :
    Nonempty ((spechtRep t).Equiv (signTwist (spechtRep (transposeTableau t)))) := by
  classical
  let tt := transposeTableau t
  let y : Specht tt := ⟨polytabloid tt, mem_cyclic _ _⟩
  let R := signTwist (spechtRep tt)
  let F := orbitAverage R (rowWord t) y
  let c : ℂ := ((Finset.univ.filter
    (fun g : Equiv.Perm (Fin n) => rowWord t ∘ g = rowWord t)).card : ℂ)
  have hy : ∀ g : Equiv.Perm (Fin n), rowWord t ∘ g = rowWord t → R g y = y := by
    intro g hg
    have hc : g ∈ columnGroup tt := by
      intro i
      exact congrArg Fin.val (congrFun hg i)
    apply Subtype.ext
    change signC g • wordRep n (μ.transpose.colLen 0) g (polytabloid tt) = polytabloid tt
    rw [polytabloid_alternating tt ⟨g, hc⟩, smul_smul, signC_mul_self, one_smul]
  have hF : F (Pi.single (rowWord t) 1) = c • y := orbitAverage_base R _ y hy
  have hc0 : c ≠ 0 := by
    apply Nat.cast_ne_zero.mpr
    apply Finset.card_ne_zero.mpr
    refine ⟨1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
    rfl
  have hm (g : columnGroup t) :
      (F (wordRep n (μ.colLen 0) (g : Equiv.Perm (Fin n))
        (Pi.single (rowWord t) 1))).val (rowWord tt) = signC (g : Equiv.Perm (Fin n)) * c := by
    rw [F.isIntertwining, hF]
    change signC (g : Equiv.Perm (Fin n)) * (c *
      polytabloid tt (rowWord tt ∘ (g : Equiv.Perm (Fin n)))) = _
    have he : rowWord tt ∘ (g : Equiv.Perm (Fin n)) = rowWord tt := by
      funext i
      apply Fin.ext
      exact g.property i
    rw [he, polytabloid_rowWord, mul_one]
  let inc : Representation.IntertwiningMap (spechtRep t) (wordRep n (μ.colLen 0)) :=
    { toLinearMap := (spechtSub t).toSubmodule.subtype
      isIntertwining' := fun _ => rfl }
  let f := F.comp inc
  have hf : f ≠ 0 := by
    intro hz
    have he : (F (polytabloid t)).val (rowWord tt) = 0 := by
      have he := congrArg (fun l : Representation.IntertwiningMap (spechtRep t) R =>
        (l ⟨polytabloid t, mem_cyclic _ _⟩).val (rowWord tt)) hz
      exact he
    let := Fintype.ofFinite (columnGroup t)
    have hp : (F (polytabloid t)).val (rowWord tt) =
        (Fintype.card (columnGroup t) : ℂ) * c := by
      change (F (∑ g : columnGroup t, signC (g : Equiv.Perm (Fin n)) •
        wordRep n (μ.colLen 0) (g : Equiv.Perm (Fin n)) (Pi.single (rowWord t) 1))).val _ = _
      simp only [map_sum, map_smul, Submodule.coe_sum, Submodule.coe_smul,
        Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hm]
      simp only [← mul_assoc, signC_mul_self, one_mul, Finset.sum_const,
        Finset.card_univ, nsmul_eq_mul]
    have hn : (Fintype.card (columnGroup t) : ℂ) ≠ 0 := by
      exact Nat.cast_ne_zero.mpr Fintype.card_ne_zero
    exact (mul_ne_zero hn hc0) (hp.symm.trans he)
  let := specht_irreducible t
  let := specht_irreducible tt
  let := signTwist_irreducible (spechtRep tt)
  exact ⟨f.ofBijective ((Representation.IsIrreducible.bijective_or_eq_zero f).resolve_right hf)⟩
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

lemma colPrefix_eq_sum (μ : YoungDiagram) (i : ℕ) :
    colPrefix μ i = ∑ k ∈ Finset.range i, μ.colLen k := by
  simp only [colPrefix, rowPrefix, YoungDiagram.rowLen_transpose]

lemma mem_colTruncate (μ : YoungDiagram) (i : ℕ) (a b : ℕ) :
    (a,b) ∈ colTruncate μ i ↔ (a,b) ∈ μ ∧ b < i := by
  simp only [colTruncate, YoungDiagram.mem_transpose, Prod.swap_prod_mk,
    Saxl.mem_rowTruncate]

lemma rowTruncate_subset (μ : YoungDiagram) (j : ℕ) :
    (rowTruncate μ j).cells ⊆ μ.cells := by
  intro p hp
  exact (Saxl.mem_rowTruncate.mp hp).1

lemma colTruncate_subset (μ : YoungDiagram) (i : ℕ) :
    (colTruncate μ i).cells ⊆ μ.cells := by
  rintro ⟨a,b⟩ hp
  exact ((mem_colTruncate μ i a b).mp hp).1

lemma colTruncate_card (μ : YoungDiagram) (i : ℕ) :
    (colTruncate μ i).card = colPrefix μ i := by
  rw [colTruncate, Saxl.transpose_card, rowTruncate_card, colPrefix]

lemma strip_area_identity (μ : YoungDiagram) (i j : ℕ) :
    μ.card + ((rowTruncate μ j).cells ∩ (colTruncate μ i).cells).card =
      rowPrefix μ j + colPrefix μ i +
        (μ.cells \ ((rowTruncate μ j).cells ∪ (colTruncate μ i).cells)).card := by
  have hu : (rowTruncate μ j).cells ∪ (colTruncate μ i).cells ⊆ μ.cells :=
    Finset.union_subset (rowTruncate_subset μ j) (colTruncate_subset μ i)
  have h₁ := Finset.card_sdiff_add_card_eq_card hu
  have h₂ := Finset.card_union_add_card_inter
    (rowTruncate μ j).cells (colTruncate μ i).cells
  have h₃ := rowTruncate_card μ j
  have h₄ := colTruncate_card μ i
  change (rowTruncate μ j).cells.card = _ at h₃
  change (colTruncate μ i).cells.card = _ at h₄
  change μ.cells.card + _ = _
  omega

lemma corner_subset_rectangle (μ : YoungDiagram) {i j : ℕ} (hi : 0 < i) (hj : 0 < j) :
    μ.cells \ ((rowTruncate μ j).cells ∪ (colTruncate μ i).cells) ⊆
      Finset.Ico j (μ.colLen (i-1)) ×ˢ Finset.Ico i (μ.rowLen (j-1)) := by
  rintro ⟨a,b⟩ hp
  simp only [Finset.mem_sdiff, Finset.mem_union, YoungDiagram.mem_cells,
    mem_rowTruncate, mem_colTruncate, not_or] at hp
  have ha : j ≤ a := Nat.le_of_not_gt fun ha => hp.2.1 ⟨hp.1, ha⟩
  have hb : i ≤ b := Nat.le_of_not_gt fun hb => hp.2.2 ⟨hp.1, hb⟩
  have ha' : a < μ.colLen (i-1) := YoungDiagram.mem_iff_lt_colLen.mp
    (μ.up_left_mem le_rfl (by omega) hp.1)
  have hb' : b < μ.rowLen (j-1) := YoungDiagram.mem_iff_lt_rowLen.mp
    (μ.up_left_mem (by omega) le_rfl hp.1)
  simpa only [Finset.mem_product, Finset.mem_Ico] using And.intro ⟨ha, ha'⟩ ⟨hb,hb'⟩

lemma prefix_last_mul_le (μ : YoungDiagram) {j : ℕ} (hj : 0 < j) :
    j * μ.rowLen (j-1) ≤ rowPrefix μ j := by
  have h := Finset.sum_le_sum (s := Finset.range j) (f := fun _ => μ.rowLen (j-1))
    (g := fun a => μ.rowLen a) (by
      intro a ha
      exact μ.rowLen_anti a (j-1) (by have := Finset.mem_range.mp ha; omega))
  simpa only [Finset.sum_const, Finset.card_range, smul_eq_mul, rowPrefix] using h

lemma capacity_floor_bound (x f : ℕ) : x ≤ 2*((x-f)/2)+f+1 := by omega

lemma prefix_le_capacity (μ : YoungDiagram) (d q : ℕ) :
    colPrefix μ q ≤ 2*bandCapacity μ d q + q*(d+1) := by
  rw [colPrefix_eq_sum, bandCapacity]
  have h := Finset.sum_le_sum (s := Finset.range q)
    (fun k _ => capacity_floor_bound (μ.colLen k) d)
  simpa only [Finset.sum_add_distrib, ← Finset.mul_sum,
    Finset.sum_const, Finset.card_range, smul_eq_mul, Nat.mul_add, Nat.mul_one,
    Nat.add_assoc] using h

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

lemma canonical_sign_transpose {n : ℕ} (μ : YoungDiagram) (hμ : μ.card = n) :
    Nonempty ((Saxl.spechtRep (Saxl.canonicalTableau μ hμ)).Equiv
      (Saxl.signTwist (Saxl.spechtRep
        (Saxl.canonicalTableau μ.transpose ((Saxl.transpose_card μ).trans hμ))))) := by
  obtain ⟨e⟩ := Saxl.specht_sign_transpose (Saxl.canonicalTableau μ hμ)
  let e' := Saxl.equivOfSubrepEq
    (Saxl.spechtSub (Saxl.transposeTableau (Saxl.canonicalTableau μ hμ)))
    (Saxl.spechtSub
      (Saxl.canonicalTableau μ.transpose ((Saxl.transpose_card μ).trans hμ)))
    (Saxl.spechtSub_tableau_independent _ _)
  exact ⟨e.trans (signTwistEquiv e')⟩

lemma canonical_self_sign {n : ℕ} (lam : YoungDiagram) (hlam : lam.card = n)
    (hself : lam.transpose = lam) :
    Nonempty ((Saxl.spechtRep (Saxl.canonicalTableau lam hlam)).Equiv
      (Saxl.signTwist (Saxl.spechtRep (Saxl.canonicalTableau lam hlam)))) := by
  obtain ⟨e⟩ := canonical_sign_transpose lam hlam
  let e' := spechtShapeEquiv hself
    (Saxl.canonicalTableau lam.transpose ((Saxl.transpose_card lam).trans hlam))
    (Saxl.canonicalTableau lam hlam)
  exact ⟨e.trans (signTwistEquiv e')⟩

lemma tensorAnti_injective {n : ℕ} {X Y Z : Type*}
    [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]
    [AddCommGroup Z] [Module ℂ Z]
    (ρ : Representation ℂ (Equiv.Perm (Fin n)) X)
    {σ : Representation ℂ (Equiv.Perm (Fin n)) Y}
    {τ : Representation ℂ (Equiv.Perm (Fin n)) Z}
    (e : σ.Equiv (Saxl.signTwist τ)) :
    Function.Injective (Saxl.tensorAnti ρ e.toIntertwiningMap) :=
  (TensorProduct.congr (LinearEquiv.refl ℂ X) e.toLinearEquiv).injective

lemma kronecker_pos_transpose {n : ℕ} (lam : YoungDiagram) (hlam : lam.card = n)
    (hself : lam.transpose = lam) (ν : YoungDiagram) (hν : ν.card = n)
    (hpos : 0 < Saxl.kronecker (Saxl.canonicalTableau lam hlam)
      (Saxl.canonicalTableau lam hlam) (Saxl.canonicalTableau ν hν)) :
    0 < Saxl.kronecker (Saxl.canonicalTableau lam hlam)
      (Saxl.canonicalTableau lam hlam)
      (Saxl.canonicalTableau ν.transpose ((Saxl.transpose_card ν).trans hν)) := by
  obtain ⟨eL⟩ := canonical_self_sign lam hlam hself
  obtain ⟨eν⟩ := canonical_sign_transpose ν hν
  obtain ⟨f, hf⟩ := (Saxl.kronecker_pos_iff _ _ _).mp hpos
  let A := Saxl.tensorAnti (Saxl.spechtRep (Saxl.canonicalTableau lam hlam))
    eL.toIntertwiningMap
  let B := (Saxl.signTwistMap
    (Y := Saxl.Specht (Saxl.canonicalTableau lam hlam) ⊗[ℂ]
      Saxl.Specht (Saxl.canonicalTableau lam hlam)) f).comp (Saxl.signCancelMap eν.symm.toIntertwiningMap)
  apply (Saxl.kronecker_pos_iff _ _ _).mpr
  refine ⟨A.comp B, ?_⟩
  intro hz
  apply hf
  ext x
  have h := congrArg (fun F => F (eν x)) hz
  have hi : Function.Injective A := tensorAnti_injective _ eL
  apply hi
  change A (f x) = A 0
  change A (f (eν.symm (eν x))) = 0 at h
  simpa only [eν.symm_apply_apply, map_zero] using h

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
-- module Solutions.OAIQ259_US.UniversalSquare_Capacity_Intermediate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Intermediate. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl

lemma first_prefix_height (μ : YoungDiagram) {K : ℕ} (hK : 0 < K)
    (h : K ≤ rowPrefix μ 4) :
    ∃ d, 1 ≤ d ∧ d ≤ 4 ∧ K ≤ rowPrefix μ d ∧
      (1 < d → rowPrefix μ (d-1) < K) := by
  let h' : ∃ d, K ≤ rowPrefix μ d := ⟨4,h⟩
  refine ⟨Nat.find h', ?_, Nat.find_min' h' h, Nat.find_spec h', ?_⟩
  · have hx := Nat.find_spec h'
    by_contra hh
    have hd : Nat.find h' = 0 := by omega
    change K ≤ rowPrefix μ (Nat.find h') at hx
    rw [hd] at hx
    simp only [rowPrefix, Finset.range_zero, Finset.sum_empty] at hx
    omega
  · intro hd
    exact Nat.lt_of_not_ge (Nat.find_min h' (by omega))

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Capacity_RefinedCapacity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Refined Capacity. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl

lemma prefix_last_after_first (μ : YoungDiagram) {j : ℕ} (hj : 0 < j) :
    μ.rowLen 0 + (j-1)*μ.rowLen (j-1) ≤ rowPrefix μ j := by
  have he : j = (j-1)+1 := by omega
  unfold rowPrefix
  conv_rhs => rw [he, Finset.sum_range_succ']
  have hh := Finset.sum_le_sum (s := Finset.range (j-1))
    (f := fun _ => μ.rowLen (j-1)) (g := fun a => μ.rowLen (a+1)) (by
      intro a ha
      exact μ.rowLen_anti _ _ (by have := Finset.mem_range.mp ha; omega))
  simp only [Finset.sum_const, Finset.card_range, smul_eq_mul] at hh
  omega

lemma endpointBound_sound (μ : YoungDiagram) {i U H : ℕ} (hi : 0 < i)
    (hU : rowPrefix μ i ≤ U) (hH : H ≤ μ.rowLen 0) :
    μ.rowLen (i-1) ≤ endpointBound i U H := by
  unfold endpointBound
  split_ifs with he
  · subst i
    simpa [rowPrefix] using hU
  · apply le_min
    · apply (Nat.le_div_iff_mul_le hi).mpr
      simpa [Nat.mul_comm] using (prefix_last_mul_le μ hi).trans hU
    · apply (Nat.le_div_iff_mul_le (by omega : 0 < i-1)).mpr
      have h := prefix_last_after_first μ hi
      have hx : (i-1)*μ.rowLen (i-1) ≤ U-H := by omega
      simpa [Nat.mul_comm] using hx

lemma prefix_intersection_hook (μ : YoungDiagram) {i j H W : ℕ}
    (hi : 0 < i) (hj : 0 < j) (hH : H ≤ μ.colLen 0) (hW : W ≤ μ.rowLen 0)
    (hHp : 0 < H) (hWp : 0 < W) :
    min i W + min j H - 1 ≤
      ((rowTruncate μ j).cells ∩ (colTruncate μ i).cells).card := by
  let A := (rectangle 1 (min i W)).cells
  let B := (rectangle (min j H) 1).cells
  have hA : A ⊆ (rowTruncate μ j).cells ∩ (colTruncate μ i).cells := by
    rintro ⟨a,b⟩ hp
    have hx : a < 1 ∧ b < min i W := mem_rectangle.mp hp
    have ha : a = 0 := by omega
    subst a
    have hc : (0,b) ∈ μ := YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)
    simpa only [Finset.mem_inter,YoungDiagram.mem_cells,mem_rowTruncate,mem_colTruncate]
      using And.intro ⟨hc,hj⟩ ⟨hc,lt_of_lt_of_le hx.2 (min_le_left _ _)⟩
  have hB : B ⊆ (rowTruncate μ j).cells ∩ (colTruncate μ i).cells := by
    rintro ⟨a,b⟩ hp
    have hx : a < min j H ∧ b < 1 := mem_rectangle.mp hp
    have hb : b = 0 := by omega
    subst b
    have hc : (a,0) ∈ μ := YoungDiagram.mem_iff_lt_colLen.mpr (by omega)
    simpa only [Finset.mem_inter,YoungDiagram.mem_cells,mem_rowTruncate,mem_colTruncate]
      using And.intro ⟨hc,lt_of_lt_of_le hx.1 (min_le_left _ _)⟩ ⟨hc,hi⟩
  have hAB : A ∩ B = {(0,0)} := by
    ext ⟨a,b⟩
    simp only [Finset.mem_inter,Finset.mem_singleton,Prod.mk.injEq]
    simp only [A,B,rectangle,Finset.mem_product,Finset.mem_range]
    omega
  have he := Finset.card_union_add_card_inter A B
  have ha : A.card = min i W := by simp [A,rectangle]
  have hb : B.card = min j H := by simp [B,rectangle]
  rw [hAB,Finset.card_singleton,ha,hb] at he
  have h := Finset.card_le_card (Finset.union_subset hA hB)
  omega

lemma area_le_refined (μ : YoungDiagram) {i j U V X Y H W : ℕ}
    (hi : 0 < i) (hj : 0 < j) (hU : colPrefix μ i ≤ U) (hV : rowPrefix μ j ≤ V)
    (hX : μ.colLen (i-1) ≤ X) (hY : μ.rowLen (j-1) ≤ Y)
    (hH : H ≤ μ.colLen 0) (hW : W ≤ μ.rowLen 0) (hHp : 0 < H) (hWp : 0 < W) :
    μ.card ≤ refinedArea i j U V X Y H W := by
  classical
  have hid := strip_area_identity μ i j
  have hh := prefix_intersection_hook μ hi hj hH hW hHp hWp
  by_cases hcell : (j-1,i-1) ∈ μ
  · have heq : (rowTruncate μ j).cells ∩ (colTruncate μ i).cells =
        (rectangle j i).cells := by
      ext ⟨a,b⟩
      simp only [Finset.mem_inter, YoungDiagram.mem_cells, mem_rowTruncate,
        mem_colTruncate, mem_rectangle]
      constructor
      · tauto
      · rintro ⟨ha,hb⟩
        have hx := μ.up_left_mem (by omega : a ≤ j-1) (by omega : b ≤ i-1) hcell
        tauto
    have hint : ((rowTruncate μ j).cells ∩ (colTruncate μ i).cells).card = j*i := by
      rw [heq]
      simp only [rectangle,Finset.card_product,Finset.card_range]
    have hcor := Finset.card_le_card (corner_subset_rectangle μ hi hj)
    simp only [Finset.card_product,Nat.card_Ico] at hcor
    have hmul := Nat.mul_le_mul (Nat.sub_le_sub_right hX j) (Nat.sub_le_sub_right hY i)
    have hx : j ≤ μ.colLen (i-1) := by
      have := YoungDiagram.mem_iff_lt_colLen.mp hcell; omega
    have hy : i ≤ μ.rowLen (j-1) := by
      have := YoungDiagram.mem_iff_lt_rowLen.mp hcell; omega
    rw [hint] at hid
    have hup : i*j ≤ U+V := by
      have ht := prefix_last_mul_le μ.transpose hi
      simp only [YoungDiagram.rowLen_transpose] at ht
      change i * μ.colLen (i-1) ≤ colPrefix μ i at ht
      nlinarith
    have hsub := Nat.sub_add_cancel hup
    have ha : μ.card ≤ U+V-i*j+(X-j)*(Y-i) := by
      rw [Nat.mul_comm j i] at hid
      omega
    unfold refinedArea
    rw [ite_eq_left ⟨hx.trans hX,hy.trans hY⟩]
    exact ha.trans (le_max_right _ _)
  · have hz : μ.cells \ ((rowTruncate μ j).cells ∪ (colTruncate μ i).cells) = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      rintro ⟨a,b⟩ hp
      simp only [Finset.mem_sdiff,Finset.mem_union,YoungDiagram.mem_cells,
        mem_rowTruncate,mem_colTruncate,not_or] at hp
      have ha : j ≤ a := Nat.le_of_not_gt fun ha => hp.2.1 ⟨hp.1,ha⟩
      have hb : i ≤ b := Nat.le_of_not_gt fun hb => hp.2.2 ⟨hp.1,hb⟩
      exact hcell (μ.up_left_mem (by omega) (by omega) hp.1)
    rw [hz,Finset.card_empty,add_zero] at hid
    have ha : μ.card ≤ U+V-(min i W+min j H-1) := by omega
    unfold refinedArea
    split_ifs
    · exact ha.trans (le_max_left _ _)
    · exact ha

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

lemma minHeight_pos (n : ℕ) (B : List (ℕ × ℕ)) : 0 < minHeight n B := by
  induction B with
  | nil => simp [minHeight]
  | cons p B ih =>
    simp only [minHeight,List.foldr_cons]
    split_ifs
    · exact lt_of_lt_of_le ih (le_max_right _ _)
    · exact ih

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

lemma impossibleBounds_false {n : ℕ} (hn : 0 < n) (μ : YoungDiagram)
    (hcard : μ.card = n) {A B : List (ℕ × ℕ)}
    (ha : RowBounds μ.transpose A) (hb : RowBounds μ B)
    (h : impossibleBounds n A B) : False := by
  have hH := minHeight_sound hn μ hcard hb
  have hW := minHeight_sound hn μ.transpose ((transpose_card _).trans hcard) ha
  simp only [YoungDiagram.colLen_transpose] at hW
  rcases h with ⟨p,hp,h⟩ | ⟨q,hq,h⟩ | ⟨p,hp,q,hq,h⟩
  · have hs := (rowLen_first_le_prefix μ.transpose (ha p hp).1).trans (ha p hp).2
    simp only [YoungDiagram.rowLen_transpose] at hs
    omega
  · have hs := (rowLen_first_le_prefix μ (hb q hq).1).trans (hb q hq).2
    omega
  · have hX := endpointBound_sound μ.transpose (ha p hp).1 (ha p hp).2
      (show minHeight n B ≤ μ.transpose.rowLen 0 by simpa using hH)
    have hY := endpointBound_sound μ (hb q hq).1 (hb q hq).2 hW
    have ht := area_le_refined μ (ha p hp).1 (hb q hq).1 (ha p hp).2
      (hb q hq).2 (by simpa using hX) hY hH hW (minHeight_pos n B) (minHeight_pos n A)
    omega

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

lemma not_dominates_witness {μ θ : YoungDiagram} (hc : μ.card = θ.card)
    (h : ¬ Dominates μ θ) :
    ∃ k, 1 ≤ k ∧ k ≤ θ.colLen 0 ∧ rowPrefix μ k < rowPrefix θ k := by
  classical
  obtain ⟨k,hk⟩ := not_forall.mp h
  have hk' : rowPrefix μ k < rowPrefix θ k := Nat.lt_of_not_ge hk
  by_cases hb : k ≤ θ.colLen 0
  · refine ⟨k,?_,hb,hk'⟩
    by_contra ht
    have hz : k = 0 := by omega
    simp [hz,rowPrefix] at hk'
  · refine ⟨θ.colLen 0,?_,le_rfl,?_⟩
    · by_contra ht
      have hz : θ.colLen 0 = 0 := by omega
      have hs := rowPrefix_eq_card θ (le_of_eq hz)
      simp only [rowPrefix,Finset.range_zero,Finset.sum_empty] at hs
      have hu := rowPrefix_le_card θ k
      omega
    · have hle := rowPrefix_mono μ (show θ.colLen 0 ≤ k by omega)
      rw [rowPrefix_eq_card θ (by omega), ← hc] at hk'
      rw [rowPrefix_eq_card θ le_rfl, ← hc]
      omega

lemma coreImpossible_false (μ : YoungDiagram) {K d : ℕ}
    (hd : K ≤ rowPrefix μ d) {A : List (ℕ × ℕ)} (ha : RowBounds μ A)
    (h : coreImpossible K d A) : False := by
  obtain ⟨p,hp,hpd,hpK⟩ := h
  have hle := (hd.trans (rowPrefix_mono μ hpd)).trans (ha p hp).2
  omega

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

lemma columnShape_perm {rs ss : List ℕ} (h : rs.Perm ss) :
    columnShape rs = columnShape ss := by
  apply YoungDiagram.ext
  ext ⟨i,j⟩
  simp only [YoungDiagram.mem_cells,YoungDiagram.mem_iff_lt_rowLen]
  rw [columnShape_rowLen,columnShape_rowLen,h.countP_eq]

lemma columnShape_diagram (μ : YoungDiagram) :
    columnShape μ.transpose.rowLens = μ := by
  obtain ⟨e,hr,_⟩ := columnShape_placement μ.transpose.rowLens
  apply YoungDiagram.ext
  ext ⟨i,j⟩
  simp only [YoungDiagram.mem_cells,YoungDiagram.mem_iff_lt_rowLen]
  obtain ⟨f,hf,_⟩ := place_columns μ (List.Perm.refl _)
  rw [placed_rowLen e hr,placed_rowLen f hf]

lemma columnShape_sorted (rs : List ℕ) (hs : rs.SortedGE) (hp : ∀ a ∈ rs, 0 < a) :
    columnShape rs = (YoungDiagram.ofRowLens rs hs).transpose := by
  conv_lhs => rw [← YoungDiagram.rowLens_ofRowLens_eq_self hp (hw := hs)]
  simpa only [YoungDiagram.transpose_transpose] using
    columnShape_diagram ((YoungDiagram.ofRowLens rs hs).transpose)

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

lemma rowDiagram_eq (rs : List ℕ) (h : GoodRows rs) :
    rowDiagram rs = YoungDiagram.ofRowLens rs h.1 := by
  rw [rowDiagram,columnShape_sorted rs h.1 h.2,YoungDiagram.transpose_transpose]

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
-- module Solutions.OAIQ259_US.UniversalSquare_Specht_CandidateColumns
attribute [-simp] _root_.OAI.UniversalTensorSquare.candidateRowShuffle_row _root_.OAI.UniversalTensorSquare.candidateSeparatedRow_row
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Candidate Columns. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance

lemma candidate_rowLens {M b δ : ℕ} (hM : 4 ≤ M) :
    (candidate M b δ).rowLens = [M+b+δ,M-1+b] ++
      (List.range' 3 (M-4)).reverse ++ List.replicate (b+1) 2 ++ List.replicate (1+δ) 1 := by
  have hh : (candidate M b δ).colLen 0 = M+b+δ := by
    rw [candidate_colLen _ _ _ _ hM]
    simp [candidateLengths]
  apply List.ext_getElem
  · simp only [YoungDiagram.length_rowLens,hh,List.length_append,List.length_cons,
      List.length_nil,List.length_reverse,List.length_range',List.length_replicate]
    omega
  · intro i hi hj
    rw [YoungDiagram.get_rowLens,candidate_rowLen _ _ _ _ hM]
    by_cases hi0 : i = 0
    · subst i
      simp [candidateLengths]
    by_cases hi1 : i = 1
    · subst i
      simp [candidateLengths]
    have hi2 : 2 ≤ i := by omega
    have hlen : i < M+b+δ := by simpa only [YoungDiagram.length_rowLens,hh] using hi
    simp only [List.append_assoc]
    rw [List.getElem_append_right (by simp; omega)]
    simp only [List.length_cons,List.length_nil, Nat.zero_add]
    simp only [candidateLengths,ite_eq_right hi0,ite_eq_right hi1]
    by_cases him : i < M-2
    · rw [ite_eq_left him,List.getElem_append_left (by simp; omega),List.getElem_reverse,
        List.getElem_range']
      simp only [List.length_range',Nat.one_mul]
      omega
    · rw [ite_eq_right him,List.getElem_append_right (by simp; omega)]
      simp only [List.length_reverse,List.length_range']
      by_cases hib : i < M-1+b
      · rw [ite_eq_left hib,List.getElem_append_left (by simp; omega),List.getElem_replicate]
      · rw [ite_eq_right hib,ite_eq_left hlen,List.getElem_append_right (by simp; omega),
          List.getElem_replicate]

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

end UniversalTensorSquare
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Capacity_SentinelExhaustion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Sentinel Exhaustion. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

lemma testWidth_valid_pos {M f : ℕ} (hf : 1 ≤ f) (hw : 0 < testWidth M f) :
    testWidth M f ≤ 8 ∧ f * testWidth M f + 7 + f ≤ 2*M-1 := by
  refine ⟨min_le_left _ _, ?_⟩
  have hh := Nat.mul_le_mul_left f (min_le_right 8 ((2*M-8-f)/f))
  have hh' := Nat.div_mul_le_self (2*M-8-f) f
  have hq : 0 < (2*M-8-f)/f := lt_of_lt_of_le hw (min_le_right _ _)
  have hn : f ≤ 2*M-8-f := by simpa using (Nat.le_div_iff_mul_le (by omega)).mp hq
  unfold testWidth
  nlinarith [Nat.sub_add_cancel (show f ≤ 2*M-8 by omega),
    Nat.sub_add_cancel (show 8 ≤ 2*M by omega),
    Nat.sub_add_cancel (show 1 ≤ 2*M by omega)]

lemma sentinel_height (μ : YoungDiagram) {K : ℕ} (hK : 0 < K) :
    ∃ d, 1 ≤ d ∧ d ≤ 5 ∧ (d ≤ 4 → K ≤ rowPrefix μ d) ∧
      (1 < d → rowPrefix μ (d-1) < K) := by
  by_cases hh : K ≤ rowPrefix μ 4
  · obtain ⟨d,hd,h4,hp,hl⟩ := first_prefix_height μ hK hh
    exact ⟨d,hd,by omega,fun _ => hp,hl⟩
  · exact ⟨5,by decide,le_rfl,by omega,by simpa using Nat.lt_of_not_ge hh⟩

lemma prefixBounds_sound_sentinel (μ : YoungDiagram) {M r d e : ℕ}
    (hM : 1 ≤ M) (hr : 0 < r)
    (hd : 1 < d → colPrefix μ (d-1) < 2*M-1)
    (he : e ≤ 4 → 2*M-1 ≤ rowPrefix μ e) (hfail : ¬BandTest M r μ) :
    ∀ p ∈ prefixBounds M r d e, 0 < p.1 ∧ colPrefix μ p.1 ≤ p.2 := by
  intro p hp
  simp only [prefixBounds,List.mem_append] at hp
  rcases hp with hp | hp
  · split_ifs at hp with hd'
    · simp only [List.mem_cons,List.not_mem_nil,or_false] at hp
      subst p
      exact ⟨by omega,by have := hd hd'; dsimp; omega⟩
    · simp at hp
  · obtain ⟨k,hk,hkp⟩ := List.mem_filterMap.mp hp
    simp only [List.mem_range] at hk
    split_ifs at hkp with hke
    · have hp' := Option.some.inj hkp
      subst p
      have hw := testWidth_valid_pos (by omega : 1 ≤ k+1) hke.2
      have hc : bandCapacity μ (k+1) (testWidth M (k+1)) < r := by
        by_contra hh
        apply hfail
        exact ⟨k+1,by omega,by omega,testWidth M (k+1),hw.1,
          (he (by omega)).trans (rowPrefix_mono μ hke.1),hw.2,by omega⟩
      have hb := prefix_le_capacity μ (k+1) (testWidth M (k+1))
      exact ⟨hke.2,by dsimp; omega⟩

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

lemma transposeRows_eq {rs : List ℕ} (h : GoodRows rs) :
    transposeRows rs = (rowDiagram rs).transpose.rowLens := by
  conv_lhs => rw [← rowDiagram_rows h,transposeRows_rowLens]

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

theorem semantic_capacity_dichotomy (μ θ : YoungDiagram) {n M r : ℕ}
    (hn : 0 < n) (hM : 1 ≤ M) (hr : 0 < r) (hc : μ.card = n) (ht : θ.card = n)
    (P : List ℕ → Prop)
    (check : ∀ d ∈ List.range 5, ∀ e ∈ List.range 5,
      ∀ a ∈ List.range θ.rowLens.length, ∀ b ∈ List.range θ.rowLens.length,
        semanticResidualCheck n M r (d+1) (e+1) (a+1) (b+1) θ.rowLens P) :
    BandTest M r μ ∨ BandTest M r μ.transpose ∨ Dominates μ θ ∨
      Dominates μ.transpose θ ∨ P μ.rowLens := by
  classical
  by_contra hh
  push Not at hh
  rcases hh with ⟨hband,hband',hdom,hdom',hP⟩
  obtain ⟨d,hd,hd',hHd,hHd'⟩ := sentinel_height μ.transpose (show 0 < 2*M-1 by omega)
  obtain ⟨e,he,he',hWe,hWe'⟩ := sentinel_height μ (show 0 < 2*M-1 by omega)
  obtain ⟨a,ha,ha',hA⟩ := not_dominates_witness ((transpose_card _).trans hc |>.trans ht.symm) hdom'
  obtain ⟨b,hb,hb',hB⟩ := not_dominates_witness (hc.trans ht.symm) hdom
  have hAf := prefixBounds_sound_sentinel μ hM hr hHd' hWe hband
  have hBf := prefixBounds_sound_sentinel μ.transpose hM hr
    (by simpa only [colPrefix,YoungDiagram.transpose_transpose] using hWe') hHd hband'
  let A := prefixBounds M r d e ++ [(a,(θ.rowLens.take a).sum-1)]
  let B := prefixBounds M r e d ++ [(b,(θ.rowLens.take b).sum-1)]
  have hAbb : RowBounds μ.transpose A := by
    intro p hp
    rcases List.mem_append.mp hp with hp | hp
    · exact hAf p hp
    · have heq : p = (a,(θ.rowLens.take a).sum-1) := by simpa using hp
      subst p
      rw [rowPrefix_eq_take θ] at hA
      exact ⟨ha,by dsimp; omega⟩
  have hBbb : RowBounds μ B := by
    intro p hp
    rcases List.mem_append.mp hp with hp | hp
    · simpa only [colPrefix,YoungDiagram.transpose_transpose] using hBf p hp
    · have heq : p = (b,(θ.rowLens.take b).sum-1) := by simpa using hp
      subst p
      rw [rowPrefix_eq_take θ] at hB
      exact ⟨hb,by dsimp; omega⟩
  have h := check (d-1) (by simp; omega) (e-1) (by simp; omega)
    (a-1) (by simp only [List.mem_range,YoungDiagram.length_rowLens]; omega)
    (b-1) (by simp only [List.mem_range,YoungDiagram.length_rowLens]; omega)
  have hde : d-1+1 = d := by omega
  have hee : e-1+1 = e := by omega
  have hae : a-1+1 = a := by omega
  have hbe : b-1+1 = b := by omega
  rw [hde,hee,hae,hbe] at h
  rcases h with ⟨h4,h⟩ | ⟨h4,h⟩ | h | h
  · exact coreImpossible_false μ.transpose (hHd h4) hAbb h
  · exact coreImpossible_false μ (hWe h4) hBbb h
  · exact impossibleBounds_false hn μ hc hAbb hBbb h
  · exact hP (h μ hc hAbb hBbb)

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

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_DegreePlans18
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Degree Plans 18. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

lemma degreeCones18 : ∀ q ∈ degreeQs18, ∀ μ : YoungDiagram, μ.card = 18 →
    RowsDom μ.rowLens q → SquareOccurs (candidate 4 2 0) μ := by
  intro q hq
  simp only [degreeQs18,List.not_mem_nil] at hq

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_DegreeCover18
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Degree Cover 18. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

lemma degreeCover18_0_0 :
    ∀ a ∈ List.range degreeRows18_0.length, ∀ c ∈ List.range degreeRows18_0.length,
      regionCheck 18 4 4 1 1 (a+1) (c+1) degreeRows18_0 degreeRegions18 := by
  decide +kernel

lemma degreeCover18_0_1 :
    ∀ a ∈ List.range degreeRows18_0.length, ∀ c ∈ List.range degreeRows18_0.length,
      regionCheck 18 4 4 1 2 (a+1) (c+1) degreeRows18_0 degreeRegions18 := by
  decide +kernel

lemma degreeCover18_0_2 :
    ∀ a ∈ List.range degreeRows18_0.length, ∀ c ∈ List.range degreeRows18_0.length,
      regionCheck 18 4 4 1 3 (a+1) (c+1) degreeRows18_0 degreeRegions18 := by
  decide +kernel

lemma degreeCover18_0_3 :
    ∀ a ∈ List.range degreeRows18_0.length, ∀ c ∈ List.range degreeRows18_0.length,
      regionCheck 18 4 4 1 4 (a+1) (c+1) degreeRows18_0 degreeRegions18 := by
  decide +kernel

lemma degreeCover18_0_4 :
    ∀ a ∈ List.range degreeRows18_0.length, ∀ c ∈ List.range degreeRows18_0.length,
      regionCheck 18 4 4 1 5 (a+1) (c+1) degreeRows18_0 degreeRegions18 := by
  decide +kernel

lemma degreeCover18_1_0 :
    ∀ a ∈ List.range degreeRows18_0.length, ∀ c ∈ List.range degreeRows18_0.length,
      regionCheck 18 4 4 2 1 (a+1) (c+1) degreeRows18_0 degreeRegions18 := by
  decide +kernel

lemma degreeCover18_1_1 :
    ∀ a ∈ List.range degreeRows18_0.length, ∀ c ∈ List.range degreeRows18_0.length,
      regionCheck 18 4 4 2 2 (a+1) (c+1) degreeRows18_0 degreeRegions18 := by
  decide +kernel

lemma degreeCover18_1_2 :
    ∀ a ∈ List.range degreeRows18_0.length, ∀ c ∈ List.range degreeRows18_0.length,
      regionCheck 18 4 4 2 3 (a+1) (c+1) degreeRows18_0 degreeRegions18 := by
  decide +kernel

lemma degreeCover18_1_3 :
    ∀ a ∈ List.range degreeRows18_0.length, ∀ c ∈ List.range degreeRows18_0.length,
      regionCheck 18 4 4 2 4 (a+1) (c+1) degreeRows18_0 degreeRegions18 := by
  decide +kernel

lemma degreeCover18_1_4 :
    ∀ a ∈ List.range degreeRows18_0.length, ∀ c ∈ List.range degreeRows18_0.length,
      regionCheck 18 4 4 2 5 (a+1) (c+1) degreeRows18_0 degreeRegions18 := by
  decide +kernel

lemma degreeCover18_2_0 :
    ∀ a ∈ List.range degreeRows18_0.length, ∀ c ∈ List.range degreeRows18_0.length,
      regionCheck 18 4 4 3 1 (a+1) (c+1) degreeRows18_0 degreeRegions18 := by
  decide +kernel

lemma degreeCover18_2_1 :
    ∀ a ∈ List.range degreeRows18_0.length, ∀ c ∈ List.range degreeRows18_0.length,
      regionCheck 18 4 4 3 2 (a+1) (c+1) degreeRows18_0 degreeRegions18 := by
  decide +kernel

lemma degreeCover18_2_2 :
    ∀ a ∈ List.range degreeRows18_0.length, ∀ c ∈ List.range degreeRows18_0.length,
      regionCheck 18 4 4 3 3 (a+1) (c+1) degreeRows18_0 degreeRegions18 := by
  decide +kernel

lemma degreeCover18_2_3 :
    ∀ a ∈ List.range degreeRows18_0.length, ∀ c ∈ List.range degreeRows18_0.length,
      regionCheck 18 4 4 3 4 (a+1) (c+1) degreeRows18_0 degreeRegions18 := by
  decide +kernel

lemma degreeCover18_2_4 :
    ∀ a ∈ List.range degreeRows18_0.length, ∀ c ∈ List.range degreeRows18_0.length,
      regionCheck 18 4 4 3 5 (a+1) (c+1) degreeRows18_0 degreeRegions18 := by
  decide +kernel

lemma degreeCover18_3_0 :
    ∀ a ∈ List.range degreeRows18_0.length, ∀ c ∈ List.range degreeRows18_0.length,
      regionCheck 18 4 4 4 1 (a+1) (c+1) degreeRows18_0 degreeRegions18 := by
  decide +kernel

lemma degreeCover18_3_1 :
    ∀ a ∈ List.range degreeRows18_0.length, ∀ c ∈ List.range degreeRows18_0.length,
      regionCheck 18 4 4 4 2 (a+1) (c+1) degreeRows18_0 degreeRegions18 := by
  decide +kernel

lemma degreeCover18_3_2 :
    ∀ a ∈ List.range degreeRows18_0.length, ∀ c ∈ List.range degreeRows18_0.length,
      regionCheck 18 4 4 4 3 (a+1) (c+1) degreeRows18_0 degreeRegions18 := by
  decide +kernel

lemma degreeCover18_3_3 :
    ∀ a ∈ List.range degreeRows18_0.length, ∀ c ∈ List.range degreeRows18_0.length,
      regionCheck 18 4 4 4 4 (a+1) (c+1) degreeRows18_0 degreeRegions18 := by
  decide +kernel

lemma degreeCover18_3_4 :
    ∀ a ∈ List.range degreeRows18_0.length, ∀ c ∈ List.range degreeRows18_0.length,
      regionCheck 18 4 4 4 5 (a+1) (c+1) degreeRows18_0 degreeRegions18 := by
  decide +kernel

lemma degreeCover18_4_0 :
    ∀ a ∈ List.range degreeRows18_0.length, ∀ c ∈ List.range degreeRows18_0.length,
      regionCheck 18 4 4 5 1 (a+1) (c+1) degreeRows18_0 degreeRegions18 := by
  decide +kernel

lemma degreeCover18_4_1 :
    ∀ a ∈ List.range degreeRows18_0.length, ∀ c ∈ List.range degreeRows18_0.length,
      regionCheck 18 4 4 5 2 (a+1) (c+1) degreeRows18_0 degreeRegions18 := by
  decide +kernel

lemma degreeCover18_4_2 :
    ∀ a ∈ List.range degreeRows18_0.length, ∀ c ∈ List.range degreeRows18_0.length,
      regionCheck 18 4 4 5 3 (a+1) (c+1) degreeRows18_0 degreeRegions18 := by
  decide +kernel

lemma degreeCover18_4_3 :
    ∀ a ∈ List.range degreeRows18_0.length, ∀ c ∈ List.range degreeRows18_0.length,
      regionCheck 18 4 4 5 4 (a+1) (c+1) degreeRows18_0 degreeRegions18 := by
  decide +kernel

lemma degreeCover18_4_4 :
    ∀ a ∈ List.range degreeRows18_0.length, ∀ c ∈ List.range degreeRows18_0.length,
      regionCheck 18 4 4 5 5 (a+1) (c+1) degreeRows18_0 degreeRegions18 := by
  decide +kernel

lemma degreeCover18 : ∀ d ∈ List.range 5, ∀ e ∈ List.range 5,
    ∀ a ∈ List.range degreeRows18_0.length, ∀ c ∈ List.range degreeRows18_0.length,
      regionCheck 18 4 4 (d+1) (e+1) (a+1) (c+1) degreeRows18_0 degreeRegions18 := by
  intro d hd e he
  have hd' : d < 5 := List.mem_range.mp hd
  have he' : e < 5 := List.mem_range.mp he
  interval_cases d <;> interval_cases e
  · exact degreeCover18_0_0
  · exact degreeCover18_0_1
  · exact degreeCover18_0_2
  · exact degreeCover18_0_3
  · exact degreeCover18_0_4
  · exact degreeCover18_1_0
  · exact degreeCover18_1_1
  · exact degreeCover18_1_2
  · exact degreeCover18_1_3
  · exact degreeCover18_1_4
  · exact degreeCover18_2_0
  · exact degreeCover18_2_1
  · exact degreeCover18_2_2
  · exact degreeCover18_2_3
  · exact degreeCover18_2_4
  · exact degreeCover18_3_0
  · exact degreeCover18_3_1
  · exact degreeCover18_3_2
  · exact degreeCover18_3_3
  · exact degreeCover18_3_4
  · exact degreeCover18_4_0
  · exact degreeCover18_4_1
  · exact degreeCover18_4_2
  · exact degreeCover18_4_3
  · exact degreeCover18_4_4

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_DegreeUnionData18
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Degree Union Data 18. -/

section

namespace UniversalTensorSquare

lemma degreeHalfHeight18 : ∀ R ∈ degreeHalfRegions18, firstBound 18 R.1 ≤ 17 := by decide +kernel

lemma degreeHalfWidth18 : ∀ R ∈ degreeHalfRegions18, firstBound 18 R.2 ≤ 17 := by decide +kernel

end UniversalTensorSquare
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Support_RowChecker
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Row Checker. -/

section

namespace UniversalTensorSquare

lemma quickRejected_iff (fuel n upper : ℕ) (A B : List (ℕ × ℕ)) :
    quickRejected fuel n upper A B = true ↔ rejectedRows fuel n upper A B := by
  simp only [quickRejected,rejectedRows,Bool.or_eq_true,Bool.and_eq_true,
    List.any_eq_true,decide_eq_true_eq]
  simp only [or_assoc]

lemma quickAllowed_iff (a : ℕ) (A B : List (ℕ × ℕ)) :
    quickAllowed a A B = true ↔ allowedRow a A B := by
  simp only [quickAllowed,allowedRow,Bool.and_eq_true,List.all_eq_true,
    Bool.or_eq_true,decide_eq_true_eq]
  constructor
  · rintro ⟨hA,hB⟩
    refine ⟨hA,fun p hp hk => ?_⟩
    obtain h | h := hB p hp
    · omega
    · exact h
  · rintro ⟨hA,hB⟩
    refine ⟨hA,fun p hp => ?_⟩
    by_cases hz : p.1 = 0
    · exact Or.inl hz
    · exact Or.inr (hB p hp (by omega))

end UniversalTensorSquare
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Support_FastRowCheck
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Fast Row Check. -/

section

namespace UniversalTensorSquare

lemma quickBand_sound {M r : ℕ} {rs : List ℕ} (h : quickBand M r rs = true) :
    RowsBand M r rs := by
  obtain ⟨k,hk,hh⟩ := List.any_eq_true.mp h
  simp only [Bool.and_eq_true,decide_eq_true_eq] at hh
  exact ⟨k,hk,hh.1.1,hh.1.2,hh.2⟩

lemma quickResidual_sound {M r : ℕ} {qs : List (List ℕ)} {t : RowTree} {rs : List ℕ}
    (h : quickResidual M r qs t rs = true) : TreeResidual M r qs t rs := by
  simp only [quickResidual,Bool.or_eq_true] at h
  rcases h with (((h | h) | h) | h) | h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr h)
  · exact Or.inl (Or.inl (quickBand_sound h))
  · exact Or.inl (Or.inr (Or.inl (quickBand_sound h)))
  · obtain ⟨q,hq,h⟩ := List.any_eq_true.mp h
    simp only [Bool.or_eq_true,decide_eq_true_eq] at h
    exact Or.inl (Or.inr (Or.inr (Or.inl ⟨q,hq,h⟩)))

end UniversalTensorSquare
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Support_UnionRowChecker
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Union Row Checker. -/

section

namespace UniversalTensorSquare

lemma checkRegionPrefixes_sound (P : List ℕ → Bool) (fuel n upper : ℕ)
    (regions : List PrefixRegion) (pref : List ℕ)
    (hc : checkRegionPrefixes P fuel n upper regions pref = true) :
    ∀ A B, (A,B) ∈ regions → ∀ rs ∈ constrainedRows fuel n upper A B,
      P (pref.reverse ++ rs) = true := by
  induction fuel generalizing n upper regions pref with
  | zero =>
    intro A B hR rs hrs
    rw [constrainedRows] at hrs
    split_ifs at hrs with hrej hn
    · simp at hrs
    · simp only [List.mem_singleton] at hrs
      subst rs
      have hmem : (A,B) ∈ liveRegions 0 n upper regions := by
        apply List.mem_filter.mpr
        exact ⟨hR,by simpa only [Bool.not_eq_true',quickRejected_iff,
          Bool.eq_false_iff,ne_eq] using hrej⟩
      have hne : ¬(liveRegions 0 n upper regions).isEmpty := by
        simp only [List.isEmpty_iff]
        intro he
        simp only [he,List.not_mem_nil] at hmem
      simpa only [checkRegionPrefixes,ite_eq_right hne,ite_eq_left hn,List.append_nil] using hc
    · simp at hrs
  | succ k ih =>
    intro A B hR rs hrs
    rw [constrainedRows] at hrs
    split_ifs at hrs with hrej
    · simp at hrs
    · have hmem : (A,B) ∈ liveRegions (k+1) n upper regions := by
        apply List.mem_filter.mpr
        exact ⟨hR,by simpa only [Bool.not_eq_true',quickRejected_iff,
          Bool.eq_false_iff,ne_eq] using hrej⟩
      have hne : ¬(liveRegions (k+1) n upper regions).isEmpty := by
        simp only [List.isEmpty_iff]
        intro he
        simp only [he,List.not_mem_nil] at hmem
      obtain ⟨a,ha,hr⟩ := List.mem_flatMap.mp hrs
      split_ifs at hr with hallowed
      · obtain ⟨ys,hy,rfl⟩ := List.mem_map.mp hr
        have hlo : max 1 (n/(k+1)) ≤ a := by
          have hh := Nat.div_le_of_le_mul hallowed.2
          have ha' := (List.mem_range'_1.mp ha).1
          exact max_le ha' hh
        have hai : a ∈ List.range' (max 1 (n/(k+1)))
            (min n upper+1-max 1 (n/(k+1))) := by
          have ha' := List.mem_range'_1.mp ha
          apply List.mem_range'_1.mpr
          refine ⟨hlo, ?_⟩
          have he : max 1 (n/(k+1)) + (min n upper+1-max 1 (n/(k+1))) = min n upper+1 := by
            apply Nat.add_sub_of_le
            omega
          rw [he]
          omega
        rw [checkRegionPrefixes] at hc
        simp only [ite_eq_right hne] at hc
        have hh := List.all_eq_true.mp hc a hai
        rw [ite_eq_left hallowed.2] at hh
        have hnext : (clipBudget A a,rowBudget B a) ∈
            nextRegions a (liveRegions (k+1) n upper regions) := by
          apply List.mem_filterMap.mpr
          refine ⟨(A,B),hmem,?_⟩
          simp only [quickAllowed_iff,ite_eq_left hallowed.1]
        have hi := ih (n-a) a (nextRegions a (liveRegions (k+1) n upper regions))
          (a::pref) hh _ _ hnext ys hy
        simpa only [List.reverse_cons,List.append_assoc,List.singleton_append] using hi
      · simp at hr

lemma checkedRegion_diagram {n M r H W : ℕ} {qs : List (List ℕ)} {t : RowTree}
    {regions : List PrefixRegion}
    (check : ∀ h ≤ H, checkRegionPrefixes (quickResidual M r qs t) h n W regions [] = true)
    (μ : YoungDiagram) (hn : μ.card = n) {A B : List (ℕ × ℕ)}
    (hR : (A,B) ∈ regions) (hA : RowBounds μ.transpose A) (hB : RowBounds μ B)
    (hH : firstBound n A ≤ H) (hW : firstBound n B ≤ W) :
    TreeResidual M r qs t μ.rowLens := by
  have hu : ∀ a ∈ μ.rowLens, a ≤ W := by
    intro a ha
    obtain ⟨i,hi,he⟩ := List.getElem_of_mem ha
    rw [← he, YoungDiagram.get_rowLens]
    exact (μ.rowLen_anti _ _ (Nat.zero_le _)).trans ((firstBound_sound μ hn hB).trans hW)
  have hl : μ.rowLens.length ≤ H := by
    rw [YoungDiagram.length_rowLens]
    have hh := (firstBound_sound μ.transpose ((Saxl.transpose_card μ).trans hn) hA).trans hH
    simpa only [YoungDiagram.rowLen_transpose] using hh
  have hmem : μ.rowLens ∈ constrainedRows μ.rowLens.length n W A B := by
    apply mem_constrainedRows _ _ _ _ _ _ rfl
    · exact (Saxl.card_eq_sum_rowLens μ).symm.trans hn
    · exact μ.pos_of_mem_rowLens
    · exact hu
    · exact μ.rowLens_sorted
    · intro p hp
      rw [clippedSum_rowLens]
      exact (hA p hp).2
    · intro p hp
      rw [← rowPrefix_eq_take]
      exact (hB p hp).2
  apply quickResidual_sound
  have hh := checkRegionPrefixes_sound (quickResidual M r qs t) μ.rowLens.length n W
    regions [] (check _ hl) A B hR μ.rowLens hmem
  simpa only [List.reverse_nil,List.nil_append] using hh

end UniversalTensorSquare
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_DegreeLeaves18
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Degree Leaves 18. -/

section

namespace UniversalTensorSquare

lemma degreeUnionBranch18_0 : checkRegionPrefixes (quickResidual 4 4 degreeQs18 degreeTree18) 0 18 17 degreeHalfRegions18 [] = true := by
  decide +kernel

lemma degreeUnionBranch18_1 : checkRegionPrefixes (quickResidual 4 4 degreeQs18 degreeTree18) 1 18 17 degreeHalfRegions18 [] = true := by
  decide +kernel

lemma degreeUnionBranch18_2 : checkRegionPrefixes (quickResidual 4 4 degreeQs18 degreeTree18) 2 18 17 degreeHalfRegions18 [] = true := by
  decide +kernel

lemma degreeUnionBranch18_3 : checkRegionPrefixes (quickResidual 4 4 degreeQs18 degreeTree18) 3 18 17 degreeHalfRegions18 [] = true := by
  decide +kernel

lemma degreeUnionBranch18_4 : checkRegionPrefixes (quickResidual 4 4 degreeQs18 degreeTree18) 4 18 17 degreeHalfRegions18 [] = true := by
  decide +kernel

lemma degreeUnionBranch18_5 : checkRegionPrefixes (quickResidual 4 4 degreeQs18 degreeTree18) 5 18 17 degreeHalfRegions18 [] = true := by
  decide +kernel

lemma degreeUnionBranch18_6 : checkRegionPrefixes (quickResidual 4 4 degreeQs18 degreeTree18) 6 18 17 degreeHalfRegions18 [] = true := by
  decide +kernel

lemma degreeUnionBranch18_7 : checkRegionPrefixes (quickResidual 4 4 degreeQs18 degreeTree18) 7 18 17 degreeHalfRegions18 [] = true := by
  decide +kernel

lemma degreeUnionBranch18_8 : checkRegionPrefixes (quickResidual 4 4 degreeQs18 degreeTree18) 8 18 17 degreeHalfRegions18 [] = true := by
  decide +kernel

lemma degreeUnionBranch18_9 : checkRegionPrefixes (quickResidual 4 4 degreeQs18 degreeTree18) 9 18 17 degreeHalfRegions18 [] = true := by
  decide +kernel

lemma degreeUnionBranch18_10 : checkRegionPrefixes (quickResidual 4 4 degreeQs18 degreeTree18) 10 18 17 degreeHalfRegions18 [] = true := by
  decide +kernel

lemma degreeUnionBranch18_11 : checkRegionPrefixes (quickResidual 4 4 degreeQs18 degreeTree18) 11 18 17 degreeHalfRegions18 [] = true := by
  decide +kernel

end UniversalTensorSquare
end

section

namespace UniversalTensorSquare

lemma degreeUnionBranch18_12 : checkRegionPrefixes (quickResidual 4 4 degreeQs18 degreeTree18) 12 18 17 degreeHalfRegions18 [] = true := by
  decide +kernel

lemma degreeUnionBranch18_13 : checkRegionPrefixes (quickResidual 4 4 degreeQs18 degreeTree18) 13 18 17 degreeHalfRegions18 [] = true := by
  decide +kernel

lemma degreeUnionBranch18_14 : checkRegionPrefixes (quickResidual 4 4 degreeQs18 degreeTree18) 14 18 17 degreeHalfRegions18 [] = true := by
  decide +kernel

lemma degreeUnionBranch18_15 : checkRegionPrefixes (quickResidual 4 4 degreeQs18 degreeTree18) 15 18 17 degreeHalfRegions18 [] = true := by
  decide +kernel

lemma degreeUnionBranch18_16 : checkRegionPrefixes (quickResidual 4 4 degreeQs18 degreeTree18) 16 18 17 degreeHalfRegions18 [] = true := by
  decide +kernel

lemma degreeUnionBranch18_17 : checkRegionPrefixes (quickResidual 4 4 degreeQs18 degreeTree18) 17 18 17 degreeHalfRegions18 [] = true := by
  decide +kernel

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
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_DegreeRegions18
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Degree Regions 18. -/

section

namespace UniversalTensorSquare

lemma degreeUnionCheck18 : ∀ h ≤ 17,
    checkRegionPrefixes (quickResidual 4 4 degreeQs18 degreeTree18) h 18 17 degreeHalfRegions18 [] = true := by
  intro h hh
  interval_cases h
  · exact degreeUnionBranch18_0
  · exact degreeUnionBranch18_1
  · exact degreeUnionBranch18_2
  · exact degreeUnionBranch18_3
  · exact degreeUnionBranch18_4
  · exact degreeUnionBranch18_5
  · exact degreeUnionBranch18_6
  · exact degreeUnionBranch18_7
  · exact degreeUnionBranch18_8
  · exact degreeUnionBranch18_9
  · exact degreeUnionBranch18_10
  · exact degreeUnionBranch18_11
  · exact degreeUnionBranch18_12
  · exact degreeUnionBranch18_13
  · exact degreeUnionBranch18_14
  · exact degreeUnionBranch18_15
  · exact degreeUnionBranch18_16
  · exact degreeUnionBranch18_17

lemma degreeHalfCover18 : ∀ R ∈ degreeRegions18,
    R ∈ degreeHalfRegions18 ∨ (R.2,R.1) ∈ degreeHalfRegions18 := by decide +kernel

lemma degreeDiagramRegionsChecked18 : ∀ R ∈ degreeRegions18,
    ∀ μ : YoungDiagram, μ.card = 18 → RowBounds μ.transpose R.1 →
      RowBounds μ R.2 → degreeP18 μ.rowLens :=
  checkedUnion_symmetric degreeUnionCheck18 degreeHalfHeight18 degreeHalfWidth18
    degreeHalfCover18

end UniversalTensorSquare
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_DegreeChecks18
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Degree Checks 18. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

lemma degreeCheck18 : ∀ d ∈ List.range 5, ∀ e ∈ List.range 5,
    ∀ a ∈ List.range degreeRows18_0.length, ∀ c ∈ List.range degreeRows18_0.length,
      semanticResidualCheck 18 4 4 (d+1) (e+1) (a+1) (c+1) degreeRows18_0 degreeP18 := by
  intro d hd e he a ha c hc
  exact regionCheck_sound_diagram degreeDiagramRegionsChecked18 (degreeCover18 d hd e he a ha c hc)

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_NumericalDegree18
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Numerical Degree 18. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns

lemma degree_pos18_oai (μ : YoungDiagram) (hμ : μ.card = 18) :
    0 < kronecker (canonicalTableau (candidate 4 2 0) degreeCard18)
      (canonicalTableau (candidate 4 2 0) degreeCard18) (canonicalTableau μ hμ) := by
  apply candidate_semantic_pos (r := 4) (by decide) (by decide) rfl (by decide)
    degreeCard18 degreeRows18_0 (by decide) (by decide)
    degreePlan18_0 (by decide) (by decide) (by decide) (by decide) degreeP18 ?_
    degreeCheck18 μ hμ
  intro rs hr hn hh
  exact treeResidual_sound (by decide) (by decide) degreeCard18 rfl degreeCones18
    degreeTreeAll18 hr hn hh

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.degree_pos18_oai := @OAI.UniversalTensorSquare.degree_pos18_oai
