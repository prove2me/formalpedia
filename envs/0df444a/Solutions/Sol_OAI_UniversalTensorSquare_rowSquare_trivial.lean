-- Prove2me | solution 1 for OAI.UniversalTensorSquare.rowSquare_trivial
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T13:37:53.669209+00:00
-- url     : https://prove2.me/submissions/19ce817e-c435-4dfb-b4f5-d1b5fb30a14b

import Mathlib
import Definitions.Def_UniversalTensorSquares
import Definitions.Def_OAIQ259US021
import Theorems.Thm_OAI_Saxl_young_orbit_map_uts
import Theorems.Thm_OAI_UniversalTensorSquare_rowDiagram_eq

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
-- module Solutions.OAIQ259_US.UniversalSquare_Specht_RepeatedColumns
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Repeated Columns. -/

section

noncomputable section
open scoped TensorProduct
namespace Saxl

theorem specht_map_back_of_nonzero {n : ℕ} {μ : YoungDiagram}
    {X : Type*} [AddCommGroup X] [Module ℂ X]
    (ρ : Representation ℂ (Equiv.Perm (Fin n)) X) (t : Tableau n μ)
    (F : Representation.IntertwiningMap ρ (spechtRep t)) (hF : F ≠ 0) :
    ∃ f : Representation.IntertwiningMap (spechtRep t) ρ, f ≠ 0 := by
  let := specht_irreducible t
  have hs : Function.Surjective F :=
    (Representation.IsIrreducible.surjective_or_eq_zero F).resolve_right hF
  obtain ⟨f, hf⟩ := intertwining_lift_surjective F hs
    (Representation.IntertwiningMap.id (spechtRep t))
  refine ⟨f, ?_⟩
  intro hz
  have he := congrArg (fun H : Representation.IntertwiningMap (spechtRep t) (spechtRep t) =>
    H ⟨polytabloid t, mem_cyclic _ _⟩) hf
  change F (f _) = _ at he
  rw [hz] at he
  change F 0 = _ at he
  rw [map_zero] at he
  exact polytabloid_ne_zero t (congrArg Subtype.val he.symm)

theorem kronecker_pos_of_column_content {n : ℕ} {α μ : YoungDiagram}
    (a : Tableau n α) (t : Tableau n μ) (θ : YoungDiagram)
    (hc : μ.card = θ.card) (hd : Dominates μ θ)
    (f : Fin (α.colLen 0) → Fin (θ.colLen 0))
    (hw : ∀ j, (Finset.univ.filter (fun i => f (columnLengthWord a i) = j)).card =
      θ.rowLen j) : 0 < kronecker a a t := by
  classical
  let w := f ∘ columnLengthWord a
  obtain ⟨F, hF⟩ := young_orbit_map_uts θ μ t hc hd w (Equiv.refl _) hw
  let P : Representation.IntertwiningMap ((spechtRep a).tprod (spechtRep a))
      (wordRep n (θ.colLen 0)) := (letterLift f).comp ((orbitProjection (columnLengthWord a)).comp
    ((pairSumMap n (α.colLen 0) (α.colLen 0)).comp (spechtTensorMap a a)))
  let Q : Representation.IntertwiningMap ((spechtRep a).tprod (spechtRep a))
      (spechtRep t) := F.comp P
  let v : Specht a := ⟨polytabloid a, mem_cyclic _ _⟩
  have hp : P (v ⊗ₜ[ℂ] v) =
      ((Nat.card (columnGroup a) : ℂ) * signC (columnReversal a).val) •
        Pi.single w 1 := by
    change letterLift f (orbitProjection _ (pairSumMap _ _ _
      (spechtTensorMap a a (v ⊗ₜ[ℂ] v)))) = _
    have he : spechtTensorMap a a (v ⊗ₜ[ℂ] v) =
        wordTensor _ _ _ (polytabloid a ⊗ₜ[ℂ] polytabloid a) := by
      unfold spechtTensorMap
      rfl
    rw [he, squared_polytabloid_projection, map_smul, letterLift_single]
  have hQ : Q ≠ 0 := by
    intro hz
    have hh := congrArg (fun H => H (v ⊗ₜ[ℂ] v)) hz
    change F (P (v ⊗ₜ[ℂ] v)) = 0 at hh
    rw [hp, map_smul] at hh
    exact (smul_ne_zero (column_projection_coefficient_ne_zero a) hF) hh
  apply (kronecker_pos_iff a a t).mpr
  exact specht_map_back_of_nonzero (X := Specht a ⊗[ℂ] Specht a)
    ((spechtRep a).tprod (spechtRep a)) t Q hQ

end Saxl
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

lemma rowDiagram_rowLen {rs : List ℕ} (h : GoodRows rs) (i : ℕ) :
    (rowDiagram rs).rowLen i = rs[i]?.getD 0 := by
  rw [rowDiagram_eq rs h,ofRowLens_rowLen]

lemma rowDiagram_height {rs : List ℕ} (h : GoodRows rs) :
    (rowDiagram rs).colLen 0 = rs.length := by
  rw [← YoungDiagram.length_rowLens,rowDiagram_rows h]

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Support_RowSquareTools
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Row Square Tools. -/

section

noncomputable section
open scoped TensorProduct
namespace UniversalTensorSquare
open Saxl Saxl.Columns Saxl.Balance

lemma rowSquare_trivial_oai (p : List ℕ) (hn : 0 < p.sum) : RowSquare p [p.sum] := by
  have hgood : GoodRows [p.sum] := ⟨by apply List.Pairwise.sortedGE; simp,by simpa using hn⟩
  let a := canonicalTableau (rowDiagram p) (rowDiagram_card p)
  let t := canonicalTableau (rowDiagram [p.sum]) (by simpa using rowDiagram_card [p.sum])
  have height : (rowDiagram [p.sum]).colLen 0 = 1 := by rw [rowDiagram_height hgood]; rfl
  let f : Fin ((rowDiagram p).colLen 0) → Fin ((rowDiagram [p.sum]).colLen 0) :=
    fun _ => ⟨0,by omega⟩
  refine ⟨p.sum,a,t,kronecker_pos_of_column_content a t (rowDiagram [p.sum]) rfl
    (fun _ => le_rfl) f ?_⟩
  intro j
  have hj : j.val = 0 := by have := j.isLt; omega
  have heq (i : Fin p.sum) : f (columnLengthWord a i) = j := Fin.ext hj.symm
  simp only [heq,Finset.filter_true,Finset.card_univ,Fintype.card_fin,
    rowDiagram_rowLen hgood,hj]
  rfl

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.rowSquare_trivial_oai := @OAI.UniversalTensorSquare.rowSquare_trivial_oai
