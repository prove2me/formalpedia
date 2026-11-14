-- Prove2me | solution 1 for OAI.UniversalTensorSquare.packingPlan_pos
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T13:05:51.968062+00:00
-- url     : https://prove2.me/submissions/52f35e68-be82-4b37-b2f2-a869e8841f7e

import Mathlib
import Definitions.Def_UniversalTensorSquares
import Definitions.Def_OAIQ259US004
import Definitions.Def_OAIQ259US022
import Theorems.Thm_OAI_Saxl_Balance_PackingPlan_realize
import Theorems.Thm_OAI_Saxl_Balance_WordPacking_kronecker_pos

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
-- module Solutions.OAIQ259_US.UniversalSquare_Band_OutputBands
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Output Bands. -/

section

noncomputable section
namespace Saxl.Balance

lemma OutputBands.label_spec (B : OutputBands) {x : ℕ} (h : B.Allows x) :
    B.label x ∈ B.starts ∧ B.label x ≤ x ∧ x ≤ B.upper (B.label x) := by
  rw [OutputBands.label,dite_eq_left h]
  exact Classical.choose_spec h

lemma OutputBands.unique (B : OutputBands) {x k l : ℕ}
    (hk : k ∈ B.starts) (hl : l ∈ B.starts)
    (hkx : k ≤ x) (hxk : x ≤ B.upper k) (hlx : l ≤ x) (hxl : x ≤ B.upper l) : k = l := by
  rcases lt_trichotomy k l with h | h | h
  · have := B.separated k hk l hl h
    omega
  · exact h
  · have := B.separated l hl k hk h
    omega

lemma OutputBands.label_iff (B : OutputBands) {k x : ℕ} (hk : k ∈ B.starts) :
    (B.Allows x ∧ B.label x = k) ↔ x ∈ Set.Icc k (B.upper k) := by
  constructor
  · rintro ⟨hx,hk'⟩
    have h := B.label_spec hx
    rw [hk'] at h
    exact h.2
  · rintro ⟨hkx,hxk⟩
    have hx : B.Allows x := ⟨k,hk,hkx,hxk⟩
    have h := B.label_spec hx
    exact ⟨hx,B.unique h.1 hk h.2.1 h.2.2 hkx hxk⟩

lemma OutputBands.ordered (B : OutputBands) {x y : ℕ}
    (hx : B.Allows x) (hy : B.Allows y) (hxy : B.label x < B.label y) : x < y := by
  have hx' := B.label_spec hx
  have hy' := B.label_spec hy
  exact lt_of_le_of_lt hx'.2.2 ((B.separated _ hx'.1 _ hy'.1 hxy).trans_le hy'.2.1)

lemma OutputBands.letter_iff (B : OutputBands) {d k : ℕ} (hk : k ∈ B.starts)
    (a : Fin (d*d)) :
    (B.alphabet d a ∧ B.letterLabel d a = k) ↔ output a ∈ Set.Icc k (B.upper k) :=
  B.label_iff hk

lemma OutputBands.letter_ordered (B : OutputBands) (d : ℕ) :
    ∀ x y, B.alphabet d x → B.alphabet d y →
      B.letterLabel d x < B.letterLabel d y → output x < output y := by
  intro x y hx hy h
  exact B.ordered hx hy h

end Saxl.Balance
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Capacity_NumericBands
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Numeric Bands. -/

section

noncomputable section
namespace Saxl.Balance

lemma numericBands_iff {es : List (ℕ × ℕ)} (h : BandsValid es) {e : ℕ × ℕ}
    (he : e ∈ es) {d : ℕ} (z : Fin (d*d)) :
    ((numericBands es h).alphabet d z ∧ (numericBands es h).letterLabel d z = e.1) ↔
      output z ∈ Set.Icc e.1 e.2 := by
  rw [(numericBands es h).letter_iff (mem_bandStarts.mpr ⟨e,he,rfl⟩)]
  rw [show (numericBands es h).upper e.1 = e.2 from bandUpper_eq h he]

end Saxl.Balance
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

end UniversalTensorSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Balance_PackingPlans
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Packing Plans. -/

section

noncomputable section

namespace UniversalTensorSquare
open Saxl Saxl.Balance Saxl.Columns Saxl.FlagColumns

theorem packingPlan_pos_oai {n d : ℕ} (p : PackingPlan) {lam μ : YoungDiagram}
    (hv : p.Valid d) (hb : BandsValid p.bands) (hheight : lam.colLen 0 = d)
    (hc : p.columns.Perm lam.transpose.rowLens) (hp : ∀ x ∈ p.parts, 0 < x)
    (a : Tableau n lam) (t : Tableau n μ)
    (hd : Dominates μ (columnShape p.parts).transpose) : 0 < kronecker a a t := by
  obtain ⟨e,hr,hc'⟩ := place_columns lam hc
  have hn : p.columns.sum = n := by
    simpa only [Fintype.card_fin] using Fintype.card_congr (((enumerate p.columns).trans e).trans a.symm)
  subst n
  let B := numericBands p.bands hb
  obtain ⟨P⟩ := p.realize hv (B.alphabet d) (B.letterLabel d)
    (fun e he z => numericBands_iff hb he z)
  rw [← hheight] at P
  let a' := (enumerate p.columns).trans e
  exact kronecker_pos_of_shapes rfl rfl rfl a' a' t a a t
    (P.kronecker_pos a' t (standard_placed_self e hr hc') hp (B.letter_ordered _) hd)

end UniversalTensorSquare
end
end

end OAI
end

theorem solution : type_of% @OAI.UniversalTensorSquare.packingPlan_pos_oai := @OAI.UniversalTensorSquare.packingPlan_pos_oai
