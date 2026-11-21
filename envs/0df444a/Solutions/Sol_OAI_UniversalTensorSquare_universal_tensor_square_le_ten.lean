-- Prove2me | solution 1 for OAI.UniversalTensorSquare.universal_tensor_square_le_ten
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T00:29:11.936297+00:00
-- url     : https://prove2.me/submissions/d1493989-58e3-403c-9866-931adbfe6d48

import Mathlib
import Definitions.Def_UniversalTensorSquares
import Definitions.Def_OAIQ259US006
import Definitions.Def_OAIQ259US007
import Definitions.Def_OAIQ259US012
import Definitions.Def_OAIQ259US000
import Theorems.Thm_OAI_Saxl_saxl_kronecker_pos
import Definitions.Def_OAIQ259US002
import Theorems.Thm_OAI_UniversalTensorSquare_eight_kronecker_pos
import Definitions.Def_OAIQ259US001
import Theorems.Thm_OAI_UniversalTensorSquare_seven_kronecker_pos
import Theorems.Thm_OAI_UniversalTensorSquare_universal_tensor_square_five

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
-- module Solutions.OAIQ259_US.UniversalSquare_Support_Extensions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Extensions. -/

section

noncomputable section
open scoped TensorProduct

namespace UniversalTensorSquare

universe u

theorem irreducibles_of_kronecker_pos {n : ℕ} (lam : YoungDiagram) (hlam : lam.card = n)
    (hpos : ∀ (ν : YoungDiagram) (hν : ν.card = n),
      0 < Saxl.kronecker (Saxl.canonicalTableau lam hlam)
        (Saxl.canonicalTableau lam hlam) (Saxl.canonicalTableau ν hν)) :
    Representation.IsIrreducible (Saxl.spechtRep (Saxl.canonicalTableau lam hlam)) ∧
    ∀ (V : Type u) [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V]
      (ρ : Representation ℂ (Equiv.Perm (Fin n)) V) [Representation.IsIrreducible ρ],
      ∃ F : Representation.IntertwiningMap ρ
        ((Saxl.spechtRep (Saxl.canonicalTableau lam hlam)).tprod
          (Saxl.spechtRep (Saxl.canonicalTableau lam hlam))),
        Function.Injective F := by
  refine ⟨Saxl.specht_irreducible _, ?_⟩
  intro V _ _ _ ρ _
  obtain ⟨p, ⟨e⟩⟩ := Saxl.irreducible_equiv_specht ρ
  obtain ⟨f, hf⟩ := (Saxl.kronecker_pos_iff _ _ _).mp
    (hpos (Saxl.partitionDiagram p) (Saxl.partitionDiagram_card p))
  let := Saxl.specht_irreducible (Saxl.canonicalTableau (Saxl.partitionDiagram p)
    (Saxl.partitionDiagram_card p))
  have hs := Representation.IsIrreducible.injective_or_eq_zero
    (W := Saxl.Specht (Saxl.canonicalTableau lam hlam) ⊗[ℂ]
      Saxl.Specht (Saxl.canonicalTableau lam hlam)) f
  have hi : Function.Injective f := hs.resolve_right hf
  exact ⟨f.comp e.toIntertwiningMap, hi.comp e.injective⟩

theorem universal_tensor_square_triangular (m : ℕ) (hm : 1 ≤ m) :
    ∃ (lam : YoungDiagram) (hlam : lam.card = m * (m + 1) / 2),
      (∀ (ν : YoungDiagram) (hν : ν.card = m * (m + 1) / 2),
        0 < Saxl.kronecker (Saxl.canonicalTableau lam hlam)
          (Saxl.canonicalTableau lam hlam) (Saxl.canonicalTableau ν hν)) ∧
      Representation.IsIrreducible (Saxl.spechtRep (Saxl.canonicalTableau lam hlam)) ∧
      ∀ (V : Type u) [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V]
        (ρ : Representation ℂ (Equiv.Perm (Fin (m * (m + 1) / 2))) V)
        [Representation.IsIrreducible ρ],
        ∃ F : Representation.IntertwiningMap ρ
          ((Saxl.spechtRep (Saxl.canonicalTableau lam hlam)).tprod
            (Saxl.spechtRep (Saxl.canonicalTableau lam hlam))),
          Function.Injective F := by
  refine ⟨Saxl.staircase m, Saxl.staircase_card m, Saxl.saxl_kronecker_pos m hm, ?_⟩
  exact irreducibles_of_kronecker_pos _ _ (Saxl.saxl_kronecker_pos m hm)

end UniversalTensorSquare

end
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

noncomputable section

universe u

theorem universal_tensor_square_eight :
    ∃ (lam : YoungDiagram) (hlam : lam.card = 8),
      (∀ (ν : YoungDiagram) (hν : ν.card = 8),
        0 < kronecker (canonicalTableau lam hlam)
          (canonicalTableau lam hlam) (canonicalTableau ν hν)) ∧
      Representation.IsIrreducible (spechtRep (canonicalTableau lam hlam)) ∧
      ∀ (V : Type u) [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V]
        (ρ : Representation ℂ (Equiv.Perm (Fin 8)) V) [Representation.IsIrreducible ρ],
        ∃ F : Representation.IntertwiningMap ρ
          ((spechtRep (canonicalTableau lam hlam)).tprod
            (spechtRep (canonicalTableau lam hlam))), Function.Injective F := by
  exact ⟨eightWitness, eightWitness_card, eight_kronecker_pos,
    irreducibles_of_kronecker_pos _ _ eight_kronecker_pos⟩

end
end UniversalTensorSquare
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Finite_DegreeSeven
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Degree Seven. -/

section

open Saxl Saxl.Columns
namespace UniversalTensorSquare

noncomputable section

universe u

theorem universal_tensor_square_seven :
    ∃ (lam : YoungDiagram) (hlam : lam.card = 7),
      (∀ (ν : YoungDiagram) (hν : ν.card = 7),
        0 < kronecker (canonicalTableau lam hlam)
          (canonicalTableau lam hlam) (canonicalTableau ν hν)) ∧
      Representation.IsIrreducible (spechtRep (canonicalTableau lam hlam)) ∧
      ∀ (V : Type u) [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V]
        (ρ : Representation ℂ (Equiv.Perm (Fin 7)) V) [Representation.IsIrreducible ρ],
        ∃ F : Representation.IntertwiningMap ρ
          ((spechtRep (canonicalTableau lam hlam)).tprod
            (spechtRep (canonicalTableau lam hlam))), Function.Injective F := by
  exact ⟨sevenWitness, sevenWitness_card, seven_kronecker_pos,
    irreducibles_of_kronecker_pos _ _ seven_kronecker_pos⟩

end
end UniversalTensorSquare
end

end OAI
end

section
-- module Solutions.OAIQ259_US.UniversalSquare_Support_SmallDegrees
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Small Degrees. -/

section

namespace UniversalTensorSquare
open Saxl

universe u

theorem universal_tensor_square_le_ten_oai
    (n : ℕ) (hn : 0 < n) (h2 : n ≠ 2) (h4 : n ≠ 4) (h9 : n ≠ 9)
    (hsmall : n ≤ 10) :
    ∃ (lam : YoungDiagram) (hlam : lam.card = n),
      (∀ (ν : YoungDiagram) (hν : ν.card = n),
        0 < kronecker (canonicalTableau lam hlam)
          (canonicalTableau lam hlam) (canonicalTableau ν hν)) ∧
      Representation.IsIrreducible (spechtRep (canonicalTableau lam hlam)) ∧
      ∀ (V : Type u) [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V]
        (ρ : Representation ℂ (Equiv.Perm (Fin n)) V) [Representation.IsIrreducible ρ],
        ∃ F : Representation.IntertwiningMap ρ
          ((spechtRep (canonicalTableau lam hlam)).tprod
            (spechtRep (canonicalTableau lam hlam))), Function.Injective F := by
  have hcases : n = 1 ∨ n = 3 ∨ n = 5 ∨ n = 6 ∨ n = 7 ∨ n = 8 ∨ n = 10 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact universal_tensor_square_triangular 1 (by decide)
  · exact universal_tensor_square_triangular 2 (by decide)
  · exact universal_tensor_square_five
  · exact universal_tensor_square_triangular 3 (by decide)
  · exact universal_tensor_square_seven
  · exact universal_tensor_square_eight
  · exact universal_tensor_square_triangular 4 (by decide)

end UniversalTensorSquare
end

end OAI
end

theorem solution.{u} : type_of% @OAI.UniversalTensorSquare.universal_tensor_square_le_ten_oai.{u} := @OAI.UniversalTensorSquare.universal_tensor_square_le_ten_oai.{u}
