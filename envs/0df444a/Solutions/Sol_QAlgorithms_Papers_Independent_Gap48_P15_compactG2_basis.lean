-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Gap48.P15.compactG2_basis
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung
-- created : 2026-10-22T00:19:22.750643+00:00
-- url     : https://prove2.me/submissions/f5334a4b-b1e1-464d-ae57-0b4b026fdd50

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P15

open QAlgorithms.Papers.Independent.Gap48.P15

attribute [local instance 100] LieRing.ofAssociativeRing

-- Reuse Mathlib Matrix and Matrix.single directly. Natural one-based
-- coordinates are restricted to Fin coordinates with Matrix.submatrix.

namespace G2Gen
lemma span_eq_lieSpan {t m : ℕ} (v : Fin m → Matrix (Fin t) (Fin t) ℝ)
    (h : ∀ i j, ⁅v i, v j⁆ ∈ Submodule.span ℝ (Set.range v)) :
    Submodule.span ℝ (Set.range v) =
      (LieSubalgebra.lieSpan ℝ (Matrix (Fin t) (Fin t) ℝ) (Set.range v)).toSubmodule := by
  set S := Submodule.span ℝ (Set.range v) with hS
  have hcl : ∀ x ∈ S, ∀ y ∈ S, ⁅x, y⁆ ∈ S := by
    intro x hx y hy
    induction hx using Submodule.span_induction with
    | mem x hx' =>
      obtain ⟨i, rfl⟩ := hx'
      induction hy using Submodule.span_induction with
      | mem y hy' => obtain ⟨j, rfl⟩ := hy'; exact h i j
      | zero => simp
      | add a b _ _ ha hb => rw [lie_add]; exact S.add_mem ha hb
      | smul r a _ ha => rw [lie_smul]; exact S.smul_mem r ha
    | zero => simp
    | add a b _ _ ha hb => rw [add_lie]; exact S.add_mem ha hb
    | smul r a _ ha => rw [smul_lie]; exact S.smul_mem r ha
  let L' : LieSubalgebra ℝ (Matrix (Fin t) (Fin t) ℝ) :=
    { S with lie_mem' := fun {x y} hx hy => hcl x hx y hy }
  apply le_antisymm
  · rw [Submodule.span_le]; rintro _ ⟨i, rfl⟩; exact LieSubalgebra.subset_lieSpan ⟨i, rfl⟩
  · have hle : LieSubalgebra.lieSpan ℝ _ (Set.range v) ≤ L' :=
      (LieSubalgebra.lieSpan_le).2 (fun x hx => Submodule.subset_span hx)
    exact fun x hx => hle hx
end G2Gen

namespace G2Hcompact
open Matrix

abbrev E (a b : Fin 8) : Matrix (Fin 8) (Fin 8) ℝ := Matrix.single a b 1

lemma subS (p q : ℕ) (a b : Fin 8) (ha : a.val + 1 = p) (hb : b.val + 1 = q) :
    (Matrix.single p q (1:ℝ)).submatrix (fun i : Fin 8 => i.val + 1) (fun j : Fin 8 => j.val + 1) =
      E a b := by
  ext i j
  simp only [Matrix.submatrix_apply, E, Matrix.single_apply, Fin.ext_iff]
  congr 1
  apply propext; omega

def b' : Fin 14 → Matrix (Fin 8) (Fin 8) ℝ := ![
  E 1 2 - E 2 1 + E 5 6 - E 6 5,
  E 1 3 - E 3 1 + E 5 7 - E 7 5,
  E 1 4 - E 3 6 - E 4 1 + E 6 3,
  E 1 5 - E 3 7 - E 5 1 + E 7 3,
  E 1 6 + E 3 4 - E 4 3 - E 6 1,
  E 1 7 + E 3 5 - E 5 3 - E 7 1,
  E 2 3 - E 3 2 + E 6 7 - E 7 6,
  E 2 4 + E 3 5 - E 4 2 - E 5 3,
  E 2 5 - E 3 4 + E 4 3 - E 5 2,
  E 2 6 - E 3 7 - E 6 2 + E 7 3,
  E 2 7 + E 3 6 - E 6 3 - E 7 2,
  E 4 5 - E 5 4 + E 6 7 - E 7 6,
  E 4 6 - E 5 7 - E 6 4 + E 7 5,
  E 4 7 + E 5 6 - E 6 5 - E 7 4]

lemma s23 : (Matrix.single 2 3 (1:ℝ)).submatrix (fun i : Fin 8 => i.val + 1) (fun j : Fin 8 => j.val + 1) = E 1 2 := subS 2 3 1 2 rfl rfl
lemma s32 : (Matrix.single 3 2 (1:ℝ)).submatrix (fun i : Fin 8 => i.val + 1) (fun j : Fin 8 => j.val + 1) = E 2 1 := subS 3 2 2 1 rfl rfl
lemma s24 : (Matrix.single 2 4 (1:ℝ)).submatrix (fun i : Fin 8 => i.val + 1) (fun j : Fin 8 => j.val + 1) = E 1 3 := subS 2 4 1 3 rfl rfl
lemma s42 : (Matrix.single 4 2 (1:ℝ)).submatrix (fun i : Fin 8 => i.val + 1) (fun j : Fin 8 => j.val + 1) = E 3 1 := subS 4 2 3 1 rfl rfl
lemma s25 : (Matrix.single 2 5 (1:ℝ)).submatrix (fun i : Fin 8 => i.val + 1) (fun j : Fin 8 => j.val + 1) = E 1 4 := subS 2 5 1 4 rfl rfl
lemma s52 : (Matrix.single 5 2 (1:ℝ)).submatrix (fun i : Fin 8 => i.val + 1) (fun j : Fin 8 => j.val + 1) = E 4 1 := subS 5 2 4 1 rfl rfl
lemma s26 : (Matrix.single 2 6 (1:ℝ)).submatrix (fun i : Fin 8 => i.val + 1) (fun j : Fin 8 => j.val + 1) = E 1 5 := subS 2 6 1 5 rfl rfl
lemma s62 : (Matrix.single 6 2 (1:ℝ)).submatrix (fun i : Fin 8 => i.val + 1) (fun j : Fin 8 => j.val + 1) = E 5 1 := subS 6 2 5 1 rfl rfl
lemma s27 : (Matrix.single 2 7 (1:ℝ)).submatrix (fun i : Fin 8 => i.val + 1) (fun j : Fin 8 => j.val + 1) = E 1 6 := subS 2 7 1 6 rfl rfl
lemma s72 : (Matrix.single 7 2 (1:ℝ)).submatrix (fun i : Fin 8 => i.val + 1) (fun j : Fin 8 => j.val + 1) = E 6 1 := subS 7 2 6 1 rfl rfl
lemma s28 : (Matrix.single 2 8 (1:ℝ)).submatrix (fun i : Fin 8 => i.val + 1) (fun j : Fin 8 => j.val + 1) = E 1 7 := subS 2 8 1 7 rfl rfl
lemma s82 : (Matrix.single 8 2 (1:ℝ)).submatrix (fun i : Fin 8 => i.val + 1) (fun j : Fin 8 => j.val + 1) = E 7 1 := subS 8 2 7 1 rfl rfl
lemma s34 : (Matrix.single 3 4 (1:ℝ)).submatrix (fun i : Fin 8 => i.val + 1) (fun j : Fin 8 => j.val + 1) = E 2 3 := subS 3 4 2 3 rfl rfl
lemma s43 : (Matrix.single 4 3 (1:ℝ)).submatrix (fun i : Fin 8 => i.val + 1) (fun j : Fin 8 => j.val + 1) = E 3 2 := subS 4 3 3 2 rfl rfl
lemma s35 : (Matrix.single 3 5 (1:ℝ)).submatrix (fun i : Fin 8 => i.val + 1) (fun j : Fin 8 => j.val + 1) = E 2 4 := subS 3 5 2 4 rfl rfl
lemma s53 : (Matrix.single 5 3 (1:ℝ)).submatrix (fun i : Fin 8 => i.val + 1) (fun j : Fin 8 => j.val + 1) = E 4 2 := subS 5 3 4 2 rfl rfl
lemma s36 : (Matrix.single 3 6 (1:ℝ)).submatrix (fun i : Fin 8 => i.val + 1) (fun j : Fin 8 => j.val + 1) = E 2 5 := subS 3 6 2 5 rfl rfl
lemma s63 : (Matrix.single 6 3 (1:ℝ)).submatrix (fun i : Fin 8 => i.val + 1) (fun j : Fin 8 => j.val + 1) = E 5 2 := subS 6 3 5 2 rfl rfl
lemma s37 : (Matrix.single 3 7 (1:ℝ)).submatrix (fun i : Fin 8 => i.val + 1) (fun j : Fin 8 => j.val + 1) = E 2 6 := subS 3 7 2 6 rfl rfl
lemma s73 : (Matrix.single 7 3 (1:ℝ)).submatrix (fun i : Fin 8 => i.val + 1) (fun j : Fin 8 => j.val + 1) = E 6 2 := subS 7 3 6 2 rfl rfl
lemma s38 : (Matrix.single 3 8 (1:ℝ)).submatrix (fun i : Fin 8 => i.val + 1) (fun j : Fin 8 => j.val + 1) = E 2 7 := subS 3 8 2 7 rfl rfl
lemma s83 : (Matrix.single 8 3 (1:ℝ)).submatrix (fun i : Fin 8 => i.val + 1) (fun j : Fin 8 => j.val + 1) = E 7 2 := subS 8 3 7 2 rfl rfl
lemma s45 : (Matrix.single 4 5 (1:ℝ)).submatrix (fun i : Fin 8 => i.val + 1) (fun j : Fin 8 => j.val + 1) = E 3 4 := subS 4 5 3 4 rfl rfl
lemma s54 : (Matrix.single 5 4 (1:ℝ)).submatrix (fun i : Fin 8 => i.val + 1) (fun j : Fin 8 => j.val + 1) = E 4 3 := subS 5 4 4 3 rfl rfl
lemma s46 : (Matrix.single 4 6 (1:ℝ)).submatrix (fun i : Fin 8 => i.val + 1) (fun j : Fin 8 => j.val + 1) = E 3 5 := subS 4 6 3 5 rfl rfl
lemma s64 : (Matrix.single 6 4 (1:ℝ)).submatrix (fun i : Fin 8 => i.val + 1) (fun j : Fin 8 => j.val + 1) = E 5 3 := subS 6 4 5 3 rfl rfl
lemma s47 : (Matrix.single 4 7 (1:ℝ)).submatrix (fun i : Fin 8 => i.val + 1) (fun j : Fin 8 => j.val + 1) = E 3 6 := subS 4 7 3 6 rfl rfl
lemma s74 : (Matrix.single 7 4 (1:ℝ)).submatrix (fun i : Fin 8 => i.val + 1) (fun j : Fin 8 => j.val + 1) = E 6 3 := subS 7 4 6 3 rfl rfl
lemma s48 : (Matrix.single 4 8 (1:ℝ)).submatrix (fun i : Fin 8 => i.val + 1) (fun j : Fin 8 => j.val + 1) = E 3 7 := subS 4 8 3 7 rfl rfl
lemma s84 : (Matrix.single 8 4 (1:ℝ)).submatrix (fun i : Fin 8 => i.val + 1) (fun j : Fin 8 => j.val + 1) = E 7 3 := subS 8 4 7 3 rfl rfl
lemma s56 : (Matrix.single 5 6 (1:ℝ)).submatrix (fun i : Fin 8 => i.val + 1) (fun j : Fin 8 => j.val + 1) = E 4 5 := subS 5 6 4 5 rfl rfl
lemma s65 : (Matrix.single 6 5 (1:ℝ)).submatrix (fun i : Fin 8 => i.val + 1) (fun j : Fin 8 => j.val + 1) = E 5 4 := subS 6 5 5 4 rfl rfl
lemma s57 : (Matrix.single 5 7 (1:ℝ)).submatrix (fun i : Fin 8 => i.val + 1) (fun j : Fin 8 => j.val + 1) = E 4 6 := subS 5 7 4 6 rfl rfl
lemma s75 : (Matrix.single 7 5 (1:ℝ)).submatrix (fun i : Fin 8 => i.val + 1) (fun j : Fin 8 => j.val + 1) = E 6 4 := subS 7 5 6 4 rfl rfl
lemma s58 : (Matrix.single 5 8 (1:ℝ)).submatrix (fun i : Fin 8 => i.val + 1) (fun j : Fin 8 => j.val + 1) = E 4 7 := subS 5 8 4 7 rfl rfl
lemma s85 : (Matrix.single 8 5 (1:ℝ)).submatrix (fun i : Fin 8 => i.val + 1) (fun j : Fin 8 => j.val + 1) = E 7 4 := subS 8 5 7 4 rfl rfl
lemma s67 : (Matrix.single 6 7 (1:ℝ)).submatrix (fun i : Fin 8 => i.val + 1) (fun j : Fin 8 => j.val + 1) = E 5 6 := subS 6 7 5 6 rfl rfl
lemma s76 : (Matrix.single 7 6 (1:ℝ)).submatrix (fun i : Fin 8 => i.val + 1) (fun j : Fin 8 => j.val + 1) = E 6 5 := subS 7 6 6 5 rfl rfl
lemma s68 : (Matrix.single 6 8 (1:ℝ)).submatrix (fun i : Fin 8 => i.val + 1) (fun j : Fin 8 => j.val + 1) = E 5 7 := subS 6 8 5 7 rfl rfl
lemma s86 : (Matrix.single 8 6 (1:ℝ)).submatrix (fun i : Fin 8 => i.val + 1) (fun j : Fin 8 => j.val + 1) = E 7 5 := subS 8 6 7 5 rfl rfl
lemma s78 : (Matrix.single 7 8 (1:ℝ)).submatrix (fun i : Fin 8 => i.val + 1) (fun j : Fin 8 => j.val + 1) = E 6 7 := subS 7 8 6 7 rfl rfl
lemma s87 : (Matrix.single 8 7 (1:ℝ)).submatrix (fun i : Fin 8 => i.val + 1) (fun j : Fin 8 => j.val + 1) = E 7 6 := subS 8 7 7 6 rfl rfl
lemma heq : bG2 = b' := by
  funext k; fin_cases k <;>
    simp only [bG2, b', QAlgorithms.Papers.Independent.Gap48.P15.J, QAlgorithms.Papers.Independent.Gap48.P15.Z, s23, s24, s25, s26, s27, s28, s32, s34, s35, s36, s37, s38, s42, s43, s45, s46, s47, s48, s52, s53, s54, s56, s57, s58, s62, s63, s64, s65, s67, s68, s72, s73, s74, s75, s76, s78, s82, s83, s84, s85, s86, s87] <;> simp <;> abel

def C : Fin 14 → Fin 14 → Fin 14 → ℝ := ![
  ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, -1, 0, 0, 0, -1, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]],
  ![![0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, -2, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![-1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, -1, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0], ![0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0]],
  ![![0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0], ![0, -2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![-1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0]],
  ![![0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1], ![0, -2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![-1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]],
  ![![0, 0, 0, -1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0], ![0, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![-1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]],
  ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, -2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, -1, 0, 0, 0, -1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![-1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]],
  ![![0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0], ![0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0]],
  ![![0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, -2, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0]],
  ![![0, 0, 0, -1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0], ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, -2, 0, 0, 0, 0, 2, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0]],
  ![![0, 0, 0, 0, -1, 0, 0, 0, -1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1], ![0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, -2, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0]],
  ![![0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, -1, 0, 0, 0, -1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0], ![0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0]],
  ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -2], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0]],
  ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], ![0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 0, 0]],
  ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0], ![0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]]

lemma two (a b : Fin 8) : single a b (2:ℝ) = (2:ℝ) • single a b 1 := by
  rw [smul_single, smul_eq_mul, mul_one]
lemma mtwo (a b : Fin 8) : single a b (-2:ℝ) = (-2:ℝ) • single a b 1 := by
  rw [smul_single, smul_eq_mul, mul_one]

set_option maxHeartbeats 8000000 in
lemma hbr : ∀ i j, i < j → ⁅b' i, b' j⁆ = ∑ k, C i j k • b' k := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> (try exact absurd hij (by decide)) <;>
  (try simp only [Fin.reduceFinMk, Fin.zero_eta, Fin.mk_one] at *
   simp only [C, b', Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.cons_val_one, Matrix.head_cons, Fin.succ_zero_eq_one, Fin.succ_one_eq_two, Matrix.cons_val, zero_smul, add_zero, zero_add, Ring.lie_def]
   simp only [E, add_mul, mul_add, sub_mul, mul_sub, single_mul_single_same, mul_one, neg_mul, mul_neg]
   try simp (disch := decide) only [single_mul_single_of_ne, sub_zero, zero_sub, add_zero, zero_add, neg_zero]) <;> (try simp only [two, mtwo]) <;> module

set_option maxHeartbeats 8000000 in
lemma lin : LinearIndependent ℝ b' := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  have e : ∀ r c, (∑ i, g i • b' i) r c = 0 := fun r c => by rw [hg]; rfl
  have h0 := e 1 2
  have h1 := e 1 3
  have h2 := e 1 4
  have h3 := e 1 5
  have h4 := e 1 6
  have h5 := e 1 7
  have h6 := e 2 3
  have h7 := e 2 4
  have h8 := e 2 5
  have h9 := e 2 6
  have h10 := e 2 7
  have h11 := e 4 5
  have h12 := e 4 6
  have h13 := e 4 7
  simp [b', E, Fin.sum_univ_succ, Matrix.single_apply] at h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13
  intro k; fin_cases k <;> simp <;> linarith

lemma mem : ∀ i j, ⁅b' i, b' j⁆ ∈ Submodule.span ℝ (Set.range b') := by
  have h1 : ∀ i j, i < j → ⁅b' i, b' j⁆ ∈ Submodule.span ℝ (Set.range b') := by
    intro i j hij; rw [hbr i j hij]
    exact Submodule.sum_mem _ (fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩))
  intro i j
  rcases lt_trichotomy i j with h | rfl | h
  · exact h1 i j h
  · rw [lie_self]; exact Submodule.zero_mem _
  · rw [← lie_skew]; exact Submodule.neg_mem _ (h1 j i h)

end G2Hcompact

/-- The 14 literal compact g2 generators are linearly independent and span their
Lie-generated algebra over the reals. Source: PDF pp. 12-13, Bg2.
In particular, closure of the linear span is asserted, not assumed. -/
theorem solution : isBasisFor compactG2 bG2 := by
  unfold isBasisFor compactG2
  rw [G2Hcompact.heq]
  exact ⟨G2Hcompact.lin, G2Gen.span_eq_lieSpan _ G2Hcompact.mem⟩


