-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Gap48.P15.compactG2_b1_rank_cartan
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung
-- created : 2026-10-22T00:59:18.300716+00:00
-- url     : https://prove2.me/submissions/3bea8118-224a-4cb0-af2a-5a13d3ca293a

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


namespace RkFW
open LieAlgebra LieSubalgebra Module Polynomial

variable {L : Type*} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]

lemma le_rank (r : ℕ) (h : ∀ x : L, r ≤ (LieAlgebra.ad ℝ L x).charpoly.natTrailingDegree) :
    r ≤ LieAlgebra.rank ℝ L := by
  obtain ⟨x, hx⟩ := LieAlgebra.exists_isRegular ℝ L
  rw [← (LieAlgebra.isRegular_iff_natTrailingDegree_charpoly_eq_rank ℝ x).1 hx]
  exact h x

lemma rank_eq (r : ℕ) (h : ∀ x : L, r ≤ (LieAlgebra.ad ℝ L x).charpoly.natTrailingDegree)
    (x0 : L) (h0 : finrank ℝ (engel ℝ x0) ≤ r) : LieAlgebra.rank ℝ L = r :=
  le_antisymm ((LieAlgebra.rank_le_finrank_engel ℝ x0).trans h0) (le_rank r h)

lemma cartan_engel (x : L) (hx : finrank ℝ (engel ℝ x) ≤ LieAlgebra.rank ℝ L) :
    (engel ℝ x).IsCartanSubalgebra := by
  have h : finrank ℝ L ≤ Cardinal.mk ℝ :=
    (Cardinal.natCast_le_aleph0).trans (Cardinal.infinite_iff.mp inferInstance)
  have hreg : finrank ℝ (engel ℝ x) = LieAlgebra.rank ℝ L :=
    le_antisymm hx (LieAlgebra.rank_le_finrank_engel ℝ x)
  refine ⟨?_, normalizer_engel _ _⟩
  apply isNilpotent_of_forall_le_engel
  intro y hy
  set Ex : {engel ℝ z | z ∈ engel ℝ x} := ⟨engel ℝ x, x, self_mem_engel _ _, rfl⟩
  suffices IsBot Ex from @this ⟨engel ℝ y, y, hy, rfl⟩
  apply LieAlgebra.engel_isBot_of_isMin h (engel ℝ x) Ex le_rfl
  rintro ⟨_, y, hy, rfl⟩ hyx
  suffices finrank ℝ (engel ℝ x) ≤ finrank ℝ (engel ℝ y) by
    suffices engel ℝ y = engel ℝ x from this.ge
    apply LieSubalgebra.toSubmodule_injective
    exact Submodule.eq_of_le_of_finrank_le hyx this
  rw [hreg]
  apply LieAlgebra.rank_le_finrank_engel

/-- engel x0 ≤ H if ad x0 reflects membership in H. -/
lemma engel_le (x0 : L) (H : Submodule ℝ L) (hH : ∀ y, ⁅x0, y⁆ ∈ H → y ∈ H) :
    (engel ℝ x0).toSubmodule ≤ H := by
  intro y hy
  rw [LieSubalgebra.mem_toSubmodule, mem_engel_iff] at hy
  obtain ⟨n, hn⟩ := hy
  induction n generalizing y with
  | zero => simp at hn; rw [hn]; exact H.zero_mem
  | succ n ih =>
    apply hH
    apply ih
    rw [pow_succ, Module.End.mul_apply] at hn
    exact hn

end RkFW

namespace RkFW
open Polynomial

lemma neg_cp {n : Type*} [Fintype n] [DecidableEq n] (M : Matrix n n ℝ) :
    (-M).charpoly = (-1) ^ Fintype.card n * M.charpoly.comp (-X) := by
  have h : M.charpoly.comp (-X) = (-1) ^ Fintype.card n * (-M).charpoly := by
    rw [Matrix.charpoly, ← Polynomial.coe_compRingHom_apply, RingHom.map_det]
    have : (Polynomial.compRingHom (-X : ℝ[X])).mapMatrix M.charmatrix = -((-M).charmatrix) := by
      ext i j
      by_cases hij : i = j
      · subst hij; simp; ring
      · simp [hij]
    rw [this, Matrix.det_neg, Matrix.charpoly]
  rw [h, ← mul_assoc, ← pow_add, ← two_mul, pow_mul]; simp

lemma coeff_one_comp_neg (p : ℝ[X]) : (p.comp (-X)).coeff 1 = - p.coeff 1 := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp [add_comp, hp, hq]; ring
  | monomial k a =>
    rw [← C_mul_X_pow_eq_monomial]
    have : ((C a * X ^ k).comp (-X)) = C (a * (-1) ^ k) * X ^ k := by
      rw [mul_comp, C_comp, X_pow_comp, neg_pow, C_mul, C_pow, C_neg, C_1]; ring
    rw [this, coeff_C_mul_X_pow, coeff_C_mul_X_pow]
    split_ifs with hk
    · subst hk; ring
    · simp

lemma even_cp {N : ℕ} (M G : Matrix (Fin N) (Fin N) ℝ) (hG : IsUnit G.det)
    (h : M.transpose * G = -(G * M)) (hN : Even N) : M.charpoly.coeff 1 = 0 := by
  have h1 : M.transpose = G * (-M) * G⁻¹ := by
    rw [Matrix.mul_neg, ← h, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hG, Matrix.mul_one]
  have h2 : M.charpoly = (-M).charpoly := by
    rw [← Matrix.charpoly_transpose, h1]
    have := Matrix.charpoly_units_conj (Matrix.nonsingInvUnit G hG) (-M)
    exact this
  have h3 := congrArg (fun p => p.coeff 1) h2
  simp only [neg_cp, Fintype.card_fin, hN.neg_one_pow, one_mul, coeff_one_comp_neg] at h3
  linarith

end RkFW

namespace RkFW
open Polynomial Module LieAlgebra

attribute [local instance 100] LieRing.ofAssociativeRing

variable {t : ℕ} (L : LieSubalgebra ℝ (Matrix (Fin t) (Fin t) ℝ))

noncomputable def trB : LinearMap.BilinForm ℝ L :=
  LinearMap.mk₂ ℝ (fun y z => Matrix.trace ((y : Matrix (Fin t) (Fin t) ℝ) * (z : Matrix (Fin t) (Fin t) ℝ)))
    (by intros; simp [add_mul, Matrix.trace_add])
    (by intros; simp [Matrix.trace_smul])
    (by intros; simp [mul_add, Matrix.trace_add])
    (by intros; simp [Matrix.trace_smul])

lemma trB_apply (y z : L) : trB L y z = Matrix.trace ((y : Matrix (Fin t) (Fin t) ℝ) * (z : Matrix (Fin t) (Fin t) ℝ)) := rfl

lemma tr_self_transpose (y : Matrix (Fin t) (Fin t) ℝ) (h : Matrix.trace (y * y.transpose) = 0) :
    y = 0 := by
  have h2 : ∀ i, ∀ j, y i j = 0 := by
    have hs : ∑ i, ∑ j, y i j * y i j = 0 := by
      rw [← h]; simp [Matrix.trace, Matrix.mul_apply]
    intro i j
    have hnn : ∀ i, 0 ≤ ∑ j, y i j * y i j := fun i =>
      Finset.sum_nonneg (fun j _ => mul_self_nonneg _)
    have hi := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => hnn i)).1 hs i (Finset.mem_univ _)
    have hj := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => mul_self_nonneg (y i j))).1 hi j
      (Finset.mem_univ _)
    exact mul_self_eq_zero.1 hj
  ext i j; exact h2 i j

lemma trB_nondeg (hT : ∀ y ∈ L, y.transpose ∈ L) : (trB L).Nondegenerate := by
  refine ⟨fun y hy => ?_, fun y hy => ?_⟩
  · have := hy ⟨(y : Matrix (Fin t) (Fin t) ℝ).transpose, hT _ y.2⟩
    rw [trB_apply] at this
    exact Subtype.ext (tr_self_transpose _ this)
  · have := hy ⟨(y : Matrix (Fin t) (Fin t) ℝ).transpose, hT _ y.2⟩
    rw [trB_apply, Matrix.trace_mul_comm] at this
    exact Subtype.ext (tr_self_transpose _ this)

lemma parity (hT : ∀ y ∈ L, y.transpose ∈ L) (hN : Even (finrank ℝ L)) (hpos : 0 < finrank ℝ L)
    (x : L) : 2 ≤ (ad ℝ L x).charpoly.natTrailingDegree := by
  set b := Module.finBasis ℝ L
  set M := LinearMap.toMatrix b b (ad ℝ L x)
  set G := LinearMap.BilinForm.toMatrix b (trB L)
  have hinv : (trB L).compLeft (ad ℝ L x) = -((trB L).compRight (ad ℝ L x)) := by
    ext y z
    simp only [LinearMap.BilinForm.compLeft_apply, LinearMap.BilinForm.compRight_apply,
      LinearMap.neg_apply, trB_apply, LieAlgebra.ad_apply, LieSubalgebra.coe_bracket, Ring.lie_def]
    rw [sub_mul, mul_sub, Matrix.trace_sub, Matrix.trace_sub, Matrix.mul_assoc,
      Matrix.trace_mul_comm (x : Matrix (Fin t) (Fin t) ℝ), Matrix.mul_assoc]
    simp only [Matrix.mul_assoc]; ring
  have h : M.transpose * G = -(G * M) := by
    rw [← LinearMap.BilinForm.toMatrix_compLeft, ← LinearMap.BilinForm.toMatrix_compRight, hinv]
    exact map_neg (LinearMap.BilinForm.toMatrix b) _
  have hG : IsUnit G.det :=
    isUnit_iff_ne_zero.2 ((LinearMap.BilinForm.nondegenerate_iff_det_ne_zero b).1 (trB_nondeg L hT))
  have c1 : M.charpoly.coeff 1 = 0 := even_cp M G hG h hN
  have hdet : M.det = 0 := by
    by_cases hx : x = 0
    · have hM0 : M = 0 := by simp [M, hx]
      have hne : Nonempty (Fin (finrank ℝ L)) := ⟨⟨0, hpos⟩⟩
      rw [hM0]; exact Matrix.det_zero
    · rw [← Matrix.exists_mulVec_eq_zero_iff]
      refine ⟨b.repr x, by simpa using hx, ?_⟩
      rw [LinearMap.toMatrix_mulVec_repr]; simp
  have c0 : M.charpoly.coeff 0 = 0 := by
    have := Matrix.det_eq_sign_charpoly_coeff M
    rw [hdet] at this
    have hs : ((-1 : ℝ) ^ Fintype.card (Fin (finrank ℝ L))) ≠ 0 := pow_ne_zero _ (by norm_num)
    exact (mul_eq_zero.1 this.symm).resolve_left hs
  rw [← LinearMap.charpoly_toMatrix (ad ℝ L x) b]
  apply Polynomial.le_natTrailingDegree (Matrix.charpoly_monic M).ne_zero
  intro m hm
  interval_cases m
  · exact c0
  · exact c1

end RkFW

namespace RkFW
open Module LieAlgebra LieSubalgebra

attribute [local instance 100] LieRing.ofAssociativeRing

lemma finish {t m : ℕ} (L : LieSubalgebra ℝ (Matrix (Fin t) (Fin t) ℝ))
    (v : Fin m → Matrix (Fin t) (Fin t) ℝ)
    (hlow : ∀ x : L, m ≤ (LieAlgebra.ad ℝ L x).charpoly.natTrailingDegree)
    (x0 : L) (hvL : ∀ i, v i ∈ L) (hcomm : ∀ i, ⁅(x0 : Matrix (Fin t) (Fin t) ℝ), v i⁆ = 0)
    (hlin : LinearIndependent ℝ v)
    (hrefl : ∀ y ∈ L, ⁅(x0 : Matrix (Fin t) (Fin t) ℝ), y⁆ ∈ Submodule.span ℝ (Set.range v) →
      y ∈ Submodule.span ℝ (Set.range v)) :
    LieAlgebra.rank ℝ L = m ∧
    ∃ H : LieSubalgebra ℝ L, H.IsCartanSubalgebra ∧ LinearIndependent ℝ v ∧
      Submodule.span ℝ (Set.range v) = H.toSubmodule.map L.toSubmodule.subtype := by
  set S := Submodule.span ℝ (Set.range v)
  have he : (engel ℝ x0).toSubmodule ≤ S.comap L.toSubmodule.subtype := by
    apply engel_le x0
    intro y hy
    rw [Submodule.mem_comap] at hy ⊢
    exact hrefl y y.2 hy
  have hmap : (engel ℝ x0).toSubmodule.map L.toSubmodule.subtype = S := by
    apply le_antisymm (Submodule.map_le_iff_le_comap.2 he)
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    refine ⟨⟨v i, hvL i⟩, ?_, rfl⟩
    show _ ∈ engel ℝ x0
    rw [mem_engel_iff]
    refine ⟨1, ?_⟩
    rw [pow_one, LieAlgebra.ad_apply]
    exact Subtype.ext (hcomm i)
  have hfin : finrank ℝ (engel ℝ x0) = m := by
    have h1 := LinearEquiv.finrank_eq (Submodule.equivMapOfInjective L.toSubmodule.subtype
      Subtype.val_injective (engel ℝ x0).toSubmodule)
    have h2 : finrank ℝ S = m := by
      rw [finrank_span_eq_card hlin, Fintype.card_fin]
    rw [hmap] at h1
    exact h1.trans h2
  have hrank : LieAlgebra.rank ℝ L = m := rank_eq m hlow x0 hfin.le
  exact ⟨hrank, engel ℝ x0, cartan_engel x0 (by rw [hrank, hfin]), hlin, hmap.symm⟩

end RkFW


namespace G2R_c_b1

open Module Matrix G2Hcompact

abbrev LL := compactG2

lemma hL : LL.toSubmodule = Submodule.span ℝ (Set.range b') := by
  show (compactG2).toSubmodule = _
  unfold compactG2; rw [heq]; exact (G2Gen.span_eq_lieSpan _ mem).symm

lemma memL (y : Matrix (Fin 8) (Fin 8) ℝ) : y ∈ LL ↔ y ∈ Submodule.span ℝ (Set.range b') := by
  rw [← hL]; rfl

lemma fr : finrank ℝ LL = 14 := by
  have : finrank ℝ LL.toSubmodule = 14 := by rw [hL, finrank_span_eq_card lin, Fintype.card_fin]
  exact this

def sg : Fin 14 → ℝ := ![(-1:ℝ), (-1:ℝ), (-1:ℝ), (-1:ℝ), (-1:ℝ), (-1:ℝ), (-1:ℝ), (-1:ℝ), (-1:ℝ), (-1:ℝ), (-1:ℝ), (-1:ℝ), (-1:ℝ), (-1:ℝ)]

lemma trb (k : Fin 14) : (b' k).transpose = sg k • b' k := by
  fin_cases k <;> simp [b', sg, E, Matrix.transpose_sub, Matrix.transpose_add, Matrix.transpose_single] <;> abel

lemma hT : ∀ y ∈ LL, y.transpose ∈ LL := by
  intro y hy
  rw [memL] at hy ⊢
  induction hy using Submodule.span_induction with
  | mem x hx => obtain ⟨k, rfl⟩ := hx; rw [trb]; exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
  | zero => simp
  | add a b _ _ ha hb => rw [Matrix.transpose_add]; exact Submodule.add_mem _ ha hb
  | smul r a _ ha => rw [Matrix.transpose_smul]; exact Submodule.smul_mem _ r ha

def P0 : Fin 14 → ℝ := ![(1:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ)]

def P1 : Fin 14 → ℝ := ![(0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (1:ℝ)]

noncomputable def V0 : Matrix (Fin 8) (Fin 8) ℝ := b' 0

noncomputable def V1 : Matrix (Fin 8) (Fin 8) ℝ := b' 13

lemma v0eq : V0 = ∑ k, P0 k • b' k := by
  simp [V0, P0, Fin.sum_univ_succ]; try module

lemma v1eq : V1 = ∑ k, P1 k • b' k := by
  simp [V1, P1, Fin.sum_univ_succ]; try module

noncomputable def X0 : Matrix (Fin 8) (Fin 8) ℝ := (1:ℝ) • V0 + (2:ℝ) • V1

lemma spmem (c : Fin 14 → ℝ) : ∑ k, c k • b' k ∈ Submodule.span ℝ (Set.range b') :=
  Submodule.sum_mem _ (fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩))

lemma X0mem : X0 ∈ LL := by
  rw [memL, X0]; exact Submodule.add_mem _ (Submodule.smul_mem _ _ (by rw [v0eq]; exact spmem _)) (Submodule.smul_mem _ _ (by rw [v1eq]; exact spmem _))

lemma X0e : X0 = (1:ℝ) • E 1 2 + (-1:ℝ) • E 2 1 + (2:ℝ) • E 4 7 + (3:ℝ) • E 5 6 + (-3:ℝ) • E 6 5 + (-2:ℝ) • E 7 4 := by
  simp only [X0, V0, V1, b', E, Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val, Fin.reduceFinMk]; module

def A : Fin 14 → Fin 14 → ℝ := ![
  ![(0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ)],
  ![(0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (-1:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (-2:ℝ), (0:ℝ), (0:ℝ)],
  ![(0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (-2:ℝ), (0:ℝ), (-1:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ)],
  ![(0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (-3:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (-1:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ)],
  ![(0:ℝ), (0:ℝ), (0:ℝ), (3:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (-1:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ)],
  ![(0:ℝ), (0:ℝ), (2:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (-1:ℝ), (0:ℝ), (0:ℝ), (0:ℝ)],
  ![(0:ℝ), (1:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (-2:ℝ), (0:ℝ)],
  ![(0:ℝ), (0:ℝ), (1:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (-2:ℝ), (0:ℝ), (0:ℝ), (0:ℝ)],
  ![(0:ℝ), (0:ℝ), (0:ℝ), (1:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (-3:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ)],
  ![(0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (1:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (3:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ)],
  ![(0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (1:ℝ), (0:ℝ), (2:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ)],
  ![(0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (-5:ℝ), (0:ℝ)],
  ![(0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (5:ℝ), (0:ℝ), (0:ℝ)],
  ![(0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ)]]

set_option maxHeartbeats 8000000 in
lemma brk : ∀ k, ⁅X0, b' k⁆ = ∑ l, A k l • b' l := by
  intro k
  rw [X0e]
  fin_cases k <;>
  (simp only [A, b', Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.cons_val_one, Matrix.head_cons, Fin.succ_zero_eq_one, Fin.succ_one_eq_two, Matrix.cons_val, zero_smul, add_zero, zero_add, Fin.reduceFinMk, Fin.zero_eta, Fin.mk_one]
   simp only [Ring.lie_def]
   simp only [E, add_mul, mul_add, sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm, single_mul_single_same, mul_one, neg_mul, mul_neg]
   try simp (disch := decide) only [single_mul_single_of_ne, sub_zero, zero_sub, add_zero, zero_add, neg_zero, smul_zero]) <;> (try simp only [two, mtwo]) <;> module

set_option maxHeartbeats 8000000 in
lemma comm : ⁅X0, V0⁆ = 0 ∧ ⁅X0, V1⁆ = 0 := by
  rw [X0e]
  constructor <;>
  (simp only [V0, V1, b', Fin.reduceFinMk, Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val]
   simp only [Ring.lie_def]
   simp only [E, add_mul, mul_add, sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm, single_mul_single_same, mul_one, neg_mul, mul_neg]
   try simp (disch := decide) only [single_mul_single_of_ne, sub_zero, zero_sub, add_zero, zero_add, neg_zero, smul_zero]) <;> (try simp only [two, mtwo]) <;> module

lemma coef (c d : Fin 14 → ℝ) (h : ∑ k, c k • b' k = ∑ k, d k • b' k) : ∀ k, c k = d k := by
  have := Fintype.linearIndependent_iff.1 lin (c - d)
    (by simp only [Pi.sub_apply, sub_smul, Finset.sum_sub_distrib, h, sub_self])
  intro k; exact sub_eq_zero.1 (this k)

lemma comb (s u : ℝ) : s • V0 + u • V1 = ∑ k, (s * P0 k + u * P1 k) • b' k := by
  rw [v0eq, v1eq, Finset.smul_sum, Finset.smul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [smul_smul, smul_smul, add_smul]

lemma brsum (g : Fin 14 → ℝ) : ⁅X0, ∑ k, g k • b' k⁆ = ∑ l, (∑ k, g k * A k l) • b' l := by
  rw [lie_sum]
  simp_rw [lie_smul, brk, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  simp_rw [Finset.sum_smul]

lemma hS : Set.range ![V0, V1] = {V0, V1} := by
  rw [Matrix.range_cons, Matrix.range_cons, Matrix.range_empty, Set.union_empty]; rfl

set_option maxHeartbeats 4000000 in
lemma main : LieAlgebra.rank ℝ LL = 2 ∧
    ∃ H : LieSubalgebra ℝ LL, H.IsCartanSubalgebra ∧ LinearIndependent ℝ ![V0, V1] ∧
      Submodule.span ℝ (Set.range ![V0, V1]) = H.toSubmodule.map LL.toSubmodule.subtype := by
  apply RkFW.finish LL ![V0, V1] _ ⟨X0, X0mem⟩
  · intro i; fin_cases i
    · show V0 ∈ LL; rw [memL, v0eq]; exact spmem _
    · show V1 ∈ LL; rw [memL, v1eq]; exact spmem _
  · intro i; fin_cases i
    · exact comm.1
    · exact comm.2
  · rw [LinearIndependent.pair_iff]
    intro s u h
    rw [comb] at h
    have h0 := coef _ 0 (by rw [h]; simp)
    have e1 := h0 0; have e2 := h0 13
    simp [P0, P1] at e1 e2
    constructor <;> linarith
  · intro y hy hb
    rw [memL, Submodule.mem_span_range_iff_exists_fun] at hy
    obtain ⟨g, rfl⟩ := hy
    rw [hS, Submodule.mem_span_pair] at hb ⊢
    obtain ⟨s, u, h⟩ := hb
    rw [comb, brsum] at h
    have hc := coef _ _ h
    have e0 := hc 0; have e1 := hc 1; have e2 := hc 2; have e3 := hc 3; have e4 := hc 4
    have e5 := hc 5; have e6 := hc 6; have e7 := hc 7; have e8 := hc 8; have e9 := hc 9
    have e10 := hc 10; have e11 := hc 11; have e12 := hc 12; have e13 := hc 13
    simp only [P0, P1, A, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.cons_val_one, Matrix.head_cons, Fin.succ_zero_eq_one, Fin.succ_one_eq_two, Matrix.cons_val, Fin.reduceFinMk, Fin.zero_eta, Fin.mk_one, Fin.reduceSucc] at e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13
    norm_num at e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13
    refine ⟨g 0, g 13, ?_⟩
    rw [comb]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    congr 1
    fin_cases k <;> simp [P0, P1] <;> linarith
  · exact RkFW.parity LL hT (by rw [fr]; decide) (by rw [fr]; norm_num)
end G2R_c_b1


/-- Compact g2 has rank 2 and Cartan basis [b1,b14], retaining the seed b1.
Source: PDF p. 14, first RankOfg2 output. -/
theorem solution :
    LieAlgebra.rank ℝ compactG2 = 2 ∧
    isCartanBasisFor compactG2 ![bG2 0, bG2 13] := by
  have hv : (![bG2 0, bG2 13] : Fin 2 → Matrix (Fin 8) (Fin 8) ℝ) = ![G2R_c_b1.V0, G2R_c_b1.V1] := by
    rw [G2Hcompact.heq]; funext i; fin_cases i <;> simp [G2R_c_b1.V0, G2R_c_b1.V1] <;> module
  rw [hv]; exact G2R_c_b1.main


