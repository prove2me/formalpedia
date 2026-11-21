-- Prove2me | solution 1 for RandomSizeStable.Stability.RankCutCert.cells_near_zero
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-20T20:13:51.735223+00:00
-- url     : https://prove2.me/submissions/eaf2b099-aaf1-4e8a-a76c-7598f60cd1b4

import Mathlib
import Definitions.Def_RandomSizeStable_Stability_RankCutCert
import Definitions.Def_RandomSizeStable_Stability_RankCutCertEngine
import Theorems.Thm_RandomSizeStable_Stability_RankCutCert_cell0Check_ok

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option Elab.async false

namespace RandomSizeStable.Stability.RankCutCert.Pieces.cells_near_zero

open RandomSizeStable.Stability.RankCutCert RandomSizeStable.Stability.RankCutCert.Dev


theorem run_append (leaf : Box → Bool) :
    ∀ (n : Nat) (B : Box) (c rest r : List Nat), run leaf n B c = some r →
      run leaf n B (c ++ rest) = some (r ++ rest) := by
  intro n
  induction n with
  | zero => intro B c rest r h; simp [run] at h
  | succ n ih =>
    intro B c rest r h
    match c with
    | [] => simp [run] at h
    | 0 :: c' =>
      rw [List.cons_append]
      simp only [run] at h ⊢
      by_cases hl : leaf B = true
      · simp only [hl, if_true, Option.some.injEq] at h ⊢; subst h; rfl
      · simp [hl] at h
    | (i + 1) :: c' =>
      rw [List.cons_append]
      simp only [run] at h ⊢
      by_cases he : evenH B i = true
      · simp only [he, if_true] at h ⊢
        cases h1 : run leaf n (splitL B i) c' with
        | none => simp [h1] at h
        | some r1 =>
          simp only [h1] at h
          rw [ih _ _ _ _ h1]
          exact ih _ _ _ _ h
      · simp [he] at h

theorem run_node (leaf : Box → Bool) (n : Nat) (B : Box) (i : Nat) (cL cR : List Nat)
    (he : evenH B i = true) (hL : run leaf n (splitL B i) cL = some [])
    (hR : run leaf n (splitR B i) cR = some []) :
    run leaf (n + 1) B ((i + 1) :: (cL ++ cR)) = some [] := by
  simp only [run, he, if_true]
  rw [show run leaf n (splitL B i) (cL ++ cR) = some ([] ++ cR) from run_append leaf n _ cL cR [] hL]
  simpa using hR

theorem runAll_of_run (leaf : Box → Bool) (B : Box) (c : List Nat) (h : run leaf 64 B c = some []) :
    runAll leaf B c = true := by
  simp [runAll, h]


def cdC : CellData where
  pm := ⟨18014398509481984, 0⟩
  ph := ⟨18014398509481984, 0⟩
  l0 := ⟨⟨200, 0⟩, 1⟩
  l1 := ⟨⟨200, 0⟩, 1⟩
  l2 := ⟨⟨0, 0⟩, 1⟩
  t0 := ![⟨⟨87682280743, 0⟩, 444296519⟩, ⟨⟨32954716717, 0⟩, 198979068⟩, ⟨⟨128047802483, 0⟩, 970322315⟩, ⟨⟨94336841669, 0⟩, 988603519⟩, ⟨⟨6922288940, 0⟩, 101054439⟩, ⟨⟨34506801923, 0⟩, 759678632⟩, ⟨⟨1025779682, 0⟩, 65695225⟩, ⟨⟨0, 0⟩, 1⟩, ⟨⟨0, 0⟩, 1⟩]
  t1 := ![⟨⟨200, 0⟩, 1⟩, ⟨⟨200, 0⟩, 1⟩, ⟨⟨200, 0⟩, 1⟩, ⟨⟨200, 0⟩, 1⟩, ⟨⟨200, 0⟩, 1⟩, ⟨⟨200, 0⟩, 1⟩, ⟨⟨200, 0⟩, 1⟩, ⟨⟨200, 0⟩, 1⟩, ⟨⟨200, 0⟩, 1⟩]
  tree1 := []
  tree2 := []

def t1_b1 : Box := root1 cdC
def t1_k2 : List Nat := [0]
theorem t1_s3 : run (leaf1 cdC) 64 t1_b1 t1_k2 = some [] := by decide +kernel
def t2_b1 : Box := root2 cdC
theorem t2_e2 : evenH t2_b1 2 = true := by decide +kernel
def t2_b3 : Box := splitL t2_b1 2
def t2_k4 : List Nat := [3,0,3,0,3,0,3,0,3,0,3,3,0,3,3,2,0,0,2,0,0,1,0,0,1,0,1,0,1,0,0]
theorem t2_s5 : run (leafZ2 cdC) 63 t2_b3 t2_k4 = some [] := by decide +kernel
def t2_b6 : Box := splitR t2_b1 2
theorem t2_e7 : evenH t2_b6 2 = true := by decide +kernel
def t2_b8 : Box := splitL t2_b6 2
theorem t2_e9 : evenH t2_b8 2 = true := by decide +kernel
def t2_b10 : Box := splitL t2_b8 2
theorem t2_e11 : evenH t2_b10 2 = true := by decide +kernel
def t2_b12 : Box := splitL t2_b10 2
def t2_k13 : List Nat := [1,0,1,0,1,0,1,0,1,0,1,0,1,0,1,0,1,2,1,0,3,0,0,0,2,3,0,1,0,2,3,0,0,0,3,0,0]
theorem t2_s14 : run (leafZ2 cdC) 60 t2_b12 t2_k13 = some [] := by decide +kernel
def t2_b15 : Box := splitR t2_b10 2
theorem t2_e16 : evenH t2_b15 2 = true := by decide +kernel
def t2_b17 : Box := splitL t2_b15 2
theorem t2_e18 : evenH t2_b17 2 = true := by decide +kernel
def t2_b19 : Box := splitL t2_b17 2
theorem t2_e20 : evenH t2_b19 2 = true := by decide +kernel
def t2_b21 : Box := splitL t2_b19 2
theorem t2_e22 : evenH t2_b21 2 = true := by decide +kernel
def t2_b23 : Box := splitL t2_b21 2
def t2_k24 : List Nat := [1,0,1,0,1,0,1,0,1,0,1,0,1,0,0]
theorem t2_s25 : run (leafZ2 cdC) 56 t2_b23 t2_k24 = some [] := by decide +kernel
def t2_b26 : Box := splitR t2_b21 2
theorem t2_e27 : evenH t2_b26 2 = true := by decide +kernel
def t2_b28 : Box := splitL t2_b26 2
theorem t2_e29 : evenH t2_b28 2 = true := by decide +kernel
def t2_b30 : Box := splitL t2_b28 2
def t2_k31 : List Nat := [3,1,0,1,0,1,0,1,0,1,0,1,0,0,2,1,0,1,0,1,0,1,0,1,0,1,0,0,3,1,0,0,2,1,0,0,3,2,0,0,0]
theorem t2_s32 : run (leafZ2 cdC) 54 t2_b30 t2_k31 = some [] := by decide +kernel
def t2_b33 : Box := splitR t2_b28 2
theorem t2_e34 : evenH t2_b33 2 = true := by decide +kernel
def t2_b35 : Box := splitL t2_b33 2
theorem t2_e36 : evenH t2_b35 1 = true := by decide +kernel
def t2_b37 : Box := splitL t2_b35 1
def t2_k38 : List Nat := [3,2,1,0,1,0,1,0,1,0,1,0,0,3,1,0,0,2,1,0,0,3,0,2,0,0,2,3,1,0,1,0,1,0,1,0,1,0,1,0,0,2,1,0,1,0,1,0,1,0,1,0,0,3,1,0,0,2,1,0,0,3,2,0,0,0,3,2,3,1,0,0,2,0,0,3,2,0,0,0,2,3,2,0,0,2,0,0,0]
theorem t2_s39 : run (leafZ2 cdC) 52 t2_b37 t2_k38 = some [] := by decide +kernel
def t2_b40 : Box := splitR t2_b35 1
def t2_k41 : List Nat := [3,2,3,2,0,0,2,0,0,3,0,0,1,0,0]
theorem t2_s42 : run (leafZ2 cdC) 52 t2_b40 t2_k41 = some [] := by decide +kernel
def t2_k43 : List Nat := 2 :: (t2_k38 ++ t2_k41)
theorem t2_n44 : run (leafZ2 cdC) 53 t2_b35 t2_k43 = some [] :=
  run_node (leafZ2 cdC) 52 t2_b35 1 t2_k38 t2_k41 t2_e36 t2_s39 t2_s42
def t2_b45 : Box := splitR t2_b33 2
theorem t2_e46 : evenH t2_b45 1 = true := by decide +kernel
def t2_b47 : Box := splitL t2_b45 1
theorem t2_e48 : evenH t2_b47 2 = true := by decide +kernel
def t2_b49 : Box := splitL t2_b47 2
theorem t2_e50 : evenH t2_b49 1 = true := by decide +kernel
def t2_b51 : Box := splitL t2_b49 1
theorem t2_e52 : evenH t2_b51 2 = true := by decide +kernel
def t2_b53 : Box := splitL t2_b51 2
def t2_k54 : List Nat := [2,3,1,0,1,0,1,0,1,0,1,0,1,0,0,2,3,1,0,1,0,1,0,1,0,1,0,0,2,1,0,1,0,1,0,1,0,1,0,0,3,1,0,0,2,1,0,0,0,3,2,3,1,0,0,2,0,0,0,2,3,2,0,0,2,0,0,0,3,2,3,2,0,0,2,0,0,3,0,0,2,3,2,0,0,0,0]
theorem t2_s55 : run (leafZ2 cdC) 49 t2_b53 t2_k54 = some [] := by decide +kernel
def t2_b56 : Box := splitR t2_b51 2
theorem t2_e57 : evenH t2_b56 1 = true := by decide +kernel
def t2_b58 : Box := splitL t2_b56 1
theorem t2_e59 : evenH t2_b58 2 = true := by decide +kernel
def t2_b60 : Box := splitL t2_b58 2
theorem t2_e61 : evenH t2_b60 1 = true := by decide +kernel
def t2_b62 : Box := splitL t2_b60 1
theorem t2_e63 : evenH t2_b62 2 = true := by decide +kernel
def t2_b64 : Box := splitL t2_b62 2
def t2_k65 : List Nat := [2,3,1,0,1,0,1,0,1,0,1,0,1,0,0,2,1,0,1,0,1,0,1,0,1,0,1,0,0,3,2,1,0,0,0,2,3,2,0,0,2,0,0,3,0,0,3,2,3,2,0,0,2,0,0,3,0,0,2,3,2,0,0,0,0]
theorem t2_s66 : run (leafZ2 cdC) 45 t2_b64 t2_k65 = some [] := by decide +kernel
def t2_b67 : Box := splitR t2_b62 2
theorem t2_e68 : evenH t2_b67 1 = true := by decide +kernel
def t2_b69 : Box := splitL t2_b67 1
theorem t2_e70 : evenH t2_b69 2 = true := by decide +kernel
def t2_b71 : Box := splitL t2_b69 2
theorem t2_e72 : evenH t2_b71 1 = true := by decide +kernel
def t2_b73 : Box := splitL t2_b71 1
theorem t2_e74 : evenH t2_b73 2 = true := by decide +kernel
def t2_b75 : Box := splitL t2_b73 2
def t2_k76 : List Nat := [2,3,1,0,1,0,1,0,1,0,1,0,0,2,1,0,1,0,1,0,1,0,1,0,0,3,1,0,0,2,1,0,0,0,3,2,1,0,0,0,2,3,2,0,0,2,0,0,3,0,0]
theorem t2_s77 : run (leafZ2 cdC) 41 t2_b75 t2_k76 = some [] := by decide +kernel
def t2_b78 : Box := splitR t2_b73 2
theorem t2_e79 : evenH t2_b78 1 = true := by decide +kernel
def t2_b80 : Box := splitL t2_b78 1
theorem t2_e81 : evenH t2_b80 2 = true := by decide +kernel
def t2_b82 : Box := splitL t2_b80 2
def t2_k83 : List Nat := [2,3,1,0,1,0,1,0,1,0,1,0,0,2,1,0,1,0,1,0,1,0,1,0,0,3,1,0,0,2,1,0,0,0,3,2,3,1,0,0,2,0,0,0,2,3,2,0,0,2,0,0,0]
theorem t2_s84 : run (leafZ2 cdC) 39 t2_b82 t2_k83 = some [] := by decide +kernel
def t2_b85 : Box := splitR t2_b80 2
theorem t2_e86 : evenH t2_b85 1 = true := by decide +kernel
def t2_b87 : Box := splitL t2_b85 1
theorem t2_e88 : evenH t2_b87 2 = true := by decide +kernel
def t2_b89 : Box := splitL t2_b87 2
def t2_k90 : List Nat := [2,3,1,0,1,0,1,0,1,0,1,0,1,0,0,2,3,1,0,1,0,1,0,1,0,1,0,0,2,1,0,1,0,1,0,1,0,1,0,0,3,1,0,0,2,1,0,0,0,3,2,1,0,0,0,2,3,2,0,0,2,0,0,3,0,0,3,2,3,2,0,0,2,0,0,3,0,0,2,3,2,0,0,0,0]
theorem t2_s91 : run (leafZ2 cdC) 37 t2_b89 t2_k90 = some [] := by decide +kernel
def t2_b92 : Box := splitR t2_b87 2
theorem t2_e93 : evenH t2_b92 1 = true := by decide +kernel
def t2_b94 : Box := splitL t2_b92 1
theorem t2_e95 : evenH t2_b94 2 = true := by decide +kernel
def t2_b96 : Box := splitL t2_b94 2
theorem t2_e97 : evenH t2_b96 1 = true := by decide +kernel
def t2_b98 : Box := splitL t2_b96 1
theorem t2_e99 : evenH t2_b98 2 = true := by decide +kernel
def t2_b100 : Box := splitL t2_b98 2
def t2_k101 : List Nat := [2,3,1,0,1,0,1,0,1,0,1,0,0,2,1,0,1,0,1,0,1,0,1,0,0,3,2,1,0,0,0,2,3,1,0,0,2,0,0,0,3,2,3,1,0,0,2,0,0,0,2,3,2,0,0,0,0]
theorem t2_s102 : run (leafZ2 cdC) 33 t2_b100 t2_k101 = some [] := by decide +kernel
def t2_b103 : Box := splitR t2_b98 2
theorem t2_e104 : evenH t2_b103 1 = true := by decide +kernel
def t2_b105 : Box := splitL t2_b103 1
theorem t2_e106 : evenH t2_b105 2 = true := by decide +kernel
def t2_b107 : Box := splitL t2_b105 2
theorem t2_e108 : evenH t2_b107 1 = true := by decide +kernel
def t2_b109 : Box := splitL t2_b107 1
def t2_k110 : List Nat := [3,2,1,0,1,0,1,0,1,0,1,0,0,3,1,0,0,2,1,0,0,0,2,3,1,0,1,0,1,0,1,0,1,0,0,2,1,0,1,0,1,0,1,0,1,0,0,3,2,1,0,0,0,2,3,2,0,0,2,0,0,3,0,0,3,2,3,2,0,0,2,0,0,3,0,0,2,3,2,0,0,0,0]
theorem t2_s111 : run (leafZ2 cdC) 30 t2_b109 t2_k110 = some [] := by decide +kernel
def t2_b112 : Box := splitR t2_b107 1
def t2_k113 : List Nat := [3,2,3,2,0,0,2,0,0,0,0]
theorem t2_s114 : run (leafZ2 cdC) 30 t2_b112 t2_k113 = some [] := by decide +kernel
def t2_k115 : List Nat := 2 :: (t2_k110 ++ t2_k113)
theorem t2_n116 : run (leafZ2 cdC) 31 t2_b107 t2_k115 = some [] :=
  run_node (leafZ2 cdC) 30 t2_b107 1 t2_k110 t2_k113 t2_e108 t2_s111 t2_s114
def t2_b117 : Box := splitR t2_b105 2
theorem t2_e118 : evenH t2_b117 1 = true := by decide +kernel
def t2_b119 : Box := splitL t2_b117 1
theorem t2_e120 : evenH t2_b119 2 = true := by decide +kernel
def t2_b121 : Box := splitL t2_b119 2
theorem t2_e122 : evenH t2_b121 1 = true := by decide +kernel
def t2_b123 : Box := splitL t2_b121 1
theorem t2_e124 : evenH t2_b123 2 = true := by decide +kernel
def t2_b125 : Box := splitL t2_b123 2
theorem t2_e126 : evenH t2_b125 1 = true := by decide +kernel
def t2_b127 : Box := splitL t2_b125 1
theorem t2_e128 : evenH t2_b127 2 = true := by decide +kernel
def t2_b129 : Box := splitL t2_b127 2
def t2_k130 : List Nat := [2,3,1,0,1,0,1,0,1,0,0,2,1,0,1,0,1,0,1,0,0,3,1,0,0,2,1,0,0,0,3,2,3,1,0,0,2,0,0,0,2,3,2,0,0,2,0,0,0]
theorem t2_s131 : run (leafZ2 cdC) 25 t2_b129 t2_k130 = some [] := by decide +kernel
def t2_b132 : Box := splitR t2_b127 2
theorem t2_e133 : evenH t2_b132 1 = true := by decide +kernel
def t2_b134 : Box := splitL t2_b132 1
theorem t2_e135 : evenH t2_b134 2 = true := by decide +kernel
def t2_b136 : Box := splitL t2_b134 2
def t2_k137 : List Nat := [2,3,1,0,1,0,1,0,0,2,1,0,1,0,1,0,0,3,2,1,0,0,0,2,3,0,0,0,3,2,3,2,0,0,2,0,0,0,2,3,2,0,0,0,0]
theorem t2_s138 : run (leafZ2 cdC) 23 t2_b136 t2_k137 = some [] := by decide +kernel
def t2_b139 : Box := splitR t2_b134 2
def t2_k140 : List Nat := [2,3,2,3,2,1,0,1,0,0,3,2,0,0,2,0,0,2,3,2,3,1,0,0,2,1,0,0,0,3,2,0,0,2,0,0,2,3,2,3,0,0,0,2,3,0,0,0,0,3,2,3,0,0,0,0,3,2,3,2,0,0,0,0,0,0,0]
theorem t2_s141 : run (leafZ2 cdC) 23 t2_b139 t2_k140 = some [] := by decide +kernel
def t2_k142 : List Nat := 3 :: (t2_k137 ++ t2_k140)
theorem t2_n143 : run (leafZ2 cdC) 24 t2_b134 t2_k142 = some [] :=
  run_node (leafZ2 cdC) 23 t2_b134 2 t2_k137 t2_k140 t2_e135 t2_s138 t2_s141
def t2_b144 : Box := splitR t2_b132 1
def t2_k145 : List Nat := [0]
theorem t2_s146 : run (leafZ2 cdC) 24 t2_b144 t2_k145 = some [] := by decide +kernel
def t2_k147 : List Nat := 2 :: (t2_k142 ++ t2_k145)
theorem t2_n148 : run (leafZ2 cdC) 25 t2_b132 t2_k147 = some [] :=
  run_node (leafZ2 cdC) 24 t2_b132 1 t2_k142 t2_k145 t2_e133 t2_n143 t2_s146
def t2_k149 : List Nat := 3 :: (t2_k130 ++ t2_k147)
theorem t2_n150 : run (leafZ2 cdC) 26 t2_b127 t2_k149 = some [] :=
  run_node (leafZ2 cdC) 25 t2_b127 2 t2_k130 t2_k147 t2_e128 t2_s131 t2_n148
def t2_b151 : Box := splitR t2_b125 1
def t2_k152 : List Nat := [3,2,3,2,0,0,0,0,0]
theorem t2_s153 : run (leafZ2 cdC) 26 t2_b151 t2_k152 = some [] := by decide +kernel
def t2_k154 : List Nat := 2 :: (t2_k149 ++ t2_k152)
theorem t2_n155 : run (leafZ2 cdC) 27 t2_b125 t2_k154 = some [] :=
  run_node (leafZ2 cdC) 26 t2_b125 1 t2_k149 t2_k152 t2_e126 t2_n150 t2_s153
def t2_b156 : Box := splitR t2_b123 2
def t2_k157 : List Nat := [0]
theorem t2_s158 : run (leafZ2 cdC) 27 t2_b156 t2_k157 = some [] := by decide +kernel
def t2_k159 : List Nat := 3 :: (t2_k154 ++ t2_k157)
theorem t2_n160 : run (leafZ2 cdC) 28 t2_b123 t2_k159 = some [] :=
  run_node (leafZ2 cdC) 27 t2_b123 2 t2_k154 t2_k157 t2_e124 t2_n155 t2_s158
def t2_b161 : Box := splitR t2_b121 1
def t2_k162 : List Nat := [0]
theorem t2_s163 : run (leafZ2 cdC) 28 t2_b161 t2_k162 = some [] := by decide +kernel
def t2_k164 : List Nat := 2 :: (t2_k159 ++ t2_k162)
theorem t2_n165 : run (leafZ2 cdC) 29 t2_b121 t2_k164 = some [] :=
  run_node (leafZ2 cdC) 28 t2_b121 1 t2_k159 t2_k162 t2_e122 t2_n160 t2_s163
def t2_b166 : Box := splitR t2_b119 2
def t2_k167 : List Nat := [0]
theorem t2_s168 : run (leafZ2 cdC) 29 t2_b166 t2_k167 = some [] := by decide +kernel
def t2_k169 : List Nat := 3 :: (t2_k164 ++ t2_k167)
theorem t2_n170 : run (leafZ2 cdC) 30 t2_b119 t2_k169 = some [] :=
  run_node (leafZ2 cdC) 29 t2_b119 2 t2_k164 t2_k167 t2_e120 t2_n165 t2_s168
def t2_b171 : Box := splitR t2_b117 1
def t2_k172 : List Nat := [0]
theorem t2_s173 : run (leafZ2 cdC) 30 t2_b171 t2_k172 = some [] := by decide +kernel
def t2_k174 : List Nat := 2 :: (t2_k169 ++ t2_k172)
theorem t2_n175 : run (leafZ2 cdC) 31 t2_b117 t2_k174 = some [] :=
  run_node (leafZ2 cdC) 30 t2_b117 1 t2_k169 t2_k172 t2_e118 t2_n170 t2_s173
def t2_k176 : List Nat := 3 :: (t2_k115 ++ t2_k174)
theorem t2_n177 : run (leafZ2 cdC) 32 t2_b105 t2_k176 = some [] :=
  run_node (leafZ2 cdC) 31 t2_b105 2 t2_k115 t2_k174 t2_e106 t2_n116 t2_n175
def t2_b178 : Box := splitR t2_b103 1
def t2_k179 : List Nat := [0]
theorem t2_s180 : run (leafZ2 cdC) 32 t2_b178 t2_k179 = some [] := by decide +kernel
def t2_k181 : List Nat := 2 :: (t2_k176 ++ t2_k179)
theorem t2_n182 : run (leafZ2 cdC) 33 t2_b103 t2_k181 = some [] :=
  run_node (leafZ2 cdC) 32 t2_b103 1 t2_k176 t2_k179 t2_e104 t2_n177 t2_s180
def t2_k183 : List Nat := 3 :: (t2_k101 ++ t2_k181)
theorem t2_n184 : run (leafZ2 cdC) 34 t2_b98 t2_k183 = some [] :=
  run_node (leafZ2 cdC) 33 t2_b98 2 t2_k101 t2_k181 t2_e99 t2_s102 t2_n182
def t2_b185 : Box := splitR t2_b96 1
def t2_k186 : List Nat := [0]
theorem t2_s187 : run (leafZ2 cdC) 34 t2_b185 t2_k186 = some [] := by decide +kernel
def t2_k188 : List Nat := 2 :: (t2_k183 ++ t2_k186)
theorem t2_n189 : run (leafZ2 cdC) 35 t2_b96 t2_k188 = some [] :=
  run_node (leafZ2 cdC) 34 t2_b96 1 t2_k183 t2_k186 t2_e97 t2_n184 t2_s187
def t2_b190 : Box := splitR t2_b94 2
def t2_k191 : List Nat := [0]
theorem t2_s192 : run (leafZ2 cdC) 35 t2_b190 t2_k191 = some [] := by decide +kernel
def t2_k193 : List Nat := 3 :: (t2_k188 ++ t2_k191)
theorem t2_n194 : run (leafZ2 cdC) 36 t2_b94 t2_k193 = some [] :=
  run_node (leafZ2 cdC) 35 t2_b94 2 t2_k188 t2_k191 t2_e95 t2_n189 t2_s192
def t2_b195 : Box := splitR t2_b92 1
def t2_k196 : List Nat := [0]
theorem t2_s197 : run (leafZ2 cdC) 36 t2_b195 t2_k196 = some [] := by decide +kernel
def t2_k198 : List Nat := 2 :: (t2_k193 ++ t2_k196)
theorem t2_n199 : run (leafZ2 cdC) 37 t2_b92 t2_k198 = some [] :=
  run_node (leafZ2 cdC) 36 t2_b92 1 t2_k193 t2_k196 t2_e93 t2_n194 t2_s197
def t2_k200 : List Nat := 3 :: (t2_k90 ++ t2_k198)
theorem t2_n201 : run (leafZ2 cdC) 38 t2_b87 t2_k200 = some [] :=
  run_node (leafZ2 cdC) 37 t2_b87 2 t2_k90 t2_k198 t2_e88 t2_s91 t2_n199
def t2_b202 : Box := splitR t2_b85 1
def t2_k203 : List Nat := [0]
theorem t2_s204 : run (leafZ2 cdC) 38 t2_b202 t2_k203 = some [] := by decide +kernel
def t2_k205 : List Nat := 2 :: (t2_k200 ++ t2_k203)
theorem t2_n206 : run (leafZ2 cdC) 39 t2_b85 t2_k205 = some [] :=
  run_node (leafZ2 cdC) 38 t2_b85 1 t2_k200 t2_k203 t2_e86 t2_n201 t2_s204
def t2_k207 : List Nat := 3 :: (t2_k83 ++ t2_k205)
theorem t2_n208 : run (leafZ2 cdC) 40 t2_b80 t2_k207 = some [] :=
  run_node (leafZ2 cdC) 39 t2_b80 2 t2_k83 t2_k205 t2_e81 t2_s84 t2_n206
def t2_b209 : Box := splitR t2_b78 1
def t2_k210 : List Nat := [0]
theorem t2_s211 : run (leafZ2 cdC) 40 t2_b209 t2_k210 = some [] := by decide +kernel
def t2_k212 : List Nat := 2 :: (t2_k207 ++ t2_k210)
theorem t2_n213 : run (leafZ2 cdC) 41 t2_b78 t2_k212 = some [] :=
  run_node (leafZ2 cdC) 40 t2_b78 1 t2_k207 t2_k210 t2_e79 t2_n208 t2_s211
def t2_k214 : List Nat := 3 :: (t2_k76 ++ t2_k212)
theorem t2_n215 : run (leafZ2 cdC) 42 t2_b73 t2_k214 = some [] :=
  run_node (leafZ2 cdC) 41 t2_b73 2 t2_k76 t2_k212 t2_e74 t2_s77 t2_n213
def t2_b216 : Box := splitR t2_b71 1
def t2_k217 : List Nat := [3,2,3,2,0,0,0,0,0]
theorem t2_s218 : run (leafZ2 cdC) 42 t2_b216 t2_k217 = some [] := by decide +kernel
def t2_k219 : List Nat := 2 :: (t2_k214 ++ t2_k217)
theorem t2_n220 : run (leafZ2 cdC) 43 t2_b71 t2_k219 = some [] :=
  run_node (leafZ2 cdC) 42 t2_b71 1 t2_k214 t2_k217 t2_e72 t2_n215 t2_s218
def t2_b221 : Box := splitR t2_b69 2
def t2_k222 : List Nat := [1,0,0]
theorem t2_s223 : run (leafZ2 cdC) 43 t2_b221 t2_k222 = some [] := by decide +kernel
def t2_k224 : List Nat := 3 :: (t2_k219 ++ t2_k222)
theorem t2_n225 : run (leafZ2 cdC) 44 t2_b69 t2_k224 = some [] :=
  run_node (leafZ2 cdC) 43 t2_b69 2 t2_k219 t2_k222 t2_e70 t2_n220 t2_s223
def t2_b226 : Box := splitR t2_b67 1
def t2_k227 : List Nat := [1,0,0]
theorem t2_s228 : run (leafZ2 cdC) 44 t2_b226 t2_k227 = some [] := by decide +kernel
def t2_k229 : List Nat := 2 :: (t2_k224 ++ t2_k227)
theorem t2_n230 : run (leafZ2 cdC) 45 t2_b67 t2_k229 = some [] :=
  run_node (leafZ2 cdC) 44 t2_b67 1 t2_k224 t2_k227 t2_e68 t2_n225 t2_s228
def t2_k231 : List Nat := 3 :: (t2_k65 ++ t2_k229)
theorem t2_n232 : run (leafZ2 cdC) 46 t2_b62 t2_k231 = some [] :=
  run_node (leafZ2 cdC) 45 t2_b62 2 t2_k65 t2_k229 t2_e63 t2_s66 t2_n230
def t2_b233 : Box := splitR t2_b60 1
def t2_k234 : List Nat := [1,0,0]
theorem t2_s235 : run (leafZ2 cdC) 46 t2_b233 t2_k234 = some [] := by decide +kernel
def t2_k236 : List Nat := 2 :: (t2_k231 ++ t2_k234)
theorem t2_n237 : run (leafZ2 cdC) 47 t2_b60 t2_k236 = some [] :=
  run_node (leafZ2 cdC) 46 t2_b60 1 t2_k231 t2_k234 t2_e61 t2_n232 t2_s235
def t2_b238 : Box := splitR t2_b58 2
def t2_k239 : List Nat := [1,0,1,0,1,0,0]
theorem t2_s240 : run (leafZ2 cdC) 47 t2_b238 t2_k239 = some [] := by decide +kernel
def t2_k241 : List Nat := 3 :: (t2_k236 ++ t2_k239)
theorem t2_n242 : run (leafZ2 cdC) 48 t2_b58 t2_k241 = some [] :=
  run_node (leafZ2 cdC) 47 t2_b58 2 t2_k236 t2_k239 t2_e59 t2_n237 t2_s240
def t2_b243 : Box := splitR t2_b56 1
def t2_k244 : List Nat := [1,0,0]
theorem t2_s245 : run (leafZ2 cdC) 48 t2_b243 t2_k244 = some [] := by decide +kernel
def t2_k246 : List Nat := 2 :: (t2_k241 ++ t2_k244)
theorem t2_n247 : run (leafZ2 cdC) 49 t2_b56 t2_k246 = some [] :=
  run_node (leafZ2 cdC) 48 t2_b56 1 t2_k241 t2_k244 t2_e57 t2_n242 t2_s245
def t2_k248 : List Nat := 3 :: (t2_k54 ++ t2_k246)
theorem t2_n249 : run (leafZ2 cdC) 50 t2_b51 t2_k248 = some [] :=
  run_node (leafZ2 cdC) 49 t2_b51 2 t2_k54 t2_k246 t2_e52 t2_s55 t2_n247
def t2_b250 : Box := splitR t2_b49 1
def t2_k251 : List Nat := [1,0,0]
theorem t2_s252 : run (leafZ2 cdC) 50 t2_b250 t2_k251 = some [] := by decide +kernel
def t2_k253 : List Nat := 2 :: (t2_k248 ++ t2_k251)
theorem t2_n254 : run (leafZ2 cdC) 51 t2_b49 t2_k253 = some [] :=
  run_node (leafZ2 cdC) 50 t2_b49 1 t2_k248 t2_k251 t2_e50 t2_n249 t2_s252
def t2_b255 : Box := splitR t2_b47 2
def t2_k256 : List Nat := [1,0,1,0,1,0,1,0,1,0,0]
theorem t2_s257 : run (leafZ2 cdC) 51 t2_b255 t2_k256 = some [] := by decide +kernel
def t2_k258 : List Nat := 3 :: (t2_k253 ++ t2_k256)
theorem t2_n259 : run (leafZ2 cdC) 52 t2_b47 t2_k258 = some [] :=
  run_node (leafZ2 cdC) 51 t2_b47 2 t2_k253 t2_k256 t2_e48 t2_n254 t2_s257
def t2_b260 : Box := splitR t2_b45 1
def t2_k261 : List Nat := [1,0,0]
theorem t2_s262 : run (leafZ2 cdC) 52 t2_b260 t2_k261 = some [] := by decide +kernel
def t2_k263 : List Nat := 2 :: (t2_k258 ++ t2_k261)
theorem t2_n264 : run (leafZ2 cdC) 53 t2_b45 t2_k263 = some [] :=
  run_node (leafZ2 cdC) 52 t2_b45 1 t2_k258 t2_k261 t2_e46 t2_n259 t2_s262
def t2_k265 : List Nat := 3 :: (t2_k43 ++ t2_k263)
theorem t2_n266 : run (leafZ2 cdC) 54 t2_b33 t2_k265 = some [] :=
  run_node (leafZ2 cdC) 53 t2_b33 2 t2_k43 t2_k263 t2_e34 t2_n44 t2_n264
def t2_k267 : List Nat := 3 :: (t2_k31 ++ t2_k265)
theorem t2_n268 : run (leafZ2 cdC) 55 t2_b28 t2_k267 = some [] :=
  run_node (leafZ2 cdC) 54 t2_b28 2 t2_k31 t2_k265 t2_e29 t2_s32 t2_n266
def t2_b269 : Box := splitR t2_b26 2
def t2_k270 : List Nat := [1,0,1,0,1,0,1,0,1,0,1,0,1,0,1,0,1,0,2,1,0,2,1,0,2,1,0,2,1,0,2,1,0,2,1,0,2,1,0,3,0,0,0,0,0,0,0,0,0]
theorem t2_s271 : run (leafZ2 cdC) 55 t2_b269 t2_k270 = some [] := by decide +kernel
def t2_k272 : List Nat := 3 :: (t2_k267 ++ t2_k270)
theorem t2_n273 : run (leafZ2 cdC) 56 t2_b26 t2_k272 = some [] :=
  run_node (leafZ2 cdC) 55 t2_b26 2 t2_k267 t2_k270 t2_e27 t2_n268 t2_s271
def t2_k274 : List Nat := 3 :: (t2_k24 ++ t2_k272)
theorem t2_n275 : run (leafZ2 cdC) 57 t2_b21 t2_k274 = some [] :=
  run_node (leafZ2 cdC) 56 t2_b21 2 t2_k24 t2_k272 t2_e22 t2_s25 t2_n273
def t2_b276 : Box := splitR t2_b19 2
def t2_k277 : List Nat := [1,0,1,0,1,0,1,0,1,0,1,0,1,0,1,0,1,0,2,1,0,2,1,0,2,1,0,2,3,1,0,2,1,0,2,1,3,0,0,3,2,1,0,2,1,3,0,0,3,0,0,0,0,0,1,0,3,0,0,0,0,3,0,0,0,0,0]
theorem t2_s278 : run (leafZ2 cdC) 57 t2_b276 t2_k277 = some [] := by decide +kernel
def t2_k279 : List Nat := 3 :: (t2_k274 ++ t2_k277)
theorem t2_n280 : run (leafZ2 cdC) 58 t2_b19 t2_k279 = some [] :=
  run_node (leafZ2 cdC) 57 t2_b19 2 t2_k274 t2_k277 t2_e20 t2_n275 t2_s278
def t2_b281 : Box := splitR t2_b17 2
def t2_k282 : List Nat := [1,0,1,0,1,0,1,0,1,0,1,0,1,0,1,0,1,0,3,2,1,0,2,0,0,0,0]
theorem t2_s283 : run (leafZ2 cdC) 58 t2_b281 t2_k282 = some [] := by decide +kernel
def t2_k284 : List Nat := 3 :: (t2_k279 ++ t2_k282)
theorem t2_n285 : run (leafZ2 cdC) 59 t2_b17 t2_k284 = some [] :=
  run_node (leafZ2 cdC) 58 t2_b17 2 t2_k279 t2_k282 t2_e18 t2_n280 t2_s283
def t2_b286 : Box := splitR t2_b15 2
def t2_k287 : List Nat := [1,0,1,0,1,0,1,0,1,0,1,0,1,0,3,0,0]
theorem t2_s288 : run (leafZ2 cdC) 59 t2_b286 t2_k287 = some [] := by decide +kernel
def t2_k289 : List Nat := 3 :: (t2_k284 ++ t2_k287)
theorem t2_n290 : run (leafZ2 cdC) 60 t2_b15 t2_k289 = some [] :=
  run_node (leafZ2 cdC) 59 t2_b15 2 t2_k284 t2_k287 t2_e16 t2_n285 t2_s288
def t2_k291 : List Nat := 3 :: (t2_k13 ++ t2_k289)
theorem t2_n292 : run (leafZ2 cdC) 61 t2_b10 t2_k291 = some [] :=
  run_node (leafZ2 cdC) 60 t2_b10 2 t2_k13 t2_k289 t2_e11 t2_s14 t2_n290
def t2_b293 : Box := splitR t2_b8 2
def t2_k294 : List Nat := [1,0,1,0,1,0,3,1,0,1,0,3,0,0,0]
theorem t2_s295 : run (leafZ2 cdC) 61 t2_b293 t2_k294 = some [] := by decide +kernel
def t2_k296 : List Nat := 3 :: (t2_k291 ++ t2_k294)
theorem t2_n297 : run (leafZ2 cdC) 62 t2_b8 t2_k296 = some [] :=
  run_node (leafZ2 cdC) 61 t2_b8 2 t2_k291 t2_k294 t2_e9 t2_n292 t2_s295
def t2_b298 : Box := splitR t2_b6 2
def t2_k299 : List Nat := [3,1,0,1,0,3,0,0,3,1,0,3,0,0,3,0,0]
theorem t2_s300 : run (leafZ2 cdC) 62 t2_b298 t2_k299 = some [] := by decide +kernel
def t2_k301 : List Nat := 3 :: (t2_k296 ++ t2_k299)
theorem t2_n302 : run (leafZ2 cdC) 63 t2_b6 t2_k301 = some [] :=
  run_node (leafZ2 cdC) 62 t2_b6 2 t2_k296 t2_k299 t2_e7 t2_n297 t2_s300
def t2_k303 : List Nat := 3 :: (t2_k4 ++ t2_k301)
theorem t2_n304 : run (leafZ2 cdC) 64 t2_b1 t2_k303 = some [] :=
  run_node (leafZ2 cdC) 63 t2_b1 2 t2_k4 t2_k301 t2_e2 t2_s5 t2_n302
theorem hpre : (zle zero cdC.ph && zle zero (zsub cdC.pm cdC.ph) && zlt (zadd cdC.pm cdC.ph) S && rootOK0 cdC) = true := by decide +kernel
theorem hc : cell0Check { cdC with tree1 := t1_k2, tree2 := t2_k303 } = true := by
  have e : cell0Check { cdC with tree1 := t1_k2, tree2 := t2_k303 } =
      ((zle zero cdC.ph && zle zero (zsub cdC.pm cdC.ph) && zlt (zadd cdC.pm cdC.ph) S && rootOK0 cdC) && runAll (leaf1 cdC) (root1 cdC) t1_k2 && runAll (leafZ2 cdC) (root2 cdC) t2_k303) := rfl
  rw [e, hpre, runAll_of_run (leaf1 cdC) (root1 cdC) t1_k2 t1_s3, runAll_of_run (leafZ2 cdC) (root2 cdC) t2_k303 t2_n304]; rfl

theorem e0 : toR (zsub cdC.pm cdC.ph) = (0 / 1 : ℝ) := by norm_num [cdC, toR, zsub, SN]
theorem e1 : toR (zadd cdC.pm cdC.ph) = (1 / 512 : ℝ) := by norm_num [cdC, toR, zadd, SN]

end RandomSizeStable.Stability.RankCutCert.Pieces.cells_near_zero

open RandomSizeStable.Stability.RankCutCert RandomSizeStable.Stability.RankCutCert.Dev in
theorem RandomSizeStable.Stability.RankCutCert.cells_near_zero_dev :
    ∃ (n : ℕ) (p0 p1 l0 l1 l2 : Fin n → ℝ) (t0 t1 : Fin n → Fin 9 → ℝ),
      (∀ k, CellOK (p0 k) (p1 k) (l0 k) (l1 k) (l2 k) (t0 k) (t1 k)) ∧
      ∀ p : ℝ, 0 < p → p ≤ 1 / 512 → ∃ k, p0 k ≤ p ∧ p ≤ p1 k := by
  have h := RandomSizeStable.Stability.RankCutCert.cell0Check_ok _ RandomSizeStable.Stability.RankCutCert.Pieces.cells_near_zero.hc
  refine ⟨1, fun _ => _, fun _ => _, fun _ => _, fun _ => _, fun _ => _, fun _ => _, fun _ => _,
    fun _ => h, ?_⟩
  intro p hp0 hp1
  refine ⟨0, ?_, ?_⟩
  · show toR (zsub RandomSizeStable.Stability.RankCutCert.Pieces.cells_near_zero.cdC.pm RandomSizeStable.Stability.RankCutCert.Pieces.cells_near_zero.cdC.ph) ≤ p
    rw [RandomSizeStable.Stability.RankCutCert.Pieces.cells_near_zero.e0]; linarith
  · show p ≤ toR (zadd RandomSizeStable.Stability.RankCutCert.Pieces.cells_near_zero.cdC.pm RandomSizeStable.Stability.RankCutCert.Pieces.cells_near_zero.cdC.ph)
    rw [RandomSizeStable.Stability.RankCutCert.Pieces.cells_near_zero.e1]; linarith

theorem solution : type_of% @RandomSizeStable.Stability.RankCutCert.cells_near_zero_dev := @RandomSizeStable.Stability.RankCutCert.cells_near_zero_dev
