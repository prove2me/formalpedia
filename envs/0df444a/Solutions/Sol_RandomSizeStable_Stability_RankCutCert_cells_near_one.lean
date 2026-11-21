-- Prove2me | solution 1 for RandomSizeStable.Stability.RankCutCert.cells_near_one
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-20T20:18:56.489364+00:00
-- url     : https://prove2.me/submissions/3f8fe235-22fe-49c2-ad98-920bf10335a2

import Mathlib
import Definitions.Def_RandomSizeStable_Stability_RankCutCert
import Definitions.Def_RandomSizeStable_Stability_RankCutCertEngine
import Theorems.Thm_RandomSizeStable_Stability_RankCutCert_cellNCheck_ok

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option Elab.async false

namespace RandomSizeStable.Stability.RankCutCert.Pieces.cells_near_one

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
  pm := ⟨18444492273895866368, 0⟩
  ph := ⟨2251799813685248, 0⟩
  l0 := ⟨⟨200, 0⟩, 1⟩
  l1 := ⟨⟨0, 32202968683⟩, 161015224⟩
  l2 := ⟨⟨0, 0⟩, 1⟩
  t0 := ![⟨⟨0, 123410651736⟩, 622912507⟩, ⟨⟨0, 168121832542⟩, 929404021⟩, ⟨⟨0, 98189432532⟩, 495933955⟩, ⟨⟨0, 104856751160⟩, 529797199⟩, ⟨⟨0, 51027636533⟩, 279408047⟩, ⟨⟨0, 123264097166⟩, 623110027⟩, ⟨⟨0, 6595313727⟩, 33349705⟩, ⟨⟨0, 984632503⟩, 4981069⟩, ⟨⟨0, 66344283949⟩, 340117958⟩]
  t1 := ![⟨⟨200, 0⟩, 1⟩, ⟨⟨181467847883, 0⟩, 992528848⟩, ⟨⟨200, 0⟩, 1⟩, ⟨⟨200, 0⟩, 1⟩, ⟨⟨177877261335, 0⟩, 962752471⟩, ⟨⟨200, 0⟩, 1⟩, ⟨⟨200, 0⟩, 1⟩, ⟨⟨200, 0⟩, 1⟩, ⟨⟨121372300784, 0⟩, 614420217⟩]
  tree1 := []
  tree2 := []

def t1_b1 : Box := root1 cdC
theorem t1_e2 : evenH t1_b1 0 = true := by decide +kernel
def t1_b3 : Box := splitL t1_b1 0
theorem t1_e4 : evenH t1_b3 0 = true := by decide +kernel
def t1_b5 : Box := splitL t1_b3 0
theorem t1_e6 : evenH t1_b5 0 = true := by decide +kernel
def t1_b7 : Box := splitL t1_b5 0
theorem t1_e8 : evenH t1_b7 0 = true := by decide +kernel
def t1_b9 : Box := splitL t1_b7 0
theorem t1_e10 : evenH t1_b9 0 = true := by decide +kernel
def t1_b11 : Box := splitL t1_b9 0
theorem t1_e12 : evenH t1_b11 0 = true := by decide +kernel
def t1_b13 : Box := splitL t1_b11 0
def t1_k14 : List Nat := [0]
theorem t1_s15 : run (leafN1 cdC) 58 t1_b13 t1_k14 = some [] := by decide +kernel
def t1_b16 : Box := splitR t1_b11 0
theorem t1_e17 : evenH t1_b16 0 = true := by decide +kernel
def t1_b18 : Box := splitL t1_b16 0
def t1_k19 : List Nat := [1,0,1,1,1,1,0,1,2,1,0,2,1,0,0,0,0,2,1,2,0,1,0,0,0,1,0,2,1,0,0,0,1,1,2,0,1,2,0,1,0,0,0,0,0,0,1,1,1,0,1,0,2,1,0,0,0,1,1,2,0,1,2,0,1,0,0,0,0,0,0]
theorem t1_s20 : run (leafN1 cdC) 57 t1_b18 t1_k19 = some [] := by decide +kernel
def t1_b21 : Box := splitR t1_b16 0
theorem t1_e22 : evenH t1_b21 0 = true := by decide +kernel
def t1_b23 : Box := splitL t1_b21 0
def t1_k24 : List Nat := [1,1,1,0,1,1,2,1,2,0,0,0,0,2,0,1,2,0,0,0,0,0,1,1,0,1,0,1,2,1,2,0,0,0,0,2,0,1,2,0,0,0,0]
theorem t1_s25 : run (leafN1 cdC) 56 t1_b23 t1_k24 = some [] := by decide +kernel
def t1_b26 : Box := splitR t1_b21 0
def t1_k27 : List Nat := [1,1,1,1,0,0,1,1,2,0,1,0,2,0,1,0,0,0,0,1,0,1,0,1,0,2,1,2,0,0,0,0,1,1,1,1,2,0,1,2,0,0,0,0,0,0,1,0,1,0,1,2,0,0,0]
theorem t1_s28 : run (leafN1 cdC) 56 t1_b26 t1_k27 = some [] := by decide +kernel
def t1_k29 : List Nat := 1 :: (t1_k24 ++ t1_k27)
theorem t1_n30 : run (leafN1 cdC) 57 t1_b21 t1_k29 = some [] :=
  run_node (leafN1 cdC) 56 t1_b21 0 t1_k24 t1_k27 t1_e22 t1_s25 t1_s28
def t1_k31 : List Nat := 1 :: (t1_k19 ++ t1_k29)
theorem t1_n32 : run (leafN1 cdC) 58 t1_b16 t1_k31 = some [] :=
  run_node (leafN1 cdC) 57 t1_b16 0 t1_k19 t1_k29 t1_e17 t1_s20 t1_n30
def t1_k33 : List Nat := 1 :: (t1_k14 ++ t1_k31)
theorem t1_n34 : run (leafN1 cdC) 59 t1_b11 t1_k33 = some [] :=
  run_node (leafN1 cdC) 58 t1_b11 0 t1_k14 t1_k31 t1_e12 t1_s15 t1_n32
def t1_b35 : Box := splitR t1_b9 0
theorem t1_e36 : evenH t1_b35 0 = true := by decide +kernel
def t1_b37 : Box := splitL t1_b35 0
def t1_k38 : List Nat := [1,1,1,0,1,1,0,1,1,2,1,2,0,0,0,0,2,0,1,2,0,0,0,0,0,1,0,1,0,1,1,0,1,2,1,0,2,1,0,2,0,0,0,0,2,1,2,0,1,0,2,0,0,0,1,0,2,1,0,2,0,0,0,1,1,2,0,1,2,0,1,0,2,0,0,0,0,0,1,1,0,0,1,0,0]
theorem t1_s39 : run (leafN1 cdC) 58 t1_b37 t1_k38 = some [] := by decide +kernel
def t1_b40 : Box := splitR t1_b35 0
def t1_k41 : List Nat := [1,1,1,0,0,1,0,0,1,1,0,0,1,0,0]
theorem t1_s42 : run (leafN1 cdC) 58 t1_b40 t1_k41 = some [] := by decide +kernel
def t1_k43 : List Nat := 1 :: (t1_k38 ++ t1_k41)
theorem t1_n44 : run (leafN1 cdC) 59 t1_b35 t1_k43 = some [] :=
  run_node (leafN1 cdC) 58 t1_b35 0 t1_k38 t1_k41 t1_e36 t1_s39 t1_s42
def t1_k45 : List Nat := 1 :: (t1_k33 ++ t1_k43)
theorem t1_n46 : run (leafN1 cdC) 60 t1_b9 t1_k45 = some [] :=
  run_node (leafN1 cdC) 59 t1_b9 0 t1_k33 t1_k43 t1_e10 t1_n34 t1_n44
def t1_b47 : Box := splitR t1_b7 0
def t1_k48 : List Nat := [1,1,1,1,1,0,0,1,0,0,1,1,0,0,1,0,0,1,1,1,0,0,1,0,0,1,0,0,1,1,1,0,0,1,0,0,1,1,0,0,1,0,0]
theorem t1_s49 : run (leafN1 cdC) 60 t1_b47 t1_k48 = some [] := by decide +kernel
def t1_k50 : List Nat := 1 :: (t1_k45 ++ t1_k48)
theorem t1_n51 : run (leafN1 cdC) 61 t1_b7 t1_k50 = some [] :=
  run_node (leafN1 cdC) 60 t1_b7 0 t1_k45 t1_k48 t1_e8 t1_n46 t1_s49
def t1_b52 : Box := splitR t1_b5 0
def t1_k53 : List Nat := [1,1,1,1,1,0,0,1,0,0,1,0,0,1,1,0,0,1,0,0,1,1,1,0,0,1,0,0,1,1,0,0,1,0,0]
theorem t1_s54 : run (leafN1 cdC) 61 t1_b52 t1_k53 = some [] := by decide +kernel
def t1_k55 : List Nat := 1 :: (t1_k50 ++ t1_k53)
theorem t1_n56 : run (leafN1 cdC) 62 t1_b5 t1_k55 = some [] :=
  run_node (leafN1 cdC) 61 t1_b5 0 t1_k50 t1_k53 t1_e6 t1_n51 t1_s54
def t1_b57 : Box := splitR t1_b3 0
theorem t1_e58 : evenH t1_b57 0 = true := by decide +kernel
def t1_b59 : Box := splitL t1_b57 0
def t1_k60 : List Nat := [1,1,1,1,0,0,1,0,0,1,1,0,0,1,0,0,1,1,1,0,1,0,0,1,1,0,0,1,0,0,1,1,1,0,0,1,0,0,1,1,0,0,1,0,0]
theorem t1_s61 : run (leafN1 cdC) 61 t1_b59 t1_k60 = some [] := by decide +kernel
def t1_b62 : Box := splitR t1_b57 0
theorem t1_e63 : evenH t1_b62 0 = true := by decide +kernel
def t1_b64 : Box := splitL t1_b62 0
theorem t1_e65 : evenH t1_b64 0 = true := by decide +kernel
def t1_b66 : Box := splitL t1_b64 0
def t1_k67 : List Nat := [1,1,1,0,0,1,1,0,0,1,0,0,1,1,1,0,0,1,0,0,1,1,0,0,1,0,0]
theorem t1_s68 : run (leafN1 cdC) 59 t1_b66 t1_k67 = some [] := by decide +kernel
def t1_b69 : Box := splitR t1_b64 0
theorem t1_e70 : evenH t1_b69 0 = true := by decide +kernel
def t1_b71 : Box := splitL t1_b69 0
def t1_k72 : List Nat := [1,1,1,0,2,0,0,1,2,0,0,2,0,0,1,1,2,0,0,2,0,0,1,2,0,0,2,0,0]
theorem t1_s73 : run (leafN1 cdC) 58 t1_b71 t1_k72 = some [] := by decide +kernel
def t1_b74 : Box := splitR t1_b69 0
theorem t1_e75 : evenH t1_b74 0 = true := by decide +kernel
def t1_b76 : Box := splitL t1_b74 0
def t1_k77 : List Nat := [1,1,2,1,0,0,1,0,0,2,1,0,0,1,0,0,1,2,1,0,0,1,0,0,2,1,0,2,0,0,1,2,0,0,2,0,0]
theorem t1_s78 : run (leafN1 cdC) 57 t1_b76 t1_k77 = some [] := by decide +kernel
def t1_b79 : Box := splitR t1_b74 0
theorem t1_e80 : evenH t1_b79 0 = true := by decide +kernel
def t1_b81 : Box := splitL t1_b79 0
theorem t1_e82 : evenH t1_b81 0 = true := by decide +kernel
def t1_b83 : Box := splitL t1_b81 0
def t1_k84 : List Nat := [2,1,2,0,0,2,0,0,1,2,0,0,2,0,0]
theorem t1_s85 : run (leafN1 cdC) 55 t1_b83 t1_k84 = some [] := by decide +kernel
def t1_b86 : Box := splitR t1_b81 0
theorem t1_e87 : evenH t1_b86 0 = true := by decide +kernel
def t1_b88 : Box := splitL t1_b86 0
theorem t1_e89 : evenH t1_b88 0 = true := by decide +kernel
def t1_b90 : Box := splitL t1_b88 0
theorem t1_e91 : evenH t1_b90 0 = true := by decide +kernel
def t1_b92 : Box := splitL t1_b90 0
theorem t1_e93 : evenH t1_b92 0 = true := by decide +kernel
def t1_b94 : Box := splitL t1_b92 0
def t1_k95 : List Nat := [0]
theorem t1_s96 : run (leafN1 cdC) 51 t1_b94 t1_k95 = some [] := by decide +kernel
def t1_b97 : Box := splitR t1_b92 0
theorem t1_e98 : evenH t1_b97 1 = true := by decide +kernel
def t1_b99 : Box := splitL t1_b97 1
theorem t1_e100 : evenH t1_b99 0 = true := by decide +kernel
def t1_b101 : Box := splitL t1_b99 0
def t1_k102 : List Nat := [2,1,0,2,1,0,2,1,0,2,1,0,2,1,0,0,0,0,0,0,0]
theorem t1_s103 : run (leafN1 cdC) 49 t1_b101 t1_k102 = some [] := by decide +kernel
def t1_b104 : Box := splitR t1_b99 0
theorem t1_e105 : evenH t1_b104 1 = true := by decide +kernel
def t1_b106 : Box := splitL t1_b104 1
def t1_k107 : List Nat := [1,2,1,2,1,2,0,1,0,0,0,1,0,2,1,2,0,1,0,0,0,1,0,2,0,1,0,0,0,1,0,2,1,2,1,2,0,0,0,1,0,2,1,0,0,0,0,1,0,2,1,2,1,0,0,0,0,1,0,2,1,0,0,0,2,0,1,0,0]
theorem t1_s108 : run (leafN1 cdC) 48 t1_b106 t1_k107 = some [] := by decide +kernel
def t1_b109 : Box := splitR t1_b104 1
def t1_k110 : List Nat := [1,0,2,1,2,1,2,1,0,2,0,1,0,0,0,2,0,1,2,0,1,0,0,0,1,0,2,1,0,2,0,1,0,0,0,2,0,1,2,0,1,2,1,2,0,0,0,0,0,0,1,0,2,1,2,1,0,2,1,0,0,0,0,2,0,1,2,1,0,0,0,0,1,0,2,1,0,2,1,0,2,0,0,0,0]
theorem t1_s111 : run (leafN1 cdC) 48 t1_b109 t1_k110 = some [] := by decide +kernel
def t1_k112 : List Nat := 2 :: (t1_k107 ++ t1_k110)
theorem t1_n113 : run (leafN1 cdC) 49 t1_b104 t1_k112 = some [] :=
  run_node (leafN1 cdC) 48 t1_b104 1 t1_k107 t1_k110 t1_e105 t1_s108 t1_s111
def t1_k114 : List Nat := 1 :: (t1_k102 ++ t1_k112)
theorem t1_n115 : run (leafN1 cdC) 50 t1_b99 t1_k114 = some [] :=
  run_node (leafN1 cdC) 49 t1_b99 0 t1_k102 t1_k112 t1_e100 t1_s103 t1_n113
def t1_b116 : Box := splitR t1_b97 1
def t1_k117 : List Nat := [0]
theorem t1_s118 : run (leafN1 cdC) 50 t1_b116 t1_k117 = some [] := by decide +kernel
def t1_k119 : List Nat := 2 :: (t1_k114 ++ t1_k117)
theorem t1_n120 : run (leafN1 cdC) 51 t1_b97 t1_k119 = some [] :=
  run_node (leafN1 cdC) 50 t1_b97 1 t1_k114 t1_k117 t1_e98 t1_n115 t1_s118
def t1_k121 : List Nat := 1 :: (t1_k95 ++ t1_k119)
theorem t1_n122 : run (leafN1 cdC) 52 t1_b92 t1_k121 = some [] :=
  run_node (leafN1 cdC) 51 t1_b92 0 t1_k95 t1_k119 t1_e93 t1_s96 t1_n120
def t1_b123 : Box := splitR t1_b90 0
theorem t1_e124 : evenH t1_b123 0 = true := by decide +kernel
def t1_b125 : Box := splitL t1_b123 0
theorem t1_e126 : evenH t1_b125 1 = true := by decide +kernel
def t1_b127 : Box := splitL t1_b125 1
def t1_k128 : List Nat := [1,2,0,1,2,0,1,2,0,1,2,1,2,0,1,2,0,0,0,0,1,2,1,0,2,0,0,0,2,0,1,0,0,0,0,0,0]
theorem t1_s129 : run (leafN1 cdC) 50 t1_b127 t1_k128 = some [] := by decide +kernel
def t1_b130 : Box := splitR t1_b125 1
theorem t1_e131 : evenH t1_b130 0 = true := by decide +kernel
def t1_b132 : Box := splitL t1_b130 0
theorem t1_e133 : evenH t1_b132 1 = true := by decide +kernel
def t1_b134 : Box := splitL t1_b132 1
theorem t1_e135 : evenH t1_b134 0 = true := by decide +kernel
def t1_b136 : Box := splitL t1_b134 0
def t1_k137 : List Nat := [2,1,2,1,0,2,1,2,0,1,0,0,0,1,0,2,0,1,0,2,0,0,0,2,0,1,2,1,2,1,2,0,0,0,1,0,2,0,0,0,1,0,2,1,0,0,0,0,1,0,2,1,0,2,1,2,1,0,0,0,2,0,1,2,0,0,0,1,0,2,1,0,2,0,0,0,0]
theorem t1_s138 : run (leafN1 cdC) 47 t1_b136 t1_k137 = some [] := by decide +kernel
def t1_b139 : Box := splitR t1_b134 0
def t1_k140 : List Nat := [2,0,1,2,1,2,0,1,2,0,1,2,0,0,0,0,0,1,2,1,2,1,0,2,0,0,0,2,0,1,0,0,0,2,0,1,2,0,1,0,0,0,0]
theorem t1_s141 : run (leafN1 cdC) 47 t1_b139 t1_k140 = some [] := by decide +kernel
def t1_k142 : List Nat := 1 :: (t1_k137 ++ t1_k140)
theorem t1_n143 : run (leafN1 cdC) 48 t1_b134 t1_k142 = some [] :=
  run_node (leafN1 cdC) 47 t1_b134 0 t1_k137 t1_k140 t1_e135 t1_s138 t1_s141
def t1_b144 : Box := splitR t1_b132 1
theorem t1_e145 : evenH t1_b144 0 = true := by decide +kernel
def t1_b146 : Box := splitL t1_b144 0
def t1_k147 : List Nat := [0]
theorem t1_s148 : run (leafN1 cdC) 47 t1_b146 t1_k147 = some [] := by decide +kernel
def t1_b149 : Box := splitR t1_b144 0
def t1_k150 : List Nat := [2,1,2,1,0,2,1,0,2,1,2,0,1,0,0,0,1,0,2,0,0,0,0,2,1,2,0,1,2,1,2,0,0,0,1,0,2,0,0,0,0,1,2,1,0,2,1,2,1,0,0,0,0,0,0,2,0,1,2,1,0,0,0,2,0,1,2,0,1,0,0,0,1,0,2,1,0,2,1,0,2,1,0,2,0,0,0,0,0]
theorem t1_s151 : run (leafN1 cdC) 47 t1_b149 t1_k150 = some [] := by decide +kernel
def t1_k152 : List Nat := 1 :: (t1_k147 ++ t1_k150)
theorem t1_n153 : run (leafN1 cdC) 48 t1_b144 t1_k152 = some [] :=
  run_node (leafN1 cdC) 47 t1_b144 0 t1_k147 t1_k150 t1_e145 t1_s148 t1_s151
def t1_k154 : List Nat := 2 :: (t1_k142 ++ t1_k152)
theorem t1_n155 : run (leafN1 cdC) 49 t1_b132 t1_k154 = some [] :=
  run_node (leafN1 cdC) 48 t1_b132 1 t1_k142 t1_k152 t1_e133 t1_n143 t1_n153
def t1_b156 : Box := splitR t1_b130 0
def t1_k157 : List Nat := [2,0,1,2,0,1,2,1,2,1,2,0,1,2,0,0,0,0,1,2,1,0,2,0,0,0,2,0,1,2,1,0,0,0,0,0,1,0,2,1,2,0,1,0,0,0,1,0,2,1,2,0,1,0,0,0,1,0,2,0,0,2,0,1,0,0,0]
theorem t1_s158 : run (leafN1 cdC) 49 t1_b156 t1_k157 = some [] := by decide +kernel
def t1_k159 : List Nat := 1 :: (t1_k154 ++ t1_k157)
theorem t1_n160 : run (leafN1 cdC) 50 t1_b130 t1_k159 = some [] :=
  run_node (leafN1 cdC) 49 t1_b130 0 t1_k154 t1_k157 t1_e131 t1_n155 t1_s158
def t1_k161 : List Nat := 2 :: (t1_k128 ++ t1_k159)
theorem t1_n162 : run (leafN1 cdC) 51 t1_b125 t1_k161 = some [] :=
  run_node (leafN1 cdC) 50 t1_b125 1 t1_k128 t1_k159 t1_e126 t1_s129 t1_n160
def t1_b163 : Box := splitR t1_b123 0
def t1_k164 : List Nat := [0]
theorem t1_s165 : run (leafN1 cdC) 51 t1_b163 t1_k164 = some [] := by decide +kernel
def t1_k166 : List Nat := 1 :: (t1_k161 ++ t1_k164)
theorem t1_n167 : run (leafN1 cdC) 52 t1_b123 t1_k166 = some [] :=
  run_node (leafN1 cdC) 51 t1_b123 0 t1_k161 t1_k164 t1_e124 t1_n162 t1_s165
def t1_k168 : List Nat := 1 :: (t1_k121 ++ t1_k166)
theorem t1_n169 : run (leafN1 cdC) 53 t1_b90 t1_k168 = some [] :=
  run_node (leafN1 cdC) 52 t1_b90 0 t1_k121 t1_k166 t1_e91 t1_n122 t1_n167
def t1_b170 : Box := splitR t1_b88 0
def t1_k171 : List Nat := [2,0,0]
theorem t1_s172 : run (leafN1 cdC) 53 t1_b170 t1_k171 = some [] := by decide +kernel
def t1_k173 : List Nat := 1 :: (t1_k168 ++ t1_k171)
theorem t1_n174 : run (leafN1 cdC) 54 t1_b88 t1_k173 = some [] :=
  run_node (leafN1 cdC) 53 t1_b88 0 t1_k168 t1_k171 t1_e89 t1_n169 t1_s172
def t1_b175 : Box := splitR t1_b86 0
def t1_k176 : List Nat := [2,2,0,0,2,0,0]
theorem t1_s177 : run (leafN1 cdC) 54 t1_b175 t1_k176 = some [] := by decide +kernel
def t1_k178 : List Nat := 1 :: (t1_k173 ++ t1_k176)
theorem t1_n179 : run (leafN1 cdC) 55 t1_b86 t1_k178 = some [] :=
  run_node (leafN1 cdC) 54 t1_b86 0 t1_k173 t1_k176 t1_e87 t1_n174 t1_s177
def t1_k180 : List Nat := 1 :: (t1_k84 ++ t1_k178)
theorem t1_n181 : run (leafN1 cdC) 56 t1_b81 t1_k180 = some [] :=
  run_node (leafN1 cdC) 55 t1_b81 0 t1_k84 t1_k178 t1_e82 t1_s85 t1_n179
def t1_b182 : Box := splitR t1_b79 0
def t1_k183 : List Nat := [1,2,1,2,0,0,2,0,0,2,1,0,0,1,0,0,2,1,2,0,0,0,1,2,0,0,2,0,0]
theorem t1_s184 : run (leafN1 cdC) 56 t1_b182 t1_k183 = some [] := by decide +kernel
def t1_k185 : List Nat := 1 :: (t1_k180 ++ t1_k183)
theorem t1_n186 : run (leafN1 cdC) 57 t1_b79 t1_k185 = some [] :=
  run_node (leafN1 cdC) 56 t1_b79 0 t1_k180 t1_k183 t1_e80 t1_n181 t1_s184
def t1_k187 : List Nat := 1 :: (t1_k77 ++ t1_k185)
theorem t1_n188 : run (leafN1 cdC) 58 t1_b74 t1_k187 = some [] :=
  run_node (leafN1 cdC) 57 t1_b74 0 t1_k77 t1_k185 t1_e75 t1_s78 t1_n186
def t1_k189 : List Nat := 1 :: (t1_k72 ++ t1_k187)
theorem t1_n190 : run (leafN1 cdC) 59 t1_b69 t1_k189 = some [] :=
  run_node (leafN1 cdC) 58 t1_b69 0 t1_k72 t1_k187 t1_e70 t1_s73 t1_n188
def t1_k191 : List Nat := 1 :: (t1_k67 ++ t1_k189)
theorem t1_n192 : run (leafN1 cdC) 60 t1_b64 t1_k191 = some [] :=
  run_node (leafN1 cdC) 59 t1_b64 0 t1_k67 t1_k189 t1_e65 t1_s68 t1_n190
def t1_b193 : Box := splitR t1_b62 0
def t1_k194 : List Nat := [1,1,1,1,1,2,1,0,0,1,0,0,2,0,0,1,2,0,0,0,1,0,0,1,0,0,1,0,0]
theorem t1_s195 : run (leafN1 cdC) 60 t1_b193 t1_k194 = some [] := by decide +kernel
def t1_k196 : List Nat := 1 :: (t1_k191 ++ t1_k194)
theorem t1_n197 : run (leafN1 cdC) 61 t1_b62 t1_k196 = some [] :=
  run_node (leafN1 cdC) 60 t1_b62 0 t1_k191 t1_k194 t1_e63 t1_n192 t1_s195
def t1_k198 : List Nat := 1 :: (t1_k60 ++ t1_k196)
theorem t1_n199 : run (leafN1 cdC) 62 t1_b57 t1_k198 = some [] :=
  run_node (leafN1 cdC) 61 t1_b57 0 t1_k60 t1_k196 t1_e58 t1_s61 t1_n197
def t1_k200 : List Nat := 1 :: (t1_k55 ++ t1_k198)
theorem t1_n201 : run (leafN1 cdC) 63 t1_b3 t1_k200 = some [] :=
  run_node (leafN1 cdC) 62 t1_b3 0 t1_k55 t1_k198 t1_e4 t1_n56 t1_n199
def t1_b202 : Box := splitR t1_b1 0
theorem t1_e203 : evenH t1_b202 0 = true := by decide +kernel
def t1_b204 : Box := splitL t1_b202 0
theorem t1_e205 : evenH t1_b204 0 = true := by decide +kernel
def t1_b206 : Box := splitL t1_b204 0
def t1_k207 : List Nat := [1,1,1,1,0,1,1,0,1,1,1,1,1,0,0,0,0,0,0,0,1,0,0,0,1,1,0,1,1,1,1,0,1,0,1,0,1,1,0,2,0,1,0,0,0,2,0,1,0,0,0,0,0]
theorem t1_s208 : run (leafN1 cdC) 61 t1_b206 t1_k207 = some [] := by decide +kernel
def t1_b209 : Box := splitR t1_b204 0
def t1_k210 : List Nat := [1,1,1,0,1,0,1,1,1,0,1,0,1,1,1,2,0,1,0,2,0,0,0,0,0,0,0,0,1,1,1,0,1,0,1,1,1,0,1,1,0,1,0,2,0,0,0,0,0,0,1,0,1,1,0,1,1,0,1,0,1,1,0,1,0,2,0,1,0,2,0,1,0,0,0,0,0]
theorem t1_s211 : run (leafN1 cdC) 61 t1_b209 t1_k210 = some [] := by decide +kernel
def t1_k212 : List Nat := 1 :: (t1_k207 ++ t1_k210)
theorem t1_n213 : run (leafN1 cdC) 62 t1_b204 t1_k212 = some [] :=
  run_node (leafN1 cdC) 61 t1_b204 0 t1_k207 t1_k210 t1_e205 t1_s208 t1_s211
def t1_b214 : Box := splitR t1_b202 0
def t1_k215 : List Nat := [1,1,1,0,1,1,0,1,1,1,1,0,1,0,1,0,1,1,0,2,0,1,0,2,0,0,0,0,0,0,0,1,0,1,0,1,1,1,1,1,0,1,1,1,0,1,0,2,0,1,0,2,0,0,0,0,0,0,0,0,1,0,1,0,1,1,1,1,1,0,1,1,0,1,1,1,1,0,0,0,0,0,0,0,0,0,1,0,0]
theorem t1_s216 : run (leafN1 cdC) 62 t1_b214 t1_k215 = some [] := by decide +kernel
def t1_k217 : List Nat := 1 :: (t1_k212 ++ t1_k215)
theorem t1_n218 : run (leafN1 cdC) 63 t1_b202 t1_k217 = some [] :=
  run_node (leafN1 cdC) 62 t1_b202 0 t1_k212 t1_k215 t1_e203 t1_n213 t1_s216
def t1_k219 : List Nat := 1 :: (t1_k200 ++ t1_k217)
theorem t1_n220 : run (leafN1 cdC) 64 t1_b1 t1_k219 = some [] :=
  run_node (leafN1 cdC) 63 t1_b1 0 t1_k200 t1_k217 t1_e2 t1_n201 t1_n218
def t2_b1 : Box := root2 cdC
def t2_k2 : List Nat := [1,2,1,1,1,1,1,0,0,0,0,0,0,2,1,1,1,1,1,0,0,0,0,0,0,2,1,1,1,1,1,0,0,0,0,0,0,2,1,1,1,1,0,0,0,0,0,2,1,1,1,0,0,0,0,1,1,1,0,0,0,0,0]
theorem t2_s3 : run (leafN2 cdC) 64 t2_b1 t2_k2 = some [] := by decide +kernel
theorem hpre : (zle zero cdC.ph && zlt zero (zsub cdC.pm cdC.ph) && zle (zadd cdC.pm cdC.ph) S && rootOK0 cdC) = true := by decide +kernel
theorem hc : cellNCheck { cdC with tree1 := t1_k219, tree2 := t2_k2 } = true := by
  have e : cellNCheck { cdC with tree1 := t1_k219, tree2 := t2_k2 } =
      ((zle zero cdC.ph && zlt zero (zsub cdC.pm cdC.ph) && zle (zadd cdC.pm cdC.ph) S && rootOK0 cdC) && runAll (leafN1 cdC) (root1 cdC) t1_k219 && runAll (leafN2 cdC) (root2 cdC) t2_k2) := rfl
  rw [e, hpre, runAll_of_run (leafN1 cdC) (root1 cdC) t1_k219 t1_n220, runAll_of_run (leafN2 cdC) (root2 cdC) t2_k2 t2_s3]; rfl

theorem e0 : toR (zsub cdC.pm cdC.ph) = (4095 / 4096 : ℝ) := by norm_num [cdC, toR, zsub, SN]
theorem e1 : toR (zadd cdC.pm cdC.ph) = (1 / 1 : ℝ) := by norm_num [cdC, toR, zadd, SN]

end RandomSizeStable.Stability.RankCutCert.Pieces.cells_near_one

open RandomSizeStable.Stability.RankCutCert RandomSizeStable.Stability.RankCutCert.Dev in
theorem RandomSizeStable.Stability.RankCutCert.cells_near_one_dev :
    ∃ (n : ℕ) (p0 p1 l0 l1 l2 : Fin n → ℝ) (t0 t1 : Fin n → Fin 9 → ℝ),
      (∀ k, CellOK (p0 k) (p1 k) (l0 k) (l1 k) (l2 k) (t0 k) (t1 k)) ∧
      ∀ p : ℝ, 4095 / 4096 ≤ p → p < 1 → ∃ k, p0 k ≤ p ∧ p ≤ p1 k := by
  have h := RandomSizeStable.Stability.RankCutCert.cellNCheck_ok _ RandomSizeStable.Stability.RankCutCert.Pieces.cells_near_one.hc
  refine ⟨1, fun _ => _, fun _ => _, fun _ => _, fun _ => _, fun _ => _, fun _ => _, fun _ => _,
    fun _ => h, ?_⟩
  intro p hp0 hp1
  refine ⟨0, ?_, ?_⟩
  · show toR (zsub RandomSizeStable.Stability.RankCutCert.Pieces.cells_near_one.cdC.pm RandomSizeStable.Stability.RankCutCert.Pieces.cells_near_one.cdC.ph) ≤ p
    rw [RandomSizeStable.Stability.RankCutCert.Pieces.cells_near_one.e0]; linarith
  · show p ≤ toR (zadd RandomSizeStable.Stability.RankCutCert.Pieces.cells_near_one.cdC.pm RandomSizeStable.Stability.RankCutCert.Pieces.cells_near_one.cdC.ph)
    rw [RandomSizeStable.Stability.RankCutCert.Pieces.cells_near_one.e1]; linarith

theorem solution : type_of% @RandomSizeStable.Stability.RankCutCert.cells_near_one_dev := @RandomSizeStable.Stability.RankCutCert.cells_near_one_dev
