-- Prove2me | solution 1 for OddOrder.Isaacs.Ch07.sl2_unique_involution
-- status  : ACCEPTED   (prove)
-- author  : @burkh4rt
-- created : 2026-11-12T05:47:47.354912+00:00
-- url     : https://prove2.me/submissions/fd4086df-1334-4042-80b8-77537717df0f

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Isaacs/Ch07_ThompsonSubgroup/S7A1_JpGL2p.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_GroupTheory_OmegaSubgroup
import Definitions.Def_OddOrder_GroupTheory_ThompsonSubgroup
import Definitions.Def_OddOrder_Isaacs_Ch02_Subnormality_Theorem211Wielandt
import Definitions.Def_OddOrder_Isaacs_Ch04_Commutators_Main_CommutatorBasics
import Definitions.Def_OddOrder_Isaacs_Ch04_Commutators_Main_ThreeSubgroupsCoprime
import Definitions.Def_OddOrder_Isaacs_Ch04_Commutators_Main_BaerTrick
import Definitions.Def_OddOrder_Isaacs_Ch04_Commutators_Main_ChainNilpotent
import Definitions.Def_OddOrder_Isaacs_Ch04_Commutators_ForwardFromCh03
import Definitions.Def_OddOrder_Isaacs_Ch04_Commutators_Main_ThreeSubgroups
import Definitions.Def_OddOrder_Isaacs_Ch05_Transfer_Main
import Definitions.Def_OddOrder_Isaacs_Ch06_FrobeniusActions_Main
import Definitions.Def_OddOrder_Isaacs_Ch07_ThompsonSubgroup_S7A1_JpGL2p
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Module.ZMod
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.GroupTheory.FiniteAbelian.Basic
import Mathlib.GroupTheory.IndexNormal
import Mathlib.GroupTheory.PGroup
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.LinearCombination

-- ===== OddOrder/Isaacs/Ch07_ThompsonSubgroup/S7A1_JpGL2p.lean =====
namespace OddOrder.Isaacs.Ch07

open scoped commutatorElement

open scoped Pointwise

variable {G : Type*} [Group G]

/-- **Isaacs Lem 7.4** (mmd L3765): `F` field, characteristic ≠ 2 ⇒ `SL(2, F)`
の唯一 involution は `-1` (= `-I`).

Isaacs 原本の "`q` odd" は本質的に `char F ≠ 2` (= `(2 : F) ≠ 0`) の特殊化.
`F = ZMod q` (`q` 奇素数冪) では `(2 : ZMod q) ≠ 0`.

**proof 戦略**: `M := ↑ₘt`, `M² = I`, `det M = 1`. 4 entries `a = M 0 0`,
`b = M 0 1`, `c = M 1 0`, `d = M 1 1` で:

* `M² = I` の (0,1) entry: `b(a+d) = 0`.
* `M² = I` の (1,0) entry: `c(a+d) = 0`.
* `M² = I` の (0,0) entry: `a² + bc = 1`.
* `M² = I` の (1,1) entry: `bc + d² = 1`.
* `det M = 1`: `ad - bc = 1`.

`a + d = 0` の場合: `det + (0,0)entry` から `a² - 1 = -1 - a² + (a² + bc) - bc - 0 = -1`,
即ち `2 = 0`, char ≠ 2 と矛盾. 従って `a + d ≠ 0`, よって `b = c = 0`.
`a² = 1` かつ `a · d = 1`, `a = d` で `a = ±1`. `t ≠ 1` から `a = -1`, `d = -1`. -/
theorem _root_.solution
    {F : Type*} [Field F] (h2 : (2 : F) ≠ 0)
    {t : Matrix.SpecialLinearGroup (Fin 2) F}
    (ht_sq : t ^ 2 = 1) (ht_ne : t ≠ 1) :
    t = -1 := by
  -- 行列レベルで議論する: M := t.val
  set M : Matrix (Fin 2) (Fin 2) F := t.val with hM_def
  -- 1) M * M = I (from t ^ 2 = 1)
  have hM_sq : M * M = 1 := by
    have h := congrArg Subtype.val ht_sq
    simpa [sq, hM_def, Matrix.SpecialLinearGroup.coe_mul,
           Matrix.SpecialLinearGroup.coe_one] using h
  -- 2) det M = 1
  have hM_det : M.det = 1 := t.property
  -- 3) 4 entries
  set a := M 0 0
  set b := M 0 1
  set c := M 1 0
  set d := M 1 1
  -- det equation
  have hdet : a * d - b * c = 1 := by
    have h := Matrix.det_fin_two M
    rw [hM_det] at h
    linear_combination -h
  -- M² entries (from M * M = 1)
  have h00 : a * a + b * c = 1 := by
    have h := congrArg (fun M : Matrix (Fin 2) (Fin 2) F => M 0 0) hM_sq
    simpa [Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply] using h
  have h01 : a * b + b * d = 0 := by
    have h := congrArg (fun M : Matrix (Fin 2) (Fin 2) F => M 0 1) hM_sq
    simpa [Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply] using h
  have h10 : c * a + d * c = 0 := by
    have h := congrArg (fun M : Matrix (Fin 2) (Fin 2) F => M 1 0) hM_sq
    simpa [Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply] using h
  have h11 : c * b + d * d = 1 := by
    have h := congrArg (fun M : Matrix (Fin 2) (Fin 2) F => M 1 1) hM_sq
    simpa [Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply] using h
  -- b * (a + d) = 0, c * (a + d) = 0
  have hb_ad : b * (a + d) = 0 := by linear_combination h01
  have hc_ad : c * (a + d) = 0 := by linear_combination h10
  -- a + d ≠ 0 (would imply 2 = 0)
  have had_ne : a + d ≠ 0 := by
    intro had
    apply h2
    linear_combination -hdet - h00 + a * had
  -- a + d ≠ 0 ⇒ b = c = 0
  have hb_zero : b = 0 :=
    (mul_eq_zero.mp hb_ad).resolve_right had_ne
  have hc_zero : c = 0 :=
    (mul_eq_zero.mp hc_ad).resolve_right had_ne
  -- After b = c = 0: a * d = 1, a² = 1
  have had_eq_one : a * d = 1 := by linear_combination hdet + b * hc_zero
  have ha_sq : a * a = 1 := by linear_combination h00 - b * hc_zero
  -- a ≠ 0 (since a² = 1)
  have ha_ne : a ≠ 0 := by
    intro hae
    apply one_ne_zero (α := F)
    linear_combination -ha_sq + a * hae
  -- d = a
  have hd_eq_a : d = a := by
    have h : a * (d - a) = 0 := by linear_combination had_eq_one - ha_sq
    have hda : d - a = 0 := (mul_eq_zero.mp h).resolve_left ha_ne
    linear_combination hda
  -- (a - 1) * (a + 1) = a² - 1 = 0
  have h_factor : (a - 1) * (a + 1) = 0 := by linear_combination ha_sq
  rcases mul_eq_zero.mp h_factor with h_pos | h_neg
  · -- a = 1 case: t = I, contradicts t ≠ 1
    exfalso
    apply ht_ne
    have ha_one : a = 1 := by linear_combination h_pos
    have hd_one : d = 1 := by rw [hd_eq_a]; exact ha_one
    have hM_eq : M = !![(1 : F), 0; 0, 1] := by
      ext i j
      fin_cases i <;> fin_cases j
      · exact ha_one
      · exact hb_zero
      · exact hc_zero
      · exact hd_one
    have hone_val : ((1 : Matrix.SpecialLinearGroup (Fin 2) F).val
        : Matrix (Fin 2) (Fin 2) F) = !![(1 : F), 0; 0, 1] := by
      rw [Matrix.SpecialLinearGroup.coe_one]
      ext i j
      fin_cases i <;> fin_cases j <;> simp
    exact Subtype.ext (hM_eq.trans hone_val.symm)
  · -- a = -1 case: t = -I
    have ha_neg : a = -1 := by linear_combination h_neg
    have hd_neg : d = -1 := by rw [hd_eq_a]; exact ha_neg
    have hM_eq : M = !![(-1 : F), 0; 0, -1] := by
      ext i j
      fin_cases i <;> fin_cases j
      · exact ha_neg
      · exact hb_zero
      · exact hc_zero
      · exact hd_neg
    have hneg_val : ((-1 : Matrix.SpecialLinearGroup (Fin 2) F).val
        : Matrix (Fin 2) (Fin 2) F) = !![(-1 : F), 0; 0, -1] := by
      rw [Matrix.SpecialLinearGroup.coe_neg, Matrix.SpecialLinearGroup.coe_one]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.neg_apply]
    exact Subtype.ext (hM_eq.trans hneg_val.symm)

end OddOrder.Isaacs.Ch07
