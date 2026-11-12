-- Prove2me | solution 1 for OddOrder.Isaacs.Ch07.card_sl2_mul_units_eq_card_gl2_zmod_prime
-- status  : ACCEPTED   (prove)
-- author  : @burkh4rt
-- created : 2026-11-12T05:47:31.021905+00:00
-- url     : https://prove2.me/submissions/0c89df3d-ea2e-4ae1-869c-978745ac3906

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

theorem _root_.solution
    {p : ℕ} [Fact p.Prime] :
    Nat.card (Matrix.SpecialLinearGroup (Fin 2) (ZMod p)) * (p - 1) =
      Nat.card (Matrix.GeneralLinearGroup (Fin 2) (ZMod p)) := by
  let detGL : Matrix.GeneralLinearGroup (Fin 2) (ZMod p) →* (ZMod p)ˣ :=
    Matrix.GeneralLinearGroup.det
  let toGLSL : Matrix.SpecialLinearGroup (Fin 2) (ZMod p) →*
      Matrix.GeneralLinearGroup (Fin 2) (ZMod p) :=
    Matrix.SpecialLinearGroup.toGL
  have htoGL_range_eq_ker : toGLSL.range = detGL.ker := by
    ext g
    constructor
    · rintro ⟨s, rfl⟩
      simp [detGL, toGLSL]
    · intro hg
      rw [MonoidHom.mem_ker] at hg
      have hgdet : ((g : Matrix.GeneralLinearGroup (Fin 2) (ZMod p)) :
          Matrix (Fin 2) (Fin 2) (ZMod p)).det = 1 := by
        have := congrArg Units.val hg
        simpa [detGL, Matrix.GeneralLinearGroup.val_det_apply] using this
      refine ⟨⟨((g : Matrix.GeneralLinearGroup (Fin 2) (ZMod p)) :
        Matrix (Fin 2) (Fin 2) (ZMod p)), hgdet⟩, ?_⟩
      exact Units.ext rfl
  have htop_map_eq_range :
      (⊤ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) (ZMod p))).map toGLSL =
        toGLSL.range := by
    ext g
    simp [toGLSL]
  have hcard_SL_range :
      Nat.card (Matrix.SpecialLinearGroup (Fin 2) (ZMod p)) =
        Nat.card toGLSL.range := by
    calc
      Nat.card (Matrix.SpecialLinearGroup (Fin 2) (ZMod p))
          = Nat.card (⊤ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) (ZMod p))) := by
            rw [Subgroup.card_top]
      _ = Nat.card ((⊤ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) (ZMod p))).map
            toGLSL) := by
            exact Nat.card_congr
              (Subgroup.equivMapOfInjective
                (⊤ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) (ZMod p))) toGLSL
                Matrix.SpecialLinearGroup.toGL_injective).toEquiv
      _ = Nat.card toGLSL.range := by
            rw [htop_map_eq_range]
  have hcard_SL_ker :
      Nat.card (Matrix.SpecialLinearGroup (Fin 2) (ZMod p)) =
        Nat.card detGL.ker := by
    rw [hcard_SL_range, htoGL_range_eq_ker]
  have hdet_range_top : detGL.range = ⊤ := by
    ext u
    constructor
    · intro _
      trivial
    · intro _
      let A : Matrix (Fin 2) (Fin 2) (ZMod p) := !![(u : ZMod p), 0; 0, 1]
      have hdetA_ne : A.det ≠ 0 := by
        simp [A, Matrix.det_fin_two, u.ne_zero]
      refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero A hdetA_ne, ?_⟩
      ext
      simp [detGL, A, Matrix.det_fin_two]
  have hcard_range : Nat.card detGL.range = p - 1 := by
    rw [hdet_range_top, Subgroup.card_top, Nat.card_eq_fintype_card, Fintype.card_units,
      ZMod.card]
  have hker_mul_range :
      Nat.card detGL.ker * Nat.card detGL.range =
        Nat.card (Matrix.GeneralLinearGroup (Fin 2) (ZMod p)) := by
    rw [← Subgroup.index_ker detGL]
    exact Subgroup.card_mul_index detGL.ker
  calc
    Nat.card (Matrix.SpecialLinearGroup (Fin 2) (ZMod p)) * (p - 1)
        = Nat.card detGL.ker * Nat.card detGL.range := by
          rw [hcard_SL_ker, hcard_range]
    _ = Nat.card (Matrix.GeneralLinearGroup (Fin 2) (ZMod p)) := hker_mul_range

end OddOrder.Isaacs.Ch07
