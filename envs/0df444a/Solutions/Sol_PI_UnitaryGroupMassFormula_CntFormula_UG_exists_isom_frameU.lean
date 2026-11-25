-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.CntFormula.UG.exists_isom_frameU
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T11:40:14.6099+00:00
-- url     : https://prove2.me/submissions/503b2bc8-1746-498e-a095-2421b4b976d1

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CountingFormula_ExistsIsomMove
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_ExistsOrthogonalUnitVector
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CountingFormula_ExistsIsomSelfDual
import Theorems.Thm_Formalism_H_dualEquiv_apply
import Theorems.Thm_PI_UnitaryGroupMassFormula_CntFormula_UG_exists_isom_move
import Theorems.Thm_PI_UnitaryGroupMassFormula_CntFormula_UG_exists_of_ref
import Theorems.Thm_PI_UnitaryGroupMassFormula_CntFormula_UG_star_h
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.H.dualEquiv_apply



set_option autoImplicit false
open NumberField Module
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.CntFormula PI.UnitaryGroupMassFormula.CntFormula.UG
open Formalism.HermitianLattices.Ext.L3.WA
variable {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V]
variable {S : Subring K} {h : V →ₗ⋆[K] V →ₗ[K] K}
namespace PI.UnitaryGroupMassFormula.CntFormula.UG
theorem _root_.solution (hS : IsHermSemilocal S) (hs : h.IsSymm) {M : AddSubgroup V}
    (hM : IsSelfDualMod S h M) {n : ℕ} (x : Fin n → V) (hxo : ∀ i j, i ≠ j → h (x i) (x j) = 0)
    (hxu : ∀ i, IsUnitIn S (h (x i) (x i))) :
    ∃ g ∈ Formalism.HermitianLatticesTheory.isom h, ∀ i, g (x i) ∈ M := by
  classical
  have P : ∀ k, k ≤ n → ∃ g ∈ Formalism.HermitianLatticesTheory.isom h, ∀ i : Fin n, i.val < k → g (x i) ∈ M := by
    intro k
    induction k with
    | zero => intro _; exact ⟨1, one_mem _, fun i hi => absurd hi (Nat.not_lt_zero _)⟩
    | succ k ih =>
      intro hk
      obtain ⟨g, hg, hgM⟩ := ih (by omega)
      have hg' : ∀ a b, h (g a) (g b) = h a b := hg
      have hne : ∀ i : Fin n, i.val < k → i ≠ ⟨k, hk⟩ := by
        intro i hi e
        rw [e] at hi
        exact lt_irrefl _ hi
      let y : {i : Fin n // i.val < k} → V := fun i => g (x i.1)
      have hyo : ∀ i j : {i : Fin n // i.val < k}, i ≠ j → h (y i) (y j) = 0 := by
        intro i j hij
        simp only [y]
        rw [hg']
        exact hxo _ _ (fun e => hij (Subtype.ext e))
      have hyu : ∀ i : {i : Fin n // i.val < k}, IsUnitIn S (h (y i) (y i)) := by
        intro i
        simp only [y]
        rw [hg']
        exact hxu _
      have hyM : ∀ i : {i : Fin n // i.val < k}, y i ∈ M := fun i => hgM i.1 i.2
      have hu := hxu ⟨k, hk⟩
      have hus : star (h (x ⟨k, hk⟩) (x ⟨k, hk⟩)) = h (x ⟨k, hk⟩) (x ⟨k, hk⟩) := star_h hs _ _
      have hrr : h (g (x ⟨k, hk⟩)) (g (x ⟨k, hk⟩)) = h (x ⟨k, hk⟩) (x ⟨k, hk⟩) := hg' _ _
      have hrx : ∀ i : {i : Fin n // i.val < k}, h (y i) (g (x ⟨k, hk⟩)) = 0 := by
        intro i
        simp only [y]
        rw [hg']
        exact hxo _ _ (hne i.1 i.2)
      obtain ⟨z, hzM, hzz, hzo⟩ := exists_of_ref hS hs hM y hyo hyu hyM hu hus hrr hrx
      obtain ⟨τ, hτ, hτr, hτfix⟩ := exists_isom_move hS hs hu.1 hus hrr hzz
      refine ⟨τ * g, mul_mem hτ hg, fun i hi => ?_⟩
      show τ (g (x i)) ∈ M
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with h1 | h1
      · rw [hτfix]
        · exact hgM i h1
        · rw [hg']
          exact hxo _ _ (fun e => hne i h1 e.symm)
        · rw [← star_h hs]
          have := hzo ⟨i, h1⟩
          simp only [y] at this
          rw [this, star_zero]
      · have : i = ⟨k, hk⟩ := Fin.ext h1
        rw [this, hτr]
        exact hzM
  obtain ⟨g, hg, hgM⟩ := P n le_rfl
  exact ⟨g, hg, fun i => hgM i i.isLt⟩
end PI.UnitaryGroupMassFormula.CntFormula.UG
