-- Prove2me | solution 1 for PI.LevelKSplit.W.Split.splitK_level
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:22:49.792956+00:00
-- url     : https://prove2.me/submissions/b00569c8-d6ce-4c55-bf46-12c15977e990

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_RatVMemSpan
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_LevelSAllOfExistSMeasKf
import Theorems.Thm_PI_LevelKSplit_W_Split_stab_of
import Theorems.Thm_PI_LevelKSplit_W_Glob_H_fix_e
import Theorems.Thm_PI_LevelKSplit_W_Glob_H_perp
import Theorems.Thm_PI_LevelKSplit_W_Glob_hR_ratV_left
import Theorems.Thm_PI_LevelKSplit_W_Glob_lin_fix_span
import Theorems.Thm_PI_LevelKSplit_W_Glob_mem_Kf
import Theorems.Thm_PI_LevelKSplit_W_Glob_spanR_univ


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.LevelKSplit PI.LevelKSplit.W PI.LevelKSplit.W.Split
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain PI.LevelKSplit
  PI.LevelKSplit.W.Glob
open scoped TensorProduct
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E}
namespace PI.LevelKSplit.W.Split
theorem _root_.solution : SplitK F E σ n J := by
  intro hJ hinv r P T hP ΛX ΛW ΛY hA m h hm hh hmh
  have hNm : ∀ m' : HA (Af F) σ J, m' ∈ Nsub (Af F) σ J P → ∀ y, InXperp (Af F) σ J P y →
      lin (Af F) σ J m' y - y ∈ spanR (F := F) (Af F) P.e Set.univ :=
    fun m' hm' y hy => hm'.2 y hy
  have hperp : ∀ w ∈ ΛW, ∀ k : HA (Af F) σ J, k ∈ Hsub (Af F) σ J P →
      InXperp (Af F) σ J P (lin (Af F) σ J k (ratV (F := F) (Af F) w)) := by
    intro w hw k hk a
    rw [hR_ratV_left]
    exact (H_perp P k hk w (hA.2.2 w hw) a).1
  have h1 : ∀ w ∈ ΛW, lin (Af F) σ J (m * h) (ratV (F := F) (Af F) w) -
      lin (Af F) σ J h (ratV (F := F) (Af F) w) ∈ spanR (F := F) (Af F) P.e Set.univ := by
    intro w hw
    rw [lin_mul]
    exact hNm m hm _ (hperp w hw h hh)
  have h2 : ∀ w ∈ ΛW, lin (Af F) σ J (m * h)⁻¹ (ratV (F := F) (Af F) w) -
      lin (Af F) σ J h⁻¹ (ratV (F := F) (Af F) w) ∈ spanR (F := F) (Af F) P.e Set.univ := by
    intro w hw
    rw [mul_inv_rev, lin_mul, ← map_sub]
    have hp := hperp w hw 1 (Subgroup.one_mem _)
    rw [lin_one] at hp
    have hx := hNm m⁻¹ (Subgroup.inv_mem _ hm) _ hp
    rw [lin_fix_span h⁻¹ P.e (H_fix_e P _ (Subgroup.inv_mem _ hh)) _ (by rwa [spanR_univ] at hx)]
    exact hx
  rw [mem_Kf]
  intro v x
  have s1 := stab_of hJ hinv P T hP ΛX ΛW ΛY hA h (m * h) hh hmh h1 v
  have s2 := stab_of hJ hinv P T hP ΛX ΛW ΛY hA h⁻¹ (m * h)⁻¹ (Subgroup.inv_mem _ hh)
    (Subgroup.inv_mem _ hmh) h2 v
  constructor
  · exact s1 x
  · intro hx
    have := s2 _ hx
    rwa [map_inv, map_inv, Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec] at this
end PI.LevelKSplit.W.Split
