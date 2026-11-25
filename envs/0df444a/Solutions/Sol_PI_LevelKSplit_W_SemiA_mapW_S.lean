-- Prove2me | solution 1 for PI.LevelKSplit.W.SemiA.mapW_S
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:13:59.136109+00:00
-- url     : https://prove2.me/submissions/33d5d63c-36e2-42aa-85de-11331eb93712

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_HermitianIsotropicProjComplement
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_FundamentalEquivalence_LevelIntersectParabolic
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_SemiAlg
import Theorems.Thm_PI_LevelKSplit_W_SemiA_spanR_le
import Theorems.Thm_PI_LevelKSplit_W_SemiA_stabilizer_fixes_tail_coords
import Theorems.Thm_PI_LevelKSplit_W_SemiA_mapX_S
import Theorems.Thm_PI_LevelKSplit_W_SemiA_uni_lin

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.LevelKSplit PI.LevelKSplit.W PI.LevelKSplit.W.SemiA
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub
open scoped TensorProduct
variable {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
  (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) {r : ℕ} (P : Frame E M r) (T : F)
variable {R σ J P T}
namespace PI.LevelKSplit.W.SemiA
theorem _root_.solution {g : HA R σ J} (hg : g ∈ Ssub R σ J P) : (datR R σ J P T).MapW (lin R σ J g) := by
  intro w hW
  obtain ⟨hWe, -, hWz⟩ := hW
  have hadd : ∀ u v, (datR R σ J P T).h (u + v) w = (datR R σ J P T).h u w + (datR R σ J P T).h v w := by
    intro u v
    simp only [SemiG.Dat.h, Formalism.UG.hform, Pi.add_apply, map_add, add_mul, Finset.sum_add_distrib]
  have hsmul : ∀ (c : R ⊗[F] E) u, (datR R σ J P T).h (c • u) w =
      (datR R σ J P T).σA c * (datR R σ J P T).h u w := by
    intro c u
    simp only [SemiG.Dat.h, Formalism.UG.hform, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum, mul_assoc]
  have hzero : (datR R σ J P T).h 0 w = 0 := by
    simp [SemiG.Dat.h, Formalism.UG.hform]
  have hspan : ∀ v ∈ Submodule.span (R ⊗[F] E) (Set.range (datR R σ J P T).e),
      (datR R σ J P T).h v w = 0 := by
    intro v hv
    induction hv using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨a, rfl⟩ := hx
      exact hWe a
    | zero => exact hzero
    | add x y _ _ hx hy => rw [hadd, hx, hy, add_zero]
    | smul c x _ hx => rw [hsmul, hx, mul_zero]
  have hinv : g⁻¹ ∈ Ssub R σ J P := inv_mem hg
  have hgi : ∀ u, lin R σ J g (lin R σ J g⁻¹ u) = u := by
    intro u
    have h0 := lin_inv_lin (R := R) (σ := σ) (J := J) g⁻¹ u
    rwa [inv_inv] at h0
  have hu : ∀ u, (datR R σ J P T).h u (lin R σ J g w) = (datR R σ J P T).h (lin R σ J g⁻¹ u) w := by
    intro u
    conv_lhs => rw [← hgi u]
    exact uni_lin (P := P) (T := T) g _ _
  refine ⟨fun b => ?_, ?_⟩
  · rw [hu]
    exact hspan _ (mapX_S (T := T) hinv b)
  · rw [hu]
    show (datR R σ J P T).h (lin R σ J g⁻¹ (ratV (F := F) R P.z)) w = 0
    have hWz' : (datR R σ J P T).h (ratV (F := F) R P.z) w = 0 := hWz
    have h2 := hspan _ (spanR_le (σ := σ) (J := J) (T := T) _ (stabilizer_fixes_tail_coords hinv))
    rw [← sub_add_cancel (lin R σ J g⁻¹ (ratV (F := F) R P.z)) (ratV (F := F) R P.z), hadd, h2, hWz', add_zero]
end PI.LevelKSplit.W.SemiA
