-- Prove2me | solution 1 for PI.LevelKSplit.W.NCL.levG_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:53:20.59006+00:00
-- url     : https://prove2.me/submissions/933e1e12-f6eb-422a-af48-23f80c2e89b8

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_LevLSubPerp
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_NCDefs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_ToMatrixLin
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_LeviInfUnipotentEqOne
import Theorems.Thm_PI_LevelKSplit_W_NCL_uT_apply
import Theorems.Thm_PI_LevelKSplit_W_NCL_lin_levG
import Theorems.Thm_PI_LevelKSplit_W_NCL_lin_levG_inv
import Theorems.Thm_PI_LevelKSplit_W_Glob_spanR_univ
import Theorems.Thm_PI_LevelKSplit_W_NCL_levL_alt
import Theorems.Thm_PI_LevelKSplit_W_NCL_levL_e
import Theorems.Thm_PI_LevelKSplit_W_NCL_levL_f
import Theorems.Thm_PI_LevelKSplit_W_NCL_levL_sub_perp
import Theorems.Thm_PI_LevelKSplit_W_SemiA_datR_hyp


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.LevelKSplit PI.LevelKSplit.W PI.LevelKSplit.W.NCL
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub PI.LevelKSplit.W.NC PI.VolSemiDirect.W
open scoped TensorProduct
variable {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
  (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) {r : ℕ} (P : Frame E M r) (T : F)
variable {R σ J P T}
variable (R σ J P)
variable {R σ J P}
variable (hσσ : ∀ x, σ (σ x) = x) (hJ : IsHermND σ J) (hP : P.IsStd σ J T)
include hσσ hJ hP
namespace PI.LevelKSplit.W.NCL
theorem _root_.solution (g : HA R σ J) : levG hσσ hJ hP g ∈ Asub R σ J P := by
  have H : (datR R σ J P T).Hyp := datR_hyp hσσ hJ hP
  have hfs : ∀ (U W : Matrix (Fin r) (Fin r) (R ⊗[F] E)) (b : Fin r),
      levL (datR R σ J P T) U W (ratV (F := F) R (P.f b)) ∈ spanR (F := F) R P.f Set.univ :=
    fun U W b => by
      show levL (datR R σ J P T) U W ((datR R σ J P T).f b) ∈ _
      rw [levL_f H]
      exact Submodule.sum_mem _ fun d _ => Submodule.smul_mem _ _
        (Submodule.subset_span ⟨d, Set.mem_univ _, rfl⟩)
  refine ⟨⟨fun b => ?_, fun v hv => ?_⟩, fun w hw => ?_, fun b => ?_, fun b => ?_⟩
  · rw [lin_levG]
    show levL (datR R σ J P T) _ _ ((datR R σ J P T).e b) - (datR R σ J P T).e b ∈ _
    rw [levL_e H]
    have e1 : ∑ a, uT R σ J P g a b • (datR R σ J P T).e a - (datR R σ J P T).e b =
        ∑ a, (if a < b then uT R σ J P g a b else 0) • (datR R σ J P T).e a := by
      have eb : (datR R σ J P T).e b =
          ∑ a, (if a = b then (1 : R ⊗[F] E) else 0) • (datR R σ J P T).e a := by simp
      rw [eb, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [← sub_smul]
      congr 1
      rw [uT_apply]
      rcases lt_trichotomy a b with h | h | h
      · simp [h, h.ne]
      · subst h; simp
      · simp [not_lt.2 h.le, h.ne']
    rw [e1]
    refine Submodule.sum_mem _ fun a _ => ?_
    split_ifs with h
    · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, h, rfl⟩)
    · rw [zero_smul]; exact Submodule.zero_mem _
  · rw [lin_levG, PI.LevelKSplit.W.Glob.spanR_univ]
    exact levL_sub_perp H _ _ hv
  · rw [lin_levG]
    exact levL_alt H _ _ hw.2 hw.1
  · rw [lin_levG]; exact hfs _ _ b
  · rw [lin_levG_inv]; exact hfs _ _ b
end PI.LevelKSplit.W.NCL
