-- Prove2me | solution 1 for PI.KerTens.W.slice_th
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T09:57:24.219053+00:00
-- url     : https://prove2.me/submissions/a919bf9f-b04d-4d21-9dc2-c6f52872f18c

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_KerTens
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TensorSpanning_MatHHOne
import Theorems.Thm_PI_KerTens_W_blk_apply
import Theorems.Thm_PI_KerTens_W_upd_eq
import Theorems.Thm_PI_KerTens_W_upd_add
import Theorems.Thm_PI_KerTens_W_formV_blk
import Theorems.Thm_PI_KerTens_W_matH_hOne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate
open PI PI.KerTens PI.KerTens.W
open Formalism.L2.Th1.H (Sesq matH alphaQ qOf opU Th fixedBy)
namespace PI.KerTens.W
theorem _root_.solution (c : ℝ) (L : PeriodPair) {n : Type} [Fintype n] [DecidableEq n] (ΛM : AddSubgroup (n → ℂ))
    {N N' : ℕ} (F : (n → Fin N' → Fin N → ℂ) → ℂ)
    (hF : F ∈ Th (formV (Formalism.L2.Th1.F.area L) n N N') (alphaQ c (formV (Formalism.L2.Th1.F.area L) n N N'))
      (powLat ΛM N N'))
    (z : n → Fin N' → Fin N → ℂ) (b : Fin N' × Fin N) :
    (fun t => F (upd z b t)) ∈ Th (matH (hOne L n)) (alphaQ c (matH (hOne L n))) ΛM := by
  obtain ⟨hFa, hFf⟩ := hF
  have hA : AnalyticOnNhd ℂ (fun t : n → ℂ => upd z b t) Set.univ := by
    intro t _
    rw [show (fun t : n → ℂ => upd z b t) =
        fun t => (fun τ i j => if (i, j) = b then 0 else z τ i j) + blk b t from
      funext fun t => upd_eq z b t]
    exact analyticAt_const.add ((LinearMap.toContinuousLinearMap (blk b)).analyticAt t)
  refine ⟨hFa.comp hA (Set.mapsTo_univ _ _), ?_⟩
  intro x hx t
  have hX : blk b x ∈ powLat ΛM N N' := by
    intro i j
    by_cases h : (i, j) = b
    · have e : (fun τ => blk b x τ i j) = x := funext fun τ => by simp [blk_apply, h]
      rw [e]
      exact hx
    · have e : (fun τ => blk b x τ i j) = 0 := funext fun τ => by simp [blk_apply, h]
      rw [e]
      exact ΛM.zero_mem
  have key := hFf (blk b x) hX (upd z b t)
  simp only [opU] at key ⊢
  have e2 : formV (Formalism.L2.Th1.F.area L) n N N' (upd z b t) (blk b x) = matH (hOne L n) t x := by
    rw [formV_blk, matH_hOne]
    simp [upd]
  have e3 : formV (Formalism.L2.Th1.F.area L) n N N' (blk b x) (blk b x) = matH (hOne L n) x x := by
    rw [formV_blk, matH_hOne]
    simp [blk_apply]
  have e4 : alphaQ c (formV (Formalism.L2.Th1.F.area L) n N N') (blk b x) =
      alphaQ c (matH (hOne L n)) x := by
    simp only [alphaQ, qOf, e3]
  rw [upd_add, e2, e3, e4] at key
  exact key
end PI.KerTens.W
