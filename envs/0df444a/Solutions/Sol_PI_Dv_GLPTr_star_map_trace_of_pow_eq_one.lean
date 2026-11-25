-- Prove2me | solution 1 for PI.Dv.GLPTr.star_map_trace_of_pow_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T09:38:42.704994+00:00
-- url     : https://prove2.me/submissions/34bdd81e-4c93-4bdc-be8e-b54876b17aef

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_SameFormAllLevels
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProjectionLattices_StarMapTraceOfPowEqOne
import Theorems.Thm_PI_Dv_GLPTr_star_trace_of_pow_eq_one

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.Dv PI.Dv.GLPTr
open Matrix
open scoped ComplexOrder
namespace PI.Dv.GLPTr
theorem _root_.solution {K : Type} [Field K] {W : Type} [AddCommGroup W] [Module K W]
    [FiniteDimensional K W] (σ : K →+* ℂ) (f : Module.End K W) (n : ℕ) (hn : 0 < n) (hf : f ^ n = 1) :
    star (σ (LinearMap.trace K W f)) = σ (LinearMap.trace K W (f ^ (n - 1))) := by
  classical
  let b := Module.finBasis K W
  obtain ⟨A, hAdef⟩ : ∃ A, LinearMap.toMatrix b b f = A := ⟨_, rfl⟩
  have hpow : ∀ k, LinearMap.toMatrix b b (f ^ k) = A ^ k := fun k => by
    rw [← LinearMap.toMatrix_pow, hAdef]
  have hmap : ∀ B : Matrix (Fin (Module.finrank K W)) (Fin (Module.finrank K W)) K,
      σ B.trace = (B.map σ).trace := fun B => AddMonoidHom.map_trace σ B
  have hmp : ∀ k, (A ^ k).map σ = (A.map σ) ^ k := fun k => RingHom.map_pow σ.mapMatrix A k
  rw [LinearMap.trace_eq_matrix_trace K b, LinearMap.trace_eq_matrix_trace K b, hAdef, hpow, hmap,
    hmap, hmp]
  refine star_trace_of_pow_eq_one (A.map σ) n hn ?_
  rw [← hmp, ← hpow, hf, LinearMap.toMatrix_one]
  exact Matrix.map_one σ (map_zero σ) (map_one σ)
end PI.Dv.GLPTr
