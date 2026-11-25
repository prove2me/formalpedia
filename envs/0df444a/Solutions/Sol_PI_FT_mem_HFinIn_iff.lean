-- Prove2me | solution 1 for PI.FT.mem_HFinIn_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T09:44:15.754668+00:00
-- url     : https://prove2.me/submissions/4481ae32-e3bb-4b2f-8603-d6ab8431d908

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FrameTransport_StepTransl
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FrameTransport_MemHFinInIff
import Theorems.Thm_PI_FT_map_one_incl
import Theorems.Thm_PI_FT_cT_map_incl

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.FT
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Matrix
open scoped TensorProduct
variable {F E : Type} [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) {M : ℕ}
variable (R : Type) [CommRing R] [Algebra F R]
namespace PI.FT
theorem _root_.solution (hinj : Function.Injective (inclR (F := F) (E := E) R))
    {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (g : HA R σ J) :
    toHR g ∈ HFinIn R σ J ↔
      (∃ a : Matrix (Fin n) (Fin n) E, ((HA.mat R σ J g : GL (Fin n) (R ⊗[F] E)) :
          Matrix (Fin n) (Fin n) (R ⊗[F] E)) = a.map (inclR (F := F) (E := E) R)) ∧
      (∃ a : Matrix (Fin n) (Fin n) E, (((HA.mat R σ J g)⁻¹ : GL (Fin n) (R ⊗[F] E)) :
          Matrix (Fin n) (Fin n) (R ⊗[F] E)) = a.map (inclR (F := F) (E := E) R)) := by
  simp only [HFinIn]
  rw [Subgroup.mem_subgroupOf]
  simp only [HFin, Subgroup.mem_map, Formalism.UG.bc, Formalism.UG.UJ, toHR, HA.mat]
  have inj : Function.Injective (fun M : Matrix (Fin n) (Fin n) E => M.map (inclR (F := F) (E := E) R)) :=
    fun M N h => Matrix.ext fun i j => hinj (by simpa using congrArg (fun P => P i j) h)
  constructor
  · rintro ⟨y, -, hy⟩
    rw [← hy]
    exact ⟨⟨(y : Matrix (Fin n) (Fin n) E), rfl⟩, ⟨((y⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E), rfl⟩⟩
  · rintro ⟨⟨a, ha⟩, ⟨a', ha'⟩⟩
    have h1 : a * a' = 1 := by
      apply inj
      show (a * a').map (inclR (F := F) (E := E) R) = (1 : Matrix (Fin n) (Fin n) E).map (inclR (F := F) (E := E) R)
      rw [Matrix.map_mul, ← ha, ← ha', Units.mul_inv, map_one_incl]
    have h2 : a' * a = 1 := by
      apply inj
      show (a' * a).map (inclR (F := F) (E := E) R) = (1 : Matrix (Fin n) (Fin n) E).map (inclR (F := F) (E := E) R)
      rw [Matrix.map_mul, ← ha, ← ha', Units.inv_mul, map_one_incl]
    refine ⟨⟨a, a', h1, h2⟩, ?_, Units.ext ha.symm⟩
    show Formalism.UG.cT (σ : E →+* E) a * J * a = J
    apply inj
    simp only [Matrix.map_mul, cT_map_incl, ← ha]
    have hg := g.2
    simp only [HA, HR, Formalism.UG.UJ, JR, Subgroup.mem_mk, Submonoid.mem_mk, Subsemigroup.mem_mk,
      Set.mem_setOf_eq] at hg
    exact hg
end PI.FT
