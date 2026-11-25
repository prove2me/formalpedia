-- Prove2me | solution 1 for PI.LPI.plLocal_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:13:49.121849+00:00
-- url     : https://prove2.me/submissions/4e00744b-8fd6-49e6-9104-4bfe80d072fd

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelProductIndex_PrVSumTmul
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelProductIndex_SingleApply
import Theorems.Thm_PI_LPI_prV_sigR
import Theorems.Thm_PI_LPI_prV_inclE
import Theorems.Thm_PI_LPI_lift_lat
import Theorems.Thm_PI_LPI_bc_mulVec


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix NumberField IsDedekindDomain
open scoped TensorProduct RestrictedProduct
noncomputable section
open PI PI.LPI
open Formalism.UG
namespace PI.LPI
theorem _root_.solution (hG : PLGen) (hD : PLDown) : PLLocal := by
  intro F E _ _ _ _ _ n σ J Lb hfin g hg v
  have fwd : ∀ h ∈ levelAfL σ J Lb, ∀ x ∈ latV v Lb,
      ((bc (prV (E := E) v) h : GL (Fin n) (E ⊗[F] v.adicCompletion F)) :
        Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) *ᵥ x ∈ latV v Lb := by
    intro h hh x hx
    obtain ⟨y, hy, rfl⟩ := lift_lat hG Lb hfin v x hx
    rw [← bc_mulVec]
    exact hD F E n Lb v _ (((Subgroup.mem_inf.1 hh).2 y).1 hy)
  refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
  · have hU := (Subgroup.mem_inf.1 hg).1
    change cT (sigR σ (FiniteAdeleRing (𝓞 F) F)) (g : Matrix (Fin n) (Fin n) _) *
      J.map (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) * (g : Matrix (Fin n) (Fin n) _) =
      J.map (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) at hU
    change cT (sigR σ (v.adicCompletion F)) ((g : Matrix (Fin n) (Fin n) _).map (prV (E := E) v)) *
      J.map (inclE (F := F) (v.adicCompletion F)) * (g : Matrix (Fin n) (Fin n) _).map (prV (E := E) v) =
      J.map (inclE (F := F) (v.adicCompletion F))
    have e2 : J.map (inclE (F := F) (v.adicCompletion F)) =
        (J.map (inclE (F := F) (FiniteAdeleRing (𝓞 F) F))).map (prV (E := E) v) := by
      ext i j; simp [prV_inclE]
    have e3 : cT (sigR σ (v.adicCompletion F)) ((g : Matrix (Fin n) (Fin n) _).map (prV (E := E) v)) =
        (cT (sigR σ (FiniteAdeleRing (𝓞 F) F)) (g : Matrix (Fin n) (Fin n) _)).map (prV (E := E) v) := by
      ext i j; simp [cT, prV_sigR]
    rw [e3, e2, ← Matrix.map_mul, ← Matrix.map_mul, hU]
  · intro x
    constructor
    · exact fwd g hg x
    · intro hx
      have h2 := fwd g⁻¹ (inv_mem hg) _ hx
      rwa [map_inv, Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec] at h2
end PI.LPI
