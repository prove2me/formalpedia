-- Prove2me | solution 1 for PIW.AdelClassFin.mLat_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:03:17.644501+00:00
-- url     : https://prove2.me/submissions/7bd66156-a220-4284-b231-09227762b846

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_DictPlan
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_DictGen
import Theorems.Thm_PIW_AdelClassFin_DictGen_exists_denominator_fmat
import Theorems.Thm_PIW_AdelClassFin_DictGen_nL_sub
import Theorems.Thm_PIW_AdelClassFin_DictGen_nLam_sub

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PIW PIW.AdelClassFin
open Formalism.MainNotions.S PI.AdelClassFin NumberField
open scoped TensorProduct Matrix
namespace PIW.AdelClassFin
theorem _root_.solution (hInt : LInter) (hD : LDenom) : MLat := by
  intro I x
  obtain ⟨N, hN, hN'⟩ := DictGen.exists_denominator_fmat I hD x
  have hNE : (N : I.E) ≠ 0 := by exact_mod_cast hN.ne'
  constructor
  · let ψ : (Fin I.n → I.E) →ₗ[𝓞 I.E] (Fin I.n → I.E) :=
      (((N : I.E)⁻¹ • LinearMap.id : (Fin I.n → I.E) →ₗ[I.E] (Fin I.n → I.E))).restrictScalars (𝓞 I.E)
    have hle : abelian₂ I x ≤ I.L.map ψ := by
      intro v hv
      have h1 : N • v ∈ I.L := DictGen.nLam_sub I hInt x N hN' hv
      have e : ψ (N • v) = v := by
        show (N : I.E)⁻¹ • (N • v) = v
        rw [← Nat.cast_smul_eq_nsmul I.E, smul_smul, inv_mul_cancel₀ hNE, one_smul]
      rw [← e]
      exact Submodule.mem_map_of_mem h1
    haveI : IsNoetherian (𝓞 I.E) (I.L.map ψ) := isNoetherian_of_fg_of_noetherian _ (I.L_fg.map ψ)
    haveI : IsNoetherian (𝓞 I.E) (abelian₂ I x) := isNoetherian_of_le hle
    first
      | exact (Submodule.fg_top _).mp (IsNoetherian.noetherian _)
      | exact Module.Finite.iff_fg.mp inferInstance
  · rw [eq_top_iff, ← I.L_span, Submodule.span_le]
    intro v hv
    have h1 : N • v ∈ abelian₂ I x := DictGen.nL_sub I x N hN' hv
    have h2 : N • v ∈ Submodule.span I.E
        ((abelian₂ I x : Submodule (𝓞 I.E) (Fin I.n → I.E)) : Set (Fin I.n → I.E)) :=
      Submodule.subset_span h1
    have e : v = (N : I.E)⁻¹ • (N • v) := by
      rw [← Nat.cast_smul_eq_nsmul I.E, smul_smul, inv_mul_cancel₀ hNE, one_smul]
    rw [e]
    exact Submodule.smul_mem _ _ h2
end PIW.AdelClassFin
