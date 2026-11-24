-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_GenericProjClosureDim_exists_ne_zero_of_span_5f8e06e12f5c
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:43:46.06002+00:00
-- url     : https://prove2.me/submissions/e6789dc0-0276-4ba8-b616-881d8286da59

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsGenericProjClosureDim
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsDvrConeDimTrdeg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsPairBundleTrdeg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PTwistedDualGensSpan
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PGenericProjClosureDim

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NumbersDVR
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
noncomputable section
open GroundTheory.Heights₂.Heights.NumbersDVR.GenericProjClosureDim
variable {R : Type*} [CommRing R] {L : Type*} [Field L] [Algebra R L] {K : Type*} [DecidableEq K]
  {ι : K → Type*}
namespace GroundTheory.Heights₂.Heights.NumbersDVR.GenericProjClosureDim
theorem _root_.solution {Ω : Type*} [Field Ω] {E : Type*} [AddCommGroup E] [Module Ω E]
    {Φ : Type*} [Field Φ] [Algebra Ω Φ] {N P : ℕ} (hN : 0 < N) (e : Module.Basis (Fin N) Ω E)
    {t : Fin N → Φ} (ht : LinearIndependent Ω t) (ψ : Fin P → Module.Dual Ω E)
    (hψ : Submodule.span Ω (Set.range ψ) = ⊤) :
    ∃ l, ∑ i, t i * algebraMap Ω Φ (ψ l (e i)) ≠ 0 := by
  by_contra! h0
  have hall : ∀ l, ψ l = 0 := by
    intro l
    refine e.ext fun i => ?_
    have := Fintype.linearIndependent_iff.1 ht (fun i => ψ l (e i))
      (by rw [← h0 l]; exact Finset.sum_congr rfl fun i _ => by rw [Algebra.smul_def, mul_comm])
    simpa using this i
  have htop : (⊤ : Submodule Ω (Module.Dual Ω E)) = ⊥ := by
    rw [← hψ, Submodule.span_eq_bot]
    rintro _ ⟨l, rfl⟩
    exact hall l
  have hc : e.coord ⟨0, hN⟩ = 0 := by
    have : e.coord ⟨0, hN⟩ ∈ (⊥ : Submodule Ω (Module.Dual Ω E)) := htop ▸ Submodule.mem_top
    simpa using this
  have := congrArg (fun f => f (e ⟨0, hN⟩)) hc
  simp at this
end GroundTheory.Heights₂.Heights.NumbersDVR.GenericProjClosureDim
