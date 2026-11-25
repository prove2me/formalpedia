-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FiniteCovolume_LatticeOrbitsFinite_proof_7aa74a0582e3
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T04:49:43.481931+00:00
-- url     : https://prove2.me/submissions/4dfb4344-30d5-49c5-96f3-cc37da7f55c6

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_SecondCountableTopologyArchUnitary
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PLatticeOrbitsFinite
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_isIsotropicLine_span_singleton_9971ad41966c

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FiniteCovolume
open NumberField GroundTheory.Automorphic Module
open scoped Pointwise
noncomputable section
variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [IsTotallyComplex E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]
namespace GroundTheory.Heights₂.Heights.FiniteCovolume
namespace LatticeOrbitsFinite
theorem _root_.solution (h : HermitianForm F E W) (v : Basis ι E W) [FiniteDimensional E W]
    (h₁ : MahlerCompactness.Statement h v) (h₂ : MajorantExists.Statement h v)
    (h₃ : ShortVectorIsotropic.Statement h v) (h₄ : LinePairOrbitsFinite.Statement h) :
    LatticeOrbitsFinite.Statement h := by
  intro D
  obtain ⟨M⟩ := h₂
  obtain ⟨S₁, hS₁, K, -, hK⟩ := h₁ M D 1 one_pos
  obtain ⟨S₂, hS₂, hP⟩ := h₄ D
  refine ⟨S₁ ∪ Prod.fst '' S₂, hS₁.union (hS₂.image _), ?_⟩
  intro La hLa
  by_cases hshort : ∃ x : W, x ∈ La ∧ x ≠ 0 ∧ M.len (invApply (1 : archUnitary h v) (vecAt v x)) < 1
  · obtain ⟨x, hxL, hx0, hxlt⟩ := hshort
    have hxx : h.toSesq x x = 0 := h₃ M D La 1 x hLa hxL hxlt
    obtain ⟨p, hp, g, hg, -⟩ := hP La (Submodule.span E {x}) hLa
      (isIsotropicLine_span_singleton h hx0 hxx)
    exact ⟨p.1, Or.inr ⟨p, hp, rfl⟩, g, hg⟩
  · push Not at hshort
    obtain ⟨γ, hγ, -⟩ := hK La 1 hLa hshort
    exact ⟨γ • La, Or.inl hγ, γ⁻¹, inv_smul_smul γ La⟩
end LatticeOrbitsFinite
end GroundTheory.Heights₂.Heights.FiniteCovolume
