-- Prove2me | solution 1 for P2M_GlobalTheory_Cube_SemiHom_homology___79af601acfd5
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T04:48:20.98485+00:00
-- url     : https://prove2.me/submissions/991389eb-2efb-41d3-b783-fb845aa7a99c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_PresheafCubeExactAtSuccOfSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_CohomologyPresheafFunctorMapAppApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_SumNegOnePowFinrankEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsAddEquivOfSurjectiveOfKerIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_CechModulesFunctorShortExactOfAcyclic
import Theorems.Thm_P2M_GlobalTheory___cechClass_89909f0dccc0
import Theorems.Thm_GlobalTheory_exists_lift_cechCocycle
import Theorems.Thm_GlobalTheory_Cube_SemiHom_homology_cechClass
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.Cube.SemiHom.homology_cechClass



set_option autoImplicit false
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace Opposite
universe v u
noncomputable section
open GlobalTheory
variable {ι : Type} [LinearOrder ι] {R : Type v} [Ring R]
namespace GlobalTheory
namespace Cube.SemiHom
theorem _root_.solution {R' : Type*} [Ring R'] {σ : R →+* R'}
    {S : ShortComplex (Cube.{u} ι R)} {S' : ShortComplex (Cube.{u} ι R')}
    (hS : (S.map (cechFunctor ι R)).ShortExact) (hS' : (S'.map (cechFunctor ι R')).ShortExact)
    (ψ₁ : Cube.SemiHom σ S.X₁ S'.X₁) (ψ₂ : Cube.SemiHom σ S.X₂ S'.X₂)
    (ψ₃ : Cube.SemiHom σ S.X₃ S'.X₃)
    (hf : ∀ s x, ψ₂.app s ((S.f.app s).hom x) = (S'.f.app s).hom (ψ₁.app s x))
    (hg : ∀ s x, ψ₃.app s ((S.g.app s).hom x) = (S'.g.app s).hom (ψ₂.app s x))
    (p : ℕ) (x : (cechComplex S.X₃).homology p) :
    ψ₁.homology (p + 1) ((hS.δ p (p + 1) rfl).hom x) =
      (hS'.δ p (p + 1) rfl).hom (ψ₃.homology p x) := by
  obtain ⟨x₃, rfl⟩ := cechClass_surjective S.X₃ p x
  obtain ⟨x₂, x₁, h₂, h₁⟩ := exists_lift_cechCocycle hS p x₃
  rw [δ_cechClass hS p x₃ x₂ x₁ h₂ h₁, homology_cechClass, homology_cechClass]
  refine (δ_cechClass hS' p _ (ψ₂.term _ x₂) _ ?_ ?_).symm
  · rw [coe_cocycle, ← h₂]
    exact funext fun s => (hg s.1 _).symm
  · rw [coe_cocycle, ← term_d, ← h₁]
    exact funext fun s => (hf s.1 _).symm
end Cube.SemiHom
end GlobalTheory
