-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LC.Core.kAlg_of_adjoin_restrict
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T11:46:27.958579+00:00
-- url     : https://prove2.me/submissions/a0592ba5-26ac-4e4f-965f-f540f374e588

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_MonomialMemSupported
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_KAlgOfAdjoinRestrict

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LC PositivityTheory.Rg.Sw.LC.Core
open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LC
variable {m n : ℕ}
namespace PositivityTheory.Rg.Sw.LC.Core
theorem _root_.solution (ε : Fin m → Bool) (V : Submodule ℂ (PX m n))
    (hK : ∀ ij : Fin n × Fin n, ∀ f ∈ V, KopL ε ij.1 ij.2 f ∈ V) (y : Module.End ℂ V)
    (hy : y ∈ Algebra.adjoin ℂ (Set.range fun ij : Fin n × Fin n => (KopL ε ij.1 ij.2).restrict (hK ij))) :
    ∃ w ∈ kAlg ε, ∀ v : V, w v = (y v : PX m n) := by
  induction hy using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨ij, rfl⟩ := hx
    exact ⟨KopL ε ij.1 ij.2, Algebra.subset_adjoin ⟨ij, rfl⟩, fun v => rfl⟩
  | algebraMap r =>
    exact ⟨algebraMap ℂ _ r, Subalgebra.algebraMap_mem _ r, fun v => by simp [Algebra.algebraMap_eq_smul_one]⟩
  | add x y _ _ hx hy =>
    obtain ⟨w₁, h₁, e₁⟩ := hx
    obtain ⟨w₂, h₂, e₂⟩ := hy
    exact ⟨w₁ + w₂, Subalgebra.add_mem _ h₁ h₂, fun v => by simp [e₁, e₂]⟩
  | mul x y _ _ hx hy =>
    obtain ⟨w₁, h₁, e₁⟩ := hx
    obtain ⟨w₂, h₂, e₂⟩ := hy
    refine ⟨w₁ * w₂, Subalgebra.mul_mem _ h₁ h₂, fun v => ?_⟩
    simp only [Module.End.mul_apply]
    rw [e₂, ← e₁ (y v)]
end PositivityTheory.Rg.Sw.LC.Core
