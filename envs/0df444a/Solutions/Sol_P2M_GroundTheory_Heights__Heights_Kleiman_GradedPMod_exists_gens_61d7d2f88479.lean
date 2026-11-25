-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_GradedPMod_exists_gens_61d7d2f88479
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T04:01:41.71384+00:00
-- url     : https://prove2.me/submissions/918ac259-c0e8-4c64-a4d2-feec71f69138

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PSerreOnto

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman
open MvPolynomial
noncomputable section
universe u v w w'
variable {S : Type u} [CommRing S] {N : ℕ}
variable {M : Type v} [AddCommGroup M] [Module (Poly S N) M] [Module S M] [IsScalarTower S (Poly S N) M]
omit [IsScalarTower S (Poly S N) M]
namespace GroundTheory.Heights₂.Heights.Kleiman
namespace GradedPMod
theorem _root_.solution (𝓜 : GradedPMod S N M) (hM : Module.Finite (Poly S N) M) :
    ∃ (r : ℕ) (g : Fin r → M) (deg : Fin r → ℤ), (∀ j, g j ∈ 𝓜.piece (deg j)) ∧
      Submodule.span (Poly S N) (Set.range g) = ⊤ := by
  classical
  let _ := 𝓜.isInternal.chooseDecomposition
  obtain ⟨s, hs⟩ := hM.fg_top
  let J := Σ m : s, ((DirectSum.decompose 𝓜.piece (m : M)).support : Finset ℤ)
  let e := Fintype.equivFin J
  refine ⟨Fintype.card J, fun j => (DirectSum.decompose 𝓜.piece ((e.symm j).1 : M) (e.symm j).2 : M),
    fun j => ((e.symm j).2 : ℤ), fun j => (DirectSum.decompose 𝓜.piece _ _).2, ?_⟩
  rw [eq_top_iff, ← hs, Submodule.span_le]
  intro m hm
  rw [← DirectSum.sum_support_decompose 𝓜.piece m]
  refine Submodule.sum_mem _ fun c hc => Submodule.subset_span ⟨e ⟨⟨m, hm⟩, ⟨c, hc⟩⟩, ?_⟩
  dsimp only
  rw [Equiv.symm_apply_apply]
end GradedPMod
end GroundTheory.Heights₂.Heights.Kleiman
