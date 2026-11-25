-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HilbertSamuel_FiltrationHilbSum_comp_mem_sup_8b18db97daef
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T03:55:31.514391+00:00
-- url     : https://prove2.me/submissions/755f49b9-336b-4aeb-a536-81b11f08d93a

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsFiltrationHilbSum
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PFiltrationStepHilb
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PGradedPieceQuot
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PFiltrationHilbSum

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.HilbertSamuel
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR
noncomputable section
universe u v
open GroundTheory.Heights₂.Heights.HilbertSamuel.FiltrationHilbSum
variable {F : Type u} [Field F] {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type}
  {M : Type v} [AddCommGroup M] [Module (MRing ι F) M] [Module F M]
  [IsScalarTower F (MRing ι F) M] {piece : (K → ℤ) → Submodule F M}
omit [DecidableEq K] [IsScalarTower F (MRing ι F) M]
namespace GroundTheory.Heights₂.Heights.HilbertSamuel.FiltrationHilbSum
theorem _root_.solution [DirectSum.Decomposition piece] {N₁ N₂ : Submodule (MRing ι F) M}
    (h₁ : ∀ y ∈ N₁, ∀ m, comp (piece := piece) m y ∈ N₁)
    (h₂ : ∀ y ∈ N₂, ∀ m, comp (piece := piece) m y ∈ N₂) :
    ∀ y ∈ N₁ ⊔ N₂, ∀ m, comp (piece := piece) m y ∈ N₁ ⊔ N₂ := by
  intro y hy m
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hy
  rw [map_add]
  exact Submodule.add_mem_sup (h₁ a ha m) (h₂ b hb m)
end GroundTheory.Heights₂.Heights.HilbertSamuel.FiltrationHilbSum
