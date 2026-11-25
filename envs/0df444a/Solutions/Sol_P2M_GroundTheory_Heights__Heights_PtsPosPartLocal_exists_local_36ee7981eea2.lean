-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_PtsPosPartLocal_exists_local_36ee7981eea2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T04:47:51.565789+00:00
-- url     : https://prove2.me/submissions/f60c0775-b42a-431c-88be-50321f4d4763

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterBridgeF
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StPtsPosPartLocal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PPtsPosPartLocal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MeasureTheory Filter Topology ReciprocityTheory.ChartRestriction.G.Geo
open GroundTheory.Heights₂.Heights.PtsPosPartLocal
set_option linter.unusedSectionVars false
variable {K : Type*} [Fintype K] [DecidableEq K] {ι : K → Type*} [∀ k, Fintype (ι k)] {e : ℕ}
variable {Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)}
namespace GroundTheory.Heights₂.Heights.PtsPosPartLocal
theorem _root_.solution {P : Ideal (MRing ι)} {w₀ : ((k : K) → ι k) → ℂ} (h : IsSimpleSheetPt P Ψ w₀) :
    ∃ (y₀ : Fin e → ℂ) (γ : (Fin e → ℂ) → (Σ k, ι k) → ℂ) (U : Set (Fin e → ℂ))
      (N : Set ((Fin e → ℂ) × (((k : K) → ι k) → ℂ))),
      IsOpen U ∧ IsOpen N ∧ (y₀, w₀) ∈ N ∧ segre (γ y₀) = w₀ ∧
      (∀ y ∈ U, DifferentiableAt ℂ γ y ∧ γ y ∈ mcPts P ∧ Ψ (segre (γ y)) = Fin.cons 1 y) ∧
      ∀ q ∈ N, q.1 ∈ U ∧ (q.2 ∈ fibre P Ψ q.1 → q.2 = segre (γ q.1)) := by
  obtain ⟨y₀, γ, hsh, hev⟩ := h
  obtain ⟨U, hUs, hU, hy₀⟩ := mem_nhds_iff.mp hsh.2
  obtain ⟨N₁, hN₁s, hN₁, hq₁⟩ := mem_nhds_iff.mp hev
  exact ⟨y₀, γ, U, N₁ ∩ U ×ˢ Set.univ, hU, hN₁.inter (hU.prod isOpen_univ), ⟨hq₁, hy₀, trivial⟩,
    hsh.1, fun y hy => hUs hy, fun q hq => ⟨hq.2.1, hN₁s hq.1⟩⟩
end GroundTheory.Heights₂.Heights.PtsPosPartLocal
