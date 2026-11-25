-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ZeroLocusDimH_dimH_le_of_local_antilipschitz_c1a501dd5ea8
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T05:25:25.825398+00:00
-- url     : https://prove2.me/submissions/475e4ee6-5750-44fa-982b-7e170dee1187

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_ZeroLocusDimHGeo

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open Metric Filter Topology Finset
noncomputable section
open GroundTheory.Heights₂.Heights.ZeroLocusDimH
namespace GroundTheory.Heights₂.Heights.ZeroLocusDimH
theorem _root_.solution {n r : ℕ} (f : (Fin n → ℂ) → (Fin r → ℂ))
    (S : Set (Fin n → ℂ))
    (h : ∀ x₀ ∈ S, ∃ U ∈ 𝓝 x₀, ∃ K : ℝ, 0 ≤ K ∧
      ∀ x ∈ S ∩ U, ∀ x' ∈ S ∩ U, ‖x - x'‖ ≤ K * ‖f x - f x'‖) :
    dimH S ≤ 2 * (r : ENNReal) := by
  by_contra hlt0
  have hlt := not_le.1 hlt0
  obtain ⟨x₀, hx₀, hall⟩ := exists_mem_nhdsWithin_lt_dimH_of_lt_dimH hlt
  obtain ⟨U, hU, K, hK, hKU⟩ := h x₀ hx₀
  have hlt' := hall (S ∩ U) (inter_mem_nhdsWithin S hU)
  refine (not_le.2 hlt') ?_
  let g : (S ∩ U : Set (Fin n → ℂ)) → (Fin r → ℂ) := fun a => f a
  have hg : AntilipschitzWith ⟨K, hK⟩ g := by
    refine AntilipschitzWith.of_le_mul_dist fun a b => ?_
    rw [Subtype.dist_eq, dist_eq_norm, dist_eq_norm]
    exact hKU a a.2 b b.2
  have e1 : dimH (S ∩ U) = dimH (Set.univ : Set (S ∩ U : Set (Fin n → ℂ))) := by
    rw [← (isometry_subtype_coe).dimH_image Set.univ, Subtype.coe_image_univ]
  have hfin : Module.finrank ℝ (Fin r → ℂ) = 2 * r := by
    rw [Module.finrank_pi_fintype, Complex.finrank_real_complex, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_comm]
  calc dimH (S ∩ U) = dimH (Set.univ : Set (S ∩ U : Set (Fin n → ℂ))) := e1
    _ ≤ dimH (g '' Set.univ) := hg.le_dimH_image _
    _ ≤ dimH (Set.univ : Set (Fin r → ℂ)) := dimH_mono (Set.subset_univ _)
    _ = Module.finrank ℝ (Fin r → ℂ) := Real.dimH_univ_eq_finrank _
    _ = 2 * (r : ENNReal) := by rw [hfin]; push_cast; ring
end GroundTheory.Heights₂.Heights.ZeroLocusDimH
