-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Vertical_SecBFinite_incIdeal_le_map_cbf637ec4a9e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T08:35:41.898416+00:00
-- url     : https://prove2.me/submissions/815b5ea3-22da-4c89-88bb-fe5c8a5061ac

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_IntToFracInjective
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_PSecBFinite
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Vertical_SecBFinite_map_integralModel_07d238438554

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Vertical
open MvPolynomial NumberField IsDedekindDomain
noncomputable section
open GroundTheory.Heights₂.Heights.Vertical.SecBFinite
variable {K : Type*} [Field K] [NumberField K]
namespace GroundTheory.Heights₂.Heights.Vertical.SecBFinite
theorem _root_.solution {n k : ℕ} (I : Ideal (MvPolynomial (Fin n) K)) :
    incIdeal I k ≤ (incIdeal (integralModel I) k).map (MvPolynomial.map (algebraMap (𝓞 K) K)) := by
  apply sup_le
  · have hI : I.map (rename (R := K) (Sum.inl : Fin n → Fin n ⊕ (Fin k × Fin n))) =
        ((integralModel I).map (MvPolynomial.map (algebraMap (𝓞 K) K))).map (rename Sum.inl) := by
      rw [map_integralModel]
    rw [hI, Ideal.map_le_iff_le_comap, Ideal.map_le_iff_le_comap]
    intro p hp
    rw [Ideal.mem_comap, Ideal.mem_comap, ← map_rename]
    exact Ideal.mem_map_of_mem _ (Ideal.mem_sup_left (Ideal.mem_map_of_mem _ hp))
  · rw [Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    have hform : (∑ j, X (Sum.inr (i, j)) * X (Sum.inl j) : MvPolynomial (Fin n ⊕ (Fin k × Fin n)) K) =
        MvPolynomial.map (algebraMap (𝓞 K) K) (∑ j, X (Sum.inr (i, j)) * X (Sum.inl j)) := by
      simp [map_sum]
    show (∑ j, X (Sum.inr (i, j)) * X (Sum.inl j) : MvPolynomial (Fin n ⊕ (Fin k × Fin n)) K) ∈ _
    rw [hform]
    exact Ideal.mem_map_of_mem _ (Ideal.mem_sup_right (Ideal.subset_span ⟨i, rfl⟩))
end GroundTheory.Heights₂.Heights.Vertical.SecBFinite
