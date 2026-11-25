-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_exists_mul_mem_chartRing_29135794d49d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T08:30:54.577517+00:00
-- url     : https://prove2.me/submissions/168fd708-0bf8-44b8-bd07-be6b4f14bd8d

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_GenericPointSectionHypotheses
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsTildeTail
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PFiniteSections
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_exists_monos_map_78062567800a
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_algebraMap_ne_zero_of_mem_6daf37f2ffbd

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
universe u w
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω} {F : Type u} [Field F] [Algebra S F] [Algebra F Ω] [IsScalarTower S F Ω]
  [IsFractionRing S F]
namespace GroundTheory.Heights₂.Heights.Kleiman
theorem _root_.solution {I : Chart x} {a : Ω} (ha : a ∈ chartRing F x I) :
    ∃ t ∈ nonZeroDivisors S, algebraMap S Ω t * a ∈ chartRing S x I := by
  obtain ⟨f, s, e, hs, hf, hse, rfl⟩ := ha
  obtain ⟨s', hs', rfl⟩ := exists_monos_map (S := S) hs
  have hinj : Function.Injective (algebraMap S F) := IsFractionRing.injective S F
  have hse' : s'.IsHomogeneous e := fun d hd => hse (by
    rw [coeff_map]; exact fun h => hd (hinj (h.trans (map_zero _).symm)))
  have hsum : aeval x f / aeval x (map (algebraMap S F) s') =
      ∑ d ∈ f.support, coeff d f • (aeval x (monomial d (1 : S)) / aeval x s') := by
    rw [aeval_map_algebraMap]
    conv_lhs => rw [f.as_sum]
    rw [map_sum, Finset.sum_div]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [aeval_monomial, aeval_monomial, map_one, one_mul, Algebra.smul_def, mul_div_assoc]
  rw [hsum]
  refine Finset.sum_induction _ (fun a => ∃ t ∈ nonZeroDivisors S, algebraMap S Ω t * a ∈ chartRing S x I)
    ?_ ⟨1, one_mem _, by rw [mul_zero]; exact zero_mem _⟩ ?_
  · rintro a b ⟨t, ht, hta⟩ ⟨t', ht', htb⟩
    refine ⟨t * t', mul_mem ht ht', ?_⟩
    have : algebraMap S Ω (t * t') * (a + b) =
        algebraMap S Ω t' * (algebraMap S Ω t * a) + algebraMap S Ω t * (algebraMap S Ω t' * b) := by
      rw [map_mul]; ring
    rw [this]
    exact add_mem (mul_mem (Subalgebra.algebraMap_mem _ _) hta)
      (mul_mem (Subalgebra.algebraMap_mem _ _) htb)
  · intro d hd
    have hmem : aeval x (monomial d (1 : S)) / aeval x s' ∈ chartRing S x I :=
      ⟨monomial d 1, s', e, hs', isHomogeneous_monomial _ (by
        rw [Finsupp.degree_eq_weight_one]; exact hf (mem_support_iff.mp hd)), hse', rfl⟩
    obtain ⟨u, v, hv, huv⟩ := IsFractionRing.div_surjective (A := S) (coeff d f)
    refine ⟨v, hv, ?_⟩
    have hv0 : algebraMap S Ω v ≠ 0 := algebraMap_ne_zero_of_mem F hv
    have : algebraMap S Ω v * (coeff d f • (aeval x (monomial d (1 : S)) / aeval x s')) =
        algebraMap S Ω u * (aeval x (monomial d (1 : S)) / aeval x s') := by
      rw [Algebra.smul_def, ← huv, map_div₀, ← IsScalarTower.algebraMap_apply,
        ← IsScalarTower.algebraMap_apply]
      field_simp
    rw [this]
    exact mul_mem (Subalgebra.algebraMap_mem _ _) hmem
end GroundTheory.Heights₂.Heights.Kleiman
