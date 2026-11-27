-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_SnapperQuotFilt_smul_mem_gmul_7802f5c56b4b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T05:02:55.873342+00:00
-- url     : https://prove2.me/submissions/55516597-d0c1-4f31-8a66-00014cdd2e8b

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_SnapperQuotFiltSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TwistAlg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PDomination
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_HomogeneousComponentMulForm
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SnapperQuotFilt_homogeneousComponent_mul_form_2ed9f7654015

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
universe u v w
open GroundTheory.Heights₂.Heights.Kleiman.SnapperQuotFilt
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ} {x : Fin (N + 1) → Ω}
  {E : Type v} [AddCommGroup E] [Module Ω E] [Module S E] [IsScalarTower S Ω E]
namespace GroundTheory.Heights₂.Heights.Kleiman.SnapperQuotFilt
theorem _root_.solution (M : FinGradedSub (S := S) (x := x) E) {s : ℕ} (h : Fin s → Poly S N) (d : Fin s → ℕ)
    (hh : ∀ l, (h l).IsHomogeneous (d l)) {J : Ideal (Poly S N)} (hJ : Ideal.span (Set.range h) = J)
    {f : Poly S N} {e : ℕ} (hfJ : f ∈ J) (hf : f.IsHomogeneous e) {a : ℤ} {z : E} (hz : z ∈ M.piece a) :
    aeval x f • z ∈ (gmul M h d).piece (a + e) := by
  classical
  rw [← hJ] at hfJ
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun _).mp hfJ
  have hf' : f = ∑ l, (if d l ≤ e then homogeneousComponent (e - d l) (c l) * h l else 0) := by
    conv_lhs => rw [← homogeneousComponent_eq_self hf, ← hc, map_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [smul_eq_mul, homogeneousComponent_mul_form _ _ (hh l)]
  rw [hf', map_sum, Finset.sum_smul]
  refine Submodule.sum_mem _ fun l _ => ?_
  by_cases hle : d l ≤ e
  · rw [if_pos hle, map_mul, mul_comm, mul_smul]
    refine Submodule.subset_span ⟨l, a + ((e - d l : ℕ) : ℤ), _,
      M.smul_mem _ _ _ _ (homogeneousComponent_isHomogeneous _ _) hz, ?_, rfl⟩
    rw [Nat.cast_sub hle]; ring
  · rw [if_neg hle, map_zero, zero_smul]
    exact Submodule.zero_mem _
end GroundTheory.Heights₂.Heights.Kleiman.SnapperQuotFilt
