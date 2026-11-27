-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HilbertSamuel_IrreducibleBasicOpenConnected_exists_base_vanishing_ed32069dae63
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T04:57:12.052663+00:00
-- url     : https://prove2.me/submissions/933e657a-aedb-4c39-ad95-625fd82aabd8

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PFiniteMapOpen
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_IrreducibleConnected_BasicOpenSteps
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_IrreducibleBasicOpenConnected_eval_pullback_f1d6535029bd

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
open MvPolynomial Filter Topology
namespace GroundTheory.Heights₂.Heights.HilbertSamuel
namespace IrreducibleBasicOpenConnected
theorem _root_.solution {n d : ℕ} {W : Ideal (MvPolynomial (Fin n) ℂ)}
    {A : Matrix (Fin d) (Fin n) ℂ} (hW : W.IsPrime) (hA : ComplexSets.IsFiniteProjection W A)
    {g : MvPolynomial (Fin n) ℂ} (hg : g ∉ W) :
    ∃ Q : MvPolynomial (Fin d) ℂ, Q ≠ 0 ∧
      ∀ x ∈ ComplexSets.zeroSet W, eval x g = 0 → eval (A.mulVec x) Q = 0 := by
  letI : Algebra (MvPolynomial (Fin d) ℂ) (MvPolynomial (Fin n) ℂ ⧸ W) :=
    (ComplexSets.projHom W A).toRingHom.toAlgebra
  have : IsDomain (MvPolynomial (Fin n) ℂ ⧸ W) := Ideal.Quotient.isDomain W
  have hne : Ideal.Quotient.mk W g ≠ 0 := fun h => hg (Ideal.Quotient.eq_zero_iff_mem.mp h)
  have hcomap := Ideal.comap_ne_bot_of_integral_mem hne (Ideal.mem_span_singleton_self _)
    (hA.finite.to_isIntegral _)
  obtain ⟨Q, hQmem, hQ⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hcomap
  refine ⟨Q, hQ, fun x hx hgx => ?_⟩
  rw [Ideal.mem_comap, Ideal.mem_span_singleton'] at hQmem
  obtain ⟨c, hc⟩ := hQmem
  obtain ⟨h, rfl⟩ := Ideal.Quotient.mk_surjective c
  have hmem : ComplexSets.pullback A Q - h * g ∈ W := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_mul, hc]
    exact sub_eq_zero.mpr rfl
  have hev := hx _ hmem
  rw [map_sub, map_mul, hgx, mul_zero, sub_zero, IrreducibleBasicOpenConnected.eval_pullback] at hev
  exact hev
end IrreducibleBasicOpenConnected
end GroundTheory.Heights₂.Heights.HilbertSamuel
