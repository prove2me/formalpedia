-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_TranslateEq_mem_twist_twistSys_iff_89a1717ba8b8
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T01:01:59.64325+00:00
-- url     : https://prove2.me/submissions/c615a98b-094c-43d7-bd08-6ee110252019

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_Objects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_CoordIdealIsMultiProjPrime
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_EqZeroOrIsHomogeneousOfMemPolyPiece

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman GroundTheory.Heights₂.Heights.Kleiman.TranslateEq
open MvPolynomial
noncomputable section
variable {S : Type} [CommRing S] {N : ℕ} {Ω : Type} [Field Ω] [Algebra S Ω] {x : Fin (N + 1) → Ω}
variable {E : Type} [AddCommGroup E] [Module Ω E] [Module S E] [IsScalarTower S Ω E]
omit [Module S E] [IsScalarTower S Ω E]
namespace GroundTheory.Heights₂.Heights.Kleiman.TranslateEq
theorem _root_.solution (F : Kleiman.SubSystem S x E) (c : ℤ) (I : Kleiman.Chart x)
    {i : Fin (N + 1)} (hi : i ∈ I.1) (z : E) :
    z ∈ (F.twist (Kleiman.twistSys S x c)).sub I ↔ ∃ y ∈ F.sub I, z = x i ^ c • y := by
  constructor
  · intro hz
    induction hz using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨q, hq, y, hy, rfl⟩ := hz
      change q ∈ Kleiman.twistMod S x c I at hq
      rw [Kleiman.twistMod_eq_span c I hi, Submodule.mem_span_singleton] at hq
      obtain ⟨a, rfl⟩ := hq
      refine ⟨a • y, Submodule.smul_mem _ a hy, ?_⟩
      rw [Kleiman.chartRing_smul_def, mul_smul]
      exact smul_comm _ _ _
    | zero => exact ⟨0, zero_mem _, (smul_zero _).symm⟩
    | add a b _ _ ha hb =>
      obtain ⟨y, hy, rfl⟩ := ha
      obtain ⟨y', hy', rfl⟩ := hb
      exact ⟨y + y', add_mem hy hy', (smul_add _ _ _).symm⟩
    | smul a w _ hw =>
      obtain ⟨y, hy, rfl⟩ := hw
      refine ⟨a • y, Submodule.smul_mem _ a hy, ?_⟩
      rw [Subalgebra.smul_def, Subalgebra.smul_def, smul_comm]
  · rintro ⟨y, hy, rfl⟩
    refine Submodule.subset_span ⟨x i ^ c, ?_, y, hy, rfl⟩
    change x i ^ c ∈ Kleiman.twistMod S x c I
    rw [Kleiman.twistMod_eq_span c I hi]
    exact Submodule.mem_span_singleton_self _
end GroundTheory.Heights₂.Heights.Kleiman.TranslateEq
