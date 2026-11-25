-- Prove2me | solution 1 for PI.LevelKSplit.W.Meas.stab_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T09:50:48.260103+00:00
-- url     : https://prove2.me/submissions/d4a653fa-190f-4c96-9361-9302163abff7

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_MeasDefs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_RatVMemSpan
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicLocalCompactness_T2SpaceTensorProductFiniteExtension
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_CompVInvMulVec
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
namespace PI.LevelKSplit.W.Meas
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory PI.LevelKSplit
  PI.LevelKSplit.W.Glob
open scoped TensorProduct
private theorem mulVec_mem_span_of_mulVec_generators_mem {O B : Type} [CommRing O] [CommRing B] [Algebra O B] {n : ℕ}
    (A : Matrix (Fin n) (Fin n) B) (G : Set (Fin n → B))
    (hG : ∀ y ∈ G, A.mulVec y ∈ Submodule.span O G) :
    ∀ x ∈ Submodule.span O G, A.mulVec x ∈ Submodule.span O G := by
  intro x hx
  induction hx using Submodule.span_induction with
  | mem y hy => exact hG y hy
  | zero => rw [Matrix.mulVec_zero]; exact Submodule.zero_mem _
  | add a b _ _ ha hb => rw [Matrix.mulVec_add]; exact Submodule.add_mem _ ha hb
  | smul c a _ ha => rw [Matrix.mulVec_smul]; exact Submodule.smul_mem _ c ha
end PI.LevelKSplit.W.Meas
end
end

set_option autoImplicit false
noncomputable section
open PI PI.LevelKSplit PI.LevelKSplit.W PI.LevelKSplit.W.Meas
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory PI.LevelKSplit
  PI.LevelKSplit.W.Glob
open scoped TensorProduct
namespace PI.LevelKSplit.W.Meas
theorem _root_.solution {O B : Type} [CommRing O] [CommRing B] [Algebra O B] {n : ℕ}
    (A C : Matrix (Fin n) (Fin n) B) (hCA : ∀ x, C.mulVec (A.mulVec x) = x)
    (hAC : ∀ x, A.mulVec (C.mulVec x) = x) (G : Set (Fin n → B)) :
    (∀ x, x ∈ Submodule.span O G ↔ A.mulVec x ∈ Submodule.span O G) ↔
      ∀ y ∈ G, A.mulVec y ∈ Submodule.span O G ∧ C.mulVec y ∈ Submodule.span O G := by
  constructor
  · intro h y hy
    have hyS : y ∈ Submodule.span O G := Submodule.subset_span hy
    refine ⟨(h y).1 hyS, ?_⟩
    rw [h (C.mulVec y), hAC y]
    exact hyS
  · intro h x
    constructor
    · exact fun hx => mulVec_mem_span_of_mulVec_generators_mem A G (fun y hy => (h y hy).1) x hx
    · intro hx
      have hC := mulVec_mem_span_of_mulVec_generators_mem C G (fun y hy => (h y hy).2) _ hx
      rwa [hCA x] at hC
end PI.LevelKSplit.W.Meas
