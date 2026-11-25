-- Prove2me | solution 1 for PI.VolStabW.TopoMuInv.BR_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:58:01.223634+00:00
-- url     : https://prove2.me/submissions/1adb8740-b65e-4313-a281-aef4378c3f9e

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_TopoFibInv
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_TopoMuInv
import Theorems.Thm_PI_VolStabW_TopoMuInv_smul_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabW PI.VolStabW.TopoMuInv
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory Matrix NumberField IsDedekindDomain
open scoped TensorProduct
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] [FiniteDimensional F E]
  (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R]
  [SecondCountableTopology R] (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)
namespace PI.VolStabW.TopoMuInv
theorem _root_.solution (h : HA R σ J) {n : ℕ} (X Y : Fin n → Fin M → R ⊗[F] E) :
    BR R σ J (h • X) (h • Y) = BR R σ J X Y := by
  simp only [BR, smul_apply]
  refine Finset.sum_congr rfl fun a _ => ?_
  obtain ⟨g, hg⟩ := h
  simp only [HA.mat, HR, hR, Subgroup.mem_mk, Submonoid.mem_mk, Subsemigroup.mem_mk,
    Set.mem_setOf_eq] at hg ⊢
  simp only [Formalism.UG.UJ, Formalism.UG.hform, Subgroup.mem_mk, Submonoid.mem_mk, Subsemigroup.mem_mk,
    Set.mem_setOf_eq] at hg ⊢
  congr 1
  conv_rhs => rw [← hg]
  simp only [Matrix.mulVec, dotProduct, Matrix.mul_apply, Formalism.UG.cT, map_sum, map_mul,
    Finset.sum_mul, Finset.mul_sum]
  refine (Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_comm).trans ?_
  refine (Finset.sum_congr rfl fun _ _ => Finset.sum_comm).trans ?_
  refine (Finset.sum_comm).trans ?_
  refine (Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_comm).trans ?_
  refine (Finset.sum_congr rfl fun _ _ => Finset.sum_comm).trans ?_
  refine (Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_comm).trans ?_
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
    Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
  rw [Matrix.transpose_apply, Matrix.map_apply]
  ring
end PI.VolStabW.TopoMuInv
