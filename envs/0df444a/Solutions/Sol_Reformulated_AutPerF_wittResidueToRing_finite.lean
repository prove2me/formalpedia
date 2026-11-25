-- Prove2me | solution 1 for Reformulated.AutPerF.wittResidueToRing_finite
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T16:30:13.572865+00:00
-- url     : https://prove2.me/submissions/5fe8031c-5c9b-4f8d-9b9f-6ab6f6181afe

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_Section
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_Residue
import Theorems.Thm_Reformulated_AutPerF_isPrecomplete_pi
import Theorems.Thm_Reformulated_AutPerF_exists_sum_wittResidueToRing
import Theorems.Thm_Reformulated_AutPerF_AinfInv_liftFracWitt_algebraMap
import Theorems.Thm_Reformulated_AutPerF_Ainf_ofWitt_teichmuller
import Theorems.Thm_Reformulated_AutPerF_Bst_monodromy_logFlat
import Theorems.Thm_Reformulated_AutPerF_awayMap_algebraMap
import Theorems.Thm_Reformulated_AutPerF_fracWittLift_algebraMap
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Reformulated.AutPerF.Ainf.ofWitt_teichmuller
attribute [local simp] Reformulated.AutPerF.AinfInv.liftFracWitt_algebraMap
attribute [local simp] Reformulated.AutPerF.Bst.monodromy_logFlat
attribute [local simp] Reformulated.AutPerF.awayMap_algebraMap
attribute [local simp] Reformulated.AutPerF.fracWittLift_algebraMap



set_option autoImplicit false
noncomputable section
open Ideal IsLocalRing
open Reformulated Reformulated.AutPerF
universe u
variable (p : ℕ) [Fact p.Prime]
variable (A : Type u) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [CharZero A]
  [Fact ¬IsUnit (p : A)]
variable [CharP (ResidueField A) p] [PerfectRing (ResidueField A) p]
variable [IsAdicComplete (span {(p : A)}) A]
namespace Reformulated.AutPerF
theorem _root_.solution : (wittResidueToRing p A).Finite := by
  letI := (wittResidueToRing p A).toAlgebra
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible A
  obtain ⟨e, he⟩ := exists_maximalIdeal_pow_le_span_p p A
  rw [hπ.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.span_singleton_le_span_singleton] at he
  obtain ⟨u, hu⟩ := he
  let f : (Fin e → WittVector p (ResidueField A)) →ₗ[WittVector p (ResidueField A)] A :=
    Fintype.linearCombination _ fun i => π ^ (i : ℕ)
  have hmap : (span {(p : WittVector p (ResidueField A))}).map
      (algebraMap (WittVector p (ResidueField A)) A) = span {(p : A)} := by
    simp [Ideal.map_span]
  haveI : IsHausdorff (span {(p : WittVector p (ResidueField A))}) A := by
    rw [← IsHausdorff.map_algebraMap_iff (S := A), hmap]
    infer_instance
  haveI := isPrecomplete_pi (p : WittVector p (ResidueField A)) (Fin e)
  refine Module.Finite.of_surjective f
    (surjective_of_mkQ_comp_surjective (I := span {(p : WittVector p (ResidueField A))}) ?_)
  intro y
  obtain ⟨a, rfl⟩ := Submodule.mkQ_surjective _ y
  obtain ⟨c, b, rfl⟩ := exists_sum_wittResidueToRing p A hπ e a
  refine ⟨fun i => c i, ?_⟩
  rw [LinearMap.comp_apply, Submodule.mkQ_apply, Submodule.mkQ_apply, eq_comm,
    Submodule.Quotient.eq]
  have : f (fun i => c i) = ∑ i ∈ Finset.range e, wittResidueToRing p A (c i) * π ^ i := by
    rw [Finset.sum_range]
    simp [f, Fintype.linearCombination_apply, Algebra.smul_def, RingHom.algebraMap_toAlgebra]
  rw [this, add_sub_cancel_left, hu, mul_assoc]
  have h2 : (p : A) * (u * b) = (p : WittVector p (ResidueField A)) • (u * b) := by
    rw [Algebra.smul_def, map_natCast]
  rw [h2]
  exact Submodule.smul_mem_smul (mem_span_singleton_self _) Submodule.mem_top
end Reformulated.AutPerF
