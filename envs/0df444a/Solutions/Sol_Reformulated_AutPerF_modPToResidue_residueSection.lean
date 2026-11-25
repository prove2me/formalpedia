-- Prove2me | solution 1 for Reformulated.AutPerF.modPToResidue_residueSection
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T15:58:36.263816+00:00
-- url     : https://prove2.me/submissions/280120c7-e4a1-4246-8481-67d85a79cc2a

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_Section
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_Residue
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
namespace Reformulated.AutPerF
theorem _root_.solution (a : ResidueField A) :
    modPToResidue p A (residueSection p A a) = a := by
  obtain ⟨a, rfl⟩ := (iterateFrobeniusEquiv (ResidueField A) p
    (exists_maximalIdeal_pow_le_span_p p A).choose).surjective a
  obtain ⟨b, rfl⟩ := modPToResidue_surjective p A a
  rw [residueSection, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe,
    RingEquiv.symm_apply_apply, RingHom.liftOfSurjective_comp_apply]
  simp [iterateFrobenius_def, iterateFrobeniusEquiv_def]
end Reformulated.AutPerF
