-- Prove2me | solution 1 for P2M_Bl_general_b_fact_third_____goal1_dd5cc179dc85
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T13:41:40.851373+00:00
-- url     : https://prove2.me/submissions/de38cf0f-a096-483e-aca8-b0e2d6b91f40

import Mathlib
import Definitions.Def_Formalism_HermitianLattices_StatementLat
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_SArith
import Definitions.Def_Formalism_LocalRingCardinality_Params
import Definitions.Def_Formalism_LocalRingCardinality_DataSpaces
import Definitions.Def_Formalism_LocalRingCardinality_DataCoeff
import Definitions.Def_Formalism_LocalRingCardinality_DataArith
import Definitions.Def_Formalism_LocalRingCardinality_DataKernels
import Definitions.Def_Formalism_LocalRingCardinality_DataRows
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_DataS
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_DataG
import Definitions.Def_Formalism_LocalRingCardinality_DataCD
import Definitions.Def_Formalism_FrobeniusOrbits_DiscrMaximalRealCyclotomic
import Definitions.Def_Formalism_FrobeniusOrbits_HostOrbitsPlaces
import Definitions.Def_Formalism_FrobeniusOrbits_HostDiffSupport
import Definitions.Def_Formalism_FrobeniusOrbits_HostThickExists
import Definitions.Def_Formalism_FrobeniusOrbits_HostOrbitCountSg
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_ConjEMemHostFIff
import Definitions.Def_Formalism_CoboundaryTransfers_Statement
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_RealCyclotomicSubfield
import Definitions.Def_Formalism_FrobeniusOrbits_Statement
import Definitions.Def_Formalism_TameInertiaTowers_FinalGroup
import Definitions.Def_Formalism_TameInertiaTowers_CentralOrderTwo_Galois
import Definitions.Def_Formalism_TameInertiaTowers_CentralOrderTwo_ConjEqInvOfPowEqOne
import Definitions.Def_Lemmata_GeneralBFactThirdRest_Imports

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Bl Bl.general_b_fact_third''''
namespace Bl.general_b_fact_third''''
theorem _root_.solution :
  ∀ {E : Type} [inst : Field.{0} E] [inst_1 : NumberField.{0} E] [inst_2 : StarRing.{0} E] (S : Formalism.BasicNotions.HSpace E)
  (Λ : Submodule.{0, 0} (NumberField.RingOfIntegers.{0} E) S.V),
  Submodule.IsLattice.{0, 0, 0} E Λ →
    ∀ (x : S.V),
      Exists.{1} fun (a : NumberField.RingOfIntegers.{0} E) ↦
        And (Ne.{1} a 0) (Membership.mem.{0, 0} Λ (HSMul.hSMul.{0, 0, 0} a x)) := by
  intro E _ _ _ S Λ hL x
  have hx : x ∈ Submodule.span E (Λ : Set S.V) := by
    rw [hL.2]; exact Submodule.mem_top
  induction hx using Submodule.span_induction with
  | mem y hy => exact ⟨1, one_ne_zero, by rw [one_smul]; exact hy⟩
  | zero => exact ⟨1, one_ne_zero, by rw [smul_zero]; exact Λ.zero_mem⟩
  | add y z _ _ hy hz =>
    obtain ⟨a, ha, hay⟩ := hy
    obtain ⟨b, hb, hbz⟩ := hz
    refine ⟨a * b, mul_ne_zero ha hb, ?_⟩
    have h1 : (a * b) • y = b • (a • y) := by rw [mul_comm, mul_smul]
    have h2 : (a * b) • z = a • (b • z) := by rw [mul_smul]
    rw [smul_add, h1, h2]
    exact Λ.add_mem (Λ.smul_mem b hay) (Λ.smul_mem a hbz)
  | smul c y _ hy =>
    obtain ⟨a, ha, hay⟩ := hy
    obtain ⟨w, hw⟩ := IsLocalization.surj (nonZeroDivisors (NumberField.RingOfIntegers E)) c
    refine ⟨(w.2 : NumberField.RingOfIntegers E) * a, mul_ne_zero (nonZeroDivisors.ne_zero w.2.2) ha, ?_⟩
    have key : ((w.2 : NumberField.RingOfIntegers E) * a) • (c • y) = w.1 • (a • y) := by
      rw [← algebraMap_smul E ((w.2 : NumberField.RingOfIntegers E) * a), ← algebraMap_smul E w.1,
        ← algebraMap_smul E a, smul_smul, smul_smul, ← hw, map_mul]
      congr 1
      ring
    rw [key]
    exact Λ.smul_mem w.1 hay
end Bl.general_b_fact_third''''
