-- Prove2me | solution 1 for PositivityTheory.ThKG.Fub.unitInvariant_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:00:38.374846+00:00
-- url     : https://prove2.me/submissions/9f880419-2bb1-48ef-a51f-b556371dc803

import Mathlib
import Definitions.Def_Development_WeilBound_ThetaLifts_LocalTheory_ConeShifts_FubGen
import Theorems.Thm_PositivityTheory_ThKG_Fub_coe_unitP
import Theorems.Thm_PositivityTheory_ThKG_Fub_idem_add

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PositivityTheory PositivityTheory.ThKG PositivityTheory.ThKG.Fub
open MeasureTheory Topology Filter
open scoped NNReal
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G]
  [T2Space G] [MeasurableSpace G] [BorelSpace G]
variable {S A B : Subgroup G} {p q : G →* G}
variable {R : Type} [CommRing R]
variable {P : R → G →* G} {K : Subgroup G} {U : Set G} {good : R → Prop}
namespace PositivityTheory.ThKG.Fub
theorem _root_.solution {A : Type} [Ring A] [Algebra R A] {a b : R} (ha : a * a = a) (hb : b * b = b) (h : a * b = 0) (x : Aˣ) :
    unitP (a + b) x = unitP a x * unitP b x := by
  ext
  rw [Units.val_mul, coe_unitP ha, coe_unitP hb, coe_unitP (idem_add ha hb h)]
  have h1 : a * (1 - b) = a := by linear_combination -h
  have h2 : (1 - a) * b = b := by linear_combination -h
  have h3 : (1 - a) * (1 - b) = 1 - (a + b) := by linear_combination h
  simp only [add_mul, mul_add, smul_mul_smul_comm, h, h1, h2, h3, zero_smul, mul_one, one_mul, zero_add, add_smul]
  abel
end PositivityTheory.ThKG.Fub
