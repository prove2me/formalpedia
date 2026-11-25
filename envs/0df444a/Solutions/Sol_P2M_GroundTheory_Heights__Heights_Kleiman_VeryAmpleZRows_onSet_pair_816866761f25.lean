-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_VeryAmpleZRows_onSet_pair_816866761f25
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T08:42:49.864907+00:00
-- url     : https://prove2.me/submissions/5bd81705-6a4d-4afb-a82b-f339be16ee0e

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_VeryAmpleZRowsSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_CechPartitionSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_ZChartSmulSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_ZChartLocalSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PVeryAmpleZRows
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_VeryAmpleZRows_d_eq_e6c0efb7ec0f

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
noncomputable section
universe u v w
open GroundTheory.Heights₂.Heights.Kleiman.VeryAmpleZRows
variable {R : Type u} [CommRing R] {V : Type v} [AddCommGroup V] [Module R V] {n : ℕ} {U : Finset (Fin n)}
namespace GroundTheory.Heights₂.Heights.Kleiman.VeryAmpleZRows
theorem _root_.solution {s : Cech.Cochain (fun _ : Cell U => V) 0}
    (hs : Cech.d (fun _ : Cell U => V) (Cech.idRes R V U) 0 s = 0) {a b : Fin n} (ha : a ∈ U) (hb : b ∈ U)
    (hab : a < b) : onSet s {a} = onSet s {b} := by
  have hcard : ({a, b} : Finset (Fin n)).card = 0 + 1 + 1 := Finset.card_pair hab.ne
  have h := congrFun hs ⟨⟨{a, b}, Finset.insert_nonempty _ _,
    Finset.insert_subset ha (Finset.singleton_subset_iff.mpr hb)⟩, hcard⟩
  rw [d_eq] at h
  change ∑ j ∈ ({a, b} : Finset (Fin n)), Cech.sgn {a, b} j • onSet s (({a, b} : Finset _).erase j) = 0 at h
  rw [Finset.sum_pair hab.ne, Finset.erase_insert (Finset.notMem_singleton.mpr hab.ne),
    Finset.erase_insert_of_ne hab.ne, Finset.erase_singleton, insert_empty_eq] at h
  have e1 : Cech.sgn ({a, b} : Finset (Fin n)) a = 1 := by
    simp [Cech.sgn, Finset.filter_insert, Finset.filter_singleton, not_lt.mpr hab.le]
  have e2 : Cech.sgn ({a, b} : Finset (Fin n)) b = -1 := by
    simp [Cech.sgn, Finset.filter_insert, Finset.filter_singleton, hab]
  rw [e1, e2, one_smul, neg_one_smul, ← sub_eq_add_neg, sub_eq_zero] at h
  exact h.symm
end GroundTheory.Heights₂.Heights.Kleiman.VeryAmpleZRows
