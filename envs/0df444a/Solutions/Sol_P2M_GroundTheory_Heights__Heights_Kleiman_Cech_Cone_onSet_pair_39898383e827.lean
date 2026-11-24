-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_Cech_Cone_onSet_pair_39898383e827
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T01:01:59.63426+00:00
-- url     : https://prove2.me/submissions/bdf2e7fd-414c-43fc-8acf-0acf6a703a8e

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsSerrePoly
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PCechCone
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_Cech_Cone_sgn_insert_925364762348
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_Cech_Cone_d_eq_93862b1062b9

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
universe u v
open GroundTheory.Heights₂.Heights.Kleiman.Cech GroundTheory.Heights₂.Heights.Kleiman.Cech.Cone
variable {R : Type u} [CommRing R] {V : Type v} [AddCommGroup V] [Module R V] {N : ℕ}
namespace GroundTheory.Heights₂.Heights.Kleiman.Cech.Cone
theorem _root_.solution {z : Cech.Cochain (fun _ : StdCell N => V) 0}
    (hz : Cech.d (fun _ : StdCell N => V) (Cech.idRes R V Finset.univ) 0 z = 0)
    {a b : Fin (N + 1)} (hab : a < b) : onSet z {a} = onSet z {b} := by
  have hcard : ({a, b} : Finset (Fin (N + 1))).card = 0 + 1 + 1 := Finset.card_pair hab.ne
  have h := congrFun hz ⟨⟨{a, b}, Finset.insert_nonempty _ _, Finset.subset_univ _⟩, hcard⟩
  rw [d_eq] at h
  change ∑ j ∈ ({a, b} : Finset (Fin (N + 1))), Cech.sgn {a, b} j • onSet z (({a, b} : Finset _).erase j)
    = 0 at h
  have ha : a ∉ ({b} : Finset (Fin (N + 1))) := Finset.notMem_singleton.mpr hab.ne
  rw [Finset.sum_pair hab.ne, Finset.erase_insert ha, Finset.erase_insert_of_ne hab.ne,
    Finset.erase_singleton, sgn_insert ha, sgn_insert ha, if_neg (lt_irrefl _), if_pos hab] at h
  have e1 : Cech.sgn ({b} : Finset (Fin (N + 1))) a = 1 := by
    simp [Cech.sgn, Finset.filter_singleton, lt_asymm hab]
  have e2 : Cech.sgn ({b} : Finset (Fin (N + 1))) b = 1 := by
    simp [Cech.sgn, Finset.filter_singleton]
  rw [e1, e2, insert_empty_eq] at h
  rw [one_mul, one_smul, one_mul, neg_one_smul, ← sub_eq_add_neg, sub_eq_zero] at h
  exact h.symm
end GroundTheory.Heights₂.Heights.Kleiman.Cech.Cone
