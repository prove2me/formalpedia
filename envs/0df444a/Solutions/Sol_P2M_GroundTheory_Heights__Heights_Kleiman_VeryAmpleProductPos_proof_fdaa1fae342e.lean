-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_VeryAmpleProductPos_proof_fdaa1fae342e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T05:03:30.337799+00:00
-- url     : https://prove2.me/submissions/d33bd42c-648b-46e9-9ba3-dcf9bd19b0b2

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_VeryAmpleProductPosSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PointDegreePosSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_CutComponentSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_CutMultPosSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PVeryAmpleProductPos
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_exists_sec_not_mem_625a28c0b3ac


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
open MvPolynomial
noncomputable section
universe u w
namespace GroundTheory.Heights₂.Heights.Kleiman
namespace VeryAmpleProductPos
theorem _root_.solution (hR : GenericPointSectionInput.Statement.{u, w}) (hP : PointDegreePos.Statement.{u, w})
    (hC : CutComponent.Statement.{u, w}) (hM : CutMultPos.Statement.{u}) :
    VeryAmpleProductPos.Statement.{u, w} := by
  intro k _ Ω _ _ N x e
  induction e with
  | zero =>
    intro pp L hW _
    have h0 : (fun i => (L i).toSubSystem) = (![] : Fin 0 → SubSystem k x Ω) :=
      funext fun i => i.elim0
    rw [h0, (hR k Ω N x).2.2.2.2 pp hW]
    exact_mod_cast hP k Ω N x pp hW
  | succ n ih =>
    intro pp L hW hL
    obtain ⟨s, hs, hsI⟩ := exists_sec_not_mem (L (Fin.last n)) (hL _) hW
    have hsplit : (fun i => (L i).toSubSystem) = Fin.snoc (α := fun _ => SubSystem k x Ω)
        (fun i : Fin n => (L (Fin.castSucc i)).toSubSystem) (L (Fin.last n)).toSubSystem :=
      (Fin.snoc_init_self _).symm
    rw [hsplit, (hR k Ω N x).2.2.2.1 n pp (fun i => L (Fin.castSucc i)) (L (Fin.last n)) s hW hs hsI]
    obtain ⟨q₀, hq₀, hq₀W⟩ := hC k Ω N x n pp (L (Fin.last n)) s hW (hL _) hs hsI

    have hterm : ∀ qq (h : qq ∈ (pp ⊔ zeroIdeal (L (Fin.last n)).toSubSystem s).minimalPrimes),
        IsSubvar x qq n → haveI : qq.IsPrime := h.1.1
        0 < (((cutMult (pp ⊔ zeroIdeal (L (Fin.last n)).toSubSystem s) qq).toNat : ℤ) *
          interNum qq (fun i => (L (Fin.castSucc i)).toSubSystem)) := by
      intro qq h hqW
      have hm := hM k N _ qq h
      exact mul_pos (by exact_mod_cast ENat.toNat_pos hm.1.ne' hm.2.ne) (ih qq _ hqW fun i => hL _)
    refine lt_of_lt_of_le ?_ (single_le_finsum q₀ ?_ ?_)
    · rw [dif_pos ⟨hq₀, hq₀W⟩]
      exact hterm q₀ hq₀ hq₀W
    · refine (Ideal.finite_minimalPrimes_of_isNoetherianRing _
        (pp ⊔ zeroIdeal (L (Fin.last n)).toSubSystem s)).subset fun qq hqq => ?_
      by_contra hn
      exact hqq (dif_neg fun h => hn h.1)
    · intro qq
      split_ifs with h
      · exact (hterm qq h.1 h.2).le
      · exact le_rfl
end VeryAmpleProductPos
end GroundTheory.Heights₂.Heights.Kleiman
