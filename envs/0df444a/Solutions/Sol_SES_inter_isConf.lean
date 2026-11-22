-- Prove2me | solution 1 for SES.inter_isConf
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T21:14:47.697804+00:00
-- url     : https://prove2.me/submissions/238c7dca-5708-4ca3-ae30-30f95d2671bb

import Definitions.Def_EventStructures_General_Basic
import Definitions.Def_EventStructures_General_Stable
import Theorems.Thm_SES_toFamily_Config
import Theorems.Thm_GES_toFamily_Config
import Theorems.Thm_GES_toFamily_Event
attribute [local simp] GES.toFamily_Config
attribute [local simp] GES.toFamily_Event


attribute [local simp] SES.toFamily_Config

set_option autoImplicit true
open SES
variable {L : Type*} (S : SES L)
local infix:50 " ⊢ " => S.enable
variable {S}
open GES
namespace SES
theorem _root_.solution {x y z : Set S.Event} (hx : S.toGES.isConf x) (hy : S.toGES.isConf y)
    (hz : S.toGES.isConf z) (hxz : x ⊆ z) (hyz : y ⊆ z) : S.toGES.isConf (x ∩ y) := by
  classical
  refine ⟨fun X hX => hz.1 X (hX.trans (fun _ hw => hxz hw.1)), ?_⟩
  have key : ∀ n e, e ∈ x → e ∈ y → S.toGES.rank x e = n →
      ∃ m, e ∈ S.toGES.secApprox (x ∩ y) m := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      rintro e hex hey rfl
      obtain ⟨k, hk⟩ : ∃ k, S.toGES.rank x e = k + 1 := by
        have : S.toGES.rank x e ≠ 0 := by
          intro h0
          have hmem := rank_mem (hx.2 e hex)
          rw [h0] at hmem
          exact hmem
        exact ⟨S.toGES.rank x e - 1, by omega⟩
      obtain ⟨-, X, hXsub, hXen⟩ := hk ▸ rank_mem (hx.2 e hex)
      obtain ⟨j, hj⟩ := hy.2 e hey
      obtain ⟨k', hk'⟩ : ∃ k', j = k' + 1 := by
        cases j with
        | zero => exact hj.elim
        | succ k' => exact ⟨k', rfl⟩
      obtain ⟨-, Y, hYsub, hYen⟩ := hk' ▸ hj
      have hXx : ↑X ⊆ x := hXsub.trans (secApprox_subset k)
      have hYy : ↑Y ⊆ y := hYsub.trans (secApprox_subset k')
      have hcons : S.toGES.Consistent (↑X ∪ ↑Y ∪ {e}) :=
        fun W hW => hz.1 W (hW.trans (by
          rintro w ((hw | hw) | hw)
          · exact hxz (hXx hw)
          · exact hyz (hYy hw)
          · exact hxz (Set.mem_singleton_iff.mp hw ▸ hex)))
      have hen : (X ∩ Y) ⊢ e :=
        S.enable_inter hXen hYen hcons (by simp)
      obtain ⟨N, hN⟩ := exists_bound (x := x ∩ y) fun g hg => by
        rw [Finset.mem_inter] at hg
        refine ih _ ?_ g (hXx hg.1) (hYy hg.2) rfl
        exact hk ▸ Nat.lt_succ_of_le (rank_le (hXsub hg.1))
      exact ⟨N + 1, ⟨hex, hey⟩, X ∩ Y, hN, hen⟩
  exact fun e he => key _ e he.1 he.2 rfl
end SES
