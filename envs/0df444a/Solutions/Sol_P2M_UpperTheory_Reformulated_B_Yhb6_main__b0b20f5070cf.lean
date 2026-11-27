-- Prove2me | solution 1 for P2M_UpperTheory_Reformulated_B_Yhb6_main__b0b20f5070cf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T05:13:51.721939+00:00
-- url     : https://prove2.me/submissions/a78f7170-b59c-4edf-970b-16bce29ed741

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_CardFiber
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace MultisetMapEqExistsEquivPerm
private lemma card_fiber {α : Type*} [DecidableEq α] {l : ℕ} (x : Fin l → α) (v : α) :
    Fintype.card {a : Fin l // x a = v} =
      (Multiset.map x Finset.univ.val).countP (fun b => b = v) := by
  rw [Multiset.countP_map, Fintype.card_subtype]
  rfl
end MultisetMapEqExistsEquivPerm
end

set_option autoImplicit false

namespace UpperTheory.Reformulated.B.Yhb6.main
theorem _root_.solution.{u_1} :
    ∀ {α : Type u_1} {l : ℕ} {x y : Fin l → α},
      Multiset.map y Finset.univ.val = Multiset.map x Finset.univ.val →
        ∃ (e : Equiv.Perm (Fin l)), ∀ (a : Fin l), y a = x ((e : Fin l → Fin l) a) := by
  intro α l x y h
  classical
  have hc : ∀ v : α, Fintype.card {a : Fin l // y a = v} = Fintype.card {a : Fin l // x a = v} := by
    intro v
    convert (MultisetMapEqExistsEquivPerm.card_fiber y v).trans
      ((congrArg (fun m => Multiset.countP (fun b => b = v) m) h).trans (MultisetMapEqExistsEquivPerm.card_fiber x v).symm)
  let E : ∀ v : α, {a : Fin l // y a = v} ≃ {a : Fin l // x a = v} :=
    fun v => Fintype.equivOfCardEq (hc v)
  refine ⟨Equiv.ofFiberEquiv E, fun a => ?_⟩
  exact (Equiv.ofFiberEquiv_map E a).symm
end UpperTheory.Reformulated.B.Yhb6.main
