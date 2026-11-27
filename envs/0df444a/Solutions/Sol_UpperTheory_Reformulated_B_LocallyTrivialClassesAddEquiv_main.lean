-- Prove2me | solution 1 for UpperTheory.Reformulated.B.LocallyTrivialClassesAddEquiv.main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T05:33:27.622814+00:00
-- url     : https://prove2.me/submissions/cfd3553a-ab9b-4b7c-a795-ac7887505970

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_FirstStatementD

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

namespace UpperTheory.Reformulated.B.LocallyTrivialClassesAddEquiv
theorem _root_.solution :
    ∀ {R ι H C : Type} [inst : CommRing R] [inst_1 : AddCommGroup H] [inst_2 : _root_.Module R H] [inst_3 : AddCommGroup C]
      {Hv Cv : ι → Type} [inst_4 : (v : ι) → AddCommGroup (Hv v)] [inst_5 : (v : ι) → AddCommGroup (Cv v)]
      (res : (v : ι) → H →+ Hv v) (pres : (v : ι) → C →+ Cv v) (E : H ≃+ C) (Ev : (v : ι) → Hv v ≃+ Cv v),
      (∀ (v : ι) (x : H), (Ev v : Hv v → Cv v) ((res v : H → Hv v) x) = (pres v : C → Cv v) ((E : H → C) x)) →
        ∀ (U : Submodule R H) (T : AddSubgroup C),
          (∀ (x : H), x ∈ U ↔ ∀ (v : ι), (res v : H → Hv v) x = (0 : Hv v)) →
            (∀ (y : C), y ∈ T ↔ ∀ (v : ι), (pres v : C → Cv v) y = (0 : Cv v)) → Nonempty (↥U ≃+ ↥T) := by
  intro R ι H C _ _ _ _ Hv Cv _ _ res pres E Ev hcomm U T hU hT
  have key : ∀ x : H, x ∈ U ↔ E x ∈ T := by
    intro x
    rw [hU, hT]
    refine forall_congr' fun v => ?_
    rw [← hcomm v x]
    constructor
    · intro h; rw [h, map_zero]
    · intro h
      have := congrArg (Ev v).symm h
      simpa using this
  exact ⟨{ toFun := fun x => ⟨E x.1, (key x.1).1 x.2⟩
           invFun := fun y => ⟨E.symm y.1, (key _).2 (by simpa using y.2)⟩
           left_inv := fun x => by ext; simp
           right_inv := fun y => by ext; simp
           map_add' := fun x y => by ext; simp }⟩
end UpperTheory.Reformulated.B.LocallyTrivialClassesAddEquiv
