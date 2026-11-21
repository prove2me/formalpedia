-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Intake100.P88.corner_endomorphisms
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-20T08:57:32.361179+00:00
-- url     : https://prove2.me/submissions/14ddb762-1272-4901-bb07-09cd47cc3b5c

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P88
noncomputable section

namespace QAlgorithms.Papers.Independent.Intake100.P88

attribute [local instance] Classical.propDecidable

universe u

theorem _root_.solution (A : Type u) [Ring A] [Algebra ℂ A]
    (p : A) (_hp0 : p ≠ 0) (hp : IsIdempotentElem p) :
    ∃ e : hp.Cornerᵐᵒᵖ ≃+* Module.End A (principalLeftIdeal p),
      ∀ c : hp.Corner, ∀ a : principalLeftIdeal p,
        ((e (MulOpposite.op c)) a : A) = (a : A) * c.val := by
  have cmem : ∀ c : hp.Corner, p * c.val = c.val ∧ c.val * p = c.val :=
    fun c => (Subsemigroup.mem_corner_iff hp).mp c.2
  have pmem : p ∈ principalLeftIdeal p := hp.eq
  let R : hp.Corner → Module.End A (principalLeftIdeal p) := fun c =>
    { toFun := fun a => ⟨(a : A) * c.val, by
        change (a : A) * c.val * p = (a : A) * c.val
        rw [mul_assoc, (cmem c).2]⟩
      map_add' := fun a b => by ext; simp [add_mul]
      map_smul' := fun r a => by ext; simp [smul_eq_mul, mul_assoc] }
  have fpmem : ∀ f : Module.End A (principalLeftIdeal p),
      ((f ⟨p, pmem⟩ : principalLeftIdeal p) : A) ∈ Subsemigroup.corner p := by
    intro f
    rw [Subsemigroup.mem_corner_iff hp]
    refine ⟨?_, (f ⟨p, pmem⟩).2⟩
    have h1 : (p • (⟨p, pmem⟩ : principalLeftIdeal p)) = ⟨p, pmem⟩ := by
      ext; exact hp.eq
    have h2 := congrArg (fun x : principalLeftIdeal p => (x : A)) (f.map_smul p ⟨p, pmem⟩)
    simp only [h1] at h2
    have h3 : ((p • f ⟨p, pmem⟩ : principalLeftIdeal p) : A) = p * (f ⟨p, pmem⟩ : A) := rfl
    rw [← h3]; exact h2.symm
  let Inv : Module.End A (principalLeftIdeal p) → hp.Corner := fun f => ⟨_, fpmem f⟩
  refine ⟨{ toFun := fun c => R c.unop
            invFun := fun f => MulOpposite.op (Inv f)
            left_inv := fun c => by
              apply MulOpposite.unop_injective
              apply Subtype.ext
              change p * c.unop.val = c.unop.val
              exact (cmem _).1
            right_inv := fun f => by
              ext a
              change (a : A) * ((f ⟨p, pmem⟩ : principalLeftIdeal p) : A) = ((f a : principalLeftIdeal p) : A)
              have ha : (a : A) • (⟨p, pmem⟩ : principalLeftIdeal p) = a := by
                ext; exact a.2
              have h2 := congrArg (fun x : principalLeftIdeal p => (x : A)) (f.map_smul (a : A) ⟨p, pmem⟩)
              simp only [ha] at h2
              rw [h2]; rfl
            map_mul' := fun c d => by
              ext a
              change (a : A) * (d.unop.val * c.unop.val) = (a : A) * d.unop.val * c.unop.val
              rw [mul_assoc]
            map_add' := fun c d => by
              ext a
              change (a : A) * (c.unop.val + d.unop.val) = (a : A) * c.unop.val + (a : A) * d.unop.val
              rw [mul_add] }, ?_⟩
  intro c a
  rfl

end QAlgorithms.Papers.Independent.Intake100.P88
