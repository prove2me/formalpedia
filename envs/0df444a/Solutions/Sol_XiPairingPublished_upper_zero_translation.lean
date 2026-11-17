-- Prove2me | solution 1 for XiPairingPublished.upper_zero_translation
-- status  : ACCEPTED   (prove)
-- author  : @bueno_ricardo
-- created : 2026-11-16T11:19:56.628201+00:00
-- url     : https://prove2.me/submissions/a39f990e-ea3f-4d2a-ae25-f23a66fbce1e

import Mathlib
open Complex
namespace ShiftedIndex
abbrev Upper (f : ℂ → ℂ) := (z : {z : ℂ // 0 < z.im}) × Fin (analyticOrderNatAt f z.val)
abbrev Occurrence (f : ℂ → ℂ) := (z : {z : ℂ // f z = 0 ∧ 0 < z.im}) × Fin (analyticOrderNatAt f z.val)

theorem order_shift (f : ℂ → ℂ) (c : ℝ) (z : ℂ) :
    analyticOrderNatAt (fun w => f (w+(c : ℂ))) z = analyticOrderNatAt f (z+c) := by
  have h := analyticOrderAt_comp_of_deriv_ne_zero (f := f)
    (g := fun w : ℂ => w+(c : ℂ)) (z₀ := z) (by fun_prop) (by simp)
  exact congrArg ENat.toNat h

def forward (f : ℂ → ℂ) (c : ℝ) (p : Upper (fun w => f (w+(c : ℂ)))) : Occurrence f :=
  ⟨⟨p.1.val+c, by
      have h : analyticOrderNatAt f (p.1.val+c) ≠ 0 := by
        rw [← order_shift]; have := p.2.isLt; omega
      exact ⟨apply_eq_zero_of_analyticOrderNatAt_ne_zero h, by simpa using p.1.property⟩⟩,
    ⟨p.2.val, by rw [← order_shift]; exact p.2.isLt⟩⟩

def backward (f : ℂ → ℂ) (c : ℝ) (p : Occurrence f) : Upper (fun w => f (w+(c : ℂ))) :=
  ⟨⟨p.1.val-c, by simpa using p.1.property.2⟩,
    ⟨p.2.val, by rw [order_shift, sub_add_cancel]; exact p.2.isLt⟩⟩

theorem fin_heq {n m : ℕ} (h : n = m) {i : Fin n} {j : Fin m}
    (hv : i.val = j.val) : HEq i j := by
  subst m
  exact heq_of_eq (Fin.ext hv)

def equiv (f : ℂ → ℂ) (c : ℝ) : Upper (fun w => f (w+(c : ℂ))) ≃ Occurrence f where
  toFun := forward f c
  invFun := backward f c
  left_inv p := by
    apply Sigma.ext (Subtype.ext (add_sub_cancel_right p.1.val (c : ℂ)))
    have h : analyticOrderNatAt (fun w => f (w+(c : ℂ))) ((p.1.val+c)-c) =
        analyticOrderNatAt (fun w => f (w+(c : ℂ))) p.1.val := by rw [add_sub_cancel_right]
    exact fin_heq h rfl
  right_inv p := by
    apply Sigma.ext (Subtype.ext (sub_add_cancel p.1.val (c : ℂ)))
    have h : analyticOrderNatAt f ((p.1.val-c)+c) = analyticOrderNatAt f p.1.val := by rw [sub_add_cancel]
    exact fin_heq h rfl

end ShiftedIndex
#print axioms ShiftedIndex.equiv

theorem solution (f : ℂ → ℂ) (c : ℝ) :
    let U := (z : {z : ℂ // 0 < z.im}) × Fin (analyticOrderNatAt (fun w => f (w+(c : ℂ))) z.val)
    let Z := (z : {z : ℂ // f z = 0 ∧ 0 < z.im}) × Fin (analyticOrderNatAt f z.val)
    ∃ e : U ≃ Z, ∀ p, (e p).1.val = p.1.val+c ∧ (e p).2.val = p.2.val :=
  ⟨ShiftedIndex.equiv f c,fun _ => ⟨rfl,rfl⟩⟩
#print axioms solution
