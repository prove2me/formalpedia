-- Prove2me | solution 1 for Stanley.eval_neg_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T01:01:43.197873+00:00
-- url     : https://prove2.me/submissions/5ad455c0-ea10-4b07-b600-7feb61c219a6

module
public import Definitions.Def_Stanley_Convolution
public import Mathlib.Tactic.NormNum
public import Definitions.Def_Stanley_NegOne
public import Theorems.Thm_Stanley_orientationCount_induce_univ
public import Theorems.Thm_Stanley_orientationCount_empty
public import Theorems.Thm_Stanley_chromaticPolynomial_empty
public import Theorems.Thm_Stanley_signed_sources
public import Theorems.Thm_Stanley_chromaticPolynomial_induce_univ
public import Theorems.Thm_Stanley_chromaticPolynomial_iso
public import Theorems.Thm_Stanley_independent_recurrence
attribute [local simp] Stanley.chromaticPolynomial_induce_univ


attribute [local simp] Stanley.orientationCount_induce_univ

set_option autoImplicit true
@[expose] public section
public section
open Stanley
open SimpleGraph Finset Polynomial
universe u
variable {V : Type u} [Fintype V] (G : SimpleGraph V)
namespace Stanley
theorem _root_.solution : (chromaticPolynomial G).eval (-1) =
    (-1 : ℤ) ^ Fintype.card V * orientationCount G := by
  classical
  have aux : ∀ n : ℕ, ∀ (W : Type u) [Fintype W] (H : SimpleGraph W),
      Fintype.card W = n → (chromaticPolynomial H).eval (-1) =
        (-1 : ℤ) ^ Fintype.card W * orientationCount H := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro W _ H hn
      by_cases hzero : n = 0
      · have : IsEmpty W := Fintype.card_eq_zero_iff.mp (hn.trans hzero)
        simp [chromaticPolynomial_empty, orientationCount_empty]
      · have : Nonempty W := Fintype.card_pos_iff.mp (by omega)
        let f (s : Finset W) : ℤ := if Independent H (s : Set W) then
          (chromaticPolynomial (H.induce (s : Set W)ᶜ)).eval (-1) else 0
        let g (s : Finset W) : ℤ := if Independent H (s : Set W) then
          (-1 : ℤ) ^ Fintype.card ↥((s : Set W)ᶜ) *
            orientationCount (H.induce (s : Set W)ᶜ) else 0
        have hdiff : ∑ s : Finset W, (f s - g s) = 0 := by
          rw [Finset.sum_sub_distrib]
          change (∑ s : Finset W, f s) - (∑ s : Finset W, g s) = 0
          rw [show (∑ s : Finset W, f s) = 0 from independent_recurrence H,
            show (∑ s : Finset W, g s) = 0 from signed_sources H, sub_self]
        have hsingle : (∑ s : Finset W, (f s - g s)) = f ∅ - g ∅ := by
          apply Finset.sum_eq_single ∅
          · intro s _ hs
            have hsne : s.Nonempty := Finset.nonempty_iff_ne_empty.mpr hs
            obtain ⟨v, hv⟩ := hsne
            have hcard : Fintype.card ↥((s : Set W)ᶜ) < n := by
              rw [← hn]
              exact Fintype.card_subtype_lt (p := fun v => v ∉ (s : Set W)) (by simpa)
            have h := ih _ hcard _ (H.induce (s : Set W)ᶜ) rfl
            simp only [f, g, h, sub_self]
          · simp
        rw [hsingle] at hdiff
        let e : H.induce (((∅ : Finset W) : Set W)ᶜ) ≃g H :=
          { toEquiv :=
              { toFun := Subtype.val
                invFun := fun v => ⟨v, by simp⟩
                left_inv := fun _ => rfl
                right_inv := fun _ => rfl }
            map_rel_iff' := by intros; rfl }
        have hp := chromaticPolynomial_iso _ _ e
        have ha : orientationCount (H.induce (((∅ : Finset W) : Set W)ᶜ)) =
            orientationCount H := by
          unfold orientationCount
          exact_mod_cast Nat.card_congr (AcyclicOrientation.mapEquiv e)
        have hc := Fintype.card_congr e.toEquiv
        have hi : Independent H ((∅ : Finset W) : Set W) := by
          intro u hu
          simp at hu
        simp only [f, g, if_pos hi] at hdiff
        rw [hp, hc, ha] at hdiff
        exact sub_eq_zero.mp hdiff
  exact aux _ V G rfl
end Stanley
