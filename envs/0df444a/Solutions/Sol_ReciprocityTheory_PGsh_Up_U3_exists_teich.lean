-- Prove2me | solution 1 for ReciprocityTheory.PGsh.Up.U3.exists_teich
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T15:37:20.883243+00:00
-- url     : https://prove2.me/submissions/5d7b9247-d1cd-49c2-984a-e6996302f4ff

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_VIntCastLtOneOfDvd
import Theorems.Thm_ReciprocityTheory_PGsh_Up_U3_v_intCast_lt_one_of_dvd

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open ReciprocityTheory ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Up.U3
variable {p : ℕ} [hp : Fact p.Prime] {C : Type} [Field C] {v : Valuation C NNReal}
  {R : Type} [CommRing R] [Algebra R C]
namespace ReciprocityTheory.PGsh.Up.U3
theorem _root_.solution [IsAlgClosed C] (hv : v.Integers R) (hpv : v (p : C) < 1) (n : ℕ) :
    ∃ r : C, r ^ p = r ∧ v (r - n) < 1 := by
  have hdvd : (p : ℤ) ∣ ((n : ℤ) ^ p - n) := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    rw [ZMod.pow_card, sub_self]
  have hv1 : v ((n : C) ^ p - n) < 1 := by
    have := v_intCast_lt_one_of_dvd hv hpv hdvd
    push_cast at this
    exact this
  have hmon : (Polynomial.X ^ p - Polynomial.X : Polynomial C).Monic :=
    Polynomial.monic_X_pow_sub (by rw [Polynomial.degree_X]; exact_mod_cast hp.out.one_lt)
  have heq : (Polynomial.X ^ p - Polynomial.X : Polynomial C) =
      ((Polynomial.X ^ p - Polynomial.X : Polynomial C).roots.map (fun a => Polynomial.X - Polynomial.C a)).prod := by
    first
    | exact Polynomial.eq_prod_roots_of_monic_of_splits_id hmon (IsAlgClosed.splits _)
    | exact (Polynomial.Monic.eq_prod_roots_of_splits_id hmon (IsAlgClosed.splits _))
    | (have hc := Polynomial.C_leadingCoeff_mul_prod_multiset_X_sub_C
          (Polynomial.splits_iff_card_roots.mp (IsAlgClosed.splits (Polynomial.X ^ p - Polynomial.X : Polynomial C)))
       rw [hmon.leadingCoeff, map_one, one_mul] at hc
       exact hc.symm)
    | (have hc := Polynomial.C_leadingCoeff_mul_prod_multiset_X_sub_C
          (IsAlgClosed.card_roots_eq_natDegree (k := C) (p := Polynomial.X ^ p - Polynomial.X))
       rw [hmon.leadingCoeff, map_one, one_mul] at hc
       exact hc.symm)
  have heval : (n : C) ^ p - n =
      ((Polynomial.X ^ p - Polynomial.X : Polynomial C).roots.map (fun a => (n : C) - a)).prod := by
    have := congrArg (Polynomial.eval (n : C)) heq
    rw [Polynomial.eval_multiset_prod, Multiset.map_map] at this
    simpa [Function.comp_def] using this
  by_contra hno
  push_neg at hno
  have hge : 1 ≤ v ((n : C) ^ p - n) := by
    rw [heval, map_multiset_prod, Multiset.map_map]
    apply Multiset.one_le_prod_of_one_le
    intro x hx
    obtain ⟨a, ha, rfl⟩ := Multiset.mem_map.mp hx
    have h2 := (Polynomial.mem_roots hmon.ne_zero).mp ha
    rw [Polynomial.IsRoot, Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X] at h2
    have h3 := hno a (sub_eq_zero.mp h2)
    simp only [Function.comp_apply]
    rwa [Valuation.map_sub_swap]
  exact absurd hv1 (not_lt.mpr hge)
end ReciprocityTheory.PGsh.Up.U3
