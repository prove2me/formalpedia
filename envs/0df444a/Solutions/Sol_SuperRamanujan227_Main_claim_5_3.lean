-- Prove2me | solution 1 for SuperRamanujan227.Main.claim_5_3
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T03:27:08.937541+00:00
-- url     : https://prove2.me/submissions/56b1f2c9-4636-423d-ab43-58d707ea6477

import Mathlib
import Definitions.Def_SuperRamanujan227_Main_Spectra

section
set_option autoImplicit false
open Polynomial

namespace SuperRamanujan227.Dev.Base
open SuperRamanujan227.Main

lemma alpha1_def (P : ℝ[X]) : kthLargestRoot P 1 = (P.roots.sort (· ≥ ·)).getD 0 0 := by
  simp [kthLargestRoot]

lemma sort_cons_form {P : ℝ[X]} (hne : P.roots ≠ 0) :
    ∃ a l, P.roots.sort (· ≥ ·) = a :: l := by
  have hlen : (P.roots.sort (· ≥ ·)).length ≠ 0 := by
    rw [Multiset.length_sort]; simpa using hne
  cases hl : P.roots.sort (· ≥ ·) with
  | nil => rw [hl] at hlen; simp at hlen
  | cons a l => exact ⟨a, l, rfl⟩

lemma alpha1_mem {P : ℝ[X]} (hne : P.roots ≠ 0) : kthLargestRoot P 1 ∈ P.roots := by
  rw [alpha1_def]
  obtain ⟨a, l, hl⟩ := sort_cons_form hne
  rw [hl]
  simp only [List.getD_cons_zero]
  rw [← Multiset.mem_sort (· ≥ ·), hl]
  simp

lemma le_alpha1 {P : ℝ[X]} (hne : P.roots ≠ 0) : ∀ r ∈ P.roots, r ≤ kthLargestRoot P 1 := by
  intro r hr
  rw [alpha1_def]
  obtain ⟨a, l, hl⟩ := sort_cons_form hne
  have hp := Multiset.pairwise_sort P.roots (· ≥ ·)
  rw [hl] at hp
  have hr' : r ∈ a :: l := by rw [← hl]; exact (Multiset.mem_sort (· ≥ ·)).mpr hr
  rw [hl]
  simp only [List.getD_cons_zero]
  rcases List.mem_cons.mp hr' with h | h
  · rw [h]
  · exact (List.pairwise_cons.mp hp).1 r h

lemma rr_roots_ne {P : ℝ[X]} (hP : RealRooted P) (h1 : 1 ≤ P.natDegree) : P.roots ≠ 0 := by
  intro h
  have := hP.2
  rw [h] at this
  simp at this
  omega

lemma prod_pos (s : Multiset ℝ) (x : ℝ) (hx : ∀ r ∈ s, r < x) :
    0 < (s.map (fun r => (X - C r : ℝ[X]))).prod.eval x ∧
      (s ≠ 0 → 0 < (derivative (s.map (fun r => (X - C r : ℝ[X]))).prod).eval x) := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    have hax : a < x := hx a (Multiset.mem_cons_self a s)
    have ih' := ih (fun r hr => hx r (Multiset.mem_cons_of_mem hr))
    obtain ⟨h1, h2⟩ := ih'
    simp only [Multiset.map_cons, Multiset.prod_cons]
    refine ⟨?_, fun _ => ?_⟩
    · simp only [eval_mul, eval_sub, eval_X, eval_C]
      exact mul_pos (by linarith) h1
    · rw [derivative_mul]
      simp only [eval_add, eval_mul, eval_sub, eval_X, eval_C, derivative_sub, derivative_X,
        derivative_C, sub_zero, eval_one, one_mul]
      by_cases hs : s = 0
      · subst hs; simp
      · have := h2 hs
        have := mul_pos (sub_pos.mpr hax) this
        nlinarith [h1]

lemma pos_beyond {P : ℝ[X]} (hP : RealRooted P) (x : ℝ) (hx : ∀ r ∈ P.roots, r < x) :
    0 < P.leadingCoeff * P.eval x ∧
      (1 ≤ P.natDegree → 0 < P.leadingCoeff * (derivative P).eval x) := by
  have hP0 := hP.1
  have hne : P.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hP0
  have heq : P = C P.leadingCoeff * (P.roots.map (fun r => (X - C r : ℝ[X]))).prod :=
    (C_leadingCoeff_mul_prod_multiset_X_sub_C hP.2).symm
  obtain ⟨h1, h2⟩ := prod_pos P.roots x hx
  have hd0 : 1 ≤ P.natDegree → P.roots ≠ 0 := rr_roots_ne hP
  generalize (P.roots.map (fun r => (X - C r : ℝ[X]))).prod = Q at heq h1 h2
  generalize P.leadingCoeff = c at heq hne
  have hlc : 0 < c * c := mul_self_pos.mpr hne
  have hd0' : P.roots ≠ 0 → 0 < (derivative Q).eval x := h2
  constructor
  · rw [heq]
    simp only [eval_mul, eval_C]
    nlinarith
  · intro hd
    have h3 := h2 (hd0 hd)
    rw [heq, derivative_C_mul]
    simp only [eval_mul, eval_C]
    nlinarith

end SuperRamanujan227.Dev.Base
end

section
set_option autoImplicit false
open Polynomial

namespace SuperRamanujan227.Dev.Deriv
open SuperRamanujan227.Main SuperRamanujan227.Dev.Base

lemma natDeg_iter (P : ℝ[X]) (hP : P ≠ 0) (k : ℕ) (hk : k ≤ P.natDegree) :
    (derivative^[k] P).natDegree = P.natDegree - k ∧
    (derivative^[k] P).leadingCoeff = (P.natDegree.descFactorial k : ℝ) * P.leadingCoeff := by
  have hc : (derivative^[k] P).coeff (P.natDegree - k) =
      (P.natDegree.descFactorial k : ℝ) * P.leadingCoeff := by
    rw [coeff_iterate_derivative, Nat.sub_add_cancel hk, nsmul_eq_mul]
    rfl
  have hne : (derivative^[k] P).coeff (P.natDegree - k) ≠ 0 := by
    rw [hc]
    exact mul_ne_zero (by exact_mod_cast (Nat.descFactorial_pos.mpr hk).ne')
      (leadingCoeff_ne_zero.mpr hP)
  have hdeg : (derivative^[k] P).natDegree = P.natDegree - k :=
    natDegree_eq_of_le_of_coeff_ne_zero (natDegree_iterate_derivative P k) hne
  exact ⟨hdeg, by rw [leadingCoeff, hdeg, hc]⟩

lemma rr_deriv {P : ℝ[X]} (hP : RealRooted P) (h1 : 1 ≤ P.natDegree) :
    RealRooted (derivative P) := by
  have hd0 : derivative P ≠ 0 := by
    intro h
    have := (derivative_eq_zero).mp h
    omega
  refine ⟨hd0, ?_⟩
  have h2 := card_roots_le_derivative P
  have h3 := hP.2
  have h4 := natDegree_derivative_le P
  have h5 := card_roots' (derivative P)
  omega

lemma rr_iter {P : ℝ[X]} (hP : RealRooted P) (k : ℕ) (hk : k ≤ P.natDegree) :
    RealRooted (derivative^[k] P) := by
  induction k with
  | zero => simpa using hP
  | succ k ih =>
    have ih' := ih (by omega)
    rw [Function.iterate_succ_apply']
    apply rr_deriv ih'
    rw [(natDeg_iter P hP.1 k (by omega)).1]
    omega

lemma deriv_roots_ne {P : ℝ[X]} (hP : RealRooted P) (h2 : 2 ≤ P.natDegree) :
    (derivative P).roots ≠ 0 := by
  have hr := rr_deriv hP (by omega)
  apply rr_roots_ne hr
  have := (natDeg_iter P hP.1 1 (by omega)).1
  rw [Function.iterate_one] at this
  omega

lemma alpha1_deriv_le {P : ℝ[X]} (hP : RealRooted P) (h2 : 2 ≤ P.natDegree) :
    kthLargestRoot (derivative P) 1 ≤ kthLargestRoot P 1 := by
  have hrd := deriv_roots_ne hP h2
  have hmem := alpha1_mem hrd
  have hP1 := rr_roots_ne hP (by omega)
  by_contra hlt
  rw [not_le] at hlt
  have := (pos_beyond hP (kthLargestRoot (derivative P) 1)
    (fun r hr => lt_of_le_of_lt (le_alpha1 hP1 r hr) hlt)).2 (by omega)
  have hz : (derivative P).eval (kthLargestRoot (derivative P) 1) = 0 :=
    ((mem_roots (rr_deriv hP (by omega)).1).mp hmem)
  rw [hz] at this
  simp at this

lemma lead_deriv {P : ℝ[X]} (hP : P ≠ 0) (h1 : 1 ≤ P.natDegree) :
    (derivative P).leadingCoeff = (P.natDegree : ℝ) * P.leadingCoeff := by
  have := (natDeg_iter P hP 1 h1).2
  rw [Function.iterate_one, Nat.descFactorial_one] at this
  exact this

lemma pos_beyond_lead {P : ℝ[X]} (hP : RealRooted P) (h2 : 2 ≤ P.natDegree) (x : ℝ)
    (hx : kthLargestRoot (derivative P) 1 < x) :
    0 < P.leadingCoeff * (derivative P).eval x := by
  have hrd := rr_deriv hP (by omega)
  have hne := deriv_roots_ne hP h2
  have h := (pos_beyond hrd x (fun r hr => lt_of_le_of_lt (le_alpha1 hne r hr) hx)).1
  rw [lead_deriv hP.1 (by omega)] at h
  have hn : (0 : ℝ) < P.natDegree := by exact_mod_cast (by omega : 0 < P.natDegree)
  nlinarith

lemma T {P : ℝ[X]} (hP : RealRooted P) (h2 : 2 ≤ P.natDegree) :
    P.leadingCoeff * P.eval (kthLargestRoot (derivative P) 1) ≤ 0 := by
  set t := kthLargestRoot (derivative P) 1 with ht
  have hP1 := rr_roots_ne hP (by omega)
  set ρ := kthLargestRoot P 1 with hρ
  have htρ : t ≤ ρ := alpha1_deriv_le hP h2
  have hρroot : P.eval ρ = 0 := ((mem_roots hP.1).mp (alpha1_mem hP1))
  have hmono : MonotoneOn (fun x => P.leadingCoeff * P.eval x) (Set.Ici t) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici t)
    · exact (continuous_const.mul P.continuous).continuousOn
    · exact (differentiable_const _ |>.mul P.differentiable).differentiableOn
    · intro x hx
      rw [interior_Ici] at hx
      have : deriv (fun x => P.leadingCoeff * P.eval x) x = P.leadingCoeff * (derivative P).eval x := by
        rw [deriv_const_mul _ P.differentiableAt, Polynomial.deriv]
      rw [this]
      exact (pos_beyond_lead hP h2 x hx).le
  have := hmono (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr htρ) htρ
  simp only [hρroot, mul_zero] at this
  exact this

end SuperRamanujan227.Dev.Deriv
end

section
set_option autoImplicit false
open Polynomial

namespace SuperRamanujan227.Dev.C53
open SuperRamanujan227.Main SuperRamanujan227.Dev.Base SuperRamanujan227.Dev.Deriv

lemma iter_lin (g : ℝ[X]) (θ : ℝ) (j : ℕ) :
    derivative^[j + 1] ((X - C θ) * g) =
      (X - C θ) * derivative^[j + 1] g + (j + 1 : ℕ) • derivative^[j] g := by
  have : (X - C θ) * g = g * X - C θ * g := by ring
  rw [this, iterate_derivative_sub, iterate_derivative_mul_X, iterate_derivative_C_mul]
  simp only [Nat.add_sub_cancel]
  ring

end SuperRamanujan227.Dev.C53

namespace SuperRamanujan227.Main
open SuperRamanujan227.Dev.Base SuperRamanujan227.Dev.Deriv SuperRamanujan227.Dev.C53

theorem chk_claim_5_3 (f : ℝ[X]) (m : ℕ) (hf : RealRooted f) (hdeg : f.natDegree = m)
    (hm : 2 ≤ m) (k : ℕ) (hk : k ≤ m - 2) :
    kthLargestRoot (derivative^[k] (f /ₘ (X - C (kthLargestRoot f 1)))) 1 ≤
      kthLargestRoot (derivative^[k] f) 1 := by
  have hf0 := hf.1
  have hfne : f.roots ≠ 0 := rr_roots_ne hf (by omega)
  have hθroot : IsRoot f (kthLargestRoot f 1) := (mem_roots hf0).mp (alpha1_mem hfne)
  generalize hθ : kthLargestRoot f 1 = θ at hθroot ⊢
  have hfg : (X - C θ) * (f /ₘ (X - C θ)) = f := mul_divByMonic_eq_iff_isRoot.mpr hθroot
  generalize f /ₘ (X - C θ) = g at hfg ⊢
  have hg0 : g ≠ 0 := by
    intro h; rw [h] at hfg; simp at hfg; exact hf0 hfg.symm
  have hgdeg : g.natDegree = m - 1 := by
    have := natDegree_mul (X_sub_C_ne_zero θ) hg0
    rw [hfg, natDegree_X_sub_C, hdeg] at this
    omega
  have hgroots : f.roots = θ ::ₘ g.roots := by
    rw [← hfg, roots_mul (mul_ne_zero (X_sub_C_ne_zero θ) hg0), roots_X_sub_C]
    simp
  have hgrr : RealRooted g := by
    refine ⟨hg0, ?_⟩
    have := hf.2
    rw [hgroots, Multiset.card_cons, hdeg] at this
    omega
  have hglead : g.leadingCoeff = f.leadingCoeff := by
    rw [← hfg, leadingCoeff_mul, leadingCoeff_X_sub_C, one_mul]
  rcases Nat.eq_zero_or_pos k with rfl | hkpos
  · simp only [Function.iterate_zero, id]
    have hgne : g.roots ≠ 0 := rr_roots_ne hgrr (by omega)
    have h1 := alpha1_mem hgne
    have h2 : kthLargestRoot g 1 ∈ f.roots := by rw [hgroots]; exact Multiset.mem_cons_of_mem h1
    exact le_alpha1 hfne _ h2
  · obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    have hjg : j ≤ g.natDegree := by omega
    have hP : RealRooted (derivative^[j] g) := rr_iter hgrr j hjg
    obtain ⟨hPdeg, hPlead⟩ := natDeg_iter g hg0 j hjg
    have hP2 : 2 ≤ (derivative^[j] g).natDegree := by omega
    have hTT := T hP hP2
    have hdP : derivative (derivative^[j] g) = derivative^[j + 1] g := by
      rw [Function.iterate_succ_apply']
    rw [hdP] at hTT
    have hne := deriv_roots_ne hP hP2
    rw [hdP] at hne
    have hFrr : RealRooted (derivative^[j + 1] f) := rr_iter hf _ (by omega)
    obtain ⟨hFdeg, hFlead⟩ := natDeg_iter f hf0 (j + 1) (by omega)
    by_contra hlt
    rw [not_le] at hlt
    have hFev : (derivative^[j + 1] f) = (X - C θ) * derivative^[j + 1] g + (j + 1 : ℕ) • derivative^[j] g := by
      rw [← iter_lin, hfg]
    have hroot : (derivative^[j + 1] g).eval (kthLargestRoot (derivative^[j + 1] g) 1) = 0 :=
      (mem_roots (by
        have := (rr_deriv hP (by omega)).1
        rwa [hdP] at this)).mp (alpha1_mem hne)
    have hpb := (pos_beyond hFrr (kthLargestRoot (derivative^[j + 1] g) 1) ?_).1
    · rw [hFlead, hFev] at hpb
      simp only [eval_add, eval_mul, hroot, mul_zero, zero_add, nsmul_eq_mul, eval_natCast] at hpb
      rw [hdeg] at hpb
      rw [hPlead, hgdeg, hglead] at hTT
      have hA : (0 : ℝ) < (m.descFactorial (j + 1) : ℝ) := by
        exact_mod_cast Nat.descFactorial_pos.mpr (by omega)
      have hB : (0 : ℝ) < ((m - 1).descFactorial j : ℝ) := by
        exact_mod_cast Nat.descFactorial_pos.mpr (by omega)
      have h1 : f.leadingCoeff * (derivative^[j] g).eval (kthLargestRoot (derivative^[j + 1] g) 1) ≤ 0 := by
        by_contra hc
        rw [not_le] at hc
        have := mul_pos hB hc
        nlinarith
      have h2 : (m.descFactorial (j + 1) : ℝ) * f.leadingCoeff *
          (((j + 1 : ℕ) : ℝ) * (derivative^[j] g).eval (kthLargestRoot (derivative^[j + 1] g) 1)) =
          ((m.descFactorial (j + 1) : ℝ) * ((j + 1 : ℕ) : ℝ)) *
          (f.leadingCoeff * (derivative^[j] g).eval (kthLargestRoot (derivative^[j + 1] g) 1)) := by ring
      have h3 : (0 : ℝ) ≤ (m.descFactorial (j + 1) : ℝ) * ((j + 1 : ℕ) : ℝ) := by positivity
      have := mul_nonpos_of_nonneg_of_nonpos h3 h1
      linarith
    · intro r hr
      exact lt_of_le_of_lt (le_alpha1 (rr_roots_ne hFrr (by omega)) r hr) hlt

end SuperRamanujan227.Main
end

theorem solution : type_of% @SuperRamanujan227.Main.chk_claim_5_3 := @SuperRamanujan227.Main.chk_claim_5_3
