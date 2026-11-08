-- Prove2me | solution 1 for SimplicialIso.Cheeger.adjoint
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T06:27:05.895198+00:00
-- url     : https://prove2.me/submissions/66c2e951-f38a-4fdd-9d6b-8a4c9325168c

import Mathlib
import Definitions.Def_SimplicialIso_Cheeger_Setting

/- Supporting proof by Nickrobbins95, accepted submission b9af35aa-9557-4f92-8e55-2dff60472df4. -/

set_option autoImplicit false

namespace SimplicialIso.Cheeger.Aux17

open SimplicialIso.Cheeger Finset

variable {n d : ℕ}

lemma app_eq_ev {k : ℕ} (f : Form n k) (σ : Cell n k) : f σ = ev f σ.1 := by
  unfold ev; rw [dif_pos σ.2]

lemma ev_of_ne {k : ℕ} (f : Form n k) (s : Finset (Fin n)) (h : s.card ≠ k) : ev f s = 0 := by
  unfold ev; rw [dif_neg h]

lemma sum_cell {k : ℕ} (F : Finset (Fin n) → ℝ) :
    ∑ σ : Cell n k, F σ.1 = ∑ s : Finset (Fin n), if s.card = k then F s else 0 := by
  rw [← Finset.sum_filter]
  exact (Finset.sum_subtype (univ.filter (fun s : Finset (Fin n) => s.card = k))
    (by simp) F).symm

lemma inner_eq_sum {k : ℕ} (f g : Form n k) :
    inner ℝ f g = ∑ s : Finset (Fin n), ev f s * ev g s := by
  rw [PiLp.inner_apply]
  have : ∀ σ : Cell n k, inner ℝ (f σ) (g σ) = ev f σ.1 * ev g σ.1 := by
    intro σ; rw [app_eq_ev, app_eq_ev, Real.inner_apply]
  simp_rw [this]
  rw [sum_cell (fun s => ev f s * ev g s)]
  refine Finset.sum_congr rfl fun s _ => ?_
  split_ifs with h
  · rfl
  · rw [ev_of_ne f s h, zero_mul]

lemma sgn_insert (s : Finset (Fin n)) (v w : Fin n) (hv : v ∉ s) :
    sgn (insert v s) w = (if v < w then -1 else 1) * sgn s w := by
  unfold sgn
  rw [Finset.filter_insert]
  split_ifs with h
  · rw [Finset.card_insert_of_notMem (by simp [hv]), pow_succ]; ring
  · ring

lemma sgn_insert_self (s : Finset (Fin n)) (v : Fin n) (hv : v ∉ s) :
    sgn (insert v s) v = sgn s v := by
  rw [sgn_insert s v v hv]; simp

lemma sgn_mul_self (s : Finset (Fin n)) (v : Fin n) : sgn s v * sgn s v = 1 := by
  unfold sgn; rw [← pow_add, ← two_mul, pow_mul]; norm_num

lemma ev_cobd (X : Complex n d) (f : Form n d) (t : Finset (Fin n)) :
    ev (cobdTop X f) t = if t ∈ X.top then ∑ v ∈ t, sgn t v * ev f (t.erase v) else 0 := by
  by_cases h1 : t.card = d + 1
  · rw [show ev (cobdTop X f) t = (cobdTop X f) ⟨t, h1⟩ from dif_pos h1]
    rfl
  · rw [ev_of_ne _ t h1, if_neg (fun h2 => h1 (X.card_top t h2))]

lemma ev_bd (X : Complex n d) (g : Form n (d + 1)) (s : Finset (Fin n)) (hs : s.card = d) :
    ev (bdTop X g) s = ∑ v ∈ univ.filter (fun v => v ∉ s ∧ insert v s ∈ X.top),
      sgn (insert v s) v * ev g (insert v s) := by
  unfold ev; rw [dif_pos hs]; rfl

/-- adjointness of `bdTop` and `cobdTop` -/
lemma inner_bd (X : Complex n d) (g : Form n (d + 1)) (h : Form n d) :
    inner ℝ (bdTop X g) h = inner ℝ g (cobdTop X h) := by
  rw [inner_eq_sum, inner_eq_sum]
  have L : ∀ s : Finset (Fin n), ev (bdTop X g) s * ev h s =
      ∑ v : Fin n, if v ∉ s ∧ insert v s ∈ X.top then
        sgn (insert v s) v * ev g (insert v s) * ev h ((insert v s).erase v) else 0 := by
    intro s
    by_cases hs : s.card = d
    · rw [ev_bd X g s hs, Finset.sum_mul, Finset.sum_filter]
      refine Finset.sum_congr rfl fun v _ => ?_
      split_ifs with hc
      · rw [Finset.erase_insert hc.1]
      · simp
    · rw [ev_of_ne h s hs, mul_zero]
      symm; refine Finset.sum_eq_zero fun v _ => ?_
      split_ifs with hc
      · exfalso; apply hs
        have := X.card_top _ hc.2
        rw [Finset.card_insert_of_notMem hc.1] at this; omega
      · rfl
  have R : ∀ t : Finset (Fin n), ev g t * ev (cobdTop X h) t =
      ∑ v : Fin n, if v ∈ t ∧ t ∈ X.top then
        sgn t v * ev g t * ev h (t.erase v) else 0 := by
    intro t
    rw [ev_cobd]
    split_ifs with ht
    · rw [Finset.mul_sum]
      rw [← Finset.sum_filter]
      have : univ.filter (fun v => v ∈ t ∧ t ∈ X.top) = t := by
        ext v; simp [ht]
      rw [this]
      refine Finset.sum_congr rfl fun v _ => by ring
    · rw [mul_zero]; symm; refine Finset.sum_eq_zero fun v _ => ?_
      rw [if_neg (by tauto)]
  simp_rw [L, R]
  rw [Finset.sum_comm, Finset.sum_comm (f := fun t v => if v ∈ t ∧ t ∈ X.top then
        sgn t v * ev g t * ev h (t.erase v) else 0)]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [← Finset.sum_filter, ← Finset.sum_filter]
  apply Finset.sum_nbij' (fun s => insert v s) (fun t => t.erase v)
  · intro s hs; simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hs ⊢
    exact ⟨Finset.mem_insert_self _ _, hs.2⟩
  · intro t ht; simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ht ⊢
    rw [Finset.insert_erase ht.1]; exact ⟨Finset.notMem_erase _ _, ht.2⟩
  · intro s hs; simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hs
    exact Finset.erase_insert hs.1
  · intro t ht; simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ht
    exact Finset.insert_erase ht.1
  · intro s _; rfl

/-- `∂_{d-1} ∂_d = 0` -/
lemma bdLow_bdTop (hd : 1 ≤ d) (X : Complex n d) (g : Form n (d + 1)) :
    bdLow n d (bdTop X g) = 0 := by
  ext ρ
  have hρ := ρ.2
  show (∑ v ∈ univ.filter (fun v => v ∉ ρ.1),
    sgn (insert v ρ.1) v * ev (bdTop X g) (insert v ρ.1)) = 0
  set r := ρ.1 with hr
  let H : Fin n → Fin n → ℝ := fun v w =>
    if v ∉ r ∧ w ∉ insert v r ∧ insert w (insert v r) ∈ X.top then
      sgn (insert v r) v * (sgn (insert w (insert v r)) w * ev g (insert w (insert v r))) else 0
  have hsum : (∑ v ∈ univ.filter (fun v => v ∉ r),
      sgn (insert v r) v * ev (bdTop X g) (insert v r)) = ∑ v : Fin n, ∑ w : Fin n, H v w := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun v _ => ?_
    by_cases hv : v ∈ r
    · rw [if_neg (not_not.mpr hv)]
      symm; refine Finset.sum_eq_zero fun w _ => ?_
      simp only [H]; rw [if_neg (by tauto)]
    · rw [if_pos hv]
      have hc : (insert v r).card = d := by
        rw [Finset.card_insert_of_notMem hv, hρ]; omega
      rw [ev_bd X g _ hc, Finset.mul_sum, Finset.sum_filter]
      refine Finset.sum_congr rfl fun w _ => ?_
      simp only [H]
      split_ifs with h1 h2 h2
      · rfl
      · exact (h2 ⟨hv, h1⟩).elim
      · exact (h1 ⟨h2.2.1, h2.2.2⟩).elim
      · simp
  have hanti : ∀ v w, H w v = - H v w := by
    intro v w
    simp only [H]
    by_cases hc : v ∉ r ∧ w ∉ insert v r ∧ insert w (insert v r) ∈ X.top
    · have hvw : v ≠ w := by
        intro e; apply hc.2.1; rw [e]; exact Finset.mem_insert_self _ _
      have hw : w ∉ r := fun h => hc.2.1 (Finset.mem_insert_of_mem h)
      have hc' : w ∉ r ∧ v ∉ insert w r ∧ insert v (insert w r) ∈ X.top := by
        refine ⟨hw, ?_, ?_⟩
        · simp [hc.1, hvw]
        · rw [Finset.insert_comm]; exact hc.2.2
      rw [if_pos hc, if_pos hc', Finset.insert_comm w v r]
      rw [sgn_insert_self _ _ hc.1, sgn_insert_self _ _ hw,
        sgn_insert_self (insert w r) v hc'.2.1, sgn_insert r w v hw,
        sgn_insert (insert w r) v w hc'.2.1, sgn_insert_self r w hw]
      rcases lt_or_gt_of_ne hvw with h | h
      · rw [if_pos h, if_neg (not_lt.mpr h.le)]; ring
      · rw [if_neg (not_lt.mpr h.le), if_pos h]; ring
    · have hc' : ¬ (w ∉ r ∧ v ∉ insert w r ∧ insert v (insert w r) ∈ X.top) := by
        rintro ⟨h1, h2, h3⟩
        apply hc
        have hvw : v ≠ w := by
          intro e; apply h2; rw [e]; exact Finset.mem_insert_self _ _
        refine ⟨fun h => h2 (Finset.mem_insert_of_mem h), ?_, ?_⟩
        · simp [h1, hvw.symm]
        · rw [Finset.insert_comm]; exact h3
      rw [if_neg hc, if_neg hc', neg_zero]
  rw [hsum]
  have hS : ∑ v : Fin n, ∑ w : Fin n, H v w = - ∑ v : Fin n, ∑ w : Fin n, H v w := by
    calc ∑ v : Fin n, ∑ w : Fin n, H v w = ∑ v : Fin n, ∑ w : Fin n, H w v := Finset.sum_comm
      _ = ∑ v : Fin n, ∑ w : Fin n, - H v w :=
          Finset.sum_congr rfl fun v _ => Finset.sum_congr rfl fun w _ => hanti v w
      _ = - ∑ v : Fin n, ∑ w : Fin n, H v w := by simp only [Finset.sum_neg_distrib]
  show _ = (0 : Form n (d - 1)) ρ
  simp only [PiLp.zero_apply]
  linarith


end SimplicialIso.Cheeger.Aux17
open SimplicialIso.Cheeger

theorem solution (n d : ℕ) (hd : 1 ≤ d) (X : Complex n d) (g : Form n (d + 1)) (f : Form n d) :
    inner ℝ (bdTop X g) f = inner ℝ g (cobdTop X f) := by
  exact SimplicialIso.Cheeger.Aux17.inner_bd X g f

#print axioms solution
