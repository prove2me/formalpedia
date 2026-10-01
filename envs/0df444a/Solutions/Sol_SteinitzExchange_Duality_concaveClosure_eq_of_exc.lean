-- Prove2me | solution 1 for SteinitzExchange.Duality.concaveClosure_eq_of_exc
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T14:55:05.479751+00:00
-- url     : https://prove2.me/submissions/17d22328-5b58-4543-a53d-a1e62ef664c5

import Mathlib.Analysis.Convex.Combination
import Mathlib.Data.EReal.Basic
import Mathlib.Tactic
import Definitions.Def_SteinitzExchange_Duality_IntegralBaseSet
import Definitions.Def_SteinitzExchange_Duality_Exchange
import Definitions.Def_SteinitzExchange_Duality_Conjugate

namespace SteinitzExchange.Duality

lemma aux_cce_pair_add {V : Type*} [Fintype V] (p : V → ℝ) (a b : V → ℤ) :
    pairing p (toReal (a + b)) = pairing p (toReal a) + pairing p (toReal b) := by
  unfold pairing toReal
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun w _ => ?_
  simp only [Pi.add_apply]
  push_cast
  ring

lemma aux_cce_pair_sub {V : Type*} [Fintype V] (p : V → ℝ) (a b : V → ℤ) :
    pairing p (toReal (a - b)) = pairing p (toReal a) - pairing p (toReal b) := by
  unfold pairing toReal
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun w _ => ?_
  simp only [Pi.sub_apply]
  push_cast
  ring

lemma aux_cce_pair_chi {V : Type*} [Fintype V] [DecidableEq V] (p : V → ℝ) (u : V) :
    pairing p (toReal (chi u)) = p u := by
  unfold pairing toReal chi
  simp [Pi.single_apply]

/-- Triangle lemma for exchanges at a fixed point `x`. -/
lemma aux_cce_tri {V : Type*} [DecidableEq V] {B : Finset (V → ℤ)} {ω : (V → ℤ) → ℝ}
    (hω : SatisfiesEXC B ω) {x : V → ℤ} {a b c : V}
    (hab : x - chi a + chi b ∈ B) (hbc : x - chi b + chi c ∈ B) :
    x - chi a + chi c ∈ B ∧
      ω (x - chi a + chi b) + ω (x - chi b + chi c) ≤ ω x + ω (x - chi a + chi c) := by
  by_cases h1 : a = b
  · subst h1
    have e : x - chi a + chi a = x := by abel
    rw [e]
    exact ⟨hbc, le_refl _⟩
  by_cases h2 : b = c
  · subst h2
    have e : x - chi b + chi b = x := by abel
    rw [e]
    exact ⟨hab, by linarith⟩
  have hval : ∀ w, ((x - chi a + chi b) - (x - chi b + chi c)) w
      = 2 * chi b w - chi a w - chi c w := by
    intro w
    simp only [Pi.sub_apply, Pi.add_apply]
    ring
  have hpos : 0 < ((x - chi a + chi b) - (x - chi b + chi c)) b := by
    rw [hval]
    simp [chi, Ne.symm h1, h2]
  obtain ⟨v, hv, m1, m2, hineq⟩ := hω _ hab _ hbc b hpos
  have hvac : v = a ∨ v = c := by
    by_contra hcon
    push Not at hcon
    rw [hval] at hv
    have : chi a v = 0 := by simp [chi, hcon.1]
    have : chi c v = 0 := by simp [chi, hcon.2]
    have : 0 ≤ chi b v := by simp only [chi, Pi.single_apply]; split_ifs <;> norm_num
    omega
  rcases hvac with hva | hvc
  · subst hva
    have e1 : x - chi v + chi b - chi b + chi v = x := by abel
    have e2 : x - chi b + chi c + chi b - chi v = x - chi v + chi c := by abel
    rw [e1] at hineq
    rw [e2] at m2 hineq
    exact ⟨m2, hineq⟩
  · subst hvc
    have e1 : x - chi a + chi b - chi b + chi v = x - chi a + chi v := by abel
    have e2 : x - chi b + chi v + chi b - chi v = x := by abel
    rw [e1] at m1 hineq
    rw [e2] at hineq
    exact ⟨m1, by linarith⟩

/-- Local optimality implies global optimality for M-concave functions (perturbed by `p`). -/
lemma aux_cce_global {V : Type*} [Fintype V] [DecidableEq V] {B : Finset (V → ℤ)}
    {ω : (V → ℤ) → ℝ} (hω : SatisfiesEXC B ω) (p : V → ℝ) {x : V → ℤ} (hx : x ∈ B)
    (hloc : ∀ u v : V, x - chi u + chi v ∈ B →
      ω (x - chi u + chi v) - pairing p (toReal (x - chi u + chi v))
        ≤ ω x - pairing p (toReal x)) :
    ∀ y ∈ B, ω y - pairing p (toReal y) ≤ ω x - pairing p (toReal x) := by
  classical
  set F : (V → ℤ) → ℝ := fun y => ω y - pairing p (toReal y) with hF
  by_contra hcon
  push Not at hcon
  obtain ⟨y0, hy0B, hy0⟩ := hcon
  set S := B.filter (fun y => F x < F y) with hS
  have hSne : S.Nonempty := ⟨y0, by simp [hS, hy0B, hy0, hF]⟩
  obtain ⟨y, hyS, hymin⟩ := S.exists_min_image (fun y => ∑ w, |y w - x w|) hSne
  rw [hS, Finset.mem_filter] at hyS
  obtain ⟨hyB, hyF⟩ := hyS
  have hyx : y ≠ x := by
    rintro rfl
    exact lt_irrefl _ hyF
  -- find u with (y - x) u > 0
  have hu : ∃ u, 0 < (y - x) u := by
    by_contra hno
    push Not at hno
    obtain ⟨w, hw⟩ : ∃ w, y w ≠ x w := by
      by_contra hall
      push Not at hall
      exact hyx (funext hall)
    have hw' : 0 < (x - y) w := by
      have := hno w
      simp only [Pi.sub_apply] at this ⊢
      omega
    obtain ⟨v, hv, -⟩ := hω x hx y hyB w hw'
    have := hno v
    simp only [Pi.sub_apply] at this hv
    omega
  obtain ⟨u, hu⟩ := hu
  obtain ⟨v, hv, m1, m2, hineq⟩ := hω y hyB x hx u hu
  have e : x + chi u - chi v = x - chi v + chi u := by abel
  rw [e] at m2 hineq
  have hl := hloc v u m2
  have hp1 : pairing p (toReal (y - chi u + chi v))
      = pairing p (toReal y) - p u + p v := by
    rw [aux_cce_pair_add, aux_cce_pair_sub, aux_cce_pair_chi, aux_cce_pair_chi]
  have hp2 : pairing p (toReal (x - chi v + chi u))
      = pairing p (toReal x) - p v + p u := by
    rw [aux_cce_pair_add, aux_cce_pair_sub, aux_cce_pair_chi, aux_cce_pair_chi]
  have hFy' : F x < F (y - chi u + chi v) := by
    simp only [hF] at hyF hl ⊢
    rw [hp2] at hl
    rw [hp1]
    linarith
  have hy'S : y - chi u + chi v ∈ S := by
    rw [hS, Finset.mem_filter]
    exact ⟨m1, hFy'⟩
  have hle := hymin _ hy'S
  have huv : u ≠ v := by
    rintro rfl
    omega
  have hlt : ∑ w, |(y - chi u + chi v) w - x w| < ∑ w, |y w - x w| := by
    apply Finset.sum_lt_sum
    · intro w _
      simp only [Pi.add_apply, Pi.sub_apply, chi, Pi.single_apply] at hu hv ⊢
      by_cases hwu : w = u
      · subst hwu
        simp only [if_true, if_neg huv]
        rcases abs_cases (y w - 1 + 0 - x w) with ⟨h1, _⟩ | ⟨h1, _⟩ <;>
          rcases abs_cases (y w - x w) with ⟨h2, _⟩ | ⟨h2, _⟩ <;> omega
      by_cases hwv : w = v
      · subst hwv
        simp only [if_true, if_neg hwu]
        rcases abs_cases (y w - 0 + 1 - x w) with ⟨h1, _⟩ | ⟨h1, _⟩ <;>
          rcases abs_cases (y w - x w) with ⟨h2, _⟩ | ⟨h2, _⟩ <;> omega
      · simp only [if_neg hwu, if_neg hwv]
        rcases abs_cases (y w - 0 + 0 - x w) with ⟨h1, _⟩ | ⟨h1, _⟩ <;>
          rcases abs_cases (y w - x w) with ⟨h2, _⟩ | ⟨h2, _⟩ <;> omega
    · refine ⟨u, Finset.mem_univ _, ?_⟩
      simp only [Pi.add_apply, Pi.sub_apply, chi, Pi.single_apply, if_true, if_neg huv]
        at hu ⊢
      rcases abs_cases (y u - 1 + 0 - x u) with ⟨h1, _⟩ | ⟨h1, _⟩ <;>
        rcases abs_cases (y u - x u) with ⟨h2, _⟩ | ⟨h2, _⟩ <;> omega
  exact absurd hle (not_le.mpr hlt)

end SteinitzExchange.Duality

open SteinitzExchange.Duality

theorem solution {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (B : Finset (V → ℤ)) (hB : IsIntegralBaseSet B) (ω : (V → ℤ) → ℝ)
    (hω : SatisfiesEXC B ω) :
    ∀ x ∈ B, concaveClosure B ω (toReal x) = ω x := by
  classical
  intro x hx
  have exx : ∀ u : V, x - chi u + chi u = x := fun u => by abel
  let ℓ : V → V → ℝ := fun u w => ω x - ω (x - chi u + chi w)
  have hne : ∀ u, (Finset.univ.filter (fun w => x - chi u + chi w ∈ B)).Nonempty :=
    fun u => ⟨u, by simp [exx u, hx]⟩
  choose w hwS hwmin using fun u => Finset.exists_min_image _ (ℓ u) (hne u)
  let p : V → ℝ := fun u => ℓ u (w u)
  have hloc' : ∀ u v, x - chi u + chi v ∈ B → p u - p v ≤ ℓ u v := by
    intro u v huv
    have hwv : x - chi v + chi (w v) ∈ B := by
      have := hwS v
      simpa using this
    obtain ⟨hmem, hineq⟩ := aux_cce_tri hω huv hwv
    have h1 : ℓ u (w u) ≤ ℓ u (w v) := hwmin u (w v) (by simpa using hmem)
    show ℓ u (w u) - ℓ v (w v) ≤ ℓ u v
    simp only [ℓ] at h1 ⊢
    linarith
  have hloc : ∀ u v : V, x - chi u + chi v ∈ B →
      ω (x - chi u + chi v) - pairing p (toReal (x - chi u + chi v))
        ≤ ω x - pairing p (toReal x) := by
    intro u v huv
    have h := hloc' u v huv
    have hp : pairing p (toReal (x - chi u + chi v))
        = pairing p (toReal x) - p u + p v := by
      rw [aux_cce_pair_add, aux_cce_pair_sub, aux_cce_pair_chi, aux_cce_pair_chi]
    rw [hp]
    simp only [ℓ] at h
    linarith
  have hglob := aux_cce_global hω p hx hloc
  -- bounds on the conjugate
  have hconj_le : ∀ q : V → ℝ,
      concaveConj B ω q ≤ pairing q (toReal x) - ω x := by
    intro q
    unfold concaveConj
    have hbdd : BddBelow (Set.range fun y : (B : Set (V → ℤ)) =>
        pairing q (toReal (y : V → ℤ)) - ω y) :=
      (Set.finite_range _).bddBelow
    exact ciInf_le hbdd (⟨x, by simpa using hx⟩ : (B : Set (V → ℤ)))
  have hbddC : BddBelow (Set.range fun q : V → ℝ =>
      pairing q (toReal x) - concaveConj B ω q) := by
    refine ⟨ω x, ?_⟩
    rintro _ ⟨q, rfl⟩
    have := hconj_le q
    simp only
    linarith
  unfold concaveClosure
  apply le_antisymm
  · have hconj_ge : pairing p (toReal x) - ω x ≤ concaveConj B ω p := by
      unfold concaveConj
      have : Nonempty (B : Set (V → ℤ)) := ⟨⟨x, by simpa using hx⟩⟩
      apply le_ciInf
      rintro ⟨y, hy⟩
      have := hglob y (by simpa using hy)
      simp only
      linarith
    have := ciInf_le hbddC p
    linarith
  · apply le_ciInf
    intro q
    have := hconj_le q
    linarith
