-- Prove2me | solution 1 for SteinitzExchange.Extension.exc_iff_exc_loc
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T02:21:52.882028+00:00
-- url     : https://prove2.me/submissions/1efc6787-f8e1-466d-8210-57e56423b465

import Mathlib
import Definitions.Def_SteinitzExchange_Extension_IntegralBaseSet
import Definitions.Def_SteinitzExchange_Extension_Exchange

namespace SteinitzExchange.Extension

lemma aux_eel_chi_apply {V : Type*} [DecidableEq V] (u w : V) :
    chi u w = if w = u then 1 else 0 := by
  simp [chi, Pi.single_apply]

lemma aux_eel_abs_sum {V : Type*} [Fintype V] [DecidableEq V] (i u j v : V) :
    ∑ w, (chi i w + chi u w + chi j w + chi v w) = 4 := by
  simp only [Finset.sum_add_distrib, chi, Finset.sum_pi_single', Finset.mem_univ, if_true]
  norm_num

lemma aux_eel_norm4 {V : Type*} [Fintype V] [DecidableEq V] (y : V → ℤ) (i u j v : V)
    (hij : i ≠ j) (hiv : i ≠ v) (huj : u ≠ j) (huv : u ≠ v) :
    ∑ w, |(y + chi i - chi j + chi u - chi v) w - y w| = 4 := by
  have h : ∀ w, |(y + chi i - chi j + chi u - chi v) w - y w| =
      chi i w + chi u w + chi j w + chi v w := by
    intro w
    have e : (y + chi i - chi j + chi u - chi v) w - y w =
        (chi i w + chi u w) - (chi j w + chi v w) := by
      simp only [Pi.add_apply, Pi.sub_apply]; ring
    rw [e]
    have hi0 : 0 ≤ chi i w := by rw [aux_eel_chi_apply]; split_ifs <;> norm_num
    have hu0 : 0 ≤ chi u w := by rw [aux_eel_chi_apply]; split_ifs <;> norm_num
    have hj0 : 0 ≤ chi j w := by rw [aux_eel_chi_apply]; split_ifs <;> norm_num
    have hv0 : 0 ≤ chi v w := by rw [aux_eel_chi_apply]; split_ifs <;> norm_num
    by_cases hw : w = j ∨ w = v
    · have h1 : chi i w = 0 := by
        rw [aux_eel_chi_apply, if_neg]; rintro rfl; rcases hw with rfl | rfl <;> simp_all
      have h2 : chi u w = 0 := by
        rw [aux_eel_chi_apply, if_neg]; rintro rfl; rcases hw with rfl | rfl <;> simp_all
      rw [h1, h2, abs_of_nonpos (by linarith)]; ring
    · push Not at hw
      have h1 : chi j w = 0 := by rw [aux_eel_chi_apply, if_neg hw.1]
      have h2 : chi v w = 0 := by rw [aux_eel_chi_apply, if_neg hw.2]
      rw [h1, h2, abs_of_nonneg (by linarith)]; ring
  rw [Finset.sum_congr rfl (fun w _ => h w)]
  exact aux_eel_abs_sum i u j v

lemma aux_eel_abs1 (a : ℤ) (h : 0 < a) : |a - 1| ≤ |a| := by
  rw [abs_of_nonneg (by omega), abs_of_pos h]; omega

lemma aux_eel_abs2 (a : ℤ) (h : a < 0) : |a + 1| < |a| := by
  rw [abs_of_nonpos (by omega), abs_of_neg h]; omega

theorem aux_eel_main {V : Type*} [Fintype V] [DecidableEq V]
    (B : Finset (V → ℤ)) (hB : IsIntegralBaseSet B) (ω : (V → ℤ) → ℝ)
    (hloc : SatisfiesEXCLoc B ω) :
    ∀ n : ℕ, ∀ x ∈ B, ∀ y ∈ B, ∑ w, |x w - y w| < (n : ℤ) → ∀ u : V, 0 < (x - y) u →
    ∃ v : V, (x - y) v < 0 ∧ x - chi u + chi v ∈ B ∧ y + chi u - chi v ∈ B ∧
      ω x + ω y ≤ ω (x - chi u + chi v) + ω (y + chi u - chi v) := by
  classical
  intro n
  induction n with
  | zero =>
    intro x _ y _ hn
    exact absurd hn (not_lt.mpr (by
      push_cast
      exact Finset.sum_nonneg (fun w _ => abs_nonneg _)))
  | succ n ih =>
    intro x hx y hy hn u hu
    by_contra H
    push Not at H
    -- the constant M
    have hMj : ∀ j, ω (y + chi u - chi j) - ω y <
        1 + ∑ j, |ω (y + chi u - chi j) - ω y| := by
      intro j
      have h1 := Finset.single_le_sum (f := fun j => |ω (y + chi u - chi j) - ω y|)
        (fun j _ => abs_nonneg _) (Finset.mem_univ j)
      have h2 := le_abs_self (ω (y + chi u - chi j) - ω y)
      linarith
    let G : V → ℝ := fun j => if x - chi u + chi j ∈ B then ω x - ω (x - chi u + chi j)
      else 1 + ∑ j, |ω (y + chi u - chi j) - ω y|
    have hb : ∀ j, (x - y) j < 0 → y + chi u - chi j ∈ B →
        ω (y + chi u - chi j) - G j < ω y := by
      intro j hj hjB
      by_cases hxj : x - chi u + chi j ∈ B
      · have := H j hj hxj hjB
        simp only [G, if_pos hxj]; linarith
      · simp only [G, if_neg hxj]; linarith [hMj j]
    -- candidate set
    let P : V × V → Prop := fun p => 0 < (x - y) p.1 ∧ (p.1 = u → 2 ≤ (x - y) u) ∧
      (x - y) p.2 < 0 ∧ y + chi p.1 - chi p.2 ∈ B
    let C : Finset (V × V) := Finset.univ.filter P
    have hCne : C.Nonempty := by
      obtain ⟨v1, hv1, hx1⟩ := hB.2 x hx y hy u hu
      by_cases h2 : 2 ≤ (x - y) u
      · obtain ⟨i, hi, hiB⟩ := hB.2 y hy x hx v1 (by
          simp only [Pi.sub_apply] at hv1 ⊢; linarith)
        refine ⟨(i, v1), Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_, ?_, hv1, ?_⟩⟩
        · simp only [Pi.sub_apply] at hi ⊢; linarith
        · intro _; exact h2
        · have e : y + chi i - chi v1 = y - chi v1 + chi i := by abel
          simp only [e]; exact hiB
      · have hu1 : (x - y) u = 1 := by omega
        by_cases hxy : x - chi u + chi v1 = y
        · exfalso
          have hyx : y + chi u - chi v1 = x := by rw [← hxy]; abel
          have := H v1 hv1 hx1 (by rw [hyx]; exact hx)
          rw [hxy, hyx] at this; linarith
        · have hw : ∃ w, 0 < (y - (x - chi u + chi v1)) w := by
            by_contra hw
            push Not at hw
            obtain ⟨a, ha⟩ : ∃ a, (x - chi u + chi v1) a ≠ y a := by
              by_contra hh; push Not at hh; exact hxy (funext hh)
            have ha' : 0 < ((x - chi u + chi v1) - y) a := by
              have := hw a; simp only [Pi.sub_apply] at this ⊢; omega
            obtain ⟨b, hb2, _⟩ := hB.2 _ hx1 y hy a ha'
            have := hw b; simp only [Pi.sub_apply] at this hb2; omega
          obtain ⟨w, hw⟩ := hw
          obtain ⟨a, ha, haB⟩ := hB.2 y hy _ hx1 w hw
          have huv1 : v1 ≠ u := by
            rintro rfl; simp only [Pi.sub_apply] at hu hv1; omega
          have hA1 : a ≠ u := by
            intro hau; rw [hau] at ha
            simp only [Pi.sub_apply, Pi.add_apply, aux_eel_chi_apply, ↓reduceIte,
              if_neg (Ne.symm huv1)] at ha
            simp only [Pi.sub_apply] at hu1; omega
          have hA2 : 0 < (x - y) a := by
            by_cases hav : a = v1
            · rw [hav] at ha
              simp only [Pi.sub_apply, Pi.add_apply, aux_eel_chi_apply, ↓reduceIte,
                if_neg huv1] at ha
              simp only [Pi.sub_apply] at hv1 ⊢; omega
            · simp only [Pi.sub_apply, Pi.add_apply, aux_eel_chi_apply, if_neg hA1,
                if_neg hav] at ha
              simp only [Pi.sub_apply]; omega
          have hW : (x - y) w < 0 := by
            have hwu : w ≠ u := by
              intro hwu; rw [hwu] at hw
              simp only [Pi.sub_apply, Pi.add_apply, aux_eel_chi_apply, ↓reduceIte,
                if_neg (Ne.symm huv1)] at hw
              simp only [Pi.sub_apply] at hu1; omega
            by_cases hwv : w = v1
            · rw [hwv]; exact hv1
            · simp only [Pi.sub_apply, Pi.add_apply, aux_eel_chi_apply, if_neg hwu,
                if_neg hwv] at hw
              simp only [Pi.sub_apply]; omega
          refine ⟨(a, w), Finset.mem_filter.mpr ⟨Finset.mem_univ _, hA2, ?_, hW, ?_⟩⟩
          · intro hau; exact absurd hau hA1
          · have e : y + chi a - chi w = y - chi w + chi a := by abel
            simp only [e]; exact haB
    obtain ⟨⟨i0, j0⟩, hp0, hmax⟩ :=
      Finset.exists_max_image C (fun p => ω (y + chi p.1 - chi p.2) - G p.2) hCne
    simp only [C, P, Finset.mem_filter, Finset.mem_univ, true_and] at hp0
    obtain ⟨hi0, hi0u, hj0, hy'B⟩ := hp0
    have hi0j0 : i0 ≠ j0 := by rintro rfl; omega
    have hu_j0 : u ≠ j0 := by rintro rfl; omega
    -- the new pair (x, y')
    have hmeas : ∑ w, |x w - (y + chi i0 - chi j0) w| < (n : ℤ) := by
      have hlt : ∑ w, |x w - (y + chi i0 - chi j0) w| < ∑ w, |x w - y w| := by
        apply Finset.sum_lt_sum
        · intro w _
          have e : x w - (y + chi i0 - chi j0) w = (x w - y w) - chi i0 w + chi j0 w := by
            simp only [Pi.add_apply, Pi.sub_apply]; ring
          rw [e]
          by_cases hw1 : w = i0
          · subst hw1
            rw [aux_eel_chi_apply, aux_eel_chi_apply, if_pos rfl, if_neg hi0j0]
            simp only [Pi.sub_apply] at hi0
            have := aux_eel_abs1 (x w - y w) hi0
            simpa using this
          · by_cases hw2 : w = j0
            · subst hw2
              rw [aux_eel_chi_apply, aux_eel_chi_apply, if_pos rfl, if_neg hw1]
              simp only [Pi.sub_apply] at hj0
              have := aux_eel_abs2 (x w - y w) hj0
              simp only [sub_zero]; exact this.le
            · rw [aux_eel_chi_apply, aux_eel_chi_apply, if_neg hw1, if_neg hw2]
              simp
        · refine ⟨j0, Finset.mem_univ _, ?_⟩
          have e : x j0 - (y + chi i0 - chi j0) j0 = (x j0 - y j0) + 1 := by
            simp only [Pi.add_apply, Pi.sub_apply, aux_eel_chi_apply, ↓reduceIte,
              if_neg (Ne.symm hi0j0)]; ring
          rw [e]
          simp only [Pi.sub_apply] at hj0
          exact aux_eel_abs2 _ hj0
      push_cast at hn
      omega
    have hux : 0 < (x - (y + chi i0 - chi j0)) u := by
      simp only [Pi.sub_apply, Pi.add_apply, aux_eel_chi_apply, if_neg hu_j0]
      by_cases hiu : u = i0
      · rw [if_pos hiu]; have := hi0u hiu.symm; simp only [Pi.sub_apply] at this; omega
      · rw [if_neg hiu]; simp only [Pi.sub_apply] at hu; omega
    obtain ⟨v, hv, hxv, hzB, hineq⟩ := ih x hx _ hy'B hmeas u hux
    have hvW : (x - y) v < 0 := by
      simp only [Pi.sub_apply, Pi.add_apply, aux_eel_chi_apply] at hv ⊢
      by_cases hvi : v = i0
      · subst hvi; simp only [Pi.sub_apply] at hi0
        rw [if_pos rfl, if_neg hi0j0] at hv; omega
      · rw [if_neg hvi] at hv
        split_ifs at hv <;> omega
    have hi0v : i0 ≠ v := by rintro rfl; simp only [Pi.sub_apply] at hi0 hvW; omega
    have huv : u ≠ v := by rintro rfl; simp only [Pi.sub_apply] at hu hvW; omega
    have hdist := aux_eel_norm4 y i0 u j0 v hi0j0 hi0v hu_j0 huv
    obtain ⟨a, b, ha, hb', hzab, hyab, hloc'⟩ := hloc _ hzB y hy hdist
    have haa : a = i0 ∨ a = u := by
      by_contra hh
      push Not at hh
      simp only [Pi.sub_apply, Pi.add_apply, aux_eel_chi_apply, if_neg hh.1, if_neg hh.2] at ha
      split_ifs at ha <;> omega
    have hbb : b = j0 ∨ b = v := by
      by_contra hh
      push Not at hh
      simp only [Pi.sub_apply, Pi.add_apply, aux_eel_chi_apply, if_neg hh.1, if_neg hh.2] at hb'
      split_ifs at hb' <;> omega
    have hGv : G v = ω x - ω (x - chi u + chi v) := by simp only [G, if_pos hxv]
    have key : (ω (y + chi i0 - chi j0 + chi u - chi v) + ω y ≤
          ω (y + chi i0 - chi j0) + ω (y + chi u - chi v) ∧ y + chi u - chi v ∈ B) ∨
        (ω (y + chi i0 - chi j0 + chi u - chi v) + ω y ≤
          ω (y + chi i0 - chi v) + ω (y + chi u - chi j0) ∧ y + chi i0 - chi v ∈ B ∧
          y + chi u - chi j0 ∈ B) := by
      rcases haa with ha1 | ha1 <;> rcases hbb with hb1 | hb1 <;> rw [ha1, hb1] at hzab hyab hloc'
      · left
        have e : y + chi i0 - chi j0 + chi u - chi v - chi i0 + chi j0 = y + chi u - chi v := by
          abel
        rw [e] at hzab hloc'
        exact ⟨by linarith, hzab⟩
      · right
        have e : y + chi i0 - chi j0 + chi u - chi v - chi i0 + chi v = y + chi u - chi j0 := by
          abel
        rw [e] at hzab hloc'
        exact ⟨by linarith, hyab, hzab⟩
      · right
        have e : y + chi i0 - chi j0 + chi u - chi v - chi u + chi j0 = y + chi i0 - chi v := by
          abel
        rw [e] at hzab hloc'
        exact ⟨by linarith, hzab, hyab⟩
      · left
        have e : y + chi i0 - chi j0 + chi u - chi v - chi u + chi v = y + chi i0 - chi j0 := by
          abel
        rw [e] at hzab hloc'
        exact ⟨by linarith, hyab⟩
    rcases key with ⟨k1, k2⟩ | ⟨k1, k2, k3⟩
    · have := hb v hvW k2
      linarith
    · have h1 := hb j0 hj0 k3
      have h2 := hmax (i0, v) (by
        simp only [C, P, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨hi0, hi0u, hvW, k2⟩)
      simp only at h2
      linarith

theorem aux_eel_fwd {V : Type*} [Fintype V] [DecidableEq V]
    (B : Finset (V → ℤ)) (ω : (V → ℤ) → ℝ) (h : SatisfiesEXC B ω) :
    SatisfiesEXCLoc B ω := by
  intro x hx y hy hd
  have hne : x ≠ y := by
    rintro rfl; simp at hd
  obtain ⟨a, ha⟩ : ∃ a, x a ≠ y a := by
    by_contra hh; push Not at hh; exact hne (funext hh)
  obtain ⟨u, hu⟩ : ∃ u, 0 < (x - y) u := by
    rcases lt_or_gt_of_ne ha with h1 | h1
    · obtain ⟨v, hv, _⟩ := h y hy x hx a (by simp only [Pi.sub_apply]; omega)
      exact ⟨v, by simp only [Pi.sub_apply] at hv ⊢; omega⟩
    · exact ⟨a, by simp only [Pi.sub_apply]; omega⟩
  obtain ⟨v, hv, h1, h2, h3⟩ := h x hx y hy u hu
  exact ⟨u, v, hu, hv, h1, h2, h3⟩

end SteinitzExchange.Extension

open SteinitzExchange.Extension

theorem solution {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (B : Finset (V → ℤ)) (hB : IsIntegralBaseSet B) (ω : (V → ℤ) → ℝ) :
    SatisfiesEXC B ω ↔ SatisfiesEXCLoc B ω := by
  constructor
  · exact aux_eel_fwd B ω
  · intro hloc x hx y hy u hu
    exact aux_eel_main B hB ω hloc ((∑ w, |x w - y w|).toNat + 1) x hx y hy
      (by push_cast; omega) u hu
