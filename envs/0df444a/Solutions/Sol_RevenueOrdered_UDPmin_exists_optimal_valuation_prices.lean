-- Prove2me | solution 1 for RevenueOrdered.UDPmin.exists_optimal_valuation_prices
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-13T03:57:00.364829+00:00
-- url     : https://prove2.me/submissions/0fe7d4c9-b001-494d-ba6d-66623a73afa2

import Mathlib
import Definitions.Def_RevenueOrdered_UDPmin_Pricing

open RevenueOrdered.UDPmin

private theorem payment_nonneg {X M : Type*} [Fintype X] [Fintype M]
    (I : Instance X M) (p : X → ℝ) (hp : ∀ x, 0 < p x) (i : M) :
    0 ≤ payment I p i := by
  classical
  unfold payment
  split_ifs with h hbuy
  · exact Finset.le_inf' h p (fun x _ => (hp x).le)
  · exact le_rfl
  · exact le_rfl

private theorem revenue_bounded {X M : Type*} [Fintype X] [Fintype M]
    (I : Instance X M) (p : X → ℝ) : revenue I p ≤ ∑ i, I.v i := by
  classical
  apply Finset.sum_le_sum
  intro i hi
  unfold payment
  split_ifs with h hbuy
  · exact hbuy
  · exact (I.v_pos i).le
  · exact (I.v_pos i).le

private noncomputable def roundPrice {X M : Type*} [Fintype M] [Nonempty M]
    (I : Instance X M) (q : ℝ) : ℝ :=
  if h : (Finset.univ.filter (fun i => q ≤ I.v i)).Nonempty then
    (Finset.univ.filter (fun i => q ≤ I.v i)).inf' h I.v
  else vMax I

private theorem round_mem {X M : Type*} [Fintype M] [Nonempty M]
    (I : Instance X M) (q : ℝ) : ∃ i, roundPrice I q = I.v i := by
  classical
  unfold roundPrice
  split_ifs with h
  · obtain ⟨i,hi,he⟩ := Finset.exists_mem_eq_inf' h I.v
    exact ⟨i,he⟩
  · obtain ⟨i,hi,he⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty I.v
    exact ⟨i,he⟩

private theorem round_upper {X M : Type*} [Fintype M] [Nonempty M]
    (I : Instance X M) (q : ℝ) (i : M) (hqi : q ≤ I.v i) : roundPrice I q ≤ I.v i := by
  classical
  have hi : i ∈ Finset.univ.filter (fun k => q ≤ I.v k) := by simp [hqi]
  rw [roundPrice,dif_pos ⟨i,hi⟩]
  exact Finset.inf'_le _ hi

private theorem round_lower {X M : Type*} [Fintype M] [Nonempty M]
    (I : Instance X M) (q t : ℝ) (htq : t ≤ q) (ht : t ≤ vMax I) :
    t ≤ roundPrice I q := by
  classical
  unfold roundPrice
  split_ifs with h
  · exact Finset.le_inf' h I.v (fun i hi => htq.trans (Finset.mem_filter.mp hi).2)
  · exact ht

private theorem rounding_dominates {X M : Type*} [Fintype X] [Fintype M] [Nonempty M]
    (I : Instance X M) (p : X → ℝ) :
    revenue I p ≤ revenue I (fun x => roundPrice I (p x)) := by
  classical
  have hrpos (x : X) : 0 < roundPrice I (p x) := by
    obtain ⟨i,he⟩ := round_mem I (p x)
    rw [he]
    exact I.v_pos i
  apply Finset.sum_le_sum
  intro i hi
  by_cases hB : (I.B i).Nonempty
  · by_cases hbuy : (I.B i).inf' hB p ≤ I.v i
    · have hminmax : (I.B i).inf' hB p ≤ vMax I :=
        hbuy.trans (Finset.le_sup' I.v (Finset.mem_univ i))
      have hlo : (I.B i).inf' hB p ≤ (I.B i).inf' hB (fun x => roundPrice I (p x)) :=
        Finset.le_inf' hB _ (fun x hx => round_lower I (p x) _ (Finset.inf'_le _ hx) hminmax)
      obtain ⟨x,hx,he⟩ := Finset.exists_mem_eq_inf' hB p
      have hup : (I.B i).inf' hB (fun x => roundPrice I (p x)) ≤ I.v i :=
        (Finset.inf'_le _ hx).trans (round_upper I (p x) i (he ▸ hbuy))
      simpa only [payment,dif_pos hB,if_pos hbuy,if_pos hup] using hlo
    · rw [payment,dif_pos hB,if_neg hbuy]
      exact payment_nonneg I _ hrpos i
  · simp only [payment,dif_neg hB,le_refl]

theorem solution {X M : Type*} [Fintype X] [Fintype M] [Nonempty M]
    (I : Instance X M) :
    ∃ p : X → ℝ, (∀ x, ∃ i, p x = I.v i) ∧
      (∀ p' : X → ℝ, (∀ x, 0 < p' x) → revenue I p' ≤ revenue I p) ∧
      revenue I p = optUDP I := by
  classical
  obtain ⟨f,hf,hmax⟩ := (Finset.univ : Finset (X → M)).exists_max_image
    (fun f => revenue I (fun x => I.v (f x))) Finset.univ_nonempty
  let p : X → ℝ := fun x => I.v (f x)
  have hp : ∀ x,0 < p x := fun x => I.v_pos (f x)
  have hdom (p' : X → ℝ) : revenue I p' ≤ revenue I p := by
    choose g hg using fun x => round_mem I (p' x)
    have he : (fun x => roundPrice I (p' x)) = fun x => I.v (g x) := funext hg
    exact (rounding_dominates I p').trans (by rw [he]; exact hmax g (Finset.mem_univ _))
  refine ⟨p,fun x => ⟨f x,rfl⟩,fun p' _ => hdom p',?_⟩
  haveI : Nonempty {p : X → ℝ // ∀ x, 0 < p x} := ⟨⟨p,hp⟩⟩
  have hb : BddAbove (Set.range (fun p : {p : X → ℝ // ∀ x, 0 < p x} => revenue I p.1)) :=
    ⟨∑ i,I.v i,by rintro _ ⟨p,rfl⟩; exact revenue_bounded I p.1⟩
  apply le_antisymm
  · exact le_ciSup hb ⟨p,hp⟩
  · exact ciSup_le (fun p' => hdom p'.1)
