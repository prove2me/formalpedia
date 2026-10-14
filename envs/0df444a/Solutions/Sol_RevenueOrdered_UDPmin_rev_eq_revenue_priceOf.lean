-- Prove2me | solution 1 for RevenueOrdered.UDPmin.rev_eq_revenue_priceOf
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-13T03:59:13.375975+00:00
-- url     : https://prove2.me/submissions/786da44c-d86c-42a0-9a93-45bc7a836df4

import Mathlib
import Definitions.Def_RevenueOrdered_UDPmin_Reduction

open RevenueOrdered.UDPmin

private theorem top_gt {X M : Type*} [Fintype M] (I : Instance X M) (i : M) :
    I.v i < priceTop I := by
  have h := Finset.single_le_sum (s:=Finset.univ) (f:=I.v)
    (fun k _ => (I.v_pos k).le) (Finset.mem_univ i)
  unfold priceTop
  linarith

private theorem price_spec {X M : Type*} [Fintype X] [DecidableEq X] [Fintype M]
    (I : Instance X M) (S : Finset (RedProd I)) (x : X) :
    (∃ y ∈ S, y.1=x ∧ priceOf I S x = (y.2 : ℝ)) ∨ priceOf I S x = priceTop I := by
  classical
  unfold priceOf
  split_ifs with h
  · obtain ⟨y,hy,he⟩ := Finset.mem_image.mp (Finset.min'_mem _ h)
    exact Or.inl ⟨y,(Finset.mem_filter.mp hy).1,(Finset.mem_filter.mp hy).2,he.symm⟩
  · exact Or.inr rfl

private theorem price_le {X M : Type*} [Fintype X] [DecidableEq X] [Fintype M]
    (I : Instance X M) (S : Finset (RedProd I)) (y : RedProd I) (hy : y ∈ S) :
    priceOf I S y.1 ≤ (y.2 : ℝ) := by
  classical
  have hm : (y.2 : ℝ) ∈ (S.filter (fun z => z.1=y.1)).image (fun z => (z.2 : ℝ)) :=
    Finset.mem_image.mpr ⟨y,by simp [hy],rfl⟩
  rw [priceOf,dif_pos ⟨_,hm⟩]
  exact Finset.min'_le _ _ hm

private theorem Q_nonempty_iff {X M : Type*} [Fintype X] [DecidableEq X] [Fintype M]
    (I : Instance X M) (i : M) (S : Finset (RedProd I)) :
    (Q I i S).Nonempty ↔ ∃ y ∈ S, y.1 ∈ I.B i ∧ (y.2 : ℝ) ≤ I.v i := by
  classical
  constructor
  · rintro ⟨y,hy⟩
    obtain ⟨hyS,hyB,hyv,hmin⟩ := Finset.mem_filter.mp hy
    exact ⟨y,hyS,hyB,hyv⟩
  · rintro ⟨y,hyS,hyB,hyv⟩
    have hne : (S.filter (fun z => z.1 ∈ I.B i)).Nonempty := ⟨y,by simp [hyS,hyB]⟩
    obtain ⟨z,hz,hmin⟩ := (S.filter (fun z => z.1 ∈ I.B i)).exists_min_image
      (fun z => (z.2 : ℝ)) hne
    refine ⟨z,Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hz).1,(Finset.mem_filter.mp hz).2,?_,?_⟩⟩
    · exact (hmin y (by simp [hyS,hyB])).trans hyv
    · intro w hw hwB
      exact hmin w (by simp [hw,hwB])

private theorem payment_of_mem_Q {X M : Type*} [Fintype X] [DecidableEq X] [Fintype M]
    (I : Instance X M) (i : M) (S : Finset (RedProd I)) (y : RedProd I) (hy : y ∈ Q I i S) :
    payment I (priceOf I S) i = (y.2 : ℝ) := by
  classical
  obtain ⟨hyS,hyB,hyv,hymin⟩ := Finset.mem_filter.mp hy
  have hB : (I.B i).Nonempty := ⟨y.1,hyB⟩
  have hup : (I.B i).inf' hB (priceOf I S) ≤ (y.2 : ℝ) :=
    (Finset.inf'_le _ hyB).trans (price_le I S y hyS)
  have hlo : (y.2 : ℝ) ≤ (I.B i).inf' hB (priceOf I S) := by
    apply Finset.le_inf' hB
    intro x hx
    rcases price_spec I S x with ⟨z,hz,hzx,he⟩ | he
    · rw [he]
      exact hymin z hz (hzx ▸ hx)
    · rw [he]
      exact hyv.trans (top_gt I i).le
  have he := le_antisymm hup hlo
  rw [payment,dif_pos hB,if_pos (hup.trans hyv),he]

private theorem payment_zero_of_Q_empty {X M : Type*} [Fintype X] [DecidableEq X] [Fintype M]
    (I : Instance X M) (i : M) (S : Finset (RedProd I)) (hQ : ¬ (Q I i S).Nonempty) :
    payment I (priceOf I S) i = 0 := by
  classical
  unfold payment
  split_ifs with hB hbuy
  · obtain ⟨x,hx,he⟩ := Finset.exists_mem_eq_inf' hB (priceOf I S)
    exfalso
    apply hQ
    rcases price_spec I S x with ⟨y,hy,hyx,hyv⟩ | htop
    · apply (Q_nonempty_iff I i S).mpr
      refine ⟨y,hy,hyx ▸ hx,?_⟩
      linarith
    · have := top_gt I i
      linarith
  · rfl
  · rfl

private theorem consumer_revenue {X M : Type*} [Fintype X] [DecidableEq X] [Fintype M]
    (I : Instance X M) (i : M) (S : Finset (RedProd I)) :
    ∑ y ∈ S, Pcons I i y S * (y.2 : ℝ) = payment I (priceOf I S) i := by
  classical
  simp only [Pcons,ite_mul,zero_mul]
  rw [← Finset.sum_filter]
  have hf : S.filter (fun y => y ∈ Q I i S) = Q I i S := by
    ext y
    simp only [Finset.mem_filter]
    exact ⟨fun h => h.2,fun h => ⟨(Finset.mem_filter.mp h).1,h⟩⟩
  rw [hf]
  by_cases hQ : (Q I i S).Nonempty
  · have he : (∑ y ∈ Q I i S, (1 / ((Q I i S).card : ℝ)) * (y.2 : ℝ)) =
        ∑ _y ∈ Q I i S, (1 / ((Q I i S).card : ℝ)) * payment I (priceOf I S) i := by
      apply Finset.sum_congr rfl
      intro y hy
      rw [payment_of_mem_Q I i S y hy]
    rw [he,Finset.sum_const,nsmul_eq_mul]
    have hcard : ((Q I i S).card : ℝ) ≠ 0 := by exact_mod_cast (Finset.card_pos.mpr hQ).ne'
    field_simp
  · rw [Finset.not_nonempty_iff_eq_empty.mp hQ,Finset.sum_empty,payment_zero_of_Q_empty I i S hQ]

theorem solution {X M : Type*} [Fintype X] [DecidableEq X] [Fintype M] [Nonempty M]
    (I : Instance X M) (S : Finset (RedProd I)) :
    RevenueOrdered.Tightness.rev (redP I) (redRev I) S = revenue I (priceOf I S) := by
  classical
  have hcard : (Fintype.card M : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  unfold RevenueOrdered.Tightness.rev revenue
  calc
    (∑ y ∈ S,redP I y S * redRev I y) = ∑ y ∈ S,∑ i,Pcons I i y S * (y.2 : ℝ) := by
      apply Finset.sum_congr rfl
      intro y hy
      rw [← Finset.sum_mul]
      unfold redP redRev
      field_simp
    _ = ∑ i,∑ y ∈ S,Pcons I i y S * (y.2 : ℝ) := Finset.sum_comm
    _ = ∑ i,payment I (priceOf I S) i :=
      Finset.sum_congr rfl (fun i hi => consumer_revenue I i S)
