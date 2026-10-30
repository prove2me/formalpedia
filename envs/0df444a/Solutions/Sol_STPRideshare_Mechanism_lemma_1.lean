-- Prove2me | solution 1 for STPRideshare.Mechanism.lemma_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T05:01:23.639765+00:00
-- url     : https://prove2.me/submissions/1ae58e38-6055-40e8-8547-29fd1dea5db2

import Mathlib
import Definitions.Def_STPRideshare_Mechanism_Model

namespace STPRideshare.Mechanism

open scoped Classical

set_option linter.unusedSectionVars false

namespace StaticAux

variable {L : Type}

theorem isPathFrom_times' {κ : Type} (P : Params L) :
    ∀ (a : L) (t : ℕ) (zs : List (Trip L × Option κ)), P.IsPathFrom a t (zs.map Prod.fst) →
      ∀ st ∈ zs, t ≤ st.1.2.2
  | _, _, [], _ => by simp
  | a, t, z :: zs, h => by
    simp only [List.map_cons, Params.IsPathFrom] at h
    obtain ⟨h1, h2, h3, h4⟩ := h
    intro st hst
    rcases List.mem_cons.mp hst with rfl | hst
    · omega
    · have := isPathFrom_times' P _ _ zs h4 st hst
      omega

/-- Along a feasible path, trip start times strictly increase, so entries are distinct. -/
theorem isPathFrom_nodup {κ : Type} (P : Params L) (hP : ∀ a b, 1 ≤ P.δ a b) :
    ∀ (a : L) (t : ℕ) (zs : List (Trip L × Option κ)), P.IsPathFrom a t (zs.map Prod.fst) →
      zs.Nodup
  | _, _, [], _ => List.nodup_nil
  | a, t, z :: zs, h => by
    simp only [List.map_cons, Params.IsPathFrom] at h
    obtain ⟨h1, h2, h3, h4⟩ := h
    refine List.nodup_cons.mpr ⟨fun hz => ?_, isPathFrom_nodup P hP _ _ zs h4⟩
    have := isPathFrom_times' P _ _ zs h4 z hz
    have := hP a z.1.2.1
    omega

theorem sum_map_sub' {α : Type} (l : List α) (f g : α → ℝ) :
    (l.map (fun x => f x - g x)).sum = (l.map f).sum - (l.map g).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp only [List.map_cons, List.sum_cons, ih]; ring

theorem eq_zero_of_sum_nonpos {α : Type} (l : List α) (f : α → ℝ) (hnn : ∀ x ∈ l, 0 ≤ f x)
    (hs : (l.map f).sum ≤ 0) : ∀ x ∈ l, f x = 0 := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons] at hs
    have h1 := hnn a (by simp)
    have h2 : 0 ≤ (l.map f).sum := List.sum_nonneg (by
      intro y hy; obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hy; exact hnn x (by simp [hx]))
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · linarith
    · exact ih (fun y hy => hnn y (by simp [hy])) (by linarith) x hx

/-- The payment of a rider-tagged entry of an action path. -/
noncomputable def tagPay (p : Price L) {κ : Type} (st : Trip L × Option κ) : ℝ :=
  if st.2.isSome then p st.1 else 0

section Main

variable {ι κ : Type} [Fintype ι] [Fintype κ] (e : Econ L ι κ)

/-- With anonymous prices, a driver's total payment is the sum of the prices of the rider trips
on her action path. -/
theorem payTotal_eq (he : e.Valid) (d : Dispatch e) (hd : d.Feasible) (p : Price L) (i : ι) :
    (d.withPrices p).payTotal i = ((d.z i).map (tagPay p)).sum := by
  obtain ⟨hf1, hf2, hf3, hf4⟩ := hd
  have hnd : (d.z i).Nodup := isPathFrom_nodup e.P he.1.1 _ _ _ (hf1 i)
  -- step 1: sum over times
  have h1 : (d.withPrices p).payTotal i =
      ∑ j, if (riderTrip (e.R j), some j) ∈ d.z i then p (riderTrip (e.R j)) else 0 := by
    unfold Plan.payTotal Dispatch.withPrices
    simp only
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    have hτ : (e.R j).τ < e.P.T + 1 := by
      have := he.2.2.2 j
      have := he.1.1 (e.R j).o (e.R j).d
      simp only [Params.IsTrip, riderTrip] at *
      omega
    by_cases hm : (riderTrip (e.R j), some j) ∈ d.z i
    · rw [if_pos hm, Finset.sum_eq_single (e.R j).τ]
      · simp [hm]
      · intro b _ hb; rw [if_neg]; rintro ⟨_, h⟩; exact hb h.symm
      · intro h; exact absurd (Finset.mem_range.mpr hτ) h
    · rw [if_neg hm]
      apply Finset.sum_eq_zero
      intro b _
      rw [if_neg]; rintro ⟨h, _⟩; exact hm h
  -- step 2: as a sum over the entries of the path
  rw [h1]
  have h2 : ∀ st ∈ d.z i, tagPay p st =
      ∑ j, if st = (riderTrip (e.R j), some j) then p (riderTrip (e.R j)) else 0 := by
    intro st hst
    unfold tagPay
    rcases st with ⟨tr, _ | j0⟩
    · simp
    · have := hf2 i (tr, some j0) hst j0 rfl
      simp only at this
      subst this
      rw [Finset.sum_eq_single j0]
      · simp
      · intro b _ hb; rw [if_neg]; intro h; simp at h; exact hb h.2.symm
      · simp
  rw [List.map_congr_left h2, ← List.sum_toFinset _ hnd, Finset.sum_comm]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [Finset.sum_ite_eq']
  simp

/-- In a CE, every entry of a driver's own action path is paid exactly its positive-part price:
relocations have non-positive price and rider trips have non-negative price. -/
theorem ce_entries (he : e.Valid) (d : Dispatch e) (p : Price L) (hce : d.IsCE p) (i : ι) :
    ∀ st ∈ d.z i, tagPay p st = max (p st.1) 0 := by
  obtain ⟨hfe, _, hdr⟩ := hce
  have hpay := payTotal_eq e he d hfe p i
  have hmem := (hdr i).2 ⟨d.path i, hfe.1 i, rfl⟩
  -- own path with positive parts is at most the realized utility
  simp only [Plan.driverUtil, Dispatch.cost] at hmem
  have hcost : (d.withPrices p).toDispatch = d := rfl
  rw [hcost, hpay] at hmem
  simp only [Dispatch.path, List.map_map] at hmem
  -- termwise inequality
  have hle : ∀ st ∈ d.z i, tagPay p st ≤ max (p st.1) 0 := by
    intro st _
    unfold tagPay
    split_ifs
    · exact le_max_left _ _
    · exact le_max_right _ _
  have hsum : ((d.z i).map (fun st => max (p st.1) 0 - tagPay p st)).sum ≤ 0 := by
    have : ((d.z i).map (fun st => max (p st.1) 0 - tagPay p st)).sum =
        ((d.z i).map ((fun tr => max (p tr) 0) ∘ Prod.fst)).sum - ((d.z i).map (tagPay p)).sum := by
      rw [← sum_map_sub']; rfl
    rw [this]; linarith
  have hnn : ∀ st ∈ d.z i, 0 ≤ max (p st.1) 0 - tagPay p st := fun st hst => by
    linarith [hle st hst]
  have hzero := eq_zero_of_sum_nonpos _ _ hnn hsum
  intro st hst
  have := hzero st hst
  linarith

end Main

end StaticAux

end STPRideshare.Mechanism


namespace STPRideshare.Mechanism

open scoped Classical

theorem lemma_1_aux {L ι κ : Type} [Fintype L] [Fintype ι] [Fintype κ] (e : Econ L ι κ)
    (he : e.Valid) (d : Dispatch e) (p : Price L) (hce : d.IsCE p) :
    d.IsCE (posPart p) ∧
    (∀ j, (d.withPrices (posPart p)).q j = (d.withPrices p).q j) ∧
    (∀ i, (d.withPrices (posPart p)).payTotal i = (d.withPrices p).payTotal i) ∧
    (∀ j, (d.withPrices (posPart p)).riderUtil j = (d.withPrices p).riderUtil j) ∧
    (∀ i, (d.withPrices (posPart p)).driverUtil i = (d.withPrices p).driverUtil i) := by
  have hent := StaticAux.ce_entries e he d p hce
  obtain ⟨hfe, hri, hdr⟩ := hce
  obtain ⟨hf1, hf2, hf3, hf4⟩ := hfe
  -- prices of served riders are non-negative
  have hx1 : ∀ j, d.x j = 1 → 0 ≤ p (riderTrip (e.R j)) := by
    intro j hj
    have : 0 < d.x j := by omega
    rw [hf3 j] at this
    obtain ⟨i, hi⟩ := Finset.card_pos.mp this
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
    have := hent i _ hi
    simp only [StaticAux.tagPay, Option.isSome_some, if_true] at this
    rw [this]; exact le_max_right _ _
  have hx01 : ∀ j, d.x j = 0 ∨ d.x j = 1 := fun j => by have := hf4 j; omega
  have hq : ∀ j, (d.withPrices (posPart p)).q j = (d.withPrices p).q j := by
    intro j
    simp only [Dispatch.withPrices, posPart]
    rcases hx01 j with h | h
    · simp [h]
    · rw [h, max_eq_left (hx1 j h)]
  have hpay : ∀ i, (d.withPrices (posPart p)).payTotal i = (d.withPrices p).payTotal i := by
    intro i
    rw [StaticAux.payTotal_eq e he d ⟨hf1, hf2, hf3, hf4⟩, StaticAux.payTotal_eq e he d ⟨hf1, hf2, hf3, hf4⟩]
    congr 1
    apply List.map_congr_left
    intro st hst
    have := hent i st hst
    unfold StaticAux.tagPay at this ⊢
    split_ifs with h
    · rw [if_pos h] at this; rw [this]; rfl
    · rfl
  have hdu : ∀ i, (d.withPrices (posPart p)).driverUtil i = (d.withPrices p).driverUtil i := by
    intro i
    simp only [Plan.driverUtil]
    rw [hpay i]; rfl
  refine ⟨⟨⟨hf1, hf2, hf3, hf4⟩, fun j => ⟨fun h => (hri j).1 (lt_of_le_of_lt (le_max_left _ _) h),
      fun h => ?_⟩, fun i => ?_⟩, hq, hpay, fun j => ?_, hdu⟩
  · simp only [posPart]; rw [max_eq_left (hx1 j h)]; exact (hri j).2 h
  · rw [hdu i]
    have hset : (fun tr => max (posPart p tr) 0) = (fun tr => max (p tr) 0) := by
      funext tr; simp [posPart]
    simp only [hset]
    exact hdr i
  · simp only [Plan.riderUtil]
    rw [hq j]; rfl

end STPRideshare.Mechanism

open STPRideshare.Mechanism in
theorem solution {L ι κ : Type} [Fintype L] [Fintype ι] [Fintype κ] (e : Econ L ι κ)
    (he : e.Valid) (d : Dispatch e) (p : Price L) (hce : d.IsCE p) :
    d.IsCE (STPRideshare.Mechanism.posPart p) ∧
    (∀ j, (d.withPrices (STPRideshare.Mechanism.posPart p)).q j = (d.withPrices p).q j) ∧
    (∀ i, (d.withPrices (STPRideshare.Mechanism.posPart p)).payTotal i = (d.withPrices p).payTotal i) ∧
    (∀ j, (d.withPrices (STPRideshare.Mechanism.posPart p)).riderUtil j = (d.withPrices p).riderUtil j) ∧
    (∀ i, (d.withPrices (STPRideshare.Mechanism.posPart p)).driverUtil i = (d.withPrices p).driverUtil i) :=
  lemma_1_aux e he d p hce
