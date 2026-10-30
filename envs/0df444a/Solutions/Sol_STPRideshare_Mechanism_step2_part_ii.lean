-- Prove2me | solution 1 for STPRideshare.Mechanism.step2_part_ii
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T05:42:39.883315+00:00
-- url     : https://prove2.me/submissions/9c5ea086-b8f3-4bfc-84ff-1494d04df6ef

import Mathlib
import Definitions.Def_STPRideshare_Mechanism_Model
import Definitions.Def_STPRideshare_Mechanism_STP

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

/-! ### Concatenation and time shifts of paths -/

section Paths

variable (P : Params L)

theorem pathEnd_append : ∀ (a : L) (t : ℕ) (l1 l2 : List (Trip L)),
    P.pathEnd a t (l1 ++ l2) = P.pathEnd (P.pathEnd a t l1).1 (P.pathEnd a t l1).2 l2
  | a, t, [], l2 => by simp [Params.pathEnd]
  | a, t, z :: zs, l2 => by
    simp only [List.cons_append, Params.pathEnd]
    exact pathEnd_append _ _ zs l2

theorem isPathFrom_append : ∀ (a : L) (t : ℕ) (l1 l2 : List (Trip L)),
    P.IsPathFrom a t (l1 ++ l2) ↔
      P.IsPathFrom a t l1 ∧ P.IsPathFrom (P.pathEnd a t l1).1 (P.pathEnd a t l1).2 l2
  | a, t, [], l2 => by simp [Params.IsPathFrom, Params.pathEnd]
  | a, t, z :: zs, l2 => by
    simp only [List.cons_append, Params.IsPathFrom, Params.pathEnd]
    constructor
    · rintro ⟨h1, h2, h3, h4⟩
      rw [isPathFrom_append] at h4
      refine ⟨⟨h1, h2, h3, h4.1⟩, ?_⟩
      rw [h1, h2]; exact h4.2
    · rintro ⟨⟨h1, h2, h3, h4⟩, h5⟩
      refine ⟨h1, h2, h3, ?_⟩
      rw [isPathFrom_append]
      refine ⟨h4, ?_⟩
      rw [h1, h2] at h5; exact h5

/-- Shift a trip forward in time by `m`. -/
def tripUp (m : ℕ) (tr : Trip L) : Trip L := (tr.1, tr.2.1, tr.2.2 + m)

/-- Relation between parameters `P1` of an economy shifted by `m` and the original `P0`. -/
def ShiftRel (P0 P1 : Params L) (m : ℕ) : Prop :=
  P1.δ = P0.δ ∧ P1.T + m = P0.T ∧ (∀ a b u, P1.c a b u = P0.c a b (u + m)) ∧ P1.κ = P0.κ

theorem isPathFrom_up {P0 P1 : Params L} {m : ℕ} (hr : ShiftRel P0 P1 m) :
    ∀ (a : L) (τ : ℕ) (l : List (Trip L)), P1.IsPathFrom a τ l →
      P0.IsPathFrom a (τ + m) (l.map (tripUp m))
  | _, _, [], _ => by simp [Params.IsPathFrom]
  | a, τ, z :: zs, h => by
    obtain ⟨hδ, hT, hc, hκ⟩ := hr
    simp only [List.map_cons, Params.IsPathFrom] at h ⊢
    obtain ⟨h1, h2, h3, h4⟩ := h
    rw [hδ] at h3 h4
    refine ⟨by simp [tripUp, h1], by simp [tripUp, h2], ?_, ?_⟩
    · simp only [tripUp]; omega
    · have := isPathFrom_up ⟨hδ, hT, hc, hκ⟩ _ _ zs h4
      simp only [tripUp] at this ⊢
      rwa [show τ + m + P0.δ a z.2.1 = τ + P0.δ a z.2.1 + m by omega]

theorem isPathFrom_down {P0 P1 : Params L} {m : ℕ} (hr : ShiftRel P0 P1 m) :
    ∀ (a : L) (τ : ℕ) (l : List (Trip L)), P0.IsPathFrom a (τ + m) (l.map (tripUp m)) →
      P1.IsPathFrom a τ l
  | _, _, [], _ => by simp [Params.IsPathFrom]
  | a, τ, z :: zs, h => by
    obtain ⟨hδ, hT, hc, hκ⟩ := hr
    simp only [List.map_cons, Params.IsPathFrom, tripUp] at h ⊢
    obtain ⟨h1, h2, h3, h4⟩ := h
    rw [hδ]
    refine ⟨h1, by omega, by omega, ?_⟩
    apply isPathFrom_down ⟨hδ, hT, hc, hκ⟩
    rwa [show τ + P0.δ a z.2.1 + m = τ + m + P0.δ a z.2.1 by omega]

theorem pathEnd_up {P0 P1 : Params L} {m : ℕ} (hr : ShiftRel P0 P1 m) :
    ∀ (a : L) (τ : ℕ) (l : List (Trip L)),
      P0.pathEnd a (τ + m) (l.map (tripUp m)) = ((P1.pathEnd a τ l).1, (P1.pathEnd a τ l).2 + m)
  | a, τ, [] => by simp [Params.pathEnd]
  | a, τ, z :: zs => by
    simp only [List.map_cons, Params.pathEnd, tripUp]
    rw [show z.2.2 + m + P0.δ z.1 z.2.1 = (z.2.2 + P1.δ z.1 z.2.1) + m by rw [hr.1]; omega]
    exact pathEnd_up hr _ _ zs

theorem sumc_up {P0 P1 : Params L} {m : ℕ} (hr : ShiftRel P0 P1 m) (l : List (Trip L)) :
    ((l.map (tripUp m)).map (fun e => P0.c e.1 e.2.1 e.2.2)).sum =
      (l.map (fun e => P1.c e.1 e.2.1 e.2.2)).sum := by
  simp only [List.map_map]
  congr 1
  apply List.map_congr_left
  intro tr _
  simp [tripUp, hr.2.2.1]

end Paths

/-! ### Splicing a prefix of a dispatching of `E0` with a dispatching of a shifted economy `E1` -/

section Splice

variable {ι0 κ0 ι1 κ1 : Type} [Fintype ι0] [Fintype κ0] [Fintype ι1] [Fintype κ1]
  (E0 : Econ L ι0 κ0) (E1 : Econ L ι1 κ1) (m : ℕ)
  (f : ι1 → ι0) (finv : ι0 → Option ι1) (g : κ1 → κ0)
  (pre : ι0 → List (Trip L × Option κ0))

/-- The data needed to splice: `E1` is `E0` shifted by `m`, drivers of `E1` are drivers of `E0`
(via `f`, with partial inverse `finv`), riders of `E1` are the riders of `E0` requesting at or
after `m` (via `g`), and `pre` is a prefix of feasible paths of `E0` (trips before `m`) ending
where the drivers of `E1` start. -/
structure SpliceData : Prop where
  hP : ShiftRel E0.P E1.P m
  hfinv : ∀ i0 i1, finv i0 = some i1 ↔ f i1 = i0
  hg : Function.Injective g
  hR : ∀ j1, (E0.R (g j1)).o = (E1.R j1).o ∧ (E0.R (g j1)).d = (E1.R j1).d ∧
    (E0.R (g j1)).τ = (E1.R j1).τ + m ∧ (E0.R (g j1)).v = (E1.R j1).v
  hgsurj : ∀ j0, m ≤ (E0.R j0).τ → ∃ j1, g j1 = j0
  hpre_path : ∀ i0, E0.P.IsPathFrom (E0.D i0).ℓ (E0.D i0).τ ((pre i0).map Prod.fst)
  hpre_time : ∀ i0, ∀ st ∈ pre i0, st.1.2.2 < m
  hpre_tag : ∀ i0, ∀ st ∈ pre i0, ∀ j, st.2 = some j → st.1 = riderTrip (E0.R j)
  hpre_x : ∀ j0, (Finset.univ.filter fun i0 => (riderTrip (E0.R j0), some j0) ∈ pre i0).card ≤ 1
  hend : ∀ i1, E0.P.pathEnd (E0.D (f i1)).ℓ (E0.D (f i1)).τ ((pre (f i1)).map Prod.fst) =
    ((E1.D i1).ℓ, (E1.D i1).τ + m)
  hβ0 : ∀ i1, pre (f i1) = [] → (E1.D i1).β = (E0.D (f i1)).β
  hβ1 : ∀ i1, pre (f i1) ≠ [] → (E1.D i1).β = true

/-- Shift an entry of an action path of `E1` to `E0`. -/
def upE (st : Trip L × Option κ1) : Trip L × Option κ0 := (tripUp m st.1, st.2.map g)

/-- The spliced action paths. -/
def spliceZ (d1 : Dispatch E1) (i0 : ι0) : List (Trip L × Option κ0) :=
  pre i0 ++ (match finv i0 with
    | none => []
    | some i1 => (d1.z i1).map (upE m g))

/-- The spliced dispatching of `E0`. -/
noncomputable def splice (d1 : Dispatch E1) : Dispatch E0 where
  x := fun j0 => (Finset.univ.filter fun i0 =>
    (riderTrip (E0.R j0), some j0) ∈ spliceZ E1 m finv g pre d1 i0).card
  z := spliceZ E1 m finv g pre d1

variable {E0 E1 m f finv g pre}

theorem upE_rider (hS : SpliceData E0 E1 m f finv g pre) (j1 : κ1) :
    upE m g (riderTrip (E1.R j1), some j1) = (riderTrip (E0.R (g j1)), some (g j1)) := by
  obtain ⟨h1, h2, h3, _⟩ := hS.hR j1
  simp [upE, tripUp, riderTrip, h1, h2, h3]

theorem upE_inj (hS : SpliceData E0 E1 m f finv g pre) :
    Function.Injective (upE (κ0 := κ0) (κ1 := κ1) (L := L) m g) := by
  rintro ⟨⟨a, b, t⟩, o⟩ ⟨⟨a', b', t'⟩, o'⟩ h
  simp only [upE, tripUp, Prod.mk.injEq] at h
  obtain ⟨⟨rfl, rfl, ht⟩, ho⟩ := h
  have : t = t' := by omega
  subst this
  have : o = o' := Option.map_injective hS.hg ho
  subst this
  rfl

theorem f_inj (hS : SpliceData E0 E1 m f finv g pre) : Function.Injective f := by
  intro a b h
  have h1 := (hS.hfinv (f a) a).mpr rfl
  have h2 := (hS.hfinv (f a) b).mpr h.symm
  rw [h1] at h2; exact Option.some_injective _ h2

theorem cont_time (hS : SpliceData E0 E1 m f finv g pre) (d1 : Dispatch E1) (i1 : ι1) :
    ∀ st ∈ (d1.z i1).map (upE m g), m ≤ st.1.2.2 := by
  intro st hst
  obtain ⟨st1, _, rfl⟩ := List.mem_map.mp hst
  simp [upE, tripUp]

theorem splice_feasible (hS : SpliceData E0 E1 m f finv g pre) (d1 : Dispatch E1)
    (hd1 : d1.Feasible) : (splice E0 E1 m finv g pre d1).Feasible := by
  obtain ⟨hf1, hf2, hf3, hf4⟩ := hd1
  refine ⟨?_, ?_, fun j0 => rfl, ?_⟩
  · intro i0
    show E0.P.IsPathFrom _ _ ((spliceZ E1 m finv g pre d1 i0).map Prod.fst)
    unfold spliceZ
    rcases hfi : finv i0 with _ | i1
    · simpa using hS.hpre_path i0
    · have hi0 : f i1 = i0 := (hS.hfinv i0 i1).mp hfi
      subst hi0
      simp only [List.map_append]
      rw [isPathFrom_append, hS.hend i1]
      refine ⟨hS.hpre_path _, ?_⟩
      have := isPathFrom_up hS.hP _ _ _ (hf1 i1)
      simpa [upE, Dispatch.path, List.map_map, Function.comp_def] using this
  · intro i0 st hst j hj
    change st ∈ spliceZ E1 m finv g pre d1 i0 at hst
    unfold spliceZ at hst
    rcases List.mem_append.mp hst with h | h
    · exact hS.hpre_tag i0 st h j hj
    · rcases hfi : finv i0 with _ | i1
      · rw [hfi] at h; simp at h
      · rw [hfi] at h
        obtain ⟨st1, hst1, rfl⟩ := List.mem_map.mp h
        simp only [upE, Option.map_eq_some_iff] at hj
        obtain ⟨j1, hj1, rfl⟩ := hj
        have := hf2 i1 st1 hst1 j1 hj1
        obtain ⟨h1, h2, h3, _⟩ := hS.hR j1
        simp only [upE, tripUp, this, riderTrip, h1, h2, h3]
  · intro j0
    by_cases hj0 : m ≤ (E0.R j0).τ
    · obtain ⟨j1, rfl⟩ := hS.hgsurj j0 hj0
      refine le_trans ?_ (hf4 j1)
      rw [hf3 j1]
      -- spliced riders come from the continuation
      calc _ ≤ (Finset.univ.map ⟨f, f_inj hS⟩ |>.filter fun i0 =>
              (riderTrip (E0.R (g j1)), some (g j1)) ∈ spliceZ E1 m finv g pre d1 i0).card := by
            apply Finset.card_le_card
            intro i0
            simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map,
              Function.Embedding.coeFn_mk]
            intro hm
            refine ⟨?_, hm⟩
            unfold spliceZ at hm
            rcases List.mem_append.mp hm with h | h
            · have := hS.hpre_time i0 _ h
              simp only [riderTrip] at this; omega
            · rcases hfi : finv i0 with _ | i1
              · rw [hfi] at h; simp at h
              · exact ⟨i1, (hS.hfinv i0 i1).mp hfi⟩
        _ = _ := by
            rw [Finset.filter_map, Finset.card_map]
            congr 1
            ext i1
            simp only [Finset.mem_filter, Finset.mem_univ, true_and, Function.comp_apply,
              Function.Embedding.coeFn_mk]
            unfold spliceZ
            rw [(hS.hfinv (f i1) i1).mpr rfl]
            simp only [List.mem_append]
            constructor
            · rintro (h | h)
              · have := hS.hpre_time _ _ h
                obtain ⟨_, _, h3, _⟩ := hS.hR j1
                simp only [riderTrip] at this; omega
              · rw [← upE_rider hS j1] at h
                exact (List.mem_map_of_injective (upE_inj hS)).mp h
            · intro h; right; rw [← upE_rider hS j1]; exact List.mem_map_of_mem h
    · refine le_trans (Finset.card_le_card ?_) (hS.hpre_x j0)
      intro i0
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      intro hm
      unfold spliceZ at hm
      rcases List.mem_append.mp hm with h | h
      · exact h
      · exfalso
        rcases hfi : finv i0 with _ | i1
        · rw [hfi] at h; simp at h
        · rw [hfi] at h
          have := cont_time hS d1 i1 _ h
          simp only [riderTrip] at this; omega

/-- The part of the welfare of a spliced dispatching coming from the prefix. -/
noncomputable def spliceConst (E0 : Econ L ι0 κ0) (m : ℕ) (finv : ι0 → Option ι1)
    (pre : ι0 → List (Trip L × Option κ0)) : ℝ :=
  (∑ j0, (if (E0.R j0).τ < m then ((Finset.univ.filter fun i0 =>
      (riderTrip (E0.R j0), some j0) ∈ pre i0).card : ℝ) else 0) * (E0.R j0).v) -
  ∑ i0, (if finv i0 = none then E0.P.pathCost (E0.D i0) ((pre i0).map Prod.fst)
    else ((pre i0).map Prod.fst |>.map (fun e => E0.P.c e.1 e.2.1 e.2.2)).sum)

theorem sum_finv (hS : SpliceData E0 E1 m f finv g pre) (G : ι1 → ℝ) :
    ∑ i0, (match finv i0 with | none => 0 | some i1 => G i1) = ∑ i1, G i1 := by
  have hinj := f_inj hS
  rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.map ⟨f, hinj⟩))]
  · rw [Finset.sum_map]
    refine Finset.sum_congr rfl (fun i1 _ => ?_)
    simp only [Function.Embedding.coeFn_mk]
    rw [(hS.hfinv (f i1) i1).mpr rfl]
  · intro i0 _ hi0
    rcases hfi : finv i0 with _ | i1
    · rfl
    · exfalso; apply hi0
      simp only [Finset.mem_map, Finset.mem_univ, true_and, Function.Embedding.coeFn_mk]
      exact ⟨i1, (hS.hfinv i0 i1).mp hfi⟩

theorem cost_splice_some (hS : SpliceData E0 E1 m f finv g pre) (d1 : Dispatch E1) (i1 : ι1) :
    E0.P.pathCost (E0.D (f i1)) ((spliceZ E1 m finv g pre d1 (f i1)).map Prod.fst) =
      ((pre (f i1)).map Prod.fst |>.map (fun e => E0.P.c e.1 e.2.1 e.2.2)).sum +
      E1.P.pathCost (E1.D i1) ((d1.z i1).map Prod.fst) := by
  have hz : (spliceZ E1 m finv g pre d1 (f i1)).map Prod.fst =
      (pre (f i1)).map Prod.fst ++ ((d1.z i1).map Prod.fst).map (tripUp m) := by
    unfold spliceZ
    rw [(hS.hfinv (f i1) i1).mpr rfl]
    simp [upE, List.map_map, Function.comp_def]
  rw [hz]
  have hend := hS.hend i1
  have hP := hS.hP
  obtain ⟨hδ, hT, hc, hκ⟩ := hP
  unfold Params.pathCost
  rw [pathEnd_append, hend, pathEnd_up hS.hP, List.map_append, List.sum_append, sumc_up hS.hP]
  by_cases hpre : pre (f i1) = []
  · have hβ := hS.hβ0 i1 hpre
    rw [hpre] at hend
    simp only [hpre, List.map_nil, List.nil_append, List.sum_nil, zero_add]
    have hD0 : (E0.D (f i1)).β = (E1.D i1).β := hβ.symm
    rw [hD0, hκ]
    by_cases hq : (d1.z i1).map Prod.fst = []
    · simp [hq]
      split_ifs <;> first | rfl | (congr 1; omega)
    · have hq' : ((d1.z i1).map Prod.fst).map (tripUp m) ≠ [] := by simpa using hq
      simp only [hq, hq', and_false, if_false]
      congr 2; omega
  · have hβ := hS.hβ1 i1 hpre
    have hne : (pre (f i1)).map Prod.fst ++ ((d1.z i1).map Prod.fst).map (tripUp m) ≠ [] := by
      simp [hpre]
    rw [if_neg (by rintro ⟨_, h⟩; exact hne h), hβ, hκ]
    simp only [Bool.true_eq_false, false_and, if_false]
    rw [add_assoc]; congr 3; omega

theorem splice_x_cont (hS : SpliceData E0 E1 m f finv g pre) (d1 : Dispatch E1) (j1 : κ1) :
    (splice E0 E1 m finv g pre d1).x (g j1) =
      (Finset.univ.filter fun i1 => (riderTrip (E1.R j1), some j1) ∈ d1.z i1).card := by
  show (Finset.univ.filter fun i0 =>
    (riderTrip (E0.R (g j1)), some (g j1)) ∈ spliceZ E1 m finv g pre d1 i0).card = _
  have hsub : (Finset.univ.filter fun i0 =>
      (riderTrip (E0.R (g j1)), some (g j1)) ∈ spliceZ E1 m finv g pre d1 i0) =
      (Finset.univ.map ⟨f, f_inj hS⟩).filter fun i0 =>
      (riderTrip (E0.R (g j1)), some (g j1)) ∈ spliceZ E1 m finv g pre d1 i0 := by
    ext i0
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map,
      Function.Embedding.coeFn_mk]
    constructor
    · intro hm
      refine ⟨?_, hm⟩
      unfold spliceZ at hm
      rcases List.mem_append.mp hm with h | h
      · have := hS.hpre_time i0 _ h
        obtain ⟨_, _, h3, _⟩ := hS.hR j1
        simp only [riderTrip] at this; omega
      · rcases hfi : finv i0 with _ | i1
        · rw [hfi] at h; simp at h
        · exact ⟨i1, (hS.hfinv i0 i1).mp hfi⟩
    · exact fun h => h.2
  rw [hsub, Finset.filter_map, Finset.card_map]
  congr 1
  ext i1
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Function.comp_apply,
    Function.Embedding.coeFn_mk]
  unfold spliceZ
  rw [(hS.hfinv (f i1) i1).mpr rfl]
  simp only [List.mem_append]
  constructor
  · rintro (h | h)
    · have := hS.hpre_time _ _ h
      obtain ⟨_, _, h3, _⟩ := hS.hR j1
      simp only [riderTrip] at this; omega
    · rw [← upE_rider hS j1] at h
      exact (List.mem_map_of_injective (upE_inj hS)).mp h
  · intro h; right; rw [← upE_rider hS j1]; exact List.mem_map_of_mem h

theorem splice_x_pre (hS : SpliceData E0 E1 m f finv g pre) (d1 : Dispatch E1) (j0 : κ0)
    (hj0 : (E0.R j0).τ < m) :
    (splice E0 E1 m finv g pre d1).x j0 =
      (Finset.univ.filter fun i0 => (riderTrip (E0.R j0), some j0) ∈ pre i0).card := by
  show (Finset.univ.filter fun i0 =>
    (riderTrip (E0.R j0), some j0) ∈ spliceZ E1 m finv g pre d1 i0).card = _
  congr 1
  ext i0
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  unfold spliceZ
  constructor
  · intro hm
    rcases List.mem_append.mp hm with h | h
    · exact h
    · exfalso
      rcases hfi : finv i0 with _ | i1
      · rw [hfi] at h; simp at h
      · rw [hfi] at h
        have := cont_time hS d1 i1 _ h
        simp only [riderTrip] at this; omega
  · intro h; exact List.mem_append_left _ h

theorem splice_welfare (hS : SpliceData E0 E1 m f finv g pre) (d1 : Dispatch E1)
    (hd1 : d1.Feasible) :
    (splice E0 E1 m finv g pre d1).welfare = spliceConst E0 m finv pre + d1.welfare := by
  unfold Dispatch.welfare spliceConst
  -- costs
  have hcost : ∑ i0, (splice E0 E1 m finv g pre d1).cost i0 =
      (∑ i0, (if finv i0 = none then E0.P.pathCost (E0.D i0) ((pre i0).map Prod.fst)
        else ((pre i0).map Prod.fst |>.map (fun e => E0.P.c e.1 e.2.1 e.2.2)).sum)) +
      ∑ i1, d1.cost i1 := by
    rw [← sum_finv hS, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun i0 _ => ?_)
    unfold Dispatch.cost Dispatch.path
    rcases hfi : finv i0 with _ | i1
    · simp only [if_true, add_zero]
      show E0.P.pathCost _ ((spliceZ E1 m finv g pre d1 i0).map Prod.fst) = _
      unfold spliceZ; rw [hfi]; simp
    · have hi0 : f i1 = i0 := (hS.hfinv i0 i1).mp hfi
      subst hi0
      simp only [reduceCtorEq, if_false]
      exact cost_splice_some hS d1 i1
  -- riders
  have hrid : ∑ j0, ((splice E0 E1 m finv g pre d1).x j0 : ℝ) * (E0.R j0).v =
      (∑ j0, (if (E0.R j0).τ < m then ((Finset.univ.filter fun i0 =>
        (riderTrip (E0.R j0), some j0) ∈ pre i0).card : ℝ) else 0) * (E0.R j0).v) +
      ∑ j1, (d1.x j1 : ℝ) * (E1.R j1).v := by
    have hsplit : ∀ j0, ((splice E0 E1 m finv g pre d1).x j0 : ℝ) * (E0.R j0).v =
        (if (E0.R j0).τ < m then ((Finset.univ.filter fun i0 =>
          (riderTrip (E0.R j0), some j0) ∈ pre i0).card : ℝ) else 0) * (E0.R j0).v +
        (if (E0.R j0).τ < m then 0 else ((splice E0 E1 m finv g pre d1).x j0 : ℝ) * (E0.R j0).v) := by
      intro j0
      split_ifs with h
      · rw [splice_x_pre hS d1 j0 h]; ring
      · ring
    rw [Finset.sum_congr rfl (fun j0 _ => hsplit j0), Finset.sum_add_distrib]
    congr 1
    rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.map ⟨g, hS.hg⟩))]
    · rw [Finset.sum_map]
      refine Finset.sum_congr rfl (fun j1 _ => ?_)
      simp only [Function.Embedding.coeFn_mk]
      obtain ⟨_, _, h3, h4⟩ := hS.hR j1
      rw [if_neg (by omega), splice_x_cont hS d1 j1, ← hd1.2.2.1 j1, h4]
    · intro j0 _ hj0
      rw [if_pos]
      by_contra hlt
      apply hj0
      obtain ⟨j1, rfl⟩ := hS.hgsurj j0 (by omega)
      simp
  rw [hcost, hrid]
  ring

theorem optimal_of_splice (hS : SpliceData E0 E1 m f finv g pre) (d0 : Dispatch E0)
    (hd0 : d0.IsWelfareOptimal) (d1 : Dispatch E1) (hd1 : d1.Feasible)
    (heq : splice E0 E1 m finv g pre d1 = d0) : d1.IsWelfareOptimal := by
  refine ⟨hd1, fun d' hd' => ?_⟩
  have w1 := splice_welfare hS d' hd'
  have w2 := splice_welfare hS _ hd1
  have w3 := hd0.2 _ (splice_feasible hS d' hd')
  rw [heq] at w2
  linarith

theorem W_of_optimal (E : Econ L ι0 κ0) (d : Dispatch E) (hd : d.IsWelfareOptimal) :
    W E = d.welfare := by
  have hg : IsGreatest {w : ℝ | ∃ d : Dispatch E, d.Feasible ∧ d.welfare = w} d.welfare :=
    ⟨⟨d, hd.1, rfl⟩, by rintro w ⟨d', hdf, rfl⟩; exact hd.2 d' hdf⟩
  exact hg.csSup_eq

theorem le_W (E : Econ L ι0 κ0) (dopt : Dispatch E) (hopt : dopt.IsWelfareOptimal) (d : Dispatch E)
    (hd : d.Feasible) : d.welfare ≤ W E := by
  rw [W_of_optimal E dopt hopt]; exact hopt.2 d hd

/-- Adding one more driver to both economies, with matching types and an empty prefix. -/
theorem spliceData_add (hS : SpliceData E0 E1 m f finv g pre) (θ0 θ1 : DType L)
    (hβ : θ1.β = θ0.β) (hℓ : θ1.ℓ = θ0.ℓ) (hτ : θ0.τ = θ1.τ + m) :
    SpliceData (E0.addDriver θ0) (E1.addDriver θ1) m (Option.map f)
      (fun o => o.elim (some none) (fun i0 => (finv i0).map some))
      g (fun o => o.elim [] pre) where
  hP := hS.hP
  hfinv := by
    intro o0 o1
    cases o0 with
    | none => cases o1 <;> simp
    | some i0 =>
      cases o1 with
      | none => simp
      | some i1 =>
        simp only [Option.elim, Option.map_some, Option.some.injEq]
        rw [← hS.hfinv i0 i1]
        constructor
        · intro hh; obtain ⟨x, hx, hx'⟩ := Option.map_eq_some_iff.mp hh
          simp only [Option.some.injEq] at hx'; subst hx'; exact hx
        · intro hh; rw [hh]; rfl
  hg := hS.hg
  hR := hS.hR
  hgsurj := hS.hgsurj
  hpre_path := by
    intro o0
    cases o0 with
    | none => simp [Params.IsPathFrom]
    | some i0 => exact hS.hpre_path i0
  hpre_time := by
    intro o0
    cases o0 with
    | none => simp
    | some i0 => exact hS.hpre_time i0
  hpre_tag := by
    intro o0
    cases o0 with
    | none => simp
    | some i0 => exact hS.hpre_tag i0
  hpre_x := by
    intro j0
    refine le_trans (le_of_eq ?_) (hS.hpre_x j0)
    symm
    rw [← Finset.card_map Function.Embedding.some]
    apply congrArg Finset.card
    ext o
    cases o with
    | none => simp
    | some i0 => simp; rfl
  hend := by
    intro o1
    cases o1 with
    | none => simp [Econ.addDriver, Params.pathEnd, hℓ, hτ]
    | some i1 => exact hS.hend i1
  hβ0 := by
    intro o1
    cases o1 with
    | none => intro _; exact hβ
    | some i1 => exact hS.hβ0 i1
  hβ1 := by
    intro o1
    cases o1 with
    | none => intro h; exact absurd rfl h
    | some i1 => exact hS.hβ1 i1

theorem spliceConst_add (θ0 : DType L) :
    spliceConst (E0.addDriver θ0) m (fun o => o.elim (some none) (fun i0 => (finv i0).map some))
      (fun o => o.elim [] pre) = spliceConst E0 m finv pre := by
  unfold spliceConst
  have hr : ∀ j0 : κ0, (Finset.univ.filter fun o : Option ι0 =>
      (riderTrip ((E0.addDriver θ0).R j0), some j0) ∈ (o.elim [] pre)).card =
      (Finset.univ.filter fun i0 => (riderTrip (E0.R j0), some j0) ∈ pre i0).card := by
    intro j0
    symm
    rw [← Finset.card_map Function.Embedding.some]
    apply congrArg Finset.card
    ext o
    cases o with
    | none => simp
    | some i0 => simp; rfl
  simp only [hr]
  congr 1
  rw [Fintype.sum_option]
  simp only [Option.elim]
  simp only [reduceCtorEq, if_false, List.map_nil, List.sum_nil, zero_add]
  refine Finset.sum_congr rfl (fun i0 _ => ?_)
  by_cases hf : finv i0 = none
  · simp [hf, Econ.addDriver]
  · have hf' : (finv i0).map some ≠ none := by simpa using hf
    rw [if_neg hf]
    simp [hf', Econ.addDriver]

/-- Adding one more driver to both economies, with a prefix `p0` (relocations only) for her. -/
theorem spliceData_addP (hS : SpliceData E0 E1 m f finv g pre) (θ0 θ1 : DType L)
    (p0 : List (Trip L × Option κ0))
    (hp_path : E0.P.IsPathFrom θ0.ℓ θ0.τ (p0.map Prod.fst))
    (hp_time : ∀ st ∈ p0, st.1.2.2 < m) (hp_tag : ∀ st ∈ p0, st.2 = none)
    (hp_end : E0.P.pathEnd θ0.ℓ θ0.τ (p0.map Prod.fst) = (θ1.ℓ, θ1.τ + m))
    (hp_β0 : p0 = [] → θ1.β = θ0.β) (hp_β1 : p0 ≠ [] → θ1.β = true) :
    SpliceData (E0.addDriver θ0) (E1.addDriver θ1) m (Option.map f)
      (fun o => o.elim (some none) (fun i0 => (finv i0).map some))
      g (fun o => o.elim p0 pre) where
  hP := hS.hP
  hfinv := by
    intro o0 o1
    cases o0 with
    | none => cases o1 <;> simp
    | some i0 =>
      cases o1 with
      | none => simp
      | some i1 =>
        simp only [Option.elim, Option.map_some, Option.some.injEq]
        rw [← hS.hfinv i0 i1]
        constructor
        · intro hh; obtain ⟨x, hx, hx'⟩ := Option.map_eq_some_iff.mp hh
          simp only [Option.some.injEq] at hx'; subst hx'; exact hx
        · intro hh; rw [hh]; rfl
  hg := hS.hg
  hR := hS.hR
  hgsurj := hS.hgsurj
  hpre_path := by
    intro o0
    cases o0 with
    | none => exact hp_path
    | some i0 => exact hS.hpre_path i0
  hpre_time := by
    intro o0
    cases o0 with
    | none => exact hp_time
    | some i0 => exact hS.hpre_time i0
  hpre_tag := by
    intro o0
    cases o0 with
    | none => intro st hst j hj; rw [hp_tag st hst] at hj; cases hj
    | some i0 => exact hS.hpre_tag i0
  hpre_x := by
    intro j0
    refine le_trans (le_of_eq ?_) (hS.hpre_x j0)
    symm
    rw [← Finset.card_map Function.Embedding.some]
    apply congrArg Finset.card
    ext o
    cases o with
    | none =>
      simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
        Function.Embedding.some_apply]
      constructor
      · rintro ⟨x, _, hx⟩; cases hx
      · intro hm
        change _ ∈ p0 at hm
        have := hp_tag _ hm; simp at this
    | some i0 => simp; rfl
  hend := by
    intro o1
    cases o1 with
    | none => exact hp_end
    | some i1 => exact hS.hend i1
  hβ0 := by
    intro o1
    cases o1 with
    | none => exact hp_β0
    | some i1 => exact hS.hβ0 i1
  hβ1 := by
    intro o1
    cases o1 with
    | none => exact hp_β1
    | some i1 => exact hS.hβ1 i1

theorem spliceConst_addP (θ0 : DType L) (p0 : List (Trip L × Option κ0))
    (hp_tag : ∀ st ∈ p0, st.2 = none) :
    spliceConst (E0.addDriver θ0) m (fun o => o.elim (some none) (fun i0 => (finv i0).map some))
      (fun o => o.elim p0 pre) =
    spliceConst E0 m finv pre - ((p0.map Prod.fst).map (fun e => E0.P.c e.1 e.2.1 e.2.2)).sum := by
  unfold spliceConst
  have hr : ∀ j0 : κ0, (Finset.univ.filter fun o : Option ι0 =>
      (riderTrip ((E0.addDriver θ0).R j0), some j0) ∈ (o.elim p0 pre)).card =
      (Finset.univ.filter fun i0 => (riderTrip (E0.R j0), some j0) ∈ pre i0).card := by
    intro j0
    symm
    rw [← Finset.card_map Function.Embedding.some]
    apply congrArg Finset.card
    ext o
    cases o with
    | none =>
      simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
        Function.Embedding.some_apply]
      constructor
      · rintro ⟨x, _, hx⟩; cases hx
      · intro hm
        change _ ∈ p0 at hm
        have := hp_tag _ hm; simp at this
    | some i0 => simp; rfl
  simp only [hr]
  rw [Fintype.sum_option]
  simp only [Option.elim]
  simp only [reduceCtorEq, if_false]
  rw [show ∀ (A S X : ℝ), A - (X + S) = (A - S) - X from fun _ _ _ => by ring]
  congr 2
  apply Finset.sum_congr rfl
  intro i0 _
  by_cases hf : finv i0 = none
  · simp [hf, Econ.addDriver]
  · have hf' : (finv i0).map some ≠ none := by simpa using hf
    rw [if_neg hf]
    simp [hf', Econ.addDriver]

end Splice

end StaticAux

end STPRideshare.Mechanism

namespace STPRideshare.Mechanism

open scoped Classical

set_option linter.unusedSectionVars false

namespace BBAux

variable {L : Type}

/-! ### Invariants of a single driver's state -/

/-- Timing invariant of driver states at time `u`. -/
def StInv {κ : Type} (P : Params L) (u : ℕ) : DState L κ → Prop
  | .wait _ _ τ => u ≤ τ
  | .enroute a b t' _ => t' < u ∧ u < t' + P.δ a b
  | .gone => True

theorem stInv_step {κ : Type} (P : Params L) (R : κ → Rider L) (u : ℕ) (s : DState L κ)
    (α : DAction L κ) (hs : StInv P u s) :
    StInv P (u + 1) (step P R u s α) := by
  cases s with
  | wait β a τ =>
    simp only [StInv] at hs
    simp only [step]
    by_cases hτ : τ = u
    · subst hτ
      simp only [if_true]
      cases α with
      | move b =>
        simp only [arrive]; split_ifs with h1
        · simp [StInv]
        · simp only [StInv]; omega
      | pick j =>
        simp only [arrive]; split_ifs with h1
        · simp [StInv]
        · simp only [StInv]; omega
      | quit => simp [StInv]
      | cont => simp [StInv]
    · simp only [hτ, if_false, StInv]; omega
  | enroute a b t' j =>
    simp only [StInv] at hs
    simp only [step]; split_ifs with h1
    · simp [StInv]
    · simp only [StInv]; omega
  | gone => simp [step, StInv]

theorem stInv_stateAt {ι κ : Type} (e : Econ L ι κ) :
    ∀ (h : Hist L ι κ) (i : ι), StInv e.P h.length (stateAt e h i)
  | [], i => by simp [stateAt, StInv]
  | α :: h, i => by
    simp only [stateAt, List.length_cons]
    exact stInv_step _ _ _ _ _ (stInv_stateAt e h i)

theorem playFrom_length {ι κ : Type} (σ : Strategy L ι κ) (h : Hist L ι κ) :
    ∀ k, (playFrom σ h k).length = h.length + k
  | 0 => by simp [playFrom]
  | k + 1 => by simp [playFrom, playFrom_length σ h k]; omega

/-- Every trip a driver is on, or will become available at, ends by `T`. -/
def V {κ : Type} (P : Params L) : DState L κ → Prop
  | .wait _ _ τ => τ ≤ P.T
  | .enroute a b t' _ => t' + P.δ a b ≤ P.T
  | .gone => True

/-- Consistency of a driver's state with a planned path suffix (original time coordinates). -/
def ConsS {κ : Type} (P : Params L) : DState L κ → List (Trip L) → Prop
  | .wait _ a τ, zs => P.IsPathFrom a τ zs
  | .enroute a b t' _, zs => P.IsPathFrom b (t' + P.δ a b) zs
  | .gone, zs => zs = []

/-- A driver at time `u` is consistent with her planned action path `z`: `z` splits into a part
of trips starting before `u` and a remaining part that the driver can still follow. -/
def Cons {κ : Type} (P : Params L) (u : ℕ) (s : DState L κ) (z : List (Trip L × Option κ)) :
    Prop :=
  ∃ pre zs, z = pre ++ zs ∧ (∀ st ∈ pre, st.1.2.2 < u) ∧ ConsS P s (zs.map Prod.fst)

/-- The action prescribed at time `u` by an action path `z` (original time coordinates). -/
def planAct {κ : Type} (z : List (Trip L × Option κ)) (u : ℕ) : DAction L κ :=
  match z.find? (fun st => decide (st.1.2.2 = u)) with
  | some ((_, b, _), none) => .move b
  | some (_, some j) => .pick j
  | none => .quit

theorem find_pre_append {κ : Type} (pre zs : List (Trip L × Option κ)) (u : ℕ)
    (hpre : ∀ st ∈ pre, st.1.2.2 < u) :
    (pre ++ zs).find? (fun st => decide (st.1.2.2 = u)) =
      zs.find? (fun st => decide (st.1.2.2 = u)) := by
  rw [List.find?_append]
  rw [List.find?_eq_none.mpr]
  · simp
  · intro st hst
    have := hpre st hst
    simp only [decide_eq_true_eq]; omega

theorem isPathFrom_times {κ : Type} (P : Params L) :
    ∀ (a : L) (t : ℕ) (zs : List (Trip L × Option κ)), P.IsPathFrom a t (zs.map Prod.fst) →
      ∀ st ∈ zs, t ≤ st.1.2.2
  | _, _, [], _ => by simp
  | a, t, z :: zs, h => by
    simp only [List.map_cons, Params.IsPathFrom] at h
    obtain ⟨h1, h2, h3, h4⟩ := h
    intro st hst
    rcases List.mem_cons.mp hst with rfl | hst
    · omega
    · have := isPathFrom_times P _ _ zs h4 st hst
      have : 1 ≤ 1 := le_refl 1
      omega

theorem cons_step {κ : Type} (P : Params L) (hP : ∀ a b, 1 ≤ P.δ a b) (R : κ → Rider L) (u : ℕ)
    (s : DState L κ) (z : List (Trip L × Option κ)) (hinv : StInv P u s) (hV : V P s)
    (hc : Cons P u s z) (hfeas : ∀ st ∈ z, ∀ j, st.2 = some j → st.1 = riderTrip (R j))
    (α : DAction L κ) (hα : IsAvailAt u s → α = planAct z u) :
    Cons P (u + 1) (step P R u s α) z ∧ V P (step P R u s α) := by
  obtain ⟨pre, zs, rfl, hpre, hcs⟩ := hc
  have hpre' : ∀ st ∈ pre, st.1.2.2 < u + 1 := fun st hst => Nat.lt_succ_of_lt (hpre st hst)
  cases s with
  | wait β a τ =>
    simp only [StInv] at hinv
    simp only [V] at hV
    simp only [ConsS] at hcs
    by_cases hτ : τ = u
    · subst hτ
      have hα' := hα (by simp [IsAvailAt])
      subst hα'
      simp only [step, if_true]
      cases zs with
      | nil =>
        have : planAct (pre ++ []) τ = .quit := by
          simp only [planAct, List.append_nil]
          rw [List.find?_eq_none.mpr]
          intro st hst; have := hpre st hst; simp only [decide_eq_true_eq]; omega
        rw [this]
        exact ⟨⟨pre, [], by simp, hpre', by simp [ConsS]⟩, by simp [V]⟩
      | cons st rest =>
        obtain ⟨⟨a', b, t'⟩, tag⟩ := st
        simp only [List.map_cons, Params.IsPathFrom] at hcs
        obtain ⟨h1, h2, h3, h4⟩ := hcs
        subst a t'
        have hfind : planAct (pre ++ ((a', b, τ), tag) :: rest) τ =
            (match tag with | none => .move b | some j => .pick j) := by
          simp only [planAct]
          rw [find_pre_append _ _ _ hpre]
          cases tag <;> simp
        rw [hfind]
        have hδ := hP a' b
        have key : ∀ jj : Option κ,
            Cons P (τ + 1) (arrive P τ a' b jj) (pre ++ ((a', b, τ), tag) :: rest) ∧
              V P (arrive P τ a' b jj) := by
          intro jj
          refine ⟨⟨pre ++ [((a', b, τ), tag)], rest, by simp, ?_, ?_⟩, ?_⟩
          · intro st hst
            rcases List.mem_append.mp hst with hst | hst
            · exact hpre' st hst
            · simp at hst; subst hst; simp
          · simp only [arrive]
            split_ifs with hh
            · simp only [ConsS]
              rwa [show τ + 1 = τ + P.δ a' b by omega]
            · simpa [ConsS] using h4
          · simp only [arrive]
            split_ifs with hh
            · simp only [V]; omega
            · simp only [V]; omega
        cases tag with
        | none => exact key none
        | some j =>
          have hj := hfeas ((a', b, τ), some j) (by simp) j rfl
          simp only [riderTrip, Prod.mk.injEq] at hj
          simp only
          rw [← hj.2.1]
          exact key (some j)
    · simp only [step, hτ, if_false]
      exact ⟨⟨pre, zs, rfl, hpre', by simpa [ConsS] using hcs⟩, by simpa [V] using hV⟩
  | enroute a b t' j =>
    simp only [StInv] at hinv
    simp only [V] at hV
    simp only [ConsS] at hcs
    simp only [step]
    split_ifs with hh
    · refine ⟨⟨pre, zs, rfl, hpre', ?_⟩, ?_⟩
      · simp only [ConsS]; rwa [show u + 1 = t' + P.δ a b by omega]
      · simp only [V]; omega
    · exact ⟨⟨pre, zs, rfl, hpre', by simpa [ConsS] using hcs⟩, by simpa [V] using hV⟩
  | gone =>
    simp only [step]
    exact ⟨⟨pre, zs, rfl, hpre', hcs⟩, trivial⟩

/-- Position bookkeeping: the prefix `pre` of a plan path started at `(a0, τ0)` (type `β0`) ends
where the driver in state `s` next becomes available, and her entrance status is consistent. -/
def PosOK {κ : Type} (P : Params L) (a0 : L) (τ0 : ℕ) (β0 : Bool) (pre : List (Trip L)) :
    DState L κ → Prop
  | .wait β a τ => P.pathEnd a0 τ0 pre = (a, τ) ∧ (pre = [] → β = β0) ∧ (pre ≠ [] → β = true)
  | .enroute a b t' _ => P.pathEnd a0 τ0 pre = (b, t' + P.δ a b) ∧ (pre = [] → true = β0)
  | .gone => True

/-- `Cons` together with the position bookkeeping of the prefix. -/
def Cons2 {κ : Type} (P : Params L) (u : ℕ) (s : DState L κ) (z : List (Trip L × Option κ))
    (a0 : L) (τ0 : ℕ) (β0 : Bool) : Prop :=
  ∃ pre zs, z = pre ++ zs ∧ (∀ st ∈ pre, st.1.2.2 < u) ∧ ConsS P s (zs.map Prod.fst) ∧
    P.IsPathFrom a0 τ0 (pre.map Prod.fst) ∧ PosOK P a0 τ0 β0 (pre.map Prod.fst) s

theorem cons2_step {κ : Type} (P : Params L) (hP : ∀ a b, 1 ≤ P.δ a b) (R : κ → Rider L) (u : ℕ)
    (s : DState L κ) (z : List (Trip L × Option κ)) (a0 : L) (τ0 : ℕ) (β0 : Bool)
    (hinv : StInv P u s) (hc : Cons2 P u s z a0 τ0 β0)
    (hfeas : ∀ st ∈ z, ∀ j, st.2 = some j → st.1 = riderTrip (R j))
    (α : DAction L κ) (hα : IsAvailAt u s → α = planAct z u) :
    Cons2 P (u + 1) (step P R u s α) z a0 τ0 β0 := by
  obtain ⟨pre, zs, rfl, hpre, hcs, hpp, hpos⟩ := hc
  have hpre' : ∀ st ∈ pre, st.1.2.2 < u + 1 := fun st hst => Nat.lt_succ_of_lt (hpre st hst)
  cases s with
  | wait β a τ =>
    simp only [StInv] at hinv
    simp only [ConsS] at hcs
    simp only [PosOK] at hpos
    obtain ⟨hend, hb0, hb1⟩ := hpos
    by_cases hτ : τ = u
    · subst hτ
      have hα' := hα (by simp [IsAvailAt])
      subst hα'
      simp only [step, if_true]
      cases zs with
      | nil =>
        have : planAct (pre ++ []) τ = .quit := by
          simp only [planAct, List.append_nil]
          rw [List.find?_eq_none.mpr]
          intro st hst; have := hpre st hst; simp only [decide_eq_true_eq]; omega
        rw [this]
        exact ⟨pre, [], by simp, hpre', by simp [ConsS], hpp, trivial⟩
      | cons st rest =>
        obtain ⟨⟨a', b, t'⟩, tag⟩ := st
        have hcs' := hcs
        simp only [List.map_cons, Params.IsPathFrom] at hcs
        obtain ⟨h1, h2, h3, h4⟩ := hcs
        subst a t'
        have hfind : planAct (pre ++ ((a', b, τ), tag) :: rest) τ =
            (match tag with | none => .move b | some j => .pick j) := by
          simp only [planAct]
          rw [find_pre_append _ _ _ hpre]
          cases tag <;> simp
        rw [hfind]
        have hδ := hP a' b
        have key : ∀ jj : Option κ,
            Cons2 P (τ + 1) (arrive P τ a' b jj) (pre ++ ((a', b, τ), tag) :: rest) a0 τ0 β0 := by
          intro jj
          have hpp' : P.IsPathFrom a0 τ0 ((pre ++ [((a', b, τ), tag)]).map Prod.fst) := by
            rw [List.map_append, StaticAux.isPathFrom_append, hend]
            refine ⟨hpp, ?_⟩
            simp only [List.map_cons, List.map_nil, Params.IsPathFrom]
            exact ⟨by simp, by simp, h3, trivial⟩
          have hend' : P.pathEnd a0 τ0 ((pre ++ [((a', b, τ), tag)]).map Prod.fst) =
              (b, τ + P.δ a' b) := by
            rw [List.map_append, StaticAux.pathEnd_append, hend]
            simp [Params.pathEnd]
          have hne : (pre ++ [((a', b, τ), tag)]).map Prod.fst ≠ [] := by simp
          refine ⟨pre ++ [((a', b, τ), tag)], rest, by simp, ?_, ?_, hpp', ?_⟩
          · intro st hst
            rcases List.mem_append.mp hst with hst | hst
            · exact hpre' st hst
            · simp at hst; subst hst; simp
          · simp only [arrive]
            split_ifs with hh
            · simp only [ConsS]
              rwa [show τ + 1 = τ + P.δ a' b by omega]
            · simpa [ConsS] using h4
          · simp only [arrive]
            split_ifs with hh
            · simp only [PosOK]
              refine ⟨by rw [hend']; congr 1; omega, fun h => absurd h hne, fun _ => by simp⟩
            · simp only [PosOK]
              exact ⟨hend', fun h => absurd h hne⟩
        cases tag with
        | none => exact key none
        | some j =>
          have hj := hfeas ((a', b, τ), some j) (by simp) j rfl
          simp only [riderTrip, Prod.mk.injEq] at hj
          simp only
          rw [← hj.2.1]
          exact key (some j)
    · simp only [step, hτ, if_false]
      exact ⟨pre, zs, rfl, hpre', by simpa [ConsS] using hcs, hpp, ⟨hend, hb0, hb1⟩⟩
  | enroute a b t' j =>
    simp only [StInv] at hinv
    simp only [ConsS] at hcs
    simp only [PosOK] at hpos
    obtain ⟨hend, hb0⟩ := hpos
    simp only [step]
    split_ifs with hh
    · refine ⟨pre, zs, rfl, hpre', ?_, hpp, ?_⟩
      · simp only [ConsS]; rwa [show u + 1 = t' + P.δ a b by omega]
      · simp only [PosOK]
        refine ⟨by rw [hend]; congr 1; omega, fun h => hb0 h, fun _ => by simp⟩
    · exact ⟨pre, zs, rfl, hpre', by simpa [ConsS] using hcs, hpp, ⟨hend, hb0⟩⟩
  | gone =>
    simp only [step]
    exact ⟨pre, zs, rfl, hpre', hcs, hpp, trivial⟩

theorem V_step {κ : Type} (P : Params L) (hP : ∀ a b, 1 ≤ P.δ a b) (R : κ → Rider L) (u : ℕ)
    (s : DState L κ) (z : List (Trip L × Option κ)) (hinv : StInv P u s) (hV : V P s)
    (hc : Cons P u s z) (hfeas : ∀ st ∈ z, ∀ j, st.2 = some j → st.1 = riderTrip (R j))
    (α : DAction L κ)
    (hα : ∀ β a, s = .wait β a u →
      (α = planAct z u ∨ (∃ b, α = .move b ∧ u + P.δ a b ≤ P.T) ∨ α = .quit)) :
    V P (step P R u s α) := by
  by_cases hav : IsAvailAt u s
  · cases s with
    | wait β a τ =>
      simp only [IsAvailAt] at hav
      subst hav
      rcases hα β a rfl with h | ⟨b, rfl, hb⟩ | rfl
      · exact (cons_step P hP R τ _ z hinv hV hc hfeas α (fun _ => h)).2
      · simp only [step, if_true, arrive]
        have := hP a b
        split_ifs with hh
        · simp only [V]; omega
        · simp only [V]; omega
      · simp [step, V]
    | enroute => simp [IsAvailAt] at hav
    | gone => simp [IsAvailAt] at hav
  · exact (cons_step P hP R u s z hinv hV hc hfeas α (fun h => absurd h hav)).2

@[simp] theorem shiftParams_δ' (P : Params L) (t : ℕ) : (shiftParams P t).δ = P.δ := rfl

/-- Shift a trip of `E^{(t₀)}` back to original times. -/
def shiftBack {κ : Type} {p : κ → Prop} (t0 : ℕ) (st : Trip L × Option {j // p j}) :
    Trip L × Option κ :=
  ((st.1.1, st.1.2.1, st.1.2.2 + t0), st.2.map Subtype.val)

theorem planAction_id {κ ι0 : Type} {e0 : Econ L ι0 κ} (d : Dispatch e0) (i0 : ι0) (u : ℕ) :
    planAction d i0 u id = planAct (d.z i0) u := by
  unfold planAction planAct
  rcases hf : (d.z i0).find? (fun st => decide (st.1.2.2 = u)) with _ | ⟨⟨a, b, c⟩, _ | j⟩ <;>
    simp [hf]

theorem planAction_shiftBack {κ ι0 : Type} {p : κ → Prop} {e0 : Econ L ι0 {j // p j}}
    (d : Dispatch e0) (i0 : ι0) (t0 u : ℕ) (hle : t0 ≤ u) :
    planAction (κ := κ) d i0 (u - t0) Subtype.val = planAct ((d.z i0).map (shiftBack t0)) u := by
  unfold planAction planAct
  rw [List.find?_map]
  have hp : ((fun st : Trip L × Option κ => decide (st.1.2.2 = u)) ∘ shiftBack t0) =
      (fun st : Trip L × Option {j // p j} => decide (st.1.2.2 = u - t0)) := by
    funext st
    simp only [Function.comp, shiftBack]
    have : st.1.2.2 + t0 = u ↔ st.1.2.2 = u - t0 := by omega
    simp only [this]
  rw [hp]
  rcases hf : (d.z i0).find? (fun st => decide (st.1.2.2 = u - t0)) with _ | ⟨⟨a, b, c⟩, _ | j⟩ <;>
    simp [hf, shiftBack]

theorem isPathFrom_shift {κ0 : Type} (P : Params L) (t0 : ℕ) (hT : t0 ≤ P.T) {p : κ0 → Prop} :
    ∀ (a : L) (τ' : ℕ) (zs : List (Trip L × Option {j // p j})),
      (shiftParams P t0).IsPathFrom a τ' (zs.map Prod.fst) →
      P.IsPathFrom a (τ' + t0) ((zs.map (shiftBack t0)).map Prod.fst)
  | _, _, [], _ => by simp [Params.IsPathFrom]
  | a, τ', z :: zs, h => by
    simp only [List.map_cons, Params.IsPathFrom] at h ⊢
    obtain ⟨h1, h2, h3, h4⟩ := h
    simp only [shiftParams_δ'] at h3 h4
    refine ⟨by simp [shiftBack, h1], by simp [shiftBack, h2], ?_, ?_⟩
    · simp only [shiftBack, shiftParams] at h3 ⊢; omega
    · have := isPathFrom_shift P t0 hT _ _ zs h4
      simp only [shiftBack] at this ⊢
      rwa [show τ' + t0 + P.δ a z.1.2.1 = τ' + P.δ a z.1.2.1 + t0 by omega]

theorem consS_shiftType {κ0 : Type} (P : Params L) (t0 : ℕ) (hT : t0 ≤ P.T) (s : DState L κ0)
    (hs : s ≠ .gone) (hinv : StInv P t0 s) {R : κ0 → Rider L}
    (zs : List (Trip L × Option {j // t0 ≤ (R j).τ}))
    (hp : (shiftParams P t0).IsPathFrom (shiftType P t0 s hs).ℓ (shiftType P t0 s hs).τ
      (zs.map Prod.fst)) :
    ConsS P s ((zs.map (shiftBack t0)).map Prod.fst) := by
  cases s with
  | wait β a τ =>
    simp only [StInv] at hinv
    have := isPathFrom_shift P t0 hT a (τ - t0) zs hp
    simp only [ConsS]
    rwa [Nat.sub_add_cancel hinv] at this
  | enroute a b t' j =>
    simp only [StInv] at hinv
    have := isPathFrom_shift P t0 hT b (t' + P.δ a b - t0) zs hp
    simp only [ConsS]
    rwa [Nat.sub_add_cancel (by omega)] at this
  | gone => exact absurd rfl hs

/-- The conclusion of Step 1 used downstream: welfare-optimal dispatchings are CE with the STP
prices (28). -/
def Step1CE (L : Type) [Fintype L] : Prop :=
  ∀ {ι κ : Type} [Fintype ι] [Fintype κ] (e : Econ L ι κ), e.Valid →
    ∀ d : Dispatch e, d.IsWelfareOptimal → d.IsCE e.stpPrice

section Global

variable [Fintype L] (sel : Selector L) {ι κ : Type} [Fintype ι] [Fintype κ] (e : Econ L ι κ)

/-- The current plan's action path of each driver, in original coordinates. -/
noncomputable def curZ (h : Hist L ι κ) (i : ι) : List (Trip L × Option κ) :=
  if replanTime sel e h = 0 then (sel e).z i
  else if hi : stateAt e (h.drop (h.length - replanTime sel e h)) i ≠ .gone then
    ((sel (shiftEcon e (h.drop (h.length - replanTime sel e h)))).z ⟨i, hi⟩).map
      (shiftBack (replanTime sel e h))
  else []

theorem disp_planAct (h : Hist L ι κ) (i : ι) (hle : replanTime sel e h ≤ h.length)
    (ha : IsAvailAt h.length (stateAt e h i)) :
    stpDispatchVia sel e (replanTime sel e h) h i = planAct (curZ sel e h i) h.length := by
  unfold stpDispatchVia curZ
  rw [if_pos ha]
  by_cases h0 : replanTime sel e h = 0
  · rw [if_pos h0, if_pos h0, planAction_id]
  · rw [if_neg h0, if_neg h0]
    by_cases hi : stateAt e (h.drop (h.length - replanTime sel e h)) i ≠ .gone
    · rw [dif_pos hi, dif_pos hi, planAction_shiftBack _ _ _ _ hle]
    · rw [dif_neg hi, dif_neg hi]
      simp [planAct]

omit [Fintype L] [Fintype ι] [Fintype κ] in
theorem shiftType_le (P : Params L) (t0 : ℕ) (s : DState L κ) (hs : s ≠ .gone) (hV : V P s) :
    (shiftType P t0 s hs).τ ≤ P.T - t0 := by
  cases s with
  | wait β a τ => simp only [V] at hV; simp only [shiftType]; omega
  | enroute a b t' j => simp only [V] at hV; simp only [shiftType]; omega
  | gone => exact absurd rfl hs

omit [Fintype L] [Fintype ι] [Fintype κ] in
theorem econAt_valid (he : e.Valid) (h : Hist L ι κ)
    (hV : ∀ i, V e.P (stateAt e h i)) : (shiftEcon e h).Valid := by
  obtain ⟨⟨hP1, hP2, hP3, hP4, hP5⟩, hD, hRv, hRt⟩ := he
  refine ⟨⟨hP1, hP2, ?_, ?_, hP5⟩, ?_, ?_, ?_⟩
  · intro a b t ht
    have := hP1 a b
    exact hP3 a b (t + h.length) (by simp only [shiftEcon, econAt, shiftParams] at ht ⊢; omega)
  · intro n hn
    exact hP4 n (by simp only [shiftEcon, econAt, shiftParams] at hn ⊢; omega)
  · intro i
    exact shiftType_le e.P h.length _ i.2 (hV i.1)
  · intro j; exact hRv j.1
  · intro j
    have := hRt j.1
    have hj := j.2
    simp only [Params.IsTrip, riderTrip, shiftEcon, econAt, shiftParams] at this ⊢
    omega

/-- The current plan is feasible-like in original coordinates. -/
def PlanOK (Z : ι → List (Trip L × Option κ)) : Prop :=
  (∀ i st, st ∈ Z i → ∀ j, st.2 = some j → st.1 = riderTrip (e.R j)) ∧
  (∀ j, (Finset.univ.filter fun i => (riderTrip (e.R j), some j) ∈ Z i).card ≤ 1)

/-- The global invariant along reachable histories. -/
def Good (h : Hist L ι κ) : Prop :=
  replanTime sel e h ≤ h.length ∧ (∀ i, V e.P (stateAt e h i)) ∧ PlanOK e (curZ sel e h) ∧
    ∀ i, Cons e.P h.length (stateAt e h i) (curZ sel e h i)

theorem good_nil (he : e.Valid) (hsel : IsOptimalSelector sel) : Good sel e [] := by
  have hrt : replanTime sel e [] = 0 := rfl
  have hz : ∀ i, curZ sel e [] i = (sel e).z i := fun i => by simp [curZ, hrt]
  obtain ⟨hf1, hf2, hf3, hf4⟩ := (hsel e he).1
  refine ⟨by simp [hrt], ?_, ?_, ?_⟩
  · intro i; simp only [stateAt, V]; exact he.2.1 i
  · refine ⟨fun i st hst j hj => hf2 i st (by rw [← hz]; exact hst) j hj, fun j => ?_⟩
    have := hf4 j
    rw [hf3 j] at this
    simp only [hz]
    convert this using 2
  · intro i
    refine ⟨[], curZ sel e [] i, by simp, by simp, ?_⟩
    simp only [stateAt, ConsS, hz]
    exact hf1 i

omit [Fintype L] in
theorem stpDispatchVia_notAvail (t0 : ℕ) (h : Hist L ι κ) (i : ι)
    (hn : ¬ IsAvailAt h.length (stateAt e h i)) : stpDispatchVia sel e t0 h i = .cont := by
  simp [stpDispatchVia, hn]

omit [Fintype L] in
theorem dispatch_eq (h : Hist L ι κ) (i : ι) :
    (stp sel).dispatch e h i = stpDispatchVia sel e (replanTime sel e h) h i := by
  unfold DynMech.dispatch
  split_ifs with ha
  · rfl
  · rw [stpDispatchVia_notAvail sel e _ _ _ ha]

omit [Fintype L] in
theorem curZ_noDev (α : ι → DAction L κ) (h : Hist L ι κ) (hle : replanTime sel e h ≤ h.length)
    (hnd : ∀ i, α i = stpDispatchVia sel e (replanTime sel e h) h i) :
    replanTime sel e (α :: h) = replanTime sel e h ∧ curZ sel e (α :: h) = curZ sel e h := by
  have hrt : replanTime sel e (α :: h) = replanTime sel e h := by
    simp only [replanTime]
    rw [if_neg]
    push Not
    exact hnd
  have hdrop : (α :: h).drop ((α :: h).length - replanTime sel e (α :: h)) =
      h.drop (h.length - replanTime sel e h) := by
    rw [hrt, List.length_cons, show h.length + 1 - replanTime sel e h =
      (h.length - replanTime sel e h) + 1 by omega, List.drop_succ_cons]
  refine ⟨hrt, ?_⟩
  funext i
  unfold curZ
  rw [hdrop, hrt]

omit [Fintype L] in
theorem curZ_replan (h : Hist L ι κ) (hrt : replanTime sel e h = h.length) (hpos : h.length ≠ 0)
    (i : ι) :
    curZ sel e h i = if hi : stateAt e h i ≠ .gone then
      ((sel (shiftEcon e h)).z ⟨i, hi⟩).map (shiftBack h.length) else [] := by
  have hdrop : h.drop (h.length - replanTime sel e h) = h := by
    rw [hrt, Nat.sub_self, List.drop_zero]
  unfold curZ
  rw [if_neg (by rw [hrt]; exact hpos)]
  rw [hdrop, hrt]

omit [Fintype L] in
theorem actions_avail (h : Hist L ι κ) (i : ι) (β : Bool) (a : L)
    (hs : stateAt e h i = .wait β a h.length) (α : DAction L κ)
    (hα : α ∈ (stp sel).actions e h i) :
    α = stpDispatchVia sel e (replanTime sel e h) h i ∨
      (∃ b, α = .move b ∧ h.length + e.P.δ a b ≤ e.P.T) ∨ α = .quit := by
  unfold DynMech.actions at hα
  rw [hs] at hα
  simp only [if_true, Set.mem_union, Set.mem_singleton_iff, Set.mem_ofPred_eq] at hα
  rcases hα with (h1 | h1) | h1
  · left; exact h1
  · right; left; exact h1
  · right; right; exact h1

omit [Fintype L] in
theorem actions_notAvail (h : Hist L ι κ) (i : ι) (hn : ¬ IsAvailAt h.length (stateAt e h i))
    (α : DAction L κ) (hα : α ∈ (stp sel).actions e h i) : α = .cont := by
  unfold DynMech.actions at hα
  revert hα hn
  cases stateAt e h i with
  | wait β a τ =>
    intro hn hα
    simp only [IsAvailAt] at hn
    simpa [hn] using hα
  | enroute => intro _ hα; simpa using hα
  | gone => intro _ hα; simpa using hα

theorem card_sub {Q : ι → Prop} [Fintype {i // Q i}] (P : ι → Prop) {d1 : DecidablePred P}
    [DecidablePred (fun i' : {i // Q i} => P i'.1)] (hPQ : ∀ i, P i → Q i) :
    (Finset.univ.filter P).card = (Finset.univ.filter (fun i' : {i // Q i} => P i'.1)).card := by
  rw [← Finset.card_map (Function.Embedding.subtype Q)]
  congr 1
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map,
    Function.Embedding.subtype_apply]
  constructor
  · intro hi; exact ⟨⟨i, hPQ i hi⟩, hi, rfl⟩
  · rintro ⟨i', hi', rfl⟩; exact hi'

theorem planOK_replan (he : e.Valid) (hsel : IsOptimalSelector sel) (h : Hist L ι κ)
    (hrt : replanTime sel e h = h.length) (hpos : h.length ≠ 0)
    (hV : ∀ i, V e.P (stateAt e h i)) : PlanOK e (curZ sel e h) := by
  have hval := econAt_valid e he h hV
  obtain ⟨hf1, hf2, hf3, hf4⟩ := (hsel (shiftEcon e h) hval).1
  -- membership in the shifted-back path
  have hmem : ∀ i st, st ∈ curZ sel e h i → ∃ (hi : stateAt e h i ≠ .gone),
      ∃ st0 ∈ (sel (shiftEcon e h)).z ⟨i, hi⟩, shiftBack h.length st0 = st := by
    intro i st hst
    rw [curZ_replan sel e h hrt hpos] at hst
    by_cases hi : stateAt e h i ≠ .gone
    · rw [dif_pos hi] at hst
      obtain ⟨st0, h0, h1⟩ := List.mem_map.mp hst
      exact ⟨hi, st0, h0, h1⟩
    · rw [dif_neg hi] at hst; simp at hst
  refine ⟨?_, ?_⟩
  · intro i st hst j hj
    obtain ⟨hi, st0, h0, rfl⟩ := hmem i st hst
    simp only [shiftBack, Option.map_eq_some_iff] at hj
    obtain ⟨j1, hj1, rfl⟩ := hj
    have := hf2 ⟨i, hi⟩ st0 h0 j1 hj1
    have hτ := j1.2
    simp only [shiftBack, this, riderTrip, shiftEcon, econAt]
    simp only [Prod.mk.injEq, true_and]
    omega
  · intro j
    by_cases hj : h.length ≤ (e.R j).τ
    · set j0 : {j : κ // h.length ≤ (e.R j).τ} := ⟨j, hj⟩
      rw [card_sub (Q := fun i => stateAt e h i ≠ .gone) _ (fun i hi => by
        obtain ⟨hi', _⟩ := hmem i _ hi; exact hi')]
      calc _ ≤ (Finset.univ.filter fun i0 =>
              (riderTrip ((shiftEcon e h).R j0), some j0) ∈ (sel (shiftEcon e h)).z i0).card := by
            apply Finset.card_le_card
            intro i0
            simp only [Finset.mem_filter, Finset.mem_univ, true_and]
            intro hi0
            obtain ⟨hi, st0, h0, h1⟩ := hmem i0.1 _ hi0
            have h1' := congrArg Prod.snd h1
            simp only [shiftBack, Option.map_eq_some_iff] at h1'
            obtain ⟨j1, hj1, hj1v⟩ := h1'
            have hj10 : j1 = j0 := Subtype.ext hj1v
            have e1 := hf2 ⟨i0.1, hi⟩ st0 h0 j1 hj1
            have e2 : st0 = (st0.1, st0.2) := rfl
            rw [e2, e1, hj1, hj10] at h0
            exact h0
        _ ≤ 1 := by
            have := hf4 j0
            rw [hf3 j0] at this
            convert this using 2
            ext x; simp
    · have : (Finset.univ.filter fun i => (riderTrip (e.R j), some j) ∈ curZ sel e h i) = ∅ := by
        ext i
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
        intro hi0
        obtain ⟨hi, st0, h0, h1⟩ := hmem i _ hi0
        have h1' := congrArg Prod.snd h1
        simp only [shiftBack, Option.map_eq_some_iff] at h1'
        obtain ⟨j1, _, hj1v⟩ := h1'
        exact hj (hj1v ▸ j1.2)
      rw [this]; simp

theorem cons_replan (he : e.Valid) (hsel : IsOptimalSelector sel) (h : Hist L ι κ)
    (hrt : replanTime sel e h = h.length) (hpos : h.length ≠ 0) (hT : h.length ≤ e.P.T)
    (hV : ∀ i, V e.P (stateAt e h i)) (i : ι) :
    Cons e.P h.length (stateAt e h i) (curZ sel e h i) := by
  have hval := econAt_valid e he h hV
  obtain ⟨hf1, hf2, hf3, hf4⟩ := (hsel (shiftEcon e h) hval).1
  rw [curZ_replan sel e h hrt hpos]
  by_cases hi : stateAt e h i ≠ .gone
  · rw [dif_pos hi]
    refine ⟨[], ((sel (shiftEcon e h)).z ⟨i, hi⟩).map (shiftBack h.length), by simp, by simp, ?_⟩
    exact consS_shiftType e.P h.length hT _ hi (stInv_stateAt e h i) _ (hf1 ⟨i, hi⟩)
  · rw [dif_neg hi]
    push Not at hi
    refine ⟨[], [], by simp, by simp, ?_⟩
    rw [hi]; simp [ConsS]

theorem good_cons (he : e.Valid) (hsel : IsOptimalSelector sel) (α : ι → DAction L κ)
    (h : Hist L ι κ) (hr : (stp sel).Reachable e (α :: h)) (hg : Good sel e h) :
    Good sel e (α :: h) := by
  obtain ⟨_, hlt, hact⟩ := hr
  obtain ⟨hle, hV, ⟨hok1, hok2⟩, hC⟩ := hg
  have hP1 := he.1.1
  have hst : ∀ i, stateAt e (α :: h) i = step e.P e.R h.length (stateAt e h i) (α i) :=
    fun i => rfl
  have hV' : ∀ i, V e.P (stateAt e (α :: h) i) := by
    intro i
    rw [hst]
    refine V_step e.P hP1 e.R h.length _ (curZ sel e h i) (stInv_stateAt e h i) (hV i) (hC i)
      (hok1 i) (α i) ?_
    intro β a hs
    rcases actions_avail sel e h i β a hs (α i) (hact i) with h1 | h1 | h1
    · left
      rw [h1, disp_planAct sel e h i hle (by rw [hs]; simp [IsAvailAt])]
    · right; left; exact h1
    · right; right; exact h1
  by_cases hdev : ∃ i, α i ≠ stpDispatchVia sel e (replanTime sel e h) h i
  · have hrt : replanTime sel e (α :: h) = (α :: h).length := by
      simp only [replanTime]
      rw [if_pos hdev]; simp
    have hpos : (α :: h).length ≠ 0 := by simp
    have hT : (α :: h).length ≤ e.P.T := by simp; omega
    exact ⟨le_of_eq hrt, hV', planOK_replan sel e he hsel _ hrt hpos hV',
      cons_replan sel e he hsel _ hrt hpos hT hV'⟩
  · push Not at hdev
    obtain ⟨hrt, hz⟩ := curZ_noDev sel e α h hle hdev
    refine ⟨by rw [hrt]; exact Nat.le_succ_of_le hle, hV', by rw [hz]; exact ⟨hok1, hok2⟩, ?_⟩
    intro i
    rw [hz, hst]
    refine (cons_step e.P hP1 e.R h.length _ (curZ sel e h i) (stInv_stateAt e h i) (hV i) (hC i)
      (hok1 i) (α i) ?_).1
    intro ha
    rw [hdev i, disp_planAct sel e h i hle ha]

theorem good_of_reachable (he : e.Valid) (hsel : IsOptimalSelector sel) :
    ∀ h : Hist L ι κ, (stp sel).Reachable e h → Good sel e h
  | [], _ => good_nil sel e he hsel
  | α :: h, hr => good_cons sel e he hsel α h hr (good_of_reachable he hsel h hr.1)

/-- The state of a driver at the time the current plan was computed. -/
noncomputable def planStart (h : Hist L ι κ) (i : ι) : DState L κ :=
  stateAt e (h.drop (h.length - replanTime sel e h)) i

/-- `Cons2` relative to the plan start. -/
def ConsP {κ0 : Type} (P : Params L) (u : ℕ) (s : DState L κ0) (z : List (Trip L × Option κ0)) :
    DState L κ0 → Prop
  | .wait β a τ => Cons2 P u s z a τ β
  | .enroute a b t' _ => Cons2 P u s z b (t' + P.δ a b) true
  | .gone => True

/-- The strengthened invariant. -/
def Good2 (h : Hist L ι κ) : Prop :=
  ∀ i, ConsP e.P h.length (stateAt e h i) (curZ sel e h i) (planStart sel e h i)

omit [Fintype L] in
theorem drop_noDev (α : ι → DAction L κ) (h : Hist L ι κ) (hle : replanTime sel e h ≤ h.length)
    (hrt : replanTime sel e (α :: h) = replanTime sel e h) :
    (α :: h).drop ((α :: h).length - replanTime sel e (α :: h)) =
      h.drop (h.length - replanTime sel e h) := by
  rw [hrt, List.length_cons, show h.length + 1 - replanTime sel e h =
    (h.length - replanTime sel e h) + 1 by omega, List.drop_succ_cons]

theorem consP_start {κ0 : Type} (P : Params L) (u : ℕ) (s : DState L κ0)
    (z : List (Trip L × Option κ0)) (hc : ConsS P s (z.map Prod.fst)) :
    ConsP P u s z s := by
  cases s with
  | wait β a τ =>
    exact ⟨[], z, by simp, by simp, hc, by simp [Params.IsPathFrom],
      by simp [PosOK, Params.pathEnd]⟩
  | enroute a b t' jj =>
    exact ⟨[], z, by simp, by simp, hc, by simp [Params.IsPathFrom],
      by simp [PosOK, Params.pathEnd]⟩
  | gone => trivial

theorem good2_of_reachable (he : e.Valid) (hsel : IsOptimalSelector sel) :
    ∀ h : Hist L ι κ, (stp sel).Reachable e h → Good2 sel e h
  | [], _ => by
    intro i
    obtain ⟨hf1, _, _, _⟩ := (hsel e he).1
    have hz : curZ sel e [] i = (sel e).z i := by simp [curZ, replanTime]
    show ConsP e.P 0 (stateAt e [] i) (curZ sel e [] i) (stateAt e [] i)
    rw [hz]
    exact consP_start e.P 0 _ _ (hf1 i)
  | α :: h, hr => by
    have IH := good2_of_reachable he hsel h hr.1
    obtain ⟨hle, hV, ⟨hok1, _⟩, hC⟩ := good_of_reachable sel e he hsel h hr.1
    have hP1 := he.1.1
    by_cases hdev : ∃ i, α i ≠ stpDispatchVia sel e (replanTime sel e h) h i
    · have hrt : replanTime sel e (α :: h) = (α :: h).length := by
        simp only [replanTime]
        rw [if_pos hdev]; simp
      have hpos : (α :: h).length ≠ 0 := by simp
      obtain ⟨_, hV', _, hC'⟩ := good_of_reachable sel e he hsel (α :: h) hr
      intro i
      have hps : planStart sel e (α :: h) i = stateAt e (α :: h) i := by
        unfold planStart; rw [hrt, Nat.sub_self, List.drop_zero]
      rw [hps]
      have hval := econAt_valid e he (α :: h) hV'
      obtain ⟨hf1, _, _, _⟩ := (hsel (shiftEcon e (α :: h)) hval).1
      rw [curZ_replan sel e _ hrt hpos]
      by_cases hi : stateAt e (α :: h) i ≠ .gone
      · rw [dif_pos hi]
        apply consP_start
        exact consS_shiftType e.P _ (by have := hr.2.1; simp; omega) _ hi
          (stInv_stateAt e (α :: h) i) _ (hf1 ⟨i, hi⟩)
      · rw [dif_neg hi]
        push Not at hi
        rw [hi]; trivial
    · push Not at hdev
      obtain ⟨hrt, hz⟩ := curZ_noDev sel e α h hle hdev
      intro i
      have hps : planStart sel e (α :: h) i = planStart sel e h i := by
        unfold planStart; rw [drop_noDev sel e α h hle hrt]
      rw [hps, hz]
      have hst : stateAt e (α :: h) i = step e.P e.R h.length (stateAt e h i) (α i) := rfl
      rw [hst, List.length_cons]
      have hα : IsAvailAt h.length (stateAt e h i) → α i = planAct (curZ sel e h i) h.length :=
        fun ha => by rw [hdev i, disp_planAct sel e h i hle ha]
      have IHi := IH i
      revert IHi
      cases planStart sel e h i with
      | wait β a τ =>
        intro IHi
        exact cons2_step e.P hP1 e.R h.length _ _ a τ β (stInv_stateAt e h i) IHi (hok1 i) _ hα
      | enroute a b t' jj =>
        intro IHi
        exact cons2_step e.P hP1 e.R h.length _ _ b _ true (stInv_stateAt e h i) IHi (hok1 i) _ hα
      | gone => intro _; trivial

omit [Fintype L] [Fintype ι] [Fintype κ] in
theorem planAct_pick (z : List (Trip L × Option κ)) (u : ℕ) (j : κ)
    (hp : planAct z u = .pick j) : ∃ st ∈ z, st.1.2.2 = u ∧ st.2 = some j := by
  unfold planAct at hp
  rcases hf : z.find? (fun st => decide (st.1.2.2 = u)) with _ | ⟨⟨a, b, c⟩, _ | j'⟩ <;>
    rw [hf] at hp
  · cases hp
  · cases hp
  · simp only [DAction.pick.injEq] at hp
    subst hp
    refine ⟨_, List.mem_of_find?_eq_some hf, ?_, rfl⟩
    have := List.find?_some hf
    simpa using this

theorem pick_facts (he : e.Valid) (hsel : IsOptimalSelector sel) (h : Hist L ι κ)
    (hr : (stp sel).Reachable e h) (i : ι) (j : κ)
    (hp : stpDispatchVia sel e (replanTime sel e h) h i = .pick j) :
    IsAvailAt h.length (stateAt e h i) ∧ (e.R j).τ = h.length ∧
      (riderTrip (e.R j), some j) ∈ curZ sel e h i := by
  obtain ⟨hle, _, ⟨hok1, _⟩, _⟩ := good_of_reachable sel e he hsel h hr
  by_cases ha : IsAvailAt h.length (stateAt e h i)
  · rw [disp_planAct sel e h i hle ha] at hp
    obtain ⟨st, hst, ht, hj⟩ := planAct_pick _ _ _ hp
    have := hok1 i st hst j hj
    refine ⟨ha, ?_, ?_⟩
    · rw [← ht, this]; rfl
    · have e2 : st = (st.1, st.2) := rfl
      rw [e2, this, hj] at hst; exact hst
  · rw [stpDispatchVia_notAvail sel e _ _ _ ha] at hp; cases hp

theorem dispCount_le (he : e.Valid) (hsel : IsOptimalSelector sel) (h : Hist L ι κ)
    (hr : (stp sel).Reachable e h) (j : κ) :
    (Finset.univ.filter fun i => stpDispatchVia sel e (replanTime sel e h) h i = .pick j).card ≤ 1 := by
  obtain ⟨_, _, ⟨_, hok2⟩, _⟩ := good_of_reachable sel e he hsel h hr
  refine le_trans (Finset.card_le_card ?_) (hok2 j)
  intro i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  intro hp
  exact (pick_facts sel e he hsel h hr i j hp).2.2

omit [Fintype L] in
theorem reach_play (σ : Strategy L ι κ) (hσ : (stp sel).AdmissibleProfile e σ) :
    ∀ k, k ≤ e.P.T → (stp sel).Reachable e (playFrom σ [] k)
  | 0, _ => trivial
  | k + 1, hk => by
    refine ⟨reach_play σ hσ k (by omega), ?_, ?_⟩
    · rw [playFrom_length]; simp; omega
    · intro i
      exact hσ i _ (by rw [playFrom_length]; simp; omega)

omit [Fintype L] [Fintype ι] [Fintype κ] in
theorem avail_wait (u : ℕ) (s : DState L κ) (ha : IsAvailAt u s) : ∃ β a, s = .wait β a u := by
  cases s with
  | wait β a τ => simp only [IsAvailAt] at ha; exact ⟨β, a, by rw [ha]⟩
  | enroute => simp [IsAvailAt] at ha
  | gone => simp [IsAvailAt] at ha

omit [Fintype L] in
theorem pick_dispatched (h : Hist L ι κ) (i : ι) (α : DAction L κ)
    (hα : α ∈ (stp sel).actions e h i) (j : κ) (hp : α = .pick j) :
    IsAvailAt h.length (stateAt e h i) ∧ stpDispatchVia sel e (replanTime sel e h) h i = .pick j := by
  by_cases ha : IsAvailAt h.length (stateAt e h i)
  · refine ⟨ha, ?_⟩
    obtain ⟨β, a, hs⟩ := avail_wait _ _ ha
    rcases actions_avail sel e h i β a hs α hα with h1 | ⟨b, h1, _⟩ | h1
    · rw [← h1, hp]
    · rw [hp] at h1; cases h1
    · rw [hp] at h1; cases h1
  · have := actions_notAvail sel e h i ha α hα
    rw [hp] at this; cases this

omit [Fintype L] in
theorem pay_eq (h : Hist L ι κ) (i : ι) : (stp sel).pay e h i =
      match stpDispatchVia sel e (replanTime sel e h) h i with
      | .pick j => stpPriceVia sel e h (riderTrip (e.R j))
      | _ => 0 := rfl

omit [Fintype L] in
theorem payNow_split (h : Hist L ι κ) (hT : h.length < e.P.T) (σ : Strategy L ι κ)
    (hσ : (stp sel).AdmissibleProfile e σ) (i : ι) :
    (stp sel).payNow e h i (σ i h) =
      ∑ j, if IsAvailAt h.length (stateAt e h i) ∧ σ i h = .pick j then
        stpPriceVia sel e h (riderTrip (e.R j)) else 0 := by
  have hadm := hσ i h hT
  unfold DynMech.payNow
  by_cases hc : IsAvailAt h.length (stateAt e h i) ∧ σ i h = (stp sel).dispatch e h i
  · rw [if_pos hc, pay_eq]
    obtain ⟨ha, hd⟩ := hc
    rw [dispatch_eq] at hd
    rw [← hd]
    rcases hs : σ i h with b | j0 | _ | _
    · symm; apply Finset.sum_eq_zero; intro j _; rw [if_neg]; simp
    · simp only [DAction.pick.injEq]
      rw [Finset.sum_eq_single j0]
      · simp [ha]
      · intro j _ hj; rw [if_neg]; intro h1; exact hj h1.2.symm
      · simp
    · symm; apply Finset.sum_eq_zero; intro j _; rw [if_neg]; simp
    · symm; apply Finset.sum_eq_zero; intro j _; rw [if_neg]; simp
  · rw [if_neg hc]
    symm; apply Finset.sum_eq_zero; intro j _
    rw [if_neg]
    rintro ⟨ha, hp⟩
    apply hc
    refine ⟨ha, ?_⟩
    rw [dispatch_eq, (pick_dispatched sel e h i _ hadm j hp).2, hp]

theorem bb_main (he : e.Valid) (hsel : IsOptimalSelector sel) (σ : Strategy L ι κ)
    (hσ : (stp sel).AdmissibleProfile e σ) :
    ∑ j, (stp sel).riderCharge e σ [] j = ∑ i, (stp sel).totalPay e σ i := by
  -- the right-hand side
  have hR : ∑ i, (stp sel).totalPay e σ i = ∑ j, ∑ k ∈ Finset.range e.P.T,
      ((Finset.univ.filter fun i => IsAvailAt (playFrom σ [] k).length
          (stateAt e (playFrom σ [] k) i) ∧ σ i (playFrom σ [] k) = .pick j).card : ℝ) *
        stpPriceVia sel e (playFrom σ [] k) (riderTrip (e.R j)) := by
    unfold DynMech.totalPay
    rw [Finset.sum_comm]
    have : ∀ k ∈ Finset.range e.P.T, ∑ i, (stp sel).payNow e (playFrom σ [] k) i
        (σ i (playFrom σ [] k)) = ∑ j,
          ((Finset.univ.filter fun i => IsAvailAt (playFrom σ [] k).length
            (stateAt e (playFrom σ [] k) i) ∧ σ i (playFrom σ [] k) = .pick j).card : ℝ) *
          stpPriceVia sel e (playFrom σ [] k) (riderTrip (e.R j)) := by
      intro k hk
      have hkT : (playFrom σ [] k).length < e.P.T := by
        rw [playFrom_length]; simp only [List.length_nil, zero_add]
        exact Finset.mem_range.mp hk
      simp_rw [payNow_split sel e _ hkT σ hσ]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]
    rw [Finset.sum_congr rfl this, Finset.sum_comm]
  rw [hR]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  have hτT : (e.R j).τ < e.P.T := by
    have h1 := he.2.2.2 j
    have h2 := he.1.1 (e.R j).o (e.R j).d
    simp only [Params.IsTrip, riderTrip] at h1
    omega
  have hreach : ∀ k, k < e.P.T → (stp sel).Reachable e (playFrom σ [] k) :=
    fun k hk => reach_play sel e σ hσ k (le_of_lt hk)
  rw [Finset.sum_eq_single (e.R j).τ]
  · -- the rider's term
    unfold DynMech.riderCharge riderPicked pickCount histAt
    simp only [List.length_nil, Nat.sub_zero]
    set H := playFrom σ [] (e.R j).τ
    show stpPriceVia sel e H (riderTrip (e.R j)) *
        ((Finset.univ.filter fun i => stpDispatchVia sel e (replanTime sel e H) H i = .pick j).card : ℝ) *
        _ = _
    have hD := dispCount_le sel e he hsel H (hreach _ hτT) j
    have hsub : (Finset.univ.filter fun i => IsAvailAt H.length (stateAt e H i) ∧
        σ i H = .pick j) ⊆
        (Finset.univ.filter fun i => stpDispatchVia sel e (replanTime sel e H) H i = .pick j) := by
      intro i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      intro hi
      have hHT : H.length < e.P.T := by
        simp only [H]; rw [playFrom_length]; simpa using hτT
      exact (pick_dispatched sel e H i _ (hσ i H hHT) j hi.2).2
    have hle := Finset.card_le_card hsub
    rcases Nat.eq_zero_or_pos (Finset.univ.filter fun i => IsAvailAt H.length (stateAt e H i) ∧
        σ i H = .pick j).card with h0 | h0
    · rw [h0]; simp
    · have h1 : (Finset.univ.filter fun i =>
          stpDispatchVia sel e (replanTime sel e H) H i = .pick j).card = 1 := by omega
      rw [h1]; push_cast; ring
  · intro k hk hkj
    have hkT := Finset.mem_range.mp hk
    rw [Finset.card_eq_zero.mpr]
    · simp
    · rw [Finset.filter_eq_empty_iff]
      rintro i - ⟨_, hp⟩
      have hHT : (playFrom σ [] k).length < e.P.T := by rw [playFrom_length]; simpa using hkT
      have hd := pick_dispatched sel e _ i _ (hσ i _ hHT) j hp
      have := (pick_facts sel e he hsel _ (hreach k hkT) i j hd.2).2.1
      rw [playFrom_length] at this
      simp at this
      exact hkj this.symm
  · intro h; exact absurd (Finset.mem_range.mpr hτT) h

omit [Fintype L] in
theorem reach_drop : ∀ (h : Hist L ι κ) (n : ℕ), (stp sel).Reachable e h →
    (stp sel).Reachable e (h.drop n)
  | [], _, _ => by simp [DynMech.Reachable]
  | _ :: _, 0, hr => by simpa using hr
  | _ :: h, n + 1, hr => by simpa using reach_drop h n hr.1

theorem stpPrice_inst {ι0 κ0 : Type} (e0 : Econ L ι0 κ0) (i1 i2 : Fintype ι0) (k1 k2 : Fintype κ0)
    (tr : Trip L) : @Econ.stpPrice L ι0 κ0 i1 k1 e0 tr = @Econ.stpPrice L ι0 κ0 i2 k2 e0 tr := by
  obtain rfl := Subsingleton.elim i1 i2
  obtain rfl := Subsingleton.elim k1 k2
  rfl

/-- The rider-trip price used by the mechanism is at most the value of a rider who is dispatched
a driver: a consequence of Step 1 (the STP plan is a CE). -/
theorem price_le_value (hS1 : Step1CE L) (he : e.Valid) (hsel : IsOptimalSelector sel)
    (h : Hist L ι κ)
    (hr : (stp sel).Reachable e h) (i : ι) (j : κ)
    (hp : stpDispatchVia sel e (replanTime sel e h) h i = .pick j) :
    stpPriceVia sel e h (riderTrip (e.R j)) ≤ (e.R j).v := by
  obtain ⟨_, _, hmemZ⟩ := pick_facts sel e he hsel h hr i j hp
  obtain ⟨hle, _, _, _⟩ := good_of_reachable sel e he hsel h hr
  unfold stpPriceVia
  by_cases h0 : replanTime sel e h = 0
  · rw [if_pos h0]
    have hz : curZ sel e h i = (sel e).z i := by simp [curZ, h0]
    rw [hz] at hmemZ
    have hd := hsel e he
    obtain ⟨hf1, hf2, hf3, hf4⟩ := hd.1
    have hce := hS1 e he (sel e) hd
    have hx : (sel e).x j = 1 := by
      have h1 : (sel e).x j ≤ 1 := hf4 j
      have h2 : 1 ≤ (sel e).x j := by
        rw [hf3 j]
        apply Finset.card_pos.mpr
        exact ⟨i, by simpa using hmemZ⟩
      omega
    exact hce.2.1 j |>.2 hx
  · rw [if_neg h0]
    set t0 := replanTime sel e h with ht0
    set pre := h.drop (h.length - t0) with hpre
    have hlen : pre.length = t0 := by simp only [pre, List.length_drop]; omega
    have hrp : (stp sel).Reachable e pre := reach_drop sel e h _ hr
    obtain ⟨_, hVp, _, _⟩ := good_of_reachable sel e he hsel pre hrp
    have hval := econAt_valid e he pre hVp
    have hd := hsel (shiftEcon e pre) hval
    obtain ⟨hf1, hf2, hf3, hf4⟩ := hd.1
    have hce := hS1 (shiftEcon e pre) hval (sel (shiftEcon e pre)) hd
    have hz : curZ sel e h i = if hi : stateAt e pre i ≠ .gone then
        ((sel (shiftEcon e pre)).z ⟨i, hi⟩).map (shiftBack t0) else [] := by
      unfold curZ; rw [if_neg h0]
    rw [hz] at hmemZ
    by_cases hi : stateAt e pre i ≠ .gone
    · rw [dif_pos hi] at hmemZ
      obtain ⟨st0, hst0, hst0e⟩ := List.mem_map.mp hmemZ
      have h2 := congrArg Prod.snd hst0e
      simp only [shiftBack, Option.map_eq_some_iff] at h2
      obtain ⟨j0, hj0, hj0v⟩ := h2
      have htag := hf2 ⟨i, hi⟩ st0 hst0 j0 hj0
      have hx : (sel (shiftEcon e pre)).x j0 = 1 := by
        have h1 : (sel (shiftEcon e pre)).x j0 ≤ 1 := hf4 j0
        have h2 : 1 ≤ (sel (shiftEcon e pre)).x j0 := by
          rw [hf3 j0]
          apply Finset.card_pos.mpr
          refine ⟨⟨i, hi⟩, ?_⟩
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          have e2 : st0 = (st0.1, st0.2) := rfl
          rw [e2, htag, hj0] at hst0; exact hst0
        omega
      have key := hce.2.1 j0 |>.2 hx
      subst hj0v
      rw [stpPrice_inst _ _ (inferInstance) _ (inferInstance)]
      have hv : ((shiftEcon e pre).R j0).v = (e.R j0.1).v := rfl
      have htr : riderTrip ((shiftEcon e pre).R j0) = ((riderTrip (e.R j0.1)).1,
          (riderTrip (e.R j0.1)).2.1, (riderTrip (e.R j0.1)).2.2 - t0) := by
        simp only [riderTrip, shiftEcon, econAt, hlen]
      rw [htr, hv] at key
      exact key
    · rw [dif_neg hi] at hmemZ; simp at hmemZ

theorem tag_now_dispatched (he : e.Valid) (hsel : IsOptimalSelector sel) (h : Hist L ι κ)
    (hr : (stp sel).Reachable e h) (i : ι) (j : κ)
    (hmem : (riderTrip (e.R j), some j) ∈ curZ sel e h i) (hτ : (e.R j).τ = h.length) :
    stpDispatchVia sel e (replanTime sel e h) h i = .pick j := by
  obtain ⟨hle, _, _, hC⟩ := good_of_reachable sel e he hsel h hr
  obtain ⟨pre, zs, hz, hpre, hcs⟩ := hC i
  have hin : (riderTrip (e.R j), some j) ∈ zs := by
    rw [hz] at hmem
    rcases List.mem_append.mp hmem with h1 | h1
    · have := hpre _ h1; simp only [riderTrip] at this; omega
    · exact h1
  have hinv := stInv_stateAt e h i
  have hP1 := he.1.1
  revert hcs hinv
  rcases hs : stateAt e h i with ⟨β, a, τ⟩ | ⟨a, b, t', jj⟩ | _ <;> intro hcs hinv
  · simp only [StInv] at hinv
    simp only [ConsS] at hcs
    cases zs with
    | nil => simp at hin
    | cons st0 rest =>
      simp only [List.map_cons, Params.IsPathFrom] at hcs
      obtain ⟨h1, h2, h3, h4⟩ := hcs
      rcases List.mem_cons.mp hin with h5 | h5
      · -- the trip is the head
        subst h5
        simp only [riderTrip] at h2
        have hτ' : τ = h.length := by omega
        subst hτ'
        rw [disp_planAct sel e h i hle (by rw [hs]; simp [IsAvailAt]), hz]
        simp only [planAct]
        rw [find_pre_append _ _ _ hpre]
        simp [riderTrip, hτ]
      · have t1 := isPathFrom_times e.P _ _ rest h4 _ h5
        have t2 := hP1 a st0.1.2.1
        simp only [riderTrip] at t1
        omega
  · simp only [StInv] at hinv
    simp only [ConsS] at hcs
    have := isPathFrom_times e.P _ _ zs hcs _ hin
    simp only [riderTrip] at this
    omega
  · simp only [ConsS] at hcs
    rw [List.map_eq_nil_iff] at hcs
    subst hcs; simp at hin

theorem price_ge_value (hS1 : Step1CE L) (he : e.Valid) (hsel : IsOptimalSelector sel)
    (h : Hist L ι κ) (hr : (stp sel).Reachable e h) (j : κ) (hτ : (e.R j).τ = h.length)
    (hnd : ∀ i, stpDispatchVia sel e (replanTime sel e h) h i ≠ .pick j) :
    (e.R j).v ≤ stpPriceVia sel e h (riderTrip (e.R j)) := by
  obtain ⟨hle, _, _, _⟩ := good_of_reachable sel e he hsel h hr
  by_contra hlt
  push Not at hlt
  unfold stpPriceVia at hlt
  by_cases h0 : replanTime sel e h = 0
  · rw [if_pos h0] at hlt
    have hd := hsel e he
    obtain ⟨hf1, hf2, hf3, hf4⟩ := hd.1
    have hce := hS1 e he (sel e) hd
    have hx := (hce.2.1 j).1 hlt
    have h2 : 0 < (sel e).x j := by omega
    rw [hf3 j] at h2
    obtain ⟨i, hi⟩ := Finset.card_pos.mp h2
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
    have hz : curZ sel e h i = (sel e).z i := by simp [curZ, h0]
    exact hnd i (tag_now_dispatched sel e he hsel h hr i j (by rw [hz]; exact hi) hτ)
  · rw [if_neg h0] at hlt
    set t0 := replanTime sel e h with ht0
    set pre := h.drop (h.length - t0) with hpre
    have hlen : pre.length = t0 := by simp only [pre, List.length_drop]; omega
    have hrp : (stp sel).Reachable e pre := reach_drop sel e h _ hr
    obtain ⟨_, hVp, _, _⟩ := good_of_reachable sel e he hsel pre hrp
    have hval := econAt_valid e he pre hVp
    have hd := hsel (shiftEcon e pre) hval
    obtain ⟨hf1, hf2, hf3, hf4⟩ := hd.1
    have hce := hS1 (shiftEcon e pre) hval (sel (shiftEcon e pre)) hd
    have hj : pre.length ≤ (e.R j).τ := by omega
    set j0 : {j : κ // pre.length ≤ (e.R j).τ} := ⟨j, hj⟩
    have hv : ((shiftEcon e pre).R j0).v = (e.R j).v := rfl
    have htr : riderTrip ((shiftEcon e pre).R j0) = ((riderTrip (e.R j)).1,
        (riderTrip (e.R j)).2.1, (riderTrip (e.R j)).2.2 - t0) := by
      simp only [riderTrip, shiftEcon, econAt, hlen, j0]
    have hlt' : (shiftEcon e pre).stpPrice (riderTrip ((shiftEcon e pre).R j0)) <
        ((shiftEcon e pre).R j0).v := by
      rw [htr, hv, stpPrice_inst _ _ (inferInstance) _ (inferInstance)]; exact hlt
    have hx := (hce.2.1 j0).1 hlt'
    have h2 : 0 < (sel (shiftEcon e pre)).x j0 := by omega
    rw [hf3 j0] at h2
    obtain ⟨i0, hi0⟩ := Finset.card_pos.mp h2
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi0
    have hz : curZ sel e h i0.1 = ((sel (shiftEcon e pre)).z ⟨i0.1, i0.2⟩).map (shiftBack t0) := by
      unfold curZ; rw [if_neg h0, dif_pos i0.2]
    apply hnd i0.1
    apply tag_now_dispatched sel e he hsel h hr i0.1 j _ hτ
    rw [hz]
    refine List.mem_map.mpr ⟨_, hi0, ?_⟩
    rw [htr]
    simp only [shiftBack, riderTrip, Option.map_some, j0]
    congr 3
    omega

theorem rir_main (hS1 : Step1CE L) (he : e.Valid) (hsel : IsOptimalSelector sel) (σ : Strategy L ι κ)
    (hσ : (stp sel).AdmissibleProfile e σ) (j : κ) :
    (stp sel).riderCharge e σ [] j ≤ (riderPicked e σ [] j : ℝ) * (e.R j).v := by
  have hτT : (e.R j).τ < e.P.T := by
    have h1 := he.2.2.2 j
    have h2 := he.1.1 (e.R j).o (e.R j).d
    simp only [Params.IsTrip, riderTrip] at h1
    omega
  unfold DynMech.riderCharge riderPicked pickCount histAt
  simp only [List.length_nil, Nat.sub_zero]
  set H := playFrom σ [] (e.R j).τ
  have hHr : (stp sel).Reachable e H := reach_play sel e σ hσ _ (le_of_lt hτT)
  have hHT : H.length < e.P.T := by simp only [H]; rw [playFrom_length]; simpa using hτT
  show stpPriceVia sel e H (riderTrip (e.R j)) *
      ((Finset.univ.filter fun i => stpDispatchVia sel e (replanTime sel e H) H i = .pick j).card : ℝ) *
      _ ≤ _
  have hD := dispCount_le sel e he hsel H hHr j
  have hsub : (Finset.univ.filter fun i => IsAvailAt H.length (stateAt e H i) ∧
      σ i H = .pick j) ⊆
      (Finset.univ.filter fun i => stpDispatchVia sel e (replanTime sel e H) H i = .pick j) := by
    intro i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    intro hi
    exact (pick_dispatched sel e H i _ (hσ i H hHT) j hi.2).2
  have hle := Finset.card_le_card hsub
  rcases Nat.eq_zero_or_pos (Finset.univ.filter fun i => IsAvailAt H.length (stateAt e H i) ∧
      σ i H = .pick j).card with h0 | h0
  · rw [h0]; simp
  · have h1 : (Finset.univ.filter fun i =>
        stpDispatchVia sel e (replanTime sel e H) H i = .pick j).card = 1 := by omega
    have h2 : (Finset.univ.filter fun i => IsAvailAt H.length (stateAt e H i) ∧
        σ i H = .pick j).card = 1 := by omega
    obtain ⟨i, hi⟩ := Finset.card_pos.mp h0
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
    have hp := (pick_dispatched sel e H i _ (hσ i H hHT) j hi.2).2
    have := price_le_value sel e hS1 he hsel H hHr i j hp
    rw [h1, h2]; push_cast; linarith

end Global

/-- The milestone "Step 1 as used in Step 2" (continuation utility of an available driver). -/
def Step1Cont [Fintype L] (sel : Selector L) : Prop :=
  ∀ {ι κ : Type} [Fintype ι] [Fintype κ] (e : Econ L ι κ), e.Valid →
    ∀ (h : Hist L ι κ), (stp sel).Reachable e h → h.length < e.P.T →
      ∀ (i : ι) (β : Bool) (a : L), stateAt e h i = .wait β a h.length →
        (stp sel).contUtil e ((stp sel).sigmaStar e) h i =
          if β = true then
            PhiShift e (replanTime sel e h)
              (stateAt e (h.drop (h.length - replanTime sel e h))) a h.length
          else
            max (PhiShift e (replanTime sel e h)
              (stateAt e (h.drop (h.length - replanTime sel e h))) a h.length) 0

section Cont

variable [Fintype L] (sel : Selector L) {ι κ : Type} [Fintype ι] [Fintype κ] (e : Econ L ι κ)

omit [Fintype L] [Fintype ι] [Fintype κ] in
theorem playFrom_add (σ : Strategy L ι κ) (h : Hist L ι κ) (m : ℕ) :
    ∀ k, playFrom σ (playFrom σ h m) k = playFrom σ h (m + k)
  | 0 => rfl
  | k + 1 => by
    show (fun i => σ i (playFrom σ (playFrom σ h m) k)) :: playFrom σ (playFrom σ h m) k =
      (fun i => σ i (playFrom σ h (m + k))) :: playFrom σ h (m + k)
    rw [playFrom_add σ h m k]

omit [Fintype L] in
theorem utilNow_notAvail (h : Hist L ι κ) (i : ι) (α : DAction L κ)
    (hn : ¬ IsAvailAt h.length (stateAt e h i)) : (stp sel).utilNow e h i α = 0 := by
  unfold DynMech.utilNow DynMech.payNow costNow
  rw [if_neg (fun hc => hn hc.1)]
  revert hn
  cases stateAt e h i with
  | wait β a τ =>
    intro hn
    simp only [IsAvailAt] at hn
    cases α <;> simp [hn]
  | enroute => intro _; cases α <;> simp
  | gone => intro _; cases α <;> simp

omit [Fintype L] in
theorem contUtil_shift (σ : Strategy L ι κ) (h : Hist L ι κ) (i : ι) (m : ℕ)
    (hm : h.length + m ≤ e.P.T)
    (hz : ∀ k < m, (stp sel).utilNow e (playFrom σ h k) i (σ i (playFrom σ h k)) = 0) :
    (stp sel).contUtil e σ h i = (stp sel).contUtil e σ (playFrom σ h m) i := by
  unfold DynMech.contUtil
  rw [playFrom_length, show e.P.T - h.length = m + (e.P.T - (h.length + m)) by omega,
    Finset.sum_range_add]
  rw [Finset.sum_eq_zero (fun k hk => hz k (Finset.mem_range.mp hk)), zero_add]
  simp_rw [playFrom_add]

omit [Fintype L] in
theorem dispatch_mem_actions (h : Hist L ι κ) (i : ι) :
    (stp sel).dispatch e h i ∈ (stp sel).actions e h i := by
  unfold DynMech.dispatch DynMech.actions
  revert ‹Fintype ι›
  intro _
  rcases hs : stateAt e h i with ⟨β, a, τ⟩ | _ | _
  · by_cases hτ : τ = h.length
    · simp only [IsAvailAt, hτ, if_true]
      left; left; rfl
    · simp [IsAvailAt, hτ]
  · simp [IsAvailAt]
  · simp [IsAvailAt]

omit [Fintype L] in
theorem reach_star (h : Hist L ι κ) (hr : (stp sel).Reachable e h) :
    ∀ k, h.length + k ≤ e.P.T → (stp sel).Reachable e (playFrom ((stp sel).sigmaStar e) h k)
  | 0, _ => hr
  | k + 1, hk => by
    refine ⟨reach_star h hr k (by omega), ?_, ?_⟩
    · rw [playFrom_length]; omega
    · intro i; exact dispatch_mem_actions sel e _ i

omit [Fintype L] [Fintype ι] [Fintype κ] in
theorem wait_stays (σ : Strategy L ι κ) (h : Hist L ι κ) (i : ι) (β : Bool) (a : L) (τ : ℕ)
    (hs : stateAt e h i = .wait β a τ) :
    ∀ k, h.length + k ≤ τ → stateAt e (playFrom σ h k) i = .wait β a τ
  | 0, _ => by simpa [playFrom] using hs
  | k + 1, hk => by
    show step e.P e.R (playFrom σ h k).length (stateAt e (playFrom σ h k) i) _ = _
    rw [wait_stays σ h i β a τ hs k (by omega), playFrom_length]
    simp only [step]
    rw [if_neg (by omega)]

omit [Fintype L] [Fintype ι] [Fintype κ] in
theorem gone_stays (σ : Strategy L ι κ) (h : Hist L ι κ) (i : ι)
    (hs : stateAt e h i = .gone) : ∀ k, stateAt e (playFrom σ h k) i = .gone
  | 0 => by simpa [playFrom] using hs
  | k + 1 => by
    show step e.P e.R (playFrom σ h k).length (stateAt e (playFrom σ h k) i) _ = _
    rw [gone_stays σ h i hs k]
    rfl

omit [Fintype L] [Fintype ι] [Fintype κ] in
theorem enroute_stays (σ : Strategy L ι κ) (h : Hist L ι κ) (i : ι) (a b : L) (t' : ℕ)
    (j : Option κ) (hs : stateAt e h i = .enroute a b t' j) :
    ∀ k, h.length + k < t' + e.P.δ a b → stateAt e (playFrom σ h k) i = .enroute a b t' j
  | 0, _ => by simpa [playFrom] using hs
  | k + 1, hk => by
    show step e.P e.R (playFrom σ h k).length (stateAt e (playFrom σ h k) i) _ = _
    rw [enroute_stays σ h i a b t' j hs k (by omega), playFrom_length]
    simp only [step]
    rw [if_neg (by omega)]

omit [Fintype L] [Fintype ι] [Fintype κ] in
theorem enroute_arrive (σ : Strategy L ι κ) (h : Hist L ι κ) (i : ι) (a b : L) (t' : ℕ)
    (j : Option κ) (hs : stateAt e h i = .enroute a b t' j) (hlt : h.length < t' + e.P.δ a b) :
    stateAt e (playFrom σ h (t' + e.P.δ a b - h.length)) i = .wait true b (t' + e.P.δ a b) := by
  obtain ⟨m, hm⟩ : ∃ m, t' + e.P.δ a b - h.length = m + 1 := ⟨t' + e.P.δ a b - h.length - 1, by omega⟩
  rw [hm]
  show step e.P e.R (playFrom σ h m).length (stateAt e (playFrom σ h m) i) _ = _
  rw [enroute_stays e σ h i a b t' j hs m (by omega), playFrom_length]
  simp only [step]
  rw [if_pos (by omega), show h.length + m + 1 = t' + e.P.δ a b by omega]

/-- Continuation utility of a driver who next becomes available at time `u` in state
`(β, a, u)`, computed at that time. -/
theorem cont_arrival (hS : Step1Cont sel) (he : e.Valid) (h : Hist L ι κ)
    (hr : (stp sel).Reachable e h) (i : ι) (u : ℕ) (β : Bool) (a : L)
    (hu1 : h.length ≤ u) (hu2 : u ≤ e.P.T)
    (hz : ∀ k < u - h.length, ¬ IsAvailAt (playFrom ((stp sel).sigmaStar e) h k).length
      (stateAt e (playFrom ((stp sel).sigmaStar e) h k) i))
    (hs : stateAt e (playFrom ((stp sel).sigmaStar e) h (u - h.length)) i = .wait β a u) :
    (stp sel).contUtil e ((stp sel).sigmaStar e) h i =
      if u < e.P.T then
        (if β = true then
          PhiShift e (replanTime sel e (playFrom ((stp sel).sigmaStar e) h (u - h.length)))
            (stateAt e ((playFrom ((stp sel).sigmaStar e) h (u - h.length)).drop
              ((playFrom ((stp sel).sigmaStar e) h (u - h.length)).length -
                replanTime sel e (playFrom ((stp sel).sigmaStar e) h (u - h.length))))) a
            (playFrom ((stp sel).sigmaStar e) h (u - h.length)).length
        else
          max (PhiShift e (replanTime sel e (playFrom ((stp sel).sigmaStar e) h (u - h.length)))
            (stateAt e ((playFrom ((stp sel).sigmaStar e) h (u - h.length)).drop
              ((playFrom ((stp sel).sigmaStar e) h (u - h.length)).length -
                replanTime sel e (playFrom ((stp sel).sigmaStar e) h (u - h.length))))) a
            (playFrom ((stp sel).sigmaStar e) h (u - h.length)).length) 0)
      else 0 := by
  have hlen : (playFrom ((stp sel).sigmaStar e) h (u - h.length)).length = u := by
    rw [playFrom_length]; omega
  rw [contUtil_shift sel e _ h i (u - h.length) (by omega)
    (fun k hk => utilNow_notAvail sel e _ i _ (hz k hk))]
  by_cases hT : u < e.P.T
  · rw [if_pos hT]
    have hr' := reach_star sel e h hr (u - h.length) (by omega)
    rw [hS e he _ hr' (by rw [hlen]; exact hT) i β a (by rw [hlen]; exact hs)]
  · rw [if_neg hT]
    unfold DynMech.contUtil
    rw [hlen, show e.P.T - u = 0 by omega]
    simp

omit [Fintype L] in
theorem replanTime_star (h : Hist L ι κ) :
    replanTime sel e ((fun i => (stp sel).sigmaStar e i h) :: h) = replanTime sel e h := by
  simp only [replanTime]
  rw [if_neg]
  push Not
  intro i
  exact dispatch_eq sel e h i

omit [Fintype L] in
theorem H_facts (h' : Hist L ι κ) (hrt : replanTime sel e h' = h'.length) :
    ∀ k, replanTime sel e (playFrom ((stp sel).sigmaStar e) h' k) = h'.length ∧
      (playFrom ((stp sel).sigmaStar e) h' k).drop
        ((playFrom ((stp sel).sigmaStar e) h' k).length - h'.length) = h'
  | 0 => by simp [playFrom, hrt]
  | k + 1 => by
    obtain ⟨h1, h2⟩ := H_facts h' hrt k
    refine ⟨?_, ?_⟩
    · simp only [playFrom]; rw [replanTime_star, h1]
    · simp only [playFrom, List.length_cons, playFrom_length]
      rw [show h'.length + k + 1 - h'.length = k + 1 by omega, List.drop_succ_cons]
      rw [playFrom_length] at h2
      rwa [show h'.length + k - h'.length = k by omega] at h2

omit [Fintype L] in
theorem contUtil_succ (σ : Strategy L ι κ) (h : Hist L ι κ) (i : ι) (hT : h.length < e.P.T) :
    (stp sel).contUtil e σ h i =
      (stp sel).utilNow e h i (σ i h) + (stp sel).contUtil e σ ((fun k => σ k h) :: h) i := by
  unfold DynMech.contUtil
  rw [show e.P.T - h.length = (e.P.T - (h.length + 1)) + 1 by omega, Finset.sum_range_succ']
  rw [add_comm]
  congr 1
  simp only [List.length_cons]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [show k + 1 = 1 + k by omega, ← playFrom_add]
  rfl

omit [Fintype L] in
theorem contUtil_gone_any (σ : Strategy L ι κ) (h : Hist L ι κ) (hT : h.length ≤ e.P.T) (i : ι)
    (hs : stateAt e h i = .gone) : (stp sel).contUtil e σ h i = 0 := by
  rw [contUtil_shift sel e σ h i (e.P.T - h.length) (by omega) (fun k _ => utilNow_notAvail sel e _ i _
    (by rw [gone_stays e σ h i hs k]; simp [IsAvailAt]))]
  unfold DynMech.contUtil
  rw [playFrom_length, show e.P.T - (h.length + (e.P.T - h.length)) = 0 by omega]
  simp

omit [Fintype L] in
theorem replanTime_dev' (α : ι → DAction L κ) (h : Hist L ι κ) (i : ι)
    (hdev : α i ≠ stpDispatchVia sel e (replanTime sel e h) h i) :
    replanTime sel e (α :: h) = h.length + 1 := by
  simp only [replanTime]
  rw [if_pos ⟨i, hdev⟩]

omit [Fintype L] [Fintype ι] [Fintype κ] in
theorem isPathFrom_lt_T {κ0 : Type} (P : Params L) (hP : ∀ a b, 1 ≤ P.δ a b) :
    ∀ (a : L) (t : ℕ) (zs : List (Trip L × Option κ0)), P.IsPathFrom a t (zs.map Prod.fst) →
      ∀ st ∈ zs, st.1.2.2 < P.T
  | _, _, [], _ => by simp
  | a, t, z :: zs, h => by
    simp only [List.map_cons, Params.IsPathFrom] at h
    obtain ⟨h1, h2, h3, h4⟩ := h
    intro st hst
    rcases List.mem_cons.mp hst with rfl | hst
    · have := hP a st.1.2.1; omega
    · exact isPathFrom_lt_T P hP _ _ zs h4 st hst

/-- Times of the remaining part of a plan path are at least the driver's next availability. -/
theorem consS_times (P : Params L) (u : ℕ) (s : DState L κ) (zs : List (Trip L × Option κ))
    (hinv : StInv P u s) (hc : ConsS P s (zs.map Prod.fst)) :
    ∀ st ∈ zs, u ≤ st.1.2.2 ∧ (¬ IsAvailAt u s → u + 1 ≤ st.1.2.2) := by
  intro st hst
  cases s with
  | wait β a τ =>
    simp only [StInv] at hinv
    simp only [ConsS] at hc
    have := isPathFrom_times P _ _ zs hc st hst
    refine ⟨by omega, fun hn => ?_⟩
    simp only [IsAvailAt] at hn; omega
  | enroute a b t' jj =>
    simp only [StInv] at hinv
    simp only [ConsS] at hc
    have := isPathFrom_times P _ _ zs hc st hst
    exact ⟨by omega, fun _ => by omega⟩
  | gone =>
    simp only [ConsS] at hc
    rw [List.map_eq_nil_iff] at hc; subst hc; simp at hst

theorem curZ_star (he : e.Valid) (hsel : IsOptimalSelector sel) (h : Hist L ι κ)
    (hr : (stp sel).Reachable e h) :
    ∀ k, h.length + k ≤ e.P.T →
      curZ sel e (playFrom ((stp sel).sigmaStar e) h k) = curZ sel e h
  | 0, _ => rfl
  | k + 1, hk => by
    have hrk := reach_star sel e h hr k (by omega)
    have hle := (good_of_reachable sel e he hsel _ hrk).1
    show curZ sel e ((fun i => (stp sel).sigmaStar e i (playFrom ((stp sel).sigmaStar e) h k)) ::
      playFrom ((stp sel).sigmaStar e) h k) = _
    have h1 := (curZ_noDev sel e _ _ hle (fun i => dispatch_eq sel e _ i)).2
    exact h1.trans (curZ_star he hsel h hr k (by omega))

/-- One step of the simulation: the trip taken now under `σ*` is the first remaining planned trip
starting now. -/
theorem step_filter (he : e.Valid) (hsel : IsOptimalSelector sel) (H : Hist L ι κ)
    (hr : (stp sel).Reachable e H) (hT : H.length < e.P.T) (i : ι) :
    (curZ sel e H i).filter (fun st => decide (H.length ≤ st.1.2.2)) =
      (stepTrip e.R H.length (stateAt e H i) ((stp sel).sigmaStar e i H)).toList ++
      (curZ sel e H i).filter (fun st => decide (H.length + 1 ≤ st.1.2.2)) := by
  obtain ⟨hle, _, ⟨hok1, _⟩, hC⟩ := good_of_reachable sel e he hsel H hr
  obtain ⟨pre, zs, hz, hpre, hcs⟩ := hC i
  have hinv := stInv_stateAt e H i
  have htimes := consS_times e.P H.length _ zs hinv hcs
  have hf1 : (curZ sel e H i).filter (fun st => decide (H.length ≤ st.1.2.2)) = zs := by
    rw [hz, List.filter_append, List.filter_eq_nil_iff.mpr, List.filter_eq_self.mpr]
    · simp
    · intro st hst; simpa using (htimes st hst).1
    · intro st hst; have := hpre st hst; simp; omega
  have hf2 : (curZ sel e H i).filter (fun st => decide (H.length + 1 ≤ st.1.2.2)) =
      zs.filter (fun st => decide (H.length + 1 ≤ st.1.2.2)) := by
    rw [hz, List.filter_append, List.filter_eq_nil_iff.mpr]
    · simp
    · intro st hst; have := hpre st hst; simp; omega
  rw [hf1, hf2]
  have hσ : (stp sel).sigmaStar e i H = (stp sel).dispatch e H i := rfl
  rw [hσ, dispatch_eq]
  by_cases ha : IsAvailAt H.length (stateAt e H i)
  · obtain ⟨β, a, hs⟩ := avail_wait _ _ ha
    rw [disp_planAct sel e H i hle ha, hs]
    rw [hs] at hcs
    simp only [ConsS] at hcs
    have hfeas := hok1 i
    rw [hz] at hfeas
    cases zs with
    | nil =>
      have : planAct (curZ sel e H i) H.length = .quit := by
        rw [hz]; simp only [planAct, List.append_nil]
        rw [List.find?_eq_none.mpr]
        intro st hst; have := hpre st hst; simp only [decide_eq_true_eq]; omega
      rw [this]; simp [stepTrip]
    | cons st rest =>
      obtain ⟨⟨a', b, t'⟩, tag⟩ := st
      have hcs' := hcs
      simp only [List.map_cons, Params.IsPathFrom] at hcs
      obtain ⟨h1, h2, h3, h4⟩ := hcs
      subst a' t'
      have hrest := isPathFrom_times e.P _ _ rest h4
      have hδ := he.1.1 a b
      have hfr : (((a, b, H.length), tag) :: rest).filter
          (fun st => decide (H.length + 1 ≤ st.1.2.2)) = rest := by
        rw [List.filter_cons_of_neg (by simp), List.filter_eq_self.mpr]
        intro st hst; have := hrest st hst; simp; omega
      rw [hfr]
      have hfind : planAct (curZ sel e H i) H.length =
          (match tag with | none => .move b | some j => .pick j) := by
        rw [hz]; simp only [planAct]
        rw [find_pre_append _ _ _ hpre]
        cases tag <;> simp
      rw [hfind]
      cases tag with
      | none => simp [stepTrip]
      | some j =>
        have hj := hfeas ((a, b, H.length), some j) (by simp) j rfl
        simp only [riderTrip, Prod.mk.injEq] at hj
        simp only [stepTrip, if_true, Option.toList_some, List.singleton_append]
        rw [hj.2.1]
  · rw [stpDispatchVia_notAvail sel e _ _ _ ha]
    have : stepTrip e.R H.length (stateAt e H i) .cont = none := by
      cases stateAt e H i <;> rfl
    rw [this]
    simp only [Option.toList_none, List.nil_append]
    symm
    rw [List.filter_eq_self.mpr]
    intro st hst; have := (htimes st hst).2 ha; simp; omega

/-- The trips a driver takes under `σ*` from a reachable history are exactly the planned trips
starting from now on. -/
theorem outTrips_star (he : e.Valid) (hsel : IsOptimalSelector sel) (h : Hist L ι κ)
    (hr : (stp sel).Reachable e h) (hT : h.length ≤ e.P.T) (i : ι) :
    outTrips e ((stp sel).sigmaStar e) h i =
      (curZ sel e h i).filter (fun st => decide (h.length ≤ st.1.2.2)) := by
  have key : ∀ n, h.length + n ≤ e.P.T →
      ((List.range n).filterMap fun k => stepTrip e.R (playFrom ((stp sel).sigmaStar e) h k).length
        (stateAt e (playFrom ((stp sel).sigmaStar e) h k) i)
        ((stp sel).sigmaStar e i (playFrom ((stp sel).sigmaStar e) h k))) ++
        (curZ sel e h i).filter (fun st => decide (h.length + n ≤ st.1.2.2)) =
      (curZ sel e h i).filter (fun st => decide (h.length ≤ st.1.2.2)) := by
    intro n
    induction n with
    | zero => intro _; simp
    | succ n ih =>
      intro hn
      have hrn := reach_star sel e h hr n (by omega)
      have hlen := playFrom_length ((stp sel).sigmaStar e) h n
      have hs := step_filter sel e he hsel _ hrn (by rw [hlen]; omega) i
      rw [curZ_star sel e he hsel h hr n (by omega), hlen] at hs
      have step : ([n].filterMap fun k => stepTrip e.R (playFrom ((stp sel).sigmaStar e) h k).length
          (stateAt e (playFrom ((stp sel).sigmaStar e) h k) i)
          ((stp sel).sigmaStar e i (playFrom ((stp sel).sigmaStar e) h k))) ++
          (curZ sel e h i).filter (fun st => decide (h.length + (n + 1) ≤ st.1.2.2)) =
          (curZ sel e h i).filter (fun st => decide (h.length + n ≤ st.1.2.2)) := by
        rw [hs]
        simp only [List.filterMap_cons, List.filterMap_nil, hlen]
        split <;> rename_i x hx <;> simp [hx] <;> rfl
      rw [List.range_succ, List.filterMap_append, List.append_assoc, step, ih (by omega)]
  have := key (e.P.T - h.length) (by omega)
  rw [show h.length + (e.P.T - h.length) = e.P.T by omega] at this
  have hnil : (curZ sel e h i).filter (fun st => decide (e.P.T ≤ st.1.2.2)) = [] := by
    obtain ⟨_, _, _, hC⟩ := good_of_reachable sel e he hsel h hr
    obtain ⟨pre, zs, hz, hpre, hcs⟩ := hC i
    rw [List.filter_eq_nil_iff, hz]
    intro st hst
    rcases List.mem_append.mp hst with h1 | h1
    · have := hpre st h1; simp; omega
    · have hinv := stInv_stateAt e h i
      simp only [decide_eq_true_eq, not_le]
      revert hcs hinv
      cases stateAt e h i with
      | wait β a τ =>
        intro hcs _
        exact isPathFrom_lt_T e.P he.1.1 _ _ zs hcs st h1
      | enroute a b t' jj =>
        intro hcs _
        exact isPathFrom_lt_T e.P he.1.1 _ _ zs hcs st h1
      | gone =>
        intro hcs _
        simp only [ConsS, List.map_eq_nil_iff] at hcs; subst hcs; simp at h1
  rw [hnil, List.append_nil] at this
  exact this

end Cont

section WLemma

variable [Fintype L] (sel : Selector L)

theorem W_eq {ι κ : Type} [Fintype ι] [Fintype κ] (e : Econ L ι κ) (hsel : IsOptimalSelector sel)
    (he : e.Valid) : W e = (sel e).welfare := by
  have hd := hsel e he
  have hg : IsGreatest {w : ℝ | ∃ d : Dispatch e, d.Feasible ∧ d.welfare = w} (sel e).welfare :=
    ⟨⟨sel e, hd.1, rfl⟩, by rintro w ⟨d, hdf, rfl⟩; exact hd.2 d hdf⟩
  exact hg.csSup_eq

theorem addDriver_valid {ι κ : Type} (e : Econ L ι κ) (he : e.Valid) (θ : DType L)
    (hθ : θ.τ ≤ e.P.T) : (e.addDriver θ).Valid := by
  obtain ⟨hP, hD, hRv, hRt⟩ := he
  refine ⟨hP, ?_, hRv, hRt⟩
  intro o
  cases o with
  | none => exact hθ
  | some i => exact hD i

/-- Adding a driver who takes the empty path loses at most her empty-path cost. -/
theorem W_addDriver_ge {ι κ : Type} [Fintype ι] [Fintype κ] (e : Econ L ι κ)
    (hsel : IsOptimalSelector sel) (he : e.Valid) (θ : DType L) (hθ : θ.τ ≤ e.P.T) :
    W e - e.P.pathCost θ [] ≤ W (e.addDriver θ) := by
  have hva := addDriver_valid e he θ hθ
  rw [W_eq sel e hsel he]
  obtain ⟨hf1, hf2, hf3, hf4⟩ := (hsel e he).1
  let d' : Dispatch (e.addDriver θ) := ⟨(sel e).x, fun o => o.elim [] (sel e).z⟩
  have hfeas : d'.Feasible := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro o
      cases o with
      | none => simp [Dispatch.path, d', Params.IsPathFrom]
      | some i => exact hf1 i
    · intro o st hst j hj
      cases o with
      | none => simp [d'] at hst
      | some i => exact hf2 i st hst j hj
    · intro j
      rw [hf3 j]
      rw [← Finset.card_map Function.Embedding.some]
      congr 1
      ext o
      cases o with
      | none => simp [d']
      | some i => simp [d']; rfl
    · intro j; exact hf4 j
  have hle : d'.welfare ≤ W (e.addDriver θ) := by
    rw [W_eq sel _ hsel hva]
    exact (hsel _ hva).2 d' hfeas
  have hw : d'.welfare = (sel e).welfare - e.P.pathCost θ [] := by
    simp only [Dispatch.welfare, Dispatch.cost, Dispatch.path, Fintype.sum_option]
    simp [d', Econ.addDriver]
    ring
  linarith

theorem PhiAt_ge {ι κ : Type} [Fintype ι] [Fintype κ] (e : Econ L ι κ)
    (hsel : IsOptimalSelector sel) (he : e.Valid) (a : L) (τ : ℕ) (hτ : τ ≤ e.P.T) :
    -e.P.κ (e.P.T - τ) ≤ PhiAt e a τ := by
  have := W_addDriver_ge sel e hsel he ⟨true, a, τ⟩ hτ
  simp only [Params.pathCost, Params.pathEnd] at this
  unfold PhiAt
  simp at this
  linarith

end WLemma


end BBAux

end STPRideshare.Mechanism



namespace STPRideshare.Mechanism

open scoped Classical

namespace BBAux

open StaticAux

section WO

variable {L : Type} [Fintype L] (sel : Selector L) {ι κ : Type} [Fintype ι] [Fintype κ]
  (e : Econ L ι κ)

/-- Decomposition of the current plan at a reachable history (from the strengthened invariant). -/
theorem plan_split (he : e.Valid) (hsel : IsOptimalSelector sel) (h : Hist L ι κ)
    (hr : (stp sel).Reachable e h) (i : ι) :
    ∃ pre zs, curZ sel e h i = pre ++ zs ∧ (∀ st ∈ pre, st.1.2.2 < h.length) ∧
      ConsS e.P (stateAt e h i) (zs.map Prod.fst) ∧
      zs = (curZ sel e h i).filter (fun st => decide (h.length ≤ st.1.2.2)) := by
  obtain ⟨_, _, _, hC⟩ := good_of_reachable sel e he hsel h hr
  obtain ⟨pre, zs, hz, hpre, hcs⟩ := hC i
  refine ⟨pre, zs, hz, hpre, hcs, ?_⟩
  have htimes := consS_times e.P h.length _ zs (stInv_stateAt e h i) hcs
  rw [hz, List.filter_append, List.filter_eq_nil_iff.mpr, List.filter_eq_self.mpr]
  · simp
  · intro st hst; simpa using (htimes st hst).1
  · intro st hst; have := hpre st hst; simp; omega

theorem shiftRel_E1 (h : Hist L ι κ) (hT : h.length ≤ e.P.T) :
    ShiftRel e.P (shiftEcon e h).P h.length := by
  refine ⟨rfl, ?_, fun a b u => rfl, rfl⟩
  show e.P.T - h.length + h.length = e.P.T
  omega

/-- Membership of a rider trip in the remaining plan of a driver iff she picks the rider up
under `σ*`. -/
theorem tag_iff_picked (he : e.Valid) (hsel : IsOptimalSelector sel) (h : Hist L ι κ)
    (hr : (stp sel).Reachable e h) (j : κ) (hj : h.length ≤ (e.R j).τ) (i : ι) :
    (IsAvailAt (playFrom ((stp sel).sigmaStar e) h ((e.R j).τ - h.length)).length
        (stateAt e (playFrom ((stp sel).sigmaStar e) h ((e.R j).τ - h.length)) i) ∧
      (stp sel).sigmaStar e i (playFrom ((stp sel).sigmaStar e) h ((e.R j).τ - h.length)) =
        .pick j) ↔
    (riderTrip (e.R j), some j) ∈ curZ sel e h i := by
  have hτT : (e.R j).τ < e.P.T := by
    have h1 := he.2.2.2 j
    have h2 := he.1.1 (e.R j).o (e.R j).d
    simp only [Params.IsTrip, riderTrip] at h1
    omega
  set H := playFrom ((stp sel).sigmaStar e) h ((e.R j).τ - h.length)
  have hHr : (stp sel).Reachable e H := reach_star sel e h hr _ (by omega)
  have hlen : H.length = (e.R j).τ := by simp only [H]; rw [playFrom_length]; omega
  have hz : curZ sel e H = curZ sel e h := curZ_star sel e he hsel h hr _ (by omega)
  constructor
  · rintro ⟨ha, hp⟩
    have hp' : stpDispatchVia sel e (replanTime sel e H) H i = .pick j := by
      rw [← dispatch_eq]; exact hp
    have := (pick_facts sel e he hsel H hHr i j hp').2.2
    rwa [hz] at this
  · intro hm
    have hd := tag_now_dispatched sel e he hsel H hHr i j (by rw [hz]; exact hm) hlen.symm
    refine ⟨?_, ?_⟩
    · by_contra ha
      rw [stpDispatchVia_notAvail sel e _ _ _ ha] at hd; cases hd
    · show (stp sel).dispatch e H i = _
      rw [dispatch_eq]; exact hd

omit [Fintype L] in
theorem consS_shiftType_down (P : Params L) (t : ℕ) (s : DState L κ) (hs : s ≠ .gone)
    (l : List (Trip L)) (hc : ConsS P s l) (hinv : StInv P t s) :
    P.IsPathFrom (shiftType P t s hs).ℓ ((shiftType P t s hs).τ + t) l := by
  cases s with
  | wait β a τ =>
    simp only [StInv] at hinv
    simp only [ConsS] at hc
    simp only [shiftType]; rwa [Nat.sub_add_cancel hinv]
  | enroute a b t' j =>
    simp only [StInv] at hinv
    simp only [ConsS] at hc
    simp only [shiftType]; rwa [Nat.sub_add_cancel (by omega)]
  | gone => exact absurd rfl hs

theorem tripUp_shiftTrip (t : ℕ) (st : Trip L × Option κ) (ht : t ≤ st.1.2.2) :
    tripUp t (shiftTrip e t st).1 = st.1 := by
  obtain ⟨⟨a, b, u⟩, o⟩ := st
  simp only [tripUp, shiftTrip, Prod.mk.injEq, true_and]
  simp at ht; omega

theorem mem_d1 (he : e.Valid) (hsel : IsOptimalSelector sel) (h : Hist L ι κ)
    (hr : (stp sel).Reachable e h) (hT : h.length ≤ e.P.T) (i1 : {i // stateAt e h i ≠ .gone})
    (j1 : {j // h.length ≤ (e.R j).τ}) :
    (riderTrip ((shiftEcon e h).R j1), some j1) ∈ ((stp sel).contPlan e h).toDispatch.z i1 ↔
      (riderTrip (e.R j1.1), some j1.1) ∈ curZ sel e h i1.1 := by
  obtain ⟨_, _, ⟨hok1, _⟩, _⟩ := good_of_reachable sel e he hsel h hr
  obtain ⟨pre, zs, hz, hpre, hcs, hzs⟩ := plan_split sel e he hsel h hr i1.1
  show _ ∈ (outTrips e ((stp sel).sigmaStar e) h i1.1).map (shiftTrip e h.length) ↔ _
  rw [outTrips_star sel e he hsel h hr hT, ← hzs]
  constructor
  · intro hm
    obtain ⟨st, hst, hst'⟩ := List.mem_map.mp hm
    have h2 := congrArg Prod.snd hst'
    simp only [shiftTrip, Option.bind_eq_some_iff] at h2
    obtain ⟨j, hj, hj'⟩ := h2
    split_ifs at hj' with hjj
    simp only [Option.some.injEq] at hj'
    subst hj'
    have := hok1 i1.1 st (by rw [hz]; exact List.mem_append_right _ hst) j hj
    have e2 : st = (st.1, st.2) := rfl
    rw [hz]; apply List.mem_append_right
    rw [e2, this, hj] at hst; exact hst
  · intro hm
    have hin : (riderTrip (e.R j1.1), some j1.1) ∈ zs := by
      rw [hzs, List.mem_filter]
      exact ⟨hm, decide_eq_true j1.2⟩
    refine List.mem_map.mpr ⟨_, hin, ?_⟩
    simp only [shiftTrip, riderTrip, Option.bind_some, dif_pos j1.2]
    rfl

theorem d1_feasible (he : e.Valid) (hsel : IsOptimalSelector sel) (h : Hist L ι κ)
    (hr : (stp sel).Reachable e h) (hT : h.length ≤ e.P.T) :
    ((stp sel).contPlan e h).toDispatch.Feasible ∧
    ∀ j1 : {j // h.length ≤ (e.R j).τ}, ((stp sel).contPlan e h).toDispatch.x j1 =
      (Finset.univ.filter fun i => (riderTrip (e.R j1.1), some j1.1) ∈ curZ sel e h i).card := by
  obtain ⟨_, _, ⟨hok1, hok2⟩, _⟩ := good_of_reachable sel e he hsel h hr
  have hx : ∀ j1 : {j // h.length ≤ (e.R j).τ}, ((stp sel).contPlan e h).toDispatch.x j1 =
      (Finset.univ.filter fun i => (riderTrip (e.R j1.1), some j1.1) ∈ curZ sel e h i).card := by
    intro j1
    show pickCount e _ _ j1.1 = _
    unfold pickCount histAt
    congr 1
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact tag_iff_picked sel e he hsel h hr j1.1 j1.2 i
  refine ⟨⟨?_, ?_, ?_, ?_⟩, hx⟩
  · intro i1
    obtain ⟨pre, zs, hz, hpre, hcs, hzs⟩ := plan_split sel e he hsel h hr i1.1
    apply isPathFrom_down (shiftRel_E1 e h hT)
    show e.P.IsPathFrom _ _ ((((outTrips e ((stp sel).sigmaStar e) h i1.1).map
      (shiftTrip e h.length)).map Prod.fst).map (tripUp h.length))
    rw [outTrips_star sel e he hsel h hr hT, ← hzs]
    have hmap : ((zs.map (shiftTrip e h.length)).map Prod.fst).map (tripUp h.length) =
        zs.map Prod.fst := by
      simp only [List.map_map]
      apply List.map_congr_left
      intro st hst
      have := (consS_times e.P h.length _ zs (stInv_stateAt e h i1.1) hcs st hst).1
      exact tripUp_shiftTrip e h.length st this
    rw [hmap]
    exact consS_shiftType_down e.P h.length _ i1.2 _ hcs (stInv_stateAt e h i1.1)
  · intro i1 st1 hst1 j1 hj1
    obtain ⟨pre, zs, hz, hpre, hcs, hzs⟩ := plan_split sel e he hsel h hr i1.1
    change st1 ∈ (outTrips e ((stp sel).sigmaStar e) h i1.1).map (shiftTrip e h.length) at hst1
    rw [outTrips_star sel e he hsel h hr hT, ← hzs] at hst1
    obtain ⟨st, hst, rfl⟩ := List.mem_map.mp hst1
    simp only [shiftTrip, Option.bind_eq_some_iff] at hj1
    obtain ⟨j, hj, hj'⟩ := hj1
    split_ifs at hj' with hjj
    simp only [Option.some.injEq] at hj'
    subst hj'
    have := hok1 i1.1 st (by rw [hz]; exact List.mem_append_right _ hst) j hj
    simp only [shiftTrip, this, riderTrip, shiftEcon, econAt]
  · intro j1
    rw [hx j1]
    rw [card_sub (Q := fun i => stateAt e h i ≠ .gone) _ (fun i hi => by
      intro hg
      obtain ⟨pre, zs, hz, hpre, hcs, hzs⟩ := plan_split sel e he hsel h hr i
      rw [hg] at hcs
      simp only [ConsS, List.map_eq_nil_iff] at hcs
      subst hcs
      rw [hz, List.append_nil] at hi
      have := hpre _ hi
      have := j1.2
      simp only [riderTrip] at *; omega)]
    congr 1
    ext i1
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact (mem_d1 sel e he hsel h hr hT i1 j1).symm
  · intro j1
    rw [hx j1]; exact hok2 j1.1

/-- How the type of a driver in the planning economy `E0` relates to her state at planning time. -/
def DMatch {κ0 : Type} (P : Params L) (t0 : ℕ) (s : DState L κ0) (θ : DType L) : Prop :=
  match s with
  | .wait β a τ => θ = ⟨β, a, τ - t0⟩
  | .enroute a b t' _ => θ = ⟨true, b, t' + P.δ a b - t0⟩
  | .gone => False

omit [Fintype L] [Fintype ι] [Fintype κ] in
theorem gone_drop (h : Hist L ι κ) (i : ι) :
    ∀ n, stateAt e (h.drop n) i = .gone → stateAt e h i = .gone := by
  induction h with
  | nil => intro n hn; simpa using hn
  | cons α h ih =>
    intro n hn
    cases n with
    | zero => simpa using hn
    | succ n =>
      simp only [List.drop_succ_cons] at hn
      show step e.P e.R h.length (stateAt e h i) (α i) = .gone
      rw [ih n hn]; rfl

theorem dispatch_ext {ι0 κ0 : Type} {E0 : Econ L ι0 κ0} (d d' : Dispatch E0) (hx : d.x = d'.x)
    (hz : d.z = d'.z) : d = d' := by
  rcases d with ⟨x, z⟩; rcases d' with ⟨x', z'⟩
  simp only at hx hz; subst hx hz; rfl

omit [Fintype L] [Fintype ι] [Fintype κ] in
theorem pos_lemma (P : Params L) (t t0 : ℕ) (ht0 : t0 ≤ t) (s : DState L κ) (hs : s ≠ .gone)
    (hinvt : StInv P t s) (a0 : L) (τ0 : ℕ) (β0 : Bool) (pre : List (Trip L))
    (hpos : PosOK P a0 τ0 β0 pre s) :
    (shiftType P t s hs).ℓ = (P.pathEnd a0 τ0 pre).1 ∧
      (shiftType P t s hs).τ + (t - t0) = (P.pathEnd a0 τ0 pre).2 - t0 ∧
      (pre = [] → (shiftType P t s hs).β = β0) ∧ (pre ≠ [] → (shiftType P t s hs).β = true) := by
  cases s with
  | wait β a τ =>
    simp only [PosOK] at hpos
    simp only [StInv] at hinvt
    obtain ⟨h1, h2, h3⟩ := hpos
    rw [h1]
    simp only [shiftType]
    exact ⟨trivial, by omega, h2, h3⟩
  | enroute a b t' jj =>
    simp only [PosOK] at hpos
    simp only [StInv] at hinvt
    obtain ⟨h1, h2⟩ := hpos
    rw [h1]
    simp only [shiftType]
    exact ⟨trivial, by omega, fun hn => h2 hn, fun _ => trivial⟩
  | gone => exact absurd rfl hs

theorem splice_setup {ι0 κ0 : Type} [Fintype ι0] [Fintype κ0] (he : e.Valid)
    (hsel : IsOptimalSelector sel) (h : Hist L ι κ) (hr : (stp sel).Reachable e h)
    (hT : h.length ≤ e.P.T)
    (E0 : Econ L ι0 κ0) (d0 : Dispatch E0) (hd0f : d0.Feasible)
    (t0 : ℕ) (ht0 : replanTime sel e h = t0)
    (ofI : ι0 → ι) (toI : ι → Option ι0) (hI : ∀ i i0, toI i = some i0 ↔ ofI i0 = i)
    (ofJ : κ0 → κ) (toJ : κ → Option κ0) (hJ : ∀ j j0, toJ j = some j0 ↔ ofJ j0 = j)
    (hP0 : ShiftRel e.P E0.P t0)
    (hR0 : ∀ j0, (e.R (ofJ j0)).o = (E0.R j0).o ∧ (e.R (ofJ j0)).d = (E0.R j0).d ∧
      (e.R (ofJ j0)).τ = (E0.R j0).τ + t0 ∧ (e.R (ofJ j0)).v = (E0.R j0).v)
    (hJsurj : ∀ j, t0 ≤ (e.R j).τ → ∃ j0, ofJ j0 = j)
    (hIsurj : ∀ i, planStart sel e h i ≠ .gone → ∃ i0, ofI i0 = i)
    (hD0 : ∀ i0, DMatch e.P t0 (planStart sel e h (ofI i0)) (E0.D i0))
    (hZ : ∀ i0, curZ sel e h (ofI i0) = (d0.z i0).map (upE t0 ofJ)) :
    ∃ (f : {i // stateAt e h i ≠ .gone} → ι0) (finv : ι0 → Option {i // stateAt e h i ≠ .gone})
      (g : {j // h.length ≤ (e.R j).τ} → κ0) (pre : ι0 → List (Trip L × Option κ0)),
      SpliceData E0 (shiftEcon e h) (h.length - t0) f finv g pre ∧
      splice E0 (shiftEcon e h) (h.length - t0) finv g pre ((stp sel).contPlan e h).toDispatch = d0 := by
  obtain ⟨hle, hV, ⟨hok1, hok2⟩, hC⟩ := good_of_reachable sel e he hsel h hr
  have hG2 := good2_of_reachable sel e he hsel h hr
  rw [ht0] at hle
  obtain ⟨hd1, hx1⟩ := d1_feasible sel e he hsel h hr hT
  obtain ⟨hδ0, hT0, hc0, hκ0⟩ := hP0
  obtain ⟨hf01, hf02, hf03, hf04⟩ := hd0f
  have hP1 := he.1.1
  -- injectivity of the index maps
  have ofI_inj : Function.Injective ofI := by
    intro a b hab
    have h1 := (hI (ofI a) a).mpr rfl
    have h2 := (hI (ofI a) b).mpr hab.symm
    rw [h1] at h2; exact Option.some_injective _ h2
  have ofJ_inj : Function.Injective ofJ := by
    intro a b hab
    have h1 := (hJ (ofJ a) a).mpr rfl
    have h2 := (hJ (ofJ a) b).mpr hab.symm
    rw [h1] at h2; exact Option.some_injective _ h2
  -- the prefix state
  have hpre_len : (h.drop (h.length - t0)).length = t0 := by rw [List.length_drop]; omega
  have hps : ∀ i, planStart sel e h i = stateAt e (h.drop (h.length - t0)) i := by
    intro i; unfold planStart; rw [ht0]
  have hinv0 : ∀ i, StInv e.P t0 (planStart sel e h i) := by
    intro i
    have := stInv_stateAt e (h.drop (h.length - t0)) i
    rw [hpre_len] at this; rw [hps]; exact this
  have hnotgone : ∀ i, stateAt e h i ≠ .gone → planStart sel e h i ≠ .gone := by
    intro i hi hg
    rw [hps] at hg
    exact hi (gone_drop e h i _ hg)
  -- the maps of the splice
  let f : {i // stateAt e h i ≠ .gone} → ι0 := fun i1 =>
    Classical.choose (hIsurj i1.1 (hnotgone i1.1 i1.2))
  have hf : ∀ i1, ofI (f i1) = i1.1 := fun i1 =>
    Classical.choose_spec (hIsurj i1.1 (hnotgone i1.1 i1.2))
  let finv : ι0 → Option {i // stateAt e h i ≠ .gone} := fun i0 =>
    if hs : stateAt e h (ofI i0) ≠ .gone then some ⟨ofI i0, hs⟩ else none
  let g : {j // h.length ≤ (e.R j).τ} → κ0 := fun j1 =>
    Classical.choose (hJsurj j1.1 (by have := j1.2; omega))
  have hg : ∀ j1, ofJ (g j1) = j1.1 := fun j1 =>
    Classical.choose_spec (hJsurj j1.1 (by have := j1.2; omega))
  -- splitting the planned paths
  let pre : ι0 → List (Trip L × Option κ0) := fun i0 =>
    (d0.z i0).filter (fun st => decide (st.1.2.2 + t0 < h.length))
  let rest : ι0 → List (Trip L × Option κ0) := fun i0 =>
    (d0.z i0).filter (fun st => decide (h.length ≤ st.1.2.2 + t0))
  have hsplit : ∀ i0, d0.z i0 = pre i0 ++ rest i0 ∧
      (pre i0).map (upE t0 ofJ) = (curZ sel e h (ofI i0)).filter
        (fun st => decide (st.1.2.2 < h.length)) ∧
      (rest i0).map (upE t0 ofJ) = (curZ sel e h (ofI i0)).filter
        (fun st => decide (h.length ≤ st.1.2.2)) := by
    intro i0
    obtain ⟨preO, zsO, hz, hpreO, hcs, hzs⟩ := plan_split sel e he hsel h hr (ofI i0)
    have htimes := consS_times e.P h.length _ zsO (stInv_stateAt e h (ofI i0)) hcs
    rw [hZ] at hz
    obtain ⟨l1, l2, hl, hl1, hl2⟩ := List.map_eq_append_iff.mp hz
    have hl1t : ∀ st ∈ l1, st.1.2.2 + t0 < h.length := by
      intro st hst
      have := hpreO _ (hl1 ▸ List.mem_map_of_mem hst)
      simpa [upE, tripUp] using this
    have hl2t : ∀ st ∈ l2, h.length ≤ st.1.2.2 + t0 := by
      intro st hst
      have := (htimes _ (hl2 ▸ List.mem_map_of_mem hst)).1
      simpa [upE, tripUp] using this
    have hp : pre i0 = l1 := by
      have e1 : l1.filter (fun st => decide (st.1.2.2 + t0 < h.length)) = l1 :=
        List.filter_eq_self.mpr (fun st hst => by simpa using hl1t st hst)
      have e2 : l2.filter (fun st => decide (st.1.2.2 + t0 < h.length)) = [] :=
        List.filter_eq_nil_iff.mpr (fun st hst => by have := hl2t st hst; simp; omega)
      simp only [pre]; rw [hl, List.filter_append, e1, e2, List.append_nil]
    have hrs : rest i0 = l2 := by
      have e1 : l1.filter (fun st => decide (h.length ≤ st.1.2.2 + t0)) = [] :=
        List.filter_eq_nil_iff.mpr (fun st hst => by have := hl1t st hst; simp; omega)
      have e2 : l2.filter (fun st => decide (h.length ≤ st.1.2.2 + t0)) = l2 :=
        List.filter_eq_self.mpr (fun st hst => by simpa using hl2t st hst)
      simp only [rest]; rw [hl, List.filter_append, e1, e2, List.nil_append]
    refine ⟨by rw [hp, hrs, hl], ?_, ?_⟩
    · have e1 : (l1.map (upE t0 ofJ)).filter (fun st => decide (st.1.2.2 < h.length)) =
          l1.map (upE t0 ofJ) := List.filter_eq_self.mpr (fun st hst => by
            obtain ⟨st0, hst0, rfl⟩ := List.mem_map.mp hst
            exact decide_eq_true (hl1t st0 hst0))
      have e2 : (l2.map (upE t0 ofJ)).filter (fun st => decide (st.1.2.2 < h.length)) = [] :=
        List.filter_eq_nil_iff.mpr (fun st hst => by
            obtain ⟨st0, hst0, rfl⟩ := List.mem_map.mp hst
            have := hl2t st0 hst0; intro hc; have := of_decide_eq_true hc; simp only [upE, tripUp] at this; omega)
      rw [hp, hZ, hl, List.map_append, List.filter_append, e1, e2, List.append_nil]
    · rw [hrs, hl2, hzs]
  have hpath0 : ∀ i0, E0.P.IsPathFrom (E0.D i0).ℓ (E0.D i0).τ
      ((pre i0).map Prod.fst ++ (rest i0).map Prod.fst) := by
    intro i0
    have := hf01 i0
    unfold Dispatch.path at this
    rw [(hsplit i0).1, List.map_append] at this
    exact this
  -- position bookkeeping from the strengthened invariant
  have hpos : ∀ i1 : {i // stateAt e h i ≠ .gone},
      E0.P.pathEnd (E0.D (f i1)).ℓ (E0.D (f i1)).τ ((pre (f i1)).map Prod.fst) =
        (((shiftEcon e h).D i1).ℓ, ((shiftEcon e h).D i1).τ + (h.length - t0)) ∧
      (pre (f i1) = [] → ((shiftEcon e h).D i1).β = (E0.D (f i1)).β) ∧
      (pre (f i1) ≠ [] → ((shiftEcon e h).D i1).β = true) := by
    intro i1
    have hfi := hf i1
    have hG := hG2 i1.1
    have hD := hD0 (f i1)
    have hinv := hinv0 i1.1
    have hinvt := stInv_stateAt e h i1.1
    have hpreO := (hsplit (f i1)).2.1
    rw [hfi] at hD hpreO
    obtain ⟨preO, zsO, hz, hpreOt, hcs, hzs⟩ := plan_split sel e he hsel h hr i1.1
    -- the prefix in original coordinates is `preO`
    have hpreO' : (pre (f i1)).map (upE t0 ofJ) = preO := by
      rw [hpreO, hz, List.filter_append, List.filter_eq_self.mpr, List.filter_eq_nil_iff.mpr,
        List.append_nil]
      · intro st hst
        have := (consS_times e.P h.length _ zsO hinvt hcs st hst).1
        intro hc; have := of_decide_eq_true hc; omega
      · intro st hst; exact decide_eq_true (hpreOt st hst)
    have hmapfst : ((pre (f i1)).map Prod.fst).map (tripUp t0) = preO.map Prod.fst := by
      rw [← hpreO']; simp [upE, List.map_map, Function.comp_def]
    have hnil : pre (f i1) = [] ↔ preO.map Prod.fst = [] := by
      rw [← hmapfst]; simp
    -- shiftEcon type
    have hE1 : (shiftEcon e h).D i1 = shiftType e.P h.length (stateAt e h i1.1) i1.2 := rfl
    revert hG hD hinv
    generalize planStart sel e h i1.1 = s0
    intro hG hD hinv
    -- the Cons2 witness has the same prefix
    have hsame : ∀ pre' zs' : List (Trip L × Option κ), curZ sel e h i1.1 = pre' ++ zs' →
        (∀ st ∈ pre', st.1.2.2 < h.length) → ConsS e.P (stateAt e h i1.1) (zs'.map Prod.fst) →
        pre' = preO := by
      intro pre' zs' hz' hp' hc'
      have ht' := consS_times e.P h.length _ zs' hinvt hc'
      have : pre' = (curZ sel e h i1.1).filter (fun st => decide (st.1.2.2 < h.length)) := by
        rw [hz', List.filter_append, List.filter_eq_self.mpr, List.filter_eq_nil_iff.mpr,
          List.append_nil]
        · intro st hst; have := (ht' st hst).1; intro hc; have := of_decide_eq_true hc; omega
        · intro st hst; exact decide_eq_true (hp' st hst)
      rw [this, hz, List.filter_append, List.filter_eq_self.mpr, List.filter_eq_nil_iff.mpr,
        List.append_nil]
      · intro st hst
        have := (consS_times e.P h.length _ zsO hinvt hcs st hst).1
        intro hc; have := of_decide_eq_true hc; omega
      · intro st hst; exact decide_eq_true (hpreOt st hst)
    cases s0 with
    | gone => exact absurd hD id
    | wait β0 a0 τ0 =>
      simp only [DMatch] at hD
      simp only [StInv] at hinv
      obtain ⟨pre', zs', hz', hp', hc', hpp', hpos'⟩ := hG
      have hpe := hsame pre' zs' hz' hp' hc'
      subst hpe
      rw [hD]
      have hend := pathEnd_up ⟨hδ0, hT0, hc0, hκ0⟩ a0 (τ0 - t0) ((pre (f i1)).map Prod.fst)
      rw [Nat.sub_add_cancel hinv, hmapfst] at hend
      obtain ⟨q1, q2, q3, q4⟩ := pos_lemma e.P h.length t0 hle _ i1.2 hinvt a0 τ0 β0 _ hpos'
      rw [hend] at q1 q2
      rw [hE1]
      refine ⟨Prod.ext (by simp only; exact q1.symm) (by simp only at q2 ⊢; omega),
        fun hn => q3 (hnil.mp hn), fun hn => q4 (fun hc => hn (hnil.mpr hc))⟩
    | enroute a0 b0 t0' jj0 =>
      simp only [DMatch] at hD
      simp only [StInv] at hinv
      obtain ⟨pre', zs', hz', hp', hc', hpp', hpos'⟩ := hG
      have hpe := hsame pre' zs' hz' hp' hc'
      subst hpe
      rw [hD]
      have hend := pathEnd_up ⟨hδ0, hT0, hc0, hκ0⟩ b0 (t0' + e.P.δ a0 b0 - t0)
        ((pre (f i1)).map Prod.fst)
      rw [Nat.sub_add_cancel (by omega), hmapfst] at hend
      obtain ⟨q1, q2, q3, q4⟩ := pos_lemma e.P h.length t0 hle _ i1.2 hinvt b0 _ true _ hpos'
      rw [hend] at q1 q2
      rw [hE1]
      refine ⟨Prod.ext (by simp only; exact q1.symm) (by simp only at q2 ⊢; omega),
        fun hn => q3 (hnil.mp hn), fun hn => q4 (fun hc => hn (hnil.mpr hc))⟩
  have hfinv : ∀ i0 i1, finv i0 = some i1 ↔ f i1 = i0 := by
    intro i0 i1
    simp only [finv]
    constructor
    · intro hfi
      split_ifs at hfi with hs
      simp only [Option.some.injEq] at hfi
      subst hfi
      apply ofI_inj; rw [hf]
    · intro hfi
      subst hfi
      rw [dif_pos (by rw [hf]; exact i1.2)]
      congr 1; exact Subtype.ext (hf i1)
  have hginj : Function.Injective g := by
    intro a b hab
    apply Subtype.ext
    rw [← hg a, ← hg b, hab]
  have hS : SpliceData E0 (shiftEcon e h) (h.length - t0) f finv g pre := {
    hP := by
      refine ⟨hδ0.symm, ?_, ?_, hκ0.symm⟩
      · show e.P.T - h.length + (h.length - t0) = E0.P.T
        omega
      · intro a b u
        show e.P.c a b (u + h.length) = E0.P.c a b (u + (h.length - t0))
        rw [hc0, show u + (h.length - t0) + t0 = u + h.length by omega]
    hfinv := hfinv
    hg := hginj
    hR := by
      intro j1
      obtain ⟨r1, r2, r3, r4⟩ := hR0 (g j1)
      rw [hg j1] at r1 r2 r3 r4
      have := j1.2
      refine ⟨r1.symm, r2.symm, ?_, r4.symm⟩
      show (E0.R (g j1)).τ = (e.R j1.1).τ - h.length + (h.length - t0)
      omega
    hgsurj := by
      intro j0 hj0
      have r := (hR0 j0).2.2.1
      refine ⟨⟨ofJ j0, by omega⟩, ofJ_inj ?_⟩
      rw [hg]
    hpre_path := fun i0 => ((isPathFrom_append _ _ _ _ _).mp (hpath0 i0)).1
    hpre_time := by
      intro i0 st hst
      simp only [pre, List.mem_filter, decide_eq_true_eq] at hst
      omega
    hpre_tag := by
      intro i0 st hst j hj
      exact hf02 i0 st (List.mem_of_mem_filter hst) j hj
    hpre_x := by
      intro j0
      refine le_trans (Finset.card_le_card ?_) (le_of_eq_of_le (hf03 j0).symm (hf04 j0))
      intro i0
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact List.mem_of_mem_filter
    hend := fun i1 => (hpos i1).1
    hβ0 := fun i1 => (hpos i1).2.1
    hβ1 := fun i1 => (hpos i1).2.2 }
  -- the continuation plan spliced with the prefix is the planned dispatching
  have hzeq : ∀ i0, spliceZ (shiftEcon e h) (h.length - t0) finv g pre
      ((stp sel).contPlan e h).toDispatch i0 = d0.z i0 := by
    intro i0
    unfold spliceZ
    rw [(hsplit i0).1]
    congr 1
    rcases hfi : finv i0 with _ | i1
    · -- the driver has exited by now: nothing remains
      have hs : stateAt e h (ofI i0) = .gone := by
        simp only [finv] at hfi
        split_ifs at hfi with hs
        push Not at hs; exact hs
      obtain ⟨preO, zsO, hz, hpreO, hcs, hzs⟩ := plan_split sel e he hsel h hr (ofI i0)
      rw [hs] at hcs
      simp only [ConsS, List.map_eq_nil_iff] at hcs
      have h3 := (hsplit i0).2.2
      rw [← hzs, hcs, List.map_eq_nil_iff] at h3
      exact h3.symm
    · have hi0 : f i1 = i0 := (hfinv i0 i1).mp hfi
      have hofI : ofI i0 = i1.1 := by rw [← hi0, hf]
      show ((outTrips e ((stp sel).sigmaStar e) h i1.1).map (shiftTrip e h.length)).map
        (upE (h.length - t0) g) = rest i0
      rw [outTrips_star sel e he hsel h hr hT, ← hofI, ← (hsplit i0).2.2,
        List.map_map, List.map_map]
      conv_rhs => rw [← List.map_id (rest i0)]
      apply List.map_congr_left
      intro st hst
      have ht : h.length ≤ st.1.2.2 + t0 := by
        simp only [rest, List.mem_filter, decide_eq_true_eq] at hst; exact hst.2
      obtain ⟨⟨a, b, u⟩, o⟩ := st
      simp only [Function.comp, id, upE, tripUp, shiftTrip]
      congr 1
      · simp only [Prod.mk.injEq, true_and]; simp at ht; omega
      · cases o with
        | none => rfl
        | some j0 =>
          have htag := hf02 i0 _ (List.mem_of_mem_filter hst) j0 rfl
          simp only [riderTrip, Prod.mk.injEq] at htag
          have hτ : h.length ≤ (e.R (ofJ j0)).τ := by
            have := (hR0 j0).2.2.1
            have hu := htag.2.2
            simp only at ht
            omega
          simp only [Option.map_some, Option.bind_some, dif_pos hτ, Option.some.injEq]
          apply ofJ_inj
          rw [hg]
  have heq : splice E0 (shiftEcon e h) (h.length - t0) finv g pre
      ((stp sel).contPlan e h).toDispatch = d0 := by
    apply dispatch_ext
    · funext j0
      show (Finset.univ.filter fun i0 => (riderTrip (E0.R j0), some j0) ∈
        spliceZ (shiftEcon e h) (h.length - t0) finv g pre _ i0).card = d0.x j0
      rw [hf03 j0]
      congr 1; ext i0; simp only [Finset.mem_filter, Finset.mem_univ, true_and]; rw [hzeq]
    · funext i0; exact hzeq i0
  exact ⟨f, finv, g, pre, hS, heq⟩

theorem wo_generic {ι0 κ0 : Type} [Fintype ι0] [Fintype κ0] (he : e.Valid)
    (hsel : IsOptimalSelector sel) (h : Hist L ι κ) (hr : (stp sel).Reachable e h)
    (hT : h.length ≤ e.P.T)
    (E0 : Econ L ι0 κ0) (d0 : Dispatch E0) (hd0 : d0.IsWelfareOptimal)
    (t0 : ℕ) (ht0 : replanTime sel e h = t0)
    (ofI : ι0 → ι) (toI : ι → Option ι0) (hI : ∀ i i0, toI i = some i0 ↔ ofI i0 = i)
    (ofJ : κ0 → κ) (toJ : κ → Option κ0) (hJ : ∀ j j0, toJ j = some j0 ↔ ofJ j0 = j)
    (hP0 : ShiftRel e.P E0.P t0)
    (hR0 : ∀ j0, (e.R (ofJ j0)).o = (E0.R j0).o ∧ (e.R (ofJ j0)).d = (E0.R j0).d ∧
      (e.R (ofJ j0)).τ = (E0.R j0).τ + t0 ∧ (e.R (ofJ j0)).v = (E0.R j0).v)
    (hJsurj : ∀ j, t0 ≤ (e.R j).τ → ∃ j0, ofJ j0 = j)
    (hIsurj : ∀ i, planStart sel e h i ≠ .gone → ∃ i0, ofI i0 = i)
    (hD0 : ∀ i0, DMatch e.P t0 (planStart sel e h (ofI i0)) (E0.D i0))
    (hZ : ∀ i0, curZ sel e h (ofI i0) = (d0.z i0).map (upE t0 ofJ)) :
    ((stp sel).contPlan e h).toDispatch.IsWelfareOptimal := by
  obtain ⟨hd1, _⟩ := d1_feasible sel e he hsel h hr hT
  obtain ⟨f, finv, g, pre, hS, heq⟩ := splice_setup sel e he hsel h hr hT E0 d0 hd0.1 t0 ht0 ofI toI hI
    ofJ toJ hJ hP0 hR0 hJsurj hIsurj hD0 hZ
  refine ⟨hd1, fun d' hd' => ?_⟩
  have w1 := splice_welfare hS d' hd'
  have w2 := splice_welfare hS _ hd1
  have w3 := hd0.2 _ (splice_feasible hS d' hd')
  rw [heq] at w2
  linarith

omit [Fintype L] [Fintype ι] [Fintype κ] in
theorem dmatch_shiftType (P : Params L) (t : ℕ) (s : DState L κ) (hs : s ≠ .gone) :
    DMatch P t s (shiftType P t s hs) := by
  cases s with
  | wait β a τ => rfl
  | enroute a b t' jj => rfl
  | gone => exact absurd rfl hs

theorem wo_main (hsel : IsOptimalSelector sel) (he : e.Valid) (h : Hist L ι κ)
    (hr : (stp sel).Reachable e h) (hT : h.length ≤ e.P.T) :
    ((stp sel).contPlan e h).toDispatch.IsWelfareOptimal := by
  have hle : replanTime sel e h ≤ h.length := (good_of_reachable sel e he hsel h hr).1
  by_cases h0 : replanTime sel e h = 0
  · refine wo_generic sel e he hsel h hr hT e (sel e) (hsel e he) 0 h0 id some
      (fun _ _ => by simp [eq_comm]) id some (fun _ _ => by simp [eq_comm]) ⟨rfl, by simp, fun _ _ _ => by simp, rfl⟩ (fun j0 => by simp)
      (fun j _ => ⟨j, rfl⟩) (fun i _ => ⟨i, rfl⟩) ?_ ?_
    · intro i0
      have : planStart sel e h i0 = stateAt e [] i0 := by
        unfold planStart; rw [h0, Nat.sub_zero, List.drop_length]
      simp only [id]
      rw [this]
      show DMatch e.P 0 (.wait (e.D i0).β (e.D i0).ℓ (e.D i0).τ) (e.D i0)
      simp [DMatch]
    · intro i0
      have hz : curZ sel e h i0 = (sel e).z i0 := by simp [curZ, h0]
      simp only [id]
      rw [hz]
      conv_lhs => rw [← List.map_id ((sel e).z i0)]
      apply List.map_congr_left
      intro st _
      obtain ⟨⟨a, b, u⟩, o⟩ := st
      simp [upE, tripUp]
  · set t0 := replanTime sel e h with ht0
    set pre0 := h.drop (h.length - t0) with hpre0
    have hlen : pre0.length = t0 := by simp only [pre0, List.length_drop]; omega
    have hrp : (stp sel).Reachable e pre0 := reach_drop sel e h _ hr
    have hVp := (good_of_reachable sel e he hsel pre0 hrp).2.1
    have hval := econAt_valid e he pre0 hVp
    refine wo_generic sel e he hsel h hr hT (shiftEcon e pre0) (sel (shiftEcon e pre0))
      (hsel _ hval) t0 rfl Subtype.val
      (fun i => if hs : stateAt e pre0 i ≠ .gone then some ⟨i, hs⟩ else none) ?_
      Subtype.val (fun j => if hj : pre0.length ≤ (e.R j).τ then some ⟨j, hj⟩ else none) ?_
      ?_ ?_ ?_ ?_ ?_ ?_
    · intro i i0
      constructor
      · intro hh; split_ifs at hh with hs
        simp only [Option.some.injEq] at hh; rw [← hh]
      · intro hh; subst hh; rw [dif_pos i0.2]
    · intro j j0
      constructor
      · intro hh; split_ifs at hh with hs
        simp only [Option.some.injEq] at hh; rw [← hh]
      · intro hh; subst hh; rw [dif_pos j0.2]
    · refine ⟨rfl, ?_, fun a b u => ?_, rfl⟩
      · show e.P.T - pre0.length + t0 = e.P.T
        omega
      · show e.P.c a b (u + pre0.length) = e.P.c a b (u + t0)
        rw [hlen]
    · intro j0
      have := j0.2
      refine ⟨rfl, rfl, ?_, rfl⟩
      show (e.R j0.1).τ = (e.R j0.1).τ - pre0.length + t0
      omega
    · intro j hj
      exact ⟨⟨j, by omega⟩, rfl⟩
    · intro i hi
      exact ⟨⟨i, hi⟩, rfl⟩
    · intro i0
      have : planStart sel e h i0.1 = stateAt e pre0 i0.1 := rfl
      rw [this]
      have := dmatch_shiftType e.P pre0.length (stateAt e pre0 i0.1) i0.2
      show DMatch e.P t0 (stateAt e pre0 i0.1) (shiftType e.P pre0.length (stateAt e pre0 i0.1) i0.2)
      rw [← hlen]; exact this
    · intro i0
      unfold curZ
      rw [if_neg h0, dif_pos i0.2]
      rfl

/-! ### The planning economy at time `0` as a time-shifted economy -/

theorem initial_not_gone (i : ι) : stateAt e ([] : Hist L ι κ) i ≠ .gone := by
  simp [stateAt]

/-- Splice data identifying `e` with `E^{(0)}(s_0)`. -/
theorem spliceData_init :
    SpliceData e (shiftEcon e ([] : Hist L ι κ)) 0 Subtype.val
      (fun i => some ⟨i, initial_not_gone e i⟩) Subtype.val (fun _ => []) where
  hP := ⟨rfl, by show e.P.T - 0 + 0 = e.P.T; simp, fun a b u => rfl, rfl⟩
  hfinv := by
    intro i0 i1
    constructor
    · intro hh; simp only [Option.some.injEq] at hh; rw [← hh]
    · intro hh; subst hh; rfl
  hg := Subtype.val_injective
  hR := fun j1 => ⟨rfl, rfl, by show (e.R j1.1).τ = (e.R j1.1).τ - 0 + 0; simp, rfl⟩
  hgsurj := fun j0 _ => ⟨⟨j0, Nat.zero_le _⟩, rfl⟩
  hpre_path := fun _ => by simp [Params.IsPathFrom]
  hpre_time := fun _ => by simp
  hpre_tag := fun _ => by simp
  hpre_x := fun _ => by simp
  hend := by
    intro i1
    show ((e.D i1.1).ℓ, (e.D i1.1).τ) = ((shiftType e.P 0 (stateAt e [] i1.1) i1.2).ℓ,
      (shiftType e.P 0 (stateAt e [] i1.1) i1.2).τ + 0)
    simp [stateAt, shiftType]
  hβ0 := by
    intro i1 _
    show (shiftType e.P 0 (stateAt e [] i1.1) i1.2).β = (e.D i1.1).β
    simp [stateAt, shiftType]
  hβ1 := fun _ h => absurd rfl h

/-- Transport of a dispatching of `e` to `E^{(0)}(s_0)`. -/
noncomputable def toInit (d : Dispatch e) : Dispatch (shiftEcon e ([] : Hist L ι κ)) where
  x := fun j1 => d.x j1.1
  z := fun i1 => (d.z i1.1).map (fun st => (st.1, st.2.map (fun j => ⟨j, Nat.zero_le _⟩)))

theorem toInit_map (d : Dispatch e) (i1 : {i // stateAt e ([] : Hist L ι κ) i ≠ .gone}) :
    ((toInit e d).z i1).map (upE 0 Subtype.val) = d.z i1.1 := by
  simp only [toInit, List.map_map]
  conv_rhs => rw [← List.map_id (d.z i1.1)]
  apply List.map_congr_left
  intro st _
  obtain ⟨⟨a, b, u⟩, o⟩ := st
  cases o <;> simp [upE, tripUp]

theorem toInit_optimal (d : Dispatch e) (hd : d.IsWelfareOptimal) :
    (toInit e d).IsWelfareOptimal := by
  have hS := spliceData_init e
  obtain ⟨hf1, hf2, hf3, hf4⟩ := hd.1
  have hmapz : ∀ i : ι, ((toInit e d).z ⟨i, initial_not_gone e i⟩).map (upE 0 Subtype.val) =
      d.z i := by
    intro i
    simp only [toInit, List.map_map]
    conv_rhs => rw [← List.map_id (d.z i)]
    apply List.map_congr_left
    intro st _
    obtain ⟨⟨a, b, u⟩, o⟩ := st
    cases o <;> simp [upE, tripUp]
  have hmem : ∀ (i1 : {i // stateAt e [] i ≠ .gone}) (j1 : {j // ([] : Hist L ι κ).length ≤ (e.R j).τ}),
      (riderTrip ((shiftEcon e []).R j1), some j1) ∈ (toInit e d).z i1 ↔
        (riderTrip (e.R j1.1), some j1.1) ∈ d.z i1.1 := by
    intro i1 j1
    have := hmapz i1.1
    constructor
    · intro hm
      rw [← this]
      have := List.mem_map_of_mem (f := upE 0 Subtype.val) hm
      simpa [upE, tripUp, riderTrip, shiftEcon, econAt] using this
    · intro hm
      simp only [toInit, List.mem_map]
      refine ⟨_, hm, ?_⟩
      simp [riderTrip, shiftEcon, econAt]
  have hfeas : (toInit e d).Feasible := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro i1
      apply isPathFrom_down hS.hP
      have := hf1 i1.1
      have hm := congrArg (List.map Prod.fst) (hmapz i1.1)
      simp only [List.map_map] at hm
      show e.P.IsPathFrom _ (_ + 0) _
      have hD : (shiftEcon e []).D i1 = ⟨(e.D i1.1).β, (e.D i1.1).ℓ, (e.D i1.1).τ - 0⟩ := by
        show shiftType e.P 0 (stateAt e [] i1.1) i1.2 = _
        simp [stateAt, shiftType]
      rw [hD]
      simp only [Nat.sub_zero, Nat.add_zero]
      convert this using 1
      unfold Dispatch.path
      rw [← hm]
      simp [upE, Dispatch.path, Function.comp_def]
    · intro i1 st hst j1 hj1
      simp only [toInit, List.mem_map] at hst
      obtain ⟨st0, hst0, rfl⟩ := hst
      simp only [Option.map_eq_some_iff] at hj1
      obtain ⟨j, hj, rfl⟩ := hj1
      have := hf2 i1.1 st0 hst0 j hj
      simp [this, riderTrip, shiftEcon, econAt]
    · intro j1
      show d.x j1.1 = _
      rw [hf3 j1.1]
      rw [← Finset.card_map ⟨Subtype.val, Subtype.val_injective⟩]
      apply congrArg Finset.card
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map,
        Function.Embedding.coeFn_mk]
      constructor
      · intro hm; exact ⟨⟨i, initial_not_gone e i⟩, (hmem _ j1).mpr hm, rfl⟩
      · rintro ⟨i1, hm, rfl⟩; exact (hmem i1 j1).mp hm
    · intro j1; exact hf4 j1.1
  refine optimal_of_splice hS d hd _ hfeas ?_
  apply dispatch_ext
  · funext j0
    show (Finset.univ.filter fun i0 => (riderTrip (e.R j0), some j0) ∈
      spliceZ (shiftEcon e []) 0 _ Subtype.val (fun _ => []) (toInit e d) i0).card = d.x j0
    rw [hf3 j0]
    apply congrArg Finset.card
    ext i0
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    unfold spliceZ
    simp only [List.nil_append]
    rw [hmapz]
  · funext i0
    show spliceZ (shiftEcon e []) 0 (fun i => some ⟨i, initial_not_gone e i⟩) Subtype.val
      (fun _ => []) (toInit e d) i0 = d.z i0
    unfold spliceZ
    simp only [List.nil_append]
    exact hmapz i0

/-- The plan in force at a reachable history, as an optimal dispatching of the planning economy
`E^{(t₀)}(s_{t₀})`, spliced from its prefix and the continuation. -/
theorem setup_epoch (hsel : IsOptimalSelector sel) (he : e.Valid) (h : Hist L ι κ)
    (hr : (stp sel).Reachable e h) (hT : h.length ≤ e.P.T) :
    ∃ d0 : Dispatch (shiftEcon e (h.drop (h.length - replanTime sel e h))),
      d0.IsWelfareOptimal ∧
      ∃ (f : {i // stateAt e h i ≠ .gone} → {i // stateAt e (h.drop (h.length - replanTime sel e h)) i ≠ .gone})
        (finv : {i // stateAt e (h.drop (h.length - replanTime sel e h)) i ≠ .gone} →
          Option {i // stateAt e h i ≠ .gone})
        (g : {j // h.length ≤ (e.R j).τ} →
          {j // (h.drop (h.length - replanTime sel e h)).length ≤ (e.R j).τ})
        (pre : {i // stateAt e (h.drop (h.length - replanTime sel e h)) i ≠ .gone} →
          List (Trip L × Option {j // (h.drop (h.length - replanTime sel e h)).length ≤ (e.R j).τ})),
        SpliceData (shiftEcon e (h.drop (h.length - replanTime sel e h))) (shiftEcon e h)
          (h.length - (h.drop (h.length - replanTime sel e h)).length) f finv g pre ∧
        splice (shiftEcon e (h.drop (h.length - replanTime sel e h))) (shiftEcon e h)
          (h.length - (h.drop (h.length - replanTime sel e h)).length) finv g pre
          ((stp sel).contPlan e h).toDispatch = d0 := by
  have hle : replanTime sel e h ≤ h.length := (good_of_reachable sel e he hsel h hr).1
  have hlen : (h.drop (h.length - replanTime sel e h)).length = replanTime sel e h := by
    rw [List.length_drop]; omega
  by_cases h0 : replanTime sel e h = 0
  · have hp : h.drop (h.length - replanTime sel e h) = [] := by
      rw [h0, Nat.sub_zero, List.drop_length]
    rw [hp]
    refine ⟨toInit e (sel e), toInit_optimal e _ (hsel e he), ?_⟩
    have hZ : ∀ i0 : {i // stateAt e ([] : Hist L ι κ) i ≠ .gone},
        curZ sel e h i0.1 = ((toInit e (sel e)).z i0).map (upE 0 Subtype.val) := by
      intro i0
      rw [toInit_map]
      simp [curZ, h0]
    obtain ⟨f, finv, g, pre, hS, heq⟩ := splice_setup sel e he hsel h hr hT
      (shiftEcon e []) (toInit e (sel e)) (toInit_optimal e _ (hsel e he)).1 0 h0
      Subtype.val (fun i => some ⟨i, initial_not_gone e i⟩)
      (fun i i0 => by
        constructor
        · intro hh; simp only [Option.some.injEq] at hh; rw [← hh]
        · intro hh; subst hh; rfl)
      Subtype.val (fun j => some ⟨j, Nat.zero_le _⟩)
      (fun j j0 => by
        constructor
        · intro hh; simp only [Option.some.injEq] at hh; rw [← hh]
        · intro hh; subst hh; rfl)
      ⟨rfl, by show e.P.T - 0 + 0 = e.P.T; simp, fun a b u => rfl, rfl⟩
      (fun j0 => ⟨rfl, rfl, by show (e.R j0.1).τ = (e.R j0.1).τ - 0 + 0; simp, rfl⟩)
      (fun j _ => ⟨⟨j, Nat.zero_le _⟩, rfl⟩)
      (fun i _ => ⟨⟨i, initial_not_gone e i⟩, rfl⟩)
      (fun i0 => by
        have hps : planStart sel e h i0.1 = stateAt e [] i0.1 := by
          unfold planStart; rw [hp]
        rw [hps]
        exact dmatch_shiftType e.P 0 _ i0.2)
      hZ
    exact ⟨f, finv, g, pre, hS, heq⟩
  · set pre0 := h.drop (h.length - replanTime sel e h) with hpre0
    have hrp : (stp sel).Reachable e pre0 := reach_drop sel e h _ hr
    have hVp := (good_of_reachable sel e he hsel pre0 hrp).2.1
    have hval := econAt_valid e he pre0 hVp
    refine ⟨sel (shiftEcon e pre0), hsel _ hval, ?_⟩
    exact splice_setup sel e he hsel h hr hT (shiftEcon e pre0) (sel (shiftEcon e pre0))
      (hsel _ hval).1 pre0.length hlen.symm Subtype.val
      (fun i => if hs : stateAt e pre0 i ≠ .gone then some ⟨i, hs⟩ else none)
      (fun i i0 => by
        constructor
        · intro hh; split_ifs at hh with hs
          simp only [Option.some.injEq] at hh; rw [← hh]
        · intro hh; subst hh; rw [dif_pos i0.2])
      Subtype.val (fun j => if hj : pre0.length ≤ (e.R j).τ then some ⟨j, hj⟩ else none)
      (fun j j0 => by
        constructor
        · intro hh; split_ifs at hh with hs
          simp only [Option.some.injEq] at hh; rw [← hh]
        · intro hh; subst hh; rw [dif_pos j0.2])
      ⟨rfl, by show e.P.T - pre0.length + pre0.length = e.P.T; omega, fun a b u => rfl, rfl⟩
      (fun j0 => ⟨rfl, rfl, by
        have := j0.2
        show (e.R j0.1).τ = (e.R j0.1).τ - pre0.length + pre0.length
        omega, rfl⟩)
      (fun j hj => ⟨⟨j, hj⟩, rfl⟩)
      (fun i hi => ⟨⟨i, hi⟩, rfl⟩)
      (fun i0 => dmatch_shiftType e.P pre0.length _ i0.2)
      (fun i0 => by
        unfold curZ
        rw [if_neg h0, dif_pos i0.2]
        apply List.map_congr_left
        intro st _
        simp only [shiftBack, upE, tripUp, hlen]; rfl)

/-- Step 2, part (i), p. 54: `Φ^{(t′)}_{a,t}(s_{t′}) ≥ Φ^{(t)}_{a,t}(s_t)`. -/
theorem part_i_main (hsel : IsOptimalSelector sel) (he : e.Valid) (h : Hist L ι κ)
    (hr : (stp sel).Reachable e h) (hT : h.length < e.P.T) (a : L) :
    PhiShift e h.length (stateAt e h) a h.length ≤
      PhiShift e (replanTime sel e h) (stateAt e (h.drop (h.length - replanTime sel e h))) a
        h.length := by
  obtain ⟨d0, hd0, f, finv, g, pre, hS, heq⟩ := setup_epoch sel e hsel he h hr (le_of_lt hT)
  have hle : replanTime sel e h ≤ h.length := (good_of_reachable sel e he hsel h hr).1
  have hlen : (h.drop (h.length - replanTime sel e h)).length = replanTime sel e h := by
    rw [List.length_drop]; omega
  have hR : PhiShift e (replanTime sel e h) (stateAt e (h.drop (h.length - replanTime sel e h))) a
      h.length = PhiAt (shiftEcon e (h.drop (h.length - replanTime sel e h))) a
        (h.length - (h.drop (h.length - replanTime sel e h)).length) := by
    have key : ∀ n, n = replanTime sel e h →
        PhiAt (econAt e n (stateAt e (h.drop (h.length - replanTime sel e h)))) a (h.length - n) =
        PhiAt (econAt e (replanTime sel e h) (stateAt e (h.drop (h.length - replanTime sel e h))))
          a (h.length - replanTime sel e h) := by
      intro n hn; subst hn; rfl
    exact (key _ hlen).symm
  rw [hR]
  show W ((shiftEcon e h).addDriver ⟨true, a, h.length - h.length⟩) - W (shiftEcon e h) ≤
    W ((shiftEcon e (h.drop (h.length - replanTime sel e h))).addDriver
      ⟨true, a, h.length - (h.drop (h.length - replanTime sel e h)).length⟩) -
    W (shiftEcon e (h.drop (h.length - replanTime sel e h)))
  -- validity of the economies involved
  have hV1 := (good_of_reachable sel e he hsel h hr).2.1
  have hv1 := econAt_valid e he h hV1
  have hrp := reach_drop sel e h (h.length - replanTime sel e h) hr
  have hVp := (good_of_reachable sel e he hsel _ hrp).2.1
  have hv0 := econAt_valid e he _ hVp
  -- the continuation is optimal
  obtain ⟨hwo1, hwo2⟩ := wo_main sel e hsel he h hr (le_of_lt hT)
  have hW1 := W_of_optimal _ _ ⟨hwo1, hwo2⟩
  have hW0 := W_of_optimal _ _ hd0
  have hw0 := splice_welfare hS _ hwo1
  rw [heq] at hw0
  -- with the extra driver
  have hS' := spliceData_add hS ⟨true, a, h.length - (h.drop (h.length - replanTime sel e h)).length⟩
    ⟨true, a, h.length - h.length⟩ rfl rfl (by simp)
  have hv1' := addDriver_valid _ hv1 ⟨true, a, h.length - h.length⟩ (by simp)
  have hv0' := addDriver_valid _ hv0
    ⟨true, a, h.length - (h.drop (h.length - replanTime sel e h)).length⟩
    (by show _ ≤ e.P.T - _; simp only [hlen]; omega)
  have hdp := hsel _ hv1'
  have hsp := splice_feasible hS' _ hdp.1
  have hle0 := le_W _ _ (hsel _ hv0') _ hsp
  rw [splice_welfare hS' _ hdp.1, spliceConst_add, ← W_of_optimal _ _ hdp] at hle0
  linarith

/-! ### One step of the dynamics as a splice -/

omit [Fintype L] [Fintype ι] [Fintype κ] in
theorem one_step_pos (P : Params L) (hP : ∀ a b, 1 ≤ P.δ a b) (R : κ → Rider L) (t : ℕ)
    (s : DState L κ) (hinv : StInv P t s) (α : DAction L κ)
    (hα : IsAvailAt t s → α ≠ .cont) (hs : s ≠ .gone) (hs' : step P R t s α ≠ .gone) :
    (shiftParams P t).pathEnd (shiftType P t s hs).ℓ (shiftType P t s hs).τ
        (((stepTrip R t s α).toList).map (fun st => (st.1.1, st.1.2.1, st.1.2.2 - t))) =
      ((shiftType P (t + 1) (step P R t s α) hs').ℓ,
        (shiftType P (t + 1) (step P R t s α) hs').τ + 1) ∧
    ((stepTrip R t s α).toList = [] →
      (shiftType P (t + 1) (step P R t s α) hs').β = (shiftType P t s hs).β) ∧
    ((stepTrip R t s α).toList ≠ [] → (shiftType P (t + 1) (step P R t s α) hs').β = true) := by
  cases s with
  | wait β a τ =>
    simp only [StInv] at hinv
    by_cases hτ : τ = t
    · subst hτ
      cases α with
      | move b =>
        have hd := hP a b
        revert hs'
        simp only [step, if_true, arrive]
        split_ifs with hh
        · intro hs'
          simp [stepTrip, shiftType, Params.pathEnd, shiftParams]
          omega
        · intro hs'
          simp [stepTrip, shiftType, Params.pathEnd, shiftParams]
          omega
      | pick j =>
        have hd := hP a (R j).d
        revert hs'
        simp only [step, if_true, arrive]
        split_ifs with hh
        · intro hs'
          simp [stepTrip, shiftType, Params.pathEnd, shiftParams]
          omega
        · intro hs'
          simp [stepTrip, shiftType, Params.pathEnd, shiftParams]
          omega
      | quit => exact absurd (by simp [step]) hs'
      | cont => exact absurd rfl (hα (by simp [IsAvailAt]))
    · have hst : step P R t (.wait β a τ) α = .wait β a τ := by simp [step, hτ]
      have htr : stepTrip R t (.wait β a τ) α = none := by
        cases α <;> simp [stepTrip, hτ]
      revert hs'
      rw [hst, htr]
      intro hs'
      simp [shiftType, Params.pathEnd]
      omega
  | enroute a b t' jj =>
    simp only [StInv] at hinv
    have htr : stepTrip R t (.enroute a b t' jj) α = none := by cases α <;> rfl
    revert hs'
    rw [htr]
    simp only [step]
    split_ifs with hh
    · intro hs'
      simp [shiftType, Params.pathEnd]
      omega
    · intro hs'
      simp [shiftType, Params.pathEnd]
      omega
  | gone => exact absurd rfl hs

omit [Fintype L] [Fintype ι] [Fintype κ] in
theorem stepTrip_time (R : κ → Rider L) (t : ℕ) (s : DState L κ) (α : DAction L κ)
    (st : Trip L × Option κ) (hst : stepTrip R t s α = some st) : st.1.2.2 = t := by
  cases s with
  | wait β a τ =>
    cases α with
    | move b =>
      simp only [stepTrip] at hst; split_ifs at hst
      simp only [Option.some.injEq] at hst; subst hst; rfl
    | pick j =>
      simp only [stepTrip] at hst; split_ifs at hst
      simp only [Option.some.injEq] at hst; subst hst; rfl
    | quit => simp [stepTrip] at hst
    | cont => simp [stepTrip] at hst
  | enroute => cases α <;> simp [stepTrip] at hst
  | gone => cases α <;> simp [stepTrip] at hst

theorem planAct_ne_cont (z : List (Trip L × Option κ)) (u : ℕ) : planAct z u ≠ .cont := by
  unfold planAct
  rcases hf : z.find? (fun st => decide (st.1.2.2 = u)) with _ | ⟨⟨a, b, c⟩, _ | j⟩ <;> simp [hf]

/-- Following the dispatch for one period: the continuation plan at `h` is the splice of the
trips started now with the continuation plan one period later. -/
theorem splice_step (hsel : IsOptimalSelector sel) (he : e.Valid) (h : Hist L ι κ)
    (hr : (stp sel).Reachable e h) (hT : h.length < e.P.T) :
    ∃ (f : {i // stateAt e ((fun k => (stp sel).sigmaStar e k h) :: h) i ≠ .gone} →
          {i // stateAt e h i ≠ .gone})
      (finv : {i // stateAt e h i ≠ .gone} →
          Option {i // stateAt e ((fun k => (stp sel).sigmaStar e k h) :: h) i ≠ .gone})
      (g : {j // ((fun k => (stp sel).sigmaStar e k h) :: h).length ≤ (e.R j).τ} →
          {j // h.length ≤ (e.R j).τ})
      (pre : {i // stateAt e h i ≠ .gone} → List (Trip L × Option {j // h.length ≤ (e.R j).τ})),
      SpliceData (shiftEcon e h) (shiftEcon e ((fun k => (stp sel).sigmaStar e k h) :: h)) 1
        f finv g pre ∧
      splice (shiftEcon e h) (shiftEcon e ((fun k => (stp sel).sigmaStar e k h) :: h)) 1 finv g pre
        ((stp sel).contPlan e ((fun k => (stp sel).sigmaStar e k h) :: h)).toDispatch =
      ((stp sel).contPlan e h).toDispatch := by
  set h' := (fun k => (stp sel).sigmaStar e k h) :: h with hh'
  have hr' : (stp sel).Reachable e h' := ⟨hr, hT, fun k => dispatch_mem_actions sel e h k⟩
  have hlen' : h'.length = h.length + 1 := rfl
  obtain ⟨hle, _, ⟨hok1, _⟩, _⟩ := good_of_reachable sel e he hsel h hr
  have hz' : curZ sel e h' = curZ sel e h :=
    (curZ_noDev sel e _ h hle (fun i => dispatch_eq sel e h i)).2
  obtain ⟨hwo1, _⟩ := wo_main sel e hsel he h hr (le_of_lt hT)
  obtain ⟨hf1, hf2, hf3, hf4⟩ := hwo1
  have hgone : ∀ i, stateAt e h i = .gone → stateAt e h' i = .gone := by
    intro i hg
    show step e.P e.R h.length (stateAt e h i) _ = .gone
    rw [hg]; rfl
  let f : {i // stateAt e h' i ≠ .gone} → {i // stateAt e h i ≠ .gone} :=
    fun i2 => ⟨i2.1, fun hg => i2.2 (hgone _ hg)⟩
  let finv : {i // stateAt e h i ≠ .gone} → Option {i // stateAt e h' i ≠ .gone} :=
    fun i1 => if hs : stateAt e h' i1.1 ≠ .gone then some ⟨i1.1, hs⟩ else none
  let g : {j // h'.length ≤ (e.R j).τ} → {j // h.length ≤ (e.R j).τ} :=
    fun j2 => ⟨j2.1, by have := j2.2; have h2 : h'.length = h.length + 1 := hlen'; omega⟩
  let pre : {i // stateAt e h i ≠ .gone} → List (Trip L × Option {j // h.length ≤ (e.R j).τ}) :=
    fun i1 => (stepTrip e.R h.length (stateAt e h i1.1)
      ((stp sel).sigmaStar e i1.1 h)).toList.map (shiftTrip e h.length)
  -- the continuation plan at `h` splits
  have hsplit : ∀ i1 : {i // stateAt e h i ≠ .gone}, ((stp sel).contPlan e h).toDispatch.z i1 =
      pre i1 ++ ((curZ sel e h i1.1).filter (fun st => decide (h.length + 1 ≤ st.1.2.2))).map
        (shiftTrip e h.length) := by
    intro i1
    show (outTrips e ((stp sel).sigmaStar e) h i1.1).map (shiftTrip e h.length) = _
    rw [outTrips_star sel e he hsel h hr (le_of_lt hT), step_filter sel e he hsel h hr hT,
      List.map_append]
  have hfinv : ∀ i1 i2, finv i1 = some i2 ↔ f i2 = i1 := by
    intro i1 i2
    simp only [finv, f]
    constructor
    · intro hh
      split_ifs at hh with hs
      simp only [Option.some.injEq] at hh
      subst hh; rfl
    · intro hh
      subst hh
      rw [dif_pos i2.2]
  have hS : SpliceData (shiftEcon e h) (shiftEcon e h') 1 f finv g pre := {
    hP := by
      refine ⟨rfl, ?_, fun a b u => ?_, rfl⟩
      · show e.P.T - h'.length + 1 = e.P.T - h.length
        rw [hlen']; omega
      · show e.P.c a b (u + h'.length) = e.P.c a b (u + 1 + h.length)
        rw [hlen', show u + 1 + h.length = u + (h.length + 1) by omega]
    hfinv := hfinv
    hg := by
      intro a b hab
      apply Subtype.ext
      have := congrArg Subtype.val hab
      exact this
    hR := by
      intro j2
      have := j2.2
      have h2 : h'.length = h.length + 1 := hlen'
      refine ⟨rfl, rfl, ?_, rfl⟩
      show (e.R j2.1).τ - h.length = (e.R j2.1).τ - h'.length + 1
      omega
    hgsurj := by
      intro j1 hj1
      have : h.length + 1 ≤ (e.R j1.1).τ := by
        have := j1.2
        change 1 ≤ (e.R j1.1).τ - h.length at hj1
        omega
      exact ⟨⟨j1.1, by rw [hlen']; exact this⟩, rfl⟩
    hpre_path := by
      intro i1
      have := hf1 i1
      unfold Dispatch.path at this
      rw [hsplit i1, List.map_append] at this
      exact ((isPathFrom_append _ _ _ _ _).mp this).1
    hpre_time := by
      intro i1 st hst
      simp only [pre, List.mem_map] at hst
      obtain ⟨st0, hst0, rfl⟩ := hst
      have := stepTrip_time e.R h.length _ _ st0 (Option.mem_toList.mp hst0)
      simp [shiftTrip, this]
    hpre_tag := by
      intro i1 st hst j hj
      exact hf2 i1 st (by rw [hsplit]; exact List.mem_append_left _ hst) j hj
    hpre_x := by
      intro j1
      refine le_trans (Finset.card_le_card ?_) (le_of_eq_of_le (hf3 j1).symm (hf4 j1))
      intro i1
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      intro hm; rw [hsplit]; exact List.mem_append_left _ hm
    hend := by
      intro i2
      have hst' : stateAt e h' i2.1 =
          step e.P e.R h.length (stateAt e h i2.1) ((stp sel).sigmaStar e i2.1 h) := rfl
      have hα : IsAvailAt h.length (stateAt e h i2.1) → (stp sel).sigmaStar e i2.1 h ≠ .cont := by
        intro ha
        show (stp sel).dispatch e h i2.1 ≠ _
        rw [dispatch_eq, disp_planAct sel e h i2.1 hle ha]
        exact planAct_ne_cont _ _
      have key := one_step_pos e.P he.1.1 e.R h.length (stateAt e h i2.1)
        (stInv_stateAt e h i2.1) _ hα (f i2).2 (by rw [← hst']; exact i2.2)
      have e1 : (shiftEcon e h).D (f i2) = shiftType e.P h.length (stateAt e h i2.1) (f i2).2 := rfl
      have e2 : (shiftEcon e h').D i2 = shiftType e.P (h.length + 1)
          (step e.P e.R h.length (stateAt e h i2.1) ((stp sel).sigmaStar e i2.1 h))
          (by rw [← hst']; exact i2.2) := rfl
      rw [e1, e2]
      convert key.1 using 2
      all_goals first | rfl | (simp only [pre, List.map_map]; rfl) |
        simp [pre, shiftTrip, Function.comp_def]
    hβ0 := by
      intro i2 hp
      have hst' : stateAt e h' i2.1 =
          step e.P e.R h.length (stateAt e h i2.1) ((stp sel).sigmaStar e i2.1 h) := rfl
      have hα : IsAvailAt h.length (stateAt e h i2.1) → (stp sel).sigmaStar e i2.1 h ≠ .cont := by
        intro ha
        show (stp sel).dispatch e h i2.1 ≠ _
        rw [dispatch_eq, disp_planAct sel e h i2.1 hle ha]
        exact planAct_ne_cont _ _
      have key := one_step_pos e.P he.1.1 e.R h.length (stateAt e h i2.1)
        (stInv_stateAt e h i2.1) _ hα (f i2).2 (by rw [← hst']; exact i2.2)
      exact key.2.1 (by simpa [pre] using hp)
    hβ1 := by
      intro i2 hp
      have hst' : stateAt e h' i2.1 =
          step e.P e.R h.length (stateAt e h i2.1) ((stp sel).sigmaStar e i2.1 h) := rfl
      have hα : IsAvailAt h.length (stateAt e h i2.1) → (stp sel).sigmaStar e i2.1 h ≠ .cont := by
        intro ha
        show (stp sel).dispatch e h i2.1 ≠ _
        rw [dispatch_eq, disp_planAct sel e h i2.1 hle ha]
        exact planAct_ne_cont _ _
      have key := one_step_pos e.P he.1.1 e.R h.length (stateAt e h i2.1)
        (stInv_stateAt e h i2.1) _ hα (f i2).2 (by rw [← hst']; exact i2.2)
      exact key.2.2 (by simpa [pre] using hp) }
  refine ⟨f, finv, g, pre, hS, ?_⟩
  have hzeq : ∀ i1, spliceZ (shiftEcon e h') 1 finv g pre
      ((stp sel).contPlan e h').toDispatch i1 = ((stp sel).contPlan e h).toDispatch.z i1 := by
    intro i1
    unfold spliceZ
    rw [hsplit i1]
    congr 1
    rcases hfi : finv i1 with _ | i2
    · have hs : stateAt e h' i1.1 = .gone := by
        simp only [finv] at hfi
        split_ifs at hfi with hs
        push Not at hs; exact hs
      obtain ⟨preO, zsO, hz, hpreO, hcs, hzs⟩ := plan_split sel e he hsel h' hr' i1.1
      rw [hs] at hcs
      simp only [ConsS, List.map_eq_nil_iff] at hcs
      rw [hz', hlen', hcs] at hzs
      rw [← hzs]; rfl
    · have hi : f i2 = i1 := (hfinv i1 i2).mp hfi
      subst hi
      have h2 : h'.length = h.length + 1 := hlen'
      show ((outTrips e ((stp sel).sigmaStar e) h' i2.1).map (shiftTrip e h'.length)).map
        (upE 1 g) = _
      rw [outTrips_star sel e he hsel h' hr' (by omega), hz', List.map_map]
      have hfl : (curZ sel e h i2.1).filter (fun st => decide (h'.length ≤ st.1.2.2)) =
          (curZ sel e h i2.1).filter (fun st => decide (h.length + 1 ≤ st.1.2.2)) := by
        congr 1
      rw [hfl]
      apply List.map_congr_left
      intro st hst
      have ht : h.length + 1 ≤ st.1.2.2 := by
        simp only [List.mem_filter, decide_eq_true_eq] at hst; exact hst.2
      obtain ⟨⟨a, b, u⟩, o⟩ := st
      simp only [Function.comp, upE, tripUp, shiftTrip]
      congr 1
      · simp only [Prod.mk.injEq, true_and]; simp at ht; omega
      · cases o with
        | none => rfl
        | some j =>
          have htag := hok1 i2.1 _ (List.mem_of_mem_filter hst) j rfl
          simp only [riderTrip, Prod.mk.injEq] at htag
          have hτ1 : h.length + 1 ≤ (e.R j).τ := by simp at ht; omega
          have hτ0 : h.length ≤ (e.R j).τ := by omega
          simp only [Option.bind_some, dif_pos (show h'.length ≤ (e.R j).τ by omega),
            dif_pos hτ0, Option.map_some]
          rfl
  apply dispatch_ext
  · funext j1
    rw [hf3 j1]
    unfold splice
    dsimp only
    apply congrArg Finset.card
    ext i1
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [hzeq]
  · funext i1; exact hzeq i1

/-- Step 2, part (ii), p. 54:
`Φ^{(t)}_{a,t}(s_t) ≥ Φ^{(t+1)}_{b,t+δ(a,b)}(s_{t+1}) − c_{a,b,t}`. -/
theorem part_ii_main (hsel : IsOptimalSelector sel) (he : e.Valid) (h : Hist L ι κ)
    (hr : (stp sel).Reachable e h) (hT : h.length < e.P.T) (a b : L)
    (hb : h.length + e.P.δ a b ≤ e.P.T) :
    PhiShift e (h.length + 1) (stateAt e ((fun k => (stp sel).dispatch e h k) :: h)) b
        (h.length + e.P.δ a b) - e.P.c a b h.length ≤
      PhiShift e h.length (stateAt e h) a h.length := by
  obtain ⟨f, finv, g, pre, hS, heq⟩ := splice_step sel e hsel he h hr hT
  set h' := (fun k => (stp sel).sigmaStar e k h) :: h with hh'
  have hr' : (stp sel).Reachable e h' := ⟨hr, hT, fun k => dispatch_mem_actions sel e h k⟩
  have hδ := he.1.1 a b
  show W ((shiftEcon e h').addDriver ⟨true, b, h.length + e.P.δ a b - (h.length + 1)⟩) -
      W (shiftEcon e h') - e.P.c a b h.length ≤
    W ((shiftEcon e h).addDriver ⟨true, a, h.length - h.length⟩) - W (shiftEcon e h)
  -- validity
  have hv1 := econAt_valid e he h (good_of_reachable sel e he hsel h hr).2.1
  have hv2 := econAt_valid e he h' (good_of_reachable sel e he hsel h' hr').2.1
  -- the continuation plans are optimal and spliced
  have hwo1 := wo_main sel e hsel he h hr (le_of_lt hT)
  have hwo2 := wo_main sel e hsel he h' hr' (by show h.length + 1 ≤ e.P.T; omega)
  have hW1 := W_of_optimal _ _ hwo1
  have hW2 := W_of_optimal _ _ hwo2
  have hw := splice_welfare hS _ hwo2.1
  rw [heq] at hw
  -- the extra driver relocates from `a` to `b` first
  have hS' := spliceData_addP hS ⟨true, a, h.length - h.length⟩
    ⟨true, b, h.length + e.P.δ a b - (h.length + 1)⟩ [((a, b, h.length - h.length), none)]
    (by
      simp only [List.map_cons, List.map_nil, Params.IsPathFrom]
      refine ⟨by simp, by simp, ?_, trivial⟩
      show h.length - h.length + e.P.δ a b ≤ e.P.T - h.length
      omega)
    (by simp) (by simp)
    (by
      simp only [List.map_cons, List.map_nil, Params.pathEnd]
      show (b, h.length - h.length + e.P.δ a b) = (b, h.length + e.P.δ a b - (h.length + 1) + 1)
      congr 1; omega)
    (by simp) (fun _ => rfl)
  have hv2' := addDriver_valid _ hv2 ⟨true, b, h.length + e.P.δ a b - (h.length + 1)⟩
    (by show h.length + e.P.δ a b - (h.length + 1) ≤ e.P.T - (h.length + 1); omega)
  have hv1' := addDriver_valid _ hv1 ⟨true, a, h.length - h.length⟩ (by simp)
  have hdp := hsel _ hv2'
  have hsp := splice_feasible hS' _ hdp.1
  have hle1 := le_W _ _ (hsel _ hv1') _ hsp
  rw [splice_welfare hS' _ hdp.1, spliceConst_addP _ _ (by simp), ← W_of_optimal _ _ hdp] at hle1
  have hc : (([((a, b, h.length - h.length), (none : Option {j // h.length ≤ (e.R j).τ}))].map
      Prod.fst).map (fun e' => (shiftEcon e h).P.c e'.1 e'.2.1 e'.2.2)).sum = e.P.c a b h.length := by
    show e.P.c a b (h.length - h.length + h.length) + 0 = e.P.c a b h.length
    simp
  rw [hc] at hle1
  linarith

end WO

end BBAux

end STPRideshare.Mechanism


open STPRideshare.Mechanism in
theorem solution {L : Type} [Fintype L] (sel : Selector L) (hsel : IsOptimalSelector sel)
    {ι κ : Type} [Fintype ι] [Fintype κ] (e : Econ L ι κ) (he : e.Valid)
    (h : Hist L ι κ) (hh : (stp sel).Reachable e h) (ht : h.length < e.P.T)
    (i : ι) (β : Bool) (a : L) (hs : stateAt e h i = .wait β a h.length) :
    ∀ b : L, h.length + e.P.δ a b ≤ e.P.T →
      PhiShift e (h.length + 1) (stateAt e ((fun k => (stp sel).dispatch e h k) :: h)) b
          (h.length + e.P.δ a b) - e.P.c a b h.length ≤
        PhiShift e h.length (stateAt e h) a h.length :=
  fun b hb => BBAux.part_ii_main sel e hsel he h hh ht a b hb
