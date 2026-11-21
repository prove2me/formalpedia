-- Prove2me | solution 1 for SerialBatchTardy.early_processing_le
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-21T01:19:09.729184+00:00
-- url     : https://prove2.me/submissions/da7dcb93-7585-4faa-ab3a-5cb809c11504

import Mathlib
import Definitions.Def_SerialBatchTardy_Construction
set_option autoImplicit false

namespace Aux_SerialBatchTardy_early_processing_le

open SerialBatchTardy

theorem job_eq {xs : List ℕ} {t k : ℕ} {L : List ℕ}
    (j : Fin (hardInstance xs t k L).jobs.length) :
    (hardInstance xs t k L).job j = labelJob xs t k (labelOf xs t k L j) := by
  unfold Instance.job labelOf
  simp only [List.get_eq_getElem]
  simp only [hardInstance, List.getElem_map]
  rfl

theorem labelOf_mem {xs : List ℕ} {t k : ℕ} {L : List ℕ}
    (j : Fin (hardInstance xs t k L).jobs.length) :
    labelOf xs t k L j ∈ hardLabels xs k L :=
  List.get_mem _ _

theorem mem_hardLabels_normal {xs : List ℕ} {k : ℕ} {L : List ℕ} {ℓ x h : ℕ}
    (hm : JobLabel.normal ℓ x h ∈ hardLabels xs k L) :
    x ∈ xs ∧ ℓ < k := by
  unfold hardLabels at hm
  rcases List.mem_append.mp hm with h1 | h1
  · obtain ⟨e, _, he⟩ := List.mem_map.mp h1
    cases he
  · obtain ⟨ℓ', hℓ', h2⟩ := List.mem_flatMap.mp h1
    obtain ⟨x', hx', h3⟩ := List.mem_flatMap.mp h2
    unfold gadgetLabels at h3
    obtain ⟨h', _, h4⟩ := List.mem_flatMap.mp h3
    have h5 := (List.mem_replicate.mp h4).2
    cases h5
    exact ⟨hx', List.mem_range.mp hℓ'⟩

theorem gadget_some {xs : List ℕ} {t k : ℕ} {L : List ℕ}
    {j : Fin (hardInstance xs t k L).jobs.length} {ℓ : ℕ}
    (hg : (labelOf xs t k L j).gadget? = some ℓ) :
    ∃ x h, labelOf xs t k L j = .normal ℓ x h ∧ x ∈ xs ∧ ℓ < k := by
  have hm := labelOf_mem (xs := xs) (t := t) (k := k) (L := L) j
  obtain ⟨lab, hlab⟩ : ∃ lab, labelOf xs t k L j = lab := ⟨_, rfl⟩
  rw [hlab] at hg hm
  rw [hlab]
  cases lab with
  | leftover e => simp [JobLabel.gadget?] at hg
  | normal ℓ' x h =>
    simp only [JobLabel.gadget?, Option.some.injEq] at hg
    subst hg
    obtain ⟨hx, hℓ⟩ := mem_hardLabels_normal hm
    exact ⟨x, h, rfl, hx, hℓ⟩

theorem job_normal {xs : List ℕ} {t k : ℕ} {L : List ℕ}
    {j : Fin (hardInstance xs t k L).jobs.length} {ℓ x h : ℕ}
    (hl : labelOf xs t k L j = .normal ℓ x h) :
    (hardInstance xs t k L).job j =
      { p := xs.length ^ h, w := xs.length ^ h * (xs.prod + xs.prod / x),
        r := ((ℓ * (3 * t) : ℕ) : ℤ), d := ((ℓ * (3 * t) + t + x : ℕ) : ℤ) } := by
  rw [job_eq, hl]
  rfl

theorem batchLen_eq {xs : List ℕ} {t k : ℕ} {L : List ℕ}
    (σ : Schedule (hardInstance xs t k L)) (b : ℕ) :
    σ.batchLen b = (t : ℤ) + ∑ j ∈ σ.batchJobs b, (((hardInstance xs t k L).job j).p : ℤ) :=
  rfl

theorem batchLen_ge {xs : List ℕ} {t k : ℕ} {L : List ℕ}
    (σ : Schedule (hardInstance xs t k L)) (b : ℕ) : (t : ℤ) ≤ σ.batchLen b := by
  have h0 : (0 : ℤ) ≤ ∑ j ∈ σ.batchJobs b, (((hardInstance xs t k L).job j).p : ℤ) :=
    Finset.sum_nonneg (fun _ _ => by positivity)
  have hb := batchLen_eq σ b
  linarith

theorem mem_earlyType {xs : List ℕ} {t k : ℕ} {L : List ℕ}
    {σ : Schedule (hardInstance xs t k L)} {ℓ : ℕ} {j : Fin (hardInstance xs t k L).jobs.length} :
    j ∈ earlyType σ ℓ ↔ (labelOf xs t k L j).gadget? = some ℓ ∧ ¬ σ.IsTardy j := by
  simp only [earlyType, Finset.mem_filter, Finset.mem_univ, true_and]

theorem early_facts {xs : List ℕ} {t k : ℕ} {L : List ℕ}
    (σ : Schedule (hardInstance xs t k L)) (hσ : σ.Feasible)
    {j : Fin (hardInstance xs t k L).jobs.length} {ℓ : ℕ} (hj : j ∈ earlyType σ ℓ) :
    ∃ x h, labelOf xs t k L j = .normal ℓ x h ∧ x ∈ xs ∧
      (ℓ : ℤ) * (3 * t) ≤ σ.start (σ.batch j) ∧
      σ.comp (σ.batch j) ≤ (ℓ : ℤ) * (3 * t) + t + x ∧
      σ.start (σ.batch j) + t ≤ σ.comp (σ.batch j) := by
  rw [mem_earlyType] at hj
  obtain ⟨hg, hnt⟩ := hj
  obtain ⟨x, h, hl, hx, -⟩ := gadget_some hg
  have hr := hσ.1 j
  have hd : ¬ ((hardInstance xs t k L).job j).d < σ.comp (σ.batch j) := hnt
  have hd2 := not_lt.mp hd
  rw [job_normal hl] at hr hd2
  have hr' : (ℓ : ℤ) * (3 * t) ≤ σ.start (σ.batch j) := by
    have := hr
    push_cast at this
    linarith
  have hd' : σ.comp (σ.batch j) ≤ (ℓ : ℤ) * (3 * t) + t + x := by
    have := hd2
    push_cast at this
    linarith
  have hlen := batchLen_ge σ (σ.batch j)
  have hc : σ.comp (σ.batch j) = σ.start (σ.batch j) + σ.batchLen (σ.batch j) := rfl
  exact ⟨x, h, hl, hx, hr', hd', by linarith⟩

theorem same_batch {xs : List ℕ} {t k : ℕ} {L : List ℕ} (hlt : ∀ a ∈ xs, a < t)
    (σ : Schedule (hardInstance xs t k L)) (hσ : σ.Feasible) {ℓ : ℕ}
    {j j' : Fin (hardInstance xs t k L).jobs.length}
    (hj : j ∈ earlyType σ ℓ) (hj' : j' ∈ earlyType σ ℓ) : σ.batch j' = σ.batch j := by
  by_contra hne
  obtain ⟨x, h, _, hx, a1, a2, a3⟩ := early_facts σ hσ hj
  obtain ⟨x', h', _, hx', b1, b2, b3⟩ := early_facts σ hσ hj'
  have h1 : (x : ℤ) < t := by exact_mod_cast hlt x hx
  have h2 : (x' : ℤ) < t := by exact_mod_cast hlt x' hx'
  rcases hσ.2 _ _ ⟨j', rfl⟩ ⟨j, rfl⟩ hne with h | h
  · linarith
  · linarith

theorem pSum_le {xs : List ℕ} {t k : ℕ} {L : List ℕ} (hlt : ∀ a ∈ xs, a < t)
    (σ : Schedule (hardInstance xs t k L)) (hσ : σ.Feasible) {ℓ : ℕ}
    {j : Fin (hardInstance xs t k L).jobs.length} (hj : j ∈ earlyType σ ℓ) :
    ∃ x h, labelOf xs t k L j = .normal ℓ x h ∧ x ∈ xs ∧ pSum (earlyType σ ℓ) ≤ x := by
  obtain ⟨x, h, hl, hx, a1, a2, a3⟩ := early_facts σ hσ hj
  refine ⟨x, h, hl, hx, ?_⟩
  have hsub : earlyType σ ℓ ⊆ σ.batchJobs (σ.batch j) := by
    intro j' hj'
    simp only [Schedule.batchJobs, Finset.mem_filter, Finset.mem_univ, true_and]
    exact same_batch hlt σ hσ hj hj'
  have hP : ((pSum (earlyType σ ℓ) : ℕ) : ℤ) ≤
      ∑ i ∈ σ.batchJobs (σ.batch j), (((hardInstance xs t k L).job i).p : ℤ) := by
    unfold pSum
    push_cast
    exact Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
  have hc : σ.comp (σ.batch j) = σ.start (σ.batch j) + σ.batchLen (σ.batch j) := rfl
  have hb := batchLen_eq σ (σ.batch j)
  have : ((pSum (earlyType σ ℓ) : ℕ) : ℤ) ≤ x := by linarith
  exact_mod_cast this

theorem wSum_le {xs : List ℕ} {t k : ℕ} {L : List ℕ} (hlt : ∀ a ∈ xs, a < t)
    (σ : Schedule (hardInstance xs t k L)) (hσ : σ.Feasible) (ℓ : ℕ) :
    wSum (earlyType σ ℓ) ≤ xs.prod * pSum (earlyType σ ℓ) + xs.prod := by
  let v : Fin (hardInstance xs t k L).jobs.length → ℕ :=
    fun j => ((labelOf xs t k L j).value?).getD 0
  have key : ∀ j ∈ earlyType σ ℓ,
      ((hardInstance xs t k L).job j).w = ((hardInstance xs t k L).job j).p * xs.prod +
        ((hardInstance xs t k L).job j).p * (xs.prod / v j) ∧
      pSum (earlyType σ ℓ) ≤ v j ∧ v j ∣ xs.prod := by
    intro j hj
    obtain ⟨x, h, hl, hx, hPx⟩ := pSum_le hlt σ hσ hj
    have hv : v j = x := by simp only [v, hl, JobLabel.value?, Option.getD_some]
    rw [job_normal hl, hv]
    refine ⟨?_, hPx, List.dvd_prod hx⟩
    dsimp only
    ring
  have hw : wSum (earlyType σ ℓ) = xs.prod * pSum (earlyType σ ℓ) +
      ∑ j ∈ earlyType σ ℓ, ((hardInstance xs t k L).job j).p * (xs.prod / v j) := by
    unfold wSum pSum
    rw [Finset.sum_congr rfl (fun j hj => (key j hj).1), Finset.sum_add_distrib, Finset.mul_sum]
    congr 1
    exact Finset.sum_congr rfl (fun j _ => by ring)
  have hQ : ∑ j ∈ earlyType σ ℓ, ((hardInstance xs t k L).job j).p * (xs.prod / v j) ≤
      xs.prod := by
    rcases Nat.eq_zero_or_pos (pSum (earlyType σ ℓ)) with hP0 | hPpos
    · have hp0 : ∀ j ∈ earlyType σ ℓ, ((hardInstance xs t k L).job j).p = 0 := by
        have : ∑ j ∈ earlyType σ ℓ, ((hardInstance xs t k L).job j).p = 0 := hP0
        exact Finset.sum_eq_zero_iff.mp this
      have h0 : ∑ j ∈ earlyType σ ℓ, ((hardInstance xs t k L).job j).p * (xs.prod / v j) = 0 :=
        Finset.sum_eq_zero (fun j hj => by rw [hp0 j hj, zero_mul])
      rw [h0]
      exact Nat.zero_le _
    · apply Nat.le_of_mul_le_mul_left _ hPpos
      calc pSum (earlyType σ ℓ) *
            ∑ j ∈ earlyType σ ℓ, ((hardInstance xs t k L).job j).p * (xs.prod / v j)
          = ∑ j ∈ earlyType σ ℓ, ((hardInstance xs t k L).job j).p * (xs.prod / v j) *
              pSum (earlyType σ ℓ) := by
            rw [Finset.mul_sum]
            exact Finset.sum_congr rfl (fun _ _ => by ring)
        _ ≤ ∑ j ∈ earlyType σ ℓ, ((hardInstance xs t k L).job j).p * (xs.prod / v j) * v j :=
            Finset.sum_le_sum (fun j hj => Nat.mul_le_mul_left _ (key j hj).2.1)
        _ = ∑ j ∈ earlyType σ ℓ, ((hardInstance xs t k L).job j).p * xs.prod :=
            Finset.sum_congr rfl (fun j hj => by rw [mul_assoc, Nat.div_mul_cancel (key j hj).2.2])
        _ = pSum (earlyType σ ℓ) * xs.prod := by
            unfold pSum
            rw [Finset.sum_mul]
  rw [hw]
  exact Nat.add_le_add_left hQ _

/-! ## List sums over the label list -/

theorem sum_map_flatMap {α β : Type} (l : List α) (f : α → List β) (g : β → ℕ) :
    ((l.flatMap f).map g).sum = (l.map fun a => ((f a).map g).sum).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp [ih]

theorem lsum_range (n : ℕ) (f : ℕ → ℕ) :
    ((List.range n).map f).sum = ∑ i ∈ Finset.range n, f i := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.sum_append, ih, Finset.sum_range_succ]
    simp

theorem lsum_zero {α : Type} (l : List α) (f : α → ℕ) (hf : ∀ a ∈ l, f a = 0) :
    (l.map f).sum = 0 := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons]
    rw [hf a (by simp), ih (fun b hb => hf b (by simp [hb]))]

theorem sum_getD_pow (b : ℕ) (L : List ℕ) :
    ∑ h ∈ Finset.range L.length, L.getD h 0 * b ^ h = Nat.ofDigits b L := by
  induction L with
  | nil => simp
  | cons d L ih =>
    rw [List.length_cons, Finset.sum_range_succ', Nat.ofDigits_cons, ← ih, Finset.mul_sum]
    simp only [List.getD_cons_succ, List.getD_cons_zero, pow_zero, mul_one]
    rw [add_comm]
    congr 1
    apply Finset.sum_congr rfl
    intro h _
    ring

theorem digits_sum_mul (b x c : ℕ) :
    ∑ h ∈ Finset.range (Nat.digits b x).length, (Nat.digits b x).getD h 0 * (b ^ h * c) =
      x * c := by
  have := sum_getD_pow b (Nat.digits b x)
  rw [Nat.ofDigits_digits] at this
  calc ∑ h ∈ Finset.range (Nat.digits b x).length, (Nat.digits b x).getD h 0 * (b ^ h * c)
      = (∑ h ∈ Finset.range (Nat.digits b x).length, (Nat.digits b x).getD h 0 * b ^ h) * c := by
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl (fun _ _ => by ring)
    _ = x * c := by rw [this]

theorem gadget_sum (xs : List ℕ) (G : JobLabel → ℕ) (ℓ x c : ℕ)
    (h1 : ∀ h, G (.normal ℓ x h) = xs.length ^ h * c) :
    ((gadgetLabels xs ℓ x).map G).sum = x * c := by
  unfold gadgetLabels
  rw [sum_map_flatMap, lsum_range, ← digits_sum_mul xs.length x c]
  apply Finset.sum_congr rfl
  intro h _
  rw [List.map_replicate, List.sum_replicate, smul_eq_mul, h1]

theorem hard_sum (xs : List ℕ) (k : ℕ) (L : List ℕ) (G : JobLabel → ℕ) (c : ℕ → ℕ → ℕ)
    (h0 : ∀ e, G (.leftover e) = 0)
    (h1 : ∀ ℓ x h, G (.normal ℓ x h) = xs.length ^ h * c ℓ x) :
    ((hardLabels xs k L).map G).sum =
      ∑ ℓ ∈ Finset.range k, (xs.map fun x => x * c ℓ x).sum := by
  unfold hardLabels
  rw [List.map_append, List.sum_append, sum_map_flatMap, lsum_range]
  have hL : ((L.map JobLabel.leftover).map G).sum = 0 := by
    rw [List.map_map]
    exact lsum_zero _ _ (fun e _ => h0 e)
  rw [hL, zero_add]
  apply Finset.sum_congr rfl
  intro ℓ _
  rw [sum_map_flatMap]
  congr 1
  apply List.map_congr_left
  intro x _
  exact gadget_sum xs G ℓ x (c ℓ x) (fun h => h1 ℓ x h)

theorem sum_jobs {xs : List ℕ} {t k : ℕ} {L : List ℕ} (F : JobLabel → ℕ) :
    ∑ j : Fin (hardInstance xs t k L).jobs.length, F (labelOf xs t k L j) =
      ((hardLabels xs k L).map F).sum := by
  calc ∑ j : Fin (hardInstance xs t k L).jobs.length, F (labelOf xs t k L j)
      = ∑ i : Fin (hardLabels xs k L).length, F ((hardLabels xs k L).get i) :=
        Fin.sum_congr' (fun i => F ((hardLabels xs k L).get i)) (by simp [hardInstance])
    _ = ((hardLabels xs k L).map F).sum := by
        simp only [List.get_eq_getElem]
        exact Fin.sum_univ_fun_getElem _ _

theorem list_weight (S : ℕ) : ∀ ys : List ℕ, (∀ y ∈ ys, y ∣ S) →
    (ys.map fun x => x * (S + S / x)).sum = S * ys.sum + S * ys.length := by
  intro ys
  induction ys with
  | nil => intro _; simp
  | cons y ys ih =>
    intro h
    have hy : y * (S / y) = S := Nat.mul_div_cancel' (h y (by simp))
    have ih' := ih (fun z hz => h z (by simp [hz]))
    simp only [List.map_cons, List.sum_cons, List.length_cons, ih']
    have e : y * (S + S / y) = y * S + S := by rw [Nat.mul_add, hy]
    rw [e]
    ring

theorem gadgetW {xs : List ℕ} {t k : ℕ} {L : List ℕ} {ℓ' : ℕ} (hk : ℓ' < k) :
    ∑ j : Fin (hardInstance xs t k L).jobs.length,
      (if (labelOf xs t k L j).gadget? = some ℓ' then ((hardInstance xs t k L).job j).w else 0) =
      xs.prod * xs.sum + xs.prod * xs.length := by
  simp only [job_eq]
  refine (sum_jobs (xs := xs) (t := t) (k := k) (L := L)
    (fun lab => if lab.gadget? = some ℓ' then (labelJob xs t k lab).w else 0)).trans ?_
  refine (hard_sum xs k L _ (fun ℓ x => if ℓ = ℓ' then xs.prod + xs.prod / x else 0)
    ?_ ?_).trans ?_
  · intro e
    simp [JobLabel.gadget?]
  · intro ℓ x h
    by_cases hl : ℓ = ℓ'
    · subst hl
      simp [JobLabel.gadget?, labelJob]
    · simp [JobLabel.gadget?, labelJob, hl]
  · rw [Finset.sum_eq_single_of_mem ℓ' (Finset.mem_range.mpr hk)]
    · simpa using list_weight xs.prod xs (fun y hy => List.dvd_prod hy)
    · intro b _ hb
      simp [hb]

/-! ## Tardy weight decomposition -/

def tardyIn {xs : List ℕ} {t k : ℕ} {L : List ℕ} (σ : Schedule (hardInstance xs t k L))
    (ℓ' : ℕ) : ℕ :=
  ∑ j, (if (labelOf xs t k L j).gadget? = some ℓ' then
    (if σ.IsTardy j then ((hardInstance xs t k L).job j).w else 0) else 0)

theorem tardy_split {xs : List ℕ} {t k : ℕ} {L : List ℕ} (σ : Schedule (hardInstance xs t k L))
    (ℓ' : ℕ) :
    tardyIn σ ℓ' + wSum (earlyType σ ℓ') =
      ∑ j, (if (labelOf xs t k L j).gadget? = some ℓ' then
        ((hardInstance xs t k L).job j).w else 0) := by
  unfold tardyIn wSum earlyType
  rw [Finset.sum_filter, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  by_cases h1 : (labelOf xs t k L j).gadget? = some ℓ' <;> by_cases h2 : σ.IsTardy j <;>
    simp [h1, h2]

theorem tardy_ge {xs : List ℕ} {t k : ℕ} {L : List ℕ} (σ : Schedule (hardInstance xs t k L))
    (K : ℕ) : ∑ ℓ' ∈ Finset.range K, tardyIn σ ℓ' ≤ σ.tardyWeight := by
  unfold tardyIn Schedule.tardyWeight
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro j _
  rcases hg : (labelOf xs t k L j).gadget? with _ | m
  · simp
  · simp only [Option.some.injEq, Finset.sum_ite_eq]
    split_ifs <;> simp

theorem gadget_total {xs : List ℕ} {t k : ℕ} {L : List ℕ} (σ : Schedule (hardInstance xs t k L)) :
    ∑ ℓ' ∈ Finset.range k, tardyIn σ ℓ' + ∑ ℓ' ∈ Finset.range k, wSum (earlyType σ ℓ') =
      k * (xs.prod * xs.sum + xs.prod * xs.length) := by
  rw [← Finset.sum_add_distrib]
  have : ∀ ℓ' ∈ Finset.range k, tardyIn σ ℓ' + wSum (earlyType σ ℓ') =
      xs.prod * xs.sum + xs.prod * xs.length :=
    fun ℓ' hℓ' => (tardy_split σ ℓ').trans (gadgetW (Finset.mem_range.mp hℓ'))
  rw [Finset.sum_congr rfl this]
  simp

theorem all_nonempty (xs : List ℕ) (t k : ℕ) (L : List ℕ) (hnd : xs.Nodup) (hpos : ∀ a ∈ xs, 1 ≤ a)
    (hstand : ∀ a ∈ xs, ((k : ℤ) - 1) * a < t)
    (σ : Schedule (hardInstance xs t k L)) (hσ : σ.Feasible)
    (hW : (σ.tardyWeight : ℤ) ≤ hardBound xs t k) :
    ∀ ℓ < k, (earlyType σ ℓ).Nonempty := by
  intro ℓ hℓ
  by_contra hne
  have hE0 : earlyType σ ℓ = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
  have hk1 : 1 ≤ k := by omega
  have hk1z : (1 : ℤ) ≤ k := by exact_mod_cast hk1
  by_cases hxs : xs = []
  · subst hxs
    simp only [hardBound, List.prod_nil, List.sum_nil, List.length_nil, Nat.cast_one,
      Nat.cast_zero, one_mul, zero_add, mul_zero] at hW
    have : (0 : ℤ) ≤ σ.tardyWeight := by positivity
    linarith
  have ht1 : 1 ≤ t := by
    obtain ⟨a, ha⟩ := List.exists_mem_of_ne_nil xs hxs
    have h1 := hstand a ha
    have h2 : (0 : ℤ) ≤ ((k : ℤ) - 1) * a := mul_nonneg (by linarith) (by positivity)
    have : (0 : ℤ) < t := by linarith
    exact_mod_cast this
  have hS : 0 < xs.prod := List.prod_pos (fun a ha => hpos a ha)
  have hE : ∑ ℓ' ∈ Finset.range k, wSum (earlyType σ ℓ') + 2 * xs.prod ≤
      xs.prod * t + xs.prod * k := by
    rw [← Finset.sum_erase_add _ _ (Finset.mem_range.mpr hℓ), hE0]
    have hw0 : wSum (∅ : Finset (Fin (hardInstance xs t k L).jobs.length)) = 0 := by
      simp [wSum]
    rw [hw0, add_zero]
    have hcard : ((Finset.range k).erase ℓ).card = k - 1 := by
      rw [Finset.card_erase_of_mem (Finset.mem_range.mpr hℓ), Finset.card_range]
    by_cases hk2 : 2 ≤ k
    · have hlt : ∀ a ∈ xs, a < t := by
        intro a ha
        have h1 := hstand a ha
        have h3 : (1 : ℤ) ≤ (k : ℤ) - 1 := by
          have : (2 : ℤ) ≤ k := by exact_mod_cast hk2
          linarith
        have h2 : (a : ℤ) ≤ ((k : ℤ) - 1) * a := by
          have ha0 : (0 : ℤ) ≤ a := by positivity
          nlinarith
        have : (a : ℤ) < t := by linarith
        exact_mod_cast this
      have hb : ∀ ℓ' ∈ (Finset.range k).erase ℓ,
          wSum (earlyType σ ℓ') ≤ xs.prod * pSum (earlyType σ ℓ') + xs.prod ∧
            (k - 1) * pSum (earlyType σ ℓ') + 1 ≤ t := by
        intro ℓ' _
        refine ⟨wSum_le hlt σ hσ ℓ', ?_⟩
        rcases (earlyType σ ℓ').eq_empty_or_nonempty with he | ⟨j, hj⟩
        · rw [he]
          simp only [pSum, Finset.sum_empty, mul_zero, zero_add]
          exact ht1
        · obtain ⟨x, h, _, hx, hPx⟩ := pSum_le hlt σ hσ hj
          have h1 := hstand x hx
          have h3 : (((k - 1) * pSum (earlyType σ ℓ') : ℕ) : ℤ) ≤ ((k : ℤ) - 1) * x := by
            push_cast [Nat.cast_sub hk1]
            exact mul_le_mul_of_nonneg_left (by exact_mod_cast hPx) (by linarith)
          have : (((k - 1) * pSum (earlyType σ ℓ') : ℕ) : ℤ) + 1 ≤ t := by linarith
          exact_mod_cast this
      have s1 : ∑ ℓ' ∈ (Finset.range k).erase ℓ, wSum (earlyType σ ℓ') ≤
          xs.prod * ∑ ℓ' ∈ (Finset.range k).erase ℓ, pSum (earlyType σ ℓ') + xs.prod * (k - 1) := by
        calc ∑ ℓ' ∈ (Finset.range k).erase ℓ, wSum (earlyType σ ℓ')
            ≤ ∑ ℓ' ∈ (Finset.range k).erase ℓ, (xs.prod * pSum (earlyType σ ℓ') + xs.prod) :=
              Finset.sum_le_sum (fun ℓ' h => (hb ℓ' h).1)
          _ = _ := by
              rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_const, hcard, smul_eq_mul,
                mul_comm (k - 1)]
      have s2 : (k - 1) * ∑ ℓ' ∈ (Finset.range k).erase ℓ, pSum (earlyType σ ℓ') + (k - 1) ≤
          (k - 1) * t := by
        calc (k - 1) * ∑ ℓ' ∈ (Finset.range k).erase ℓ, pSum (earlyType σ ℓ') + (k - 1)
            = ∑ ℓ' ∈ (Finset.range k).erase ℓ, ((k - 1) * pSum (earlyType σ ℓ') + 1) := by
              rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_const, hcard, smul_eq_mul,
                mul_one]
          _ ≤ ∑ ℓ' ∈ (Finset.range k).erase ℓ, t := Finset.sum_le_sum (fun ℓ' h => (hb ℓ' h).2)
          _ = (k - 1) * t := by rw [Finset.sum_const, hcard, smul_eq_mul]
      have s3 : ∑ ℓ' ∈ (Finset.range k).erase ℓ, pSum (earlyType σ ℓ') + 1 ≤ t := by
        apply Nat.le_of_mul_le_mul_left _ (show 0 < k - 1 by omega)
        rw [Nat.mul_add, Nat.mul_one]
        exact s2
      have s4 := Nat.mul_le_mul_left xs.prod s3
      have s5 : xs.prod * (k - 1) + xs.prod = xs.prod * k := by
        have : k = (k - 1) + 1 := by omega
        conv_rhs => rw [this]
        ring
      rw [Nat.mul_add, Nat.mul_one] at s4
      linarith
    · have hemp : (Finset.range k).erase ℓ = ∅ := by
        ext m
        simp only [Finset.mem_erase, Finset.mem_range, Finset.notMem_empty, iff_false, not_and]
        intro h1 h2
        omega
      rw [hemp, Finset.sum_empty]
      have := Nat.mul_le_mul_left xs.prod ht1
      have := Nat.mul_le_mul_left xs.prod hk1
      linarith
  have htot := gadget_total σ
  have htg := tardy_ge σ k
  obtain ⟨A, hA⟩ : ∃ A, A = ∑ ℓ' ∈ Finset.range k, tardyIn σ ℓ' := ⟨_, rfl⟩
  obtain ⟨B, hB⟩ : ∃ B, B = ∑ ℓ' ∈ Finset.range k, wSum (earlyType σ ℓ') := ⟨_, rfl⟩
  rw [← hA, ← hB] at htot
  rw [← hA] at htg
  rw [← hB] at hE
  have c1 : (A : ℤ) + B = k * (xs.prod * xs.sum + xs.prod * xs.length) := by exact_mod_cast htot
  have c2 : (A : ℤ) ≤ σ.tardyWeight := by exact_mod_cast htg
  have c3 : (B : ℤ) + 2 * xs.prod ≤ xs.prod * t + xs.prod * k := by exact_mod_cast hE
  have c4 : (0 : ℤ) < xs.prod := by exact_mod_cast hS
  unfold hardBound at hW
  linarith

theorem early_window {xs : List ℕ} {t k : ℕ} {L : List ℕ} (hlt : ∀ a ∈ xs, a < t)
    (σ : Schedule (hardInstance xs t k L)) (hσ : σ.Feasible)
    {j : Fin (hardInstance xs t k L).jobs.length} {ℓ : ℕ} (hj : j ∈ earlyType σ ℓ) :
    (ℓ : ℤ) * (3 * t) ≤ σ.start (σ.batch j) ∧ σ.start (σ.batch j) + t ≤ σ.comp (σ.batch j) ∧
      σ.comp (σ.batch j) < (ℓ : ℤ) * (3 * t) + 2 * t := by
  obtain ⟨x, h, _, hx, a1, a2, a3⟩ := early_facts σ hσ hj
  have : (x : ℤ) < t := by exact_mod_cast hlt x hx
  exact ⟨a1, a3, by linarith⟩

theorem job_leftover {xs : List ℕ} {t k : ℕ} {L : List ℕ}
    {j : Fin (hardInstance xs t k L).jobs.length} {e : ℕ}
    (hl : labelOf xs t k L j = .leftover e) :
    (hardInstance xs t k L).job j =
      { p := e, w := xs.prod * (k * (xs.sum + xs.length)), r := 0, d := 3 * k * t } := by
  rw [job_eq, hl]
  rfl

theorem job_cases {xs : List ℕ} {t k : ℕ} {L : List ℕ}
    (j : Fin (hardInstance xs t k L).jobs.length) :
    (∃ e, labelOf xs t k L j = .leftover e) ∨
      (∃ ℓ x h, labelOf xs t k L j = .normal ℓ x h ∧ x ∈ xs ∧ ℓ < k) := by
  have hm := labelOf_mem (xs := xs) (t := t) (k := k) (L := L) j
  obtain ⟨lab, hlab⟩ : ∃ lab, labelOf xs t k L j = lab := ⟨_, rfl⟩
  rw [hlab] at hm
  rw [hlab]
  cases lab with
  | leftover e => exact Or.inl ⟨e, rfl⟩
  | normal ℓ x h =>
    obtain ⟨hx, hℓ⟩ := mem_hardLabels_normal hm
    exact Or.inr ⟨ℓ, x, h, rfl, hx, hℓ⟩

theorem early_bounds {xs : List ℕ} {t k : ℕ} {L : List ℕ} (hlt : ∀ a ∈ xs, a < t)
    (σ : Schedule (hardInstance xs t k L)) (hσ : σ.Feasible)
    {j : Fin (hardInstance xs t k L).jobs.length} (hj : ¬ σ.IsTardy j) :
    0 ≤ σ.start (σ.batch j) ∧ σ.comp (σ.batch j) ≤ 3 * (k : ℤ) * t ∧
      σ.start (σ.batch j) + t ≤ σ.comp (σ.batch j) := by
  have hr := hσ.1 j
  have hd : ¬ ((hardInstance xs t k L).job j).d < σ.comp (σ.batch j) := hj
  have hd2 := not_lt.mp hd
  have hlen := batchLen_ge σ (σ.batch j)
  have hc : σ.comp (σ.batch j) = σ.start (σ.batch j) + σ.batchLen (σ.batch j) := rfl
  rcases job_cases j with ⟨e, hl⟩ | ⟨ℓ, x, h, hl, hx, hℓ⟩
  · rw [job_leftover hl] at hr hd2
    have hr' : (0 : ℤ) ≤ σ.start (σ.batch j) := hr
    have hd' : σ.comp (σ.batch j) ≤ 3 * (k : ℤ) * t := hd2
    exact ⟨hr', hd', by linarith⟩
  · rw [job_normal hl] at hr hd2
    have hr' := hr
    have hd' := hd2
    push_cast at hr' hd'
    have hxt : (x : ℤ) < t := by exact_mod_cast hlt x hx
    have hℓ' : (ℓ : ℤ) + 1 ≤ k := by exact_mod_cast hℓ
    have h3t : (0 : ℤ) ≤ 3 * t := by positivity
    have hm := mul_le_mul_of_nonneg_right hℓ' h3t
    have hp : (0 : ℤ) ≤ (ℓ : ℤ) * (3 * t) := by positivity
    refine ⟨by linarith, by linarith, by linarith⟩

theorem packing {ι : Type} [DecidableEq ι] (a b : ι → ℤ) (F : Finset ι)
    (hpos : ∀ i ∈ F, a i < b i)
    (hdisj : ∀ i ∈ F, ∀ j ∈ F, i ≠ j → b i ≤ a j ∨ b j ≤ a i) :
    ∀ s ⊆ F, ∀ A B : ℤ, A ≤ B → (∀ i ∈ s, A ≤ a i ∧ b i ≤ B) →
      ∑ i ∈ s, (b i - a i) ≤ B - A := by
  intro s
  induction s using Finset.induction_on_max_value a with
  | empty =>
    intro _ A B hAB _
    simp only [Finset.sum_empty]
    linarith
  | insert m s hm hmax ih =>
    intro hsub A B hAB hin
    rw [Finset.sum_insert hm]
    have hmF : m ∈ F := hsub (Finset.mem_insert_self m s)
    have hsF : s ⊆ F := fun i hi => hsub (Finset.mem_insert_of_mem hi)
    obtain ⟨hAm, hmB⟩ := hin m (Finset.mem_insert_self m s)
    have hs' : ∀ i ∈ s, A ≤ a i ∧ b i ≤ a m := by
      intro i hi
      have hiF := hsF hi
      have hne : i ≠ m := fun h => hm (h ▸ hi)
      refine ⟨(hin i (Finset.mem_insert_of_mem hi)).1, ?_⟩
      rcases hdisj i hiF m hmF hne with h | h
      · exact h
      · have h1 := hmax i hi
        have h2 := hpos m hmF
        have h3 := hpos i hiF
        linarith
    have := ih hsF A (a m) hAm hs'
    linarith

theorem early_proc_int (xs : List ℕ) (t k : ℕ) (L : List ℕ) (hnd : xs.Nodup)
    (hpos : ∀ a ∈ xs, 1 ≤ a) (hstand : ∀ a ∈ xs, ((k : ℤ) - 1) * a < t) (hlt : ∀ a ∈ xs, a < t)
    (σ : Schedule (hardInstance xs t k L)) (hσ : σ.Feasible)
    (hW : (σ.tardyWeight : ℤ) ≤ hardBound xs t k) :
    ∑ j ∈ Finset.univ.filter (fun j => ¬ σ.IsTardy j), (((hardInstance xs t k L).job j).p : ℤ) ≤
      (k : ℤ) * t := by
  have ht0 : (0 : ℤ) ≤ t := by positivity
  rcases Nat.eq_zero_or_pos k with hk0 | hkpos
  · subst hk0
    have hgoal : ∑ j ∈ Finset.univ.filter (fun j => ¬ σ.IsTardy j),
        (((hardInstance xs t 0 L).job j).p : ℤ) ≤ 0 := by
      apply Finset.sum_nonpos
      intro j hj
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
      obtain ⟨h1, h2, h3⟩ := early_bounds hlt σ hσ hj
      have hle : (((hardInstance xs t 0 L).job j).p : ℤ) ≤
          ∑ i ∈ σ.batchJobs (σ.batch j), (((hardInstance xs t 0 L).job i).p : ℤ) :=
        Finset.single_le_sum (f := fun i => (((hardInstance xs t 0 L).job i).p : ℤ))
          (fun i _ => by positivity) (by simp [Schedule.batchJobs])
      have hb := batchLen_eq σ (σ.batch j)
      have hc : σ.comp (σ.batch j) = σ.start (σ.batch j) + σ.batchLen (σ.batch j) := rfl
      have h2' : σ.comp (σ.batch j) ≤ 0 := by
        have := h2
        simp only [Nat.cast_zero, mul_zero, zero_mul] at this
        exact this
      linarith
    have : ((0 : ℕ) : ℤ) * t = 0 := by simp
    rw [this]
    exact hgoal
  have hk1 : 1 ≤ k := hkpos
  have hall := all_nonempty xs t k L hnd hpos hstand σ hσ hW
  have ht1 : (1 : ℤ) ≤ t := by
    obtain ⟨j, hj⟩ := hall 0 hkpos
    obtain ⟨x, h, _, hx, _⟩ := early_facts σ hσ hj
    have := hlt x hx
    have : 1 ≤ t := by omega
    exact_mod_cast this
  have hβex : ∀ ℓ : ℕ, ∃ b : ℕ, ℓ < k → ∃ j ∈ earlyType σ ℓ, σ.batch j = b := by
    intro ℓ
    by_cases h : ℓ < k
    · obtain ⟨j, hj⟩ := hall ℓ h
      exact ⟨σ.batch j, fun _ => ⟨j, hj, rfl⟩⟩
    · exact ⟨0, fun h' => absurd h' h⟩
  choose β hβ using hβex
  have hwin : ∀ ℓ < k, (ℓ : ℤ) * (3 * t) ≤ σ.start (β ℓ) ∧ σ.start (β ℓ) + t ≤ σ.comp (β ℓ) ∧
      σ.comp (β ℓ) < (ℓ : ℤ) * (3 * t) + 2 * t := by
    intro ℓ hℓ
    obtain ⟨j, hj, hjb⟩ := hβ ℓ hℓ
    rw [← hjb]
    exact early_window hlt σ hσ hj
  have hβused : ∀ ℓ < k, σ.Used (β ℓ) := by
    intro ℓ hℓ
    obtain ⟨j, _, hjb⟩ := hβ ℓ hℓ
    exact ⟨j, hjb⟩
  have h3t : (0 : ℤ) ≤ 3 * t := by positivity
  have hβinj : ∀ ℓ < k, ∀ ℓ' < k, β ℓ = β ℓ' → ℓ = ℓ' := by
    intro ℓ hℓ ℓ' hℓ' heq
    by_contra hne
    obtain ⟨a1, a2, a3⟩ := hwin ℓ hℓ
    obtain ⟨b1, b2, b3⟩ := hwin ℓ' hℓ'
    rw [heq] at a1 a2 a3
    rcases Nat.lt_or_gt_of_ne hne with h | h
    · have h' : (ℓ : ℤ) + 1 ≤ ℓ' := by exact_mod_cast h
      have := mul_le_mul_of_nonneg_right h' h3t
      linarith
    · have h' : (ℓ' : ℤ) + 1 ≤ ℓ := by exact_mod_cast h
      have := mul_le_mul_of_nonneg_right h' h3t
      linarith
  obtain ⟨Bs, hBs⟩ : ∃ Bs : Finset ℕ,
      Bs = (Finset.univ.filter (fun j => ¬ σ.IsTardy j)).image σ.batch := ⟨_, rfl⟩
  have hBmem : ∀ b ∈ Bs, ∃ j, ¬ σ.IsTardy j ∧ σ.batch j = b := by
    intro b hb
    rw [hBs, Finset.mem_image] at hb
    obtain ⟨j, hj, hjb⟩ := hb
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
    exact ⟨j, hj, hjb⟩
  have hBfacts : ∀ b ∈ Bs, 0 ≤ σ.start b ∧ σ.comp b ≤ 3 * (k : ℤ) * t ∧
      σ.start b + t ≤ σ.comp b ∧ σ.Used b := by
    intro b hb
    obtain ⟨j, hj, rfl⟩ := hBmem b hb
    obtain ⟨h1, h2, h3⟩ := early_bounds hlt σ hσ hj
    exact ⟨h1, h2, h3, ⟨j, rfl⟩⟩
  -- Step A: early processing is at most the processing of the early batches
  have hA : ∑ j ∈ Finset.univ.filter (fun j => ¬ σ.IsTardy j),
      (((hardInstance xs t k L).job j).p : ℤ) ≤ ∑ b ∈ Bs, (σ.comp b - σ.start b - t) := by
    rw [← Finset.sum_fiberwise_of_maps_to (s := Finset.univ.filter (fun j => ¬ σ.IsTardy j))
      (t := Bs) (g := σ.batch) (fun j hj => by rw [hBs]; exact Finset.mem_image_of_mem _ hj)]
    apply Finset.sum_le_sum
    intro b _
    have hsub : (Finset.univ.filter (fun j => ¬ σ.IsTardy j)).filter (fun j => σ.batch j = b) ⊆
        σ.batchJobs b := by
      intro j hj
      simp only [Finset.mem_filter] at hj
      simp only [Schedule.batchJobs, Finset.mem_filter, Finset.mem_univ, true_and]
      exact hj.2
    calc _ ≤ ∑ j ∈ σ.batchJobs b, (((hardInstance xs t k L).job j).p : ℤ) :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
      _ = σ.comp b - σ.start b - t := by
          have hb' := batchLen_eq σ b
          have hc : σ.comp b = σ.start b + σ.batchLen b := rfl
          rw [hc, hb']
          ring
  -- Step B: split off the gadget batches
  have himg : (Finset.range k).image β ⊆ Bs := by
    intro b hb
    rw [Finset.mem_image] at hb
    obtain ⟨ℓ, hℓ, rfl⟩ := hb
    obtain ⟨j, hj, hjb⟩ := hβ ℓ (Finset.mem_range.mp hℓ)
    rw [hBs, ← hjb]
    apply Finset.mem_image_of_mem
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact (mem_earlyType.mp hj).2
  have hinjOn : Set.InjOn β (Finset.range k : Set ℕ) := by
    intro ℓ hℓ ℓ' hℓ' heq
    exact hβinj ℓ (Finset.mem_range.mp hℓ) ℓ' (Finset.mem_range.mp hℓ') heq
  have e1 : ∑ b ∈ (Finset.range k).image β, (σ.comp b - σ.start b - t) =
      ∑ ℓ ∈ Finset.range k, (σ.comp (β ℓ) - σ.start (β ℓ) - t) := Finset.sum_image hinjOn
  have e2 := Finset.sum_sdiff himg (f := fun b => σ.comp b - σ.start b - (t : ℤ))
  have hsplit : ∑ b ∈ Bs, (σ.comp b - σ.start b - t) =
      ∑ b ∈ Bs \ (Finset.range k).image β, (σ.comp b - σ.start b - t) +
        ∑ ℓ ∈ Finset.range k, (σ.comp (β ℓ) - σ.start (β ℓ) - t) := by
    rw [← e1]
    exact e2.symm
  -- Step C: the other batches lie in the gaps between gadget batches
  obtain ⟨O, hO⟩ : ∃ O : Finset ℕ, O = Bs \ (Finset.range k).image β := ⟨_, rfl⟩
  rw [← hO] at hsplit
  have hOmem : ∀ o ∈ O, o ∈ Bs ∧ ∀ ℓ < k, o ≠ β ℓ := by
    intro o ho
    rw [hO, Finset.mem_sdiff] at ho
    refine ⟨ho.1, fun ℓ hℓ heq => ho.2 ?_⟩
    rw [Finset.mem_image]
    exact ⟨ℓ, Finset.mem_range.mpr hℓ, heq.symm⟩
  have hOdisj : ∀ o ∈ O, ∀ ℓ < k,
      σ.comp o ≤ σ.start (β ℓ) ∨ σ.comp (β ℓ) ≤ σ.start o := by
    intro o ho ℓ hℓ
    obtain ⟨hoB, hne⟩ := hOmem o ho
    exact hσ.2 o (β ℓ) (hBfacts o hoB).2.2.2 (hβused ℓ hℓ) (hne ℓ hℓ)
  have hex : ∀ b : ℕ, ∃ ℓ : ℕ, ℓ = k ∨ σ.comp b ≤ σ.start (β ℓ) := fun b => ⟨k, Or.inl rfl⟩
  obtain ⟨g, hg1, hg2, hg3⟩ : ∃ g : ℕ → ℕ, (∀ b, g b ≤ k) ∧
      (∀ b, g b = k ∨ σ.comp b ≤ σ.start (β (g b))) ∧
      (∀ b, ∀ m < g b, ¬ m = k ∧ ¬ σ.comp b ≤ σ.start (β m)) :=
    ⟨fun b => Nat.find (hex b), fun b => Nat.find_min' (hex b) (Or.inl rfl),
      fun b => Nat.find_spec (hex b), fun b m hm => not_or.mp (Nat.find_min (hex b) hm)⟩
  obtain ⟨V, hV⟩ : ∃ V : ℕ → ℤ, ∀ m, V m = if m < k then σ.start (β m) else 3 * (k : ℤ) * t :=
    ⟨_, fun _ => rfl⟩
  have hfib : ∑ o ∈ O, (σ.comp o - σ.start o - t) =
      ∑ ℓ ∈ Finset.range (k + 1), ∑ o ∈ O with g o = ℓ, (σ.comp o - σ.start o - t) :=
    (Finset.sum_fiberwise_of_maps_to (fun o _ => Finset.mem_range.mpr
      (Nat.lt_succ_of_le (hg1 o))) _).symm
  have hne0 : ∀ o ∈ O, g o ≠ 0 := by
    intro o ho h0
    obtain ⟨hoB, _⟩ := hOmem o ho
    obtain ⟨f1, f2, f3, _⟩ := hBfacts o hoB
    obtain ⟨w1, w2, w3⟩ := hwin 0 hkpos
    rcases hg2 o with h | h
    · omega
    · rw [h0] at h
      simp only [Nat.cast_zero, zero_mul, zero_add] at w1 w3
      linarith
  have hfib0 : ∑ o ∈ O with g o = 0, (σ.comp o - σ.start o - t) = 0 := by
    apply Finset.sum_eq_zero
    intro o ho
    rw [Finset.mem_filter] at ho
    exact absurd ho.2 (hne0 o ho.1)
  have hgap : ∀ ℓ < k, ∑ o ∈ O with g o = ℓ + 1, (σ.comp o - σ.start o - t) ≤
      V (ℓ + 1) - σ.comp (β ℓ) - t := by
    intro ℓ hℓ
    have hlow : ∀ o ∈ O.filter (fun o => g o = ℓ + 1), σ.comp (β ℓ) ≤ σ.start o := by
      intro o ho
      rw [Finset.mem_filter] at ho
      obtain ⟨ho1, ho2⟩ := ho
      have h3 := (hg3 o ℓ (by omega)).2
      rcases hOdisj o ho1 ℓ hℓ with h | h
      · exact absurd h h3
      · exact h
    have hup : ∀ o ∈ O.filter (fun o => g o = ℓ + 1), σ.comp o ≤ V (ℓ + 1) := by
      intro o ho
      rw [Finset.mem_filter] at ho
      obtain ⟨ho1, ho2⟩ := ho
      obtain ⟨hoB, _⟩ := hOmem o ho1
      obtain ⟨f1, f2, f3, _⟩ := hBfacts o hoB
      rw [hV]
      by_cases hl : ℓ + 1 < k
      · rw [if_pos hl]
        rcases hg2 o with h | h
        · omega
        · rw [ho2] at h
          exact h
      · rw [if_neg hl]
        exact f2
    have hgapt : (t : ℤ) ≤ V (ℓ + 1) - σ.comp (β ℓ) := by
      obtain ⟨w1, w2, w3⟩ := hwin ℓ hℓ
      rw [hV]
      by_cases hl : ℓ + 1 < k
      · rw [if_pos hl]
        obtain ⟨v1, v2, v3⟩ := hwin (ℓ + 1) hl
        push_cast at v1
        linarith
      · rw [if_neg hl]
        have h' : (ℓ : ℤ) + 1 ≤ k := by exact_mod_cast hℓ
        have := mul_le_mul_of_nonneg_right h' h3t
        linarith
    by_cases hF : (O.filter (fun o => g o = ℓ + 1)).Nonempty
    · have hpack := packing σ.start σ.comp O
        (fun i hi => by
          obtain ⟨f1, f2, f3, _⟩ := hBfacts i (hOmem i hi).1
          linarith)
        (fun i hi j hj hij =>
          hσ.2 i j (hBfacts i (hOmem i hi).1).2.2.2 (hBfacts j (hOmem j hj).1).2.2.2 hij)
        (O.filter (fun o => g o = ℓ + 1)) (Finset.filter_subset _ _) (σ.comp (β ℓ)) (V (ℓ + 1))
        (by
          obtain ⟨o, ho⟩ := hF
          have := hlow o ho
          have := hup o ho
          obtain ⟨f1, f2, f3, _⟩ := hBfacts o (hOmem o (Finset.mem_filter.mp ho).1).1
          linarith)
        (fun i hi => ⟨hlow i hi, hup i hi⟩)
      have hcard : 1 ≤ (O.filter (fun o => g o = ℓ + 1)).card := Finset.card_pos.mpr hF
      have hcardz : (1 : ℤ) ≤ ((O.filter (fun o => g o = ℓ + 1)).card : ℤ) := by
        exact_mod_cast hcard
      have hsum : ∑ o ∈ O with g o = ℓ + 1, (σ.comp o - σ.start o - t) =
          ∑ o ∈ O with g o = ℓ + 1, (σ.comp o - σ.start o) -
            ((O.filter (fun o => g o = ℓ + 1)).card : ℤ) * t := by
        rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
      rw [hsum]
      have : (t : ℤ) ≤ ((O.filter (fun o => g o = ℓ + 1)).card : ℤ) * t := by nlinarith
      linarith
    · rw [Finset.not_nonempty_iff_eq_empty] at hF
      rw [hF, Finset.sum_empty]
      linarith
  -- assemble
  have hO_le : ∑ o ∈ O, (σ.comp o - σ.start o - t) ≤
      ∑ ℓ ∈ Finset.range k, (V (ℓ + 1) - σ.comp (β ℓ) - t) := by
    rw [hfib, Finset.sum_range_succ', hfib0, add_zero]
    exact Finset.sum_le_sum (fun ℓ hℓ => hgap ℓ (Finset.mem_range.mp hℓ))
  have htel : ∑ ℓ ∈ Finset.range k, V (ℓ + 1) =
      ∑ ℓ ∈ Finset.range k, σ.start (β ℓ) - σ.start (β 0) + 3 * (k : ℤ) * t := by
    have h1 := Finset.sum_range_succ' V k
    have h2 := Finset.sum_range_succ V k
    have hVk : V k = 3 * (k : ℤ) * t := by rw [hV, if_neg (lt_irrefl k)]
    have hV0 : V 0 = σ.start (β 0) := by rw [hV, if_pos hkpos]
    have hVs : ∑ ℓ ∈ Finset.range k, V ℓ = ∑ ℓ ∈ Finset.range k, σ.start (β ℓ) :=
      Finset.sum_congr rfl (fun ℓ hℓ => by rw [hV, if_pos (Finset.mem_range.mp hℓ)])
    rw [hVk, hVs] at h2
    rw [hV0] at h1
    linarith
  have hs1 : ∑ ℓ ∈ Finset.range k, (V (ℓ + 1) - σ.comp (β ℓ) - t) =
      ∑ ℓ ∈ Finset.range k, V (ℓ + 1) - ∑ ℓ ∈ Finset.range k, σ.comp (β ℓ) - (k : ℤ) * t := by
    rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range,
      nsmul_eq_mul]
  have hs2 : ∑ ℓ ∈ Finset.range k, (σ.comp (β ℓ) - σ.start (β ℓ) - t) =
      ∑ ℓ ∈ Finset.range k, σ.comp (β ℓ) - ∑ ℓ ∈ Finset.range k, σ.start (β ℓ) - (k : ℤ) * t := by
    rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range,
      nsmul_eq_mul]
  have hs0 : 0 ≤ σ.start (β 0) := by
    obtain ⟨w1, _, _⟩ := hwin 0 hkpos
    simp only [Nat.cast_zero, zero_mul] at w1
    exact w1
  linarith


end Aux_SerialBatchTardy_early_processing_le


open SerialBatchTardy Aux_SerialBatchTardy_early_processing_le in
theorem solution (xs : List ℕ) (t k : ℕ) (L : List ℕ) (hnd : xs.Nodup)
    (hpos : ∀ a ∈ xs, 1 ≤ a) (hstand : ∀ a ∈ xs, ((k : ℤ) - 1) * a < t) (hlt : ∀ a ∈ xs, a < t)
    (σ : Schedule (hardInstance xs t k L)) (hσ : σ.Feasible)
    (hW : (σ.tardyWeight : ℤ) ≤ hardBound xs t k) :
    ∑ j ∈ Finset.univ.filter (fun j => ¬ σ.IsTardy j), ((hardInstance xs t k L).job j).p ≤
      k * t := by
  have H := early_proc_int xs t k L hnd hpos hstand hlt σ hσ hW
  exact_mod_cast H
