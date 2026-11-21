-- Prove2me | solution 1 for SerialBatchTardy.lemma_9
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-21T01:07:33.121152+00:00
-- url     : https://prove2.me/submissions/764c526e-8936-4ea7-9f55-12fd8999a6dc

import Mathlib
import Definitions.Def_SerialBatchTardy_Construction
set_option autoImplicit false

namespace Aux_SerialBatchTardy_lemma_9

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


end Aux_SerialBatchTardy_lemma_9


open SerialBatchTardy Aux_SerialBatchTardy_lemma_9 in
theorem solution (xs : List ℕ) (t k : ℕ) (L : List ℕ) (hnd : xs.Nodup) (hpos : ∀ a ∈ xs, 1 ≤ a)
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
