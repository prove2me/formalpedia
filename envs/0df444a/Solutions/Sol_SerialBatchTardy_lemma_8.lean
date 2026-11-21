-- Prove2me | solution 1 for SerialBatchTardy.lemma_8
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-21T01:52:25.775897+00:00
-- url     : https://prove2.me/submissions/46d658f0-928d-4fae-b5ad-4a989551ab45

import Mathlib
import Definitions.Def_SerialBatchTardy_Construction
set_option autoImplicit false

namespace Aux_SerialBatchTardy_lemma_8

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

theorem labelOf_val {xs : List ℕ} {t k : ℕ} {L : List ℕ}
    (j : Fin (hardInstance xs t k L).jobs.length) :
    labelOf xs t k L j = (hardLabels xs k L)[j.val]'(by
      have := j.isLt
      simpa [hardInstance] using this) := rfl

theorem label_lt {xs : List ℕ} {t k : ℕ} {L : List ℕ}
    (j : Fin (hardInstance xs t k L).jobs.length) (h : j.val < L.length) :
    labelOf xs t k L j = .leftover (L.get ⟨j.val, h⟩) := by
  rw [labelOf_val]
  have h' : j.val < (L.map JobLabel.leftover).length := by simpa using h
  simp only [hardLabels]
  rw [List.getElem_append_left h', List.getElem_map]
  try rfl

theorem not_leftover_mem {xs : List ℕ} {k : ℕ} {e : ℕ}
    (hm : JobLabel.leftover e ∈ (List.range k).flatMap
      (fun ℓ => xs.flatMap fun x => gadgetLabels xs ℓ x)) : False := by
  obtain ⟨ℓ', _, h2⟩ := List.mem_flatMap.mp hm
  obtain ⟨x', _, h3⟩ := List.mem_flatMap.mp h2
  unfold gadgetLabels at h3
  obtain ⟨h', _, h4⟩ := List.mem_flatMap.mp h3
  have h5 := (List.mem_replicate.mp h4).2
  cases h5

theorem label_ge {xs : List ℕ} {t k : ℕ} {L : List ℕ}
    (j : Fin (hardInstance xs t k L).jobs.length) (h : ¬ j.val < L.length) :
    ∃ ℓ x hh, labelOf xs t k L j = .normal ℓ x hh ∧ x ∈ xs ∧ ℓ < k := by
  rcases job_cases j with ⟨e, hl⟩ | hn
  · exfalso
    have h' : (L.map JobLabel.leftover).length ≤ j.val := by simp; omega
    rw [labelOf_val] at hl
    simp only [hardLabels] at hl
    rw [List.getElem_append_right h'] at hl
    apply not_leftover_mem (xs := xs) (k := k) (e := e)
    rw [← hl]
    apply List.getElem_mem
  · exact hn

/-! ## The schedule of the forward direction -/

def xvF (xs : List ℕ) (k : ℕ) (π : Fin k → Fin xs.length) (ℓ : ℕ) : ℕ :=
  if h : ℓ < k then xs.get (π ⟨ℓ, h⟩) else 0

def nb (k : ℕ) (v : ℕ → ℕ) : JobLabel → ℕ
  | .leftover _ => 2 * k
  | .normal ℓ x _ => if x = v ℓ then 2 * ℓ else 2 * k

def stF (t k : ℕ) (v : ℕ → ℕ) (b : ℕ) : ℤ :=
  if b < 2 * k then
    (if b % 2 = 0 then 3 * ((b / 2 : ℕ) : ℤ) * t else 3 * ((b / 2 : ℕ) : ℤ) * t + t + v (b / 2))
  else 3 * (k : ℤ) * t

def schedF (xs : List ℕ) (t k : ℕ) (L : List ℕ) (π : Fin k → Fin xs.length)
    (a : Fin L.length → Fin k) : Schedule (hardInstance xs t k L) where
  batch j := if h : j.val < L.length then 2 * (a ⟨j.val, h⟩).val + 1
    else nb k (xvF xs k π) (labelOf xs t k L j)
  start := stF t k (xvF xs k π)

theorem stF_even (t k : ℕ) (v : ℕ → ℕ) (ℓ : ℕ) (h : ℓ < k) :
    stF t k v (2 * ℓ) = 3 * (ℓ : ℤ) * t := by
  unfold stF
  rw [if_pos (show 2 * ℓ < 2 * k by omega), if_pos (show 2 * ℓ % 2 = 0 by omega)]
  have : 2 * ℓ / 2 = ℓ := by omega
  rw [this]

theorem stF_odd (t k : ℕ) (v : ℕ → ℕ) (ℓ : ℕ) (h : ℓ < k) :
    stF t k v (2 * ℓ + 1) = 3 * (ℓ : ℤ) * t + t + v ℓ := by
  unfold stF
  rw [if_pos (show 2 * ℓ + 1 < 2 * k by omega), if_neg (show ¬ ((2 * ℓ + 1) % 2 = 0) by omega)]
  have : (2 * ℓ + 1) / 2 = ℓ := by omega
  rw [this]

theorem stF_top (t k : ℕ) (v : ℕ → ℕ) : stF t k v (2 * k) = 3 * (k : ℤ) * t := by
  unfold stF
  rw [if_neg (show ¬ (2 * k < 2 * k) by omega)]

theorem stF_nonneg (t k : ℕ) (v : ℕ → ℕ) (b : ℕ) : 0 ≤ stF t k v b := by
  unfold stF
  split_ifs <;> positivity

theorem list_ite_single (v : ℕ) (f : ℕ → ℕ) : ∀ ys : List ℕ, ys.Nodup → v ∈ ys →
    (ys.map fun x => if x = v then f x else 0).sum = f v := by
  intro ys
  induction ys with
  | nil => intro _ h; simp at h
  | cons y ys ih =>
    intro hnd hv
    rw [List.nodup_cons] at hnd
    simp only [List.map_cons, List.sum_cons]
    by_cases hy : y = v
    · subst hy
      rw [if_pos rfl]
      have : (ys.map fun x => if x = y then f x else 0).sum = 0 := by
        apply lsum_zero
        intro x hx
        have : x ≠ y := fun h => hnd.1 (h ▸ hx)
        simp [this]
      rw [this, add_zero]
    · rw [if_neg hy, zero_add]
      have hv' : v ∈ ys := by
        rcases List.mem_cons.mp hv with h | h
        · exact absurd h.symm hy
        · exact h
      exact ih hnd.2 hv'

theorem list_ite_compl (v : ℕ) (f : ℕ → ℕ) : ∀ ys : List ℕ, ys.Nodup → v ∈ ys →
    (ys.map fun x => if x = v then 0 else f x).sum + f v = (ys.map f).sum := by
  intro ys
  induction ys with
  | nil => intro _ h; simp at h
  | cons y ys ih =>
    intro hnd hv
    rw [List.nodup_cons] at hnd
    simp only [List.map_cons, List.sum_cons]
    by_cases hy : y = v
    · subst hy
      rw [if_pos rfl]
      have : (ys.map fun x => if x = y then 0 else f x) = ys.map f := by
        apply List.map_congr_left
        intro x hx
        have : x ≠ y := fun h => hnd.1 (h ▸ hx)
        simp [this]
      rw [this]
      ring
    · rw [if_neg hy]
      have hv' : v ∈ ys := by
        rcases List.mem_cons.mp hv with h | h
        · exact absurd h.symm hy
        · exact h
      have := ih hnd.2 hv'
      omega

theorem xvF_mem {xs : List ℕ} {k : ℕ} (π : Fin k → Fin xs.length) (ℓ : ℕ) (h : ℓ < k) :
    xvF xs k π ℓ ∈ xs := by
  unfold xvF
  rw [dif_pos h]
  exact List.get_mem _ _

theorem jobs_len_ge {xs : List ℕ} {t k : ℕ} {L : List ℕ} :
    L.length ≤ (hardInstance xs t k L).jobs.length := by
  simp [hardInstance, hardLabels]

section Forward

variable {xs : List ℕ} {t k : ℕ} {L : List ℕ} (π : Fin k → Fin xs.length)
  (a : Fin L.length → Fin k)

theorem batch_lt (j : Fin (hardInstance xs t k L).jobs.length) (h : j.val < L.length) :
    (schedF xs t k L π a).batch j = 2 * (a ⟨j.val, h⟩).val + 1 := by
  show (if h : j.val < L.length then 2 * (a ⟨j.val, h⟩).val + 1
    else nb k (xvF xs k π) (labelOf xs t k L j)) = _
  rw [dif_pos h]

theorem batch_ge (j : Fin (hardInstance xs t k L).jobs.length) (h : ¬ j.val < L.length) :
    (schedF xs t k L π a).batch j = nb k (xvF xs k π) (labelOf xs t k L j) := by
  show (if h : j.val < L.length then 2 * (a ⟨j.val, h⟩).val + 1
    else nb k (xvF xs k π) (labelOf xs t k L j)) = _
  rw [dif_neg h]

theorem batch_le (j : Fin (hardInstance xs t k L).jobs.length) :
    (schedF xs t k L π a).batch j ≤ 2 * k := by
  by_cases h : j.val < L.length
  · rw [batch_lt π a j h]
    have := (a ⟨j.val, h⟩).isLt
    omega
  · rw [batch_ge π a j h]
    obtain ⟨ℓ, x, hh, hl, _, hℓ⟩ := label_ge j h
    rw [hl]
    simp only [nb]
    split_ifs <;> omega

/-- processing in an even batch -/
theorem proc_even (hnd : xs.Nodup) (ℓ : ℕ) (hℓ : ℓ < k) :
    ∑ j ∈ (schedF xs t k L π a).batchJobs (2 * ℓ), ((hardInstance xs t k L).job j).p =
      xvF xs k π ℓ := by
  unfold Schedule.batchJobs
  rw [Finset.sum_filter]
  let F : JobLabel → ℕ := fun lab => match lab with
    | .leftover _ => 0
    | .normal ℓ' x h => if ℓ' = ℓ ∧ x = xvF xs k π ℓ then xs.length ^ h else 0
  have hpt : ∀ j : Fin (hardInstance xs t k L).jobs.length,
      (if (schedF xs t k L π a).batch j = 2 * ℓ then ((hardInstance xs t k L).job j).p else 0) =
        F (labelOf xs t k L j) := by
    intro j
    by_cases h : j.val < L.length
    · rw [batch_lt π a j h, label_lt j h]
      have : 2 * (a ⟨j.val, h⟩).val + 1 ≠ 2 * ℓ := by omega
      rw [if_neg this]
    · obtain ⟨ℓ', x, hh, hl, _, hℓ'⟩ := label_ge j h
      rw [batch_ge π a j h, hl, job_normal hl]
      by_cases hx : x = xvF xs k π ℓ'
      · have hnb : nb k (xvF xs k π) (.normal ℓ' x hh) = 2 * ℓ' := by
          simp only [nb, if_pos hx]
        rw [hnb]
        by_cases he : ℓ' = ℓ
        · subst he
          rw [if_pos rfl]
          simp [F, hx]
        · rw [if_neg (show 2 * ℓ' ≠ 2 * ℓ by omega)]
          simp [F, he]
      · have hnb : nb k (xvF xs k π) (.normal ℓ' x hh) = 2 * k := by
          simp only [nb, if_neg hx]
        rw [hnb, if_neg (show 2 * k ≠ 2 * ℓ by omega)]
        by_cases he : ℓ' = ℓ
        · subst he
          simp [F, hx]
        · simp [F, he]
  rw [Finset.sum_congr rfl (fun j _ => hpt j), sum_jobs F]
  rw [hard_sum xs k L F (fun ℓ' x => if ℓ' = ℓ ∧ x = xvF xs k π ℓ then 1 else 0)
    (fun e => rfl) (fun ℓ' x h => by
      simp only [F]
      split_ifs <;> simp)]
  rw [Finset.sum_eq_single_of_mem ℓ (Finset.mem_range.mpr hℓ)]
  · refine (congrArg List.sum (List.map_congr_left (fun x _ => ?_))).trans
      (list_ite_single _ (fun x => x) xs hnd (xvF_mem π ℓ hℓ))
    by_cases hx : x = xvF xs k π ℓ <;> simp [hx]
  · intro b _ hb
    apply lsum_zero
    intro x _
    simp [hb]

/-- processing in an odd batch -/
theorem proc_odd (ℓ : ℕ) (hℓ : ℓ < k)
    (ha : ∀ ℓ, (∑ i ∈ Finset.univ.filter (fun i => a i = ℓ), L.get i) + xs.get (π ℓ) = t) :
    ∑ j ∈ (schedF xs t k L π a).batchJobs (2 * ℓ + 1), ((hardInstance xs t k L).job j).p +
      xvF xs k π ℓ = t := by
  unfold Schedule.batchJobs
  rw [Finset.sum_filter]
  let Φ : ℕ → ℕ := fun m => if h : m < L.length then
    (if (a ⟨m, h⟩).val = ℓ then L.get ⟨m, h⟩ else 0) else 0
  have hpt : ∀ j : Fin (hardInstance xs t k L).jobs.length,
      (if (schedF xs t k L π a).batch j = 2 * ℓ + 1 then ((hardInstance xs t k L).job j).p
        else 0) = Φ j.val := by
    intro j
    by_cases h : j.val < L.length
    · rw [batch_lt π a j h]
      simp only [Φ, dif_pos h]
      have hp : ((hardInstance xs t k L).job j).p = L.get ⟨j.val, h⟩ := by
        rw [job_leftover (label_lt j h)]
      by_cases hal : (a ⟨j.val, h⟩).val = ℓ
      · rw [if_pos (show 2 * (a ⟨j.val, h⟩).val + 1 = 2 * ℓ + 1 by omega), if_pos hal, hp]
      · rw [if_neg (show ¬ (2 * (a ⟨j.val, h⟩).val + 1 = 2 * ℓ + 1) by omega), if_neg hal]
    · obtain ⟨ℓ', x, hh, hl, _, hℓ'⟩ := label_ge j h
      rw [batch_ge π a j h, hl]
      have key : nb k (xvF xs k π) (.normal ℓ' x hh) ≠ 2 * ℓ + 1 := by
        simp only [nb]
        split_ifs <;> omega
      rw [if_neg key]
      simp only [Φ, dif_neg h]
  rw [Finset.sum_congr rfl (fun j _ => hpt j)]
  have e1 : ∑ j : Fin (hardInstance xs t k L).jobs.length, Φ j.val =
      ∑ m ∈ Finset.range (hardInstance xs t k L).jobs.length, Φ m :=
    Fin.sum_univ_eq_sum_range Φ _
  have e2 : ∑ m ∈ Finset.range L.length, Φ m =
      ∑ m ∈ Finset.range (hardInstance xs t k L).jobs.length, Φ m := by
    apply Finset.sum_subset
    · intro m hm
      rw [Finset.mem_range] at hm ⊢
      exact lt_of_lt_of_le hm jobs_len_ge
    · intro m _ hm
      rw [Finset.mem_range] at hm
      simp only [Φ, dif_neg hm]
  have e3 : ∑ i : Fin L.length, Φ i.val = ∑ m ∈ Finset.range L.length, Φ m :=
    Fin.sum_univ_eq_sum_range Φ _
  have e4 : ∑ i : Fin L.length, Φ i.val =
      ∑ i ∈ Finset.univ.filter (fun i => a i = ⟨ℓ, hℓ⟩), L.get i := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro i _
    simp only [Φ, dif_pos i.isLt, Fin.eta]
    have : (a i = ⟨ℓ, hℓ⟩) ↔ (a i).val = ℓ := Fin.ext_iff
    by_cases hai : (a i).val = ℓ
    · rw [if_pos hai, if_pos (this.mpr hai)]
    · rw [if_neg hai, if_neg (fun h => hai (this.mp h))]
  have hv : xvF xs k π ℓ = xs.get (π ⟨ℓ, hℓ⟩) := by
    unfold xvF
    rw [dif_pos hℓ]
  rw [e1, ← e2, ← e3, e4, hv]
  exact ha ⟨ℓ, hℓ⟩

end Forward

theorem wSum_decomp2 {xs : List ℕ} {t k : ℕ} {L : List ℕ} (hlt : ∀ a ∈ xs, a < t)
    (σ : Schedule (hardInstance xs t k L)) (hσ : σ.Feasible) (ℓ : ℕ) :
    ∃ v : Fin (hardInstance xs t k L).jobs.length → ℕ,
      (∀ j ∈ earlyType σ ℓ, pSum (earlyType σ ℓ) ≤ v j ∧ v j ∣ xs.prod ∧ v j ∈ xs ∧
        (labelOf xs t k L j).value? = some (v j) ∧ 0 < ((hardInstance xs t k L).job j).p) ∧
      wSum (earlyType σ ℓ) = xs.prod * pSum (earlyType σ ℓ) +
        ∑ j ∈ earlyType σ ℓ, ((hardInstance xs t k L).job j).p * (xs.prod / v j) := by
  let v : Fin (hardInstance xs t k L).jobs.length → ℕ :=
    fun j => ((labelOf xs t k L j).value?).getD 0
  have key : ∀ j ∈ earlyType σ ℓ,
      ((hardInstance xs t k L).job j).w = ((hardInstance xs t k L).job j).p * xs.prod +
        ((hardInstance xs t k L).job j).p * (xs.prod / v j) ∧
      pSum (earlyType σ ℓ) ≤ v j ∧ v j ∣ xs.prod ∧ v j ∈ xs ∧
        (labelOf xs t k L j).value? = some (v j) ∧ 0 < ((hardInstance xs t k L).job j).p := by
    intro j hj
    obtain ⟨x, h, hl, hx, hPx⟩ := pSum_le hlt σ hσ hj
    have hv : v j = x := by simp only [v, hl, JobLabel.value?, Option.getD_some]
    have hn : 0 < xs.length := List.length_pos_of_mem hx
    rw [job_normal hl, hv, hl]
    refine ⟨?_, hPx, List.dvd_prod hx, hx, rfl, ?_⟩
    · dsimp only
      ring
    · dsimp only
      exact pow_pos hn h
  refine ⟨v, fun j hj => (key j hj).2, ?_⟩
  unfold wSum pSum
  rw [Finset.sum_congr rfl (fun j hj => (key j hj).1), Finset.sum_add_distrib, Finset.mul_sum]
  congr 1
  exact Finset.sum_congr rfl (fun j _ => by ring)

theorem gset_sum {xs : List ℕ} {t k : ℕ} {L : List ℕ} (hnd : xs.Nodup) {ℓ x0 : ℕ}
    (hℓ : ℓ < k) (hx0 : x0 ∈ xs) (Ψ : Job → ℕ) (c : ℕ)
    (hΨ : ∀ h, Ψ (labelJob xs t k (.normal ℓ x0 h)) = xs.length ^ h * c) :
    ∑ j ∈ gadgetSet xs t k L ℓ x0, Ψ ((hardInstance xs t k L).job j) = x0 * c := by
  unfold gadgetSet
  rw [Finset.sum_filter]
  simp only [job_eq]
  let F : JobLabel → ℕ := fun lab =>
    if lab.gadget? = some ℓ ∧ lab.value? = some x0 then Ψ (labelJob xs t k lab) else 0
  refine (sum_jobs (xs := xs) (t := t) (k := k) (L := L) F).trans ?_
  refine (hard_sum xs k L F (fun ℓ' x => if ℓ' = ℓ ∧ x = x0 then c else 0) ?_ ?_).trans ?_
  · intro e
    simp [F, JobLabel.gadget?]
  · intro ℓ' x h
    by_cases hc : ℓ' = ℓ ∧ x = x0
    · obtain ⟨rfl, rfl⟩ := hc
      simp [F, JobLabel.gadget?, JobLabel.value?, hΨ]
    · have hc' : ¬ (JobLabel.normal ℓ' x h).gadget? = some ℓ ∨
          ¬ (JobLabel.normal ℓ' x h).value? = some x0 := by
        simp only [JobLabel.gadget?, JobLabel.value?, Option.some.injEq]
        tauto
      have : ¬ ((JobLabel.normal ℓ' x h).gadget? = some ℓ ∧
          (JobLabel.normal ℓ' x h).value? = some x0) := by tauto
      simp only [F, if_neg this, if_neg hc, mul_zero]
  · rw [Finset.sum_eq_single_of_mem ℓ (Finset.mem_range.mpr hℓ)]
    · refine (congrArg List.sum (List.map_congr_left (fun x _ => ?_))).trans
        (list_ite_single x0 (fun x => x * c) xs hnd hx0)
      by_cases hx : x = x0 <;> simp [hx]
    · intro b _ hb
      apply lsum_zero
      intro x _
      simp [hb]


end Aux_SerialBatchTardy_lemma_8


open SerialBatchTardy Aux_SerialBatchTardy_lemma_8 in
theorem solution (xs : List ℕ) (t k : ℕ) (L : List ℕ) (hnd : xs.Nodup) (hpos : ∀ a ∈ xs, 1 ≤ a)
    (hlt : ∀ a ∈ xs, a < t) (σ : Schedule (hardInstance xs t k L)) (hσ : σ.Feasible) (ℓ x₀ : ℕ)
    (hx₀ : ∃ j ∈ earlyType σ ℓ, (labelOf xs t k L j).value? = some x₀)
    (hmin : ∀ j ∈ earlyType σ ℓ, ∀ x, (labelOf xs t k L j).value? = some x → x₀ ≤ x) :
    pSum (earlyType σ ℓ) ≤ x₀ ∧
      wSum (earlyType σ ℓ) ≤ xs.prod * (pSum (earlyType σ ℓ) + 1) ∧
      (wSum (earlyType σ ℓ) = xs.prod * (pSum (earlyType σ ℓ) + 1) ↔
        earlyType σ ℓ = gadgetSet xs t k L ℓ x₀) := by
  obtain ⟨j0, hj0, hv0⟩ := hx₀
  obtain ⟨x, h, hl, hx, hPx⟩ := pSum_le hlt σ hσ hj0
  have hxx : x = x₀ := by
    rw [hl] at hv0
    simpa [JobLabel.value?] using hv0
  have hx0 : x₀ ∈ xs := hxx ▸ hx
  obtain ⟨_, _, _, _, hℓk⟩ := gadget_some (mem_earlyType.mp hj0).1
  have hS : 0 < xs.prod := List.prod_pos (fun a ha => hpos a ha)
  have hd : x₀ ∣ xs.prod := List.dvd_prod hx0
  have hP : pSum (earlyType σ ℓ) ≤ x₀ := hxx ▸ hPx
  have hWle : wSum (earlyType σ ℓ) ≤ xs.prod * (pSum (earlyType σ ℓ) + 1) := by
    have := wSum_le hlt σ hσ ℓ
    rw [Nat.mul_add, Nat.mul_one]
    exact this
  have hG : pSum (gadgetSet xs t k L ℓ x₀) = x₀ := by
    have := gset_sum (t := t) (L := L) hnd hℓk hx0 Job.p 1 (fun h => by simp [labelJob])
    unfold pSum
    rw [this, mul_one]
  refine ⟨hP, hWle, ⟨fun heq => ?_, fun heq => ?_⟩⟩
  · obtain ⟨v, hv, hw⟩ := wSum_decomp2 hlt σ hσ ℓ
    rw [Nat.mul_add, Nat.mul_one, hw] at heq
    have hQ : ∑ j ∈ earlyType σ ℓ, ((hardInstance xs t k L).job j).p * (xs.prod / v j) =
        xs.prod := Nat.add_left_cancel heq
    have hvx : ∀ j ∈ earlyType σ ℓ, v j = x₀ := by
      intro j hj
      obtain ⟨h1, h2, h3, h4, h5⟩ := hv j hj
      have hge : x₀ ≤ v j := hmin j hj (v j) h4
      by_contra hne
      have hgt : x₀ < v j := lt_of_le_of_ne hge (Ne.symm hne)
      have hvpos : 0 < v j := hpos _ h3
      have hqpos : 0 < ((hardInstance xs t k L).job j).p * (xs.prod / v j) :=
        Nat.mul_pos h5 (Nat.div_pos (Nat.le_of_dvd hS h2) hvpos)
      have hlt' : (∑ i ∈ earlyType σ ℓ, ((hardInstance xs t k L).job i).p * (xs.prod / v i)) *
          x₀ < pSum (earlyType σ ℓ) * xs.prod := by
        calc (∑ i ∈ earlyType σ ℓ, ((hardInstance xs t k L).job i).p * (xs.prod / v i)) * x₀
            = ∑ i ∈ earlyType σ ℓ, ((hardInstance xs t k L).job i).p * (xs.prod / v i) * x₀ :=
              Finset.sum_mul _ _ _
          _ < ∑ i ∈ earlyType σ ℓ, ((hardInstance xs t k L).job i).p * (xs.prod / v i) * v i :=
              Finset.sum_lt_sum
                (fun i hi => Nat.mul_le_mul_left _ (hmin i hi (v i) (hv i hi).2.2.2.1))
                ⟨j, hj, Nat.mul_lt_mul_of_pos_left hgt hqpos⟩
          _ = ∑ i ∈ earlyType σ ℓ, ((hardInstance xs t k L).job i).p * xs.prod :=
              Finset.sum_congr rfl (fun i hi => by
                rw [mul_assoc, Nat.div_mul_cancel (hv i hi).2.1])
          _ = pSum (earlyType σ ℓ) * xs.prod := by
              unfold pSum
              rw [Finset.sum_mul]
      rw [hQ] at hlt'
      have := Nat.mul_le_mul_right xs.prod hP
      linarith
    have hPeq : pSum (earlyType σ ℓ) = x₀ := by
      have hQ2 : ∑ j ∈ earlyType σ ℓ, ((hardInstance xs t k L).job j).p * (xs.prod / v j) =
          pSum (earlyType σ ℓ) * (xs.prod / x₀) := by
        rw [Finset.sum_congr rfl (fun i hi => by rw [hvx i hi])]
        unfold pSum
        rw [Finset.sum_mul]
      have hx0pos : 0 < x₀ := hpos x₀ hx0
      have hpos' : 0 < xs.prod / x₀ := Nat.div_pos (Nat.le_of_dvd hS hd) hx0pos
      have : pSum (earlyType σ ℓ) * (xs.prod / x₀) = x₀ * (xs.prod / x₀) := by
        rw [← hQ2, hQ, Nat.mul_div_cancel' hd]
      exact Nat.eq_of_mul_eq_mul_right hpos' this
    have hsub : earlyType σ ℓ ⊆ gadgetSet xs t k L ℓ x₀ := by
      intro j hj
      unfold gadgetSet
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨(mem_earlyType.mp hj).1, by rw [(hv j hj).2.2.2.1, hvx j hj]⟩
    apply Finset.Subset.antisymm hsub
    intro g hg
    by_contra hgE
    have hgl : (labelOf xs t k L g).gadget? = some ℓ ∧ (labelOf xs t k L g).value? = some x₀ := by
      unfold gadgetSet at hg
      simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using hg
    obtain ⟨xg, hgg, hlg, hxg, _⟩ := gadget_some hgl.1
    have hpg : 0 < ((hardInstance xs t k L).job g).p := by
      rw [job_normal hlg]
      exact pow_pos (List.length_pos_of_mem hxg) hgg
    have hlt2 : ∑ j ∈ earlyType σ ℓ, ((hardInstance xs t k L).job j).p <
        ∑ j ∈ gadgetSet xs t k L ℓ x₀, ((hardInstance xs t k L).job j).p :=
      Finset.sum_lt_sum_of_subset hsub hg hgE hpg (fun _ _ _ => Nat.zero_le _)
    unfold pSum at hPeq hG
    omega
  · rw [heq]
    have hw := gset_sum (t := t) (L := L) hnd hℓk hx0 Job.w (xs.prod + xs.prod / x₀)
      (fun h => by simp [labelJob])
    have hp := gset_sum (t := t) (L := L) hnd hℓk hx0 Job.p 1 (fun h => by simp [labelJob])
    unfold wSum pSum
    rw [hw, hp, mul_one, Nat.mul_add x₀, Nat.mul_div_cancel' hd]
    ring
