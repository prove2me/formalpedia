-- Prove2me | solution 1 for SerialBatchTardy.lemma_6
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-21T01:59:39.685648+00:00
-- url     : https://prove2.me/submissions/68457423-48e3-4760-998c-b0dbc55a1a2b

import Mathlib
import Definitions.Def_SerialBatchTardy_Construction
set_option autoImplicit false

namespace Aux_SerialBatchTardy_lemma_6

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

theorem wSum_decomp {xs : List ℕ} {t k : ℕ} {L : List ℕ} (hlt : ∀ a ∈ xs, a < t)
    (σ : Schedule (hardInstance xs t k L)) (hσ : σ.Feasible) (ℓ : ℕ) :
    ∃ v : Fin (hardInstance xs t k L).jobs.length → ℕ,
      (∀ j ∈ earlyType σ ℓ, pSum (earlyType σ ℓ) ≤ v j ∧ v j ∣ xs.prod ∧ v j ∈ xs) ∧
      wSum (earlyType σ ℓ) = xs.prod * pSum (earlyType σ ℓ) +
        ∑ j ∈ earlyType σ ℓ, ((hardInstance xs t k L).job j).p * (xs.prod / v j) := by
  let v : Fin (hardInstance xs t k L).jobs.length → ℕ :=
    fun j => ((labelOf xs t k L j).value?).getD 0
  have key : ∀ j ∈ earlyType σ ℓ,
      ((hardInstance xs t k L).job j).w = ((hardInstance xs t k L).job j).p * xs.prod +
        ((hardInstance xs t k L).job j).p * (xs.prod / v j) ∧
      pSum (earlyType σ ℓ) ≤ v j ∧ v j ∣ xs.prod ∧ v j ∈ xs := by
    intro j hj
    obtain ⟨x, h, hl, hx, hPx⟩ := pSum_le hlt σ hσ hj
    have hv : v j = x := by simp only [v, hl, JobLabel.value?, Option.getD_some]
    rw [job_normal hl, hv]
    refine ⟨?_, hPx, List.dvd_prod hx, hx⟩
    dsimp only
    ring
  refine ⟨v, fun j hj => (key j hj).2, ?_⟩
  unfold wSum pSum
  rw [Finset.sum_congr rfl (fun j hj => (key j hj).1), Finset.sum_add_distrib, Finset.mul_sum]
  congr 1
  exact Finset.sum_congr rfl (fun j _ => by ring)

theorem wSum_eq_imp {xs : List ℕ} {t k : ℕ} {L : List ℕ} (hlt : ∀ a ∈ xs, a < t)
    (σ : Schedule (hardInstance xs t k L)) (hσ : σ.Feasible) (ℓ : ℕ) (hS : 0 < xs.prod)
    (heq : wSum (earlyType σ ℓ) = xs.prod * pSum (earlyType σ ℓ) + xs.prod) :
    ∃ x ∈ xs, pSum (earlyType σ ℓ) = x := by
  obtain ⟨v, hv, hw⟩ := wSum_decomp hlt σ hσ ℓ
  rw [hw] at heq
  have hQ : ∑ j ∈ earlyType σ ℓ, ((hardInstance xs t k L).job j).p * (xs.prod / v j) =
      xs.prod := Nat.add_left_cancel heq
  have hne : (earlyType σ ℓ).Nonempty := by
    by_contra hne
    rw [Finset.not_nonempty_iff_eq_empty] at hne
    rw [hne, Finset.sum_empty] at hQ
    omega
  obtain ⟨j0, hj0, hmin⟩ := Finset.exists_min_image (earlyType σ ℓ) v hne
  obtain ⟨hP0, _, hmem0⟩ := hv j0 hj0
  refine ⟨v j0, hmem0, le_antisymm hP0 ?_⟩
  have h1 : (∑ j ∈ earlyType σ ℓ, ((hardInstance xs t k L).job j).p * (xs.prod / v j)) * v j0 ≤
      pSum (earlyType σ ℓ) * xs.prod := by
    calc (∑ j ∈ earlyType σ ℓ, ((hardInstance xs t k L).job j).p * (xs.prod / v j)) * v j0
        = ∑ j ∈ earlyType σ ℓ, ((hardInstance xs t k L).job j).p * (xs.prod / v j) * v j0 :=
          Finset.sum_mul _ _ _
      _ ≤ ∑ j ∈ earlyType σ ℓ, ((hardInstance xs t k L).job j).p * (xs.prod / v j) * v j :=
          Finset.sum_le_sum (fun j hj => Nat.mul_le_mul_left _ (hmin j hj))
      _ = ∑ j ∈ earlyType σ ℓ, ((hardInstance xs t k L).job j).p * xs.prod :=
          Finset.sum_congr rfl (fun j hj => by rw [mul_assoc, Nat.div_mul_cancel (hv j hj).2.1])
      _ = pSum (earlyType σ ℓ) * xs.prod := by
          unfold pSum
          rw [Finset.sum_mul]
  rw [hQ, mul_comm (pSum (earlyType σ ℓ)) xs.prod] at h1
  exact Nat.le_of_mul_le_mul_left h1 hS

theorem leftover_early {xs : List ℕ} {t k : ℕ} {L : List ℕ}
    (σ : Schedule (hardInstance xs t k L)) (hk : 1 ≤ k) (hS : 0 < xs.prod)
    (hW : (σ.tardyWeight : ℤ) ≤ hardBound xs t k)
    (j : Fin (hardInstance xs t k L).jobs.length) (e : ℕ)
    (hl : labelOf xs t k L j = .leftover e) : ¬ σ.IsTardy j := by
  intro hT
  have h1 : ((hardInstance xs t k L).job j).w ≤ σ.tardyWeight := by
    unfold Schedule.tardyWeight
    have := Finset.single_le_sum
      (f := fun i => if σ.IsTardy i then ((hardInstance xs t k L).job i).w else 0)
      (fun i _ => Nat.zero_le _) (Finset.mem_univ j)
    simpa [hT] using this
  rw [job_leftover hl] at h1
  have h2 : xs.prod * (k * (xs.sum + xs.length)) ≤ σ.tardyWeight := h1
  have h1' : (xs.prod : ℤ) * ((k : ℤ) * ((xs.sum : ℤ) + (xs.length : ℤ))) ≤ σ.tardyWeight := by
    exact_mod_cast h2
  unfold hardBound at hW
  have hS' : (0 : ℤ) < xs.prod := by exact_mod_cast hS
  have hk' : (1 : ℤ) ≤ k := by exact_mod_cast hk
  have ht' : (0 : ℤ) ≤ t := by positivity
  have hpos' : (0 : ℤ) < xs.prod * (t + k) := mul_pos hS' (by linarith)
  linarith

def leftP : JobLabel → ℕ
  | .leftover e => e
  | .normal _ _ _ => 0

theorem leftP_sum (xs : List ℕ) (k : ℕ) (L : List ℕ) :
    ((hardLabels xs k L).map leftP).sum = L.sum := by
  unfold hardLabels
  rw [List.map_append, List.sum_append, sum_map_flatMap, lsum_range]
  have hL : ((L.map JobLabel.leftover).map leftP).sum = L.sum := by
    rw [List.map_map]
    have : leftP ∘ JobLabel.leftover = id := by
      funext e
      rfl
    rw [this, List.map_id]
  rw [hL]
  have h0 : ∑ ℓ ∈ Finset.range k,
      ((xs.flatMap fun x => gadgetLabels xs ℓ x).map leftP).sum = 0 := by
    apply Finset.sum_eq_zero
    intro ℓ _
    rw [sum_map_flatMap]
    apply lsum_zero
    intro x _
    exact (gadget_sum xs leftP ℓ x 0 (fun h => by simp [leftP])).trans (Nat.mul_zero x)
  rw [h0, add_zero]

theorem early_lower {xs : List ℕ} {t k : ℕ} {L : List ℕ}
    (σ : Schedule (hardInstance xs t k L)) (hk : 1 ≤ k) (hS : 0 < xs.prod)
    (hW : (σ.tardyWeight : ℤ) ≤ hardBound xs t k) :
    L.sum + ∑ ℓ ∈ Finset.range k, pSum (earlyType σ ℓ) ≤
      ∑ j ∈ Finset.univ.filter (fun j => ¬ σ.IsTardy j), ((hardInstance xs t k L).job j).p := by
  have hleft : ∑ j : Fin (hardInstance xs t k L).jobs.length, leftP (labelOf xs t k L j) =
      L.sum := (sum_jobs leftP).trans (leftP_sum xs k L)
  have hP : ∀ ℓ, pSum (earlyType σ ℓ) = ∑ j, (if (labelOf xs t k L j).gadget? = some ℓ ∧
      ¬ σ.IsTardy j then ((hardInstance xs t k L).job j).p else 0) := by
    intro ℓ
    unfold pSum earlyType
    rw [Finset.sum_filter]
  rw [← hleft, Finset.sum_congr rfl (fun ℓ _ => hP ℓ), Finset.sum_comm, ← Finset.sum_add_distrib,
    Finset.sum_filter]
  apply Finset.sum_le_sum
  intro j _
  rcases job_cases j with ⟨e, hl⟩ | ⟨ℓ0, x, h, hl, hx, hℓ0⟩
  · have hnt := leftover_early σ hk hS hW j e hl
    have hp : ((hardInstance xs t k L).job j).p = e := by rw [job_leftover hl]
    rw [hl]
    simp [leftP, JobLabel.gadget?, hnt, hp]
  · rw [hl]
    by_cases hT : σ.IsTardy j
    · simp [leftP, JobLabel.gadget?, hT]
    · simp [leftP, JobLabel.gadget?, hT, hℓ0]

/-! ## Moving the tardy jobs into a final batch -/

def mvT {I : Instance} (σ : Schedule I) (bstar : ℕ) (M : ℤ) : Schedule I where
  batch j := if σ.IsTardy j then bstar else σ.batch j
  start b := if b = bstar then M else σ.start b

theorem mvT_batch_T {I : Instance} (σ : Schedule I) (bstar : ℕ) (M : ℤ)
    (j : Fin I.jobs.length) (h : σ.IsTardy j) : (mvT σ bstar M).batch j = bstar := by
  show (if σ.IsTardy j then bstar else σ.batch j) = bstar
  rw [if_pos h]

theorem mvT_batch_nT {I : Instance} (σ : Schedule I) (bstar : ℕ) (M : ℤ)
    (j : Fin I.jobs.length) (h : ¬ σ.IsTardy j) : (mvT σ bstar M).batch j = σ.batch j := by
  show (if σ.IsTardy j then bstar else σ.batch j) = σ.batch j
  rw [if_neg h]

theorem mvT_start_star {I : Instance} (σ : Schedule I) (bstar : ℕ) (M : ℤ) :
    (mvT σ bstar M).start bstar = M := by
  show (if bstar = bstar then M else σ.start bstar) = M
  rw [if_pos rfl]

theorem mvT_start_ne {I : Instance} (σ : Schedule I) (bstar : ℕ) (M : ℤ) (b : ℕ)
    (h : b ≠ bstar) : (mvT σ bstar M).start b = σ.start b := by
  show (if b = bstar then M else σ.start b) = σ.start b
  rw [if_neg h]

theorem mvT_comp_le {I : Instance} (σ : Schedule I) (bstar : ℕ) (M : ℤ) (b : ℕ)
    (h : b ≠ bstar) : (mvT σ bstar M).comp b ≤ σ.comp b := by
  have hsub : (mvT σ bstar M).batchJobs b ⊆ σ.batchJobs b := by
    intro j hj
    simp only [Schedule.batchJobs, Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
    by_cases hT : σ.IsTardy j
    · rw [mvT_batch_T σ bstar M j hT] at hj
      exact absurd hj.symm h
    · rw [mvT_batch_nT σ bstar M j hT] at hj
      exact hj
  have hs : ∑ j ∈ (mvT σ bstar M).batchJobs b, ((I.job j).p : ℤ) ≤
      ∑ j ∈ σ.batchJobs b, ((I.job j).p : ℤ) :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
  have h1 : (mvT σ bstar M).comp b = (mvT σ bstar M).start b + ((I.setup : ℤ) +
      ∑ j ∈ (mvT σ bstar M).batchJobs b, ((I.job j).p : ℤ)) := rfl
  have h2 : σ.comp b = σ.start b + ((I.setup : ℤ) + ∑ j ∈ σ.batchJobs b, ((I.job j).p : ℤ)) := rfl
  rw [h1, h2, mvT_start_ne σ bstar M b h]
  linarith

theorem mvT_comp_star {I : Instance} (σ : Schedule I) (bstar : ℕ) (M : ℤ) :
    M ≤ (mvT σ bstar M).comp bstar := by
  have h1 : (mvT σ bstar M).comp bstar = (mvT σ bstar M).start bstar + ((I.setup : ℤ) +
      ∑ j ∈ (mvT σ bstar M).batchJobs bstar, ((I.job j).p : ℤ)) := rfl
  have h0 : (0 : ℤ) ≤ ∑ j ∈ (mvT σ bstar M).batchJobs bstar, ((I.job j).p : ℤ) :=
    Finset.sum_nonneg (fun _ _ => by positivity)
  have h3 : (0 : ℤ) ≤ (I.setup : ℤ) := by positivity
  rw [h1, mvT_start_star]
  linarith

theorem normal_total {xs : List ℕ} {t k : ℕ} {L : List ℕ} :
    ∑ j : Fin (hardInstance xs t k L).jobs.length,
      (if (labelOf xs t k L j).gadget?.isSome then ((hardInstance xs t k L).job j).w else 0) =
      k * (xs.prod * xs.sum + xs.prod * xs.length) := by
  simp only [job_eq]
  let G : JobLabel → ℕ := fun lab =>
    if lab.gadget?.isSome then (labelJob xs t k lab).w else 0
  refine (sum_jobs (xs := xs) (t := t) (k := k) (L := L) G).trans ?_
  refine (hard_sum xs k L G (fun _ x => xs.prod + xs.prod / x) ?_ ?_).trans ?_
  · intro e
    simp [G, JobLabel.gadget?]
  · intro ℓ x h
    simp [G, JobLabel.gadget?, labelJob]
  · rw [Finset.sum_congr rfl (fun ℓ _ => list_weight xs.prod xs (fun y hy => List.dvd_prod hy))]
    simp


end Aux_SerialBatchTardy_lemma_6


open SerialBatchTardy Aux_SerialBatchTardy_lemma_6 in
theorem solution (xs : List ℕ) (t k : ℕ) (L : List ℕ) (hpos : ∀ a ∈ xs, 1 ≤ a) (hk : 1 ≤ k)
    (σ : Schedule (hardInstance xs t k L)) (hσ : σ.Feasible)
    (hW : (σ.tardyWeight : ℤ) ≤ hardBound xs t k) :
    ∃ σ' : Schedule (hardInstance xs t k L), σ'.Feasible ∧
      (σ'.tardyWeight : ℤ) ≤ hardBound xs t k ∧
      ∃ bstar : ℕ,
        (∀ b, σ'.Used b → b ≠ bstar → σ'.comp b ≤ σ'.start bstar) ∧
        (∀ j, σ'.IsTardy j ↔ σ'.batch j = bstar) ∧
        (∀ j, (labelOf xs t k L j).gadget? = none → ¬ σ'.IsTardy j) ∧
        xs.prod * (t + k) ≤
          ∑ j ∈ Finset.univ.filter
              (fun j => (labelOf xs t k L j).gadget?.isSome ∧ ¬ σ'.IsTardy j),
            ((hardInstance xs t k L).job j).w := by
  have hS : 0 < xs.prod := List.prod_pos (fun a ha => hpos a ha)
  obtain ⟨bstar, hbstar⟩ : ∃ bstar : ℕ, ∀ j, σ.batch j < bstar :=
    ⟨Finset.univ.sup σ.batch + 1, fun j => Nat.lt_succ_of_le (Finset.le_sup (Finset.mem_univ j))⟩
  obtain ⟨M, hMc, hMr⟩ : ∃ M : ℤ, (∀ j, σ.comp (σ.batch j) ≤ M) ∧
      (∀ j, ((hardInstance xs t k L).job j).r ≤ M) := by
    refine ⟨∑ i, (|σ.comp (σ.batch i)| + |((hardInstance xs t k L).job i).r|),
      fun j => ?_, fun j => ?_⟩
    · have h0 : |σ.comp (σ.batch j)| + |((hardInstance xs t k L).job j).r| ≤
          ∑ i, (|σ.comp (σ.batch i)| + |((hardInstance xs t k L).job i).r|) :=
        Finset.single_le_sum
          (f := fun i => |σ.comp (σ.batch i)| + |((hardInstance xs t k L).job i).r|)
          (fun i _ => by positivity) (Finset.mem_univ j)
      have h1 := le_abs_self (σ.comp (σ.batch j))
      have h2 := abs_nonneg (((hardInstance xs t k L).job j).r)
      linarith
    · have h0 : |σ.comp (σ.batch j)| + |((hardInstance xs t k L).job j).r| ≤
          ∑ i, (|σ.comp (σ.batch i)| + |((hardInstance xs t k L).job i).r|) :=
        Finset.single_le_sum
          (f := fun i => |σ.comp (σ.batch i)| + |((hardInstance xs t k L).job i).r|)
          (fun i _ => by positivity) (Finset.mem_univ j)
      have h1 := le_abs_self (((hardInstance xs t k L).job j).r)
      have h2 := abs_nonneg (σ.comp (σ.batch j))
      linarith
  have hne : ∀ j, σ.batch j ≠ bstar := fun j => Nat.ne_of_lt (hbstar j)
  refine ⟨mvT σ bstar M, ?_⟩
  have hT' : ∀ j, (mvT σ bstar M).IsTardy j ↔ σ.IsTardy j := by
    intro j
    constructor
    · intro h
      by_contra hT
      have h1 : ((hardInstance xs t k L).job j).d <
          (mvT σ bstar M).comp ((mvT σ bstar M).batch j) := h
      rw [mvT_batch_nT σ bstar M j hT] at h1
      have h2 := mvT_comp_le σ bstar M (σ.batch j) (hne j)
      have h3 : ¬ ((hardInstance xs t k L).job j).d < σ.comp (σ.batch j) := hT
      exact h3 (lt_of_lt_of_le h1 h2)
    · intro h
      have h1 : ((hardInstance xs t k L).job j).d < σ.comp (σ.batch j) := h
      show ((hardInstance xs t k L).job j).d < (mvT σ bstar M).comp ((mvT σ bstar M).batch j)
      rw [mvT_batch_T σ bstar M j h]
      have h2 := mvT_comp_star σ bstar M
      have h3 := hMc j
      linarith
  have hbat : ∀ j, (mvT σ bstar M).batch j = bstar ↔ σ.IsTardy j := by
    intro j
    by_cases h : σ.IsTardy j
    · rw [mvT_batch_T σ bstar M j h]
      exact ⟨fun _ => h, fun _ => rfl⟩
    · rw [mvT_batch_nT σ bstar M j h]
      exact ⟨fun h' => absurd h' (hne j), fun h' => absurd h' h⟩
  have husedC : ∀ b, (mvT σ bstar M).Used b → b ≠ bstar →
      (mvT σ bstar M).comp b ≤ M ∧ σ.Used b := by
    rintro b ⟨j, hj⟩ hb
    have hT : ¬ σ.IsTardy j := by
      intro hT
      rw [mvT_batch_T σ bstar M j hT] at hj
      exact hb hj.symm
    rw [mvT_batch_nT σ bstar M j hT] at hj
    have h1 := mvT_comp_le σ bstar M b hb
    have h2 := hMc j
    rw [hj] at h2
    exact ⟨le_trans h1 h2, ⟨j, hj⟩⟩
  have htw : (mvT σ bstar M).tardyWeight = σ.tardyWeight := by
    unfold Schedule.tardyWeight
    apply Finset.sum_congr rfl
    intro j _
    by_cases h : σ.IsTardy j
    · rw [if_pos ((hT' j).mpr h), if_pos h]
    · rw [if_neg (fun h' => h ((hT' j).mp h')), if_neg h]
  refine ⟨⟨?_, ?_⟩, ?_, bstar, ?_, ?_, ?_, ?_⟩
  · intro j
    by_cases h : σ.IsTardy j
    · rw [mvT_batch_T σ bstar M j h, mvT_start_star]
      exact hMr j
    · rw [mvT_batch_nT σ bstar M j h, mvT_start_ne σ bstar M _ (hne j)]
      exact hσ.1 j
  · intro b b' hb hb' hbb
    by_cases h1 : b = bstar
    · subst h1
      right
      rw [mvT_start_star]
      exact (husedC b' hb' (Ne.symm hbb)).1
    · by_cases h2 : b' = bstar
      · subst h2
        left
        rw [mvT_start_star]
        exact (husedC b hb h1).1
      · obtain ⟨c1, u1⟩ := husedC b hb h1
        obtain ⟨c2, u2⟩ := husedC b' hb' h2
        have e1 := mvT_comp_le σ bstar M b h1
        have e2 := mvT_comp_le σ bstar M b' h2
        rw [mvT_start_ne σ bstar M b h1, mvT_start_ne σ bstar M b' h2]
        rcases hσ.2 b b' u1 u2 hbb with h | h
        · left
          linarith
        · right
          linarith
  · rw [htw]
    exact hW
  · intro b hb hbs
    rw [mvT_start_star]
    exact (husedC b hb hbs).1
  · intro j
    rw [hT', hbat]
  · intro j hj hT
    rw [hT'] at hT
    rcases job_cases j with ⟨e, hl⟩ | ⟨ℓ, x, h, hl, _, _⟩
    · exact leftover_early σ hk hS hW j e hl hT
    · rw [hl] at hj
      simp [JobLabel.gadget?] at hj
  · -- weight of early normal jobs
    have hsplit : ∑ j : Fin (hardInstance xs t k L).jobs.length,
        (if (labelOf xs t k L j).gadget?.isSome then ((hardInstance xs t k L).job j).w else 0) =
        ∑ j : Fin (hardInstance xs t k L).jobs.length,
          (if (labelOf xs t k L j).gadget?.isSome ∧ (mvT σ bstar M).IsTardy j then
            ((hardInstance xs t k L).job j).w else 0) +
        ∑ j ∈ Finset.univ.filter
            (fun j => (labelOf xs t k L j).gadget?.isSome ∧ ¬ (mvT σ bstar M).IsTardy j),
          ((hardInstance xs t k L).job j).w := by
      rw [Finset.sum_filter, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro j _
      by_cases h1 : (labelOf xs t k L j).gadget?.isSome <;>
        by_cases h2 : (mvT σ bstar M).IsTardy j <;> simp [h1, h2]
    have hle : ∑ j : Fin (hardInstance xs t k L).jobs.length,
        (if (labelOf xs t k L j).gadget?.isSome ∧ (mvT σ bstar M).IsTardy j then
          ((hardInstance xs t k L).job j).w else 0) ≤ (mvT σ bstar M).tardyWeight := by
      unfold Schedule.tardyWeight
      apply Finset.sum_le_sum
      intro j _
      by_cases h2 : (mvT σ bstar M).IsTardy j
      · rw [if_pos h2]
        split_ifs <;> simp
      · rw [if_neg h2, if_neg (fun h => h2 h.2)]
    rw [normal_total] at hsplit
    rw [htw] at hle
    obtain ⟨A, hA⟩ : ∃ A, A = ∑ j : Fin (hardInstance xs t k L).jobs.length,
        (if (labelOf xs t k L j).gadget?.isSome ∧ (mvT σ bstar M).IsTardy j then
          ((hardInstance xs t k L).job j).w else 0) := ⟨_, rfl⟩
    obtain ⟨B, hB⟩ : ∃ B, B = ∑ j ∈ Finset.univ.filter
            (fun j => (labelOf xs t k L j).gadget?.isSome ∧ ¬ (mvT σ bstar M).IsTardy j),
          ((hardInstance xs t k L).job j).w := ⟨_, rfl⟩
    rw [← hA, ← hB] at hsplit
    rw [← hA] at hle
    rw [← hB]
    have c1 : (k : ℤ) * (xs.prod * xs.sum + xs.prod * xs.length) = A + B := by
      exact_mod_cast hsplit
    have c2 : (A : ℤ) ≤ σ.tardyWeight := by exact_mod_cast hle
    unfold hardBound at hW
    have : (xs.prod : ℤ) * (t + k) ≤ B := by linarith
    exact_mod_cast this
