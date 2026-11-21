-- Prove2me | solution 1 for SerialBatchTardy.leftoverList_spec
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-21T02:12:31.938383+00:00
-- url     : https://prove2.me/submissions/5eb4c63a-c576-4e81-8e8f-fb47a3af6adb

import Mathlib
import Definitions.Def_SerialBatchTardy_Construction
set_option autoImplicit false

namespace Aux_SerialBatchTardy_leftoverList_spec

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

def LLgen (n k D Y : ℕ) : List ℕ :=
  (List.range D).flatMap (fun h => List.replicate (k * (n - 1) + (Nat.digits n Y).getD h 0) (n ^ h))
    ++ List.replicate (Y / n ^ D) (n ^ D)

theorem LL_eq (n k t : ℕ) : leftoverList n k t =
    LLgen n k (Nat.log n (t / 2)) ((k - 1) * t - k * (n ^ Nat.log n (t / 2) - 1)) := rfl

theorem digit_sum (b : ℕ) (hb : 1 < b) : ∀ D Y : ℕ,
    ∑ h ∈ Finset.range D, (Nat.digits b Y).getD h 0 * b ^ h = Y % b ^ D := by
  intro D
  induction D with
  | zero => intro Y; simp [Nat.mod_one]
  | succ D ih =>
    intro Y
    rcases Nat.eq_zero_or_pos Y with hY | hY
    · subst hY
      simp
    · rw [Finset.sum_range_succ', Nat.digits_def' hb hY]
      simp only [List.getD_cons_succ, List.getD_cons_zero, pow_zero, mul_one]
      have : ∑ h ∈ Finset.range D, (Nat.digits b (Y / b)).getD h 0 * b ^ (h + 1) =
          b * ∑ h ∈ Finset.range D, (Nat.digits b (Y / b)).getD h 0 * b ^ h := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun _ _ => by ring)
      rw [this, ih (Y / b), pow_succ', Nat.mod_mul]
      ring

theorem digit_le (b : ℕ) (hb : 1 < b) (Y h : ℕ) : (Nat.digits b Y).getD h 0 ≤ b - 1 := by
  rw [List.getD_eq_getElem?_getD]
  rcases hget : (Nat.digits b Y)[h]? with _ | d
  · simp
  · simp only [Option.getD_some]
    have hmem : d ∈ Nat.digits b Y := List.mem_of_getElem? hget
    have := Nat.digits_lt_base hb hmem
    omega

theorem geom_aux (n : ℕ) (hn : 1 ≤ n) : ∀ D : ℕ,
    ∑ h ∈ Finset.range D, (n - 1) * n ^ h + 1 = n ^ D := by
  intro D
  induction D with
  | zero => simp
  | succ D ih =>
    rw [Finset.sum_range_succ, pow_succ]
    have : (n - 1) * n ^ D + n ^ D = n ^ D * n := by
      obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
      simp only [Nat.add_sub_cancel]
      ring
    omega

theorem LLgen_sum (n k D Y : ℕ) (hn : 2 ≤ n) :
    (LLgen n k D Y).sum = k * (n ^ D - 1) + Y := by
  unfold LLgen
  rw [List.sum_append, List.sum_replicate, smul_eq_mul]
  have h1 : ((List.range D).flatMap (fun h =>
      List.replicate (k * (n - 1) + (Nat.digits n Y).getD h 0) (n ^ h))).sum =
      ∑ h ∈ Finset.range D, (k * (n - 1) + (Nat.digits n Y).getD h 0) * n ^ h := by
    have := sum_map_flatMap (List.range D) (fun h =>
      List.replicate (k * (n - 1) + (Nat.digits n Y).getD h 0) (n ^ h)) id
    rw [List.map_id] at this
    rw [this, lsum_range]
    apply Finset.sum_congr rfl
    intro h _
    rw [List.map_id, List.sum_replicate, smul_eq_mul]
  rw [h1]
  have h2 : ∑ h ∈ Finset.range D, (k * (n - 1) + (Nat.digits n Y).getD h 0) * n ^ h =
      k * ∑ h ∈ Finset.range D, (n - 1) * n ^ h +
        ∑ h ∈ Finset.range D, (Nat.digits n Y).getD h 0 * n ^ h := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun _ _ => by ring)
  rw [h2, digit_sum n (by omega) D Y]
  have h3 := geom_aux n (by omega) D
  have h4 : ∑ h ∈ Finset.range D, (n - 1) * n ^ h = n ^ D - 1 := by omega
  rw [h4]
  have h5 := Nat.mod_add_div' Y (n ^ D)
  omega

theorem LLgen_len (n k D Y : ℕ) (hn : 2 ≤ n) :
    (LLgen n k D Y).length ≤ D * ((k + 1) * (n - 1)) + Y / n ^ D := by
  unfold LLgen
  rw [List.length_append, List.length_replicate, List.length_flatMap]
  have : ((List.range D).map fun h =>
      (List.replicate (k * (n - 1) + (Nat.digits n Y).getD h 0) (n ^ h)).length).sum ≤
      D * ((k + 1) * (n - 1)) := by
    rw [lsum_range]
    calc ∑ h ∈ Finset.range D,
          (List.replicate (k * (n - 1) + (Nat.digits n Y).getD h 0) (n ^ h)).length
        ≤ ∑ h ∈ Finset.range D, ((k + 1) * (n - 1)) := by
          apply Finset.sum_le_sum
          intro h _
          rw [List.length_replicate]
          have := digit_le n (by omega) Y h
          nlinarith
      _ = D * ((k + 1) * (n - 1)) := by simp
  omega

theorem LLgen_mem (n k D Y : ℕ) : ∀ e ∈ LLgen n k D Y, ∃ h ≤ D, e = n ^ h := by
  intro e he
  unfold LLgen at he
  rcases List.mem_append.mp he with h1 | h1
  · obtain ⟨h, hh, h2⟩ := List.mem_flatMap.mp h1
    exact ⟨h, le_of_lt (List.mem_range.mp hh), (List.mem_replicate.mp h2).2⟩
  · exact ⟨D, le_refl _, (List.mem_replicate.mp h1).2⟩

/-! ## Assignments of list entries to parts -/

def Asg (k : ℕ) (L : List ℕ) (s : Fin k → ℕ) : Prop :=
  ∃ α : ℕ → Fin k, ∀ ℓ, ∑ m ∈ Finset.range L.length, (if α m = ℓ then L.getD m 0 else 0) = s ℓ

theorem asg_congr {k : ℕ} {L : List ℕ} {s s' : Fin k → ℕ} (h : Asg k L s) (e : s = s') :
    Asg k L s' := e ▸ h

theorem asg_nil {k : ℕ} (hk : 0 < k) : Asg k [] (fun _ => 0) :=
  ⟨fun _ => ⟨0, hk⟩, fun ℓ => by simp⟩

theorem asg_single {k : ℕ} (v : ℕ) (ℓ0 : Fin k) :
    Asg k [v] (fun ℓ => if ℓ0 = ℓ then v else 0) :=
  ⟨fun _ => ℓ0, fun ℓ => by simp⟩

theorem asg_append {k : ℕ} {A B : List ℕ} {s₁ s₂ : Fin k → ℕ} (h1 : Asg k A s₁)
    (h2 : Asg k B s₂) : Asg k (A ++ B) (fun ℓ => s₁ ℓ + s₂ ℓ) := by
  obtain ⟨α₁, hα₁⟩ := h1
  obtain ⟨α₂, hα₂⟩ := h2
  refine ⟨fun m => if m < A.length then α₁ m else α₂ (m - A.length), fun ℓ => ?_⟩
  show _ = s₁ ℓ + s₂ ℓ
  rw [List.length_append, Finset.sum_range_add, ← hα₁ ℓ, ← hα₂ ℓ]
  congr 1
  · apply Finset.sum_congr rfl
    intro m hm
    have hm' := Finset.mem_range.mp hm
    show (if (if m < A.length then α₁ m else α₂ (m - A.length)) = ℓ then (A ++ B).getD m 0
      else 0) = _
    rw [if_pos hm', List.getD_append A B 0 m hm']
  · apply Finset.sum_congr rfl
    intro m _
    have hm' : ¬ (A.length + m < A.length) := by omega
    show (if (if A.length + m < A.length then α₁ (A.length + m)
      else α₂ (A.length + m - A.length)) = ℓ then (A ++ B).getD (A.length + m) 0 else 0) = _
    rw [if_neg hm', List.getD_append_right A B 0 (A.length + m) (by omega),
      show A.length + m - A.length = m by omega]

theorem asg_replicate {k : ℕ} (hk : 0 < k) (v : ℕ) : ∀ c (u : Fin k → ℕ), ∑ ℓ, u ℓ = c →
    Asg k (List.replicate c v) (fun ℓ => u ℓ * v) := by
  intro c
  induction c with
  | zero =>
    intro u hu
    have hu0 : ∀ ℓ, u ℓ = 0 := fun ℓ => (Finset.sum_eq_zero_iff.mp hu) ℓ (Finset.mem_univ ℓ)
    refine asg_congr (asg_nil hk) ?_
    funext ℓ
    rw [hu0 ℓ, zero_mul]
  | succ c ih =>
    intro u hu
    obtain ⟨ℓ0, hℓ0⟩ : ∃ ℓ0, 0 < u ℓ0 := by
      by_contra hne
      push_neg at hne
      have : ∑ ℓ, u ℓ = 0 := Finset.sum_eq_zero (fun ℓ _ => by have := hne ℓ; omega)
      omega
    let u' : Fin k → ℕ := fun ℓ => if ℓ = ℓ0 then u ℓ - 1 else u ℓ
    have hsplit : ∀ ℓ, u ℓ = (if ℓ0 = ℓ then 1 else 0) + u' ℓ := by
      intro ℓ
      by_cases h : ℓ = ℓ0
      · have e1 : u' ℓ = u ℓ - 1 := if_pos h
        rw [e1, if_pos h.symm]
        have := hℓ0
        rw [← h] at this
        omega
      · have e1 : u' ℓ = u ℓ := if_neg h
        rw [e1, if_neg (Ne.symm h), zero_add]
    have hsum : ∑ ℓ, u' ℓ = c := by
      have : ∑ ℓ, u ℓ = ∑ ℓ, (if ℓ0 = ℓ then 1 else 0) + ∑ ℓ, u' ℓ := by
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl (fun ℓ _ => hsplit ℓ)
      rw [Finset.sum_ite_eq] at this
      simp only [Finset.mem_univ, if_true] at this
      omega
    have h := asg_append (asg_single v ℓ0) (ih u' hsum)
    rw [List.replicate_succ]
    refine asg_congr h ?_
    funext ℓ
    show (if ℓ0 = ℓ then v else 0) + u' ℓ * v = u ℓ * v
    rw [hsplit ℓ]
    split_ifs <;> ring

theorem asg_flat {k : ℕ} (hk : 0 < k) (f : ℕ → List ℕ) (g : ℕ → Fin k → ℕ) :
    ∀ D, (∀ h < D, Asg k (f h) (g h)) →
      Asg k ((List.range D).flatMap f) (fun ℓ => ∑ h ∈ Finset.range D, g h ℓ) := by
  intro D
  induction D with
  | zero =>
    intro _
    refine asg_congr (asg_nil hk) ?_
    funext ℓ
    simp
  | succ D ih =>
    intro hf
    have h1 := ih (fun h hh => hf h (by omega))
    have h2 := hf D (by omega)
    have h3 := asg_append h1 h2
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
    refine asg_congr h3 ?_
    funext ℓ
    rw [Finset.sum_range_succ]

/-! ## Distributing amounts -/

theorem distrib {k : ℕ} (m : Fin k → ℕ) : ∀ q, q ≤ ∑ ℓ, m ℓ →
    ∃ w : Fin k → ℕ, (∀ ℓ, w ℓ ≤ m ℓ) ∧ ∑ ℓ, w ℓ = q := by
  intro q
  induction q with
  | zero => intro _; exact ⟨fun _ => 0, fun _ => Nat.zero_le _, by simp⟩
  | succ q ih =>
    intro hq
    obtain ⟨w, hw1, hw2⟩ := ih (by omega)
    obtain ⟨ℓ0, hℓ0⟩ : ∃ ℓ0, w ℓ0 < m ℓ0 := by
      by_contra hne
      push_neg at hne
      have : ∑ ℓ, m ℓ ≤ ∑ ℓ, w ℓ := Finset.sum_le_sum (fun ℓ _ => hne ℓ)
      omega
    refine ⟨fun ℓ => w ℓ + (if ℓ0 = ℓ then 1 else 0), fun ℓ => ?_, ?_⟩
    · show w ℓ + (if ℓ0 = ℓ then 1 else 0) ≤ m ℓ
      by_cases h : ℓ0 = ℓ
      · rw [if_pos h, ← h]
        omega
      · rw [if_neg h, add_zero]
        exact hw1 ℓ
    · rw [Finset.sum_add_distrib, hw2, Finset.sum_ite_eq]
      simp

theorem counts {k n : ℕ} (hn : 2 ≤ n) : ∀ D (c : ℕ → ℕ) (s : Fin k → ℕ),
    (∀ h < D, k * (n - 1) ≤ c h) →
    ∑ ℓ, s ℓ = ∑ h ∈ Finset.range D, c h * n ^ h + c D * n ^ D →
    ∃ u : ℕ → Fin k → ℕ, (∀ h ≤ D, ∑ ℓ, u h ℓ = c h) ∧
      ∀ ℓ, ∑ h ∈ Finset.range (D + 1), u h ℓ * n ^ h = s ℓ := by
  intro D
  induction D with
  | zero =>
    intro c s _ hs
    refine ⟨fun _ => s, fun h hh => ?_, fun ℓ => by simp⟩
    have : h = 0 := by omega
    subst this
    simpa using hs
  | succ D ih =>
    intro c s hc hs
    -- split off level 0
    obtain ⟨R, hR⟩ : ∃ R, R = ∑ h ∈ Finset.range D, c (h + 1) * n ^ h + c (D + 1) * n ^ D :=
      ⟨_, rfl⟩
    have hs' : ∑ ℓ, s ℓ = c 0 + n * R := by
      rw [hs, hR, Finset.sum_range_succ', pow_zero, mul_one, Nat.mul_add, Finset.mul_sum]
      have : ∑ h ∈ Finset.range D, c (h + 1) * n ^ (h + 1) =
          ∑ h ∈ Finset.range D, n * (c (h + 1) * n ^ h) :=
        Finset.sum_congr rfl (fun _ _ => by ring)
      rw [this, pow_succ]
      ring
    have hrle : ∑ ℓ, s ℓ % n ≤ k * (n - 1) := by
      have := Finset.sum_le_card_nsmul Finset.univ (fun ℓ => s ℓ % n) (n - 1)
        (fun ℓ _ => by have := Nat.mod_lt (s ℓ) (show 0 < n by omega); omega)
      simpa using this
    have hc0 := hc 0 (by omega)
    have hdecomp : ∑ ℓ, s ℓ = ∑ ℓ, s ℓ % n + n * ∑ ℓ, s ℓ / n := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl (fun ℓ _ => (Nat.mod_add_div (s ℓ) n).symm)
    have hRle : R ≤ ∑ ℓ, s ℓ / n := by
      by_contra hlt
      push_neg at hlt
      have : n * (∑ ℓ, s ℓ / n + 1) ≤ n * R := Nat.mul_le_mul_left n hlt
      nlinarith
    obtain ⟨q, hq⟩ : ∃ q, q = ∑ ℓ, s ℓ / n - R := ⟨_, rfl⟩
    have hc0eq : c 0 = ∑ ℓ, s ℓ % n + n * q := by
      have h1 : n * (∑ ℓ, s ℓ / n) = n * R + n * q := by
        rw [hq, ← Nat.mul_add]
        congr 1
        omega
      omega
    obtain ⟨w, hw1, hw2⟩ := distrib (fun ℓ => s ℓ / n) q (by omega)
    obtain ⟨u', hu'1, hu'2⟩ := ih (fun h => c (h + 1)) (fun ℓ => s ℓ / n - w ℓ)
      (fun h hh => hc (h + 1) (by omega)) (by
        show ∑ ℓ, (s ℓ / n - w ℓ) = ∑ h ∈ Finset.range D, c (h + 1) * n ^ h + c (D + 1) * n ^ D
        have : ∑ ℓ, (s ℓ / n - w ℓ) = ∑ ℓ, s ℓ / n - ∑ ℓ, w ℓ := by
          rw [Finset.sum_tsub_distrib]
          exact fun ℓ _ => hw1 ℓ
        rw [this, hw2, ← hR]
        omega)
    refine ⟨fun h => match h with
      | 0 => fun ℓ => s ℓ % n + n * w ℓ
      | h + 1 => u' h, ?_, ?_⟩
    · intro h hh
      rcases h with _ | h
      · show ∑ ℓ, (s ℓ % n + n * w ℓ) = c 0
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, hw2, hc0eq]
      · show ∑ ℓ, u' h ℓ = c (h + 1)
        exact hu'1 h (by omega)
    · intro ℓ
      rw [Finset.sum_range_succ']
      show ∑ h ∈ Finset.range (D + 1), u' h ℓ * n ^ (h + 1) + (s ℓ % n + n * w ℓ) * n ^ 0 = s ℓ
      have h1 : ∑ h ∈ Finset.range (D + 1), u' h ℓ * n ^ (h + 1) =
          n * ∑ h ∈ Finset.range (D + 1), u' h ℓ * n ^ h := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun _ _ => by ring)
      have hu : ∑ h ∈ Finset.range (D + 1), u' h ℓ * n ^ h = s ℓ / n - w ℓ := hu'2 ℓ
      rw [h1, hu, pow_zero, mul_one]
      have h2 := hw1 ℓ
      have h3 := Nat.mod_add_div (s ℓ) n
      have h4 : n * (s ℓ / n - w ℓ) + n * w ℓ = n * (s ℓ / n) := by
        rw [← Nat.mul_add]
        congr 1
        omega
      omega


end Aux_SerialBatchTardy_leftoverList_spec


open SerialBatchTardy Aux_SerialBatchTardy_leftoverList_spec in
theorem solution (n k t : ℕ) (hn : 2 ≤ n) (hk : 2 ≤ k) (ht : 2 ≤ t) :
    (∀ e ∈ leftoverList n k t, ∃ h ≤ Nat.log n t, e = n ^ h) ∧
      (leftoverList n k t).sum = (k - 1) * t ∧
      (leftoverList n k t).length ≤ 2 * (k + 1) * n * (Nat.log n t + 1) ∧
      ∀ s : Fin k → ℕ, ∑ ℓ, s ℓ = (k - 1) * t →
        ∃ a : Fin (leftoverList n k t).length → Fin k,
          ∀ ℓ, ∑ i ∈ Finset.univ.filter (fun i => a i = ℓ), (leftoverList n k t).get i = s ℓ := by
  rw [LL_eq]
  obtain ⟨D, hD⟩ : ∃ D, D = Nat.log n (t / 2) := ⟨_, rfl⟩
  rw [← hD]
  have hD1 : n ^ D ≤ t / 2 := by
    rw [hD]
    exact Nat.pow_log_le_self n (by omega)
  have hD2 : t / 2 < n ^ (D + 1) := by
    rw [hD]
    exact Nat.lt_pow_succ_log_self (by omega) _
  have hDl : D ≤ Nat.log n t := by
    rw [hD]
    exact Nat.log_mono_right (Nat.div_le_self t 2)
  have hnD : 1 ≤ n ^ D := Nat.one_le_pow _ _ (by omega)
  have hkle : k * (n ^ D - 1) ≤ (k - 1) * t := by
    have h1 : k * (n ^ D - 1) ≤ k * (t / 2 - 1) := Nat.mul_le_mul_left k (by omega)
    have h2 : k * (t / 2 - 1) ≤ (k - 1) * t := by
      obtain ⟨k', rfl⟩ : ∃ k', k = k' + 2 := ⟨k - 2, by omega⟩
      obtain ⟨t', ht'⟩ : ∃ t', t / 2 = t' + 1 := ⟨t / 2 - 1, by omega⟩
      have ht2 : 2 * (t' + 1) ≤ t := by omega
      rw [ht', show t' + 1 - 1 = t' by omega, show k' + 2 - 1 = k' + 1 by omega]
      nlinarith
    exact le_trans h1 h2
  obtain ⟨Y, hY⟩ : ∃ Y, Y = (k - 1) * t - k * (n ^ D - 1) := ⟨_, rfl⟩
  rw [← hY]
  have hYeq : k * (n ^ D - 1) + Y = (k - 1) * t := by omega
  have hsum : (LLgen n k D Y).sum = (k - 1) * t := by
    rw [LLgen_sum n k D Y hn, hYeq]
  refine ⟨?_, hsum, ?_, ?_⟩
  · intro e he
    obtain ⟨h, hh, rfl⟩ := LLgen_mem n k D Y e he
    exact ⟨h, le_trans hh hDl, rfl⟩
  · have hlen := LLgen_len n k D Y hn
    have htlt : t < 2 * (n * n ^ D) := by
      have : n ^ (D + 1) = n * n ^ D := by ring
      omega
    have hYdiv : Y / n ^ D ≤ (k - 1) * (2 * n) := by
      apply Nat.div_le_of_le_mul
      have hY1 : Y ≤ (k - 1) * t := by omega
      have : (k - 1) * t ≤ (k - 1) * (2 * (n * n ^ D)) := Nat.mul_le_mul_left _ htlt.le
      calc Y ≤ (k - 1) * (2 * (n * n ^ D)) := le_trans hY1 this
        _ = n ^ D * ((k - 1) * (2 * n)) := by ring
    have h1 : D * ((k + 1) * (n - 1)) ≤ Nat.log n t * ((k + 1) * n) :=
      Nat.mul_le_mul hDl (Nat.mul_le_mul_left _ (Nat.sub_le n 1))
    have h2 : (k - 1) * (2 * n) ≤ (k + 1) * (2 * n) := Nat.mul_le_mul_right _ (by omega)
    have h3 : 2 * (k + 1) * n * (Nat.log n t + 1) =
        2 * (Nat.log n t * ((k + 1) * n)) + (k + 1) * (2 * n) := by ring
    rw [h3]
    have h4 : 0 ≤ Nat.log n t * ((k + 1) * n) := Nat.zero_le _
    omega
  · intro s hs
    have hk0 : 0 < k := by omega
    let c : ℕ → ℕ := fun h => if h < D then k * (n - 1) + (Nat.digits n Y).getD h 0 else Y / n ^ D
    have hcD : c D = Y / n ^ D := by
      simp only [c]
      exact if_neg (lt_irrefl D)
    have hclt : ∀ h < D, c h = k * (n - 1) + (Nat.digits n Y).getD h 0 := by
      intro h hh
      simp only [c]
      exact if_pos hh
    have hsum2 : (LLgen n k D Y).sum = ∑ h ∈ Finset.range D, c h * n ^ h + c D * n ^ D := by
      unfold LLgen
      rw [List.sum_append, List.sum_replicate, smul_eq_mul, hcD]
      congr 1
      have := sum_map_flatMap (List.range D) (fun h =>
        List.replicate (k * (n - 1) + (Nat.digits n Y).getD h 0) (n ^ h)) id
      rw [List.map_id] at this
      rw [this, lsum_range]
      apply Finset.sum_congr rfl
      intro h hh
      rw [List.map_id, List.sum_replicate, smul_eq_mul, hclt h (Finset.mem_range.mp hh)]
    obtain ⟨u, hu1, hu2⟩ := counts (k := k) hn D c s
      (fun h hh => by rw [hclt h hh]; exact Nat.le_add_right _ _)
      (by rw [hs, ← hsum, hsum2])
    have hA1 : Asg k ((List.range D).flatMap (fun h =>
        List.replicate (k * (n - 1) + (Nat.digits n Y).getD h 0) (n ^ h)))
        (fun ℓ => ∑ h ∈ Finset.range D, u h ℓ * n ^ h) :=
      asg_flat hk0 _ (fun h ℓ => u h ℓ * n ^ h) D (fun h hh => by
        have := asg_replicate hk0 (n ^ h) (c h) (u h) (hu1 h (le_of_lt hh))
        rw [hclt h hh] at this
        exact this)
    have hA2 : Asg k (List.replicate (Y / n ^ D) (n ^ D)) (fun ℓ => u D ℓ * n ^ D) := by
      have := asg_replicate hk0 (n ^ D) (c D) (u D) (hu1 D (le_refl _))
      rw [hcD] at this
      exact this
    obtain ⟨α, hα⟩ := asg_append hA1 hA2
    refine ⟨fun i => α i.val, fun ℓ => ?_⟩
    rw [Finset.sum_filter]
    have e1 : ∑ i : Fin (LLgen n k D Y).length,
        (if α i.val = ℓ then (LLgen n k D Y).get i else 0) =
        ∑ i : Fin (LLgen n k D Y).length,
          (fun m => if α m = ℓ then (LLgen n k D Y).getD m 0 else 0) i.val := by
      apply Finset.sum_congr rfl
      intro i _
      simp only [List.get_eq_getElem, List.getD_eq_getElem _ _ i.isLt]
    rw [e1, Fin.sum_univ_eq_sum_range (fun m => if α m = ℓ then (LLgen n k D Y).getD m 0 else 0)]
    have hαℓ : ∑ m ∈ Finset.range (LLgen n k D Y).length,
        (if α m = ℓ then (LLgen n k D Y).getD m 0 else 0) =
        ∑ h ∈ Finset.range D, u h ℓ * n ^ h + u D ℓ * n ^ D := hα ℓ
    rw [hαℓ, ← hu2 ℓ, Finset.sum_range_succ]
