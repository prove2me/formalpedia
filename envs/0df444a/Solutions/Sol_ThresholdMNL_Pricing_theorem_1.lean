-- Prove2me | solution 1 for ThresholdMNL.Pricing.theorem_1
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-26T22:45:36.563288+00:00
-- url     : https://prove2.me/submissions/a1d4203e-d69b-4f06-a866-533c163fd252

import Mathlib
import Definitions.Def_ThresholdMNL_Pricing_Model

open ThresholdMNL.Pricing Finset Classical

lemma t1_profit_eq {N : ℕ} (S : Finset (Fin N)) (α c : Fin N → ℝ) (β u0 Δ : ℝ)
    (p : Fin N → ℝ) :
    profit S α c β u0 Δ p =
      (∑ i ∈ consSet S α β u0 Δ p, (p i - c i) * Real.exp (nomUtil α β p i))
        / consDenom S α β u0 Δ p := by
  unfold profit choiceProb
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl fun i hi => ?_
  have : InCons S α β u0 Δ p i := by
    unfold consSet at hi; exact (Finset.mem_filter.1 hi).2
  rw [if_pos this]; ring

lemma t1_denom_ge {N : ℕ} (S : Finset (Fin N)) (α : Fin N → ℝ) (β u0 Δ : ℝ)
    (p : Fin N → ℝ) :
    ∑ i ∈ consSet S α β u0 Δ p, Real.exp (nomUtil α β p i) ≤ consDenom S α β u0 Δ p := by
  unfold consDenom
  have : 0 ≤ (if OutsideInCons S α β u0 Δ p then Real.exp u0 else 0) := by
    split_ifs <;> positivity
  linarith

lemma t1_bound {N : ℕ} (α c : Fin N → ℝ) (β u0 Δ : ℝ) (hβ : 0 < β)
    (S : Finset (Fin N)) (p : Fin N → ℝ) :
    profit S α c β u0 Δ p ≤ ∑ i, |α i - β * c i - u0 + Δ| / β := by
  set B := ∑ i, |α i - β * c i - u0 + Δ| / β with hB
  have hB0 : 0 ≤ B := Finset.sum_nonneg fun i _ => div_nonneg (abs_nonneg _) hβ.le
  have hm : ∀ i ∈ consSet S α β u0 Δ p, p i - c i ≤ B := by
    intro i hi
    have hin : InCons S α β u0 Δ p i := by
      unfold consSet at hi; exact (Finset.mem_filter.1 hi).2
    have h1 : u0 - Δ ≤ α i - β * p i := hin.2.1
    have h2 : p i - c i ≤ (α i - β * c i - u0 + Δ) / β := by
      rw [le_div_iff₀ hβ]; nlinarith
    have h3 : (α i - β * c i - u0 + Δ) / β ≤ |α i - β * c i - u0 + Δ| / β :=
      div_le_div_of_nonneg_right (le_abs_self _) hβ.le
    have h4 : |α i - β * c i - u0 + Δ| / β ≤ B :=
      Finset.single_le_sum (f := fun i => |α i - β * c i - u0 + Δ| / β)
        (fun i _ => div_nonneg (abs_nonneg _) hβ.le) (Finset.mem_univ i)
    linarith
  rw [t1_profit_eq]
  set X := ∑ i ∈ consSet S α β u0 Δ p, Real.exp (nomUtil α β p i)
  set D := consDenom S α β u0 Δ p
  have hXD : X ≤ D := t1_denom_ge S α β u0 Δ p
  have hX0 : 0 ≤ X := Finset.sum_nonneg fun i _ => (Real.exp_pos _).le
  have hnum : ∑ i ∈ consSet S α β u0 Δ p, (p i - c i) * Real.exp (nomUtil α β p i) ≤ B * X := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun i hi =>
      mul_le_mul_of_nonneg_right (hm i hi) (Real.exp_pos _).le
  rcases (eq_or_lt_of_le (le_trans hX0 hXD)) with hD | hD
  · rw [← hD, div_zero]; exact hB0
  · rw [div_le_iff₀ hD]
    nlinarith

lemma t1_reduce {N : ℕ} (hN : 1 ≤ N) (α c : Fin N → ℝ) (β u0 Δ : ℝ)
    (hβ : 0 < β) (hΔ : 0 ≤ Δ) (hord : Antitone fun i : Fin N => α i - β * c i)
    (S : Finset (Fin N)) (p : Fin N → ℝ) :
    ∃ n : ℕ, 1 ≤ n ∧ n ≤ N ∧ ∃ p' : Fin N → ℝ,
      profit S α c β u0 Δ p ≤ profit (ordAssort N n) α c β u0 Δ p' := by
  set C := consSet S α β u0 Δ p with hCdef
  have hmemC : ∀ x, x ∈ C ↔ InCons S α β u0 Δ p x := by
    intro x; rw [hCdef]; unfold consSet; rw [Finset.mem_filter]
    exact ⟨fun h => h.2, fun h => ⟨h.1, h⟩⟩
  by_cases hC : C = ∅
  · refine ⟨1, le_refl _, hN, c, ?_⟩
    have h0 : profit S α c β u0 Δ p = 0 := by
      unfold profit; rw [← hCdef, hC, Finset.sum_empty]
    have h1 : profit (ordAssort N 1) α c β u0 Δ c = 0 := by
      unfold profit; simp
    rw [h0, h1]
  have hCne : C.Nonempty := Finset.nonempty_iff_ne_empty.2 hC
  set k := C.card with hk
  have hk1 : 1 ≤ k := Finset.card_pos.2 hCne
  have hkN : k ≤ N := by
    have := Finset.card_le_univ C; simpa using this
  refine ⟨k, hk1, hkN, ?_⟩
  set e := C.orderEmbOfFin hk.symm with he
  have E1 : ∀ t, e t ∈ C := fun t => Finset.orderEmbOfFin_mem C hk.symm t
  have E2 : ∀ x ∈ C, ∃ t, e t = x := by
    intro x hx
    have : x ∈ Set.range e := by
      rw [he, Finset.range_orderEmbOfFin]; exact hx
    exact this
  have E3 : ∀ (t : ℕ) (ht : t < k), t ≤ (e ⟨t, ht⟩).val := by
    intro t
    induction t with
    | zero => intro _; exact Nat.zero_le _
    | succ t ih =>
      intro ht
      have h1 := ih (by omega)
      have h2 : e ⟨t, by omega⟩ < e ⟨t+1, ht⟩ :=
        e.strictMono (Fin.mk_lt_mk.2 (Nat.lt_succ_self t))
      have h3 : (e ⟨t, by omega⟩).val < (e ⟨t+1, ht⟩).val := h2
      omega
  let ψ : Fin N → Fin N := fun r => if h : r.val < k then e ⟨r.val, h⟩ else r
  have hmemS : ∀ r, r ∈ ordAssort N k ↔ r.val < k := by
    intro r; unfold ordAssort; simp
  have ψC : ∀ r ∈ ordAssort N k, ψ r ∈ C := by
    intro r hr
    have h := (hmemS r).1 hr
    simp only [ψ, dif_pos h]; exact E1 _
  have ψle : ∀ r ∈ ordAssort N k, r ≤ ψ r := by
    intro r hr
    have h := (hmemS r).1 hr
    simp only [ψ, dif_pos h]
    rw [Fin.le_def]; exact E3 _ h
  set u := nomUtil α β p with hu
  let p' : Fin N → ℝ := fun r => (α r - u (ψ r)) / β
  have hu' : ∀ r, nomUtil α β p' r = u (ψ r) := by
    intro r; simp only [nomUtil, p']; field_simp; ring
  have hbij : ∀ g : Fin N → ℝ, ∑ r ∈ ordAssort N k, g (ψ r) = ∑ x ∈ C, g x := by
    intro g
    apply Finset.sum_bij (fun r _ => ψ r)
    · intro r hr; exact ψC r hr
    · intro r1 h1 r2 h2 heq
      have a1 := (hmemS r1).1 h1
      have a2 := (hmemS r2).1 h2
      simp only [ψ, dif_pos a1, dif_pos a2] at heq
      have := e.injective heq
      exact Fin.ext (by simpa using this)
    · intro x hx
      obtain ⟨t, rfl⟩ := E2 x hx
      have ht : t.val < N := lt_of_lt_of_le t.2 hkN
      refine ⟨⟨t.val, ht⟩, (hmemS _).2 t.2, ?_⟩
      simp only [ψ, dif_pos t.2]
    · intro r _; rfl
  -- all products of S_k are considered
  have hAll : ∀ r ∈ ordAssort N k, InCons (ordAssort N k) α β u0 Δ p' r := by
    intro r hr
    have hc := (hmemC _).1 (ψC r hr)
    refine ⟨hr, ?_, ?_⟩
    · rw [hu']; exact hc.2.1
    · intro l hl
      rw [hu', hu']
      exact hc.2.2 (ψ l) ((hmemC _).1 (ψC l hl)).1
  have hcons : consSet (ordAssort N k) α β u0 Δ p' = ordAssort N k := by
    unfold consSet
    exact Finset.filter_true_of_mem hAll
  -- outside option status
  have hOut : OutsideInCons (ordAssort N k) α β u0 Δ p' ↔ OutsideInCons S α β u0 Δ p := by
    constructor
    · intro h j hj
      have hSne : S.Nonempty := ⟨j, hj⟩
      obtain ⟨jm, hjmS, hjm⟩ := Finset.exists_max_image S u hSne
      have hjmC : jm ∈ C := by
        rw [hmemC]
        refine ⟨hjmS, ?_, ?_⟩
        · obtain ⟨x, hx⟩ := hCne
          have hx' := (hmemC x).1 hx
          have := hjm x hx'.1
          have := hx'.2.1
          show u0 - Δ ≤ u jm
          linarith
        · intro l hl
          have := hjm l hl
          show u l - Δ ≤ u jm
          linarith
      obtain ⟨t, ht⟩ := E2 jm hjmC
      have htN : t.val < N := lt_of_lt_of_le t.2 hkN
      have hl : (⟨t.val, htN⟩ : Fin N) ∈ ordAssort N k := (hmemS _).2 t.2
      have h1 := h _ hl
      rw [hu'] at h1
      have hψ : ψ ⟨t.val, htN⟩ = jm := by
        simp only [ψ, dif_pos t.2]; exact ht
      rw [hψ] at h1
      have := hjm j hj
      show u j - Δ ≤ u0
      linarith
    · intro h l hl
      rw [hu']
      exact h (ψ l) ((hmemC _).1 (ψC l hl)).1
  have hDen : consDenom (ordAssort N k) α β u0 Δ p' = consDenom S α β u0 Δ p := by
    unfold consDenom
    rw [hcons, ← hCdef]
    congr 1
    · simp only [hOut]
    · rw [← hbij (fun x => Real.exp (u x))]
      exact Finset.sum_congr rfl fun r _ => by rw [hu']
  refine ⟨p', ?_⟩
  rw [t1_profit_eq, t1_profit_eq, hDen, hcons, ← hCdef]
  apply div_le_div_of_nonneg_right _ (le_trans (Finset.sum_nonneg fun i _ => (Real.exp_pos _).le)
    (t1_denom_ge S α β u0 Δ p))
  rw [← hbij (fun x => (p x - c x) * Real.exp (u x))]
  apply Finset.sum_le_sum
  intro r hr
  rw [hu']
  apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
  have hα := hord (ψle r hr)
  simp only at hα
  simp only [p', hu, nomUtil]
  rw [le_sub_iff_add_le, le_div_iff₀ hβ]
  nlinarith

theorem solution {N : ℕ} (hN : 1 ≤ N) (α c : Fin N → ℝ) (β u0 Δ : ℝ)
    (hβ : 0 < β) (hΔ : 0 ≤ Δ) (hord : Antitone fun i : Fin N => α i - β * c i) :
    ∃ V : ℝ,
      IsLUB {x | ∃ (S : Finset (Fin N)) (p : Fin N → ℝ), x = profit S α c β u0 Δ p} V ∧
      ∃ n : ℕ, 1 ≤ n ∧ n ≤ N ∧
        IsLUB {x | ∃ p : Fin N → ℝ, x = profit (ordAssort N n) α c β u0 Δ p} V ∧
        ((∃ (S : Finset (Fin N)) (p : Fin N → ℝ), profit S α c β u0 Δ p = V) →
          ∃ p : Fin N → ℝ, profit (ordAssort N n) α c β u0 Δ p = V) := by
  set B := ∑ i, |α i - β * c i - u0 + Δ| / β
  set A := {x | ∃ (S : Finset (Fin N)) (p : Fin N → ℝ), x = profit S α c β u0 Δ p} with hA
  let An : ℕ → Set ℝ := fun n => {x | ∃ p : Fin N → ℝ, x = profit (ordAssort N n) α c β u0 Δ p}
  have hAnA : ∀ n, An n ⊆ A := by
    rintro n x ⟨p, rfl⟩; exact ⟨_, p, rfl⟩
  have hAnB : ∀ n, BddAbove (An n) := by
    intro n; refine ⟨B, ?_⟩
    rintro x ⟨p, rfl⟩; exact t1_bound α c β u0 Δ hβ _ p
  have hAnne : ∀ n, (An n).Nonempty := fun n => ⟨_, c, rfl⟩
  have hIcc : (Finset.Icc 1 N).Nonempty := ⟨1, Finset.mem_Icc.2 ⟨le_refl _, hN⟩⟩
  obtain ⟨n₀, hn₀, hmax⟩ := Finset.exists_max_image (Finset.Icc 1 N) (fun n => sSup (An n)) hIcc
  obtain ⟨hn₀1, hn₀N⟩ := Finset.mem_Icc.1 hn₀
  set V := sSup (An n₀)
  have hub : V ∈ upperBounds A := by
    rintro x ⟨S, p, rfl⟩
    obtain ⟨n, hn1, hnN, p', hle⟩ :=
      t1_reduce hN α c β u0 Δ hβ hΔ hord S p
    have h1 : profit (ordAssort N n) α c β u0 Δ p' ≤ sSup (An n) :=
      le_csSup (hAnB n) ⟨p', rfl⟩
    have h2 : sSup (An n) ≤ V := hmax n (Finset.mem_Icc.2 ⟨hn1, hnN⟩)
    linarith
  have hLUB : IsLUB A V := by
    refine ⟨hub, fun y hy => ?_⟩
    exact csSup_le (hAnne n₀) fun x hx => hy (hAnA n₀ hx)
  refine ⟨V, hLUB, ?_⟩
  by_cases hatt : ∃ (S : Finset (Fin N)) (p : Fin N → ℝ), profit S α c β u0 Δ p = V
  · obtain ⟨S, p, hSp⟩ := hatt
    obtain ⟨n, hn1, hnN, p', hle⟩ := t1_reduce hN α c β u0 Δ hβ hΔ hord S p
    have hle2 : profit (ordAssort N n) α c β u0 Δ p' ≤ V := hub ⟨_, p', rfl⟩
    have heq : profit (ordAssort N n) α c β u0 Δ p' = V := by linarith
    refine ⟨n, hn1, hnN, ?_, fun _ => ⟨p', heq⟩⟩
    refine ⟨fun x hx => hub (hAnA n hx), fun y hy => ?_⟩
    exact heq ▸ hy ⟨p', rfl⟩
  · refine ⟨n₀, hn₀1, hn₀N, ?_, fun h => absurd h hatt⟩
    exact isLUB_csSup (hAnne n₀) (hAnB n₀)
