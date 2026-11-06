-- Prove2me | solution 1 for PolylogKServer.Allocation.frac_alloc_competitive
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-06T03:27:11.849182+00:00
-- url     : https://prove2.me/submissions/019d32a2-6c71-4670-914c-f569c0ff1fe5

import Mathlib
import Definitions.Def_PolylogKServer_Allocation_Problem

set_option autoImplicit false
set_option maxHeartbeats 1000000



namespace Ba300cc1
open PolylogKServer.Allocation Finset

variable {d k : ℕ}

/-- Run a step function along a request list. -/
def run (x0 : FracState d k) (S : FracState d k → Request d k → FracState d k)
    (l : List (Request d k)) : FracState d k :=
  l.foldl S x0

/-- The online algorithm given by a step function. -/
def ofStep (x0 : FracState d k) (S : FracState d k → Request d k → FracState d k) :
    FracAlg d k :=
  ⟨run x0 S⟩

lemma run_take_succ (x0 : FracState d k) (S : FracState d k → Request d k → FracState d k)
    (ρ : List (Request d k)) (t : ℕ) (ht : t < ρ.length) :
    run x0 S (ρ.take (t + 1)) = S (run x0 S (ρ.take t)) (ρ[t]'ht) := by
  unfold run
  rw [List.take_add_one, List.getElem?_eq_getElem ht, Option.toList_some, List.foldl_append,
    List.foldl_cons, List.foldl_nil]

/-- Quota after `t` requests, as a natural number. -/
def qN (κ₀ : ℕ) (ρ : List (Request d k)) : ℕ → ℕ
  | 0 => κ₀
  | t + 1 => ((ρ[t]?).map Request.quota).getD 0

lemma qN_succ (κ₀ : ℕ) (ρ : List (Request d k)) (t : ℕ) (ht : t < ρ.length) :
    qN κ₀ ρ (t + 1) = (ρ[t]'ht).quota := by
  simp [qN, List.getElem?_eq_getElem ht]

lemma quotaAt_eq (κ₀ : ℕ) (ρ : List (Request d k)) (t : ℕ) :
    quotaAt κ₀ ρ t = (qN κ₀ ρ t : ℝ) := by
  cases t with
  | zero => simp [quotaAt, qN]
  | succ t =>
    simp only [quotaAt, qN]

lemma telescope (N : ℕ) (f g P : ℕ → ℝ) (h : ∀ t < N, f t + P (t + 1) - P t ≤ g t) :
    ∑ t ∈ range N, f t ≤ ∑ t ∈ range N, g t + (P 0 - P N) := by
  have h1 : ∑ t ∈ range N, (f t + (P (t + 1) - P t)) ≤ ∑ t ∈ range N, g t :=
    Finset.sum_le_sum fun t ht => by have := h t (Finset.mem_range.1 ht); linarith
  rw [Finset.sum_add_distrib, Finset.sum_range_sub] at h1
  linarith

lemma le_of_forall_inf {θ a H G : ℝ} (hθ : 0 < θ) (T : Set ℝ) (hne : T.Nonempty)
    (h : ∀ c ∈ T, H ≤ θ * (c + G) + a) : H ≤ θ * (sInf T + G) + a := by
  have h2 : ∀ c ∈ T, (H - a) / θ - G ≤ c := fun c hc => by
    have h3 := h c hc
    have : (H - a) / θ ≤ c + G := by rw [div_le_iff₀ hθ]; linarith
    linarith
  have h3 := le_csInf hne h2
  have h4 : H - a ≤ (sInf T + G) * θ := (div_le_iff₀ hθ).1 (by linarith)
  linarith

lemma run_inv (S : FracState d k → Request d k → FracState d k)
    (Inv : FracState d k → ℕ → Prop)
    (hInvS : ∀ x q r, Inv x q → Request.Valid r → Inv (S x r) r.quota) :
    ∀ (l : List (Request d k)) (x : FracState d k) (q : ℕ), Inv x q → ValidSeq l →
      ∃ q', Inv (l.foldl S x) q' := by
  intro l
  induction l with
  | nil => intro x q hx _; exact ⟨q, hx⟩
  | cons r l ih =>
    intro x q hx hl
    have hr : r.Valid := hl r (by simp)
    exact ih (S x r) r.quota (hInvS x q r hx hr) (fun r' hr' => hl r' (by simp [hr']))

/-- **Potential-function reduction.** An online step rule with an invariant, two bounded
potentials and the per-request amortized inequalities against an arbitrary integral move of
the offline schedule is `(θ, γ)`-competitive. -/
theorem competitive_of_step (w : Fin d → ℝ) (n₀ : Fin d → ℕ) (κ₀ : ℕ) (θ γ B : ℝ)
    (hθ : 0 < θ) (hγ : 0 < γ) (hn₀ : ∀ i, n₀ i ≤ k) (hsum : ∑ i, n₀ i ≤ κ₀)
    (x0 : FracState d k) (hx0 : x0 = pointMass n₀)
    (S : FracState d k → Request d k → FracState d k)
    (Inv : FracState d k → ℕ → Prop) (hInv0 : Inv x0 κ₀)
    (hInvS : ∀ x q r, Inv x q → Request.Valid r → Inv (S x r) r.quota)
    (hFeas : ∀ x q, Inv x q → FracFeasible x q)
    (Ψh Ψm : FracState d k → (Fin d → ℕ) → ℝ)
    (hB : ∀ x q (n : Fin d → ℕ), Inv x q → (∀ i, n i ≤ k) → |Ψh x n| ≤ B ∧ |Ψm x n| ≤ B)
    (hstep : ∀ (x : FracState d k) (q : ℕ) (r : Request d k) (n n' : Fin d → ℕ),
      Inv x q → r.Valid → (∀ i, n i ≤ k) → ∑ i, n i ≤ q → (∀ i, n' i ≤ k) →
      ∑ i, n' i ≤ r.quota →
      hitCost r (S x r) + Ψh (S x r) n' - Ψh x n ≤
          θ * (r.hAt (n' r.loc) + ∑ i, w i * |((n' i : ℕ) : ℝ) - ((n i : ℕ) : ℝ)| +
            wmax w * |(r.quota : ℝ) - (q : ℝ)|) ∧
      moveCost w x (S x r) + Ψm (S x r) n' - Ψm x n ≤
          γ * (r.hAt (n' r.loc) + ∑ i, w i * |((n' i : ℕ) : ℝ) - ((n i : ℕ) : ℝ)| +
            wmax w * |(r.quota : ℝ) - (q : ℝ)|)) :
    (ofStep x0 S).IsCompetitive w n₀ κ₀ θ γ := by
  refine ⟨hx0, ?_, 2 * B, ?_⟩
  · intro l r hl
    have hl' : ValidSeq l := fun r' hr' => hl r' (by simp [hr'])
    have hr : r.Valid := hl r (by simp)
    obtain ⟨q, hq⟩ := run_inv S Inv hInvS l x0 κ₀ hInv0 hl'
    have : (ofStep x0 S).state (l ++ [r]) = S (l.foldl S x0) r := by
      simp [ofStep, run, List.foldl_append]
    rw [this]
    exact hFeas _ _ (hInvS _ _ _ hq hr)
  · intro ρ hρ
    set X : ℕ → FracState d k := fun t => run x0 S (ρ.take t) with hXdef
    have hX : ∀ t (ht : t < ρ.length), X (t + 1) = S (X t) (ρ[t]'ht) := fun t ht =>
      run_take_succ x0 S ρ t ht
    have hInvX : ∀ t, t ≤ ρ.length → Inv (X t) (qN κ₀ ρ t) := by
      intro t
      induction t with
      | zero => intro _; simpa [X, run, qN] using hInv0
      | succ t ih =>
        intro ht
        rw [hX t (by omega), qN_succ κ₀ ρ t (by omega)]
        exact hInvS _ _ _ (ih (by omega)) (hρ _ (List.getElem_mem _))
    have key : ∀ n, IntFeasible n₀ ρ n →
        (ofStep x0 S).hitTotal ρ ≤ θ * (intCost w ρ n + wmax w * quotaVariation κ₀ ρ) + 2 * B ∧
        (ofStep x0 S).moveTotal w ρ ≤
          γ * (intCost w ρ n + wmax w * quotaVariation κ₀ ρ) + 2 * B := by
      intro n hn
      obtain ⟨hn0, hnt⟩ := hn
      have hnk : ∀ t, t ≤ ρ.length → (∀ i, n t i ≤ k) ∧ ∑ i, n t i ≤ qN κ₀ ρ t := by
        intro t ht
        cases t with
        | zero => rw [hn0]; exact ⟨hn₀, hsum⟩
        | succ t =>
          obtain ⟨h1, h2⟩ := hnt t (by omega)
          rw [qN_succ κ₀ ρ t (by omega)]
          exact ⟨h1, h2⟩
      set e : ℕ → ℝ := fun t =>
        (((ρ[t]?).map fun r => r.hAt (n (t + 1) r.loc)).getD 0) +
          ∑ i, w i * |((n (t + 1) i : ℕ) : ℝ) - ((n t i : ℕ) : ℝ)| +
          wmax w * |quotaAt κ₀ ρ (t + 1) - quotaAt κ₀ ρ t| with he
      have hsumE : intCost w ρ n + wmax w * quotaVariation κ₀ ρ = ∑ t ∈ range ρ.length, e t := by
        simp only [intCost, quotaVariation, he, Finset.mul_sum, ← Finset.sum_add_distrib]
      have hPb : ∀ t, t ≤ ρ.length → |Ψh (X t) (n t)| ≤ B ∧ |Ψm (X t) (n t)| ≤ B :=
        fun t ht => hB _ _ _ (hInvX t ht) (hnk t ht).1
      have hstep' : ∀ t (ht : t < ρ.length),
          hitCost (ρ[t]'ht) (X (t + 1)) + Ψh (X (t + 1)) (n (t + 1)) - Ψh (X t) (n t) ≤ θ * e t ∧
          moveCost w (X t) (X (t + 1)) + Ψm (X (t + 1)) (n (t + 1)) - Ψm (X t) (n t) ≤
            γ * e t := by
        intro t ht
        have hq1 := quotaAt_eq κ₀ ρ (t + 1)
        have hq0 := quotaAt_eq κ₀ ρ t
        rw [qN_succ κ₀ ρ t ht] at hq1
        have hee : e t = (ρ[t]'ht).hAt (n (t + 1) (ρ[t]'ht).loc) +
            ∑ i, w i * |((n (t + 1) i : ℕ) : ℝ) - ((n t i : ℕ) : ℝ)| +
            wmax w * |((ρ[t]'ht).quota : ℝ) - (qN κ₀ ρ t : ℝ)| := by
          simp only [he, List.getElem?_eq_getElem ht, Option.map_some, Option.getD_some, hq1, hq0]
        rw [hee, hX t ht]
        have h1 := hnk t (by omega)
        have h2 := hnk (t + 1) (by omega)
        rw [qN_succ κ₀ ρ t ht] at h2
        exact hstep (X t) (qN κ₀ ρ t) (ρ[t]'ht) (n t) (n (t + 1)) (hInvX t (by omega))
          (hρ _ (List.getElem_mem _)) h1.1 h1.2 h2.1 h2.2
      constructor
      · have hT := telescope ρ.length
          (fun t => (((ρ[t]?).map fun r => hitCost r ((ofStep x0 S).state (ρ.take (t + 1))))).getD 0)
          (fun t => θ * e t) (fun t => Ψh (X t) (n t)) (by
            intro t ht
            have := (hstep' t ht).1
            simp only [List.getElem?_eq_getElem ht, Option.map_some, Option.getD_some]
            exact this)
        have hb0 := (hPb 0 (by omega)).1
        have hbN := (hPb ρ.length le_rfl).1
        rw [← Finset.mul_sum, ← hsumE] at hT
        have : Ψh (X 0) (n 0) - Ψh (X ρ.length) (n ρ.length) ≤ 2 * B := by
          have := abs_le.1 hb0; have := abs_le.1 hbN; linarith
        unfold FracAlg.hitTotal
        linarith
      · have hT := telescope ρ.length
          (fun t => moveCost w ((ofStep x0 S).state (ρ.take t))
            ((ofStep x0 S).state (ρ.take (t + 1))))
          (fun t => γ * e t) (fun t => Ψm (X t) (n t)) (by
            intro t ht
            exact (hstep' t ht).2)
        have hb0 := (hPb 0 (by omega)).2
        have hbN := (hPb ρ.length le_rfl).2
        rw [← Finset.mul_sum, ← hsumE] at hT
        have : Ψm (X 0) (n 0) - Ψm (X ρ.length) (n ρ.length) ≤ 2 * B := by
          have := abs_le.1 hb0; have := abs_le.1 hbN; linarith
        unfold FracAlg.moveTotal
        linarith
    have hne : {c : ℝ | ∃ n : ℕ → Fin d → ℕ, IntFeasible n₀ ρ n ∧ c = intCost w ρ n}.Nonempty := by
      refine ⟨intCost w ρ (fun t => if t = 0 then n₀ else 0), _, ?_, rfl⟩
      refine ⟨by simp, fun t ht => ⟨fun i => by simp, by simp⟩⟩
    constructor
    · exact le_of_forall_inf hθ _ hne (fun c ⟨n, hn, hc⟩ => hc ▸ (key n hn).1)
    · exact le_of_forall_inf hγ _ hne (fun c ⟨n, hn, hc⟩ => hc ▸ (key n hn).2)

end Ba300cc1



namespace Ba300cc1
open PolylogKServer.Allocation Finset

variable {d k : ℕ}

/-- The marginal cost `λ_j = h(j-1) - h(j)` (used for `1 ≤ j ≤ k`). -/
noncomputable def lam (r : Request d k) (j : ℕ) : ℝ := r.hAt (j - 1) - r.hAt j

lemma sum_Ioc_telescope (f : ℕ → ℝ) (n m : ℕ) (h : n ≤ m) :
    ∑ j ∈ Ioc n m, (f (j - 1) - f j) = f n - f m := by
  induction m, h using Nat.le_induction with
  | base => simp
  | succ m hm ih =>
    rw [Finset.sum_Ioc_succ_top hm, ih]
    simp

lemma filter_lt_Icc (n k : ℕ) : (Icc 1 k).filter (fun j => n < j) = Ioc n k := by
  ext j; simp only [mem_filter, mem_Icc, mem_Ioc]; omega

lemma hAt_eq_sum (r : Request d k) (n : ℕ) (hn : n ≤ k) :
    r.hAt n = r.hAt k + ∑ j ∈ Icc 1 k, (if n < j then lam r j else 0) := by
  rw [← Finset.sum_filter, filter_lt_Icc]
  unfold lam
  rw [sum_Ioc_telescope (fun j => r.hAt j) n k hn]
  ring

lemma hAt_fin (r : Request d k) (j : Fin (k + 1)) : r.hAt (j : ℕ) = r.h j := by
  unfold Request.hAt
  congr 1
  ext
  simp only
  have := j.isLt
  omega

/-- Hit cost in cumulative (`y`) form: `∑_j h(j) x_j = h(k) ∑_j x_j + ∑_{j=1}^k λ_j y_j`. -/
lemma hitCost_eq (r : Request d k) (x : FracState d k) :
    hitCost r x = r.hAt k * (∑ j, x r.loc j) +
      ∑ j ∈ Icc 1 k, lam r j * cumul x r.loc j := by
  unfold hitCost cumul
  have h1 : ∀ j : Fin (k + 1), r.h j * x r.loc j =
      r.hAt k * x r.loc j + ∑ j2 ∈ Icc 1 k, lam r j2 * (if (j : ℕ) < j2 then x r.loc j else 0) := by
    intro j
    rw [← hAt_fin, hAt_eq_sum r j (by have := j.isLt; omega), add_mul, Finset.sum_mul]
    congr 1
    refine Finset.sum_congr rfl fun j2 _ => ?_
    split_ifs <;> ring
  rw [Finset.sum_congr rfl fun j _ => h1 j, Finset.sum_add_distrib, Finset.mul_sum]
  congr 1
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j2 _ => ?_
  rw [Finset.mul_sum]

lemma cumul_pointMass (n : Fin d → ℕ) (hn : ∀ i, n i ≤ k) (i : Fin d) (j : ℕ) :
    cumul (pointMass (k := k) n) i j = if n i < j then 1 else 0 := by
  unfold cumul pointMass
  have hlt : n i < k + 1 := Nat.lt_succ_of_le (hn i)
  have key : ∀ j' : Fin (k + 1),
      (if (j' : ℕ) < j then (if (j' : ℕ) = n i then (1 : ℝ) else 0) else 0) =
        if j' = ⟨n i, hlt⟩ then (if n i < j then 1 else 0) else 0 := by
    intro j'
    by_cases h : (j' : ℕ) = n i
    · have e : j' = ⟨n i, hlt⟩ := Fin.ext h
      subst e
      simp
    · have e : j' ≠ ⟨n i, hlt⟩ := fun e => h (by rw [e])
      simp [h, e]
  rw [Finset.sum_congr rfl fun j' _ => key j', Finset.sum_ite_eq']
  simp

/-- `|a - b| = ∑_{j=1}^k |1[a<j] - 1[b<j]|` for `a, b ≤ k`. -/
lemma abs_sub_eq_sum_ind (a b k : ℕ) (ha : a ≤ k) (hb : b ≤ k) :
    |((a : ℕ) : ℝ) - ((b : ℕ) : ℝ)| =
      ∑ j ∈ Icc 1 k, |(if a < j then (1 : ℝ) else 0) - (if b < j then 1 else 0)| := by
  wlog hab : a ≤ b generalizing a b
  · rw [abs_sub_comm, this b a hb ha (by omega)]
    refine Finset.sum_congr rfl fun j _ => abs_sub_comm _ _
  have hterm : ∀ j, |(if a < j then (1 : ℝ) else 0) - (if b < j then 1 else 0)| =
      if a < j ∧ j ≤ b then 1 else 0 := by
    intro j
    by_cases h1 : a < j <;> by_cases h2 : b < j <;> simp [h1, h2] <;> omega
  rw [Finset.sum_congr rfl fun j _ => hterm j, Finset.sum_boole]
  have hf : (Icc 1 k).filter (fun j => a < j ∧ j ≤ b) = Ioc a b := by
    ext j; simp only [mem_filter, mem_Icc, mem_Ioc]; omega
  have hle : ((a : ℕ) : ℝ) ≤ ((b : ℕ) : ℝ) := by exact_mod_cast hab
  rw [hf, Nat.card_Ioc, abs_of_nonpos (by linarith), Nat.cast_sub hab]
  ring


lemma cumul_bounds (x : FracState d k) (q : ℕ) (hx : FracFeasible x q) (i : Fin d) (j : ℕ) :
    0 ≤ cumul x i j ∧ cumul x i j ≤ 1 := by
  obtain ⟨h0, h1, _⟩ := hx
  unfold cumul
  constructor
  · exact Finset.sum_nonneg fun j' _ => by split_ifs <;> simp [h0]
  · rw [← h1 i]
    exact Finset.sum_le_sum fun j' _ => by split_ifs <;> simp [h0]

/-- `log((1+β)/(y+β))`, the per-coordinate term of the movement potential. -/
noncomputable def Lg (β y : ℝ) : ℝ := Real.log ((1 + β) / (y + β))

lemma Lg_nonneg {β y : ℝ} (hβ : 0 < β) (hy0 : 0 ≤ y) (hy1 : y ≤ 1) : 0 ≤ Lg β y := by
  unfold Lg
  apply Real.log_nonneg
  rw [le_div_iff₀ (by linarith)]
  linarith

lemma Lg_le {β y : ℝ} (hβ : 0 < β) (hy0 : 0 ≤ y) : Lg β y ≤ Real.log ((1 + β) / β) := by
  unfold Lg
  apply Real.log_le_log (div_pos (by linarith) (by linarith))
  exact div_le_div_of_nonneg_left (by linarith) hβ (by linarith)

/-- The movement potential `Φ_m(y, n) = c ∑_i w_i ∑_{j > n_i} log((1+β)/(y_{ij}+β))`. -/
noncomputable def Phim (c β : ℝ) (w : Fin d → ℝ) (x : FracState d k) (n : Fin d → ℕ) : ℝ :=
  c * ∑ i, w i * ∑ j ∈ Icc 1 k, (if n i < j then Lg β (cumul x i j) else 0)

/-- An offline move `n → n'` raises `Φ_m` by at most `c α ∑ w_i |n'_i - n_i|`. -/
lemma Phim_move (c β : ℝ) (hc : 0 ≤ c) (hβ : 0 < β) (w : Fin d → ℝ) (hw : ∀ i, 0 < w i)
    (x : FracState d k) (hx : ∀ i j, 0 ≤ cumul x i j ∧ cumul x i j ≤ 1)
    (n n' : Fin d → ℕ) (hn : ∀ i, n i ≤ k) (hn' : ∀ i, n' i ≤ k) :
    Phim c β w x n' - Phim c β w x n ≤
      c * Real.log ((1 + β) / β) * ∑ i, w i * |((n' i : ℕ) : ℝ) - ((n i : ℕ) : ℝ)| := by
  unfold Phim
  rw [← mul_sub, ← Finset.sum_sub_distrib, mul_assoc]
  apply mul_le_mul_of_nonneg_left _ hc
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  have hj : ∀ j ∈ Icc 1 k, ((if n' i < j then Lg β (cumul x i j) else 0) -
      (if n i < j then Lg β (cumul x i j) else 0)) ≤
      Real.log ((1 + β) / β) * |(if n' i < j then (1 : ℝ) else 0) - (if n i < j then 1 else 0)| := by
    intro j _
    have hL0 := Lg_nonneg hβ (hx i j).1 (hx i j).2
    have hL1 := Lg_le (β := β) hβ (hx i j).1
    by_cases h1 : n' i < j <;> by_cases h2 : n i < j <;> simp [h1, h2] <;> linarith
  have hs := Finset.sum_le_sum hj
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← abs_sub_eq_sum_ind _ _ k (hn' i) (hn i)] at hs
  have hwi := (hw i).le
  have := mul_le_mul_of_nonneg_left hs hwi
  linarith [this]

end Ba300cc1



namespace Ba300cc1
open PolylogKServer.Allocation Finset

variable {d k : ℕ}

/-- Extend `y` (meaningful for `1 ≤ j ≤ k`) by `y_0 = 0` and `y_j = 1` for `j > k`. -/
noncomputable def ext (k : ℕ) (y : ℕ → ℝ) (j : ℕ) : ℝ :=
  if j = 0 then 0 else if j ≤ k then y j else 1

/-- The fractional state with cumulative vector `y`: `x_{i,j} = y_{i,j+1} - y_{i,j}`. -/
noncomputable def ofY (y : Fin d → ℕ → ℝ) : FracState d k :=
  fun i j => ext k (y i) ((j : ℕ) + 1) - ext k (y i) j

lemma sum_fin_ite_lt (m j : ℕ) (g : ℕ → ℝ) :
    ∑ j' : Fin m, (if (j' : ℕ) < j then g j' else 0) = ∑ j' ∈ range (min j m), g j' := by
  rw [Fin.sum_univ_eq_sum_range (fun j' => if j' < j then g j' else 0) m, ← Finset.sum_filter]
  congr 1
  ext j'; simp only [mem_filter, mem_range]; omega

lemma cumul_ofY (y : Fin d → ℕ → ℝ) (i : Fin d) (j : ℕ) (hj : j ≤ k + 1) :
    cumul (ofY (k := k) y) i j = ext k (y i) j := by
  unfold cumul ofY
  rw [sum_fin_ite_lt (k + 1) j (fun j' => ext k (y i) (j' + 1) - ext k (y i) j'),
    min_eq_left hj, Finset.sum_range_sub]
  simp [ext]

lemma abel_sum (e : ℕ → ℝ) (m : ℕ) :
    ∑ j ∈ range (m + 1), (j : ℝ) * (e (j + 1) - e j) = m * e (m + 1) - ∑ j ∈ Icc 1 m, e j := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, ih, Finset.sum_Icc_succ_top (by omega)]
    push_cast
    ring

lemma servers_ofY (y : Fin d → ℕ → ℝ) (i : Fin d) :
    ∑ j : Fin (k + 1), ((j : ℕ) : ℝ) * ofY (k := k) y i j = k - ∑ j ∈ Icc 1 k, y i j := by
  unfold ofY
  rw [Fin.sum_univ_eq_sum_range (fun j => (j : ℝ) * (ext k (y i) (j + 1) - ext k (y i) j)) (k + 1),
    abel_sum]
  have h1 : ext k (y i) (k + 1) = 1 := by simp [ext]
  have h2 : ∑ j ∈ Icc 1 k, ext k (y i) j = ∑ j ∈ Icc 1 k, y i j :=
    Finset.sum_congr rfl fun j hj => by
      have := Finset.mem_Icc.1 hj
      simp [ext, show j ≠ 0 by omega, show j ≤ k from this.2]
  rw [h1, h2, mul_one]

/-- A cumulative vector that is monotone in `j`, lies in `[0,1]` and meets the quota gives a
feasible fractional state. -/
lemma feasible_ofY (y : Fin d → ℕ → ℝ) (κ : ℕ)
    (hmono : ∀ i j, j ≤ k → ext k (y i) j ≤ ext k (y i) (j + 1))
    (hq : (d : ℝ) * k - κ ≤ ∑ i, ∑ j ∈ Icc 1 k, y i j) :
    FracFeasible (ofY (k := k) y) κ := by
  refine ⟨fun i j => ?_, fun i => ?_, ?_⟩
  · unfold ofY
    have := hmono i j (by have := j.isLt; omega)
    linarith
  · unfold ofY
    rw [Fin.sum_univ_eq_sum_range (fun j => ext k (y i) (j + 1) - ext k (y i) j) (k + 1),
      Finset.sum_range_sub]
    simp [ext]
  · simp only [servers_ofY, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    linarith

end Ba300cc1



namespace Ba300cc1
open Finset

/-- If `2 t A + t² B ≥ 0` for all small `t > 0` (with `B ≥ 0`), then `A ≥ 0`. -/
lemma nonneg_of_quad {A B t0 : ℝ} (hB : 0 ≤ B) (ht0 : 0 < t0)
    (h : ∀ t, 0 < t → t ≤ t0 → 0 ≤ 2 * t * A + t ^ 2 * B) : 0 ≤ A := by
  by_contra hA
  push_neg at hA
  set t := min t0 (-A / (B + 1)) with ht
  have htpos : 0 < t := lt_min ht0 (div_pos (by linarith) (by linarith))
  have h1 := h t htpos (min_le_left _ _)
  have h2 : t ≤ -A / (B + 1) := min_le_right _ _
  have h3 : t * (B + 1) ≤ -A := by rwa [le_div_iff₀ (by linarith)] at h2
  have h4 : t * (t * (B + 1)) ≤ t * (-A) := mul_le_mul_of_nonneg_left h3 htpos.le
  nlinarith

lemma abs_le_of_sq_le {x K : ℝ} (hK : 0 ≤ K) (h : x ^ 2 ≤ K) : |x| ≤ K + 1 := by
  by_contra hc
  push_neg at hc
  have h1 : (K + 1) ^ 2 < |x| ^ 2 := by
    have : 0 ≤ K + 1 := by linarith
    nlinarith
  rw [sq_abs] at h1
  nlinarith

/-- Isotonic regression on `Fin k` (equal weights), characterized by suffix sums. -/
lemma iso_fin (k : ℕ) (c : Fin k → ℝ) : ∃ s : Fin k → ℝ, Monotone s ∧
    (∑ a, (s a - c a) = 0) ∧
    (∀ m : Fin k, 0 ≤ ∑ a ∈ univ.filter (fun a => m ≤ a), (s a - c a)) ∧
    (∀ (m : Fin k) (δ : ℝ), 0 < δ → (∀ a, a < m → s a + δ ≤ s m) →
      ∑ a ∈ univ.filter (fun a => m ≤ a), (s a - c a) = 0) := by
  set M : ℝ := ∑ a, |c a| + ∑ a, c a ^ 2 + 2 with hM
  set K : Set (Fin k → ℝ) := {s | Monotone s ∧ ∀ a, s a ∈ Set.Icc (-M) M} with hK
  have hKc : IsCompact K := by
    have hbox : IsCompact (Set.pi Set.univ fun _ : Fin k => Set.Icc (-M) M) :=
      isCompact_univ_pi fun _ => isCompact_Icc
    have hmono : IsClosed {s : Fin k → ℝ | Monotone s} := by
      have : {s : Fin k → ℝ | Monotone s} = ⋂ a, ⋂ b, ⋂ (_ : a ≤ b), {s | s a ≤ s b} := by
        ext s; simp [Monotone]
      rw [this]
      exact isClosed_iInter fun a => isClosed_iInter fun b => isClosed_iInter fun _ =>
        isClosed_le (continuous_apply a) (continuous_apply b)
    have : K = {s : Fin k → ℝ | Monotone s} ∩ Set.pi Set.univ fun _ => Set.Icc (-M) M := by
      ext s; simp only [hK, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_pi, Set.mem_univ, forall_const]
    rw [this]
    exact hbox.inter_left hmono
  have hM0 : 0 ≤ ∑ a, |c a| + ∑ a, c a ^ 2 :=
    add_nonneg (sum_nonneg fun a _ => abs_nonneg _) (sum_nonneg fun a _ => sq_nonneg _)
  have h0K : (0 : Fin k → ℝ) ∈ K := ⟨fun _ _ _ => le_refl _, fun a => ⟨by simp; linarith, by simp; linarith⟩⟩
  set f : (Fin k → ℝ) → ℝ := fun s => ∑ a, (s a - c a) ^ 2 with hf
  have hfc : ContinuousOn f K := by
    apply Continuous.continuousOn
    simp only [hf]
    fun_prop
  obtain ⟨s, hsK, hsmin⟩ := hKc.exists_isMinOn ⟨0, h0K⟩ hfc
  have hmin : ∀ s' ∈ K, f s ≤ f s' := fun s' hs' => hsmin hs'
  -- a priori bound: |s a| ≤ M - 1
  have hbd : ∀ a, |s a| ≤ M - 1 := by
    intro a
    have h1 : f s ≤ f 0 := hmin 0 h0K
    have h2 : (s a - c a) ^ 2 ≤ f s :=
      single_le_sum (f := fun b => (s b - c b) ^ 2) (fun b _ => sq_nonneg _) (mem_univ a)
    have h3 : f 0 = ∑ a, c a ^ 2 := by simp [hf]
    have h4 : |s a - c a| ≤ ∑ a, c a ^ 2 + 1 :=
      abs_le_of_sq_le (sum_nonneg fun a _ => sq_nonneg _) (by linarith)
    have h5 : |c a| ≤ ∑ a, |c a| :=
      single_le_sum (f := fun b => |c b|) (fun b _ => abs_nonneg _) (mem_univ a)
    have h6 : |s a| ≤ |s a - c a| + |c a| := by
      have := abs_add_le (s a - c a) (c a); simpa using this
    linarith
  -- directional optimality
  have hdir : ∀ (v : Fin k → ℝ) (t0 : ℝ), 0 < t0 → t0 ≤ 1 → (∀ a, |v a| ≤ 1) →
      (∀ t, 0 < t → t ≤ t0 → Monotone (fun a => s a + t * v a)) →
      0 ≤ ∑ a, (s a - c a) * v a := by
    intro v t0 ht0 ht01 hv hmon
    have hB : 0 ≤ ∑ a, v a ^ 2 := sum_nonneg fun a _ => sq_nonneg _
    refine nonneg_of_quad (A := ∑ a, (s a - c a) * v a) (B := ∑ a, v a ^ 2) hB ht0 ?_
    intro t ht htt
    have hmem : (fun a => s a + t * v a) ∈ K := by
      refine ⟨hmon t ht htt, fun a => ?_⟩
      have h1 := hbd a
      have h2 : |t * v a| ≤ 1 := by
        rw [abs_mul, abs_of_pos ht]
        have := hv a
        nlinarith [abs_nonneg (v a)]
      rw [abs_le] at h1 h2
      exact ⟨by linarith, by linarith⟩
    have h1 := hmin _ hmem
    have h2 : f (fun a => s a + t * v a) - f s =
        2 * t * (∑ a, (s a - c a) * v a) + t ^ 2 * ∑ a, v a ^ 2 := by
      simp only [hf, mul_sum, ← sum_sub_distrib, ← sum_add_distrib]
      exact sum_congr rfl fun a _ => by ring
    linarith
  have hsmono : Monotone s := hsK.1
  have hseq : ∀ m : Fin k, ∑ a, (s a - c a) * (if m ≤ a then 1 else 0) =
      ∑ a ∈ univ.filter (fun a => m ≤ a), (s a - c a) := by
    intro m
    rw [sum_filter]
    exact sum_congr rfl fun a _ => by split_ifs <;> ring
  refine ⟨s, hsmono, ?_, ?_, ?_⟩
  · have h1 := hdir (fun _ => 1) 1 one_pos le_rfl (fun _ => by simp)
      (fun t _ _ a b hab => by simp only; linarith [hsmono hab])
    have h2 := hdir (fun _ => -1) 1 one_pos le_rfl (fun _ => by simp)
      (fun t _ _ a b hab => by simp only; linarith [hsmono hab])
    simp only [mul_one, mul_neg, sum_neg_distrib] at h1 h2
    linarith
  · intro m
    have h1 := hdir (fun a => if m ≤ a then 1 else 0) 1 one_pos le_rfl
      (fun a => by split_ifs <;> simp)
      (fun t ht _ a b hab => by
        simp only
        have := hsmono hab
        split_ifs with h1 h2 h2
        · linarith
        · exact absurd (le_trans h1 hab) h2
        · linarith
        · linarith)
    rwa [hseq] at h1
  · intro m δ hδ hgap
    have hpos : 0 ≤ ∑ a ∈ univ.filter (fun a => m ≤ a), (s a - c a) := by
      have h1 := hdir (fun a => if m ≤ a then 1 else 0) 1 one_pos le_rfl
        (fun a => by split_ifs <;> simp)
        (fun t ht _ a b hab => by
          simp only
          have := hsmono hab
          split_ifs with h1 h2 h2
          · linarith
          · exact absurd (le_trans h1 hab) h2
          · linarith
          · linarith)
      rwa [hseq] at h1
    have h1 := hdir (fun a => if m ≤ a then -1 else 0) (min 1 δ) (lt_min one_pos hδ)
      (min_le_left _ _) (fun a => by split_ifs <;> simp)
      (fun t ht htt a b hab => by
        simp only
        have := hsmono hab
        have htd : t ≤ δ := le_trans htt (min_le_right _ _)
        split_ifs with h1 h2 h2
        · linarith
        · exact absurd (le_trans h1 hab) h2
        · have hab' : a < m := lt_of_not_ge h1
          have := hgap a hab'
          have := hsmono h2
          linarith
        · linarith)
    have h2 : ∑ a, (s a - c a) * (if m ≤ a then -1 else 0) =
        -∑ a ∈ univ.filter (fun a => m ≤ a), (s a - c a) := by
      rw [sum_filter, ← sum_neg_distrib]
      exact sum_congr rfl fun a _ => by split_ifs <;> ring
    rw [h2] at h1
    linarith

/-- Isotonic regression on `Icc 1 k ⊆ ℕ`: monotone `s` with residual suffix sums
`R_m = ∑_{a ∈ Icc m k} (s a - c a)` nonnegative, `R_1 = 0`, and `R_m = 0` at every jump. -/
theorem iso_exists (k : ℕ) (c : ℕ → ℝ) : ∃ s : ℕ → ℝ,
    (∀ a b, 1 ≤ a → a ≤ b → b ≤ k → s a ≤ s b) ∧
    (∀ m, 1 ≤ m → 0 ≤ ∑ a ∈ Icc m k, (s a - c a)) ∧
    (∑ a ∈ Icc 1 k, (s a - c a) = 0) ∧
    (∀ m, 2 ≤ m → m ≤ k → s (m - 1) < s m → ∑ a ∈ Icc m k, (s a - c a) = 0) := by
  obtain ⟨sf, hmono, htot, hsuf, hjump⟩ := iso_fin k (fun b => c (b.1 + 1))
  set s : ℕ → ℝ := fun a => if h : 1 ≤ a ∧ a ≤ k then sf ⟨a - 1, by omega⟩ else 0 with hs
  have hsv : ∀ b : Fin k, s (b.1 + 1) = sf b := by
    intro b
    have h : 1 ≤ b.1 + 1 ∧ b.1 + 1 ≤ k := ⟨by omega, b.2⟩
    simp only [hs, dif_pos h]
    congr 1
  -- transport of suffix sums
  have htr : ∀ m, 1 ≤ m → ∑ a ∈ Icc m k, (s a - c a) =
      ∑ b ∈ univ.filter (fun b : Fin k => m ≤ b.1 + 1), (sf b - c (b.1 + 1)) := by
    intro m hm
    symm
    refine Finset.sum_bij' (fun b _ => b.1 + 1) (fun a ha => ⟨a - 1, by
        simp only [mem_Icc] at ha; omega⟩) ?_ ?_ ?_ ?_ ?_
    · intro b hb
      simp only [mem_filter, mem_univ, true_and] at hb
      simp only [mem_Icc]; omega
    · intro a ha
      simp only [mem_Icc] at ha
      simp only [mem_filter, mem_univ, true_and]; omega
    · intro b _
      ext; simp
    · intro a ha
      simp only [mem_Icc] at ha
      simp only; omega
    · intro b _
      rw [hsv b]
  refine ⟨s, ?_, ?_, ?_, ?_⟩
  · intro a b ha hab hb
    have h1 : 1 ≤ a ∧ a ≤ k := ⟨ha, by omega⟩
    have h2 : 1 ≤ b ∧ b ≤ k := ⟨by omega, hb⟩
    simp only [hs, dif_pos h1, dif_pos h2]
    apply hmono
    show a - 1 ≤ b - 1
    omega
  · intro m hm
    rw [htr m hm]
    by_cases hmk : m ≤ k
    · have := hsuf ⟨m - 1, by omega⟩
      convert this using 2
      ext b; simp only [mem_filter, mem_univ, true_and, Fin.le_def]; omega
    · have : univ.filter (fun b : Fin k => m ≤ b.1 + 1) = ∅ := by
        rw [Finset.filter_eq_empty_iff]
        intro b _; have := b.2; omega
      rw [this, sum_empty]
  · rw [htr 1 le_rfl]
    rw [← htot]
    congr 1
    ext b; simp
  · intro m hm2 hmk hlt
    rw [htr m (by omega)]
    have hm1 : 1 ≤ m - 1 ∧ m - 1 ≤ k := ⟨by omega, by omega⟩
    have hm' : 1 ≤ m ∧ m ≤ k := ⟨by omega, hmk⟩
    simp only [hs, dif_pos hm1, dif_pos hm'] at hlt
    have := hjump ⟨m - 1, by omega⟩ (sf ⟨m - 1, by omega⟩ - sf ⟨m - 1 - 1, by omega⟩)
      (by linarith) (fun a ha => by
        have : sf a ≤ sf ⟨m - 1 - 1, by omega⟩ := by
          apply hmono
          simp only [Fin.lt_def, Fin.le_def, Fin.val_mk] at ha ⊢; omega
        linarith)
    convert this using 2
    ext b; simp only [mem_filter, mem_univ, true_and, Fin.le_def]; omega

end Ba300cc1



namespace Ba300cc1
open PolylogKServer.Allocation Finset

variable {d k : ℕ}

/-- The isotonic-regression facts used by the analysis. -/
def IsoSpec (k : ℕ) (c s : ℕ → ℝ) : Prop :=
  (∀ a b, 1 ≤ a → a ≤ b → b ≤ k → s a ≤ s b) ∧
  (∀ m, 1 ≤ m → 0 ≤ ∑ a ∈ Icc m k, (s a - c a)) ∧
  (∑ a ∈ Icc 1 k, (s a - c a) = 0) ∧
  (∀ m, 2 ≤ m → m ≤ k → s (m - 1) < s m → ∑ a ∈ Icc m k, (s a - c a) = 0)

/-- The target vector of the isotonic step at the requested location. -/
noncomputable def cvec (β η : ℝ) (w : Fin d → ℝ) (yo : Fin d → ℕ → ℝ) (r : Request d k)
    (j : ℕ) : ℝ :=
  Real.log (yo r.loc j + β) - η * lam r j / w r.loc

/-- The new cumulative vector for multiplier `N`: multiplicative update off `i0`, shifted and
clipped isotonic solution at `i0`. -/
noncomputable def yOf (β : ℝ) (w : Fin d → ℝ) (yo : Fin d → ℕ → ℝ) (i0 : Fin d) (s : ℕ → ℝ)
    (N : ℝ) : Fin d → ℕ → ℝ :=
  fun i j => if i = i0 then max 0 (min 1 (Real.exp (s j + N / w i0) - β))
    else min 1 ((yo i j + β) * Real.exp (N / w i) - β)

/-- The prox step data: isotonic `s`, multiplier `N ≥ 0`, quota met, slackness. -/
def ProxOK (β η : ℝ) (w : Fin d → ℝ) (yo : Fin d → ℕ → ℝ) (r : Request d k) (Q : ℝ)
    (s : ℕ → ℝ) (N : ℝ) : Prop :=
  IsoSpec k (cvec β η w yo r) s ∧ 0 ≤ N ∧
  Q ≤ ∑ i, ∑ j ∈ Icc 1 k, yOf β w yo r.loc s N i j ∧
  (0 < N → ∑ i, ∑ j ∈ Icc 1 k, yOf β w yo r.loc s N i j = Q)

lemma yOf_cont (β : ℝ) (w : Fin d → ℝ) (yo : Fin d → ℕ → ℝ) (i0 : Fin d) (s : ℕ → ℝ) :
    Continuous fun N => ∑ i, ∑ j ∈ Icc 1 k, yOf β w yo i0 s N i j := by
  refine continuous_finset_sum _ fun i _ => continuous_finset_sum _ fun j _ => ?_
  by_cases hi : i = i0
  · simp only [yOf, if_pos hi]
    fun_prop
  · simp only [yOf, if_neg hi]
    fun_prop

theorem prox_exists (β η : ℝ) (hβ : 0 < β) (w : Fin d → ℝ) (hw : ∀ i, 0 < w i)
    (yo : Fin d → ℕ → ℝ) (hyo : ∀ i j, 0 ≤ yo i j) (r : Request d k) (Q : ℝ)
    (hQ : Q ≤ (d : ℝ) * k) : ∃ s N, ProxOK β η w yo r Q s N := by
  obtain ⟨s, hs⟩ := iso_exists k (cvec β η w yo r)
  set S : ℝ → ℝ := fun N => ∑ i, ∑ j ∈ Icc 1 k, yOf β w yo r.loc s N i j with hS
  by_cases h0 : Q ≤ S 0
  · exact ⟨s, 0, hs, le_rfl, h0, fun h => absurd h (lt_irrefl 0)⟩
  push_neg at h0
  set W : ℝ := ∑ i, w i with hW
  set A : ℝ := |Real.log ((1 + β) / β)| + |Real.log (1 + β)| + ∑ j ∈ Icc 1 k, |s j| with hA
  have hA0 : 0 ≤ A := add_nonneg (add_nonneg (abs_nonneg _) (abs_nonneg _))
    (sum_nonneg fun j _ => abs_nonneg _)
  set Nb : ℝ := W * A with hNb
  have hwW : ∀ i, w i ≤ W := fun i =>
    single_le_sum (f := w) (fun i _ => (hw i).le) (mem_univ i)
  have hNbw : ∀ i, A ≤ Nb / w i := by
    intro i
    rw [le_div_iff₀ (hw i), hNb]
    nlinarith [hwW i, hw i]
  have hNb0 : 0 ≤ Nb := by
    rcases isEmpty_or_nonempty (Fin d) with hd | ⟨⟨i⟩⟩
    · simp [hNb, hW]
    · have := hNbw i
      have h2 := hw i
      have : 0 ≤ Nb / w i := le_trans hA0 this
      exact (div_nonneg_iff.1 this).elim (fun h => h.1) (fun h => absurd h.2 (not_le.2 h2))
  have hone : ∀ i, ∀ j ∈ Icc 1 k, yOf β w yo r.loc s Nb i j = 1 := by
    intro i j hj
    by_cases hi : i = r.loc
    · simp only [yOf, if_pos hi]
      have h1 : |s j| ≤ ∑ j ∈ Icc 1 k, |s j| :=
        single_le_sum (f := fun j => |s j|) (fun j _ => abs_nonneg _) hj
      have h2 : Real.log (1 + β) ≤ s j + Nb / w r.loc := by
        have := hNbw r.loc
        have := neg_abs_le (s j)
        have := le_abs_self (Real.log (1 + β))
        have := abs_nonneg (Real.log ((1 + β) / β))
        linarith
      have h3 : 1 + β ≤ Real.exp (s j + Nb / w r.loc) := by
        calc 1 + β = Real.exp (Real.log (1 + β)) := (Real.exp_log (by linarith)).symm
          _ ≤ _ := Real.exp_le_exp.2 h2
      rw [min_eq_left (by linarith), max_eq_right zero_le_one]
    · simp only [yOf, if_neg hi]
      have h2 : Real.log ((1 + β) / β) ≤ Nb / w i := by
        have := hNbw i
        have := le_abs_self (Real.log ((1 + β) / β))
        have : 0 ≤ ∑ j ∈ Icc 1 k, |s j| := sum_nonneg fun j _ => abs_nonneg _
        linarith [abs_nonneg (Real.log (1 + β))]
      have h3 : (1 + β) / β ≤ Real.exp (Nb / w i) := by
        calc (1 + β) / β = Real.exp (Real.log ((1 + β) / β)) :=
              (Real.exp_log (div_pos (by linarith) hβ)).symm
          _ ≤ _ := Real.exp_le_exp.2 h2
      have h4 : β * ((1 + β) / β) ≤ (yo i j + β) * Real.exp (Nb / w i) :=
        mul_le_mul (by linarith [hyo i j]) h3 (div_pos (by linarith) hβ).le (by linarith [hyo i j])
      have h5 : β * ((1 + β) / β) = 1 + β := by field_simp
      rw [min_eq_left (by linarith)]
  have hSNb : S Nb = (d : ℝ) * k := by
    simp only [hS]
    rw [sum_congr rfl fun i _ => sum_congr rfl fun j hj => hone i j hj]
    simp
  obtain ⟨N, hN, hSN⟩ := intermediate_value_Icc hNb0 (yOf_cont β w yo r.loc s).continuousOn
    ⟨h0.le, hQ.trans_eq hSNb.symm⟩
  exact ⟨s, N, hs, hN.1, by simp only [hS] at hSN; rw [hSN], fun _ => by simpa [hS] using hSN⟩

end Ba300cc1



namespace Ba300cc1
open PolylogKServer.Allocation Finset

variable {d k : ℕ}

lemma tele_Icc (k : ℕ) (f : ℕ → ℝ) : ∑ m ∈ Icc 1 k, (f m - f (m - 1)) = f k - f 0 := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [sum_Icc_succ_top (by omega), ih, Nat.add_sub_cancel]
    ring

/-- Summation by parts on `Icc 1 k` with suffix sums. -/
lemma abel_Icc (k : ℕ) (r f : ℕ → ℝ) :
    ∑ a ∈ Icc 1 k, r a * f a = f 0 * ∑ a ∈ Icc 1 k, r a +
      ∑ m ∈ Icc 1 k, (∑ a ∈ Icc m k, r a) * (f m - f (m - 1)) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have h1 : ∀ m ∈ Icc 1 k, (∑ a ∈ Icc m (k + 1), r a) * (f m - f (m - 1)) =
        (∑ a ∈ Icc m k, r a) * (f m - f (m - 1)) + r (k + 1) * (f m - f (m - 1)) := by
      intro m hm
      rw [mem_Icc] at hm
      rw [sum_Icc_succ_top (by omega)]
      ring
    simp only [sum_Icc_succ_top (show 1 ≤ k + 1 by omega)]
    rw [ih, sum_congr rfl h1, sum_add_distrib, ← mul_sum, tele_Icc k f]
    simp only [Icc_self, sum_singleton, Nat.add_sub_cancel]
    ring

/-- Abel: residual against a monotone vector is nonnegative. -/
lemma iso_abel_nonneg {c s : ℕ → ℝ} (hs : IsoSpec k c s) (f : ℕ → ℝ)
    (hf : ∀ m, 2 ≤ m → m ≤ k → f (m - 1) ≤ f m) :
    0 ≤ ∑ a ∈ Icc 1 k, (s a - c a) * f a := by
  obtain ⟨_, hR, hR1, _⟩ := hs
  rw [abel_Icc, hR1, mul_zero, zero_add]
  apply sum_nonneg
  intro m hm
  rw [mem_Icc] at hm
  rcases Nat.lt_or_ge m 2 with h | h
  · have : m = 1 := by omega
    subst this
    rw [hR1, zero_mul]
  · exact mul_nonneg (hR m hm.1) (by linarith [hf m h hm.2])

/-- Abel: residual against a vector that can only drop where `s` is flat is nonpositive. -/
lemma iso_abel_nonpos {c s : ℕ → ℝ} (hs : IsoSpec k c s) (f : ℕ → ℝ)
    (hf : ∀ m, 2 ≤ m → m ≤ k → s (m - 1) = s m → f m ≤ f (m - 1)) :
    ∑ a ∈ Icc 1 k, (s a - c a) * f a ≤ 0 := by
  obtain ⟨hmono, hR, hR1, hjump⟩ := hs
  rw [abel_Icc, hR1, mul_zero, zero_add]
  apply sum_nonpos
  intro m hm
  rw [mem_Icc] at hm
  rcases Nat.lt_or_ge m 2 with h | h
  · have : m = 1 := by omega
    subst this
    rw [hR1, zero_mul]
  · have hle : s (m - 1) ≤ s m := hmono (m - 1) m (by omega) (by omega) hm.2
    rcases lt_or_eq_of_le hle with hlt | heq
    · rw [hjump m h hm.2 hlt, zero_mul]
    · exact mul_nonpos_of_nonneg_of_nonpos (hR m hm.1) (by linarith [hf m h hm.2 heq])

lemma iso_abel_zero {c s : ℕ → ℝ} (hs : IsoSpec k c s) (f : ℕ → ℝ)
    (hf : ∀ m, 2 ≤ m → m ≤ k → s (m - 1) = s m → f m = f (m - 1)) :
    ∑ a ∈ Icc 1 k, (s a - c a) * f a = 0 := by
  have h1 := iso_abel_nonpos hs f (fun m h1 h2 h3 => (hf m h1 h2 h3).le)
  have h2 := iso_abel_nonpos hs (fun a => -f a) (fun m h1 h2 h3 => by
    simp only [neg_le_neg_iff]; exact (hf m h1 h2 h3).ge)
  simp only [mul_neg, sum_neg_distrib] at h2
  linarith

/-- The clipped value at `i0`. -/
lemma clip_cases (β σ : ℝ) (hβ : 0 < β) :
    let u := max 0 (min 1 (Real.exp σ - β))
    0 ≤ u ∧ u ≤ 1 ∧
    ((Real.exp σ - β < 0 ∧ u = 0 ∧ σ < Real.log β) ∨
     (0 ≤ Real.exp σ - β ∧ Real.exp σ - β ≤ 1 ∧ u = Real.exp σ - β ∧ Real.log (u + β) = σ) ∨
     (1 < Real.exp σ - β ∧ u = 1 ∧ Real.log (1 + β) < σ)) := by
  intro u
  refine ⟨le_max_left _ _, max_le zero_le_one (min_le_left _ _), ?_⟩
  rcases lt_or_ge (Real.exp σ - β) 0 with h | h
  · left
    refine ⟨h, ?_, ?_⟩
    · simp only [u]; rw [min_eq_right (by linarith), max_eq_left h.le]
    · have : Real.exp σ < β := by linarith
      calc σ = Real.log (Real.exp σ) := (Real.log_exp σ).symm
        _ < Real.log β := Real.log_lt_log (Real.exp_pos σ) this
  · rcases le_or_gt (Real.exp σ - β) 1 with h1 | h1
    · right; left
      have hu : u = Real.exp σ - β := by simp only [u]; rw [min_eq_right h1, max_eq_right h]
      refine ⟨h, h1, hu, ?_⟩
      rw [hu, sub_add_cancel, Real.log_exp]
    · right; right
      refine ⟨h1, ?_, ?_⟩
      · simp only [u]; rw [min_eq_left h1.le, max_eq_right zero_le_one]
      · have : 1 + β < Real.exp σ := by linarith
        calc Real.log (1 + β) < Real.log (Real.exp σ) := Real.log_lt_log (by linarith) this
          _ = σ := Real.log_exp σ

/-- **Variational inequality** of the prox step. -/
theorem prox_VI (β η : ℝ) (hβ : 0 < β) (w : Fin d → ℝ) (hw : ∀ i, 0 < w i)
    (yo : Fin d → ℕ → ℝ) (hyo : ∀ i j, 0 ≤ yo i j) (r : Request d k) (Q : ℝ) (s : ℕ → ℝ)
    (N : ℝ) (hP : ProxOK β η w yo r Q s N) (z : Fin d → ℕ → ℝ)
    (hz0 : ∀ i j, 0 ≤ z i j) (hz1 : ∀ i j, z i j ≤ 1)
    (hzm : ∀ i a b, 1 ≤ a → a ≤ b → b ≤ k → z i a ≤ z i b)
    (hzQ : Q ≤ ∑ i, ∑ j ∈ Icc 1 k, z i j) :
    0 ≤ ∑ i, ∑ j ∈ Icc 1 k,
      (w i * (Real.log (yOf β w yo r.loc s N i j + β) - Real.log (yo i j + β)) +
        (if i = r.loc then η * lam r j else 0)) * (z i j - yOf β w yo r.loc s N i j) := by
  obtain ⟨hs, hN0, hQ, hslack⟩ := hP
  set y := yOf β w yo r.loc s N with hy
  set G : Fin d → ℕ → ℝ := fun i j =>
    w i * (Real.log (y i j + β) - Real.log (yo i j + β)) +
      (if i = r.loc then η * lam r j else 0) with hG
  have hsplit : ∑ i, ∑ j ∈ Icc 1 k, G i j * (z i j - y i j) =
      ∑ i, ∑ j ∈ Icc 1 k, (G i j - N) * (z i j - y i j) +
        N * (∑ i, ∑ j ∈ Icc 1 k, z i j - ∑ i, ∑ j ∈ Icc 1 k, y i j) := by
    rw [mul_sub, mul_sum, mul_sum, ← sum_sub_distrib, ← sum_add_distrib]
    refine sum_congr rfl fun i _ => ?_
    rw [mul_sum, mul_sum, ← sum_sub_distrib, ← sum_add_distrib]
    exact sum_congr rfl fun j _ => by ring
  have hNterm : 0 ≤ N * (∑ i, ∑ j ∈ Icc 1 k, z i j - ∑ i, ∑ j ∈ Icc 1 k, y i j) := by
    rcases eq_or_lt_of_le hN0 with h | h
    · rw [← h, zero_mul]
    · rw [hslack h]; exact mul_nonneg hN0 (by linarith)
  have hmain : 0 ≤ ∑ i, ∑ j ∈ Icc 1 k, (G i j - N) * (z i j - y i j) := by
    apply sum_nonneg
    intro i _
    by_cases hi : i = r.loc
    · -- the requested location
      subst hi
      have hrep : ∀ j ∈ Icc 1 k, (G r.loc j - N) * (z r.loc j - y r.loc j) =
          w r.loc * ((Real.log (y r.loc j + β) - (s j + N / w r.loc)) * (z r.loc j - y r.loc j)) +
          w r.loc * ((s j - cvec β η w yo r j) * (z r.loc j - y r.loc j)) := by
        intro j _
        simp only [hG, cvec, ↓reduceIte]
        have h1 : w r.loc * (N / w r.loc) = N := mul_div_cancel₀ _ (hw r.loc).ne'
        have h2 : w r.loc * (η * lam r j / w r.loc) = η * lam r j := mul_div_cancel₀ _ (hw r.loc).ne'
        linear_combination (z r.loc j - y r.loc j) * h1 - (z r.loc j - y r.loc j) * h2
      rw [sum_congr rfl hrep, sum_add_distrib, ← mul_sum, ← mul_sum]
      have hA : 0 ≤ ∑ j ∈ Icc 1 k,
          (Real.log (y r.loc j + β) - (s j + N / w r.loc)) * (z r.loc j - y r.loc j) := by
        apply sum_nonneg
        intro j _
        have hyj : y r.loc j = max 0 (min 1 (Real.exp (s j + N / w r.loc) - β)) := by
          simp [hy, yOf]
        obtain ⟨_, _, hc⟩ := clip_cases β (s j + N / w r.loc) hβ
        rw [hyj]
        rcases hc with ⟨_, hu, hσ⟩ | ⟨_, _, _, hlog⟩ | ⟨_, hu, hσ⟩
        · rw [hu, zero_add]
          exact mul_nonneg (by linarith) (by linarith [hz0 r.loc j])
        · rw [hlog, sub_self, zero_mul]
        · rw [hu]
          exact mul_nonneg_of_nonpos_of_nonpos (by linarith) (by linarith [hz1 r.loc j])
      have hB : 0 ≤ ∑ j ∈ Icc 1 k, (s j - cvec β η w yo r j) * (z r.loc j - y r.loc j) := by
        have h1 := iso_abel_nonneg hs (z r.loc) (fun m h1 h2 => hzm r.loc (m - 1) m (by omega)
          (by omega) h2)
        have h2 := iso_abel_zero hs (y r.loc) (fun m _ _ heq => by
          simp [hy, yOf, heq])
        rw [show ∑ j ∈ Icc 1 k, (s j - cvec β η w yo r j) * (z r.loc j - y r.loc j) =
          ∑ j ∈ Icc 1 k, (s j - cvec β η w yo r j) * z r.loc j -
            ∑ j ∈ Icc 1 k, (s j - cvec β η w yo r j) * y r.loc j by
          rw [← sum_sub_distrib]; exact sum_congr rfl fun j _ => by ring]
        linarith
      have := (hw r.loc).le
      exact add_nonneg (mul_nonneg this hA) (mul_nonneg this hB)
    · apply sum_nonneg
      intro j _
      have hyj : y i j = min 1 ((yo i j + β) * Real.exp (N / w i) - β) := by
        simp [hy, yOf, hi]
      have hGj : G i j = w i * (Real.log (y i j + β) - Real.log (yo i j + β)) := by
        simp [hG, hi]
      have hyoβ : 0 < yo i j + β := by linarith [hyo i j]
      have hlogE : Real.log ((yo i j + β) * Real.exp (N / w i)) =
          Real.log (yo i j + β) + N / w i := by
        rw [Real.log_mul hyoβ.ne' (Real.exp_pos _).ne', Real.log_exp]
      rcases le_or_gt ((yo i j + β) * Real.exp (N / w i) - β) 1 with h | h
      · have hy' : y i j = (yo i j + β) * Real.exp (N / w i) - β := by rw [hyj, min_eq_right h]
        have : G i j = N := by
          rw [hGj, hy', sub_add_cancel, hlogE]
          have := (hw i).ne'
          field_simp
          ring
        rw [this, sub_self, zero_mul]
      · have hy' : y i j = 1 := by rw [hyj, min_eq_left h.le]
        have hlt : Real.log (1 + β) < Real.log (yo i j + β) + N / w i := by
          rw [← hlogE]
          exact Real.log_lt_log (by linarith) (by linarith)
        have : G i j ≤ N := by
          rw [hGj, hy']
          have h2 : w i * (Real.log (1 + β) - Real.log (yo i j + β)) ≤ w i * (N / w i) :=
            mul_le_mul_of_nonneg_left (by linarith) (hw i).le
          rwa [mul_div_cancel₀ _ (hw i).ne'] at h2
        rw [hy']
        exact mul_nonneg_of_nonpos_of_nonpos (by linarith) (by linarith [hz1 i j])
  rw [hsplit]
  linarith

end Ba300cc1



namespace Ba300cc1
open PolylogKServer.Allocation Finset

variable {d k : ℕ}

/-- OPT's cumulative vector `z i j = 1[n i < j]`. -/
def zOf (n : Fin d → ℕ) : Fin d → ℕ → ℝ := fun i j => if n i < j then 1 else 0

/-- The hit potential `Ψh(z, y) = ∑ w [(z + β) log((1+β)/(y+β)) + y]`. -/
noncomputable def Psih (β : ℝ) (w : Fin d → ℝ) (z y : Fin d → ℕ → ℝ) : ℝ :=
  ∑ i, ∑ j ∈ Icc 1 k, w i * ((z i j + β) * Lg β (y i j) + y i j)

lemma yOf_nonneg (β : ℝ) (hβ : 0 < β) (w : Fin d → ℝ) (hw : ∀ i, 0 < w i)
    (yo : Fin d → ℕ → ℝ) (hyo : ∀ i j, 0 ≤ yo i j) (i0 : Fin d) (s : ℕ → ℝ) (N : ℝ)
    (hN : 0 ≤ N) (i : Fin d) (j : ℕ) : 0 ≤ yOf β w yo i0 s N i j := by
  unfold yOf
  split_ifs
  · exact le_max_left _ _
  · have h1 : 1 ≤ Real.exp (N / w i) := Real.one_le_exp (div_nonneg hN (hw i).le)
    have h2 : β ≤ (yo i j + β) * Real.exp (N / w i) := by nlinarith [hyo i j]
    exact le_min zero_le_one (by linarith)

lemma yOf_le_one (β : ℝ) (w : Fin d → ℝ) (yo : Fin d → ℕ → ℝ) (i0 : Fin d) (s : ℕ → ℝ)
    (N : ℝ) (i : Fin d) (j : ℕ) : yOf β w yo i0 s N i j ≤ 1 := by
  unfold yOf
  split_ifs
  · exact max_le zero_le_one (min_le_left _ _)
  · exact min_le_left _ _

lemma Lg_sub (β a b : ℝ) (hβ : 0 < β) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Lg β b - Lg β a = Real.log (a + β) - Real.log (b + β) := by
  unfold Lg
  rw [Real.log_div (by linarith) (by linarith), Real.log_div (by linarith) (by linarith)]
  ring

/-- Bregman nonnegativity for one coordinate. -/
lemma breg_coord (a b : ℝ) (ha : 0 < a) (hb : 0 < b) : a - b ≤ a * (Real.log a - Real.log b) := by
  have h := Real.one_sub_inv_le_log_of_pos (div_pos ha hb)
  rw [Real.log_div ha.ne' hb.ne', inv_div] at h
  have h2 : a * (1 - b / a) = a - b := by field_simp
  have h3 : a * (1 - b / a) ≤ a * (Real.log a - Real.log b) := mul_le_mul_of_nonneg_left h ha.le
  linarith

/-- **Per-step hit inequality** (three-point form of the prox step). -/
theorem hit_step (β η : ℝ) (hβ : 0 < β) (w : Fin d → ℝ) (hw : ∀ i, 0 < w i)
    (yo : Fin d → ℕ → ℝ) (hyo : ∀ i j, 0 ≤ yo i j) (r : Request d k) (Q : ℝ) (s : ℕ → ℝ)
    (N : ℝ) (hP : ProxOK β η w yo r Q s N) (z : Fin d → ℕ → ℝ)
    (hz0 : ∀ i j, 0 ≤ z i j) (hz1 : ∀ i j, z i j ≤ 1)
    (hzm : ∀ i a b, 1 ≤ a → a ≤ b → b ≤ k → z i a ≤ z i b)
    (hzQ : Q ≤ ∑ i, ∑ j ∈ Icc 1 k, z i j) :
    η * ∑ j ∈ Icc 1 k, lam r j * yOf β w yo r.loc s N r.loc j +
        Psih (k := k) β w z (yOf β w yo r.loc s N) ≤
      η * ∑ j ∈ Icc 1 k, lam r j * z r.loc j + Psih (k := k) β w z yo := by
  have hVI := prox_VI β η hβ w hw yo hyo r Q s N hP z hz0 hz1 hzm hzQ
  set y := yOf β w yo r.loc s N with hy
  have hy0 : ∀ i j, 0 ≤ y i j := yOf_nonneg β hβ w hw yo hyo r.loc s N hP.2.1
  set g : Fin d → ℕ → ℝ := fun i j => w i * (Real.log (y i j + β) - Real.log (yo i j + β))
    with hg
  -- split the VI
  have hsplit : ∑ i, ∑ j ∈ Icc 1 k,
      (w i * (Real.log (y i j + β) - Real.log (yo i j + β)) +
        (if i = r.loc then η * lam r j else 0)) * (z i j - y i j) =
      ∑ i, ∑ j ∈ Icc 1 k, g i j * (z i j - y i j) +
        η * (∑ j ∈ Icc 1 k, lam r j * z r.loc j - ∑ j ∈ Icc 1 k, lam r j * y r.loc j) := by
    have h1 : ∀ i, ∑ j ∈ Icc 1 k, (w i * (Real.log (y i j + β) - Real.log (yo i j + β)) +
        (if i = r.loc then η * lam r j else 0)) * (z i j - y i j) =
        ∑ j ∈ Icc 1 k, g i j * (z i j - y i j) +
          (if i = r.loc then η * (∑ j ∈ Icc 1 k, lam r j * z i j -
            ∑ j ∈ Icc 1 k, lam r j * y i j) else 0) := by
      intro i
      split_ifs with hi
      · rw [mul_sub, mul_sum, mul_sum, ← sum_sub_distrib, ← sum_add_distrib]
        exact sum_congr rfl fun j _ => by simp only [hg]; ring
      · rw [add_zero]
        exact sum_congr rfl fun j _ => by simp only [hg, add_zero]
    rw [sum_congr rfl fun i _ => h1 i, sum_add_distrib, sum_ite_eq' univ r.loc, if_pos (mem_univ _)]
  rw [hsplit] at hVI
  -- potential difference
  have hdiff : Psih (k := k) β w z yo - Psih (k := k) β w z y =
      ∑ i, ∑ j ∈ Icc 1 k, ((z i j + β) * g i j - w i * (y i j - yo i j)) := by
    unfold Psih
    rw [← sum_sub_distrib]
    refine sum_congr rfl fun i _ => ?_
    rw [← sum_sub_distrib]
    refine sum_congr rfl fun j _ => ?_
    have := Lg_sub β (y i j) (yo i j) hβ (hy0 i j) (hyo i j)
    simp only [hg]
    have h2 : w i * ((z i j + β) * Lg β (yo i j) + yo i j) -
        w i * ((z i j + β) * Lg β (y i j) + y i j) =
        w i * ((z i j + β) * (Lg β (yo i j) - Lg β (y i j))) - w i * (y i j - yo i j) := by ring
    rw [h2, this]
    ring
  have hbreg : 0 ≤ ∑ i, ∑ j ∈ Icc 1 k, ((y i j + β) * g i j - w i * (y i j - yo i j)) := by
    apply sum_nonneg; intro i _; apply sum_nonneg; intro j _
    have h := breg_coord (y i j + β) (yo i j + β) (by linarith [hy0 i j]) (by linarith [hyo i j])
    simp only [hg]
    have h2 := mul_le_mul_of_nonneg_left h (hw i).le
    nlinarith
  have hcomb : ∑ i, ∑ j ∈ Icc 1 k, ((z i j + β) * g i j - w i * (y i j - yo i j)) -
      ∑ i, ∑ j ∈ Icc 1 k, ((y i j + β) * g i j - w i * (y i j - yo i j)) =
      ∑ i, ∑ j ∈ Icc 1 k, g i j * (z i j - y i j) := by
    rw [← sum_sub_distrib]
    refine sum_congr rfl fun i _ => ?_
    rw [← sum_sub_distrib]
    exact sum_congr rfl fun j _ => by ring
  linarith

/-- An offline move changes `Ψh` by at most `log((1+β)/β) · ∑ w |n' - n|`. -/
lemma Psih_move (β : ℝ) (hβ : 0 < β) (w : Fin d → ℝ) (hw : ∀ i, 0 < w i)
    (y : Fin d → ℕ → ℝ) (hy0 : ∀ i j, 0 ≤ y i j) (hy1 : ∀ i j, y i j ≤ 1)
    (n n' : Fin d → ℕ) (hn : ∀ i, n i ≤ k) (hn' : ∀ i, n' i ≤ k) :
    Psih (k := k) β w (zOf n') y - Psih (k := k) β w (zOf n) y ≤
      Real.log ((1 + β) / β) * ∑ i, w i * |((n' i : ℕ) : ℝ) - ((n i : ℕ) : ℝ)| := by
  unfold Psih
  rw [← sum_sub_distrib, mul_sum]
  refine sum_le_sum fun i _ => ?_
  rw [abs_sub_eq_sum_ind (n' i) (n i) k (hn' i) (hn i), mul_sum, mul_sum, ← sum_sub_distrib]
  refine sum_le_sum fun j _ => ?_
  have hL0 := Lg_nonneg hβ (hy0 i j) (hy1 i j)
  have hL1 := Lg_le hβ (hy0 i j) (β := β)
  have hw0 := (hw i).le
  simp only [zOf]
  have key : ((if n' i < j then (1 : ℝ) else 0) - (if n i < j then 1 else 0)) * Lg β (y i j) ≤
      Real.log ((1 + β) / β) * |(if n' i < j then (1 : ℝ) else 0) - (if n i < j then 1 else 0)| := by
    split_ifs <;> simp <;> nlinarith
  have h2 : w i * (((if n' i < j then (1 : ℝ) else 0) + β) * Lg β (y i j) + y i j) -
      w i * (((if n i < j then (1 : ℝ) else 0) + β) * Lg β (y i j) + y i j) =
      w i * (((if n' i < j then (1 : ℝ) else 0) - (if n i < j then 1 else 0)) * Lg β (y i j)) := by
    ring
  rw [h2]
  calc w i * (((if n' i < j then (1 : ℝ) else 0) - (if n i < j then 1 else 0)) * Lg β (y i j))
      ≤ w i * (Real.log ((1 + β) / β) *
          |(if n' i < j then (1 : ℝ) else 0) - (if n i < j then 1 else 0)|) :=
        mul_le_mul_of_nonneg_left key hw0
    _ = _ := by ring

lemma Psih_bounds (β : ℝ) (hβ : 0 < β) (w : Fin d → ℝ) (hw : ∀ i, 0 < w i)
    (z y : Fin d → ℕ → ℝ) (hz0 : ∀ i j, 0 ≤ z i j) (hz1 : ∀ i j, z i j ≤ 1)
    (hy0 : ∀ i j, 0 ≤ y i j) (hy1 : ∀ i j, y i j ≤ 1) :
    0 ≤ Psih (k := k) β w z y ∧
      Psih (k := k) β w z y ≤ ∑ i, ∑ j ∈ Icc 1 k, w i * ((1 + β) * Real.log ((1 + β) / β) + 1) := by
  constructor
  · apply sum_nonneg; intro i _; apply sum_nonneg; intro j _
    have := Lg_nonneg hβ (hy0 i j) (hy1 i j)
    have := hz0 i j
    have := hy0 i j
    exact mul_nonneg (hw i).le (by positivity)
  · apply sum_le_sum; intro i _; apply sum_le_sum; intro j _
    have h0 := Lg_nonneg hβ (hy0 i j) (hy1 i j)
    have h1 := Lg_le hβ (hy0 i j) (β := β)
    have h2 := hz1 i j
    have h3 := hz0 i j
    have h4 := hy1 i j
    apply mul_le_mul_of_nonneg_left _ (hw i).le
    have : (z i j + β) * Lg β (y i j) ≤ (1 + β) * Real.log ((1 + β) / β) :=
      mul_le_mul (by linarith) h1 h0 (by linarith)
    linarith

end Ba300cc1



namespace Ba300cc1
open PolylogKServer.Allocation Finset

variable {d k : ℕ}

/-- Off the requested location: increase cost against the Φm drop, per coordinate. -/
lemma coord_off (w β N yo ζ y t g : ℝ) (hw : 0 < w) (hβ : 0 < β) (hβ1 : β ≤ 1)
    (hyo0 : 0 ≤ yo) (hyo1 : yo ≤ 1) (hN : 0 ≤ N) (hζ : ζ = 0 ∨ ζ = 1)
    (hy : y = min 1 ((yo + β) * Real.exp (N / w) - β))
    (ht : t = if 1 < (yo + β) * Real.exp (N / w) - β then 1 else 0)
    (hg : g = w * (Real.log (y + β) - Real.log (yo + β))) :
    w * max 0 (y - yo) - 2 * ζ * g ≤
      N * ((1 - t) * (y + β) * (if 0 < y then 1 else 0) - 2 * (1 - t) * ζ +
        (1 + β) * t * (1 - ζ)) := by
  have hyoβ : 0 < yo + β := by linarith
  have hlogE : Real.log ((yo + β) * Real.exp (N / w)) = Real.log (yo + β) + N / w := by
    rw [Real.log_mul hyoβ.ne' (Real.exp_pos _).ne', Real.log_exp]
  have hwN : w * (N / w) = N := mul_div_cancel₀ _ hw.ne'
  have hE1 : 1 ≤ Real.exp (N / w) := Real.one_le_exp (div_nonneg hN hw.le)
  have hEyo : yo + β ≤ (yo + β) * Real.exp (N / w) := by nlinarith
  by_cases h : 1 < (yo + β) * Real.exp (N / w) - β
  · have ht1 : t = 1 := by rw [ht, if_pos h]
    have hy1 : y = 1 := by rw [hy, min_eq_left h.le]
    subst ht1 hy1
    have hg0 : 0 ≤ g := by
      rw [hg]
      exact mul_nonneg hw.le (by linarith [Real.log_le_log hyoβ (show yo + β ≤ 1 + β by linarith)])
    have hgN : g ≤ N := by
      have hlt : Real.log (1 + β) < Real.log (yo + β) + N / w := by
        rw [← hlogE]; exact Real.log_lt_log (by linarith) (by linarith)
      rw [hg, ← hwN]
      exact mul_le_mul_of_nonneg_left (by linarith) hw.le
    have hI : w * (1 - yo) ≤ (1 + β) * g := by
      have hb := breg_coord (1 + β) (yo + β) (by linarith) hyoβ
      rw [hg]
      nlinarith
    rw [max_eq_right (by linarith)]
    rcases hζ with h0 | h1 <;> subst_vars <;> nlinarith
  · have ht0 : t = 0 := by rw [ht, if_neg h]
    push_neg at h
    have hyE : y = (yo + β) * Real.exp (N / w) - β := by rw [hy, min_eq_right h]
    have hgN : g = N := by
      rw [hg, hyE, sub_add_cancel, hlogE]
      linarith
    have hyyo : yo ≤ y := by linarith
    have hI : w * (y - yo) ≤ (y + β) * g := by
      have hb := breg_coord (y + β) (yo + β) (by linarith) hyoβ
      rw [hg]
      nlinarith
    subst ht0
    rw [max_eq_right (by linarith)]
    by_cases hy0 : 0 < y
    · rw [if_pos hy0]
      rw [hgN] at hI ⊢
      rcases hζ with h0 | h1 <;> subst_vars <;> nlinarith
    · rw [if_neg hy0]
      have : y = 0 := by linarith
      have : yo = 0 := by linarith
      rw [hgN]
      rcases hζ with h0 | h1 <;> subst_vars <;> nlinarith

/-- At the requested location, per coordinate (residual `q = w (s - c)` kept separate). -/
lemma coord_i0 (w β η lam N yo ζ s c u t g φ q : ℝ) (hw : 0 < w) (hβ : 0 < β) (hβ1 : β ≤ 1)
    (hη : 0 ≤ η) (hyo0 : 0 ≤ yo) (hyo1 : yo ≤ 1) (hlam : 0 ≤ lam) (hN : 0 ≤ N)
    (hζ : ζ = 0 ∨ ζ = 1)
    (hc : c = Real.log (yo + β) - η * lam / w)
    (hu : u = max 0 (min 1 (Real.exp (s + N / w) - β)))
    (ht : t = if 1 < Real.exp (s + N / w) - β then 1 else 0)
    (hg : g = w * (Real.log (u + β) - Real.log (yo + β)))
    (hφ : φ = (u + β) * (if yo < u then 1 else 0))
    (hq : q = w * (s - c)) :
    w * max 0 (u - yo) - 2 * ζ * g ≤
      N * ((1 - t) * (u + β) * (if 0 < u then 1 else 0) - 2 * (1 - t) * ζ +
        (1 + β) * t * (1 - ζ)) + 2 * η * lam * ζ +
      ((1 - t) * φ - 2 * (1 - t) * ζ + (1 + β) * t * (1 - ζ)) * q := by
  have hyoβ : 0 < yo + β := by linarith
  have hq' : q = w * (s + N / w) - N - w * Real.log (yo + β) + η * lam := by
    rw [hq, hc]
    have h1 : w * (N / w) = N := mul_div_cancel₀ _ hw.ne'
    have h2 : w * (η * lam / w) = η * lam := mul_div_cancel₀ _ hw.ne'
    linear_combination (-1 : ℝ) * h1 + h2
  have hel : 0 ≤ η * lam := mul_nonneg hη hlam
  obtain ⟨hu0, hu1, hcase⟩ := clip_cases β (s + N / w) hβ
  rw [← hu] at hu0 hu1 hcase
  rcases hcase with ⟨hneg, hu', hσ⟩ | ⟨hpos, hle, hu', hlog⟩ | ⟨hgt, hu', hσ⟩
  · -- clipped at 0
    have ht0 : t = 0 := by rw [ht, if_neg (by linarith)]
    have hφ0 : φ = 0 := by rw [hφ, hu', if_neg (by linarith)]; ring
    have hg' : g = w * (Real.log β - Real.log (yo + β)) := by rw [hg, hu', zero_add]
    have hkey : w * (s + N / w) ≤ w * Real.log β := mul_le_mul_of_nonneg_left hσ.le hw.le
    rw [ht0, hφ0, hu', max_eq_left (by linarith), if_neg (lt_irrefl 0)]
    rcases hζ with h0 | h1 <;> subst_vars <;> nlinarith
  · -- interior
    have ht0 : t = 0 := by rw [ht, if_neg (by linarith)]
    have hgq : g = q + N - η * lam := by
      rw [hg, hlog, hq']; ring
    rw [ht0]
    by_cases hlt : yo < u
    · have hφ' : φ = u + β := by rw [hφ, if_pos hlt]; ring
      have hb0 : 0 < u := by linarith
      rw [hφ', if_pos hb0, max_eq_right (by linarith)]
      have hI : w * (u - yo) ≤ (u + β) * g := by
        have hb := breg_coord (u + β) (yo + β) (by linarith) hyoβ
        rw [hg]; nlinarith
      have h3 : 0 ≤ (u + β) * (η * lam) := mul_nonneg (by linarith) hel
      rcases hζ with h0 | h1 <;> subst_vars <;> nlinarith
    · have hφ0 : φ = 0 := by rw [hφ, if_neg hlt]; ring
      rw [hφ0, max_eq_left (by linarith)]
      have h4 : 0 ≤ N * ((u + β) * (if 0 < u then 1 else 0)) := by
        apply mul_nonneg hN; split_ifs <;> nlinarith
      rcases hζ with h0 | h1 <;> subst_vars <;> nlinarith
  · -- clipped at 1
    have ht1 : t = 1 := by rw [ht, if_pos hgt]
    have hg' : g = w * (Real.log (1 + β) - Real.log (yo + β)) := by rw [hg, hu']
    have hg0 : 0 ≤ g := by
      rw [hg']
      exact mul_nonneg hw.le (by linarith [Real.log_le_log hyoβ (show yo + β ≤ 1 + β by linarith)])
    have hgq : g ≤ q + N := by
      have : w * Real.log (1 + β) ≤ w * (s + N / w) := mul_le_mul_of_nonneg_left hσ.le hw.le
      rw [hg', hq']; linarith
    have hI : w * (1 - yo) ≤ (1 + β) * g := by
      have hb := breg_coord (1 + β) (yo + β) (by linarith) hyoβ
      have := mul_le_mul_of_nonneg_left hb hw.le
      rw [hg']; linarith
    rw [ht1, hu', max_eq_right (by linarith)]
    have h5 := mul_le_mul_of_nonneg_left hgq (by linarith : (0 : ℝ) ≤ 1 + β)
    have h6 := mul_le_mul_of_nonneg_right hβ1 hg0
    rcases hζ with h0 | h1
    · rw [h0]; linarith
    · rw [h1]; linarith

/-- Claim 15 counting: the bracket multiplying `N` is nonpositive. -/
lemma bracket_le (β : ℝ) (hβ : 0 < β) (hβk : β * (k + 1) ≤ 1) (T Y Z : Fin d → ℕ → ℝ)
    (hT : ∀ i j, T i j = 0 ∨ T i j = 1) (hZ : ∀ i j, Z i j = 0 ∨ Z i j = 1)
    (hY0 : ∀ i j, 0 ≤ Y i j) (hTY : ∀ i j, T i j = 1 → Y i j = 1)
    (hYZ : ∑ i, ∑ j ∈ Icc 1 k, Y i j ≤ ∑ i, ∑ j ∈ Icc 1 k, Z i j)
    (hZc : ∑ i, ∑ j ∈ Icc 1 k, (1 - Z i j) ≤ k) :
    ∑ i, ∑ j ∈ Icc 1 k, ((1 - T i j) * (Y i j + β) * (if 0 < Y i j then 1 else 0) -
      2 * (1 - T i j) * Z i j + (1 + β) * T i j * (1 - Z i j)) ≤ 0 := by
  have hβ1 : β ≤ 1 := by nlinarith
  set F : Fin d → ℕ → ℝ := fun i j => (1 - T i j) * (Y i j + β) * (if 0 < Y i j then 1 else 0) -
      2 * (1 - T i j) * Z i j + (1 + β) * T i j * (1 - Z i j) with hF
  show ∑ i, ∑ j ∈ Icc 1 k, F i j ≤ 0
  have hmaster : ∀ i j, F i j ≤ (Y i j - Z i j) - (1 - β) * ((1 - T i j) * Z i j) +
      β * (1 - Z i j) := by
    intro i j
    simp only [hF]
    rcases hT i j with h1 | h1 <;> rcases hZ i j with h2 | h2
    · rw [h1, h2]
      split_ifs <;> nlinarith [hY0 i j]
    · rw [h1, h2]
      split_ifs <;> nlinarith [hY0 i j]
    · rw [h1, h2, hTY i j h1]; simp <;> nlinarith
    · rw [h1, h2, hTY i j h1]; simp
  have hsum : ∑ i, ∑ j ∈ Icc 1 k, F i j ≤
      (∑ i, ∑ j ∈ Icc 1 k, Y i j - ∑ i, ∑ j ∈ Icc 1 k, Z i j) -
        (1 - β) * ∑ i, ∑ j ∈ Icc 1 k, (1 - T i j) * Z i j +
        β * ∑ i, ∑ j ∈ Icc 1 k, (1 - Z i j) := by
    have := sum_le_sum fun i (_ : i ∈ univ) => sum_le_sum fun j (_ : j ∈ Icc 1 k) => hmaster i j
    simp only [sum_add_distrib, sum_sub_distrib, ← mul_sum] at this ⊢
    linarith
  by_cases hP : ∃ i, ∃ j ∈ Icc 1 k, (1 - T i j) * Z i j = 1
  · obtain ⟨i0, j0, hj0, h1⟩ := hP
    have hnn : ∀ i j, 0 ≤ (1 - T i j) * Z i j := fun i j => by
      rcases hT i j with h | h <;> rcases hZ i j with h' | h' <;> simp [h, h']
    have hP1 : 1 ≤ ∑ i, ∑ j ∈ Icc 1 k, (1 - T i j) * Z i j := by
      have h2 : (1 - T i0 j0) * Z i0 j0 ≤ ∑ j ∈ Icc 1 k, (1 - T i0 j) * Z i0 j :=
        single_le_sum (f := fun j => (1 - T i0 j) * Z i0 j) (fun j _ => hnn i0 j) hj0
      have h3 : ∑ j ∈ Icc 1 k, (1 - T i0 j) * Z i0 j ≤ ∑ i, ∑ j ∈ Icc 1 k, (1 - T i j) * Z i j :=
        single_le_sum (f := fun i => ∑ j ∈ Icc 1 k, (1 - T i j) * Z i j)
          (fun i _ => sum_nonneg fun j _ => hnn i j) (mem_univ i0)
      linarith
    have h4 : 0 ≤ (1 - β) * (∑ i, ∑ j ∈ Icc 1 k, (1 - T i j) * Z i j - 1) :=
      mul_nonneg (by linarith) (by linarith)
    have h5 : β * ∑ i, ∑ j ∈ Icc 1 k, (1 - Z i j) ≤ β * k := mul_le_mul_of_nonneg_left hZc hβ.le
    nlinarith
  · push_neg at hP
    have hTZ : ∀ i, ∀ j ∈ Icc 1 k, T i j = 0 → Z i j = 0 := by
      intro i j hj h0
      rcases hZ i j with h | h
      · exact h
      · exact absurd (by rw [h0, h]; ring) (hP i j hj)
    have hcoord : ∀ i, ∀ j ∈ Icc 1 k, 0 ≤ Y i j - Z i j := by
      intro i j hj
      rcases hT i j with h | h
      · rw [hTZ i j hj h]; linarith [hY0 i j]
      · rw [hTY i j h]; rcases hZ i j with h' | h' <;> rw [h'] <;> norm_num
    have hzero : ∀ i, ∀ j ∈ Icc 1 k, Y i j - Z i j = 0 := by
      have htot : ∑ i, ∑ j ∈ Icc 1 k, (Y i j - Z i j) = 0 := by
        apply le_antisymm
        · simp only [sum_sub_distrib]; linarith
        · exact sum_nonneg fun i _ => sum_nonneg fun j hj => hcoord i j hj
      rw [sum_eq_zero_iff_of_nonneg (fun i _ => sum_nonneg fun j hj => hcoord i j hj)] at htot
      intro i j hj
      exact (sum_eq_zero_iff_of_nonneg (fun j hj => hcoord i j hj)).1 (htot i (mem_univ i)) j hj
    apply le_of_eq
    apply sum_eq_zero; intro i _; apply sum_eq_zero; intro j hj
    have hyz := hzero i j hj
    simp only [hF]
    rcases hT i j with h | h
    · have hz := hTZ i j hj h
      have hy : Y i j = 0 := by linarith
      rw [h, hz, hy]; simp
    · have hy := hTY i j h
      have hz : Z i j = 1 := by linarith
      rw [h, hz]; ring

/-- P4a: the residual terms at the requested location sum to a nonpositive number. -/
lemma sum_i0 {c s : ℕ → ℝ} (hs : IsoSpec k c s) (β : ℝ) (hβ : 0 ≤ β) (t ζ φ : ℕ → ℝ)
    (ht : ∀ j, t j = 0 ∨ t j = 1) (hζ : ∀ j, ζ j = 0 ∨ ζ j = 1)
    (htm : ∀ a b, 1 ≤ a → a ≤ b → b ≤ k → t a ≤ t b)
    (hζm : ∀ a b, 1 ≤ a → a ≤ b → b ≤ k → ζ a ≤ ζ b)
    (htf : ∀ m, 2 ≤ m → m ≤ k → s (m - 1) = s m → t m = t (m - 1))
    (hφf : ∀ m, 2 ≤ m → m ≤ k → s (m - 1) = s m →
      (1 - t m) * φ m ≤ (1 - t (m - 1)) * φ (m - 1)) :
    ∑ a ∈ Icc 1 k, (s a - c a) *
      ((1 - t a) * φ a - 2 * (1 - t a) * ζ a + (1 + β) * t a * (1 - ζ a)) ≤ 0 := by
  have h1 := iso_abel_nonpos hs (fun a => (1 - t a) * φ a) hφf
  have h2 := iso_abel_zero hs t htf
  have h3 := iso_abel_nonneg hs ζ (fun m hm1 hm2 => hζm (m - 1) m (by omega) (by omega) hm2)
  have key : ∀ j1 ∈ Icc 1 k, ∀ j2 ∈ Icc 1 k, t j1 = 1 → ζ j1 = 0 → ζ j2 = 1 → t j2 = 0 →
      False := by
    intro j1 hj1 j2 hj2 a b e f
    rw [mem_Icc] at hj1 hj2
    rcases le_total j1 j2 with h | h
    · have := htm j1 j2 hj1.1 h hj2.2; linarith
    · have := hζm j2 j1 hj2.1 h hj1.2; linarith
  have hexp : ∀ a, (s a - c a) *
      ((1 - t a) * φ a - 2 * (1 - t a) * ζ a + (1 + β) * t a * (1 - ζ a)) =
      (s a - c a) * ((1 - t a) * φ a) - 2 * ((s a - c a) * ζ a) +
        (1 + β) * ((s a - c a) * t a) + (1 - β) * ((s a - c a) * (t a * ζ a)) := by
    intro a; ring
  rw [sum_congr rfl (fun a _ => hexp a)]
  simp only [sum_add_distrib, sum_sub_distrib, ← mul_sum]
  by_cases hA : ∀ j ∈ Icc 1 k, t j = 1 → ζ j = 1
  · have hc : ∀ j ∈ Icc 1 k, (s j - c j) * (t j * ζ j) = (s j - c j) * t j := by
      intro j hj
      rcases ht j with e | e
      · rw [e]; ring
      · rw [e, hA j hj e]; ring
    rw [sum_congr rfl hc]
    have : ∑ a ∈ Icc 1 k, (s a - c a) * t a = 0 := h2
    rw [this]
    nlinarith
  · push_neg at hA
    obtain ⟨j1, hj1, e1, e2⟩ := hA
    have e2' : ζ j1 = 0 := (hζ j1).resolve_right e2
    have hc : ∀ j ∈ Icc 1 k, (s j - c j) * (t j * ζ j) = (s j - c j) * ζ j := by
      intro j hj
      rcases hζ j with e | e
      · rw [e]; ring
      · rcases ht j with f | f
        · exact (key j1 hj1 j hj e1 e2' e f).elim
        · rw [e, f]; ring
    rw [sum_congr rfl hc]
    have : ∑ a ∈ Icc 1 k, (s a - c a) * t a = 0 := h2
    rw [this]
    nlinarith

lemma zOf_cases (n : Fin d → ℕ) (i : Fin d) (j : ℕ) : zOf n i j = 0 ∨ zOf n i j = 1 := by
  unfold zOf; split_ifs <;> simp

lemma sum_zOf (n : Fin d → ℕ) (hn : ∀ i, n i ≤ k) (i : Fin d) :
    ∑ j ∈ Icc 1 k, zOf n i j = (k : ℝ) - n i := by
  unfold zOf
  rw [← sum_filter, filter_lt_Icc, sum_const, Nat.card_Ioc, nsmul_eq_mul, mul_one,
    Nat.cast_sub (hn i)]

/-- P4b: the movement step (Claim 15, discrete): increase cost minus twice the
`Φm`-drop is at most `2 η λ·z`. -/
theorem move_step (β η : ℝ) (hβ : 0 < β) (hβk : β * (k + 1) ≤ 1) (hη : 0 ≤ η)
    (w : Fin d → ℝ) (hw : ∀ i, 0 < w i) (yo : Fin d → ℕ → ℝ)
    (hyo0 : ∀ i j, 0 ≤ yo i j) (hyo1 : ∀ i j, yo i j ≤ 1)
    (hyom : ∀ i a b, 1 ≤ a → a ≤ b → b ≤ k → yo i a ≤ yo i b)
    (r : Request d k) (hlam : ∀ j, 0 ≤ lam r j) (hrq : r.quota ≤ k)
    (s : ℕ → ℝ) (N : ℝ)
    (hP : ProxOK β η w yo r ((d : ℝ) * k - r.quota) s N)
    (n' : Fin d → ℕ) (hn' : ∀ i, n' i ≤ k) (hsum' : ∑ i, n' i ≤ r.quota) :
    ∑ i, ∑ j ∈ Icc 1 k, (w i * max 0 (yOf β w yo r.loc s N i j - yo i j) -
        2 * zOf n' i j * (w i * (Real.log (yOf β w yo r.loc s N i j + β) -
          Real.log (yo i j + β)))) ≤
      2 * η * ∑ j ∈ Icc 1 k, lam r j * zOf n' r.loc j := by
  obtain ⟨hs, hN, hQ, hslack⟩ := hP
  have hβ1 : β ≤ 1 := by
    have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    nlinarith
  set i0 := r.loc with hi0
  set y := yOf β w yo i0 s N with hy
  set Z := zOf (d := d) n' with hZ
  set T : Fin d → ℕ → ℝ := fun i j => if i = i0 then
      (if 1 < Real.exp (s j + N / w i0) - β then 1 else 0)
    else (if 1 < (yo i j + β) * Real.exp (N / w i) - β then 1 else 0) with hT
  set B : Fin d → ℕ → ℝ := fun i j => (1 - T i j) * (y i j + β) * (if 0 < y i j then 1 else 0) -
      2 * (1 - T i j) * Z i j + (1 + β) * T i j * (1 - Z i j) with hB
  set φ : ℕ → ℝ := fun j => (y i0 j + β) * (if yo i0 j < y i0 j then 1 else 0) with hφ
  set F : ℕ → ℝ := fun j => (1 - T i0 j) * φ j - 2 * (1 - T i0 j) * Z i0 j +
      (1 + β) * T i0 j * (1 - Z i0 j) with hF
  set cv := cvec β η w yo r with hcv
  have hyi0 : ∀ j, y i0 j = max 0 (min 1 (Real.exp (s j + N / w i0) - β)) := by
    intro j; simp [hy, yOf]
  have hyoff : ∀ i, i ≠ i0 → ∀ j, y i j = min 1 ((yo i j + β) * Real.exp (N / w i) - β) := by
    intro i hi j; simp [hy, yOf, hi]
  have hTi0 : ∀ j, T i0 j = if 1 < Real.exp (s j + N / w i0) - β then 1 else 0 := by
    intro j; simp [hT]
  -- per coordinate
  have hcoord : ∀ i, ∀ j ∈ Icc 1 k,
      w i * max 0 (y i j - yo i j) - 2 * Z i j * (w i * (Real.log (y i j + β) -
        Real.log (yo i j + β))) ≤
      N * B i j + (if i = i0 then 2 * η * lam r j * Z i0 j + F j * (w i0 * (s j - cv j))
        else 0) := by
    intro i j _
    by_cases hi : i = i0
    · subst hi
      rw [if_pos rfl]
      have := coord_i0 (w i0) β η (lam r j) N (yo i0 j) (Z i0 j) (s j) (cv j) (y i0 j)
        (T i0 j) (w i0 * (Real.log (y i0 j + β) - Real.log (yo i0 j + β))) (φ j)
        (w i0 * (s j - cv j)) (hw i0) hβ hβ1 hη (hyo0 i0 j) (hyo1 i0 j) (hlam j) hN
        (zOf_cases n' i0 j) (by simp [hcv, cvec, hi0]) (hyi0 j) (hTi0 j) rfl rfl rfl
      simp only [hB, hF]
      linarith
    · rw [if_neg hi]
      have hTo : T i j = if 1 < (yo i j + β) * Real.exp (N / w i) - β then 1 else 0 := by
        simp [hT, hi]
      have := coord_off (w i) β N (yo i j) (Z i j) (y i j) (T i j)
        (w i * (Real.log (y i j + β) - Real.log (yo i j + β))) (hw i) hβ hβ1
        (hyo0 i j) (hyo1 i j) hN (zOf_cases n' i j) (hyoff i hi j) hTo rfl
      simp only [hB]
      linarith
  have hsum1 := sum_le_sum fun i (_ : i ∈ univ) => sum_le_sum fun j (hj : j ∈ Icc 1 k) =>
    hcoord i j hj
  have hite : ∀ i, ∑ j ∈ Icc 1 k, (N * B i j + (if i = i0 then
      2 * η * lam r j * Z i0 j + F j * (w i0 * (s j - cv j)) else 0)) =
      N * ∑ j ∈ Icc 1 k, B i j + (if i = i0 then ∑ j ∈ Icc 1 k,
        (2 * η * lam r j * Z i0 j + F j * (w i0 * (s j - cv j))) else 0) := by
    intro i
    rw [sum_add_distrib, ← mul_sum]
    split_ifs <;> simp
  rw [sum_congr rfl fun i _ => hite i, sum_add_distrib, ← mul_sum, sum_ite_eq'] at hsum1
  simp only [mem_univ, if_true] at hsum1
  -- the bracket
  have hbr : N * ∑ i, ∑ j ∈ Icc 1 k, B i j ≤ 0 := by
    rcases eq_or_lt_of_le hN with h0 | hpos
    · rw [← h0, zero_mul]
    · apply mul_nonpos_of_nonneg_of_nonpos hN
      have hYeq := hslack hpos
      have hZsum : ∑ i, ∑ j ∈ Icc 1 k, Z i j = (d : ℝ) * k - ∑ i, (n' i : ℝ) := by
        simp only [hZ, sum_zOf n' hn', sum_sub_distrib, sum_const, card_univ, Fintype.card_fin,
          nsmul_eq_mul]
      have hsum'' : (∑ i, (n' i : ℝ)) ≤ r.quota := by exact_mod_cast hsum'
      have hrq' : (r.quota : ℝ) ≤ k := by exact_mod_cast hrq
      apply bracket_le β hβ hβk T y Z
      · intro i j; simp only [hT]; split_ifs <;> simp
      · intro i j; exact zOf_cases n' i j
      · intro i j; exact yOf_nonneg β hβ w hw yo hyo0 i0 s N hN i j
      · intro i j hTij
        by_cases hi : i = i0
        · subst hi
          rw [hTi0] at hTij
          split_ifs at hTij with hc
          · rw [hyi0, min_eq_left hc.le, max_eq_right zero_le_one]
          · norm_num at hTij
        · have hTo : T i j = if 1 < (yo i j + β) * Real.exp (N / w i) - β then 1 else 0 := by
            simp [hT, hi]
          rw [hTo] at hTij
          split_ifs at hTij with hc
          · rw [hyoff i hi, min_eq_left hc.le]
          · norm_num at hTij
      · rw [hYeq, hZsum]; linarith
      · have : ∑ i, ∑ j ∈ Icc 1 k, (1 - Z i j) = ∑ i, (n' i : ℝ) := by
          simp only [sum_sub_distrib, hZ, sum_zOf n' hn', sum_const, Nat.card_Icc,
            Nat.add_sub_cancel, nsmul_eq_mul, mul_one]
          ring
        rw [this]; linarith
  -- the residual at i0
  have hres : ∑ j ∈ Icc 1 k, F j * (w i0 * (s j - cv j)) ≤ 0 := by
    have hmono := hs.1
    have hts : ∀ a b, 1 ≤ a → a ≤ b → b ≤ k → T i0 a ≤ T i0 b := by
      intro a b ha hab hb
      rw [hTi0, hTi0]
      have := Real.exp_le_exp.2 (show s a + N / w i0 ≤ s b + N / w i0 by
        linarith [hmono a b ha hab hb])
      split_ifs with h1 h2 <;> first | exact (h2 (by linarith)).elim | norm_num
    have hs0 := sum_i0 hs β hβ.le (T i0) (Z i0) φ
      (fun j => by rw [hTi0]; split_ifs <;> simp) (fun j => zOf_cases n' i0 j) hts
      (fun a b ha hab hb => by
        simp only [hZ, zOf]; split_ifs with h1 h2 <;> first | exact (h2 (by omega)).elim | norm_num)
      (fun m _ _ he => by rw [hTi0, hTi0, he])
      (fun m h2 hk he => by
        have hyo' := hyom i0 (m - 1) m (by omega) (by omega) hk
        have hTm : T i0 m = T i0 (m - 1) := by rw [hTi0, hTi0, he]
        have hym : y i0 m = y i0 (m - 1) := by rw [hyi0, hyi0, he]
        rw [hTm]
        simp only [hφ]
        rw [hym]
        have h1t : 0 ≤ 1 - T i0 (m - 1) := by rw [hTi0]; split_ifs <;> norm_num
        have hyβ : 0 ≤ y i0 (m - 1) + β := by
          linarith [yOf_nonneg β hβ w hw yo hyo0 i0 s N hN i0 (m - 1)]
        apply mul_le_mul_of_nonneg_left _ h1t
        apply mul_le_mul_of_nonneg_left _ hyβ
        split_ifs with h1 h3 <;> first | exact (h3 (lt_of_le_of_lt hyo' h1)).elim | norm_num)
    have : ∑ j ∈ Icc 1 k, F j * (w i0 * (s j - cv j)) =
        w i0 * ∑ a ∈ Icc 1 k, (s a - cv a) *
          ((1 - T i0 a) * φ a - 2 * (1 - T i0 a) * Z i0 a + (1 + β) * T i0 a * (1 - Z i0 a)) := by
      rw [mul_sum]; apply sum_congr rfl; intro j _; simp only [hF]; ring
    rw [this]
    exact mul_nonpos_of_nonneg_of_nonpos (hw i0).le hs0
  have hlz : ∑ j ∈ Icc 1 k, (2 * η * lam r j * Z i0 j + F j * (w i0 * (s j - cv j))) =
      2 * η * ∑ j ∈ Icc 1 k, lam r j * Z i0 j + ∑ j ∈ Icc 1 k, F j * (w i0 * (s j - cv j)) := by
    rw [sum_add_distrib, mul_sum]; congr 1; apply sum_congr rfl; intro j _; ring
  rw [hlz] at hsum1
  linarith

end Ba300cc1



namespace Ba300cc1
open PolylogKServer.Allocation Finset

variable {d k : ℕ}

lemma cumul_mono (x : FracState d k) (hx : ∀ i j, 0 ≤ x i j) (i : Fin d) (a b : ℕ)
    (hab : a ≤ b) : cumul x i a ≤ cumul x i b := by
  unfold cumul
  apply sum_le_sum
  intro j _
  by_cases h1 : (j : ℕ) < a
  · rw [if_pos h1, if_pos (by omega)]
  · rw [if_neg h1]
    split_ifs
    · exact hx i j
    · exact le_rfl

lemma lam_nonneg (r : Request d k) (hr : r.Valid) (j : ℕ) : 0 ≤ lam r j := by
  unfold lam Request.hAt
  have hle : (⟨min (j - 1) k, Nat.lt_succ_of_le (Nat.min_le_right _ _)⟩ : Fin (k + 1)) ≤
      ⟨min j k, Nat.lt_succ_of_le (Nat.min_le_right _ _)⟩ := by
    rw [Fin.mk_le_mk]; omega
  have := hr.2.2 hle
  linarith

lemma pointMass_feasible (n₀ : Fin d → ℕ) (hn : ∀ i, n₀ i ≤ k) (κ₀ : ℕ)
    (hs : ∑ i, n₀ i ≤ κ₀) : FracFeasible (pointMass (k := k) n₀) κ₀ := by
  refine ⟨fun i j => by unfold pointMass; split_ifs <;> norm_num, fun i => ?_, ?_⟩
  · unfold pointMass
    rw [Fin.sum_univ_eq_sum_range (fun j => if j = n₀ i then (1 : ℝ) else 0) (k + 1),
      sum_ite_eq' (range (k + 1)) (n₀ i) (fun _ => (1 : ℝ))]
    rw [if_pos (mem_range.2 (Nat.lt_succ_of_le (hn i)))]
  · have h : ∀ i, ∑ j : Fin (k + 1), ((j : ℕ) : ℝ) * pointMass (k := k) n₀ i j = n₀ i := by
      intro i
      unfold pointMass
      rw [Fin.sum_univ_eq_sum_range (fun j => (j : ℝ) * if j = n₀ i then (1 : ℝ) else 0) (k + 1)]
      simp only [mul_ite, mul_one, mul_zero]
      rw [sum_ite_eq' (range (k + 1)) (n₀ i) (fun j => (j : ℝ)),
        if_pos (mem_range.2 (Nat.lt_succ_of_le (hn i)))]
    rw [sum_congr rfl fun i _ => h i]
    exact_mod_cast hs

lemma ext_mono (y : ℕ → ℝ) (h0 : ∀ j, 0 ≤ y j) (h1 : ∀ j, y j ≤ 1)
    (hm : ∀ a b, 1 ≤ a → a ≤ b → b ≤ k → y a ≤ y b) (j : ℕ) (hj : j ≤ k) :
    ext k y j ≤ ext k y (j + 1) := by
  by_cases hj0 : j = 0
  · subst hj0
    rw [ext, if_pos rfl, ext, if_neg (by omega)]
    split_ifs
    · exact h0 1
    · exact zero_le_one
  · rw [ext, if_neg hj0, if_pos hj, ext, if_neg (by omega)]
    split_ifs with h
    · exact hm j (j + 1) (by omega) (by omega) h
    · exact h1 j

lemma yOf_mono (β : ℝ) (w : Fin d → ℝ) (yo : Fin d → ℕ → ℝ)
    (hyom : ∀ i a b, 1 ≤ a → a ≤ b → b ≤ k → yo i a ≤ yo i b) (i0 : Fin d) (s : ℕ → ℝ)
    (hsm : ∀ a b, 1 ≤ a → a ≤ b → b ≤ k → s a ≤ s b) (N : ℝ) :
    ∀ i a b, 1 ≤ a → a ≤ b → b ≤ k → yOf β w yo i0 s N i a ≤ yOf β w yo i0 s N i b := by
  intro i a b ha hab hb
  unfold yOf
  split_ifs
  · exact max_le_max le_rfl (min_le_min le_rfl (sub_le_sub_right
      (Real.exp_le_exp.2 (by linarith [hsm a b ha hab hb])) _))
  · exact min_le_min le_rfl (sub_le_sub_right (mul_le_mul_of_nonneg_right
      (by linarith [hyom i a b ha hab hb]) (Real.exp_pos _).le) _)

lemma cumul_ofY_Icc (y : Fin d → ℕ → ℝ) (i : Fin d) (j : ℕ) (hj : j ∈ Icc 1 k) :
    cumul (ofY (k := k) y) i j = y i j := by
  rw [mem_Icc] at hj
  rw [cumul_ofY y i j (by omega), ext, if_neg (by omega), if_pos hj.2]

open Classical in
/-- The step's cumulative vector (prox step at nonnegative states). -/
noncomputable def stepY (β η : ℝ) (hβ : 0 < β) (w : Fin d → ℝ) (hw : ∀ i, 0 < w i)
    (x : FracState d k) (r : Request d k) : Fin d → ℕ → ℝ :=
  if hx : ∀ i j, 0 ≤ cumul x i j then
    yOf β w (cumul x) r.loc
      (prox_exists β η hβ w hw (cumul x) hx r ((d : ℝ) * k - r.quota)
        (sub_le_self _ (Nat.cast_nonneg _))).choose
      (prox_exists β η hβ w hw (cumul x) hx r ((d : ℝ) * k - r.quota)
        (sub_le_self _ (Nat.cast_nonneg _))).choose_spec.choose
  else cumul x

lemma stepY_spec (β η : ℝ) (hβ : 0 < β) (w : Fin d → ℝ) (hw : ∀ i, 0 < w i)
    (x : FracState d k) (r : Request d k) (hx : ∀ i j, 0 ≤ cumul x i j) :
    ∃ s N, ProxOK β η w (cumul x) r ((d : ℝ) * k - r.quota) s N ∧
      stepY β η hβ w hw x r = yOf β w (cumul x) r.loc s N := by
  unfold stepY
  rw [dif_pos hx]
  exact ⟨_, _, (prox_exists β η hβ w hw (cumul x) hx r ((d : ℝ) * k - r.quota)
    (sub_le_self _ (Nat.cast_nonneg _))).choose_spec.choose_spec, rfl⟩

lemma step_feasible (β η : ℝ) (hβ : 0 < β) (w : Fin d → ℝ) (hw : ∀ i, 0 < w i)
    (x : FracState d k) (q : ℕ) (hx : FracFeasible x q) (r : Request d k) :
    FracFeasible (ofY (k := k) (stepY β η hβ w hw x r)) r.quota := by
  have hb := cumul_bounds x q hx
  obtain ⟨s, N, hP, he⟩ := stepY_spec β η hβ w hw x r fun i j => (hb i j).1
  rw [he]
  apply feasible_ofY
  · intro i j hj
    apply ext_mono
    · exact yOf_nonneg β hβ w hw (cumul x) (fun i j => (hb i j).1) r.loc s N hP.2.1 i
    · exact yOf_le_one β w (cumul x) r.loc s N i
    · exact yOf_mono β w (cumul x) (fun i a b _ hab _ => cumul_mono x hx.1 i a b hab) r.loc s
        hP.1.1 N i
    · exact hj
  · exact hP.2.2.1

lemma abs_eq_two_max (a : ℝ) : |a| = 2 * max 0 a - a := by
  rcases le_total 0 a with h | h
  · rw [abs_of_nonneg h, max_eq_right h]; ring
  · rw [abs_of_nonpos h, max_eq_left h]; ring

lemma Phim_bounds (β : ℝ) (hβ : 0 < β) (w : Fin d → ℝ) (hw : ∀ i, 0 < w i)
    (x : FracState d k) (hx : ∀ i j, 0 ≤ cumul x i j ∧ cumul x i j ≤ 1) (n : Fin d → ℕ) :
    0 ≤ Phim 1 β w x n ∧ Phim 1 β w x n ≤ ∑ i, w i * (k * Real.log ((1 + β) / β)) := by
  unfold Phim
  rw [one_mul]
  constructor
  · exact sum_nonneg fun i _ => mul_nonneg (hw i).le (sum_nonneg fun j _ => by
      split_ifs
      · exact Lg_nonneg hβ (hx i j).1 (hx i j).2
      · exact le_rfl)
  · apply sum_le_sum
    intro i _
    apply mul_le_mul_of_nonneg_left _ (hw i).le
    have : ∑ j ∈ Icc 1 k, (if n i < j then Lg β (cumul x i j) else 0) ≤
        ∑ j ∈ Icc 1 k, Real.log ((1 + β) / β) := by
      apply sum_le_sum
      intro j _
      have h0 : 0 ≤ Real.log ((1 + β) / β) :=
        le_trans (Lg_nonneg hβ (hx i j).1 (hx i j).2) (Lg_le hβ (hx i j).1)
      split_ifs
      · exact Lg_le hβ (hx i j).1
      · exact h0
    rw [sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul] at this
    exact this

lemma sumY_bounds (w : Fin d → ℝ) (hw : ∀ i, 0 < w i) (x : FracState d k)
    (hx : ∀ i j, 0 ≤ cumul x i j ∧ cumul x i j ≤ 1) :
    0 ≤ ∑ i, w i * ∑ j ∈ Icc 1 k, cumul x i j ∧
      ∑ i, w i * ∑ j ∈ Icc 1 k, cumul x i j ≤ ∑ i, w i * k := by
  constructor
  · exact sum_nonneg fun i _ => mul_nonneg (hw i).le (sum_nonneg fun j _ => (hx i j).1)
  · apply sum_le_sum
    intro i _
    apply mul_le_mul_of_nonneg_left _ (hw i).le
    have : ∑ j ∈ Icc 1 k, cumul x i j ≤ ∑ j ∈ Icc 1 k, (1 : ℝ) :=
      sum_le_sum fun j _ => (hx i j).2
    simpa using this

lemma wmax_nonneg (w : Fin d → ℝ) (hw : ∀ i, 0 < w i) : 0 ≤ wmax w :=
  Real.iSup_nonneg fun i => (hw i).le

lemma zOf_bounds (n' : Fin d → ℕ) (i : Fin d) (j : ℕ) : 0 ≤ zOf n' i j ∧ zOf n' i j ≤ 1 := by
  rcases zOf_cases n' i j with h | h <;> rw [h] <;> norm_num

lemma zOf_mono (n' : Fin d → ℕ) :
    ∀ i a b, 1 ≤ a → a ≤ b → b ≤ k → zOf n' i a ≤ zOf n' i b := by
  intro i a b _ hab _
  unfold zOf
  split_ifs with h1 h2 <;> first | exact (h2 (by omega)).elim | norm_num

lemma lam_zOf (r : Request d k) (n' : Fin d → ℕ) (hn' : ∀ i, n' i ≤ k) :
    ∑ j ∈ Icc 1 k, lam r j * zOf n' r.loc j = r.hAt (n' r.loc) - r.hAt k := by
  rw [hAt_eq_sum r (n' r.loc) (hn' r.loc), add_sub_cancel_left]
  apply sum_congr rfl
  intro j _
  unfold zOf
  split_ifs <;> ring

lemma step_hit (β : ℝ) (hβ : 0 < β) (w : Fin d → ℝ) (hw : ∀ i, 0 < w i)
    (x : FracState d k) (q : ℕ) (hx : FracFeasible x q) (r : Request d k)
    (n n' : Fin d → ℕ) (hn : ∀ i, n i ≤ k) (hn' : ∀ i, n' i ≤ k)
    (hsum' : ∑ i, n' i ≤ r.quota) :
    hitCost r (ofY (k := k) (stepY β (Real.log ((1 + β) / β)) hβ w hw x r)) +
        Psih (k := k) β w (zOf n')
          (cumul (ofY (k := k) (stepY β (Real.log ((1 + β) / β)) hβ w hw x r))) /
          Real.log ((1 + β) / β) -
        Psih (k := k) β w (zOf n) (cumul x) / Real.log ((1 + β) / β) ≤
      r.hAt (n' r.loc) + ∑ i, w i * |((n' i : ℕ) : ℝ) - ((n i : ℕ) : ℝ)| := by
  set L := Real.log ((1 + β) / β) with hLdef
  have hL : 0 < L := Real.log_pos (by rw [lt_div_iff₀ hβ]; linarith)
  have hb := cumul_bounds x q hx
  have hfe := step_feasible β L hβ w hw x q hx r
  obtain ⟨s, N, hP, he⟩ := stepY_spec β L hβ w hw x r fun i j => (hb i j).1
  set y' := yOf β w (cumul x) r.loc s N with hy'
  have hcx : ∀ i, ∀ j ∈ Icc 1 k,
      cumul (ofY (k := k) (stepY β L hβ w hw x r)) i j = y' i j := by
    intro i j hj; rw [cumul_ofY_Icc _ i j hj, he]
  have hPs : Psih (k := k) β w (zOf n') (cumul (ofY (k := k) (stepY β L hβ w hw x r))) =
      Psih (k := k) β w (zOf n') y' := by
    unfold Psih
    exact sum_congr rfl fun i _ => sum_congr rfl fun j hj => by rw [hcx i j hj]
  have hhit : hitCost r (ofY (k := k) (stepY β L hβ w hw x r)) =
      r.hAt k + ∑ j ∈ Icc 1 k, lam r j * y' r.loc j := by
    rw [hitCost_eq, hfe.2.1 r.loc, mul_one]
    congr 1
    exact sum_congr rfl fun j hj => by rw [hcx r.loc j hj]
  have hzQ : (d : ℝ) * k - r.quota ≤ ∑ i, ∑ j ∈ Icc 1 k, zOf n' i j := by
    rw [sum_congr rfl fun i _ => sum_zOf n' hn' i, sum_sub_distrib, sum_const, card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    have : (∑ i, (n' i : ℝ)) ≤ r.quota := by exact_mod_cast hsum'
    linarith
  have h1 := hit_step β L hβ w hw (cumul x) (fun i j => (hb i j).1) r _ s N hP (zOf n')
    (fun i j => (zOf_bounds n' i j).1) (fun i j => (zOf_bounds n' i j).2) (zOf_mono n') hzQ
  have h2 := Psih_move β hβ w hw (cumul x) (fun i j => (hb i j).1) (fun i j => (hb i j).2)
    n n' hn hn'
  have hlz := lam_zOf r n' hn'
  rw [hhit, hPs]
  have key : (L * ∑ j ∈ Icc 1 k, lam r j * y' r.loc j + Psih (k := k) β w (zOf n') y' -
      Psih (k := k) β w (zOf n) (cumul x)) / L ≤
      (L * ∑ j ∈ Icc 1 k, lam r j * zOf n' r.loc j +
        L * ∑ i, w i * |((n' i : ℕ) : ℝ) - ((n i : ℕ) : ℝ)|) / L :=
    div_le_div_of_nonneg_right (by linarith) hL.le
  rw [sub_div, add_div, mul_div_cancel_left₀ _ hL.ne', add_div, mul_div_cancel_left₀ _ hL.ne',
    mul_div_cancel_left₀ _ hL.ne'] at key
  linarith

lemma step_move (β : ℝ) (hβ : 0 < β) (hβk : β * (k + 1) ≤ 1) (w : Fin d → ℝ)
    (hw : ∀ i, 0 < w i) (x : FracState d k) (q : ℕ) (hx : FracFeasible x q)
    (r : Request d k) (hr : r.Valid)
    (n n' : Fin d → ℕ) (hn : ∀ i, n i ≤ k) (hn' : ∀ i, n' i ≤ k)
    (hsum' : ∑ i, n' i ≤ r.quota) :
    moveCost w x (ofY (k := k) (stepY β (Real.log ((1 + β) / β)) hβ w hw x r)) +
        (4 * Phim 1 β w (ofY (k := k) (stepY β (Real.log ((1 + β) / β)) hβ w hw x r)) n' +
          ∑ i, w i * ∑ j ∈ Icc 1 k,
            cumul (ofY (k := k) (stepY β (Real.log ((1 + β) / β)) hβ w hw x r)) i j) -
        (4 * Phim 1 β w x n + ∑ i, w i * ∑ j ∈ Icc 1 k, cumul x i j) ≤
      4 * Real.log ((1 + β) / β) *
        (r.hAt (n' r.loc) + ∑ i, w i * |((n' i : ℕ) : ℝ) - ((n i : ℕ) : ℝ)|) := by
  set L := Real.log ((1 + β) / β) with hLdef
  have hL : 0 < L := Real.log_pos (by rw [lt_div_iff₀ hβ]; linarith)
  have hb := cumul_bounds x q hx
  obtain ⟨s, N, hP, he⟩ := stepY_spec β L hβ w hw x r fun i j => (hb i j).1
  set y' := yOf β w (cumul x) r.loc s N with hy'
  have hcx : ∀ i, ∀ j ∈ Icc 1 k,
      cumul (ofY (k := k) (stepY β L hβ w hw x r)) i j = y' i j := by
    intro i j hj; rw [cumul_ofY_Icc _ i j hj, he]
  have hm := move_step β L hβ hβk hL.le w hw (cumul x) (fun i j => (hb i j).1)
    (fun i j => (hb i j).2) (fun i a b _ hab _ => cumul_mono x hx.1 i a b hab) r
    (lam_nonneg r hr) hr.1 s N hP n' hn' hsum'
  have hPm := Phim_move 1 β zero_le_one hβ w hw x hb n n' hn hn'
  have hId : moveCost w x (ofY (k := k) (stepY β L hβ w hw x r)) +
      (4 * Phim 1 β w (ofY (k := k) (stepY β L hβ w hw x r)) n' +
        ∑ i, w i * ∑ j ∈ Icc 1 k, cumul (ofY (k := k) (stepY β L hβ w hw x r)) i j) -
      (4 * Phim 1 β w x n' + ∑ i, w i * ∑ j ∈ Icc 1 k, cumul x i j) =
      2 * ∑ i, ∑ j ∈ Icc 1 k, (w i * max 0 (y' i j - cumul x i j) -
        2 * zOf n' i j * (w i * (Real.log (y' i j + β) - Real.log (cumul x i j + β)))) := by
    unfold moveCost Phim
    simp only [one_mul, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    refine sum_congr rfl fun i _ => sum_congr rfl fun j hj => ?_
    rw [hcx i j hj, abs_eq_two_max]
    have h0 := (hb i j).1
    have h0' := yOf_nonneg β hβ w hw (cumul x) (fun i j => (hb i j).1) r.loc s N hP.2.1 i j
    unfold zOf
    split_ifs
    · have hL' := Lg_sub β (cumul x i j) (y' i j) hβ h0 h0'
      linear_combination (4 * w i) * hL'
    · ring
  have hlz := lam_zOf r n' hn'
  have hk0 : 0 ≤ r.hAt k := hr.2.1 _
  have hLk := mul_nonneg hL.le hk0
  rw [one_mul] at hPm
  rw [hlz] at hm
  linarith

lemma main_comp (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε ≤ 1) (d k : ℕ) (w : Fin d → ℝ)
    (n₀ : Fin d → ℕ) (κ₀ : ℕ) (hk : 2 ≤ k) (hw : ∀ i, 0 < w i) (hn₀ : ∀ i, n₀ i ≤ k)
    (hsum : ∑ i, n₀ i ≤ κ₀) :
    ∃ A : FracAlg d k, A.IsCompetitive w n₀ κ₀ (1 + ε) (8 * Real.log (k / ε)) := by
  have hk0 : (2 : ℝ) ≤ k := by exact_mod_cast hk
  set β : ℝ := ε / (k + 1) with hβdef
  have hβ : 0 < β := div_pos hε0 (by linarith)
  have hβk : β * (k + 1) = ε := div_mul_cancel₀ _ (by linarith)
  set L := Real.log ((1 + β) / β) with hLdef
  have hL : 0 < L := Real.log_pos (by rw [lt_div_iff₀ hβ]; linarith)
  have hγ : 0 < Real.log (k / ε) := Real.log_pos (by rw [lt_div_iff₀ hε0]; linarith)
  have hLγ : 4 * L ≤ 8 * Real.log (k / ε) := by
    have e1 : (1 + β) / β = 1 + (k + 1) / ε := by
      rw [add_div, div_self hβ.ne', hβdef, one_div_div]; ring
    have e2 : (1 + β) / β ≤ (k / ε) ^ 2 := by
      rw [e1, div_pow, le_div_iff₀ (by positivity), add_mul, one_mul, sq ε, ← mul_assoc,
        div_mul_cancel₀ _ hε0.ne']
      have : ε * ε ≤ 1 := by nlinarith
      have : (k + 1) * ε ≤ (k + 1 : ℝ) := by nlinarith
      nlinarith
    have e3 := Real.log_le_log (div_pos (by linarith) hβ) e2
    rw [Real.log_pow] at e3
    push_cast at e3
    linarith
  set Bh : ℝ := ∑ i, ∑ j ∈ Icc 1 k, w i * ((1 + β) * L + 1) with hBh
  set B : ℝ := Bh / L + 4 * ∑ i, w i * (k * L) + ∑ i, w i * k with hB
  refine ⟨ofStep (pointMass n₀) (fun x r => ofY (k := k) (stepY β L hβ w hw x r)), ?_⟩
  apply competitive_of_step w n₀ κ₀ (1 + ε) (8 * Real.log (k / ε)) B (by linarith)
    (by linarith) hn₀ hsum (pointMass n₀) rfl _ (fun x q => FracFeasible x q)
    (pointMass_feasible n₀ hn₀ κ₀ hsum) (fun x q r hx _ => step_feasible β L hβ w hw x q hx r)
    (fun x q h => h) (fun x n => Psih (k := k) β w (zOf n) (cumul x) / L)
    (fun x n => 4 * Phim 1 β w x n + ∑ i, w i * ∑ j ∈ Icc 1 k, cumul x i j)
  · intro x q n hx _
    beta_reduce
    have hb := cumul_bounds x q hx
    obtain ⟨p0, p1⟩ := Psih_bounds β hβ w hw (zOf n) (cumul x)
      (fun i j => (zOf_bounds n i j).1) (fun i j => (zOf_bounds n i j).2)
      (fun i j => (hb i j).1) (fun i j => (hb i j).2)
    obtain ⟨m0, m1⟩ := Phim_bounds β hβ w hw x hb n
    obtain ⟨y0, y1⟩ := sumY_bounds w hw x hb
    have hd0 : 0 ≤ Psih (k := k) β w (zOf n) (cumul x) / L := div_nonneg p0 hL.le
    have hd1 : Psih (k := k) β w (zOf n) (cumul x) / L ≤ Bh / L :=
      div_le_div_of_nonneg_right p1 hL.le
    constructor
    · rw [abs_of_nonneg hd0]; linarith
    · rw [abs_of_nonneg (by linarith)]; linarith
  · intro x q r n n' hx hr hn _ hn' hsum'
    beta_reduce
    have hX : 0 ≤ wmax w * |(r.quota : ℝ) - (q : ℝ)| :=
      mul_nonneg (wmax_nonneg w hw) (abs_nonneg _)
    have hM : 0 ≤ ∑ i, w i * |((n' i : ℕ) : ℝ) - ((n i : ℕ) : ℝ)| :=
      sum_nonneg fun i _ => mul_nonneg (hw i).le (abs_nonneg _)
    have hH : 0 ≤ r.hAt (n' r.loc) := hr.2.1 _
    have h1 := step_hit β hβ w hw x q hx r n n' hn hn' hsum'
    have h2 := step_move β hβ (by rw [hβk]; exact hε1) w hw x q hx r hr n n' hn hn' hsum'
    have hS : 0 ≤ r.hAt (n' r.loc) + ∑ i, w i * |((n' i : ℕ) : ℝ) - ((n i : ℕ) : ℝ)| +
        wmax w * |(r.quota : ℝ) - (q : ℝ)| := by linarith
    constructor
    · nlinarith [mul_nonneg hε0.le hS]
    · nlinarith [mul_le_mul_of_nonneg_right hLγ hS, mul_nonneg hL.le hX]

end Ba300cc1

open PolylogKServer.Allocation in
theorem solution :
    ∃ C : ℝ, 0 < C ∧ ∀ (ε : ℝ), 0 < ε → ε ≤ 1 →
      ∀ (d k : ℕ) (w : Fin d → ℝ) (n₀ : Fin d → ℕ) (κ₀ : ℕ), 2 ≤ k →
        (∀ i, 0 < w i) → (∀ i, n₀ i ≤ k) → ∑ i, n₀ i ≤ κ₀ → κ₀ ≤ k →
        ∃ A : FracAlg d k, A.IsCompetitive w n₀ κ₀ (1 + ε) (C * Real.log (k / ε)) := by
  refine ⟨8, by norm_num, ?_⟩
  intro ε hε0 hε1 d k w n₀ κ₀ hk hw hn₀ hsum _
  exact Ba300cc1.main_comp ε hε0 hε1 d k w n₀ κ₀ hk hw hn₀ hsum

