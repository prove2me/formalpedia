-- Prove2me | solution 1 for RandomLeadGBS.Diffusion.lemma_8_centered
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-20T11:48:20.576146+00:00
-- url     : https://prove2.me/submissions/c1228bb1-3e86-47e8-a761-c710bda86a25

import Mathlib
import Definitions.Def_RandomLeadGBS_Diffusion_Model

open RandomLeadGBS.Diffusion

namespace GBSLemma8

/-- Summing a summable family over one level `{s | s.1 = k}` of `ℤ × ℕ`. -/
lemma level_sum (g : State → ℝ) (hg : Summable g) (k : ℤ) :
    ∑' s : State, (if s.1 = k then g s else 0) = ∑' z : ℕ, g (k, z) := by
  have hs : Summable (fun s : State => if s.1 = k then g s else 0) := by
    refine Summable.of_norm_bounded hg.abs (fun s => ?_)
    split_ifs <;> simp
  rw [Summable.tsum_prod hs]
  have : (fun y : ℤ => ∑' z : ℕ, (if (y, z).1 = k then g (y, z) else 0)) =
      fun y => if y = k then ∑' z : ℕ, g (k, z) else 0 := by
    funext y
    by_cases hy : y = k
    · subst hy; simp
    · simp [hy]
  rw [this, tsum_ite_eq]

/-- Row sums of the rate matrix against a test function. -/
lemma row (P : Params) (r : ℝ) (s : State) (h : State → ℝ) :
    (fun s' => rate P r s s' * h s') =
      fun s' => (if s' = afterCustomer P r s then r * h (afterCustomer P r s) else 0) +
        (if s' = afterItem P r s then P.β * (s.2 : ℝ) * h (afterItem P r s) else 0) := by
  funext s'
  simp only [rate, add_mul]
  congr 1
  · split_ifs with h1
    · subst h1; rfl
    · simp
  · by_cases h1 : s' = afterItem P r s
    · subst h1
      by_cases hz : 1 ≤ s.2
      · simp [hz]
      · have : s.2 = 0 := by omega
        simp [this]
    · simp [h1]

lemma row_summable (P : Params) (r : ℝ) (s : State) (h : State → ℝ) :
    Summable (fun s' => rate P r s s' * h s') := by
  rw [row]
  exact (summable_of_ne_finset_zero (s := {afterCustomer P r s}) (by intro j hj; simp_all)).add
    (summable_of_ne_finset_zero (s := {afterItem P r s}) (by intro j hj; simp_all))

lemma row_tsum (P : Params) (r : ℝ) (s : State) (h : State → ℝ) :
    ∑' s', rate P r s s' * h s' =
      r * h (afterCustomer P r s) + P.β * (s.2 : ℝ) * h (afterItem P r s) := by
  rw [row, Summable.tsum_add
    (summable_of_ne_finset_zero (s := {afterCustomer P r s}) (by intro j hj; simp_all))
    (summable_of_ne_finset_zero (s := {afterItem P r s}) (by intro j hj; simp_all)),
    tsum_ite_eq, tsum_ite_eq]

lemma rate_nonneg (P : Params) (r : ℝ) (hr : 0 < r) (hβ : 0 < P.β) (s s' : State) :
    0 ≤ rate P r s s' := by
  unfold rate
  apply add_nonneg
  · split_ifs <;> linarith
  · split_ifs
    · positivity
    · rfl

/-- The flux identity: for a bounded test function `h`, stationarity gives
`E[ r h(after customer) + β Z h(after item) ] = E[(r + β Z) h]`. -/
lemma flux (P : Params) (r : ℝ) (hr : 0 < r) (hβ : 0 < P.β) (p : State → ℝ)
    (hp : IsStationary P r p) (h : State → ℝ) (hh : ∀ s, |h s| ≤ 1) :
    ∑' s, p s * (r * h (afterCustomer P r s) + P.β * (s.2 : ℝ) * h (afterItem P r s)) =
      ∑' s, p s * exitRate P r s * h s := by
  obtain ⟨hnn, _hsum, _hone, hsumx, hbal⟩ := hp
  -- summability of the double family
  have hG : Summable (fun x : State × State => p x.1 * rate P r x.1 x.2) := by
    refine (summable_prod_of_nonneg (fun x => mul_nonneg (hnn _) (rate_nonneg P r hr hβ _ _))).mpr
      ⟨fun s => ?_, ?_⟩
    · simpa using (row_summable P r s (fun _ => 1)).mul_left (p s)
    · have : (fun s : State => ∑' s' : State, p (s, s').1 * rate P r (s, s').1 (s, s').2) =
          fun s => p s * exitRate P r s := by
        funext s
        simp only
        rw [tsum_mul_left]
        have := row_tsum P r s (fun _ => 1)
        simp only [mul_one] at this
        rw [this, exitRate]
      rw [this]; exact hsumx
  have hF : Summable (Function.uncurry (fun s s' : State => p s * rate P r s s' * h s')) := by
    refine Summable.of_norm_bounded hG (fun x => ?_)
    simp only [Function.uncurry, Real.norm_eq_abs, abs_mul]
    rw [abs_of_nonneg (hnn _), abs_of_nonneg (rate_nonneg P r hr hβ _ _)]
    have := hh x.2
    have h0 : 0 ≤ p x.1 * rate P r x.1 x.2 := mul_nonneg (hnn _) (rate_nonneg P r hr hβ _ _)
    nlinarith
  symm
  calc ∑' s, p s * exitRate P r s * h s
      = ∑' s', (∑' s, p s * rate P r s s') * h s' := by
        congr 1; funext s'; rw [hbal s']
    _ = ∑' s', ∑' s, p s * rate P r s s' * h s' := by
        congr 1; funext s'; rw [tsum_mul_right]
    _ = ∑' s, ∑' s', p s * rate P r s s' * h s' := hF.tsum_comm
    _ = ∑' s, p s * (r * h (afterCustomer P r s) + P.β * (s.2 : ℝ) * h (afterItem P r s)) := by
        congr 1; funext s
        rw [← row_tsum, ← tsum_mul_left]
        congr 1; funext s'; ring


/-- Cut equations for the GBS chain: `β E[Z; Y = k] = r P(Y = k+1)`. -/
lemma cut_eq (P : Params) (r : ℝ) (hr : 0 < r) (hβ : 0 < P.β) (p : State → ℝ)
    (hp : IsStationary P r p) :
    Summable (fun s : State => p s * (s.2 : ℝ)) ∧
    ∀ k : ℤ, P.β * (∑' z : ℕ, p (k, z) * (z : ℝ)) = r * ∑' z : ℕ, p (k + 1, z) := by
  have hp' := hp
  obtain ⟨hnn, hsum, hone, hsumx, _hbal⟩ := hp'
  have hsZ : Summable (fun s : State => p s * (s.2 : ℝ)) := by
    have : (fun s : State => p s * (s.2 : ℝ)) =
        fun s => (p s * exitRate P r s - r * p s) / P.β := by
      funext s; simp only [exitRate]; field_simp; ring
    rw [this]; exact (hsumx.sub (hsum.mul_left r)).div_const _
  -- level quantities
  set m : ℤ → ℝ := fun k => ∑' z : ℕ, p (k, z) with hm
  set w : ℤ → ℝ := fun k => ∑' z : ℕ, p (k, z) * (z : ℝ) with hw
  have hlev : ∀ k : ℤ, r * m (k + 1) + P.β * w (k - 1) = r * m k + P.β * w k := by
    intro k
    have hfl := flux P r hr hβ p hp (fun s => if s.1 = k then 1 else 0)
      (fun s => by split_ifs <;> simp)
    have hL : (fun s : State => p s * (r * (if (afterCustomer P r s).1 = k then (1:ℝ) else 0) +
        P.β * (s.2 : ℝ) * (if (afterItem P r s).1 = k then (1:ℝ) else 0))) =
        fun s => (if s.1 = k + 1 then r * p s else 0) +
          (if s.1 = k - 1 then P.β * (p s * (s.2 : ℝ)) else 0) := by
      funext s
      have e1 : (afterCustomer P r s).1 = s.1 - 1 := rfl
      have e2 : (afterItem P r s).1 = s.1 + 1 := rfl
      simp only [e1, e2]
      split_ifs <;> first | (exfalso; omega) | ring
    have hR : (fun s : State => p s * exitRate P r s * (if s.1 = k then (1:ℝ) else 0)) =
        fun s => (if s.1 = k then r * p s else 0) +
          (if s.1 = k then P.β * (p s * (s.2 : ℝ)) else 0) := by
      funext s
      simp only [exitRate]
      split_ifs <;> ring
    rw [hL, hR] at hfl
    have s1 : ∀ k' : ℤ, Summable (fun s : State => if s.1 = k' then r * p s else 0) := by
      intro k'
      refine Summable.of_norm_bounded ((hsum.mul_left r).abs) (fun s => ?_)
      split_ifs <;> simp <;> positivity
    have s2 : ∀ k' : ℤ, Summable (fun s : State =>
        if s.1 = k' then P.β * (p s * (s.2 : ℝ)) else 0) := by
      intro k'
      refine Summable.of_norm_bounded ((hsZ.mul_left P.β).abs) (fun s => ?_)
      split_ifs <;> simp <;> positivity
    rw [Summable.tsum_add (s1 _) (s2 _), Summable.tsum_add (s1 _) (s2 _),
      level_sum _ (hsum.mul_left r), level_sum _ (hsum.mul_left r),
      level_sum _ (hsZ.mul_left P.β), level_sum _ (hsZ.mul_left P.β)] at hfl
    simp only [tsum_mul_left] at hfl
    simpa [hm, hw] using hfl
  -- φ k = β w k - r m (k+1) is constant
  set φ : ℤ → ℝ := fun k => P.β * w k - r * m (k + 1) with hφ
  have hstep : ∀ k : ℤ, φ k = φ (k - 1) := by
    intro k
    have := hlev k
    simp only [hφ, sub_add_cancel]; linarith
  have hconst : ∀ k : ℤ, φ k = φ 0 := by
    intro k
    induction k using Int.induction_on with
    | zero => rfl
    | succ k ih => rw [hstep (k + 1)]; simpa using ih
    | pred k ih => have := hstep (-(k:ℤ)); linarith
  have hpnn : 0 ≤ p := fun s => hnn s
  have hsm : Summable m := ((summable_prod_of_nonneg hpnn).mp hsum).2
  have hsw : Summable w := by
    have h0 : 0 ≤ (fun s : State => p s * (s.2 : ℝ)) := fun s => mul_nonneg (hnn s) (by positivity)
    exact ((summable_prod_of_nonneg h0).mp hsZ).2
  have hsm1 : Summable (fun k : ℤ => r * m (k + 1)) :=
    (Equiv.addRight (1 : ℤ)).summable_iff.mpr (hsm.mul_left r)
  have hsφ : Summable φ := (hsw.mul_left P.β).sub hsm1
  have hφ0 : φ 0 = 0 := by
    have : Summable (fun _ : ℤ => φ 0) := by
      have : φ = fun _ => φ 0 := funext hconst
      rwa [this] at hsφ
    exact (summable_const_iff (φ 0)).mp this
  have hab : ∀ k, P.β * w k = r * m (k + 1) := by
    intro k; have := hconst k; rw [hφ0] at this; simp only [hφ] at this; linarith
  exact ⟨hsZ, fun k => hab k⟩

/-- Cut equations for the artificial chain: `β Ẑ(j) q(j) = r q(j+1)`. -/
lemma art_cut (P : Params) (r : ℝ) (hβ : 0 < P.β) (p : ℤ → ℝ) (hp : IsArtStationary P r p) :
    ∀ j : ℤ, p j * (P.β * (artZ P r j : ℝ)) = p (j + 1) * r := by
  obtain ⟨_hnn, hsum, hone, hsumx, hbal⟩ := hp
  set Z : ℤ → ℝ := fun j => (artZ P r j : ℝ) with hZ
  -- a j : up-flux, b j : down-flux
  set a : ℤ → ℝ := fun j => p j * (P.β * Z j) with ha
  set b : ℤ → ℝ := fun j => p j * r with hb
  have hsa : Summable a := by
    have : a = fun j => p j * artExitRate P r j - p j * r := by
      funext j; simp only [ha, artExitRate, hZ]; ring
    rw [this]; exact hsumx.sub (hsum.mul_right r)
  have hsZ : Summable (fun j : ℤ => p j * Z j) := by
    have : (fun j : ℤ => p j * Z j) = fun j => a j / P.β := by
      funext j; simp only [ha]; field_simp
    rw [this]; exact hsa.div_const _
  -- balance equation in flux form
  have hbal' : ∀ j' : ℤ, b (j' + 1) + a (j' - 1) = b j' + a j' := by
    intro j'
    have h := hbal j'
    have hfun : (fun j => p j * artRate P r j j') =
        fun j => (if j = j' + 1 then b (j' + 1) else 0) + (if j = j' - 1 then a (j' - 1) else 0) := by
      funext j
      simp only [artRate, mul_add]
      congr 1
      · by_cases h1 : j = j' + 1
        · subst h1; simp [hb]
        · have : ¬ j' = j - 1 := by omega
          simp [h1, this]
      · by_cases h1 : j = j' - 1
        · subst h1; simp [ha, hZ]
        · have : ¬ j' = j + 1 := by omega
          simp [h1, this]
    rw [hfun, Summable.tsum_add (summable_of_ne_finset_zero (s := {j' + 1}) (by intro j hj; simp_all))
      (summable_of_ne_finset_zero (s := {j' - 1}) (by intro j hj; simp_all)),
      tsum_ite_eq, tsum_ite_eq] at h
    rw [h]; simp only [ha, hb, artExitRate, hZ]; ring
  -- φ j = a j - b (j+1) is constant
  set φ : ℤ → ℝ := fun j => a j - b (j + 1) with hφ
  have hstep : ∀ j : ℤ, φ j = φ (j - 1) := by
    intro j
    have := hbal' j
    simp only [hφ, sub_add_cancel]; linarith
  have hconst : ∀ j : ℤ, φ j = φ 0 := by
    intro j
    induction j using Int.induction_on with
    | zero => rfl
    | succ k ih => rw [hstep (k + 1)]; simpa using ih
    | pred k ih => have := hstep (-(k:ℤ)); linarith
  have hsb1 : Summable (fun j : ℤ => b (j + 1)) :=
    (Equiv.addRight (1 : ℤ)).summable_iff.mpr (hsum.mul_right r)
  have hsφ : Summable φ := hsa.sub hsb1
  have hφ0 : φ 0 = 0 := by
    have : Summable (fun _ : ℤ => φ 0) := by
      have : φ = fun _ => φ 0 := funext hconst
      rwa [this] at hsφ
    exact (summable_const_iff (φ 0)).mp this
  have hab : ∀ j, a j = b (j + 1) := by
    intro j; have := hconst j; rw [hφ0] at this; simp only [hφ] at this; linarith
  exact hab

lemma orderStep_ge (P : Params) (r : ℝ) (y : ℤ) (z : ℕ) :
    ⌈truncTarget P r y⌉ ≤ ((orderStep P r y z : ℕ) : ℤ) := by
  simp only [orderStep]
  rw [Int.ceil_sub_natCast]
  have h := Int.self_le_toNat (⌈truncTarget P r y⌉ - (z : ℤ))
  push_cast
  omega

/-- A stationary distribution vanishes on states with `Z < ⌈T(Y)⌉` (they are never entered). -/
lemma support (P : Params) (r : ℝ) (hr : 0 < r) (hβ : 0 < P.β) (p : State → ℝ)
    (hp : IsStationary P r p) (s : State) (hs : ((s.2 : ℕ) : ℤ) < ⌈truncTarget P r s.1⌉) :
    p s = 0 := by
  have hb := hp.2.2.2.2 s
  have h0 : ∀ s0 : State, p s0 * rate P r s0 s = 0 := by
    intro s0
    have : rate P r s0 s = 0 := by
      unfold rate
      rw [if_neg, if_neg]
      · simp
      · rintro ⟨-, h⟩
        have := orderStep_ge P r (s0.1 + 1) (s0.2 - 1)
        rw [h] at hs
        simp only [afterItem] at hs
        omega
      · intro h
        have := orderStep_ge P r (s0.1 - 1) s0.2
        rw [h] at hs
        simp only [afterCustomer] at hs
        omega
    rw [this, mul_zero]
  simp only [h0, tsum_zero] at hb
  have hpos : 0 < exitRate P r s := by
    unfold exitRate; positivity
  rcases mul_eq_zero.mp hb.symm with h | h
  · exact h
  · linarith



lemma T_anti (P : Params) (r : ℝ) {y₁ y₂ : ℤ} (h : y₁ ≤ y₂) :
    truncTarget P r y₂ ≤ truncTarget P r y₁ := by
  unfold truncTarget target
  have : (P.γ : ℝ) * ((y₂ : ℝ) - P.xs r) ≥ (P.γ : ℝ) * ((y₁ : ℝ) - P.xs r) := by
    apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
    have : (y₁ : ℝ) ≤ y₂ := by exact_mod_cast h
    linarith
  apply max_le_max _ le_rfl
  apply min_le_min _ le_rfl
  linarith

/-- Summing an observable of `Y` against a law on `ℤ × ℕ`. -/
lemma level_ite (p : State → ℝ) (hs : Summable p) (hnn : ∀ s, 0 ≤ p s) (c : ℤ → Prop)
    [DecidablePred c] :
    ∑' s : State, (if c s.1 then p s else 0) = ∑' y : ℤ, (if c y then ∑' z : ℕ, p (y, z) else 0) := by
  have hs' : Summable (fun s : State => if c s.1 then p s else 0) :=
    Summable.of_nonneg_of_le (fun s => by split_ifs; exact hnn s; exact le_rfl)
      (fun s => by split_ifs; exact le_rfl; exact hnn s) hs
  rw [Summable.tsum_prod hs']
  congr 1; funext y
  split_ifs with h <;> simp [h]

lemma ind_summable {ι : Type*} (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (hs : Summable w)
    (c : ι → Prop) [DecidablePred c] : Summable (fun i => if c i then w i else 0) :=
  Summable.of_nonneg_of_le (fun i => by split_ifs; exact hw i; exact le_rfl)
    (fun i => by split_ifs; exact le_rfl; exact hw i) hs

/-- Likelihood-ratio order implies stochastic order, for laws `m`, `q` on `ℤ` with
`q(k+1) = a(k) q(k)` and `m(k+1) ≥ a(k) m(k)`, `a ≥ 0`. -/
lemma lr_stoch (m q a : ℤ → ℝ) (hm0 : ∀ j, 0 ≤ m j) (hms : Summable m) (hm1 : ∑' j, m j = 1)
    (hq0 : ∀ j, 0 ≤ q j) (hqs : Summable q) (hq1 : ∑' j, q j = 1) (ha0 : ∀ j, 0 ≤ a j)
    (hq : ∀ k, q (k + 1) = a k * q k) (hm : ∀ k, a k * m k ≤ m (k + 1)) (k : ℤ) :
    ∑' j : ℤ, (if k < j then q j else 0) ≤ ∑' j : ℤ, (if k < j then m j else 0) := by
  -- (L1) m k q j ≤ m j q k for j ≥ k
  have L1 : ∀ j, k ≤ j → m k * q j ≤ m j * q k := by
    intro j hj
    induction j, hj using Int.le_induction with
    | base => exact le_of_eq (by ring)
    | succ j hkj ih =>
      rw [hq j]
      have h1 := mul_le_mul_of_nonneg_left ih (ha0 j)
      have h2 := mul_le_mul_of_nonneg_right (hm j) (hq0 k)
      nlinarith
  by_cases hqk : q k = 0
  · have hz : ∀ j, k ≤ j → q j = 0 := by
      intro j hj
      induction j, hj using Int.le_induction with
      | base => exact hqk
      | succ j hkj ih => rw [hq j, ih, mul_zero]
    have : ∑' j : ℤ, (if k < j then q j else 0) = 0 := by
      have : (fun j : ℤ => if k < j then q j else 0) = fun _ => 0 := by
        funext j; split_ifs with h
        · exact hz j h.le
        · rfl
      rw [this, tsum_zero]
    rw [this]
    exact tsum_nonneg (fun j => by split_ifs; exact hm0 j; exact le_rfl)
  have hqkpos : 0 < q k := lt_of_le_of_ne (hq0 k) (Ne.symm hqk)
  -- downward positivity
  have hdown : ∀ j, j ≤ k → 0 < q j := by
    intro j hj
    induction j, hj using Int.leInductionDown with
    | base => exact hqkpos
    | pred j hjk ih =>
      have := hq (j - 1)
      rw [sub_add_cancel] at this
      rw [this] at ih
      by_contra hneg
      have : q (j - 1) = 0 := le_antisymm (not_lt.mp hneg) (hq0 _)
      rw [this, mul_zero] at ih
      exact lt_irrefl _ ih
  -- (L2) m j q k ≤ m k q j for j ≤ k
  have L2 : ∀ j, j ≤ k → m j * q k ≤ m k * q j := by
    intro j hj
    induction j, hj using Int.leInductionDown with
    | base => exact le_of_eq (by ring)
    | pred j hjk ih =>
      have e := hq (j - 1)
      rw [sub_add_cancel] at e
      have hqj := hdown j hjk
      have hqj1 := hdown (j - 1) (by omega)
      have hapos : 0 < a (j - 1) := by
        rw [e] at hqj
        exact pos_of_mul_pos_left hqj (hq0 _)
      have hmj := hm (j - 1)
      rw [sub_add_cancel] at hmj
      have h1 : a (j - 1) * (m (j - 1) * q k) ≤ a (j - 1) * (m k * q (j - 1)) := by
        have := mul_le_mul_of_nonneg_right hmj (hq0 k)
        rw [e] at ih
        nlinarith
      exact le_of_mul_le_mul_left h1 hapos
  set Mp := ∑' j : ℤ, (if k < j then m j else 0) with hMp
  set Mn := ∑' j : ℤ, (if ¬ k < j then m j else 0) with hMn
  set Qp := ∑' j : ℤ, (if k < j then q j else 0) with hQp
  set Qn := ∑' j : ℤ, (if ¬ k < j then q j else 0) with hQn
  have hsum_m : Mp + Mn = 1 := by
    rw [hMp, hMn, ← Summable.tsum_add (ind_summable m hm0 hms _) (ind_summable m hm0 hms _), ← hm1]
    congr 1; funext j; split_ifs <;> simp
  have hsum_q : Qp + Qn = 1 := by
    rw [hQp, hQn, ← Summable.tsum_add (ind_summable q hq0 hqs _) (ind_summable q hq0 hqs _), ← hq1]
    congr 1; funext j; split_ifs <;> simp
  have hQp0 : 0 ≤ Qp := tsum_nonneg (fun j => by split_ifs <;> first | exact hq0 j | exact le_rfl)
  have hQn0 : 0 ≤ Qn := tsum_nonneg (fun j => by split_ifs <;> first | exact hq0 j | exact le_rfl)
  have hP1 : m k * Qp ≤ q k * Mp := by
    rw [hQp, hMp, ← tsum_mul_left, ← tsum_mul_left]
    refine Summable.tsum_le_tsum (fun j => ?_) ((ind_summable q hq0 hqs _).mul_left _)
      ((ind_summable m hm0 hms _).mul_left _)
    split_ifs with h
    · have := L1 j h.le; linarith
    · simp
  have hP2 : q k * Mn ≤ m k * Qn := by
    rw [hQn, hMn, ← tsum_mul_left, ← tsum_mul_left]
    refine Summable.tsum_le_tsum (fun j => ?_) ((ind_summable m hm0 hms _).mul_left _)
      ((ind_summable q hq0 hqs _).mul_left _)
    by_cases h : k < j
    · rw [if_neg (not_not.mpr h), if_neg (not_not.mpr h)]; simp
    · rw [if_pos h, if_pos h]; have := L2 j (not_lt.mp h); linarith
  rcases le_total (m k) (q k) with h | h
  · have : q k * Mn ≤ q k * Qn := le_trans hP2 (mul_le_mul_of_nonneg_right h hQn0)
    have := le_of_mul_le_mul_left this hqkpos
    linarith
  · have : q k * Qp ≤ q k * Mp := le_trans (mul_le_mul_of_nonneg_right h hQp0) hP1
    exact le_of_mul_le_mul_left this hqkpos

end GBSLemma8

open GBSLemma8

theorem solution (P : Params) (hP : P.Standing) (r : ℝ) (hr : 0 < r)
    (p : State → ℝ) (hp : IsStationary P r p) (q : ℤ → ℝ) (hq : IsArtStationary P r q) :
    (∀ x : ℝ, ∑' j : ℤ, (if x < (j : ℝ) then q j else 0) ≤
      ∑' s : State, (if x < (s.1 : ℝ) then p s else 0)) ∧
    (∀ x : ℝ, ∑' s : State, (if x < truncTarget P r s.1 then p s else 0) ≤
      ∑' j : ℤ, (if x < truncTarget P r j then q j else 0)) := by
  obtain ⟨hβ, -, -, -, -⟩ := hP
  have hp' := hp
  have hq' := hq
  obtain ⟨hpn, hps, hp1, -, -⟩ := hp'
  obtain ⟨hqn, hqs, hq1, -, -⟩ := hq'
  obtain ⟨hsZ, hcut⟩ := cut_eq P r hr hβ p hp
  have hacut := art_cut P r hβ q hq
  set m : ℤ → ℝ := fun y => ∑' z : ℕ, p (y, z) with hmdef
  set a : ℤ → ℝ := fun j => P.β * (artZ P r j : ℝ) / r with hadef
  have hm0 : ∀ j, 0 ≤ m j := fun j => tsum_nonneg (fun z => hpn _)
  have hms : Summable m := ((summable_prod_of_nonneg (fun s => hpn s)).mp hps).2
  have hm1 : ∑' j, m j = 1 := by rw [← hp1, Summable.tsum_prod hps]
  have ha0 : ∀ j, 0 ≤ a j := fun j => by simp only [hadef]; positivity
  have hqrec : ∀ k, q (k + 1) = a k * q k := by
    intro k
    have := hacut k
    simp only [hadef]
    field_simp
    linarith
  have hmrec : ∀ k, a k * m k ≤ m (k + 1) := by
    intro k
    have hc := hcut k
    -- E[Z; Y = k] ≥ ⌈T(k)⌉ P(Y = k)
    have hrow : Summable (fun z : ℕ => p (k, z)) := hps.prod_factor k
    have hrowz : Summable (fun z : ℕ => p (k, z) * (z : ℝ)) := hsZ.prod_factor k
    have hge : (artZ P r k : ℝ) * m k ≤ ∑' z : ℕ, p (k, z) * (z : ℝ) := by
      simp only [hmdef]
      rw [← tsum_mul_left]
      refine Summable.tsum_le_tsum (fun z => ?_) (hrow.mul_left _) hrowz
      by_cases hz : ((z : ℕ) : ℤ) < ⌈truncTarget P r k⌉
      · rw [support P r hr hβ p hp (k, z) hz]; simp
      · push Not at hz
        have h0 : 0 ≤ truncTarget P r k := le_max_right _ _
        have : (artZ P r k : ℝ) ≤ (z : ℝ) := by
          simp only [artZ]
          have : ((⌈truncTarget P r k⌉₊ : ℕ) : ℤ) ≤ (z : ℤ) := by
            rw [Int.natCast_ceil_eq_ceil h0]; exact hz
          exact_mod_cast this
        have := mul_le_mul_of_nonneg_left this (hpn (k, z))
        linarith
    simp only [hadef]
    rw [div_mul_eq_mul_div, div_le_iff₀ hr]
    have := mul_le_mul_of_nonneg_left hge hβ.le
    simp only [hmdef] at hc ⊢
    nlinarith
  have part29 : ∀ x : ℝ, ∑' j : ℤ, (if x < (j : ℝ) then q j else 0) ≤
      ∑' s : State, (if x < (s.1 : ℝ) then p s else 0) := by
    intro x
    have e : ∀ j : ℤ, (x < (j : ℝ)) = (⌊x⌋ < j) := fun j => propext Int.floor_lt.symm
    simp only [e]
    rw [level_ite p hps hpn (fun y => ⌊x⌋ < y)]
    exact lr_stoch m q a hm0 hms hm1 hqn hqs hq1 ha0 hqrec hmrec ⌊x⌋
  refine ⟨part29, ?_⟩
  intro x
  by_cases hall : ∀ y : ℤ, x < truncTarget P r y
  · simp only [hall, if_true, hp1, hq1, le_refl]
  by_cases hnone : ∀ y : ℤ, ¬ x < truncTarget P r y
  · simp only [hnone, if_false, tsum_zero, le_refl]
  push Not at hall hnone
  obtain ⟨y₂, hy₂⟩ := hall
  have hbdd : ∃ b : ℤ, ∀ z : ℤ, x < truncTarget P r z → z ≤ b := by
    refine ⟨y₂, fun z hz => ?_⟩
    by_contra h
    push Not at h
    have := T_anti P r h.le
    linarith
  obtain ⟨y₀, hy₀, hmax⟩ := Int.exists_greatest_of_bdd hbdd hnone
  have hiff : ∀ y : ℤ, (x < truncTarget P r y) ↔ ¬ ((y₀ : ℝ) < (y : ℝ)) := by
    intro y
    constructor
    · intro h h'
      have := hmax y h
      have : (y : ℝ) ≤ y₀ := by exact_mod_cast this
      linarith
    · intro h
      push Not at h
      have : y ≤ y₀ := by exact_mod_cast h
      exact lt_of_lt_of_le hy₀ (T_anti P r this)
  have cp : ∀ s : State, (if x < truncTarget P r s.1 then p s else 0) =
      p s - (if (y₀ : ℝ) < (s.1 : ℝ) then p s else 0) := by
    intro s; by_cases h : (y₀ : ℝ) < (s.1 : ℝ)
    · rw [if_neg ((not_congr (hiff s.1)).mpr (not_not.mpr h)), if_pos h]; ring
    · rw [if_pos ((hiff s.1).mpr h), if_neg h]; ring
  have cq : ∀ j : ℤ, (if x < truncTarget P r j then q j else 0) =
      q j - (if (y₀ : ℝ) < (j : ℝ) then q j else 0) := by
    intro j; by_cases h : (y₀ : ℝ) < (j : ℝ)
    · rw [if_neg ((not_congr (hiff j)).mpr (not_not.mpr h)), if_pos h]; ring
    · rw [if_pos ((hiff j).mpr h), if_neg h]; ring
  rw [tsum_congr cp, tsum_congr cq, Summable.tsum_sub hps (ind_summable p hpn hps _),
    Summable.tsum_sub hqs (ind_summable q hqn hqs _), hp1, hq1]
  have := part29 (y₀ : ℝ)
  linarith
