-- Prove2me | solution 1 for SampleMechDesign.pdim_l1_packing
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-06T15:58:24.423855+00:00
-- url     : https://prove2.me/submissions/25a67e9a-6075-47f0-998f-1c59a6a1fbb6

import Mathlib
import Definitions.Def_FoundationsML_Regression_Shatters

set_option autoImplicit false

open FoundationsML.Regression Finset

namespace SampleMechDesign.PackingAux

/-- `∑_{k ≤ d} C(m,k) ≤ (e m / d)^d` for `1 ≤ d ≤ m`. -/
lemma sum_choose_le (m d : ℕ) (hd : 1 ≤ d) (hdm : d ≤ m) :
    ((∑ k ∈ Iic d, m.choose k : ℕ) : ℝ) ≤ (Real.exp 1 * m / d) ^ d := by
  have hm : (0:ℝ) < m := by exact_mod_cast (lt_of_lt_of_le hd hdm)
  have hd' : (0:ℝ) < d := by exact_mod_cast hd
  set q : ℝ := (d:ℝ) / m with hq
  have hq0 : 0 < q := div_pos hd' hm
  have hq1 : q ≤ 1 := (div_le_one hm).2 (by exact_mod_cast hdm)
  set S : ℝ := ((∑ k ∈ Iic d, m.choose k : ℕ) : ℝ) with hS
  have h1 : S * q ^ d ≤ ∑ k ∈ range (m+1), (m.choose k : ℝ) * q ^ k := by
    rw [hS]; push_cast
    rw [Finset.sum_mul]
    calc ∑ k ∈ Iic d, (m.choose k : ℝ) * q ^ d ≤ ∑ k ∈ Iic d, (m.choose k : ℝ) * q ^ k := by
          apply Finset.sum_le_sum; intro k hk
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact pow_le_pow_of_le_one hq0.le hq1 (Finset.mem_Iic.1 hk)
      _ ≤ ∑ k ∈ range (m+1), (m.choose k : ℝ) * q ^ k := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro k hk; simp only [Finset.mem_Iic] at hk; simp only [Finset.mem_range]; omega
          · intro k _ _; positivity
  have h2 : ∑ k ∈ range (m+1), (m.choose k : ℝ) * q ^ k = (1 + q) ^ m := by
    rw [add_comm (1:ℝ) q, add_pow]; apply Finset.sum_congr rfl; intro k _; rw [one_pow]; ring
  have h3 : (1 + q) ^ m ≤ Real.exp 1 ^ d := by
    have e1 : 1 + q ≤ Real.exp q := by linarith [Real.add_one_le_exp q]
    calc (1 + q) ^ m ≤ Real.exp q ^ m := pow_le_pow_left₀ (by linarith) e1 m
      _ = Real.exp (m * q) := (Real.exp_nat_mul q m).symm
      _ = Real.exp 1 ^ d := by
          rw [Real.exp_one_pow]; congr 1; rw [hq]; field_simp
  have key : S * q ^ d ≤ Real.exp 1 ^ d := by linarith
  have hqm : q * ((m:ℝ) / d) = 1 := by rw [hq]; field_simp
  calc S = S * (q * ((m:ℝ) / d)) ^ d := by rw [hqm, one_pow, mul_one]
    _ = (S * q ^ d) * ((m:ℝ) / d) ^ d := by rw [mul_pow]; ring
    _ ≤ Real.exp 1 ^ d * ((m:ℝ) / d) ^ d :=
        mul_le_mul_of_nonneg_right key (by positivity)
    _ = (Real.exp 1 * m / d) ^ d := by rw [← mul_pow, mul_div_assoc]

/-- Probabilistic method by counting: if the bad tuples of all constraints are fewer than all
tuples, some tuple meets every constraint. -/
lemma exists_good_tuple {T ι : Type*} [Fintype T] [DecidableEq T] (Q : Finset ι)
    (Bad : ι → Finset T) (m : ℕ)
    (h : ∑ q ∈ Q, (#(Bad q)) ^ m < (Fintype.card T) ^ m) :
    ∃ w : Fin m → T, ∀ q ∈ Q, ∃ j, w j ∉ Bad q := by
  classical
  by_contra hne
  push_neg at hne
  have hsub : (Finset.univ : Finset (Fin m → T)) ⊆
      Q.biUnion (fun q => Fintype.piFinset (fun _ : Fin m => Bad q)) := by
    intro w _
    obtain ⟨q, hq, hw⟩ := hne w
    exact Finset.mem_biUnion.2 ⟨q, hq, Fintype.mem_piFinset.2 hw⟩
  have hc := (Finset.card_le_card hsub).trans Finset.card_biUnion_le
  simp only [Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_piFinset,
    Finset.prod_const] at hc
  omega

/-- Grid count: at least `L (hi - lo)/B - 1` of the thresholds `r B / L`, `r < L`, lie in `[lo, hi)`. -/
lemma grid_count (L : ℕ) (hL : 0 < L) {B lo hi : ℝ} (hB : 0 < B) (hlo : 0 ≤ lo)
    (hhi : hi ≤ B) :
    (L * (hi - lo) / B - 1 : ℝ) ≤
      (#((Finset.univ : Finset (Fin L)).filter
        (fun r : Fin L => lo ≤ (r.val : ℝ) * B / L ∧ (r.val : ℝ) * B / L < hi)) : ℝ) := by
  have hL' : (0:ℝ) < L := by exact_mod_cast hL
  set a := ⌈(L:ℝ) * lo / B⌉₊
  set b := ⌈(L:ℝ) * hi / B⌉₊
  have hbL : b ≤ L := by
    apply Nat.ceil_le.2
    rw [div_le_iff₀ hB]; nlinarith
  have hsub : (Finset.Ico a b).card ≤ #((Finset.univ : Finset (Fin L)).filter
        (fun r : Fin L => lo ≤ (r.val : ℝ) * B / L ∧ (r.val : ℝ) * B / L < hi)) := by
    apply Finset.card_le_card_of_injOn (fun r => (⟨r % L, Nat.mod_lt _ hL⟩ : Fin L))
    · intro r hr
      have hr' := Finset.mem_Ico.1 hr
      have hrL : r < L := lt_of_lt_of_le hr'.2 hbL
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq,
        Nat.mod_eq_of_lt hrL]
      have h1 : (L:ℝ) * lo / B ≤ r := Nat.ceil_le.1 hr'.1
      have h2 : (r:ℝ) < L * hi / B := Nat.lt_ceil.1 hr'.2
      constructor
      · rw [le_div_iff₀ hL']; rw [div_le_iff₀ hB] at h1; linarith
      · rw [div_lt_iff₀ hL']; rw [lt_div_iff₀ hB] at h2; linarith
    · intro r hr s hs hrs
      have hrL : r < L := lt_of_lt_of_le (Finset.mem_Ico.1 hr).2 hbL
      have hsL : s < L := lt_of_lt_of_le (Finset.mem_Ico.1 hs).2 hbL
      have := congrArg Fin.val hrs
      simp only [Nat.mod_eq_of_lt hrL, Nat.mod_eq_of_lt hsL] at this
      exact this
  rw [Nat.card_Ico] at hsub
  have ha : (a:ℝ) < L * lo / B + 1 := Nat.ceil_lt_add_one (by positivity)
  have hb : (L:ℝ) * hi / B ≤ b := Nat.le_ceil _
  have hcast : (b:ℝ) - a ≤ ((b - a : ℕ) : ℝ) := by
    rcases le_total a b with h | h
    · rw [Nat.cast_sub h]
    · have : (b:ℝ) ≤ a := by exact_mod_cast h
      have : (0:ℝ) ≤ ((b - a : ℕ) : ℝ) := Nat.cast_nonneg _
      linarith
  have hsub' := (Nat.cast_le (α := ℝ)).2 hsub
  have : (L:ℝ) * (hi - lo) / B = L * hi / B - L * lo / B := by ring
  linarith

/-- The analytic step: from Sauer's bound and the sample size, `log M ≤ 2 D log(5 e x)`. -/
lemma log_bound {M x : ℝ} {D m : ℕ} (hM : 0 < M) (hD : 1 ≤ D) (hx : 1 ≤ x)
    (hDm : D ≤ m) (hm : (m:ℝ) ≤ 4 * x * Real.log M + 1)
    (hSauer : M ≤ (Real.exp 1 * m / D) ^ D) :
    Real.log M ≤ 2 * D * Real.log (5 * Real.exp 1 * x) := by
  have hD' : (0:ℝ) < D := by exact_mod_cast hD
  have hm0 : (0:ℝ) < m := by exact_mod_cast (lt_of_lt_of_le hD hDm)
  have hl5 : Real.log (5 * Real.exp 1 * x) = 1 + Real.log (5 * x) := by
    rw [show 5 * Real.exp 1 * x = Real.exp 1 * (5 * x) by ring, Real.log_mul (by positivity)
      (by positivity), Real.log_exp]
  have h5x : 0 ≤ Real.log (5 * x) := Real.log_nonneg (by linarith)
  have hlogM : Real.log M ≤ D * (1 + Real.log (m / D)) := by
    have := Real.log_le_log hM hSauer
    rw [Real.log_pow, show Real.exp 1 * m / D = Real.exp 1 * (m / D) by ring,
      Real.log_mul (by positivity) (by positivity), Real.log_exp] at this
    exact this
  set y := Real.log M / D with hy
  have hyD : Real.log M = D * y := by rw [hy]; field_simp
  rcases le_or_gt y 1 with hy1 | hy1
  · rw [hl5, hyD]; nlinarith
  · have hmD : (m:ℝ) / D ≤ 5 * x * y := by
      rw [div_le_iff₀ hD']
      have : (m:ℝ) ≤ 4 * x * (D * y) + 1 := by rw [← hyD]; exact hm
      have hD1 : (1:ℝ) ≤ D := by exact_mod_cast hD
      have hxy : (1:ℝ) ≤ x * y := by nlinarith
      have hxyD : (1:ℝ) ≤ x * y * D := by nlinarith
      linarith
    have hlog1 : Real.log (m / D) ≤ Real.log (5 * x) + Real.log y := by
      rw [← Real.log_mul (by positivity) (by positivity)]
      exact Real.log_le_log (by positivity) hmD
    have hlogy : Real.log y ≤ y / 2 := by
      have := Real.log_le_sub_one_of_pos (show 0 < y / 2 by positivity)
      rw [Real.log_div (by positivity) (by norm_num)] at this
      have h2 : Real.log 2 < 1 := by
        have := Real.log_two_lt_d9; linarith
      linarith
    have : y ≤ 1 + Real.log (5 * x) + y / 2 := by
      have h' : D * y ≤ D * (1 + Real.log (m / D)) := by rw [← hyD]; exact hlogM
      have h'' : y ≤ 1 + Real.log (m / D) := le_of_mul_le_mul_left h' hD'
      linarith
    rw [hl5, hyD]; nlinarith

end SampleMechDesign.PackingAux

namespace SampleMechDesign.PackingAux

/-- Bad thresholds of one pair: few, when the pair is `ε`-separated in normalized `L¹`. -/
lemma card_bad_le {X : Type*} {B : ℝ} {N L : ℕ} (hL : 0 < L) (hB : 0 < B) (S : Fin N → X)
    (f g : X → ℝ) (hf : ∀ i, f (S i) ∈ Set.Icc 0 B) (hg : ∀ i, g (S i) ∈ Set.Icc 0 B) :
    (#((Finset.univ : Finset (Fin N × Fin L)).filter (fun p =>
        ((p.2.val : ℝ) * B / L < f (S p.1) ↔ (p.2.val : ℝ) * B / L < g (S p.1)))) : ℝ) ≤
      N * (L + 1) - L / B * ∑ i, |f (S i) - g (S i)| := by
  classical
  have hsplit : #((Finset.univ : Finset (Fin N × Fin L)).filter (fun p =>
        ((p.2.val : ℝ) * B / L < f (S p.1) ↔ (p.2.val : ℝ) * B / L < g (S p.1)))) =
      ∑ i : Fin N, #((Finset.univ : Finset (Fin L)).filter (fun r =>
        ((r.val : ℝ) * B / L < f (S i) ↔ (r.val : ℝ) * B / L < g (S i)))) := by
    simp only [Finset.card_filter, Fintype.sum_prod_type]
  rw [hsplit]; push_cast
  have hper : ∀ i : Fin N, (#((Finset.univ : Finset (Fin L)).filter (fun r =>
        ((r.val : ℝ) * B / L < f (S i) ↔ (r.val : ℝ) * B / L < g (S i)))) : ℝ) ≤
      (L + 1) - L / B * |f (S i) - g (S i)| := by
    intro i
    set a := f (S i)
    set b := g (S i)
    have hcard := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin L)))
      (p := fun r : Fin L => ((r.val : ℝ) * B / L < a ↔ (r.val : ℝ) * B / L < b))
    simp only [Finset.card_univ, Fintype.card_fin] at hcard
    have hcard' : (#((Finset.univ : Finset (Fin L)).filter (fun r =>
        ((r.val : ℝ) * B / L < a ↔ (r.val : ℝ) * B / L < b))) : ℝ) +
        #((Finset.univ : Finset (Fin L)).filter (fun r =>
        ¬((r.val : ℝ) * B / L < a ↔ (r.val : ℝ) * B / L < b))) = L := by exact_mod_cast hcard
    have hmono : #((Finset.univ : Finset (Fin L)).filter
        (fun r : Fin L => min a b ≤ (r.val : ℝ) * B / L ∧ (r.val : ℝ) * B / L < max a b)) ≤
        #((Finset.univ : Finset (Fin L)).filter (fun r =>
        ¬((r.val : ℝ) * B / L < a ↔ (r.val : ℝ) * B / L < b))) := by
      apply Finset.card_le_card
      intro r
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rintro ⟨h1, h2⟩
      rcases le_total a b with hab | hab
      · rw [min_eq_left hab] at h1; rw [max_eq_right hab] at h2
        intro hiff; have := hiff.2 h2; linarith
      · rw [min_eq_right hab] at h1; rw [max_eq_left hab] at h2
        intro hiff; have := hiff.1 h2; linarith
    have hgrid := grid_count L hL hB (lo := min a b) (hi := max a b)
      (le_min (hf i).1 (hg i).1) (max_le (hf i).2 (hg i).2)
    have hmono' := (Nat.cast_le (α := ℝ)).2 hmono
    have habs : max a b - min a b = |a - b| := by
      rcases le_total a b with hab | hab
      · rw [max_eq_right hab, min_eq_left hab, abs_of_nonpos (by linarith)]; ring
      · rw [max_eq_left hab, min_eq_right hab, abs_of_nonneg (by linarith)]
    have : (L:ℝ) * |a - b| / B = L / B * |a - b| := by ring
    rw [habs] at hgrid
    linarith
  calc ∑ i : Fin N, (#((Finset.univ : Finset (Fin L)).filter (fun r =>
        ((r.val : ℝ) * B / L < f (S i) ↔ (r.val : ℝ) * B / L < g (S i)))) : ℝ)
      ≤ ∑ i : Fin N, ((L + 1) - L / B * |f (S i) - g (S i)|) := Finset.sum_le_sum (fun i _ => hper i)
    _ = N * (L + 1) - L / B * ∑ i, |f (S i) - g (S i)| := by
        rw [Finset.sum_sub_distrib, ← Finset.mul_sum]; simp; ring

end SampleMechDesign.PackingAux

open SampleMechDesign.PackingAux in
/-- **Pollard–Haussler packing bound** for a class of pseudo-dimension at most `d`. -/
theorem solution {X : Type*} {G : Set (X → ℝ)} {d : ℕ}
    (hd : ∀ (m : ℕ) (z : Fin m → X), Shatters G z → m ≤ d)
    {B : ℝ} {N : ℕ} (S : Fin N → X) (hB : ∀ g ∈ G, ∀ i, g (S i) ∈ Set.Icc 0 B)
    {ε : ℝ} (hε : 0 < ε) (hεB : ε ≤ B)
    (P : Finset (X → ℝ)) (hP : ∀ f ∈ P, f ∈ G)
    (hsep : ∀ f ∈ P, ∀ g ∈ P, f ≠ g → ε < (1 / (N : ℝ)) * ∑ i, |f (S i) - g (S i)|) :
    Real.log (P.card : ℝ) ≤ 2 * d * Real.log (5 * Real.exp 1 * B / ε) := by
  classical
  have hB0 : 0 < B := lt_of_lt_of_le hε hεB
  set x : ℝ := B / ε with hx
  have hx1 : 1 ≤ x := (one_le_div hε).2 hεB
  have hx0 : 0 < x := by linarith
  have h5ex : 5 * Real.exp 1 * B / ε = 5 * Real.exp 1 * x := by rw [hx]; ring
  have hrhs : 0 ≤ Real.log (5 * Real.exp 1 * B / ε) := Real.log_nonneg (by
      rw [h5ex]; have := Real.add_one_le_exp 1; nlinarith)
  have hd0 : (0:ℝ) ≤ 2 * d * Real.log (5 * Real.exp 1 * B / ε) := by positivity
  set M := P.card with hM
  rcases Nat.lt_or_ge M 2 with hM2 | hM2
  · have : Real.log (M:ℝ) ≤ 0 := by interval_cases M <;> simp
    linarith
  have hM0 : (0:ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  -- a separated pair forces `N ≥ 1`
  obtain ⟨f0, hf0, g0, hg0, hfg0⟩ := Finset.one_lt_card.1 (show 1 < P.card by omega)
  have hN : 0 < N := by
    rcases Nat.eq_zero_or_pos N with h | h
    · exfalso; have := hsep f0 hf0 g0 hg0 hfg0; subst h; simp at this; linarith
    · exact h
  have hN' : (0:ℝ) < N := by exact_mod_cast hN
  set L : ℕ := ⌈2 * x⌉₊ with hLdef
  have hL2x : 2 * x ≤ L := Nat.le_ceil _
  have hL : 0 < L := by exact_mod_cast (show (0:ℝ) < L by linarith)
  have hL' : (0:ℝ) < L := by exact_mod_cast hL
  let t : Fin L → ℝ := fun r => (r.val : ℝ) * B / L
  let Bad : (X → ℝ) × (X → ℝ) → Finset (Fin N × Fin L) := fun q =>
    (Finset.univ : Finset (Fin N × Fin L)).filter (fun p =>
      ((p.2.val : ℝ) * B / L < q.1 (S p.1) ↔ (p.2.val : ℝ) * B / L < q.2 (S p.1)))
  set p : ℝ := 1 / (2 * x) with hp
  have hp0 : 0 < p := by positivity
  have hbad : ∀ q ∈ P.offDiag, (#(Bad q) : ℝ) ≤ (1 - p) * (N * L) := by
    intro q hq
    obtain ⟨hq1, hq2, hq12⟩ := Finset.mem_offDiag.1 hq
    have h1 := card_bad_le hL hB0 S q.1 q.2 (hB _ (hP _ hq1)) (hB _ (hP _ hq2))
    have h2 := hsep _ hq1 _ hq2 hq12
    have h3 : N * ε < ∑ i, |q.1 (S i) - q.2 (S i)| := by
      rw [one_div, ← div_eq_inv_mul, lt_div_iff₀ hN'] at h2; linarith
    have h4 : (L:ℝ) / B * (N * ε) ≤ L / B * ∑ i, |q.1 (S i) - q.2 (S i)| :=
      mul_le_mul_of_nonneg_left h3.le (by positivity)
    have h5 : (L:ℝ) / B * (N * ε) = N * L / x := by rw [hx]; field_simp
    have h6 : (N:ℝ) * L / x - N ≥ N * L * p := by
      rw [hp]
      have : (N:ℝ) * L / x - N - N * L * (1 / (2 * x)) = N / x * (L / 2 - x) := by
        field_simp; ring
      have : (0:ℝ) ≤ N / x * (L / 2 - x) := by
        apply mul_nonneg (by positivity); linarith
      linarith
    show (#(Bad q) : ℝ) ≤ _
    nlinarith
  set m : ℕ := ⌊4 * x * Real.log M⌋₊ + 1 with hmdef
  have hlogM : 0 ≤ Real.log M := Real.log_nonneg (by exact_mod_cast (show 1 ≤ M by omega))
  have hm_lt : 4 * x * Real.log M < m := by
    rw [hmdef]; push_cast; exact Nat.lt_floor_add_one _
  have hm_le : (m:ℝ) ≤ 4 * x * Real.log M + 1 := by
    rw [hmdef]; push_cast; linarith [Nat.floor_le (show 0 ≤ 4 * x * Real.log M by positivity)]
  -- union bound
  have hcount : ∑ q ∈ P.offDiag, (#(Bad q)) ^ m < (Fintype.card (Fin N × Fin L)) ^ m := by
    have hp1 : p ≤ 1 := by rw [hp, div_le_one (by positivity)]; linarith
    have hpow : (1 - p) ^ m < 1 / (M:ℝ) ^ 2 := by
      calc (1 - p) ^ m ≤ Real.exp (-p) ^ m := by
            apply pow_le_pow_left₀ (by linarith); linarith [Real.add_one_le_exp (-p)]
        _ = Real.exp (-(p * m)) := by rw [← Real.exp_nat_mul]; ring_nf
        _ < Real.exp (-(2 * Real.log M)) := by
            apply Real.exp_lt_exp.2
            have : p * (4 * x * Real.log M) = 2 * Real.log M := by rw [hp]; field_simp; ring
            have : p * (4 * x * Real.log M) < p * m := mul_lt_mul_of_pos_left hm_lt hp0
            linarith
        _ = 1 / (M:ℝ) ^ 2 := by
            rw [show -(2 * Real.log M) = - Real.log (M ^ 2) by rw [Real.log_pow]; push_cast; ring,
              Real.exp_neg, Real.exp_log (by positivity), one_div]
    have hR : (∑ q ∈ P.offDiag, (#(Bad q) : ℝ) ^ m) < ((N * L : ℕ) : ℝ) ^ m := by
      calc (∑ q ∈ P.offDiag, (#(Bad q) : ℝ) ^ m)
          ≤ ∑ q ∈ P.offDiag, ((1 - p) * (N * L)) ^ m := by
            apply Finset.sum_le_sum; intro q hq
            exact pow_le_pow_left₀ (Nat.cast_nonneg _) (hbad q hq) m
        _ = (#P.offDiag : ℝ) * ((1 - p) ^ m * ((N:ℝ) * L) ^ m) := by
            rw [Finset.sum_const, nsmul_eq_mul, mul_pow]
        _ ≤ (M:ℝ) ^ 2 * ((1 - p) ^ m * ((N:ℝ) * L) ^ m) := by
            apply mul_le_mul_of_nonneg_right _ (by
              have : 0 ≤ 1 - p := by linarith
              positivity)
            rw [Finset.offDiag_card]
            have : P.card ≤ P.card * P.card := Nat.le_mul_self _
            push_cast [this]; nlinarith
        _ < (M:ℝ) ^ 2 * (1 / (M:ℝ) ^ 2 * ((N:ℝ) * L) ^ m) := by
            apply mul_lt_mul_of_pos_left _ (by positivity)
            exact mul_lt_mul_of_pos_right hpow (by positivity)
        _ = ((N * L : ℕ) : ℝ) ^ m := by push_cast; field_simp
    simp only [Fintype.card_prod, Fintype.card_fin]
    exact_mod_cast hR
  obtain ⟨w, hw⟩ := exists_good_tuple P.offDiag Bad m hcount
  -- the pattern map
  let pat : (X → ℝ) → Finset (Fin m) := fun f =>
    (Finset.univ : Finset (Fin m)).filter (fun j => t (w j).2 < f (S (w j).1))
  have hinj : Set.InjOn pat P := by
    intro f hf g hg hfg
    by_contra hne
    obtain ⟨j, hj⟩ := hw (f, g) (Finset.mem_offDiag.2 ⟨hf, hg, hne⟩)
    apply hj
    simp only [Bad, Finset.mem_filter, Finset.mem_univ, true_and]
    have := congrArg (fun A => j ∈ A) hfg
    simpa [pat, t] using this
  set 𝒜 := P.image pat with h𝒜
  have hcard𝒜 : 𝒜.card = M := Finset.card_image_of_injOn hinj
  have hvc_d : 𝒜.vcDim ≤ d := by
    unfold Finset.vcDim
    apply Finset.sup_le
    intro s hs
    rw [Finset.mem_shatterer] at hs
    let e := s.equivFin
    apply hd s.card (fun i => S (w (e.symm i).1).1)
    refine ⟨fun i => t (w (e.symm i).1).2, fun b => ?_⟩
    let u : Finset (Fin m) := s.filter (fun j => ∃ h : j ∈ s, b (e ⟨j, h⟩) = true)
    obtain ⟨A, hA, hsA⟩ := hs (show u ⊆ s from Finset.filter_subset _ _)
    obtain ⟨f, hf, rfl⟩ := Finset.mem_image.1 hA
    refine ⟨f, hP f hf, ?_⟩
    intro i
    have hmem : (e.symm i).1 ∈ s := (e.symm i).2
    have h1 : (b i = true) ↔ (e.symm i).1 ∈ u := by
      simp only [u, Finset.mem_filter]
      constructor
      · intro hb; exact ⟨hmem, hmem, by simpa using hb⟩
      · rintro ⟨_, h, hb⟩; simpa using hb
    rw [← hsA] at h1
    simpa [Finset.mem_inter, pat, hmem] using h1
  have hvc_m : 𝒜.vcDim ≤ m := by
    unfold Finset.vcDim
    apply Finset.sup_le
    intro s _
    simpa using Finset.card_le_univ s
  have hsauer : M ≤ ∑ k ∈ Iic 𝒜.vcDim, m.choose k := by
    have h1 := Finset.card_le_card_shatterer 𝒜
    have h2 := Finset.card_shatterer_le_sum_vcDim (𝒜 := 𝒜)
    simp only [Fintype.card_fin] at h2
    omega
  set D := 𝒜.vcDim with hD
  rcases Nat.eq_zero_or_pos D with hD0 | hD0
  · have h0 : (Finset.Iic 0 : Finset ℕ) = {0} := by ext k; simp
    rw [hD0, h0, Finset.sum_singleton, Nat.choose_zero_right] at hsauer; omega
  have hS := sum_choose_le m D hD0 hvc_m
  have hS' : (M:ℝ) ≤ (Real.exp 1 * m / D) ^ D :=
    le_trans (by exact_mod_cast hsauer) hS
  have hlb := log_bound hM0 hD0 hx1 hvc_m hm_le hS'
  rw [h5ex]
  have hDd : (D:ℝ) ≤ d := by exact_mod_cast hvc_d
  have hl : 0 ≤ Real.log (5 * Real.exp 1 * x) := by rw [← h5ex]; exact hrhs
  nlinarith
