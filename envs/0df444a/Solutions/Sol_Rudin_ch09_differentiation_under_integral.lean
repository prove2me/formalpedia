-- Prove2me | solution 1 for Rudin.ch09_differentiation_under_integral
-- status  : ACCEPTED   (disprove)
-- author  : @Shuze Chen
-- created : 2026-09-17T03:04:14.961905+00:00
-- url     : https://prove2.me/submissions/ec62178c-8689-4940-b4b4-6e1c18e6c0d1

import Mathlib
import Definitions.Def_Rudin_ch06_stieltjes

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

open Filter Topology Rudin

/-!
# A counterexample to Rudin 9.42 as stated

The statement quantifies over `RSIntegrable`, which is defined through Mathlib's `sSup`/`sInf`
on `ℝ`; those return the junk value `0` for sets that are unbounded.  A function that is
unbounded above and below on *every* non-degenerate subinterval therefore has all its upper and
lower sums equal to `0`, hence is "integrable" with integral `0`, while the constant function
`1` has integral `1`.  Interpolating linearly in the parameter produces a family satisfying
every hypothesis whose integral jumps at the base point.
-/

namespace Ch09CE

/-! ### Rationals with prescribed numerator class and large denominator -/

theorem exists_rat (u v : ℝ) (huv : u < v) (N : ℕ) (par : ℤ) (hpar : par = 1 ∨ par = 2) :
    ∃ r : ℚ, u < (r : ℝ) ∧ (r : ℝ) < v ∧ N < r.den ∧ r.num % 6 = par := by
  obtain ⟨m, hm⟩ : ∃ m : ℕ, max ((N : ℝ) + 1) (6 / (v - u) + 1) < 3 ^ m :=
    pow_unbounded_of_one_lt _ (by norm_num)
  have h3m : (0 : ℝ) < 3 ^ m := by positivity
  have hNlt : (N : ℝ) + 1 < 3 ^ m := lt_of_le_of_lt (le_max_left _ _) hm
  have hlen : 6 < (v - u) * 3 ^ m := by
    have h1 : 6 / (v - u) + 1 < 3 ^ m := lt_of_le_of_lt (le_max_right _ _) hm
    have h2 : 6 / (v - u) < 3 ^ m := by linarith
    rw [div_lt_iff₀ (by linarith)] at h2
    linarith
  set A : ℝ := u * 3 ^ m with hA
  set K : ℤ := ⌊A⌋ + 1 with hK
  have hKA : A < K := by rw [hK]; push_cast; linarith [Int.lt_floor_add_one A]
  have hKA' : (K : ℝ) ≤ A + 1 := by rw [hK]; push_cast; linarith [Int.floor_le A]
  set p : ℤ := K + ((par - K) % 6) with hp
  have hmod6 : p % 6 = par % 6 := by
    have := Int.emod_emod_of_dvd (par - K) (dvd_refl 6)
    omega
  have hparmod : par % 6 = par := by rcases hpar with rfl | rfl <;> decide
  have hpmod : p % 6 = par := by rw [hmod6, hparmod]
  have hrange : (0 : ℤ) ≤ (par - K) % 6 ∧ (par - K) % 6 < 6 := ⟨Int.emod_nonneg _ (by norm_num),
    Int.emod_lt_of_pos _ (by norm_num)⟩
  have hpK : K ≤ p ∧ p ≤ K + 5 := by omega
  have hpA : A < p := by
    have : (K : ℝ) ≤ (p : ℝ) := by exact_mod_cast hpK.1
    linarith
  have hpB : (p : ℝ) < v * 3 ^ m := by
    have h1 : (p : ℝ) ≤ (K : ℝ) + 5 := by exact_mod_cast hpK.2
    have : (v : ℝ) * 3 ^ m = u * 3 ^ m + (v - u) * 3 ^ m := by ring
    rw [this, ← hA]
    linarith
  have h3p : ¬ ((3 : ℤ) ∣ p) := by
    intro hdvd
    have h1 : p % 3 = 0 := Int.emod_eq_zero_of_dvd hdvd
    rcases hpar with rfl | rfl <;> omega
  have hcop : Nat.Coprime p.natAbs (3 ^ m) := by
    refine Nat.Coprime.pow_right _ ?_
    rw [Nat.coprime_comm]
    refine (Nat.Prime.coprime_iff_not_dvd (by norm_num)).2 ?_
    intro hdvd
    apply h3p
    have h2 : (3 : ℤ).natAbs ∣ p.natAbs := by simpa using hdvd
    exact Int.natAbs_dvd_natAbs.1 h2
  refine ⟨⟨p, 3 ^ m, by positivity, hcop⟩, ?_, ?_, ?_, hpmod⟩
  · rw [Rat.cast_def]
    show u < (p : ℝ) / ((3 ^ m : ℕ) : ℝ)
    rw [lt_div_iff₀ (by positivity)]
    push_cast
    linarith [hpA]
  · rw [Rat.cast_def]
    show (p : ℝ) / ((3 ^ m : ℕ) : ℝ) < v
    rw [div_lt_iff₀ (by positivity)]
    push_cast
    linarith [hpB]
  · show N < 3 ^ m
    have : ((N : ℝ)) < ((3 ^ m : ℕ) : ℝ) := by push_cast; linarith
    exact_mod_cast this

/-! ### A function unbounded above and below on every non-degenerate interval -/

open Classical in
/-- `g` is `-q` at a rational with reduced numerator `≡ 1 (mod 6)` and denominator `q`, and
`+q` at the other rationals; it vanishes at the irrationals. -/
noncomputable def g (x : ℝ) : ℝ :=
  if h : ∃ r : ℚ, (r : ℝ) = x then
    (if (Classical.choose h).num % 6 = 1 then -((Classical.choose h).den : ℝ)
      else ((Classical.choose h).den : ℝ))
  else 0

theorem g_rat (r : ℚ) :
    g (r : ℝ) = if r.num % 6 = 1 then -((r.den : ℝ)) else ((r.den : ℝ)) := by
  have h : ∃ r' : ℚ, (r' : ℝ) = (r : ℝ) := ⟨r, rfl⟩
  rw [g, dif_pos h]
  have hc : Classical.choose h = r := Rat.cast_injective (Classical.choose_spec h)
  rw [hc]

theorem g_large {u v : ℝ} (huv : u < v) (M : ℝ) : ∃ x ∈ Set.Icc u v, M < g x := by
  obtain ⟨N, hN⟩ := exists_nat_gt M
  obtain ⟨r, hru, hrv, hden, hnum⟩ := exists_rat u v huv N 2 (Or.inr rfl)
  refine ⟨(r : ℝ), ⟨le_of_lt hru, le_of_lt hrv⟩, ?_⟩
  rw [g_rat, if_neg (by omega)]
  have : (N : ℝ) < (r.den : ℝ) := by exact_mod_cast hden
  linarith

theorem g_small {u v : ℝ} (huv : u < v) (M : ℝ) : ∃ x ∈ Set.Icc u v, g x < M := by
  obtain ⟨N, hN⟩ := exists_nat_gt (-M)
  obtain ⟨r, hru, hrv, hden, hnum⟩ := exists_rat u v huv N 1 (Or.inl rfl)
  refine ⟨(r : ℝ), ⟨le_of_lt hru, le_of_lt hrv⟩, ?_⟩
  rw [g_rat, if_pos hnum]
  have : (N : ℝ) < (r.den : ℝ) := by exact_mod_cast hden
  linarith

/-! ### The interpolating family -/

/-- The family `φ x t = 1 + t g x`. -/
noncomputable def phi (x t : ℝ) : ℝ := 1 + t * g x

theorem phi_large {u v : ℝ} (huv : u < v) {t : ℝ} (ht : t ≠ 0) (M : ℝ) :
    ∃ x ∈ Set.Icc u v, M < phi x t := by
  rcases lt_or_gt_of_ne ht with hneg | hpos
  · obtain ⟨x, hx, hgx⟩ := g_small huv ((M - 1) / t)
    refine ⟨x, hx, ?_⟩
    have h1 := (lt_div_iff_of_neg hneg).1 hgx
    have h2 : t * g x = g x * t := mul_comm _ _
    rw [phi]
    linarith
  · obtain ⟨x, hx, hgx⟩ := g_large huv ((M - 1) / t)
    refine ⟨x, hx, ?_⟩
    have h1 := (div_lt_iff₀ hpos).1 hgx
    have h2 : t * g x = g x * t := mul_comm _ _
    rw [phi]
    linarith

theorem phi_small {u v : ℝ} (huv : u < v) {t : ℝ} (ht : t ≠ 0) (M : ℝ) :
    ∃ x ∈ Set.Icc u v, phi x t < M := by
  rcases lt_or_gt_of_ne ht with hneg | hpos
  · obtain ⟨x, hx, hgx⟩ := g_large huv ((M - 1) / t)
    refine ⟨x, hx, ?_⟩
    have h1 := (div_lt_iff_of_neg hneg).1 hgx
    have h2 : t * g x = g x * t := mul_comm _ _
    rw [phi]
    linarith
  · obtain ⟨x, hx, hgx⟩ := g_small huv ((M - 1) / t)
    refine ⟨x, hx, ?_⟩
    have h1 := (lt_div_iff₀ hpos).1 hgx
    have h2 : t * g x = g x * t := mul_comm _ _
    rw [phi]
    linarith

theorem sSup_phi {u v : ℝ} (huv : u < v) {t : ℝ} (ht : t ≠ 0) :
    sSup ((fun x => phi x t) '' Set.Icc u v) = 0 := by
  refine Real.sSup_of_not_bddAbove ?_
  rintro ⟨M, hM⟩
  obtain ⟨x, hx, hlt⟩ := phi_large huv ht M
  exact absurd (hM ⟨x, hx, rfl⟩) (not_le.2 hlt)

theorem sInf_phi {u v : ℝ} (huv : u < v) {t : ℝ} (ht : t ≠ 0) :
    sInf ((fun x => phi x t) '' Set.Icc u v) = 0 := by
  refine Real.sInf_of_not_bddBelow ?_
  rintro ⟨M, hM⟩
  obtain ⟨x, hx, hlt⟩ := phi_small huv ht M
  exact absurd (hM ⟨x, hx, rfl⟩) (not_le.2 hlt)

/-! ### All upper and lower sums vanish for `t ≠ 0` -/

theorem upperSum_eq_zero {t : ℝ} (ht : t ≠ 0) (P : Partition 0 1) :
    upperSum (fun x => phi x t) id P = 0 := by
  rw [upperSum]
  refine Finset.sum_eq_zero ?_
  intro i hi
  rw [Finset.mem_range] at hi
  rcases lt_or_eq_of_le (P.mono i hi) with h | h
  · rw [sSup_phi h ht, zero_mul]
  · simp only [id_eq, h, sub_self, mul_zero]

theorem lowerSum_eq_zero {t : ℝ} (ht : t ≠ 0) (P : Partition 0 1) :
    lowerSum (fun x => phi x t) id P = 0 := by
  rw [lowerSum]
  refine Finset.sum_eq_zero ?_
  intro i hi
  rw [Finset.mem_range] at hi
  rcases lt_or_eq_of_le (P.mono i hi) with h | h
  · rw [sInf_phi h ht, zero_mul]
  · simp only [id_eq, h, sub_self, mul_zero]

/-! ### The sums for `t = 0` -/

theorem phi_zero (x : ℝ) : phi x 0 = 1 := by rw [phi]; ring

theorem image_phi_zero (P : Partition 0 1) {i : ℕ} (hi : i < P.n) :
    (fun x => phi x 0) '' Set.Icc (P.x i) (P.x (i + 1)) = {(1 : ℝ)} := by
  have hfun : (fun x => phi x 0) = fun _ : ℝ => (1 : ℝ) := by funext x; exact phi_zero x
  rw [hfun]
  ext y
  simp only [Set.mem_image, Set.mem_singleton_iff]
  constructor
  · rintro ⟨x, -, rfl⟩
    rfl
  · rintro rfl
    exact ⟨P.x i, Set.left_mem_Icc.2 (P.mono i hi), rfl⟩

theorem upperSum_one (P : Partition 0 1) : upperSum (fun x => phi x 0) id P = 1 := by
  rw [upperSum]
  have h : ∀ i ∈ Finset.range P.n,
      sSup ((fun x => phi x 0) '' Set.Icc (P.x i) (P.x (i + 1)))
        * (id (P.x (i + 1)) - id (P.x i)) = P.x (i + 1) - P.x i := by
    intro i hi
    rw [Finset.mem_range] at hi
    rw [image_phi_zero P hi, csSup_singleton]
    simp
  rw [Finset.sum_congr rfl h, Finset.sum_range_sub (fun i => P.x i), P.first, P.last]
  ring

theorem lowerSum_one (P : Partition 0 1) : lowerSum (fun x => phi x 0) id P = 1 := by
  rw [lowerSum]
  have h : ∀ i ∈ Finset.range P.n,
      sInf ((fun x => phi x 0) '' Set.Icc (P.x i) (P.x (i + 1)))
        * (id (P.x (i + 1)) - id (P.x i)) = P.x (i + 1) - P.x i := by
    intro i hi
    rw [Finset.mem_range] at hi
    rw [image_phi_zero P hi, csInf_singleton]
    simp
  rw [Finset.sum_congr rfl h, Finset.sum_range_sub (fun i => P.x i), P.first, P.last]
  ring

/-! ### The upper and lower integrals -/

/-- The one-piece partition of `[0,1]`. -/
def triv01 : Partition 0 1 where
  n := 1
  x := fun i => if i = 0 then 0 else 1
  first := rfl
  last := rfl
  mono := by
    intro i hi
    interval_cases i
    norm_num

theorem upperIntegral_zero {t : ℝ} (ht : t ≠ 0) :
    upperIntegral 0 1 (fun x => phi x t) id = 0 := by
  have hset : {y : ℝ | ∃ P : Partition 0 1, y = upperSum (fun x => phi x t) id P} = {0} := by
    ext y
    simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
    constructor
    · rintro ⟨P, rfl⟩
      exact upperSum_eq_zero ht P
    · rintro rfl
      exact ⟨triv01, (upperSum_eq_zero ht _).symm⟩
  rw [upperIntegral, hset, csInf_singleton]

theorem lowerIntegral_zero {t : ℝ} (ht : t ≠ 0) :
    lowerIntegral 0 1 (fun x => phi x t) id = 0 := by
  have hset : {y : ℝ | ∃ P : Partition 0 1, y = lowerSum (fun x => phi x t) id P} = {0} := by
    ext y
    simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
    constructor
    · rintro ⟨P, rfl⟩
      exact lowerSum_eq_zero ht P
    · rintro rfl
      exact ⟨triv01, (lowerSum_eq_zero ht _).symm⟩
  rw [lowerIntegral, hset, csSup_singleton]

theorem upperIntegral_one : upperIntegral 0 1 (fun x => phi x 0) id = 1 := by
  have hset : {y : ℝ | ∃ P : Partition 0 1, y = upperSum (fun x => phi x 0) id P} = {1} := by
    ext y
    simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
    constructor
    · rintro ⟨P, rfl⟩
      exact upperSum_one P
    · rintro rfl
      exact ⟨triv01, (upperSum_one _).symm⟩
  rw [upperIntegral, hset, csInf_singleton]

theorem lowerIntegral_one : lowerIntegral 0 1 (fun x => phi x 0) id = 1 := by
  have hset : {y : ℝ | ∃ P : Partition 0 1, y = lowerSum (fun x => phi x 0) id P} = {1} := by
    ext y
    simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
    constructor
    · rintro ⟨P, rfl⟩
      exact lowerSum_one P
    · rintro rfl
      exact ⟨triv01, (lowerSum_one _).symm⟩
  rw [lowerIntegral, hset, csSup_singleton]

theorem integrable_t (t : ℝ) : RSIntegrable 0 1 (fun x => phi x t) id := by
  by_cases ht : t = 0
  · subst ht
    rw [RSIntegrable, upperIntegral_one, lowerIntegral_one]
  · rw [RSIntegrable, upperIntegral_zero ht, lowerIntegral_zero ht]

theorem integral_ne (t : ℝ) (ht : t ≠ 0) : RSIntegral 0 1 (fun x => phi x t) id = 0 :=
  upperIntegral_zero ht

theorem integral_eq_one : RSIntegral 0 1 (fun x => phi x 0) id = 1 :=
  upperIntegral_one

/-! ### Rudin's Theorem 9.42 is false as stated -/

theorem main : ¬ (∀ (a b c d : ℝ), a ≤ b → c < d → ∀ (φ D2φ : ℝ → ℝ → ℝ) (α : ℝ → ℝ),
    MonotoneOn α (Set.Icc a b) →
    (∀ t ∈ Set.Icc c d, RSIntegrable a b (fun x => φ x t) α) →
    (∀ x ∈ Set.Icc a b, ∀ t ∈ Set.Ioo c d, HasDerivAt (fun u => φ x u) (D2φ x t) t) →
    ∀ (s : ℝ), s ∈ Set.Ioo c d →
    (∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ Set.Icc a b, ∀ t ∈ Set.Ioo c d,
      |t - s| < δ → |D2φ x t - D2φ x s| < ε) →
    RSIntegrable a b (fun x => D2φ x s) α ∧
      HasDerivAt (fun t => RSIntegral a b (fun x => φ x t) α)
        (RSIntegral a b (fun x => D2φ x s) α) s) := by
  intro H
  obtain ⟨-, hd⟩ := H 0 1 (-1) 1 (by norm_num) (by norm_num) phi (fun x _ => g x) id
    (monotone_id.monotoneOn _) (fun t _ => integrable_t t)
    (fun x _ t _ => by
      have h := ((hasDerivAt_id t).mul_const (g x)).const_add (1 : ℝ)
      simpa [phi] using h)
    0 (by norm_num)
    (fun ε hε => ⟨1, one_pos, fun x _ t _ _ => by simpa using hε⟩)
  have hcont : ContinuousAt (fun t => RSIntegral 0 1 (fun x => phi x t) id) 0 := hd.continuousAt
  have h1 : Tendsto (fun t => RSIntegral 0 1 (fun x => phi x t) id) (nhdsWithin 0 {(0 : ℝ)}ᶜ)
      (nhds (RSIntegral 0 1 (fun x => phi x 0) id)) := hcont.continuousWithinAt
  have h2 : Tendsto (fun t => RSIntegral 0 1 (fun x => phi x t) id) (nhdsWithin 0 {(0 : ℝ)}ᶜ)
      (nhds 0) := by
    refine Tendsto.congr' ?_ tendsto_const_nhds
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact (integral_ne t ht).symm
  have huniq := tendsto_nhds_unique h1 h2
  rw [integral_eq_one] at huniq
  exact one_ne_zero huniq

end Ch09CE

theorem solution : ¬ (∀ (a b c d : ℝ), a ≤ b → c < d → ∀ (φ D2φ : ℝ → ℝ → ℝ) (α : ℝ → ℝ),
    MonotoneOn α (Set.Icc a b) →
    (∀ t ∈ Set.Icc c d, Rudin.RSIntegrable a b (fun x => φ x t) α) →
    (∀ x ∈ Set.Icc a b, ∀ t ∈ Set.Ioo c d, HasDerivAt (fun u => φ x u) (D2φ x t) t) →
    ∀ (s : ℝ), s ∈ Set.Ioo c d →
    (∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ Set.Icc a b, ∀ t ∈ Set.Ioo c d,
      |t - s| < δ → |D2φ x t - D2φ x s| < ε) →
    Rudin.RSIntegrable a b (fun x => D2φ x s) α ∧
      HasDerivAt (fun t => Rudin.RSIntegral a b (fun x => φ x t) α)
        (Rudin.RSIntegral a b (fun x => D2φ x s) α) s) :=
  Ch09CE.main
