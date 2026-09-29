-- Prove2me | solution 1 for Rudin.ch06_integral_mono_of_bounded_larger
-- status  : ACCEPTED   (disprove)
-- author  : @Lucas
-- created : 2026-09-18T15:06:47.878373+00:00
-- url     : https://prove2.me/submissions/39e0d590-6f73-42c8-bc2f-83d3c63f6114

import Mathlib
import Definitions.Def_Rudin_ch06_stieltjes

open Filter Topology

namespace RudinSharp

open Rudin

/-- The integrand of the counterexample: `f x = -max 1 x⁻¹`, so `f 0 = -1`, `f x = -1/x` on
`(0, 1]`, and `f ≤ -1` everywhere. -/
noncomputable def fcex : ℝ → ℝ := fun x => -max 1 x⁻¹

lemma fcex_le_neg_one (x : ℝ) : fcex x ≤ -1 := by
  have h : (1 : ℝ) ≤ max 1 x⁻¹ := le_max_left _ _
  simp only [fcex, neg_le_neg_iff]
  exact h

lemma fcex_zero : fcex 0 = -1 := by norm_num [fcex]

lemma fcex_eq (x : ℝ) (hx : 0 < x) (hx1 : x ≤ 1) : fcex x = -x⁻¹ := by
  have h1 : (1 : ℝ) ≤ x⁻¹ := by
    rw [le_inv_comm₀ (by norm_num) hx]
    simpa using hx1
  simp [fcex, max_eq_right h1]

/-- The supremum of `fcex` on a subinterval of `(0, 1]` is attained at the right endpoint. -/
lemma sSup_fcex_pos {u v : ℝ} (hu : 0 < u) (huv : u ≤ v) (hv : v ≤ 1) :
    sSup (fcex '' Set.Icc u v) = -v⁻¹ := by
  have hv0 : 0 < v := lt_of_lt_of_le hu huv
  have hmem : -v⁻¹ ∈ fcex '' Set.Icc u v :=
    ⟨v, ⟨huv, le_refl v⟩, fcex_eq v hv0 hv⟩
  have hub : ∀ y ∈ fcex '' Set.Icc u v, y ≤ -v⁻¹ := by
    rintro y ⟨x, ⟨hx1, hx2⟩, rfl⟩
    have hx0 : 0 < x := lt_of_lt_of_le hu hx1
    have hxle : x ≤ 1 := le_trans hx2 hv
    rw [fcex_eq x hx0 hxle]
    have hinv : v⁻¹ ≤ x⁻¹ := by
      apply inv_anti₀ hx0 hx2
    linarith
  exact le_antisymm (csSup_le ⟨_, hmem⟩ hub) (le_csSup ⟨-v⁻¹, hub⟩ hmem)

/-- The supremum of `fcex` on `[0, v]` is `-1`, attained at `0`. -/
lemma sSup_fcex_zero {v : ℝ} (hv : 0 ≤ v) : sSup (fcex '' Set.Icc 0 v) = -1 := by
  have hmem : (-1 : ℝ) ∈ fcex '' Set.Icc 0 v := ⟨0, ⟨le_refl 0, hv⟩, fcex_zero⟩
  have hub : ∀ y ∈ fcex '' Set.Icc 0 v, y ≤ -1 := by
    rintro y ⟨x, _, rfl⟩
    exact fcex_le_neg_one x
  exact le_antisymm (csSup_le ⟨_, hmem⟩ hub) (le_csSup ⟨-1, hub⟩ hmem)

/-- `fcex` is unbounded below on any interval `[0, v]` with `v > 0`. -/
lemma not_bddBelow_image {v : ℝ} (hv : 0 < v) : ¬ BddBelow (fcex '' Set.Icc 0 v) := by
  rintro ⟨c, hc⟩
  set t : ℝ := min v (1 / (|c| + 2)) with ht
  have hc2 : (0 : ℝ) < |c| + 2 := by positivity
  have ht0 : 0 < t := lt_min hv (by positivity)
  have htv : t ≤ v := min_le_left _ _
  have htb : t ≤ 1 / (|c| + 2) := min_le_right _ _
  have ht1 : t ≤ 1 := le_trans htb (by
    rw [div_le_one hc2]
    have := abs_nonneg c
    linarith)
  have hmem : fcex t ∈ fcex '' Set.Icc 0 v := ⟨t, ⟨le_of_lt ht0, htv⟩, rfl⟩
  have hle : c ≤ fcex t := hc hmem
  have hval : fcex t = -t⁻¹ := fcex_eq t ht0 ht1
  have hinv : |c| + 2 ≤ t⁻¹ := by
    rw [le_inv_comm₀ hc2 ht0]
    simpa [one_div] using htb
  have habs : -|c| ≤ c := neg_abs_le c
  rw [hval] at hle
  linarith

/-- The infimum of `fcex` on any subinterval is nonpositive: either the image is unbounded
below, in which case the infimum takes the default value `0`, or it is at most `fcex u ≤ -1`. -/
lemma sInf_fcex_nonpos {u v : ℝ} (huv : u ≤ v) : sInf (fcex '' Set.Icc u v) ≤ 0 := by
  by_cases hb : BddBelow (fcex '' Set.Icc u v)
  · have hmem : fcex u ∈ fcex '' Set.Icc u v := ⟨u, ⟨le_refl u, huv⟩, rfl⟩
    have := csInf_le hb hmem
    have := fcex_le_neg_one u
    linarith
  · rw [Real.sInf_of_not_bddBelow hb]

/-- The geometric partition `0, 2⁻ⁿ, 2¹⁻ⁿ, …, 1` of `[0, 1]`, with `n + 1` subintervals. -/
noncomputable def geoPartition (n : ℕ) : Partition 0 1 where
  n := n + 1
  x := fun i => if i = 0 then 0 else 2 ^ (i - 1) / 2 ^ n
  first := by simp
  last := by
    have h : ((2 : ℝ) ^ n) ≠ 0 := by positivity
    simp [h]
  mono := by
    intro i _
    rcases Nat.eq_zero_or_pos i with h | h
    · subst h
      show (0 : ℝ) ≤ _
      positivity
    · have hi : i ≠ 0 := by omega
      have hi1 : i + 1 ≠ 0 := by omega
      have hpow : (2 : ℝ) ^ (i - 1) ≤ 2 ^ (i + 1 - 1) := by
        apply pow_le_pow_right₀ (by norm_num)
        omega
      have h2n : (0 : ℝ) < 2 ^ n := by positivity
      simp only [hi, hi1, if_false]
      gcongr

lemma upperSum_geoPartition (n : ℕ) :
    upperSum fcex id (geoPartition n) = -(1 / 2 ^ n) - n / 2 := by
  have h2n : (0 : ℝ) < 2 ^ n := by positivity
  rw [upperSum]
  show ∑ i ∈ Finset.range (n + 1),
      sSup (fcex '' Set.Icc ((geoPartition n).x i) ((geoPartition n).x (i + 1))) *
        (id ((geoPartition n).x (i + 1)) - id ((geoPartition n).x i)) = _
  rw [Finset.sum_range_succ']
  have hzero : sSup (fcex '' Set.Icc ((geoPartition n).x 0) ((geoPartition n).x 1)) *
      (id ((geoPartition n).x 1) - id ((geoPartition n).x 0)) = -(1 / 2 ^ n) := by
    have hx0 : (geoPartition n).x 0 = 0 := by simp [geoPartition]
    have hx1 : (geoPartition n).x 1 = 1 / 2 ^ n := by
      simp [geoPartition]
    rw [hx0, hx1, sSup_fcex_zero (by positivity)]
    simp
  have hrest : ∀ i ∈ Finset.range n,
      sSup (fcex '' Set.Icc ((geoPartition n).x (i + 1)) ((geoPartition n).x (i + 1 + 1))) *
        (id ((geoPartition n).x (i + 1 + 1)) - id ((geoPartition n).x (i + 1))) = -(1 / 2) := by
    intro i hi
    have hin : i < n := Finset.mem_range.mp hi
    have hxa : (geoPartition n).x (i + 1) = 2 ^ i / 2 ^ n := by
      simp [geoPartition]
    have hxb : (geoPartition n).x (i + 1 + 1) = 2 ^ (i + 1) / 2 ^ n := by
      simp [geoPartition]
    have ha0 : (0 : ℝ) < 2 ^ i / 2 ^ n := by positivity
    have hab : (2 : ℝ) ^ i / 2 ^ n ≤ 2 ^ (i + 1) / 2 ^ n := by
      gcongr
      · norm_num
      · omega
    have hb1 : (2 : ℝ) ^ (i + 1) / 2 ^ n ≤ 1 := by
      rw [div_le_one h2n]
      apply pow_le_pow_right₀ (by norm_num)
      omega
    rw [hxa, hxb, sSup_fcex_pos ha0 hab hb1]
    have hbne : ((2 : ℝ) ^ (i + 1) / 2 ^ n) ≠ 0 := by positivity
    simp only [id_eq, pow_succ]
    field_simp
    ring
  rw [Finset.sum_congr rfl hrest, hzero]
  simp
  ring

lemma not_bddBelow_upperSums :
    ¬ BddBelow {y : ℝ | ∃ P : Partition 0 1, y = upperSum fcex id P} := by
  rintro ⟨c, hc⟩
  obtain ⟨n, hn⟩ := exists_nat_gt (-2 * c)
  have hmem : upperSum fcex id (geoPartition n) ∈
      {y : ℝ | ∃ P : Partition 0 1, y = upperSum fcex id P} := ⟨_, rfl⟩
  have hle := hc hmem
  rw [upperSum_geoPartition n] at hle
  have hpos : (0 : ℝ) < 1 / 2 ^ n := by positivity
  linarith

lemma upperIntegral_fcex : upperIntegral 0 1 fcex id = 0 :=
  Real.sInf_of_not_bddBelow not_bddBelow_upperSums

/-- The two-point partition of `[0, 1]`. -/
def trivPartition : Partition (0 : ℝ) 1 where
  n := 1
  x := fun i => if i = 0 then 0 else 1
  first := by simp
  last := by simp
  mono := by
    intro i hi
    have : i = 0 := by omega
    subst this
    norm_num

lemma lowerSum_trivPartition : lowerSum fcex id trivPartition = 0 := by
  rw [lowerSum]
  show ∑ i ∈ Finset.range 1,
      sInf (fcex '' Set.Icc (trivPartition.x i) (trivPartition.x (i + 1))) *
        (id (trivPartition.x (i + 1)) - id (trivPartition.x i)) = 0
  have hx0 : trivPartition.x 0 = 0 := by simp [trivPartition]
  have hx1 : trivPartition.x 1 = 1 := by simp [trivPartition]
  rw [Finset.sum_range_one, hx0, hx1, Real.sInf_of_not_bddBelow (not_bddBelow_image one_pos)]
  ring

lemma lowerSum_nonpos (P : Partition (0 : ℝ) 1) : lowerSum fcex id P ≤ 0 := by
  rw [lowerSum]
  apply Finset.sum_nonpos
  intro i hi
  have hin : i < P.n := Finset.mem_range.mp hi
  have hmono : P.x i ≤ P.x (i + 1) := P.mono i hin
  have hinf : sInf (fcex '' Set.Icc (P.x i) (P.x (i + 1))) ≤ 0 := sInf_fcex_nonpos hmono
  have hdelta : (0 : ℝ) ≤ id (P.x (i + 1)) - id (P.x i) := by simpa using hmono
  exact mul_nonpos_of_nonpos_of_nonneg hinf hdelta

lemma lowerIntegral_fcex : lowerIntegral 0 1 fcex id = 0 := by
  have hmem : (0 : ℝ) ∈ {y : ℝ | ∃ P : Partition 0 1, y = lowerSum fcex id P} :=
    ⟨trivPartition, lowerSum_trivPartition.symm⟩
  have hub : ∀ y ∈ {y : ℝ | ∃ P : Partition 0 1, y = lowerSum fcex id P}, y ≤ 0 := by
    rintro y ⟨P, rfl⟩
    exact lowerSum_nonpos P
  exact le_antisymm (csSup_le ⟨_, hmem⟩ hub) (le_csSup ⟨0, hub⟩ hmem)

/-- The bounded comparison function `g = -1`. -/
lemma upperSum_const (P : Partition (0 : ℝ) 1) :
    upperSum (fun _ => (-1 : ℝ)) id P = -1 := by
  rw [upperSum]
  have hterm : ∀ i ∈ Finset.range P.n,
      sSup ((fun _ => (-1 : ℝ)) '' Set.Icc (P.x i) (P.x (i + 1))) *
        (id (P.x (i + 1)) - id (P.x i)) = -(P.x (i + 1) - P.x i) := by
    intro i hi
    have hin : i < P.n := Finset.mem_range.mp hi
    have hmono : P.x i ≤ P.x (i + 1) := P.mono i hin
    have himg : (fun _ => (-1 : ℝ)) '' Set.Icc (P.x i) (P.x (i + 1)) = {(-1 : ℝ)} :=
      Set.Nonempty.image_const (⟨P.x i, ⟨le_refl _, hmono⟩⟩ :
        (Set.Icc (P.x i) (P.x (i + 1))).Nonempty) _
    rw [himg, csSup_singleton]
    simp
  rw [Finset.sum_congr rfl hterm]
  have : ∑ i ∈ Finset.range P.n, -(P.x (i + 1) - P.x i) = -(P.x P.n - P.x 0) := by
    rw [Finset.sum_neg_distrib, Finset.sum_range_sub (fun i => P.x i) P.n]
  rw [this, P.first, P.last]
  ring

lemma lowerSum_const (P : Partition (0 : ℝ) 1) :
    lowerSum (fun _ => (-1 : ℝ)) id P = -1 := by
  rw [lowerSum]
  have hterm : ∀ i ∈ Finset.range P.n,
      sInf ((fun _ => (-1 : ℝ)) '' Set.Icc (P.x i) (P.x (i + 1))) *
        (id (P.x (i + 1)) - id (P.x i)) = -(P.x (i + 1) - P.x i) := by
    intro i hi
    have hin : i < P.n := Finset.mem_range.mp hi
    have hmono : P.x i ≤ P.x (i + 1) := P.mono i hin
    have himg : (fun _ => (-1 : ℝ)) '' Set.Icc (P.x i) (P.x (i + 1)) = {(-1 : ℝ)} :=
      Set.Nonempty.image_const (⟨P.x i, ⟨le_refl _, hmono⟩⟩ :
        (Set.Icc (P.x i) (P.x (i + 1))).Nonempty) _
    rw [himg, csInf_singleton]
    simp
  rw [Finset.sum_congr rfl hterm]
  have : ∑ i ∈ Finset.range P.n, -(P.x (i + 1) - P.x i) = -(P.x P.n - P.x 0) := by
    rw [Finset.sum_neg_distrib, Finset.sum_range_sub (fun i => P.x i) P.n]
  rw [this, P.first, P.last]
  ring

lemma upperIntegral_const : upperIntegral 0 1 (fun _ => (-1 : ℝ)) id = -1 := by
  have hset : {y : ℝ | ∃ P : Partition (0 : ℝ) 1, y = upperSum (fun _ => (-1 : ℝ)) id P}
      = {(-1 : ℝ)} := by
    ext y
    constructor
    · rintro ⟨P, rfl⟩
      simpa using upperSum_const P
    · rintro rfl
      exact ⟨trivPartition, (upperSum_const trivPartition).symm⟩
  rw [upperIntegral, hset, csInf_singleton]

lemma lowerIntegral_const : lowerIntegral 0 1 (fun _ => (-1 : ℝ)) id = -1 := by
  have hset : {y : ℝ | ∃ P : Partition (0 : ℝ) 1, y = lowerSum (fun _ => (-1 : ℝ)) id P}
      = {(-1 : ℝ)} := by
    ext y
    constructor
    · rintro ⟨P, rfl⟩
      simpa using lowerSum_const P
    · rintro rfl
      exact ⟨trivPartition, (lowerSum_const trivPartition).symm⟩
  rw [lowerIntegral, hset, csSup_singleton]

end RudinSharp

open Rudin RudinSharp in
/-- Monotonicity of the Riemann–Stieltjes integral fails if only the larger integrand is assumed
bounded: on `[0, 1]` with `α = id`, `f x = -max 1 x⁻¹` satisfies `f ≤ -1` and is degenerately
integrable with integral `0`, while the constant `-1` has integral `-1`. -/
theorem solution : ¬ (∀ (a b : ℝ) (_ : a ≤ b) (f g α : ℝ → ℝ)
    (_ : MonotoneOn α (Set.Icc a b))
    (_ : ∃ M, ∀ x ∈ Set.Icc a b, |g x| ≤ M)
    (_ : RSIntegrable a b f α) (_ : RSIntegrable a b g α)
    (_ : ∀ x ∈ Set.Icc a b, f x ≤ g x),
    RSIntegral a b f α ≤ RSIntegral a b g α) := by
  intro h
  have hf : RSIntegrable 0 1 fcex id := by
    show upperIntegral 0 1 fcex id = lowerIntegral 0 1 fcex id
    rw [upperIntegral_fcex, lowerIntegral_fcex]
  have hg : RSIntegrable 0 1 (fun _ => (-1 : ℝ)) id := by
    show upperIntegral 0 1 (fun _ => (-1 : ℝ)) id = lowerIntegral 0 1 (fun _ => (-1 : ℝ)) id
    rw [upperIntegral_const, lowerIntegral_const]
  have hmono : MonotoneOn (id : ℝ → ℝ) (Set.Icc 0 1) := fun _ _ _ _ hxy => hxy
  have hbound : ∃ M, ∀ x ∈ Set.Icc (0 : ℝ) 1, |(fun _ => (-1 : ℝ)) x| ≤ M :=
    ⟨1, by intro x _; norm_num⟩
  have hle : ∀ x ∈ Set.Icc (0 : ℝ) 1, fcex x ≤ (fun _ => (-1 : ℝ)) x := by
    intro x _
    exact fcex_le_neg_one x
  have := h 0 1 (by norm_num) fcex (fun _ => (-1 : ℝ)) id hmono hbound hf hg hle
  rw [RSIntegral, RSIntegral, upperIntegral_fcex, upperIntegral_const] at this
  linarith
