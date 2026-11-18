-- Prove2me | solution 1 for TopDownParity1043.Main.lemma_10
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-17T15:42:32.767814+00:00
-- url     : https://prove2.me/submissions/86596b2f-24a6-4019-9441-416e807c0d8a

import Mathlib
import Definitions.Def_TopDownParity1043_Main_RandomSets
import Definitions.Def_TopDownParity1043_Main_HarmonicMean
import Theorems.Thm_TopDownParity1043_Main_corollary_1
import Theorems.Thm_TopDownParity1043_Main_lemma_12
import Theorems.Thm_TopDownParity1043_Main_section_4_transfer

set_option autoImplicit false
open scoped NNReal ENNReal
open TopDownParity1043.Main

private noncomputable def density {V : Type} [Fintype V] (X : PMF (V → Bool)) :
    (V → Bool) → ℝ≥0 := fun x => (2 : ℝ≥0) ^ Fintype.card V * (X x).toNNReal

private theorem density_mean {V : Type} [Fintype V] [DecidableEq V]
    (X : PMF (V → Bool)) : cubeMean (density X) = 1 := by
  classical
  have hs : ∑ x, (X x).toNNReal = 1 := by
    rw [← ENNReal.coe_inj]
    simp only [ENNReal.coe_finset_sum, ENNReal.coe_toNNReal (X.apply_ne_top _), ENNReal.coe_one]
    simpa only [tsum_fintype] using X.tsum_coe
  simp only [cubeMean, density, ← Finset.mul_sum, hs, mul_one,
    Fintype.card_fun, Fintype.card_bool, Nat.cast_pow, Nat.cast_ofNat]
  exact div_self (pow_ne_zero _ two_ne_zero)

private theorem density_cap {V : Type} [Fintype V] [DecidableEq V]
    (X : PMF (V → Bool)) (k : ℝ) (hX : lawDeficit X ≤ k) (x : V → Bool) :
    (density X x : ℝ) ≤ (2 : ℝ) ^ k := by
  classical
  let M : ℝ := ⨆ y, (X y).toReal
  have hbound : BddAbove (Set.range (fun y => (X y).toReal)) := by
    refine ⟨1, ?_⟩
    rintro a ⟨y, rfl⟩
    exact ENNReal.toReal_le_of_le_ofReal (by norm_num) (by simpa using X.coe_le_one y)
  have hMx : (X x).toReal ≤ M := le_ciSup hbound x
  have hMpos : 0 < M := by
    obtain ⟨y, hy⟩ := X.support_nonempty
    have hy0 : X y ≠ 0 := hy
    have hyp : 0 < (X y).toReal := ENNReal.toReal_pos hy0 (X.apply_ne_top y)
    exact hyp.trans_le (le_ciSup hbound y)
  have hlog : Real.logb 2 M ≤ k - Fintype.card V := by
    unfold lawDeficit SamplingAC0.minEntropy at hX
    dsimp [M]
    linarith
  have hMcap : M ≤ (2 : ℝ) ^ (k - Fintype.card V) :=
    (Real.logb_le_iff_le_rpow (by norm_num) hMpos).mp hlog
  have hn : (0 : ℝ) ≤ 2 ^ Fintype.card V := by positivity
  calc
    (density X x : ℝ) = (2 : ℝ) ^ Fintype.card V * (X x).toReal := by
      simp [density, ENNReal.toReal]
    _ ≤ 2 ^ Fintype.card V * 2 ^ (k - Fintype.card V) :=
      mul_le_mul_of_nonneg_left (hMx.trans hMcap) hn
    _ = 2 ^ k := by
      rw [← Real.rpow_natCast, ← Real.rpow_add (by norm_num)]
      congr 1
      ring

private theorem conditional_density {V : Type} [Fintype V] [DecidableEq V]
    (X : PMF (V → Bool)) (R : Finset V) (z : R → Bool) :
    conditionalMean (density X) R z =
      (2 : ℝ≥0) ^ R.card * ((projectionLaw X R z).toNNReal) := by
  classical
  have hm : (projectionLaw X R z).toNNReal =
      ∑ x : V → Bool, if project R x = z then (X x).toNNReal else 0 := by
    unfold projectionLaw
    rw [PMF.map_apply, tsum_fintype, ENNReal.toNNReal_sum]
    · apply Finset.sum_congr rfl
      intro x hx
      split_ifs <;> simp_all [eq_comm]
    · intro x hx
      split_ifs <;> simp [X.apply_ne_top]
  rw [hm]
  unfold conditionalMean
  have hsum :
      (∑ x : V → Bool, if project R x = z then density X x else 0) =
        (2 : ℝ≥0) ^ Fintype.card V *
          ∑ x : V → Bool, if project R x = z then (X x).toNNReal else 0 := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x hx
    split_ifs <;> simp [density]
  rw [hsum]
  have hc := Finset.card_le_univ R
  have hp : (2 : ℝ≥0) ^ Fintype.card V =
      2 ^ R.card * 2 ^ (Fintype.card V - R.card) := by
    rw [← pow_add, Nat.add_sub_of_le hc]
  rw [hp]
  field_simp

private theorem density_sqrt_mean {V : Type} [Fintype V] [DecidableEq V]
    (X : PMF (V → Bool)) (k : ℝ) (hX : lawDeficit X ≤ k) :
    (2 : ℝ) ^ (-k / 2) ≤ (cubeMean (fun x => density X x ^ (1 / 2 : ℝ)) : ℝ) := by
  classical
  have hBpos : 0 < (2 : ℝ) ^ (k / 2) := by positivity
  have hsqrtB : Real.sqrt ((2 : ℝ) ^ k) = (2 : ℝ) ^ (k / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (by norm_num)]
    congr 1
    ring
  have hpoint : ∀ x : V → Bool,
      (density X x : ℝ) / (2 : ℝ) ^ (k / 2) ≤ (density X x : ℝ) ^ (1 / 2 : ℝ) := by
    intro x
    have hcap := Real.sqrt_le_sqrt (density_cap X k hX x)
    rw [hsqrtB] at hcap
    have hsquare := Real.sq_sqrt (density X x).coe_nonneg
    have hnonneg := Real.sqrt_nonneg (density X x : ℝ)
    rw [← Real.sqrt_eq_rpow, div_le_iff₀ hBpos]
    nlinarith
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun x hx => hpoint x)
  rw [← Finset.sum_div] at hsum
  have hmean1 : ((∑ x, density X x : ℝ≥0) : ℝ) / Fintype.card (V → Bool) = 1 := by
    have hm := congrArg (fun a : ℝ≥0 => (a : ℝ)) (density_mean X)
    simpa [cubeMean] using hm
  have hnpos : (0 : ℝ) < Fintype.card (V → Bool) := by
    exact_mod_cast Fintype.card_pos
  have hmoment : 1 / (2 : ℝ) ^ (k / 2) ≤
      (∑ x, (density X x : ℝ) ^ (1 / 2 : ℝ)) / Fintype.card (V → Bool) := by
    conv_lhs => rw [← hmean1]
    have hh := div_le_div_of_nonneg_right hsum hnpos.le
    push_cast
    rw [div_right_comm]
    exact hh
  have hexp : 1 / (2 : ℝ) ^ (k / 2) = (2 : ℝ) ^ (-k / 2) := by
    rw [one_div, ← Real.rpow_neg (by norm_num)]
    congr 1
    ring
  rw [hexp] at hmoment
  simpa [cubeMean, NNReal.coe_rpow] using hmoment

private theorem weight_nonneg {V : Type} [Fintype V] [DecidableEq V]
    (p : Bias) (R : Finset V) : 0 ≤ setWeight p R := by
  unfold setWeight
  exact mul_nonneg (pow_nonneg p.property.1 _) (pow_nonneg (sub_nonneg.mpr p.property.2) _)

private theorem weight_sum {V : Type} [Fintype V] [DecidableEq V] (p : Bias) :
    ∑ R : Finset V, setWeight p R = 1 := by
  simp only [setWeight, Fintype.sum_pow_mul_eq_add_pow, add_sub_cancel, one_pow]

private theorem prob_mono {V : Type} [Fintype V] [DecidableEq V]
    (p : Bias) (E F : Finset V → Prop) (hEF : ∀ R, E R → F R) :
    setProb p E ≤ setProb p F := by
  classical
  apply Finset.sum_le_sum
  intro R hR
  by_cases hE : E R
  · simp [hE, hEF R hE]
  · simp only [if_neg hE]
    split_ifs <;> positivity [weight_nonneg p R]

private theorem bounded_tail {V : Type} [Fintype V] [DecidableEq V]
    (p : Bias) (a : Finset V → ℝ) (ha : ∀ R, a R ≤ 1) (L : ℝ) (hL : 0 ≤ L)
    (hmean : L ≤ ∑ R : Finset V, setWeight p R * a R) :
    L / 2 ≤ setProb p (fun R => L / 2 ≤ a R) := by
  classical
  have hpoint : ∀ R, a R ≤ (if L / 2 ≤ a R then 1 else 0) + L / 2 := by
    intro R
    split_ifs with hR
    · linarith [ha R]
    · linarith
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun R hR =>
    mul_le_mul_of_nonneg_left (hpoint R) (weight_nonneg p R))
  have heq : (∑ R : Finset V, setWeight p R * ((if L / 2 ≤ a R then 1 else 0) + L / 2)) =
      setProb p (fun R => L / 2 ≤ a R) + L / 2 := by
    simp only [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, weight_sum, one_mul]
    congr 1
    unfold setProb
    apply Finset.sum_congr rfl
    intro R hR
    split_ifs <;> simp
  rw [heq] at hsum
  linarith

private theorem mean_toReal {V : Type} [Fintype V] [DecidableEq V]
    (p : Bias) (a : Finset V → ℝ≥0∞) (ha : ∀ R, a R ≠ ∞) :
    (setMean p a).toReal = ∑ R : Finset V, setWeight p R * (a R).toReal := by
  classical
  unfold setMean
  rw [ENNReal.toReal_sum]
  · apply Finset.sum_congr rfl
    intro R hR
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (weight_nonneg p R)]
  · intro R hR
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ha R)

private theorem harmonic_le_one {V : Type} [Fintype V] [DecidableEq V]
    (X : PMF (V → Bool)) (R : Finset V) : harmonicMean (density X) R ≤ 1 := by
  have h := (corollary_1 V (density X) (density X) (density X)).2.2.1 R
  simpa [density_mean X] using h

private theorem harmonic_finite {V : Type} [Fintype V] [DecidableEq V]
    (X : PMF (V → Bool)) (R : Finset V) : harmonicMean (density X) R ≠ ∞ :=
  ne_top_of_le_ne_top ENNReal.one_ne_top (harmonic_le_one X R)

private theorem quarter_good_mass {V : Type} [Fintype V] [DecidableEq V]
    (X : PMF (V → Bool)) (k : ℝ) (hX : lawDeficit X ≤ k) :
    (2 : ℝ) ^ (-k / 2) / 2 ≤
      setProb quarterBias (fun R => ENNReal.ofReal ((2 : ℝ) ^ (-k - 2)) ≤
        harmonicMean (density X) R) := by
  classical
  let a : Finset V → ℝ≥0∞ := fun R => harmonicMean (density X) R ^ (1 / 2 : ℝ)
  have hafin : ∀ R, a R ≠ ∞ := fun R =>
    ENNReal.rpow_ne_top_of_nonneg (by norm_num) (harmonic_finite X R)
  have ha1 : ∀ R, (a R).toReal ≤ 1 := by
    intro R
    have hb := ENNReal.rpow_le_one (harmonic_le_one X R) (by norm_num : (0 : ℝ) ≤ 1 / 2)
    exact ENNReal.toReal_le_of_le_ofReal (by norm_num) (by simpa [a] using hb)
  have hmoment : (2 : ℝ) ^ (-k / 2) ≤
      ∑ R : Finset V, setWeight quarterBias R * (a R).toReal := by
    have h12 := lemma_12 V (density X)
    have hfinmean : setMean quarterBias a ≠ ∞ := by
      unfold setMean
      apply ENNReal.sum_ne_top.mpr
      intro R hR
      exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hafin R)
    have hr := ENNReal.toReal_mono hfinmean h12
    rw [mean_toReal quarterBias a hafin] at hr
    simp only [ENNReal.coe_toReal] at hr
    exact (density_sqrt_mean X k hX).trans hr
  have htail := bounded_tail quarterBias (fun R => (a R).toReal) ha1
    ((2 : ℝ) ^ (-k / 2)) (by positivity) hmoment
  apply htail.trans
  apply prob_mono
  intro R hR
  rw [ENNReal.ofReal_le_iff_le_toReal (harmonic_finite X R)]
  have hsq : ((a R).toReal) ^ 2 = (harmonicMean (density X) R).toReal := by
    dsimp [a]
    rw [← ENNReal.toReal_rpow, ← Real.sqrt_eq_rpow]
    exact Real.sq_sqrt ENNReal.toReal_nonneg
  have hT : ((2 : ℝ) ^ (-k / 2) / 2) ^ 2 = (2 : ℝ) ^ (-k - 2) := by
    rw [div_pow, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    rw [Real.rpow_sub (by norm_num)]
    congr 1
    · congr 1
      norm_num <;> ring
    · norm_num
  rw [← hT]
  nlinarith [show 0 ≤ (a R).toReal from ENNReal.toReal_nonneg,
    Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) (-k / 2)]

private theorem harmonic_positive_cond {V : Type} [Fintype V] [DecidableEq V]
    (f : (V → Bool) → ℝ≥0) (R : Finset V) (hH : 0 < harmonicMean f R)
    (z : R → Bool) : 0 < conditionalMean f R z := by
  classical
  by_contra h
  have hz : conditionalMean f R z = 0 := le_antisymm (not_lt.mp h) bot_le
  have hsum : ∑ y : R → Bool, (conditionalMean f R y : ℝ≥0∞)⁻¹ = ∞ := by
    rw [ENNReal.sum_eq_top]
    exact ⟨z, Finset.mem_univ _, by simp [hz]⟩
  have hzero : harmonicMean f R = 0 := by
    simp [harmonicMean, hsum]
  rw [hzero] at hH
  exact lt_irrefl 0 hH

private theorem harmonic_real_formula {V : Type} [Fintype V] [DecidableEq V]
    (f : (V → Bool) → ℝ≥0) (R : Finset V) (hH : 0 < harmonicMean f R) :
    (harmonicMean f R).toReal =
      (2 : ℝ) ^ R.card / ∑ z : R → Bool, (conditionalMean f R z : ℝ)⁻¹ := by
  classical
  have hg : ∀ z, conditionalMean f R z ≠ 0 :=
    fun z => (harmonic_positive_cond f R hH z).ne'
  have hsum : ∑ z : R → Bool, (conditionalMean f R z : ℝ≥0∞)⁻¹ =
      ((∑ z : R → Bool, (conditionalMean f R z)⁻¹ : ℝ≥0) : ℝ≥0∞) := by
    simp only [ENNReal.coe_finset_sum]
    apply Finset.sum_congr rfl
    intro z hz
    exact (ENNReal.coe_inv (hg z)).symm
  unfold harmonicMean
  rw [hsum]
  simp only [ENNReal.toReal_inv, ENNReal.toReal_mul, ENNReal.toReal_pow,
    ENNReal.toReal_ofNat, ENNReal.coe_toReal, NNReal.coe_sum, NNReal.coe_inv]
  field_simp

private theorem light_cond_bound {V : Type} [Fintype V] [DecidableEq V]
    (X : PMF (V → Bool)) (R : Finset V) (k : ℝ) (z : R → Bool)
    (hz : ((projectionLaw X R z).toReal) ≤ (2 : ℝ) ^ (-(R.card : ℝ) - 2 * k - 2)) :
    (conditionalMean (density X) R z : ℝ) ≤ (2 : ℝ) ^ (-2*k-2) := by
  rw [conditional_density]
  push_cast
  change (2 : ℝ) ^ R.card * (projectionLaw X R z).toReal ≤ _
  calc
    (2 : ℝ) ^ R.card * (projectionLaw X R z).toReal ≤
        2 ^ R.card * 2 ^ (-(R.card : ℝ) - 2 * k - 2) :=
      mul_le_mul_of_nonneg_left hz (by positivity)
    _ = 2 ^ (-2*k-2) := by
      rw [← Real.rpow_natCast, ← Real.rpow_add (by norm_num)]
      congr 1
      ring

private theorem good_implies_light {V : Type} [Fintype V] [DecidableEq V]
    (X : PMF (V → Bool)) (R : Finset V) (k : ℝ)
    (hgood : ENNReal.ofReal ((2 : ℝ) ^ (-k-2)) ≤ harmonicMean (density X) R) :
    (lightCount X R k : ℝ) ≤ (2 : ℝ) ^ ((R.card : ℝ) - k) := by
  classical
  have ht : (0 : ℝ) < 2 ^ (-k-2) := by positivity
  have hH : 0 < harmonicMean (density X) R :=
    (ENNReal.ofReal_pos.mpr ht).trans_le hgood
  have hg : ∀ z, (0 : ℝ) < (conditionalMean (density X) R z : ℝ) := by
    intro z
    exact_mod_cast harmonic_positive_cond (density X) R hH z
  let L : Finset (R → Bool) := Finset.univ.filter fun z =>
    (projectionLaw X R z).toReal ≤ (2 : ℝ) ^ (-(R.card : ℝ)-2*k-2)
  let D : ℝ := ∑ z : R → Bool, (conditionalMean (density X) R z : ℝ)⁻¹
  have hD : 0 < D := by
    apply Finset.sum_pos
    · intro z hz
      exact inv_pos.mpr (hg z)
    · exact Finset.univ_nonempty
  have hprod : (2 : ℝ) ^ (-k-2) * D ≤ 2 ^ R.card := by
    rw [ENNReal.ofReal_le_iff_le_toReal (harmonic_finite X R),
      harmonic_real_formula (density X) R hH] at hgood
    exact (le_div_iff₀ hD).mp hgood
  have hcount : (L.card : ℝ) ≤ (2 : ℝ) ^ (-2*k-2) * D := by
    calc
      (L.card : ℝ) = ∑ _ ∈ L, (1 : ℝ) := by simp
      _ ≤ ∑ z ∈ L, (2 : ℝ) ^ (-2*k-2) * (conditionalMean (density X) R z : ℝ)⁻¹ := by
        apply Finset.sum_le_sum
        intro z hz
        have hlight := light_cond_bound X R k z ((Finset.mem_filter.mp hz).2)
        exact (le_mul_inv_iff₀ (hg z)).mpr (by simpa using hlight)
      _ ≤ ∑ z : R → Bool, (2 : ℝ) ^ (-2*k-2) * (conditionalMean (density X) R z : ℝ)⁻¹ := by
        exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ L)
          (fun z hz hzl => by positivity)
      _ = (2 : ℝ) ^ (-2*k-2) * D := by rw [← Finset.mul_sum]
  have hratio : (2 : ℝ) ^ (-2*k-2) / 2 ^ (-k-2) = 2 ^ (-k) := by
    rw [← Real.rpow_sub (by norm_num)]
    congr 1
    ring
  have hDle : D ≤ (2 : ℝ) ^ R.card / 2 ^ (-k-2) :=
    (le_div_iff₀ ht).mpr (by nlinarith [hprod])
  change (L.card : ℝ) ≤ _
  calc
    (L.card : ℝ) ≤ (2 : ℝ) ^ (-2*k-2) * D := hcount
    _ ≤ 2 ^ (-2*k-2) * (2 ^ R.card / 2 ^ (-k-2)) :=
      mul_le_mul_of_nonneg_left hDle (by positivity)
    _ = 2 ^ ((R.card : ℝ)-k) := by
      rw [show (2 : ℝ) ^ (-2*k-2) * (2 ^ R.card / 2 ^ (-k-2)) =
          2 ^ R.card * (2 ^ (-2*k-2) / 2 ^ (-k-2)) by ring,
        hratio, ← Real.rpow_natCast, ← Real.rpow_add (by norm_num)]
      congr 1

private theorem exp_two_lower (t : ℝ) (ht : 0 ≤ t) : 1 - t ≤ (2 : ℝ) ^ (-t) := by
  have hlog : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  have h := Real.add_one_le_exp (Real.log 2 * (-t))
  rw [Real.rpow_def_of_pos (by norm_num)]
  nlinarith

theorem solution (V : Type) [Fintype V] [DecidableEq V]
    (k : ℝ) (hk : 1 ≤ k) (r : Bias) (hr : (r : ℝ) ≤ (512 * k)⁻¹)
    (X : PMF (V → Bool)) (hX : lawDeficit X ≤ k) :
    (63 : ℝ) / 64 ≤ setProb r (fun R : Finset V =>
      (lightCount X R k : ℝ) ≤ (2 : ℝ) ^ ((R.card : ℝ) - k)) := by
  classical
  let A : Set (Finset V) := {R | ENNReal.ofReal ((2 : ℝ) ^ (-k-2)) ≤
    harmonicMean (density X) R}
  have hA : A.Nonempty := by
    refine ⟨∅, ?_⟩
    have he : harmonicMean (density X) ∅ = 1 := by
      rw [← (corollary_1 V (density X) (density X) (density X)).2.2.2, density_mean]
      rfl
    have hpow : (2 : ℝ) ^ (-k-2) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by linarith)
    change ENNReal.ofReal _ ≤ _
    rw [he]
    exact (ENNReal.ofReal_le_ofReal hpow).trans_eq (by simp)
  have hdown : DownwardClosed A := by
    intro R hR S hSR
    exact hR.trans ((corollary_1 V (density X) (density X) (density X)).2.1 S R hSR)
  have hprod : (r : ℝ) * (512 * k) ≤ 1 := by
    have hp : 0 < 512 * k := by linarith
    exact (le_div_iff₀ hp).mp (by simpa only [one_div] using hr)
  have hr20 : (r : ℝ) ≤ 1 / 20 := by
    have hr0 := r.property.1
    nlinarith
  have htransfer := section_4_transfer V A hA hdown r hr20
  have hquarter : (2 : ℝ) ^ (-k / 2 - 1) ≤ setProb quarterBias (fun R => R ∈ A) := by
    have hq := quarter_good_mass X k hX
    rw [Real.rpow_sub (by norm_num), Real.rpow_one]
    exact hq
  have hpower : ((2 : ℝ) ^ (-k / 2 - 1)) ^ (5 * (r : ℝ)) ≤
      (setProb quarterBias (fun R => R ∈ A)) ^ (5 * (r : ℝ)) :=
    Real.rpow_le_rpow (by positivity) hquarter (by positivity [r.property.1])
  have hsmall : 5 * (r : ℝ) * (k / 2 + 1) ≤ 1 / 64 := by
    have hr0 := r.property.1
    have hrk : (r : ℝ) ≤ (r : ℝ) * k := by nlinarith
    nlinarith
  have hnum : (63 : ℝ) / 64 ≤ ((2 : ℝ) ^ (-k / 2 - 1)) ^ (5 * (r : ℝ)) := by
    rw [← Real.rpow_mul (by norm_num)]
    have ht0 : 0 ≤ 5 * (r : ℝ) * (k / 2 + 1) := by positivity [r.property.1]
    have hexp := exp_two_lower (5 * (r : ℝ) * (k / 2 + 1)) ht0
    have he : (-k / 2 - 1) * (5 * (r : ℝ)) = -(5 * (r : ℝ) * (k / 2 + 1)) := by ring
    rw [he]
    linarith
  apply (hnum.trans (hpower.trans htransfer)).trans
  apply prob_mono
  intro R hR
  exact good_implies_light X R k hR
