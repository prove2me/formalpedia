-- Prove2me | solution 1 for TFIMPhaseDiagram.Classical.prop_9
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-27T04:22:29.683799+00:00
-- url     : https://prove2.me/submissions/0a819364-d0a0-49a3-b53e-f68e4df26898

import Theorems.Thm_TFIMPhaseDiagram_Classical_prop_8

set_option autoImplicit false
open scoped BigOperators Nat
noncomputable section
open MeasureTheory Filter Topology

namespace TFIMPhaseDiagram.Classical.RSAux

def stepf (f : ℝ → ℝ) (M : ℕ) (t : ℝ) : ℝ := f ((⌊t * M⌋ : ℝ) / M)

lemma floor_eq_on (M : ℕ) (hM : 0 < M) (k : ℕ) (t : ℝ)
    (ht : t ∈ Set.Ico ((k : ℝ) / M) (((k : ℝ) + 1) / M)) : ⌊t * M⌋ = (k : ℤ) := by
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM
  rw [Int.floor_eq_iff]
  obtain ⟨h1, h2⟩ := ht
  rw [div_le_iff₀ hMr] at h1
  rw [lt_div_iff₀ hMr] at h2
  push_cast; constructor <;> linarith

lemma Ico_union (M : ℕ) (hM : 0 < M) :
    Set.Ico (0 : ℝ) 1 = ⋃ k ∈ (Finset.range M), Set.Ico ((k : ℝ) / M) (((k : ℝ) + 1) / M) := by
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM
  ext t
  simp only [Set.mem_Ico, Set.mem_iUnion, Finset.mem_range, exists_prop]
  constructor
  · rintro ⟨h0, h1⟩
    refine ⟨⌊t * M⌋₊, ?_, ?_, ?_⟩
    · have : t * M < M := by nlinarith
      exact_mod_cast (Nat.floor_lt (by positivity)).2 (by exact_mod_cast this)
    · rw [div_le_iff₀ hMr]; exact Nat.floor_le (by positivity)
    · rw [lt_div_iff₀ hMr]; exact Nat.lt_floor_add_one _
  · rintro ⟨k, hk, h1, h2⟩
    have hk' : (k : ℝ) + 1 ≤ M := by exact_mod_cast hk
    constructor
    · exact le_trans (by positivity) h1
    · calc t < ((k : ℝ) + 1) / M := h2
        _ ≤ 1 := by rw [div_le_one hMr]; exact hk'

lemma riemann_eq (f : ℝ → ℝ) (B : ℝ) (hB : ∀ t, |f t| ≤ B) (hf : Measurable f) (M : ℕ) (hM : 0 < M) :
    (1 / (M : ℝ)) * ∑ k : Fin M, f (k.val / M) = ∫ t in Set.Icc (0 : ℝ) 1, stepf f M t := by
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM
  have hmeas : Measurable (stepf f M) := by
    unfold stepf
    exact hf.comp (((measurable_of_countable (fun z : ℤ => (z : ℝ))).comp
      (Int.measurable_floor.comp (measurable_id.mul_const _))).div_const _)
  rw [integral_Icc_eq_integral_Ico, Ico_union M hM]
  rw [integral_biUnion_finset]
  · rw [Fin.sum_univ_eq_sum_range (fun k => f (k / M)), Finset.mul_sum]
    apply Finset.sum_congr rfl; intro k _
    rw [setIntegral_congr_fun measurableSet_Ico (g := fun _ => f (k / M)) (fun t ht => by
      simp only [stepf]; rw [floor_eq_on M hM k t ht]; simp)]
    rw [setIntegral_const, Measure.real, Real.volume_Ico, ENNReal.toReal_ofReal (by
      rw [sub_nonneg]; gcongr; linarith), smul_eq_mul]
    congr 1; field_simp; ring
  · intro k _; exact measurableSet_Ico
  · intro k _ j _ hkj
    simp only [Function.onFun]
    rw [Set.disjoint_left]
    intro t h1 h2
    have := floor_eq_on M hM k t h1
    rw [floor_eq_on M hM j t h2] at this
    exact hkj (by exact_mod_cast this.symm)
  · intro k _
    refine Measure.integrableOn_of_bounded (M := B) ?_ hmeas.aestronglyMeasurable ?_
    · simp
    · exact Eventually.of_forall (fun t => by rw [Real.norm_eq_abs]; exact hB _)


theorem riemann_tendsto (f : ℝ → ℝ) (B : ℝ) (hB : ∀ t, |f t| ≤ B) (hf : Measurable f) (S : Finset ℝ)
    (hloc : ∀ t, 0 ≤ t → t < 1 → t ∉ S → ∃ δ > 0, ∀ s, t - δ < s → s ≤ t → f s = f t) :
    Tendsto (fun M : ℕ => (1 / (M : ℝ)) * ∑ k : Fin M, f (k.val / M)) atTop
      (𝓝 (∫ t in Set.Icc (0 : ℝ) 1, f t)) := by
  have hmeas : ∀ M : ℕ, Measurable (stepf f M) := fun M => by
    unfold stepf
    exact hf.comp (((measurable_of_countable (fun z : ℤ => (z : ℝ))).comp
      (Int.measurable_floor.comp (measurable_id.mul_const _))).div_const _)
  have heq : (fun M : ℕ => ∫ t in Set.Icc (0 : ℝ) 1, stepf f M t) =ᶠ[atTop]
      (fun M : ℕ => (1 / (M : ℝ)) * ∑ k : Fin M, f (k.val / M)) := by
    filter_upwards [eventually_ge_atTop 1] with M hM
    exact (riemann_eq f B hB hf M hM).symm
  refine Tendsto.congr' heq ?_
  apply tendsto_integral_of_dominated_convergence (fun _ => B)
  · intro M; exact (hmeas M).aestronglyMeasurable
  · exact integrable_const B
  · intro M; exact Eventually.of_forall (fun t => by rw [Real.norm_eq_abs]; exact hB _)
  · have hnull : volume ((S : Set ℝ) ∪ {1}) = 0 :=
      ((S.finite_toSet).union (Set.finite_singleton 1)).measure_zero volume
    have hae : ∀ᵐ t ∂volume, t ∉ (S : Set ℝ) ∪ {1} := measure_eq_zero_iff_ae_notMem.1 hnull
    rw [ae_restrict_iff' measurableSet_Icc]
    filter_upwards [hae] with t ht hIcc
    simp only [Set.mem_union, Finset.mem_coe, Set.mem_singleton_iff, not_or] at ht
    have ht1 : t < 1 := lt_of_le_of_ne hIcc.2 ht.2
    obtain ⟨δ, hδ, hδf⟩ := hloc t hIcc.1 ht1 ht.1
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_gt_atTop ⌈1 / δ⌉₊, eventually_ge_atTop 1] with M hM hM1
    have hMr : (0 : ℝ) < M := by exact_mod_cast hM1
    have hMδ : 1 / δ < M := lt_of_le_of_lt (Nat.le_ceil _) (by exact_mod_cast hM)
    have hinv : 1 / (M : ℝ) < δ := by
      rw [div_lt_iff₀ hMr]; rw [div_lt_iff₀ hδ] at hMδ; linarith
    symm
    apply hδf
    · have h1 : t * M - 1 < (⌊t * M⌋ : ℝ) := Int.sub_one_lt_floor _
      rw [lt_div_iff₀ hMr]
      have : (t - δ) * M < t * M - 1 := by
        have : 1 < δ * M := by rw [div_lt_iff₀ hMr] at hinv; linarith
        nlinarith
      linarith
    · rw [div_le_iff₀ hMr]; exact Int.floor_le _

end TFIMPhaseDiagram.Classical.RSAux

namespace TFIMPhaseDiagram.Classical.P9Aux
open TFIMPhaseDiagram.Classical TFIMPhaseDiagram.Classical.RSAux

lemma neg_one_pow_pm (c : ℕ) : (-1 : ℝ) ^ c = 1 ∨ (-1 : ℝ) ^ c = -1 := by
  rcases Nat.even_or_odd c with h | h
  · left; exact h.neg_one_pow
  · right; exact h.neg_one_pow

lemma pathValue_spin (σ : PathData) (t : ℝ) : pathValue σ t = spin (pathBits σ t) := by
  unfold pathBits pathValue
  rcases neg_one_pow_pm ((Finset.range σ.1).filter (fun k => σ.2.2 k ≤ t)).card with h | h <;>
    rw [h] <;> cases σ.2.1 <;> simp [spin] <;> norm_num

lemma meas_card' {ι : Type} (s : Finset ι) (t : ℝ) :
    Measurable (fun u : ι → ℝ => (s.filter (fun j => u j ≤ t)).card) := by
  have : (fun u : ι → ℝ => (s.filter (fun j => u j ≤ t)).card) =
      fun u => ∑ j ∈ s, (if u j ≤ t then 1 else 0) := by
    funext u; rw [Finset.card_filter]
  rw [this]
  exact Finset.measurable_sum _ (fun j _ => Measurable.ite
    (measurableSet_le (measurable_pi_apply j) measurable_const) measurable_const measurable_const)

lemma pathValue_meas' (t : ℝ) : Measurable (fun σ : PathData => pathValue σ t) := by
  apply measurable_from_prod_countable_right
  intro d
  unfold pathValue
  simp only
  apply Measurable.mul
  · exact (measurable_of_countable (fun b : Bool => spin b)).comp measurable_fst
  · exact (measurable_of_countable (fun n : ℕ => (-1 : ℝ) ^ n)).comp
      ((meas_card' (Finset.range d) t).comp measurable_snd)

lemma discretize_meas' (M : ℕ) : Measurable (discretize M) := by
  apply measurable_pi_lambda
  intro k
  apply measurable_to_bool
  have : (fun σ : PathData => discretize M σ k) ⁻¹' {true} = {σ | pathValue σ (k.val / (M:ℝ)) < 0} := by
    ext σ; simp [discretize, pathBits]
  rw [this]
  exact measurableSet_lt (pathValue_meas' _) measurable_const

instance u01_prob' : IsProbabilityMeasure TFIMPhaseDiagram.Classical.uniform01 :=
  ⟨by simp [TFIMPhaseDiagram.Classical.uniform01]⟩

lemma mass_nonneg (η : ℝ) (hη : 0 ≤ η) (p : Bool) (d : ℕ) : 0 ≤ parityMass η p d := by
  unfold parityMass
  split_ifs <;> try positivity

lemma mass_hasSum (η : ℝ) (hη : 0 ≤ η) (p : Bool) : HasSum (fun d => parityMass η p d) 1 := by
  by_cases h0 : η = 0
  · subst h0
    have : (fun d => parityMass 0 p d) = fun d => if d = (if p then 1 else 0) then 1 else 0 := by
      funext d; simp [parityMass]
    rw [this]
    convert hasSum_ite_eq (if p then 1 else 0) (1:ℝ)
  have hpos : 0 < η := lt_of_le_of_ne hη (Ne.symm h0)
  cases p
  · have hc := (Real.hasSum_cosh η).div_const (Real.cosh η)
    rw [div_self (Real.cosh_pos η).ne'] at hc
    rw [← (Function.Injective.hasSum_iff (g := fun n : ℕ => 2 * n) (fun a b h => by simpa using h) _)]
    · have e : (fun d => parityMass η false d) ∘ (fun n : ℕ => 2 * n) =
          fun i => η ^ (2 * i) / ↑(2 * i)! / Real.cosh η := by
        funext n; simp only [Function.comp, parityMass, h0, if_false, Bool.false_eq_true]
        rw [if_pos (by omega)]; field_simp
      rw [e]; exact hc
    · intro x hx
      simp only [parityMass, h0, if_false, Bool.false_eq_true]
      rw [if_neg]; intro h; exact hx ⟨x / 2, by show 2 * (x / 2) = x; omega⟩
  · have hs : 0 < Real.sinh η := Real.sinh_pos_iff.2 hpos
    have hc := (Real.hasSum_sinh η).div_const (Real.sinh η)
    rw [div_self hs.ne'] at hc
    rw [← (Function.Injective.hasSum_iff (g := fun n : ℕ => 2 * n + 1) (fun a b h => by simpa using h) _)]
    · have e : (fun d => parityMass η true d) ∘ (fun n : ℕ => 2 * n + 1) =
          fun i => η ^ (2 * i + 1) / ↑(2 * i + 1)! / Real.sinh η := by
        funext n; simp only [Function.comp, parityMass, h0, if_false, if_true]
        rw [if_pos (by omega)]; field_simp
      rw [e]; exact hc
    · intro x hx
      simp only [parityMass, h0, if_false, if_true]
      rw [if_neg]; intro h; exact hx ⟨x / 2, by show 2 * (x / 2) + 1 = x; omega⟩

lemma parityLaw_prob (η : ℝ) (hη : 0 ≤ η) (p : Bool) : IsProbabilityMeasure (parityLaw η p) := by
  constructor
  unfold parityLaw
  rw [Measure.sum_apply _ MeasurableSet.univ]
  simp only [Measure.smul_apply, Measure.dirac_apply_of_mem (Set.mem_univ _), smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_tsum_of_nonneg (mass_nonneg η hη p) (mass_hasSum η hη p).summable,
    (mass_hasSum η hη p).tsum_eq, ENNReal.ofReal_one]

instance bern_prob : IsProbabilityMeasure (finiteLaw (fun _ : Bool => (1/2 : ℝ))) := by
  constructor
  unfold finiteLaw
  simp only [Measure.coe_finset_sum, Finset.sum_apply, Measure.smul_apply,
    Measure.dirac_apply_of_mem (Set.mem_univ _), smul_eq_mul, mul_one, Finset.sum_const,
    Finset.card_univ, Fintype.card_bool, nsmul_eq_mul]
  rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by norm_num)]; norm_num

lemma pathLaw_prob (η : ℝ) (hη : 0 ≤ η) (p : Bool) : IsProbabilityMeasure (pathLaw η p) := by
  haveI := parityLaw_prob η hη p
  unfold pathLaw; infer_instance

def Bp {n : ℕ} (J : Matrix (Fin n) (Fin n) ℝ) (h : Fin n → ℝ) : ℝ :=
  (1/2) * ∑ i, ∑ j, |J i j| + ∑ i, |h i|

lemma pot_bound {n : ℕ} (J : Matrix (Fin n) (Fin n) ℝ) (h : Fin n → ℝ) (s : Fin n → ℝ)
    (hs : ∀ i, |s i| ≤ 1) : |potential J h s| ≤ Bp J h := by
  unfold potential Bp
  refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
  · rw [abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 1/2)]
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun i _ => ?_))
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun j _ => ?_))
    rw [abs_mul, abs_mul]
    calc |J i j| * |s i| * |s j| ≤ |J i j| * 1 * 1 := by
          gcongr
          · exact hs i
          · exact hs j
      _ = |J i j| := by ring
  · refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun i _ => ?_))
    rw [abs_mul]
    calc |h i| * |s i| ≤ |h i| * 1 := by gcongr; exact hs i
      _ = |h i| := by ring

lemma pathValue_abs (σ : PathData) (t : ℝ) : |pathValue σ t| = 1 := by
  rw [pathValue_spin]; cases pathBits σ t <;> simp [spin]

lemma pot_cont {n : ℕ} (J : Matrix (Fin n) (Fin n) ℝ) (h : Fin n → ℝ) : Continuous (potential J h) := by
  unfold potential; fun_prop

lemma pathValue_meas_t (σ : PathData) : Measurable (fun t : ℝ => pathValue σ t) := by
  unfold pathValue
  apply Measurable.const_mul
  apply (measurable_of_countable (fun n : ℕ => (-1 : ℝ) ^ n)).comp
  have : (fun t : ℝ => ((Finset.range σ.1).filter (fun k => σ.2.2 k ≤ t)).card) =
      fun t => ∑ k ∈ Finset.range σ.1, (if σ.2.2 k ≤ t then 1 else 0) := by
    funext t; rw [Finset.card_filter]
  rw [this]
  exact Finset.measurable_sum _ (fun k _ => Measurable.ite (measurableSet_le measurable_const measurable_id)
    measurable_const measurable_const)

lemma meshPot_meas {n : ℕ} (J : Matrix (Fin n) (Fin n) ℝ) (h : Fin n → ℝ) (M : ℕ) :
    Measurable (fun σ : Fin n → PathData => meshPotential J h M σ) := by
  unfold meshPotential
  apply Measurable.const_mul
  apply Finset.measurable_sum; intro k _
  exact (pot_cont J h).measurable.comp
    (measurable_pi_lambda _ (fun i => (pathValue_meas' _).comp (measurable_pi_apply i)))

lemma pathSign_meas {n : ℕ} (P : Fin n → Pauli) : Measurable (fun σ : Fin n → PathData => pathSign P σ) := by
  unfold pathSign
  apply Finset.measurable_prod; intro i _
  by_cases hc : P i = .Y ∨ P i = .Z
  · simp only [hc, if_true]; exact (pathValue_meas' 0).comp (measurable_pi_apply i)
  · simp only [hc, if_false]; exact measurable_const

lemma pathSign_abs {n : ℕ} (P : Fin n → Pauli) (σ : Fin n → PathData) : |pathSign P σ| ≤ 1 := by
  unfold pathSign
  rw [Finset.abs_prod]
  apply Finset.prod_le_one (fun i _ => abs_nonneg _)
  intro i _
  split_ifs
  · rw [pathValue_abs]
  · simp

lemma meshPot_abs {n : ℕ} (J : Matrix (Fin n) (Fin n) ℝ) (h : Fin n → ℝ) (M : ℕ) (σ : Fin n → PathData) :
    |meshPotential J h M σ| ≤ Bp J h := by
  have hB0 : 0 ≤ Bp J h := le_trans (abs_nonneg _) (pot_bound J h (fun _ => 0) (fun _ => by simp))
  unfold meshPotential
  rcases Nat.eq_zero_or_pos M with hM | hM
  · subst hM; simp [hB0]
  have hMr : (0:ℝ) < M := by exact_mod_cast hM
  rw [abs_mul, abs_of_pos (by positivity)]
  calc 1 / (M:ℝ) * |∑ k : Fin M, potential J h (fun i => pathValue (σ i) (k.val / M))|
      ≤ 1 / (M:ℝ) * ∑ k : Fin M, Bp J h := by
        gcongr
        refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun k _ => ?_))
        exact pot_bound J h _ (fun i => (pathValue_abs _ _).le)
    _ = Bp J h := by simp; field_simp


def Rw {n : ℕ} (J : Matrix (Fin n) (Fin n) ℝ) (h : Fin n → ℝ) (k : Fin n) : ℝ :=
  (∑ j ∈ Finset.univ.erase k, |J k j|) + |h k|

lemma Rw_le {n : ℕ} (J : Matrix (Fin n) (Fin n) ℝ) (h : Fin n → ℝ) (k : Fin n) :
    2 * Rw J h k ≤ trotterConstant J h := by
  unfold trotterConstant
  have : Rw J h k ≤ ⨆ i, ((∑ j ∈ Finset.univ.erase i, |J i j|) + |h i|) :=
    le_ciSup (Set.finite_range _).bddAbove k
  linarith

lemma offdiag_split {n : ℕ} (J : Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ) :
    ∑ k, ∑ l, J k l * x k * x l = ∑ k, J k k * (x k * x k) +
      ∑ k, ∑ l ∈ Finset.univ.erase k, J k l * x k * x l := by
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro k _
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ k)]; ring

lemma pot_lip {n : ℕ} (J : Matrix (Fin n) (Fin n) ℝ) (hJ : J.IsSymm) (h : Fin n → ℝ)
    (x y : Fin n → ℝ) (hx : ∀ k, x k * x k = 1) (hy : ∀ k, y k * y k = 1)
    (hxa : ∀ k, |x k| ≤ 1) (hya : ∀ k, |y k| ≤ 1) :
    |potential J h x - potential J h y| ≤
      trotterConstant J h * (Finset.univ.filter (fun k => x k ≠ y k)).card := by
  have hsym : ∀ k l, J k l = J l k := fun k l => by
    have := congrFun (congrFun hJ l) k; simpa [Matrix.transpose_apply] using this
  set D := Finset.univ.filter (fun k => x k ≠ y k)
  have hd : ∀ k, |x k - y k| ≤ 2 * (if k ∈ D then 1 else 0) := by
    intro k
    by_cases hk : x k = y k
    · simp [D, hk]
    · have : k ∈ D := by simp [D, hk]
      rw [if_pos this]
      calc |x k - y k| ≤ |x k| + |y k| := abs_sub _ _
        _ ≤ 2 * 1 := by linarith [hxa k, hya k]
  have hdiag : ∑ k, J k k * (x k * x k) = ∑ k, J k k * (y k * y k) := by
    simp [hx, hy]
  -- difference of off-diagonal parts
  have hoff : ∑ k, ∑ l ∈ Finset.univ.erase k, J k l * x k * x l -
      ∑ k, ∑ l ∈ Finset.univ.erase k, J k l * y k * y l =
      ∑ k, ∑ l ∈ Finset.univ.erase k, J k l * ((x k - y k) * x l) +
      ∑ k, ∑ l ∈ Finset.univ.erase k, J k l * (y k * (x l - y l)) := by
    rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro k _
    rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro l _; ring
  have hA : |∑ k, ∑ l ∈ Finset.univ.erase k, J k l * ((x k - y k) * x l)| ≤
      ∑ k, 2 * (if k ∈ D then 1 else 0) * ∑ l ∈ Finset.univ.erase k, |J k l| := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun k _ => ?_))
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum; intro l _
    rw [abs_mul, abs_mul]
    calc |J k l| * (|x k - y k| * |x l|) ≤ |J k l| * (2 * (if k ∈ D then 1 else 0) * 1) := by
          gcongr
          · exact hd k
          · exact hxa l
      _ = 2 * (if k ∈ D then 1 else 0) * |J k l| := by ring
  have hB : |∑ k, ∑ l ∈ Finset.univ.erase k, J k l * (y k * (x l - y l))| ≤
      ∑ l, 2 * (if l ∈ D then 1 else 0) * ∑ k ∈ Finset.univ.erase l, |J l k| := by
    have hswap : ∀ f : Fin n → Fin n → ℝ, ∑ k, ∑ l ∈ Finset.univ.erase k, f k l =
        ∑ l, ∑ k ∈ Finset.univ.erase l, f k l := by
      intro f
      have e : ∀ k, ∑ l ∈ Finset.univ.erase k, f k l = ∑ l, if l ≠ k then f k l else 0 := by
        intro k; rw [Finset.sum_ite, Finset.sum_const_zero, add_zero]; congr 1; ext l; simp
      have e' : ∀ l, ∑ k ∈ Finset.univ.erase l, f k l = ∑ k, if l ≠ k then f k l else 0 := by
        intro l; rw [Finset.sum_ite, Finset.sum_const_zero, add_zero]; congr 1; ext k; simp [eq_comm]
      simp only [e, e']; exact Finset.sum_comm
    rw [hswap]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun l _ => ?_))
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum; intro k _
    rw [abs_mul, abs_mul, hsym k l]
    calc |J l k| * (|y k| * |x l - y l|) ≤ |J l k| * (1 * (2 * (if l ∈ D then 1 else 0))) := by
          gcongr
          · exact hya k
          · exact hd l
      _ = 2 * (if l ∈ D then 1 else 0) * |J l k| := by ring
  have hC : |∑ k, h k * x k - ∑ k, h k * y k| ≤ ∑ k, 2 * (if k ∈ D then 1 else 0) * |h k| := by
    rw [← Finset.sum_sub_distrib]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun k _ => ?_))
    rw [← mul_sub, abs_mul]
    calc |h k| * |x k - y k| ≤ |h k| * (2 * (if k ∈ D then 1 else 0)) := by gcongr; exact hd k
      _ = _ := by ring
  have htot : |potential J h x - potential J h y| ≤ ∑ k, (if k ∈ D then 1 else 0) * (2 * Rw J h k) := by
    unfold potential
    rw [offdiag_split, offdiag_split J y, hdiag]
    have e : 1 / 2 * (∑ k, J k k * (y k * y k) + ∑ k, ∑ l ∈ Finset.univ.erase k, J k l * x k * x l) +
        ∑ k, h k * x k - (1 / 2 * (∑ k, J k k * (y k * y k) +
          ∑ k, ∑ l ∈ Finset.univ.erase k, J k l * y k * y l) + ∑ k, h k * y k) =
        1 / 2 * (∑ k, ∑ l ∈ Finset.univ.erase k, J k l * x k * x l -
          ∑ k, ∑ l ∈ Finset.univ.erase k, J k l * y k * y l) +
        (∑ k, h k * x k - ∑ k, h k * y k) := by ring
    rw [e, hoff]
    calc |1 / 2 * (∑ k, ∑ l ∈ Finset.univ.erase k, J k l * ((x k - y k) * x l) +
          ∑ k, ∑ l ∈ Finset.univ.erase k, J k l * (y k * (x l - y l))) +
          (∑ k, h k * x k - ∑ k, h k * y k)|
        ≤ 1 / 2 * (|∑ k, ∑ l ∈ Finset.univ.erase k, J k l * ((x k - y k) * x l)| +
          |∑ k, ∑ l ∈ Finset.univ.erase k, J k l * (y k * (x l - y l))|) +
          |∑ k, h k * x k - ∑ k, h k * y k| := by
          refine (abs_add_le _ _).trans (add_le_add ?_ le_rfl)
          rw [abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 1/2)]
          exact mul_le_mul_of_nonneg_left (abs_add_le _ _) (by norm_num)
      _ ≤ 1 / 2 * (∑ k, 2 * (if k ∈ D then 1 else 0) * ∑ l ∈ Finset.univ.erase k, |J k l| +
          ∑ l, 2 * (if l ∈ D then 1 else 0) * ∑ k ∈ Finset.univ.erase l, |J l k|) +
          ∑ k, 2 * (if k ∈ D then 1 else 0) * |h k| := by gcongr
      _ = ∑ k, (if k ∈ D then 1 else 0) * (2 * Rw J h k) := by
          unfold Rw
          rw [← Finset.sum_add_distrib, Finset.mul_sum, ← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl; intro k _; ring
  refine htot.trans ?_
  rw [Finset.card_filter, Nat.cast_sum, Finset.mul_sum]
  apply Finset.sum_le_sum; intro k _
  by_cases hk : k ∈ D
  · simp only [hk, if_true, one_mul]
    have : x k ≠ y k := (Finset.mem_filter.1 hk).2
    simp only [this, ne_eq, not_false_eq_true, if_true, Nat.cast_one, mul_one]
    exact Rw_le J h k
  · simp only [hk, if_false, zero_mul]
    have : ¬ (x k ≠ y k) := fun h' => hk (Finset.mem_filter.2 ⟨Finset.mem_univ _, h'⟩)
    simp only [this, if_false, Nat.cast_zero, mul_zero, le_refl]


lemma tc_nonneg {n : ℕ} (J : Matrix (Fin n) (Fin n) ℝ) (h : Fin n → ℝ) : 0 ≤ trotterConstant J h := by
  unfold trotterConstant
  have : 0 ≤ ⨆ i, ((∑ j ∈ Finset.univ.erase i, |J i j|) + |h i|) :=
    Real.iSup_nonneg (fun i => by positivity)
  linarith

lemma pot_path_diff {n : ℕ} (J : Matrix (Fin n) (Fin n) ℝ) (hJ : J.IsSymm) (h : Fin n → ℝ)
    (σ : Fin n → PathData) (s t : ℝ) (hst : s ≤ t) :
    |potential J h (fun i => pathValue (σ i) t) - potential J h (fun i => pathValue (σ i) s)| ≤
      trotterConstant J h * ∑ i, (((Finset.range (σ i).1).filter
        (fun j => s < (σ i).2.2 j ∧ (σ i).2.2 j ≤ t)).card : ℝ) := by
  have hsq : ∀ (τ : PathData) (r : ℝ), pathValue τ r * pathValue τ r = 1 := by
    intro τ r; rw [pathValue_spin]; cases pathBits τ r <;> simp [spin]
  refine (pot_lip J hJ h _ _ (fun k => hsq _ _) (fun k => hsq _ _)
    (fun k => (pathValue_abs _ _).le) (fun k => (pathValue_abs _ _).le)).trans ?_
  apply mul_le_mul_of_nonneg_left _ (tc_nonneg J h)
  rw [Finset.card_filter, Nat.cast_sum]
  apply Finset.sum_le_sum; intro i _
  by_cases hdiff : pathValue (σ i) t ≠ pathValue (σ i) s
  · rw [if_pos hdiff]
    simp only [Nat.cast_one, Nat.one_le_cast]
    rw [Nat.one_le_iff_ne_zero]
    intro h0
    apply hdiff
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff] at h0
    unfold pathValue
    congr 2
    congr 1
    apply Finset.filter_congr; intro j hj
    constructor
    · intro hu; by_contra hc; exact h0 hj ⟨lt_of_not_ge hc, hu⟩
    · intro hu; exact le_trans hu hst
  · rw [if_neg hdiff]; simp

def Aset (M : ℕ) (u : ℝ) : Set ℝ := {t | (⌊t * M⌋ : ℝ) / M < u ∧ u ≤ t}

lemma Aset_meas (M : ℕ) (u : ℝ) : MeasurableSet (Aset M u) := by
  apply MeasurableSet.inter
  · exact measurableSet_lt (((measurable_of_countable (fun z : ℤ => (z : ℝ))).comp
      (Int.measurable_floor.comp (measurable_id.mul_const _))).div_const _) measurable_const
  · exact measurableSet_le measurable_const measurable_id

lemma Aset_int (M : ℕ) (hM : 1 ≤ M) (u : ℝ) :
    ∫ t in Set.Icc (0:ℝ) 1, (Aset M u).indicator (1 : ℝ → ℝ) t ≤ 1 / M := by
  have hMr : (0:ℝ) < M := by exact_mod_cast hM
  rw [integral_indicator_one (Aset_meas M u)]
  have hsub : Aset M u ⊆ Set.Ico u (u + 1 / M) := by
    intro t ⟨h1, h2⟩
    refine ⟨h2, ?_⟩
    have hf : t * M < (⌊t * M⌋ : ℝ) + 1 := Int.lt_floor_add_one _
    rw [div_lt_iff₀ hMr] at h1
    have : t * M < u * M + 1 := by linarith
    have : t < u + 1 / M := by
      rw [show u + 1 / M = (u * M + 1) / M by field_simp]
      rw [lt_div_iff₀ hMr]; linarith
    exact this
  have h1M : (0:ℝ) ≤ 1 / M := by positivity
  have hpos : u ≤ u + 1 / M := by linarith
  calc (volume.restrict (Set.Icc (0:ℝ) 1)).real (Aset M u)
        ≤ (volume.restrict (Set.Icc (0:ℝ) 1)).real (Set.Ico u (u + 1 / M)) :=
          measureReal_mono hsub (measure_ne_top _ _)
    _ ≤ volume.real (Set.Ico u (u + 1 / M)) := by
        apply ENNReal.toReal_mono (by rw [Real.volume_Ico]; exact ENNReal.ofReal_ne_top)
        exact Measure.restrict_apply_le _ _
    _ = 1 / M := by rw [Real.volume_real_Ico_of_le hpos]; ring


theorem VM_diff {n : ℕ} (J : Matrix (Fin n) (Fin n) ℝ) (hJ : J.IsSymm) (h : Fin n → ℝ)
    (σ : Fin n → PathData) (M : ℕ) (hM : 1 ≤ M) :
    |pathPotential J h σ - meshPotential J h M σ| ≤
      trotterConstant J h * (∑ i, ((σ i).1 : ℝ)) / M := by
  have hMr : (0:ℝ) < M := by exact_mod_cast hM
  set f : ℝ → ℝ := fun t => potential J h (fun i => pathValue (σ i) t)
  have hfm : Measurable f := (pot_cont J h).measurable.comp
    (measurable_pi_lambda _ (fun i => pathValue_meas_t (σ i)))
  have hB : ∀ t, |f t| ≤ Bp J h := fun t => pot_bound J h _ (fun i => (pathValue_abs (σ i) t).le)
  have hsm : Measurable (stepf f M) := by
    unfold stepf
    exact hfm.comp (((measurable_of_countable (fun z : ℤ => (z : ℝ))).comp
      (Int.measurable_floor.comp (measurable_id.mul_const _))).div_const _)
  have hint : ∀ g : ℝ → ℝ, Measurable g → (∀ t, |g t| ≤ Bp J h) →
      Integrable g (volume.restrict (Set.Icc (0:ℝ) 1)) := by
    intro g hg hgB
    exact Measure.integrableOn_of_bounded (M := Bp J h) (by simp) hg.aestronglyMeasurable
      (Eventually.of_forall (fun t => by rw [Real.norm_eq_abs]; exact hgB t))
  have hmesh : meshPotential J h M σ = ∫ t in Set.Icc (0:ℝ) 1, stepf f M t :=
    riemann_eq f (Bp J h) hB hfm M hM
  have hpath : pathPotential J h σ = ∫ t in Set.Icc (0:ℝ) 1, f t := rfl
  rw [hmesh, hpath, ← integral_sub (hint f hfm hB) (hint _ hsm (fun t => hB _))]
  have hind : ∀ u, Integrable ((Aset M u).indicator (1 : ℝ → ℝ)) (volume.restrict (Set.Icc (0:ℝ) 1)) :=
    fun u => (integrable_const (1:ℝ)).indicator (Aset_meas M u)
  set g : ℝ → ℝ := fun t => trotterConstant J h *
    ∑ i, ∑ j ∈ Finset.range (σ i).1, (Aset M ((σ i).2.2 j)).indicator (1 : ℝ → ℝ) t
  have hgm : Measurable g := by
    apply Measurable.const_mul
    exact Finset.measurable_sum _ (fun i _ => Finset.measurable_sum _ (fun j _ =>
      (measurable_const.indicator (Aset_meas M _))))
  have hgi : Integrable g (volume.restrict (Set.Icc (0:ℝ) 1)) := by
    apply Integrable.const_mul
    exact integrable_finset_sum _ (fun i _ => integrable_finset_sum _ (fun j _ => hind _))
  have hpt : ∀ t, |f t - stepf f M t| ≤ g t := by
    intro t
    have hst : (⌊t * M⌋ : ℝ) / M ≤ t := by
      rw [div_le_iff₀ hMr]; exact Int.floor_le _
    refine (pot_path_diff J hJ h σ _ t hst).trans (le_of_eq ?_)
    simp only [g]
    congr 1
    apply Finset.sum_congr rfl; intro i _
    rw [Finset.card_filter, Nat.cast_sum]
    apply Finset.sum_congr rfl; intro j _
    simp only [Set.indicator, Aset, Set.mem_setOf_eq, Pi.one_apply]
    split_ifs <;> simp
  calc |∫ t in Set.Icc (0:ℝ) 1, (f t - stepf f M t)|
      ≤ ∫ t in Set.Icc (0:ℝ) 1, |f t - stepf f M t| := abs_integral_le_integral_abs
    _ ≤ ∫ t in Set.Icc (0:ℝ) 1, g t := by
        apply integral_mono ((hint f hfm hB).sub (hint _ hsm (fun t => hB _))).abs hgi
        exact hpt
    _ = trotterConstant J h * ∑ i, ∑ j ∈ Finset.range (σ i).1,
          ∫ t in Set.Icc (0:ℝ) 1, (Aset M ((σ i).2.2 j)).indicator (1 : ℝ → ℝ) t := by
        simp only [g]
        rw [integral_const_mul, integral_finset_sum _ (fun i _ => integrable_finset_sum _ (fun j _ => hind _))]
        congr 1
        apply Finset.sum_congr rfl; intro i _
        exact integral_finset_sum _ (fun j _ => hind _)
    _ ≤ trotterConstant J h * ∑ i, ∑ j ∈ Finset.range (σ i).1, (1 / (M:ℝ)) := by
        apply mul_le_mul_of_nonneg_left _ (tc_nonneg J h)
        exact Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => Aset_int M hM _))
    _ = trotterConstant J h * (∑ i, ((σ i).1 : ℝ)) / M := by
        simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        rw [Finset.mul_sum, Finset.mul_sum, Finset.sum_div]
        apply Finset.sum_congr rfl; intro i _; ring


lemma sinh_le_mul_cosh (c : ℝ) (hc : 0 ≤ c) : Real.sinh c ≤ c * Real.cosh c := by
  have h1 := Real.hasSum_sinh c
  have h2 := (Real.hasSum_cosh c).mul_left c
  refine hasSum_le (fun k => ?_) h1 h2
  rw [mul_div_assoc', ← pow_succ']
  apply div_le_div_of_nonneg_left (by positivity) (by positivity)
  exact_mod_cast Nat.factorial_le (by omega)

lemma e_bound : Real.exp 1 - 1 ≤ 2 := by
  have := Real.exp_one_lt_d9; linarith

lemma cosh_ratio (η : ℝ) (hη : 0 ≤ η) :
    Real.cosh (Real.exp 1 * η) ≤ Real.exp (1 + 2 * η) * Real.cosh η := by
  set c := (Real.exp 1 - 1) * η
  have hc : 0 ≤ c := mul_nonneg (by linarith [Real.add_one_le_exp (1:ℝ)]) hη
  have e : Real.exp 1 * η = η + c := by simp only [c]; ring
  rw [e, Real.cosh_add]
  have hsc : Real.sinh η ≤ Real.cosh η := by
    have := Real.cosh_sub_sinh η; have := Real.exp_pos (-η); linarith
  have hs0 : 0 ≤ Real.sinh c := Real.sinh_nonneg_iff.2 hc
  have hce : Real.cosh c + Real.sinh c = Real.exp c := by rw [Real.cosh_add_sinh]
  have : Real.exp c ≤ Real.exp (1 + 2 * η) := Real.exp_le_exp.2 (by
    simp only [c]; nlinarith [e_bound])
  calc Real.cosh η * Real.cosh c + Real.sinh η * Real.sinh c
      ≤ Real.cosh η * Real.cosh c + Real.cosh η * Real.sinh c := by gcongr
    _ = Real.exp c * Real.cosh η := by rw [← hce]; ring
    _ ≤ Real.exp (1 + 2 * η) * Real.cosh η := by gcongr

lemma sinh_ratio (η : ℝ) (hη : 0 < η) :
    Real.sinh (Real.exp 1 * η) ≤ Real.exp (1 + 2 * η) * Real.sinh η := by
  set c := (Real.exp 1 - 1) * η
  have he1 : 0 ≤ Real.exp 1 - 1 := by linarith [Real.add_one_le_exp (1:ℝ)]
  have hc : 0 ≤ c := mul_nonneg he1 hη.le
  have e : Real.exp 1 * η = η + c := by simp only [c]; ring
  rw [e, Real.sinh_add]
  have hsη : 0 < Real.sinh η := Real.sinh_pos_iff.2 hη
  have hcoth : Real.cosh η ≤ (1 + 1 / η) * Real.sinh η := by
    have h1 := Real.cosh_sub_sinh η
    have h2 : Real.exp (-η) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
    have h3 : η ≤ Real.sinh η := Real.self_le_sinh_iff.2 hη.le
    have h4 : 1 ≤ Real.sinh η / η := by rw [le_div_iff₀ hη]; linarith
    have : (1 + 1 / η) * Real.sinh η = Real.sinh η + Real.sinh η / η := by field_simp
    rw [this]; linarith
  have hs0 : 0 ≤ Real.sinh c := Real.sinh_nonneg_iff.2 hc
  have hsc := sinh_le_mul_cosh c hc
  have hce : Real.cosh c + Real.sinh c = Real.exp c := by rw [Real.cosh_add_sinh]
  have hcexp : Real.cosh c ≤ Real.exp c := by linarith
  have hexp : Real.exp 1 * Real.exp c ≤ Real.exp (1 + 2 * η) := by
    rw [← Real.exp_add]; apply Real.exp_le_exp.2; simp only [c]; nlinarith [e_bound]
  have hcη : Real.sinh c / η ≤ (Real.exp 1 - 1) * Real.cosh c := by
    rw [div_le_iff₀ hη]; simp only [c] at hsc ⊢; nlinarith [Real.cosh_pos c]
  calc Real.sinh η * Real.cosh c + Real.cosh η * Real.sinh c
      ≤ Real.sinh η * Real.cosh c + ((1 + 1 / η) * Real.sinh η) * Real.sinh c := by gcongr
    _ = Real.sinh η * (Real.cosh c + Real.sinh c + Real.sinh c / η) := by field_simp; ring
    _ ≤ Real.sinh η * (Real.exp c + (Real.exp 1 - 1) * Real.exp c) := by
        apply mul_le_mul_of_nonneg_left _ hsη.le
        rw [hce]; nlinarith
    _ = Real.exp 1 * Real.exp c * Real.sinh η := by ring
    _ ≤ Real.exp (1 + 2 * η) * Real.sinh η := by gcongr


lemma mgf_hasSum (η : ℝ) (hη : 0 ≤ η) (p : Bool) :
    ∃ S : ℝ, S ≤ Real.exp (1 + 2 * η) ∧
      HasSum (fun d => parityMass η p d * Real.exp d) S := by
  by_cases h0 : η = 0
  · subst h0
    refine ⟨Real.exp (if p then 1 else 0), ?_, ?_⟩
    · apply Real.exp_le_exp.2; split_ifs <;> norm_num
    · have : (fun d : ℕ => parityMass 0 p d * Real.exp d) =
          fun d => if d = (if p then 1 else 0) then Real.exp (if p then 1 else 0) else 0 := by
        funext d; simp only [parityMass, if_true]
        split_ifs with h1 h2 <;> simp_all
      rw [this]
      exact hasSum_ite_eq _ _
  have hpos : 0 < η := lt_of_le_of_ne hη (Ne.symm h0)
  have hed : ∀ d : ℕ, Real.exp d = Real.exp 1 ^ d := fun d => by rw [← Real.exp_nat_mul, mul_one]
  cases p
  · refine ⟨Real.cosh (Real.exp 1 * η) / Real.cosh η, ?_, ?_⟩
    · rw [div_le_iff₀ (Real.cosh_pos _)]; exact cosh_ratio η hη
    · have hc := (Real.hasSum_cosh (Real.exp 1 * η)).div_const (Real.cosh η)
      rw [← (Function.Injective.hasSum_iff (g := fun m : ℕ => 2 * m) (fun a b h => by simpa using h) _)]
      · have e : (fun d => parityMass η false d * Real.exp d) ∘ (fun m : ℕ => 2 * m) =
            fun i => (Real.exp 1 * η) ^ (2 * i) / ↑(2 * i)! / Real.cosh η := by
          funext m; simp only [Function.comp, parityMass, h0, if_false, Bool.false_eq_true]
          rw [if_pos (by omega), hed, mul_pow]; field_simp
        rw [e]; exact hc
      · intro x hx
        simp only [parityMass, h0, if_false, Bool.false_eq_true]
        rw [if_neg, zero_mul]; intro h; exact hx ⟨x / 2, by show 2 * (x / 2) = x; omega⟩
  · refine ⟨Real.sinh (Real.exp 1 * η) / Real.sinh η, ?_, ?_⟩
    · rw [div_le_iff₀ (Real.sinh_pos_iff.2 hpos)]; exact sinh_ratio η hpos
    · have hc := (Real.hasSum_sinh (Real.exp 1 * η)).div_const (Real.sinh η)
      rw [← (Function.Injective.hasSum_iff (g := fun m : ℕ => 2 * m + 1) (fun a b h => by simpa using h) _)]
      · have e : (fun d => parityMass η true d * Real.exp d) ∘ (fun m : ℕ => 2 * m + 1) =
            fun i => (Real.exp 1 * η) ^ (2 * i + 1) / ↑(2 * i + 1)! / Real.sinh η := by
          funext m; simp only [Function.comp, parityMass, h0, if_false, if_true]
          rw [if_pos (by omega), hed, mul_pow]; field_simp
        rw [e]; exact hc
      · intro x hx
        simp only [parityMass, h0, if_false, if_true]
        rw [if_neg, zero_mul]; intro h; exact hx ⟨x / 2, by show 2 * (x / 2) + 1 = x; omega⟩

lemma site_mgf (η : ℝ) (hη : 0 ≤ η) (p : Bool) :
    Integrable (fun σ : PathData => Real.exp σ.1) (pathLaw η p) ∧
      ∫ σ, Real.exp σ.1 ∂pathLaw η p ≤ Real.exp (1 + 2 * η) := by
  obtain ⟨S, hSle, hS⟩ := mgf_hasSum η hη p
  have hnn : ∀ d : ℕ, 0 ≤ parityMass η p d * Real.exp d := fun d =>
    mul_nonneg (mass_nonneg η hη p d) (Real.exp_pos _).le
  haveI := pathLaw_prob η hη p
  have hlin : ∫⁻ σ : PathData, ENNReal.ofReal (Real.exp σ.1) ∂pathLaw η p = ENNReal.ofReal S := by
    unfold pathLaw
    rw [lintegral_prod _ (by
      exact (ENNReal.measurable_ofReal.comp ((measurable_of_countable (fun d : ℕ => Real.exp d)).comp
        measurable_fst)).aemeasurable)]
    simp only [lintegral_const, measure_univ, mul_one]
    unfold parityLaw
    rw [lintegral_sum_measure]
    simp only [lintegral_smul_measure, lintegral_dirac, smul_eq_mul]
    rw [← hS.tsum_eq, ENNReal.ofReal_tsum_of_nonneg hnn hS.summable]
    congr 1; funext d
    rw [ENNReal.ofReal_mul (mass_nonneg η hη p d)]
  have hmeas : AEStronglyMeasurable (fun σ : PathData => Real.exp σ.1) (pathLaw η p) :=
    ((measurable_of_countable (fun d : ℕ => Real.exp d)).comp measurable_fst).aestronglyMeasurable
  have hint : Integrable (fun σ : PathData => Real.exp σ.1) (pathLaw η p) := by
    refine ⟨hmeas, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (Eventually.of_forall (fun σ => (Real.exp_pos _).le)), hlin]
    exact ENNReal.ofReal_lt_top
  refine ⟨hint, ?_⟩
  rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall (fun σ => (Real.exp_pos _).le)) hmeas,
    hlin, ENNReal.toReal_ofReal (hS.nonneg hnn)]
  exact hSle


lemma total_mgf {n : ℕ} (η : Fin n → ℝ) (hη : ∀ i, 0 ≤ η i) (P : Fin n → Pauli) :
    Integrable (fun σ : Fin n → PathData => Real.exp (∑ i, ((σ i).1 : ℝ))) (nu η P) ∧
      ∫ σ, Real.exp (∑ i, ((σ i).1 : ℝ)) ∂nu η P ≤ Real.exp (n + 2 * ∑ i, η i) := by
  have he : (fun σ : Fin n → PathData => Real.exp (∑ i, ((σ i).1 : ℝ))) =
      fun σ => ∏ i, (fun (_ : Fin n) (τ : PathData) => Real.exp τ.1) i (σ i) := by
    funext σ; rw [Real.exp_sum]
  haveI : ∀ i, IsProbabilityMeasure (pathLaw (η i) (hasFlip (P i))) :=
    fun i => pathLaw_prob (η i) (hη i) _
  rw [he]
  unfold nu
  refine ⟨Integrable.fintype_prod (fun i => (site_mgf (η i) (hη i) _).1), ?_⟩
  rw [integral_fintype_prod_eq_prod (fun (_ : Fin n) (τ : PathData) => Real.exp τ.1)]
  calc ∏ i, ∫ τ, Real.exp τ.1 ∂pathLaw (η i) (hasFlip (P i)) ≤ ∏ i, Real.exp (1 + 2 * η i) :=
        Finset.prod_le_prod (fun i _ => integral_nonneg (fun τ => (Real.exp_pos _).le))
          (fun i _ => (site_mgf (η i) (hη i) _).2)
    _ = Real.exp (n + 2 * ∑ i, η i) := by
        rw [← Real.exp_sum]; congr 1
        rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, Finset.mul_sum]
        simp

lemma pathValue_joint : Measurable (fun q : PathData × ℝ => pathValue q.1 q.2) := by
  have e : (fun q : PathData × ℝ => pathValue q.1 q.2) =
      (fun r : ℕ × ((Bool × (ℕ → ℝ)) × ℝ) => spin r.2.1.1 *
        (-1 : ℝ) ^ ((Finset.range r.1).filter (fun j => r.2.1.2 j ≤ r.2.2)).card) ∘
        (MeasurableEquiv.prodAssoc : (ℕ × (Bool × (ℕ → ℝ))) × ℝ ≃ᵐ ℕ × ((Bool × (ℕ → ℝ)) × ℝ)) := by
    funext q; rfl
  rw [e]
  refine Measurable.comp ?_ MeasurableEquiv.prodAssoc.measurable
  apply measurable_from_prod_countable_right
  intro d
  simp only
  apply Measurable.mul
  · exact (measurable_of_countable (fun b : Bool => spin b)).comp (measurable_fst.comp measurable_fst)
  · apply (measurable_of_countable (fun n : ℕ => (-1 : ℝ) ^ n)).comp
    have : (fun y : (Bool × (ℕ → ℝ)) × ℝ => ((Finset.range d).filter (fun j => y.1.2 j ≤ y.2)).card) =
        fun y => ∑ j ∈ Finset.range d, (if y.1.2 j ≤ y.2 then 1 else 0) := by
      funext y; rw [Finset.card_filter]
    rw [this]
    exact Finset.measurable_sum _ (fun j _ => Measurable.ite
      (measurableSet_le ((measurable_pi_apply j).comp (measurable_snd.comp measurable_fst)) measurable_snd)
      measurable_const measurable_const)

lemma pathPot_meas {n : ℕ} (J : Matrix (Fin n) (Fin n) ℝ) (h : Fin n → ℝ) :
    Measurable (fun σ : Fin n → PathData => pathPotential J h σ) := by
  have hF : StronglyMeasurable (fun q : (Fin n → PathData) × ℝ =>
      potential J h (fun i => pathValue (q.1 i) q.2)) := by
    apply Measurable.stronglyMeasurable
    exact (pot_cont J h).measurable.comp (measurable_pi_lambda _ (fun i =>
      (pathValue_joint.comp (((measurable_pi_apply i).comp measurable_fst).prodMk measurable_snd) :
        Measurable ((fun q : PathData × ℝ => pathValue q.1 q.2) ∘
          (fun c : (Fin n → PathData) × ℝ => (c.1 i, c.2))))))
  exact (hF.integral_prod_right (ν := volume.restrict (Set.Icc (0:ℝ) 1))).measurable

end TFIMPhaseDiagram.Classical.P9Aux


namespace TFIMPhaseDiagram.Classical.TJAux

theorem tilt_bounds {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (V W N : Ω → ℝ) (hV : Measurable V) (hW : Measurable W) (hN : Measurable N)
    (hN0 : ∀ ω, 0 ≤ N ω) (B0 : ℝ) (hVb : ∀ ω, |V ω| ≤ B0) (R : ℝ)
    (hR : ∀ ω ω', V ω ≤ V ω' + R) (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (hWV : ∀ ω, |W ω - V ω| ≤ q * N ω) (G : ℝ)
    (heN : Integrable (fun ω => Real.exp (N ω)) μ) (hG : ∫ ω, Real.exp (N ω) ∂μ ≤ G) :
    (∫ ω, Real.exp (V ω) ∂μ) * Real.exp (-(q * (R + Real.log G))) ≤ ∫ ω, Real.exp (W ω) ∂μ ∧
      ∫ ω, Real.exp (W ω) ∂μ ≤ (∫ ω, Real.exp (V ω) ∂μ) * Real.exp (q * (R + Real.log G)) := by
  set A := ∫ ω, Real.exp (V ω) ∂μ
  have hexpV_le : ∀ ω, Real.exp (V ω) ≤ Real.exp B0 := fun ω =>
    Real.exp_le_exp.2 (le_of_abs_le (hVb ω))
  have hiV : Integrable (fun ω => Real.exp (V ω)) μ :=
    Integrable.of_bound (Real.measurable_exp.comp hV).aestronglyMeasurable (Real.exp B0)
      (Filter.Eventually.of_forall (fun ω => by
        rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]; exact hexpV_le ω))
  have hA : 0 < A := integral_pos_iff_support_of_nonneg (fun ω => (Real.exp_pos _).le) hiV |>.2 (by
    have : Function.support (fun ω => Real.exp (V ω)) = Set.univ :=
      Set.eq_univ_of_forall (fun ω => (Real.exp_pos _).ne')
    rw [this, measure_univ]; norm_num)
  -- integrable products
  have hiVN : Integrable (fun ω => Real.exp (V ω) * Real.exp (N ω)) μ :=
    heN.bdd_mul (c := Real.exp B0) (Real.measurable_exp.comp hV).aestronglyMeasurable
      (Filter.Eventually.of_forall (fun ω => by
        rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]; exact hexpV_le ω))
  have hN_le : ∀ ω, N ω ≤ Real.exp (N ω) := fun ω => by
    linarith [Real.add_one_le_exp (N ω)]
  have hiN : Integrable N μ := heN.mono' hN.aestronglyMeasurable
    (Filter.Eventually.of_forall (fun ω => by rw [Real.norm_eq_abs, abs_of_nonneg (hN0 ω)]; exact hN_le ω))
  have hiVNl : Integrable (fun ω => Real.exp (V ω) * N ω) μ :=
    hiN.bdd_mul (c := Real.exp B0) (Real.measurable_exp.comp hV).aestronglyMeasurable
      (Filter.Eventually.of_forall (fun ω => by
        rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]; exact hexpV_le ω))
  have hWup : ∀ ω, Real.exp (W ω) ≤ Real.exp (V ω) * Real.exp (q * N ω) := fun ω => by
    rw [← Real.exp_add]; apply Real.exp_le_exp.2; linarith [le_of_abs_le (hWV ω)]
  have hWlo : ∀ ω, Real.exp (V ω) * Real.exp (-(q * N ω)) ≤ Real.exp (W ω) := fun ω => by
    rw [← Real.exp_add]; apply Real.exp_le_exp.2
    have := neg_abs_le (W ω - V ω); linarith [hWV ω]
  have hqN : ∀ ω, Real.exp (q * N ω) ≤ Real.exp (N ω) := fun ω =>
    Real.exp_le_exp.2 (by nlinarith [hN0 ω])
  have hiVqN : Integrable (fun ω => Real.exp (V ω) * Real.exp (q * N ω)) μ :=
    hiVN.mono' ((Real.measurable_exp.comp hV).mul (Real.measurable_exp.comp (hN.const_mul q))).aestronglyMeasurable
      (Filter.Eventually.of_forall (fun ω => by
        rw [Real.norm_eq_abs, abs_of_pos (by positivity)]
        exact mul_le_mul_of_nonneg_left (hqN ω) (Real.exp_pos _).le))
  have hiW : Integrable (fun ω => Real.exp (W ω)) μ :=
    hiVqN.mono' (Real.measurable_exp.comp hW).aestronglyMeasurable
      (Filter.Eventually.of_forall (fun ω => by
        rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]; exact hWup ω))
  have hiVmqN : Integrable (fun ω => Real.exp (V ω) * Real.exp (-(q * N ω))) μ :=
    hiV.mono' ((Real.measurable_exp.comp hV).mul (Real.measurable_exp.comp (hN.const_mul q).neg)).aestronglyMeasurable
      (Filter.Eventually.of_forall (fun ω => by
        rw [Real.norm_eq_abs, abs_of_pos (by positivity)]
        calc Real.exp (V ω) * Real.exp (-(q * N ω)) ≤ Real.exp (V ω) * 1 :=
              mul_le_mul_of_nonneg_left (Real.exp_le_one_iff.2 (by nlinarith [hN0 ω])) (Real.exp_pos _).le
          _ = Real.exp (V ω) := mul_one _))
  -- key quantities
  set E1 := ∫ ω, Real.exp (V ω) * Real.exp (N ω) ∂μ
  set m := E1 / A
  have hE1pos : 0 < E1 := by
    apply integral_pos_iff_support_of_nonneg (fun ω => by positivity) hiVN |>.2
    have : Function.support (fun ω => Real.exp (V ω) * Real.exp (N ω)) = Set.univ :=
      Set.eq_univ_of_forall (fun ω => (mul_pos (Real.exp_pos _) (Real.exp_pos _)).ne')
    rw [this, measure_univ]; norm_num
  have hm : 0 < m := div_pos hE1pos hA
  have hEV : ∀ ω, Real.exp (V ω) ≤ Real.exp R * A := by
    intro ω
    have : ∫ ω', Real.exp (V ω) ∂μ ≤ ∫ ω', Real.exp R * Real.exp (V ω') ∂μ := by
      apply integral_mono (integrable_const _) (hiV.const_mul _)
      intro ω'; simp only; rw [← Real.exp_add]; apply Real.exp_le_exp.2; linarith [hR ω ω']
    rw [integral_const, integral_const_mul] at this
    simpa using this
  have hGpos : 0 < G := lt_of_lt_of_le (integral_pos_iff_support_of_nonneg
    (fun ω => (Real.exp_pos _).le) heN |>.2 (by
      have : Function.support (fun ω => Real.exp (N ω)) = Set.univ :=
        Set.eq_univ_of_forall (fun ω => (Real.exp_pos _).ne')
      rw [this, measure_univ]; norm_num)) hG
  have hmle : m ≤ Real.exp R * G := by
    rw [div_le_iff₀ hA]
    calc E1 ≤ ∫ ω, Real.exp R * A * Real.exp (N ω) ∂μ := by
          apply integral_mono hiVN (heN.const_mul _)
          intro ω; exact mul_le_mul_of_nonneg_right (hEV ω) (Real.exp_pos _).le
      _ = Real.exp R * A * ∫ ω, Real.exp (N ω) ∂μ := integral_const_mul _ _
      _ ≤ Real.exp R * A * G := by gcongr
      _ = Real.exp R * G * A := by ring
  have hlogm : Real.log m ≤ R + Real.log G := by
    rw [← Real.log_exp R, ← Real.log_mul (Real.exp_pos _).ne' hGpos.ne']
    exact Real.log_le_log hm hmle
  constructor
  · -- lower bound
    set m' := (∫ ω, Real.exp (V ω) * N ω ∂μ) / A
    have htan : ∀ ω, Real.exp (-(q * m')) * (1 - q * N ω + q * m') ≤ Real.exp (-(q * N ω)) := by
      intro ω
      have := Real.add_one_le_exp (-(q * N ω) + q * m')
      calc Real.exp (-(q * m')) * (1 - q * N ω + q * m')
          ≤ Real.exp (-(q * m')) * Real.exp (-(q * N ω) + q * m') := by
            apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le; linarith
        _ = Real.exp (-(q * N ω)) := by rw [← Real.exp_add]; ring_nf
    have hlow1 : A * Real.exp (-(q * m')) ≤ ∫ ω, Real.exp (V ω) * Real.exp (-(q * N ω)) ∂μ := by
      have : ∫ ω, Real.exp (V ω) * (Real.exp (-(q * m')) * (1 - q * N ω + q * m')) ∂μ =
          A * Real.exp (-(q * m')) := by
        have e : (fun ω => Real.exp (V ω) * (Real.exp (-(q * m')) * (1 - q * N ω + q * m'))) =
            fun ω => Real.exp (-(q * m')) * (1 + q * m') * Real.exp (V ω) -
              Real.exp (-(q * m')) * q * (Real.exp (V ω) * N ω) := by
          funext ω; ring
        rw [e, integral_sub (hiV.const_mul _) (hiVNl.const_mul _), integral_const_mul,
          integral_const_mul]
        simp only [m']; field_simp; ring
      rw [← this]
      apply integral_mono _ hiVmqN
      · intro ω; exact mul_le_mul_of_nonneg_left (htan ω) (Real.exp_pos _).le
      · have e : (fun ω => Real.exp (V ω) * (Real.exp (-(q * m')) * (1 - q * N ω + q * m'))) =
            fun ω => Real.exp (-(q * m')) * (1 + q * m') * Real.exp (V ω) -
              Real.exp (-(q * m')) * q * (Real.exp (V ω) * N ω) := by
          funext ω; ring
        rw [e]; exact (hiV.const_mul _).sub (hiVNl.const_mul _)
    have hm'le : m' ≤ Real.log m := by
      have htan2 : ∀ ω, Real.exp m' * (1 + N ω - m') ≤ Real.exp (N ω) := by
        intro ω
        have := Real.add_one_le_exp (N ω - m')
        calc Real.exp m' * (1 + N ω - m') ≤ Real.exp m' * Real.exp (N ω - m') := by
              apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le; linarith
          _ = Real.exp (N ω) := by rw [← Real.exp_add]; ring_nf
      have : A * Real.exp m' ≤ E1 := by
        have e : (fun ω => Real.exp (V ω) * (Real.exp m' * (1 + N ω - m'))) =
            fun ω => Real.exp m' * (1 - m') * Real.exp (V ω) + Real.exp m' * (Real.exp (V ω) * N ω) := by
          funext ω; ring
        have hval : ∫ ω, Real.exp (V ω) * (Real.exp m' * (1 + N ω - m')) ∂μ = A * Real.exp m' := by
          rw [e, integral_add (hiV.const_mul _) (hiVNl.const_mul _), integral_const_mul,
            integral_const_mul]
          simp only [m']; field_simp; ring
        rw [← hval]
        apply integral_mono _ hiVN
        · intro ω; exact mul_le_mul_of_nonneg_left (htan2 ω) (Real.exp_pos _).le
        · rw [e]; exact (hiV.const_mul _).add (hiVNl.const_mul _)
      rw [Real.le_log_iff_exp_le hm, le_div_iff₀ hA]; linarith
    calc A * Real.exp (-(q * (R + Real.log G))) ≤ A * Real.exp (-(q * m')) := by
          apply mul_le_mul_of_nonneg_left _ hA.le
          apply Real.exp_le_exp.2
          have : m' ≤ R + Real.log G := hm'le.trans hlogm
          nlinarith
      _ ≤ ∫ ω, Real.exp (V ω) * Real.exp (-(q * N ω)) ∂μ := hlow1
      _ ≤ ∫ ω, Real.exp (W ω) ∂μ := integral_mono hiVmqN hiW hWlo
  · -- upper bound
    have hbern : ∀ ω, Real.exp (q * N ω) ≤ m ^ q * (1 + q * (Real.exp (N ω) / m - 1)) := by
      intro ω
      have hs : -1 ≤ Real.exp (N ω) / m - 1 := by
        have : 0 ≤ Real.exp (N ω) / m := by positivity
        linarith
      have hb := rpow_one_add_le_one_add_mul_self hs hq0 hq1
      have he : Real.exp (q * N ω) = m ^ q * (1 + (Real.exp (N ω) / m - 1)) ^ q := by
        rw [show 1 + (Real.exp (N ω) / m - 1) = Real.exp (N ω) / m by ring,
          Real.div_rpow (Real.exp_pos _).le hm.le, ← Real.exp_mul]
        field_simp
      rw [he]
      exact mul_le_mul_of_nonneg_left hb (by positivity)
    have hint2 : Integrable (fun ω => Real.exp (V ω) * (m ^ q * (1 + q * (Real.exp (N ω) / m - 1)))) μ := by
      have e : (fun ω => Real.exp (V ω) * (m ^ q * (1 + q * (Real.exp (N ω) / m - 1)))) =
          fun ω => m ^ q * (1 - q) * Real.exp (V ω) + m ^ q * q / m * (Real.exp (V ω) * Real.exp (N ω)) := by
        funext ω; field_simp; ring
      rw [e]; exact (hiV.const_mul _).add (hiVN.const_mul _)
    calc ∫ ω, Real.exp (W ω) ∂μ ≤ ∫ ω, Real.exp (V ω) * Real.exp (q * N ω) ∂μ :=
          integral_mono hiW hiVqN hWup
      _ ≤ ∫ ω, Real.exp (V ω) * (m ^ q * (1 + q * (Real.exp (N ω) / m - 1))) ∂μ :=
          integral_mono hiVqN hint2 (fun ω => mul_le_mul_of_nonneg_left (hbern ω) (Real.exp_pos _).le)
      _ = A * m ^ q := by
          have e : (fun ω => Real.exp (V ω) * (m ^ q * (1 + q * (Real.exp (N ω) / m - 1)))) =
              fun ω => m ^ q * (1 - q) * Real.exp (V ω) + m ^ q * q / m * (Real.exp (V ω) * Real.exp (N ω)) := by
            funext ω; field_simp; ring
          rw [e, integral_add (hiV.const_mul _) (hiVN.const_mul _), integral_const_mul, integral_const_mul]
          simp only [m]; field_simp; ring
      _ ≤ A * Real.exp (q * (R + Real.log G)) := by
          apply mul_le_mul_of_nonneg_left _ hA.le
          rw [Real.rpow_def_of_pos hm]
          apply Real.exp_le_exp.2
          nlinarith

end TFIMPhaseDiagram.Classical.TJAux

namespace TFIMPhaseDiagram.Classical.P9Fin
open TFIMPhaseDiagram.Classical TFIMPhaseDiagram.Classical.P9Aux TFIMPhaseDiagram.Classical.RSAux
  TFIMPhaseDiagram.Classical.TJAux MeasureTheory Filter

lemma pathPot_abs {n : ℕ} (J : Matrix (Fin n) (Fin n) ℝ) (h : Fin n → ℝ) (σ : Fin n → PathData) :
    |pathPotential J h σ| ≤ Bp J h := by
  unfold pathPotential
  have := norm_setIntegral_le_of_norm_le_const (μ := volume) (s := Set.Icc (0:ℝ) 1)
    (f := fun t => potential J h (fun i => pathValue (σ i) t)) (C := Bp J h) (by simp)
    (fun t _ => by rw [Real.norm_eq_abs]; exact pot_bound J h _ (fun i => (pathValue_abs (σ i) t).le))
  rw [Real.norm_eq_abs] at this
  simpa using this

lemma V_range {n : ℕ} (J : Matrix (Fin n) (Fin n) ℝ) (hJ : J.IsSymm) (h : Fin n → ℝ)
    (σ σ' : Fin n → PathData) :
    pathPotential J h σ ≤ pathPotential J h σ' + trotterConstant J h * n := by
  have hsq : ∀ (τ : PathData) (r : ℝ), pathValue τ r * pathValue τ r = 1 := by
    intro τ r; rw [pathValue_spin]; cases pathBits τ r <;> simp [spin]
  set f : (Fin n → PathData) → ℝ → ℝ := fun ρ t => potential J h (fun i => pathValue (ρ i) t)
  have hfm : ∀ ρ, Measurable (f ρ) := fun ρ => (pot_cont J h).measurable.comp
    (measurable_pi_lambda _ (fun i => pathValue_meas_t (ρ i)))
  have hint : ∀ ρ, Integrable (f ρ) (volume.restrict (Set.Icc (0:ℝ) 1)) := fun ρ =>
    Measure.integrableOn_of_bounded (M := Bp J h) (by simp) (hfm ρ).aestronglyMeasurable
      (Eventually.of_forall (fun t => by
        rw [Real.norm_eq_abs]; exact pot_bound J h _ (fun i => (pathValue_abs (ρ i) t).le)))
  have hpt : ∀ t, f σ t - f σ' t ≤ trotterConstant J h * n := by
    intro t
    refine (le_abs_self _).trans ((pot_lip J hJ h _ _ (fun k => hsq _ _) (fun k => hsq _ _)
      (fun k => (pathValue_abs _ _).le) (fun k => (pathValue_abs _ _).le)).trans ?_)
    apply mul_le_mul_of_nonneg_left _ (tc_nonneg J h)
    have := Finset.card_filter_le (Finset.univ : Finset (Fin n))
      (fun k => pathValue (σ k) t ≠ pathValue (σ' k) t)
    rw [Finset.card_univ, Fintype.card_fin] at this
    exact_mod_cast this
  have : pathPotential J h σ - pathPotential J h σ' ≤ trotterConstant J h * n := by
    unfold pathPotential
    rw [← integral_sub (hint σ) (hint σ')]
    calc ∫ t in Set.Icc (0:ℝ) 1, (f σ t - f σ' t) ≤ ∫ t in Set.Icc (0:ℝ) 1, trotterConstant J h * n :=
          integral_mono ((hint σ).sub (hint σ')) (integrable_const _) hpt
      _ = trotterConstant J h * n := by simp
  linarith

theorem prop9 {n : ℕ} (hn : 0 < n) (J : Matrix (Fin n) (Fin n) ℝ)
    (hJ : J.IsSymm) (h η : Fin n → ℝ) (hη : ∀ i, 0 ≤ η i)
    (S : Finset (Fin n)) (ε : ℝ) (hε : 0 < ε ∧ ε < 1)
    (M : ℕ) (hM : 3 ≤ M)
    (hmesh : (M : ℝ) ≥ trotterConstant J h *
      ((trotterConstant J h + 1) * n + 2 * ∑ i, |η i|) / ε) :
  (Matrix.trace (xSubset S * matrixExp (hamiltonian J h η))).re * Real.exp (-ε) ≤
    (Matrix.trace (xSubset S * trotter J h η M)).re ∧
  (Matrix.trace (xSubset S * trotter J h η M)).re ≤
    (Matrix.trace (xSubset S * matrixExp (hamiltonian J h η))).re * Real.exp ε := by
  obtain ⟨hε0, hε1⟩ := hε
  set P : Fin n → Pauli := fun i => if i ∈ S then .X else .I
  have hX : xSubset S = pauliString P := rfl
  obtain ⟨hCim, hCre, -, -, h1, h2, -⟩ := TFIMPhaseDiagram.Classical.prop_8 hn J hJ h η hη P M hM
  have hy : yCount P = 0 := by
    unfold yCount; rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro i _; by_cases hi : i ∈ S <;> simp [P, hi]
  have hps : ∀ σ, pathSign P σ = 1 := by
    intro σ; unfold pathSign; apply Finset.prod_eq_one; intro i _
    by_cases hi : i ∈ S <;> simp [P, hi]
  simp only [hy, pow_zero, one_mul, hps, mul_one] at h1 h2
  rw [hX, h1, h2]
  set C := Matrix.trace (xSubset (flipSet P) * matrixExp (hx η))
  set A := ∫ σ, Real.exp (pathPotential J h σ) ∂nu η P
  set B := ∫ σ, Real.exp (meshPotential J h M σ) ∂nu η P
  have hre : ∀ x : ℝ, (C * (x : ℂ)).re = C.re * x := by
    intro x; simp [Complex.mul_re, hCim]
  rw [hre, hre]
  -- the core estimate
  haveI : ∀ i, IsProbabilityMeasure (pathLaw (η i) (hasFlip (P i))) :=
    fun i => pathLaw_prob (η i) (hη i) _
  haveI : IsProbabilityMeasure (nu η P) := by unfold nu; infer_instance
  set c := trotterConstant J h
  have hc0 : 0 ≤ c := tc_nonneg J h
  have hMr : (0:ℝ) < M := by exact_mod_cast (by omega : 0 < M)
  have hsumη : ∑ i, |η i| = ∑ i, η i := Finset.sum_congr rfl (fun i _ => abs_of_nonneg (hη i))
  rw [hsumη] at hmesh
  have hη0 : 0 ≤ ∑ i, η i := Finset.sum_nonneg (fun i _ => hη i)
  have hn1 : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hX1 : 1 ≤ (c + 1) * n + 2 * ∑ i, η i := by nlinarith
  have hqε : c / M * (c * n + Real.log (Real.exp (n + 2 * ∑ i, η i))) ≤ ε := by
    rw [Real.log_exp, div_mul_eq_mul_div, div_le_iff₀ hMr]
    rw [ge_iff_le, div_le_iff₀ hε0] at hmesh
    nlinarith
  have hq1 : c / M ≤ 1 := by
    rw [div_le_one hMr]
    rw [ge_iff_le, div_le_iff₀ hε0] at hmesh
    nlinarith
  have hN : Measurable (fun σ : Fin n → PathData => ∑ i, ((σ i).1 : ℝ)) :=
    Finset.measurable_sum _ (fun i _ => (measurable_of_countable (fun d : ℕ => (d : ℝ))).comp
      (measurable_fst.comp (measurable_pi_apply i)))
  obtain ⟨heN, hG⟩ := total_mgf η hη P
  have hTB := tilt_bounds (nu η P) (pathPotential J h) (meshPotential J h M)
    (fun σ => ∑ i, ((σ i).1 : ℝ)) (pathPot_meas J h) (meshPot_meas J h M) hN
    (fun σ => Finset.sum_nonneg (fun i _ => Nat.cast_nonneg _)) (Bp J h) (pathPot_abs J h)
    (c * n) (fun σ σ' => V_range J hJ h σ σ') (c / M) (by positivity) hq1
    (fun σ => by
      rw [abs_sub_comm]
      have := VM_diff J hJ h σ M (by omega)
      calc |pathPotential J h σ - meshPotential J h M σ| ≤ c * (∑ i, ((σ i).1 : ℝ)) / M := this
        _ = c / M * ∑ i, ((σ i).1 : ℝ) := by ring)
    (Real.exp (n + 2 * ∑ i, η i)) heN hG
  obtain ⟨hlo, hup⟩ := hTB
  constructor
  · rw [mul_assoc]
    apply mul_le_mul_of_nonneg_left _ hCre
    refine le_trans ?_ hlo
    apply mul_le_mul_of_nonneg_left _ (integral_nonneg (fun σ => (Real.exp_pos _).le))
    exact Real.exp_le_exp.2 (by linarith)
  · rw [mul_assoc]
    apply mul_le_mul_of_nonneg_left _ hCre
    refine hup.trans ?_
    apply mul_le_mul_of_nonneg_left _ (integral_nonneg (fun σ => (Real.exp_pos _).le))
    exact Real.exp_le_exp.2 hqε

end TFIMPhaseDiagram.Classical.P9Fin

open TFIMPhaseDiagram.Classical in
theorem solution {n : ℕ} (hn : 0 < n) (J : Matrix (Fin n) (Fin n) ℝ)
    (hJ : J.IsSymm) (h η : Fin n → ℝ) (hη : ∀ i, 0 ≤ η i)
    (S : Finset (Fin n)) (ε : ℝ) (hε : 0 < ε ∧ ε < 1)
    (M : ℕ) (hM : 3 ≤ M)
    (hmesh : (M : ℝ) ≥ trotterConstant J h *
      ((trotterConstant J h + 1) * n + 2 * ∑ i, |η i|) / ε) :
  (Matrix.trace (xSubset S * matrixExp (hamiltonian J h η))).re * Real.exp (-ε) ≤
    (Matrix.trace (xSubset S * trotter J h η M)).re ∧
  (Matrix.trace (xSubset S * trotter J h η M)).re ≤
    (Matrix.trace (xSubset S * matrixExp (hamiltonian J h η))).re * Real.exp ε :=
  TFIMPhaseDiagram.Classical.P9Fin.prop9 hn J hJ h η hη S ε hε M hM hmesh
