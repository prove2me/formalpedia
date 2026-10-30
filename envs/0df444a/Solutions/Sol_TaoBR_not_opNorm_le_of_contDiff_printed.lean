-- Prove2me | solution 1 for TaoBR.not_opNorm_le_of_contDiff_printed
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-29T21:19:03.537328+00:00
-- url     : https://prove2.me/submissions/07e9051d-3d39-4acc-b4e1-650888db9ddc

import Mathlib
import Definitions.Def_TaoBR

open MeasureTheory Metric
open scoped ENNReal ComplexConjugate

namespace TaoBR

lemma enorm_setIntegral_sq_le {α : Type*} [MeasurableSpace α] (μ : Measure α) (J : Set α)
    (g : α → ℂ) (hg : AEStronglyMeasurable g μ) :
    ‖∫ x in J, g x ∂μ‖ₑ ^ 2 ≤ μ J * ∫⁻ x in J, ‖g x‖ₑ ^ 2 ∂μ := by
  have h1 : ‖∫ x in J, g x ∂μ‖ₑ ≤ ∫⁻ x in J, ‖g x‖ₑ ∂μ := enorm_integral_le_lintegral_enorm _
  have h2 : (∫⁻ x in J, ‖g x‖ₑ ∂μ) ^ 2 ≤ μ J * ∫⁻ x in J, ‖g x‖ₑ ^ 2 ∂μ := by
    have := ENNReal.lintegral_mul_le_Lp_mul_Lq (μ.restrict J) Real.HolderConjugate.two_two
      (f := fun _ => (1 : ℝ≥0∞)) (g := fun x => ‖g x‖ₑ) aemeasurable_const
      hg.enorm.restrict
    simp only [Pi.mul_apply, one_mul, ENNReal.one_rpow, lintegral_const, Measure.restrict_apply_univ,
      one_div, one_pow, ENNReal.rpow_ofNat] at this
    have hsq : ∀ x : ℝ≥0∞, (x ^ (2⁻¹ : ℝ)) ^ 2 = x := fun x => by
      rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]; norm_num
    calc _ ≤ (μ J ^ (2⁻¹ : ℝ) * (∫⁻ (a : α) in J, ‖g a‖ₑ ^ 2 ∂μ) ^ (2⁻¹ : ℝ)) ^ 2 :=
          pow_le_pow_left' this 2
      _ = _ := by rw [mul_pow, hsq, hsq]
  exact (pow_le_pow_left' h1 2).trans h2

noncomputable def ek (k : ℕ) (t : ℝ) : ℂ := Complex.exp (2 * Real.pi * Complex.I * k * t)

lemma continuous_ek (k : ℕ) : Continuous (ek k) := by unfold ek; fun_prop

lemma integral_ek_mul_conj (k j : ℕ) :
    ∫ t in Set.Icc (0 : ℝ) 1, ek k t * conj (ek j t) = if k = j then 1 else 0 := by
  have hint : ∀ t : ℝ, ek k t * conj (ek j t) =
      Complex.exp (((k : ℤ) - j : ℤ) * (2 * Real.pi * Complex.I) * t) := by
    intro t
    unfold ek
    rw [← Complex.exp_conj, ← Complex.exp_add]
    congr 1
    simp [Complex.conj_ofReal, map_ofNat]
    push_cast
    ring
  simp_rw [hint]
  split_ifs with h
  · subst h; simp
  · have hc : (((k : ℤ) - j : ℤ) : ℂ) * (2 * Real.pi * Complex.I) ≠ 0 := by
      have : ((k : ℤ) - j : ℤ) ≠ 0 := by omega
      have h2 : (((k : ℤ) - j : ℤ) : ℂ) ≠ 0 := by exact_mod_cast this
      exact mul_ne_zero h2 (by simp [Real.pi_ne_zero])
    rw [MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le zero_le_one,
      integral_exp_mul_complex hc]
    have e := Complex.exp_int_mul_two_pi_mul_I ((k : ℤ) - j)
    simp only [Complex.ofReal_one, Complex.ofReal_zero, mul_one, mul_zero, Complex.exp_zero, e,
      sub_self, zero_div]

lemma integral_norm_sq_sum (I : Finset ℕ) (c : ℕ → ℂ) :
    ∫ t in Set.Icc (0 : ℝ) 1, ‖∑ k ∈ I, c k * ek k t‖ ^ 2 = ∑ k ∈ I, ‖c k‖ ^ 2 := by
  apply Complex.ofReal_injective
  rw [← integral_complex_ofReal]
  have h1 : ∀ t : ℝ, (((‖∑ k ∈ I, c k * ek k t‖ ^ 2 : ℝ)) : ℂ) =
      ∑ k ∈ I, ∑ j ∈ I, (c k * conj (c j)) * (ek k t * conj (ek j t)) := by
    intro t
    rw [Complex.ofReal_pow, ← Complex.mul_conj', map_sum, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => ?_
    rw [map_mul]; ring
  simp_rw [h1]
  have hcont : ∀ k j : ℕ, IntegrableOn (fun t : ℝ => (c k * conj (c j)) * (ek k t * conj (ek j t)))
      (Set.Icc (0 : ℝ) 1) := fun k j =>
    (((continuous_const.mul ((continuous_ek k).mul (Complex.continuous_conj.comp (continuous_ek j))))).integrableOn_Icc)
  rw [integral_finsetSum _ (fun k _ => integrable_finsetSum _ (fun j _ => hcont k j))]
  push_cast
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [integral_finsetSum _ (fun j _ => hcont k j)]
  simp_rw [integral_const_mul, integral_ek_mul_conj]
  simp [Finset.sum_ite_eq', hk, Complex.mul_conj']


/-- coordinate map `E 1 ≃ ℝ` -/
noncomputable def e1 : E 1 ≃ᵐ ℝ :=
  (MeasurableEquiv.toLp 2 (Fin 1 → ℝ)).symm.trans (MeasurableEquiv.funUnique (Fin 1) ℝ)

lemma e1_apply (x : E 1) : e1 x = x 0 := rfl

lemma e1_mp : MeasurePreserving e1 volume volume :=
  (volume_preserving_funUnique (Fin 1) ℝ).comp
    (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin 1))

lemma norm_E1 (x : E 1) : ‖x‖ = |x 0| := by
  simp [EuclideanSpace.norm_eq, Real.sqrt_sq_eq_abs]

def Xs : Set (E 1) := {x | 0 ≤ x 0 ∧ x 0 ≤ 1}

lemma Xs_eq : Xs = e1 ⁻¹' Set.Icc 0 1 := rfl

noncomputable def kk (y : E 1) : ℕ := ⌊1 / y 0⌋₊

noncomputable def Mof (R : ℝ) : ℕ := ⌈R⌉₊ + 1

open Classical in
noncomputable def Kf (R : ℝ) (x y : E 1) : ℂ :=
  if x ∈ Xs ∧ 0 < y 0 ∧ Mof R ≤ kk y ∧ kk y ≤ 2 * Mof R then ek (kk y) (x 0) else 0

noncomputable def bf (x y : E 1) (_τ : ℝ) : ℂ := Complex.exp (-(2 * Real.pi * Complex.I * (kk y) * (x 0)))

/-- the pieces `Yk k`: `kk y = k`, i.e. `y 0 ∈ (1/(k+1), 1/k]` -/
def Yk (k : ℕ) : Set (E 1) := {y | 0 < y 0 ∧ kk y = k}

lemma Yk_eq (k : ℕ) (hk : 1 ≤ k) :
    Yk k = e1 ⁻¹' Set.Ioc (1 / ((k : ℝ) + 1)) (1 / k) := by
  ext y
  simp only [Yk, Set.mem_setOf_eq, Set.mem_preimage, Set.mem_Ioc, e1_apply, kk]
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  constructor
  · rintro ⟨hy, h⟩
    have h1 := (Nat.floor_eq_iff (by positivity)).1 h
    obtain ⟨h1, h2⟩ := h1
    constructor
    · rw [div_lt_iff₀ (by positivity)]
      have := (div_lt_iff₀ hy).1 h2
      linarith
    · rw [le_div_iff₀ hk']
      have := (le_div_iff₀ hy).1 h1
      linarith
  · rintro ⟨h1, h2⟩
    have hy : 0 < y 0 := lt_of_le_of_lt (by positivity) h1
    refine ⟨hy, (Nat.floor_eq_iff (by positivity)).2 ⟨?_, ?_⟩⟩
    · rw [le_div_iff₀ hy]; have := (le_div_iff₀ hk').1 h2; linarith
    · rw [div_lt_iff₀ hy]; have := (div_lt_iff₀ (by positivity)).1 h1; linarith

lemma measurableSet_Yk (k : ℕ) : MeasurableSet (Yk k) := by
  unfold Yk kk
  have hm : Measurable (fun y : E 1 => y 0) := e1.measurable
  refine MeasurableSet.inter (measurableSet_lt measurable_const hm) ?_
  exact measurableSet_eq_fun (Nat.measurable_floor.comp (measurable_const.div hm)) measurable_const

lemma volume_Yk (k : ℕ) (hk : 1 ≤ k) :
    volume (Yk k) = ENNReal.ofReal (1 / (k : ℝ) - 1 / ((k : ℝ) + 1)) := by
  rw [Yk_eq k hk, e1_mp.measure_preimage (measurableSet_Ioc).nullMeasurableSet, Real.volume_Ioc]
  
lemma Mof_pos (R : ℝ) : 1 ≤ Mof R := by unfold Mof; omega

lemma Kf_eq_sum (R : ℝ) (x y : E 1) (hx : x ∈ Xs) :
    Kf R x y = ∑ k ∈ Finset.Icc (Mof R) (2 * Mof R),
      (Yk k).indicator (fun _ => ek k (x 0)) y := by
  classical
  unfold Kf
  by_cases hy : 0 < y 0 ∧ Mof R ≤ kk y ∧ kk y ≤ 2 * Mof R
  · rw [if_pos ⟨hx, hy⟩]
    rw [Finset.sum_eq_single (kk y)]
    · rw [Set.indicator_of_mem]; exact ⟨hy.1, rfl⟩
    · intro k _ hk
      rw [Set.indicator_of_notMem]
      rintro ⟨_, h⟩; exact hk h.symm
    · intro h; exact absurd (Finset.mem_Icc.2 hy.2) h
  · rw [if_neg (fun h => hy h.2)]
    symm
    refine Finset.sum_eq_zero fun k hk => ?_
    rw [Set.indicator_of_notMem]
    rintro ⟨h1, h2⟩
    apply hy
    rw [Finset.mem_Icc] at hk
    exact ⟨h1, h2 ▸ hk.1, h2 ▸ hk.2⟩

lemma integrableOn_Yk {f : E 1 → ℂ} (hf : MemLp f 2 volume) (k : ℕ) (hk : 1 ≤ k) :
    IntegrableOn f (Yk k) := by
  have hfin : volume (Yk k) < ∞ := by rw [volume_Yk k hk]; exact ENNReal.ofReal_lt_top
  haveI : IsFiniteMeasure (volume.restrict (Yk k)) := ⟨by simpa using hfin⟩
  exact (hf.restrict (Yk k)).integrable one_le_two

lemma kernelOp_Kf (R : ℝ) {f : E 1 → ℂ} (hf : MemLp f 2 volume) (x : E 1) :
    kernelOp (Kf R) f x = Xs.indicator (fun x => ∑ k ∈ Finset.Icc (Mof R) (2 * Mof R),
      (∫ y in Yk k, f y) * ek k (x 0)) x := by
  unfold kernelOp
  by_cases hx : x ∈ Xs
  · rw [Set.indicator_of_mem hx]
    have : ∀ y, Kf R x y * f y = ∑ k ∈ Finset.Icc (Mof R) (2 * Mof R),
        (Yk k).indicator (fun y => ek k (x 0) * f y) y := by
      intro y
      rw [Kf_eq_sum R x y hx, Finset.sum_mul]
      refine Finset.sum_congr rfl fun k _ => ?_
      by_cases hy : y ∈ Yk k <;> simp [Set.indicator, hy]
    simp_rw [this]
    rw [integral_finsetSum]
    · refine Finset.sum_congr rfl fun k hk => ?_
      have hk1 : 1 ≤ k := le_trans (Mof_pos R) (Finset.mem_Icc.1 hk).1
      rw [integral_indicator (measurableSet_Yk k), integral_const_mul, mul_comm]
    · intro k hk
      have hk1 : 1 ≤ k := le_trans (Mof_pos R) (Finset.mem_Icc.1 hk).1
      exact (integrable_indicator_iff (measurableSet_Yk k)).2
        ((integrableOn_Yk hf k hk1).const_mul _)
  · rw [Set.indicator_of_notMem hx]
    have : ∀ y, Kf R x y * f y = 0 := fun y => by simp [Kf, hx]
    simp [this]

lemma sq_eLpNorm_two {α : Type*} {mα : MeasurableSpace α} {F : Type*} [NormedAddCommGroup F]
    (g : α → F) (μ : Measure α) : eLpNorm g 2 μ ^ 2 = ∫⁻ x, ‖g x‖ₑ ^ 2 ∂μ := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)]
  simp only [ENNReal.toReal_ofNat, ENNReal.rpow_ofNat]
  rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
  norm_num

lemma A_sq (R : ℝ) {f : E 1 → ℂ} (hf : MemLp f 2 volume) :
    ∫⁻ x, ‖kernelOp (Kf R) f x‖ₑ ^ 2 =
      ∑ k ∈ Finset.Icc (Mof R) (2 * Mof R), ‖∫ y in Yk k, f y‖ₑ ^ 2 := by
  set c : ℕ → ℂ := fun k => ∫ y in Yk k, f y with hc
  set G : ℝ → ℂ := fun t => ∑ k ∈ Finset.Icc (Mof R) (2 * Mof R), c k * ek k t with hG
  have h1 : ∀ x, ‖kernelOp (Kf R) f x‖ₑ ^ 2 = Xs.indicator (fun x => ‖G (e1 x)‖ₑ ^ 2) x := by
    intro x
    rw [kernelOp_Kf R hf x]
    by_cases hx : x ∈ Xs <;> simp [Set.indicator, hx, hG, e1_apply, hc]
  simp_rw [h1]
  rw [lintegral_indicator (by rw [Xs_eq]; exact measurableSet_Icc.preimage e1.measurable), Xs_eq,
    e1_mp.setLIntegral_comp_preimage_emb e1.measurableEmbedding (fun t => ‖G t‖ₑ ^ 2)]
  have hint : IntegrableOn (fun t : ℝ => ‖G t‖ ^ 2) (Set.Icc 0 1) := by
    refine Continuous.integrableOn_Icc ?_
    have : Continuous G := by
      refine continuous_finset_sum _ fun k _ => continuous_const.mul (continuous_ek k)
    fun_prop
  have h2 : ∀ t, ‖G t‖ₑ ^ 2 = ENNReal.ofReal (‖G t‖ ^ 2) := fun t => by
    rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]
  simp_rw [h2]
  rw [← ofReal_integral_eq_lintegral_ofReal hint (Filter.Eventually.of_forall fun t => by positivity),
    integral_norm_sq_sum, ENNReal.ofReal_sum_of_nonneg (fun k _ => by positivity)]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]

lemma volume_Yk_le (k M : ℕ) (hM : 1 ≤ M) (hk : M ≤ k) :
    volume (Yk k) ≤ ENNReal.ofReal (1 / (M : ℝ) ^ 2) := by
  rw [volume_Yk k (le_trans hM hk)]
  refine ENNReal.ofReal_le_ofReal ?_
  have hM' : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hk' : (M : ℝ) ≤ k := by exact_mod_cast hk
  have hk0 : (0 : ℝ) < k := by linarith
  rw [div_sub_div _ _ hk0.ne' (by positivity), div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith

lemma pairwiseDisjoint_Yk (t : Finset ℕ) : Set.PairwiseDisjoint (↑t : Set ℕ) Yk := by
  intro k _ k' _ hne
  rw [Function.onFun, Set.disjoint_left]
  rintro y ⟨_, h1⟩ ⟨_, h2⟩
  exact hne (h1.symm.trans h2)

lemma A_bound (R : ℝ) {f : E 1 → ℂ} (hf : MemLp f 2 volume) :
    eLpNorm (kernelOp (Kf R) f) 2 volume ≤
      ENNReal.ofReal (1 / (Mof R : ℝ)) * eLpNorm f 2 volume := by
  have hM := Mof_pos R
  set M := Mof R with hMdef
  have key : eLpNorm (kernelOp (Kf R) f) 2 volume ^ 2 ≤
      (ENNReal.ofReal (1 / (M : ℝ)) * eLpNorm f 2 volume) ^ 2 := by
    rw [sq_eLpNorm_two, mul_pow, sq_eLpNorm_two, A_sq R hf]
    have h1 : ∀ k ∈ Finset.Icc M (2 * M), ‖∫ y in Yk k, f y‖ₑ ^ 2 ≤
        ENNReal.ofReal (1 / (M : ℝ) ^ 2) * ∫⁻ y in Yk k, ‖f y‖ₑ ^ 2 := by
      intro k hk
      refine (enorm_setIntegral_sq_le volume (Yk k) f hf.aestronglyMeasurable).trans ?_
      gcongr
      exact volume_Yk_le k M hM (Finset.mem_Icc.1 hk).1
    refine (Finset.sum_le_sum h1).trans ?_
    rw [← Finset.mul_sum, ← lintegral_biUnion_finset (pairwiseDisjoint_Yk _) (fun k _ => measurableSet_Yk k)]
    have : ENNReal.ofReal (1 / (M : ℝ)) ^ 2 = ENNReal.ofReal (1 / (M : ℝ) ^ 2) := by
      rw [← ENNReal.ofReal_pow (by positivity), div_pow, one_pow]
    rw [this]
    exact mul_le_mul_right (setLIntegral_le_lintegral _ _) _
  by_contra hcon
  have := ENNReal.pow_lt_pow_left two_ne_zero (not_le.1 hcon)
  exact absurd key (not_le.2 this)

def Yset (M : ℕ) : Set (E 1) := {y | 0 < y 0 ∧ M ≤ kk y ∧ kk y ≤ 2 * M}

lemma Yset_eq (M : ℕ) (hM : 1 ≤ M) :
    Yset M = e1 ⁻¹' Set.Ioc (1 / (2 * (M : ℝ) + 1)) (1 / M) := by
  ext y
  simp only [Yset, Set.mem_setOf_eq, Set.mem_preimage, Set.mem_Ioc, e1_apply, kk]
  have hM' : (0 : ℝ) < M := by exact_mod_cast hM
  constructor
  · rintro ⟨hy, h1, h2⟩
    have a1 : (M : ℝ) ≤ 1 / y 0 := (Nat.le_floor_iff (by positivity)).1 h1
    have a2 : 1 / y 0 < ((2 * M + 1 : ℕ) : ℝ) :=
      (Nat.floor_lt (by positivity)).1 (Nat.lt_succ_of_le h2)
    push_cast at a2
    constructor
    · rw [div_lt_iff₀ (by positivity)]
      have := (div_lt_iff₀ hy).1 a2
      linarith
    · rw [le_div_iff₀ hM']
      have := (le_div_iff₀ hy).1 a1
      linarith
  · rintro ⟨h1, h2⟩
    have hy : 0 < y 0 := lt_of_le_of_lt (by positivity) h1
    refine ⟨hy, ?_, ?_⟩
    · refine (Nat.le_floor_iff (by positivity)).2 ?_
      rw [le_div_iff₀ hy]; have := (le_div_iff₀ hM').1 h2; linarith
    · have : ⌊1 / y 0⌋₊ < 2 * M + 1 := by
        refine (Nat.floor_lt (by positivity)).2 ?_
        push_cast
        rw [div_lt_iff₀ hy]; have := (div_lt_iff₀ (by positivity)).1 h1; linarith
      omega

lemma measurableSet_Yset (M : ℕ) (hM : 1 ≤ M) : MeasurableSet (Yset M) := by
  rw [Yset_eq M hM]; exact measurableSet_Ioc.preimage e1.measurable

lemma volume_Yset (M : ℕ) (hM : 1 ≤ M) :
    volume (Yset M) = ENNReal.ofReal (1 / (M : ℝ) - 1 / (2 * (M : ℝ) + 1)) := by
  rw [Yset_eq M hM, e1_mp.measure_preimage measurableSet_Ioc.nullMeasurableSet, Real.volume_Ioc]

lemma volume_Xs : volume Xs = 1 := by
  rw [Xs_eq, e1_mp.measure_preimage measurableSet_Icc.nullMeasurableSet]; simp

open Classical in
lemma Kf_mul_bf (R τ : ℝ) (x y : E 1) :
    Kf R x y * bf x y τ = if x ∈ Xs ∧ y ∈ Yset (Mof R) then 1 else 0 := by
  unfold Kf bf Yset
  by_cases h : x ∈ Xs ∧ 0 < y 0 ∧ Mof R ≤ kk y ∧ kk y ≤ 2 * Mof R
  · rw [if_pos h, if_pos ⟨h.1, h.2⟩, ek, ← Complex.exp_add]; simp
  · have h2 : ¬ (x ∈ Xs ∧ y ∈ {y : E 1 | 0 < y 0 ∧ Mof R ≤ kk y ∧ kk y ≤ 2 * Mof R}) :=
      fun h' => h h'
    rw [if_neg h, if_neg h2]; simp

lemma B_lower (R τ : ℝ) :
    ENNReal.ofReal (Real.sqrt (1 / (Mof R : ℝ) - 1 / (2 * (Mof R : ℝ) + 1))) ≤
      opNorm 2 2 (kernelOp fun x y : E 1 => Kf R x y * bf x y τ) := by
  classical
  have hM := Mof_pos R
  have hKb : ∀ x y : E 1, Kf R x y * bf x y τ =
      if x ∈ Xs ∧ y ∈ Yset (Mof R) then 1 else 0 := fun x y => Kf_mul_bf R τ x y
  generalize Mof R = M at hM hKb ⊢
  have hM' : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hv : 0 < 1 / (M : ℝ) - 1 / (2 * (M : ℝ) + 1) := by
    rw [sub_pos]
    exact one_div_lt_one_div_of_lt (by positivity) (by linarith)
  set v := 1 / (M : ℝ) - 1 / (2 * (M : ℝ) + 1) with hvdef
  have hvol : volume (Yset M) = ENNReal.ofReal v := volume_Yset M hM
  have hfin : volume (Yset M) ≠ ∞ := by rw [hvol]; exact ENNReal.ofReal_ne_top
  unfold opNorm
  refine le_sInf fun C hC => ?_
  let f : E 1 → ℂ := (Yset M).indicator (fun _ => (1 : ℂ))
  have hf : MemLp f 2 volume := memLp_indicator_const 2 (measurableSet_Yset M hM) (1 : ℂ) (Or.inr hfin)
  have hT : kernelOp (fun x y : E 1 => Kf R x y * bf x y τ) f =
      Xs.indicator (fun _ => (v : ℂ)) := by
    funext x
    unfold kernelOp
    by_cases hx : x ∈ Xs
    · rw [Set.indicator_of_mem hx]
      have : ∀ y, Kf R x y * bf x y τ * f y = (Yset M).indicator (fun _ => (1 : ℂ)) y := by
        intro y
        rw [hKb]
        by_cases hy : y ∈ Yset M <;> simp [f, hx, hy]
      simp_rw [this]
      rw [integral_indicator_const _ (measurableSet_Yset M hM)]
      simp [Measure.real, hvol, ENNReal.toReal_ofReal hv.le]
    · rw [Set.indicator_of_notMem hx]
      have : ∀ y, Kf R x y * bf x y τ * f y = 0 := fun y => by rw [hKb]; simp [hx]
      simp [this]
  have h1 := hC f hf
  rw [hT] at h1
  simp only [f] at h1
  rw [eLpNorm_indicator_const (by rw [Xs_eq]; exact measurableSet_Icc.preimage e1.measurable)
      (by norm_num) (by norm_num),
    eLpNorm_indicator_const (measurableSet_Yset M hM) (by norm_num) (by norm_num)] at h1
  have hw : ENNReal.ofReal v ^ (1 / (2 : ℝ≥0∞).toReal) = ENNReal.ofReal (Real.sqrt v) := by
    rw [ENNReal.toReal_ofNat, ENNReal.ofReal_rpow_of_nonneg hv.le (by norm_num),
      Real.sqrt_eq_rpow]
  have hww : ENNReal.ofReal v = ENNReal.ofReal (Real.sqrt v) * ENNReal.ofReal (Real.sqrt v) := by
    rw [← ENNReal.ofReal_mul (Real.sqrt_nonneg _), Real.mul_self_sqrt hv.le]
  rw [hvol, volume_Xs, hw] at h1
  have hsq : 0 < Real.sqrt v := Real.sqrt_pos.2 hv
  have hw0 : ENNReal.ofReal (Real.sqrt v) ≠ 0 := (ENNReal.ofReal_pos.2 hsq).ne'
  have hwt : ENNReal.ofReal (Real.sqrt v) ≠ ∞ := ENNReal.ofReal_ne_top
  have hv1 : ‖(v : ℂ)‖ₑ = ENNReal.ofReal v := by
    rw [← ofReal_norm, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hv]
  simp only [ENNReal.one_rpow, mul_one, enorm_one, one_mul, hv1] at h1
  rw [hww] at h1
  exact (ENNReal.mul_le_mul_iff_left hw0 hwt).1 h1

lemma norm_cexp_real_mul_I (a : ℝ) : ‖Complex.exp (a * Complex.I)‖ = 1 := Complex.norm_exp_ofReal_mul_I a

lemma norm_ek (k : ℕ) (t : ℝ) : ‖ek k t‖ = 1 := by
  have : ek k t = Complex.exp (((2 * Real.pi * k * t : ℝ) : ℂ) * Complex.I) := by
    unfold ek; congr 1; push_cast; ring
  rw [this]; exact norm_cexp_real_mul_I _

lemma norm_bf (x y : E 1) (τ : ℝ) : ‖bf x y τ‖ = 1 := by
  have : bf x y τ = Complex.exp (((-(2 * Real.pi * kk y * x 0) : ℝ) : ℂ) * Complex.I) := by
    unfold bf; congr 1; push_cast; ring
  rw [this]; exact norm_cexp_real_mul_I _

lemma measurable_kk : Measurable kk := Nat.measurable_floor.comp (measurable_const.div e1.measurable)

lemma measurable_Kf (R : ℝ) : Measurable (Function.uncurry (Kf R)) := by
  classical
  have hx : Measurable (fun p : E 1 × E 1 => p.1 0) := e1.measurable.comp measurable_fst
  have hy : Measurable (fun p : E 1 × E 1 => p.2 0) := e1.measurable.comp measurable_snd
  have hk : Measurable (fun p : E 1 × E 1 => kk p.2) := measurable_kk.comp measurable_snd
  unfold Kf Function.uncurry
  refine Measurable.ite ?_ ?_ measurable_const
  · have h1 : MeasurableSet {p : E 1 × E 1 | p.1 ∈ Xs} :=
      (show MeasurableSet Xs by rw [Xs_eq]; exact measurableSet_Icc.preimage e1.measurable).preimage measurable_fst
    have h2 : MeasurableSet {p : E 1 × E 1 | 0 < p.2 0} := measurableSet_lt measurable_const hy
    have h3 : MeasurableSet {p : E 1 × E 1 | Mof R ≤ kk p.2} := measurableSet_le measurable_const hk
    have h4 : MeasurableSet {p : E 1 × E 1 | kk p.2 ≤ 2 * Mof R} := measurableSet_le hk measurable_const
    exact h1.inter (h2.inter (h3.inter h4))
  · unfold ek
    refine Complex.measurable_exp.comp ?_
    fun_prop

lemma measurable_bf (τ : ℝ) : Measurable (Function.uncurry fun x y : E 1 => bf x y τ) := by
  have hx : Measurable (fun p : E 1 × E 1 => p.1 0) := e1.measurable.comp measurable_fst
  have hk : Measurable (fun p : E 1 × E 1 => kk p.2) := measurable_kk.comp measurable_snd
  unfold bf Function.uncurry
  refine Complex.measurable_exp.comp ?_
  fun_prop

lemma Kf_support (R : ℝ) (x y : E 1) (h : Kf R x y ≠ 0) : (x, y) ∈ closedBall (0 : E 1 × E 1) 1 := by
  classical
  unfold Kf at h
  split_ifs at h with hc
  · obtain ⟨hx, hy, hk, _⟩ := hc
    have hM := Mof_pos R
    have hy1 : y 0 ≤ 1 := by
      have : 1 ≤ ⌊1 / y 0⌋₊ := le_trans hM hk
      have := (Nat.le_floor_iff (by positivity)).1 this
      simp only [Nat.cast_one] at this
      rwa [le_div_iff₀ hy, one_mul] at this
    rw [mem_closedBall_zero_iff, Prod.norm_def, norm_E1, norm_E1, abs_of_nonneg hx.1,
      abs_of_pos hy]
    exact max_le hx.2 hy1
  · exact absurd rfl h

lemma contDiff_bf (y : E 1) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun z : E 1 × ℝ => bf z.1 y z.2) Set.univ := by
  rw [contDiffOn_univ]
  unfold bf
  have : ContDiff ℝ (⊤ : ℕ∞) (fun z : E 1 × ℝ => z.1 0) :=
    ((EuclideanSpace.proj (0 : Fin 1) : E 1 →L[ℝ] ℝ).contDiff).comp contDiff_fst
  exact Complex.contDiff_exp.comp (ContDiff.neg (contDiff_const.mul
    (Complex.ofRealCLM.contDiff.comp this)))

theorem opNorm_dev :
    ¬ ∀ (n : ℕ) (p q : ℝ≥0∞), 1 ≤ p → 1 ≤ q →
      ∀ (K : ℝ → E n → E n → ℂ) (S : Set (E n × E n)), IsCompact S → ∀ M : ℝ,
      (∀ R, Measurable (Function.uncurry (K R))) →
      (∀ R x y, ‖K R x y‖ ≤ M ∧ (K R x y ≠ 0 → (x, y) ∈ S)) →
      ∀ b : E n → E n → ℝ → ℂ, (∀ τ, Measurable (Function.uncurry fun x y => b x y τ)) →
      ∀ B : ℝ, (∀ x y τ, ‖b x y τ‖ ≤ B) → ∀ τ₀ : ℝ, 0 < τ₀ →
      ∀ U : Set (E n × ℝ), IsOpen U → (Prod.fst '' S) ×ˢ Set.Icc 0 τ₀ ⊆ U →
      (∀ y ∈ Prod.snd '' S, ContDiffOn ℝ (⊤ : ℕ∞) (fun z : E n × ℝ => b z.1 y z.2) U) →
      ∀ N : ℝ, 0 < N → ∃ C R₀ : ℝ, ∀ R : ℝ, R₀ ≤ R →
        opNorm p q (kernelOp fun x y => K R x y * b x y R⁻¹) ≤
          ENNReal.ofReal C * opNorm p q (kernelOp (K R)) + ENNReal.ofReal (C * R ^ (-N)) := by
  intro H
  obtain ⟨C, R₀, hCR⟩ := H 1 2 2 (by norm_num) (by norm_num) Kf (closedBall 0 1) (isCompact_closedBall _ _) 1
    measurable_Kf
    (fun R x y => ⟨by
      unfold Kf; split_ifs
      · rw [norm_ek]
      · simp, Kf_support R x y⟩)
    bf measurable_bf 1 (fun x y τ => (norm_bf x y τ).le) 1 one_pos Set.univ isOpen_univ
    (Set.subset_univ _) (fun y _ => contDiff_bf y) 1 one_pos
  set C' := max C 0 with hC'
  have hC'0 : 0 ≤ C' := le_max_right _ _
  obtain ⟨N0, hN0⟩ := exists_nat_gt (max (max R₀ 1) (18 * C' ^ 2))
  have hN1 : (1 : ℝ) < N0 := lt_of_le_of_lt ((le_max_right _ _).trans (le_max_left _ _)) hN0
  have hNR : R₀ < N0 := lt_of_le_of_lt ((le_max_left _ _).trans (le_max_left _ _)) hN0
  have hN18 : 18 * C' ^ 2 < N0 := lt_of_le_of_lt (le_max_right _ _) hN0
  have hR := hCR (N0 : ℝ) hNR.le
  have hMof : Mof (N0 : ℝ) = N0 + 1 := by unfold Mof; simp
  have hlow := B_lower (N0 : ℝ) ((N0 : ℝ)⁻¹)
  have hA : opNorm 2 2 (kernelOp (Kf (N0 : ℝ))) ≤ ENNReal.ofReal (1 / ((N0 : ℝ) + 1)) := by
    unfold opNorm
    refine sInf_le fun f hf => ?_
    have := A_bound (N0 : ℝ) hf
    rw [hMof] at this
    simpa using this
  have h1 := hlow.trans hR
  rw [hMof] at h1
  have h2 : ENNReal.ofReal C * opNorm 2 2 (kernelOp (Kf (N0 : ℝ))) +
      ENNReal.ofReal (C * (N0 : ℝ) ^ (-(1 : ℝ))) ≤
      ENNReal.ofReal (C' * (1 / ((N0 : ℝ) + 1)) + C' * (N0 : ℝ)⁻¹) := by
    have hN0pos : (0 : ℝ) < N0 := by linarith
    rw [Real.rpow_neg_one]
    rw [ENNReal.ofReal_add (by positivity) (by positivity), ENNReal.ofReal_mul hC'0]
    gcongr
    · exact le_max_left _ _
    · exact le_max_left _ _
  have h3 := h1.trans h2
  push_cast at h3
  have hN0pos : (0 : ℝ) < N0 := by linarith
  rw [ENNReal.ofReal_le_ofReal_iff (by positivity)] at h3
  set v := 1 / ((N0 : ℝ) + 1) - 1 / (2 * ((N0 : ℝ) + 1) + 1) with hv
  have hMr : (0 : ℝ) < (N0 : ℝ) + 1 := by linarith
  have hb : C' * (N0 : ℝ)⁻¹ ≤ 2 * C' / ((N0 : ℝ) + 1) := by
    rw [mul_comm 2 C', mul_div_assoc, inv_eq_one_div]
    refine mul_le_mul_of_nonneg_left ?_ hC'0
    rw [div_le_div_iff₀ hN0pos hMr]; linarith
  have h4 : Real.sqrt v ≤ 3 * C' / ((N0 : ℝ) + 1) := by
    refine h3.trans ?_
    have : C' * (1 / ((N0 : ℝ) + 1)) = C' / ((N0 : ℝ) + 1) := by ring
    rw [this]
    have h5 : 3 * C' / ((N0 : ℝ) + 1) = C' / ((N0 : ℝ) + 1) + 2 * C' / ((N0 : ℝ) + 1) := by ring
    rw [h5]; linarith
  have h6 := (Real.sqrt_le_iff.1 h4).2
  have hvlow : 1 / (2 * ((N0 : ℝ) + 1)) ≤ v := by
    rw [hv, div_sub_div _ _ hMr.ne' (by positivity), div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  have h7 := le_trans hvlow h6
  rw [div_pow, mul_pow, div_le_div_iff₀ (by positivity) (by positivity)] at h7
  have h8 : ((N0 : ℝ) + 1) * ((N0 : ℝ) + 1) ≤ (18 * C' ^ 2) * ((N0 : ℝ) + 1) := by nlinarith
  have h9 := le_of_mul_le_mul_right h8 hMr
  linarith

end TaoBR

open TaoBR in
theorem solution : type_of% @TaoBR.opNorm_dev := @TaoBR.opNorm_dev
