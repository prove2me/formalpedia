-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Dependency50.P39.discreteDiagonalEffects
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-24T02:18:13.305608+00:00
-- url     : https://prove2.me/submissions/9e7cc3e1-6450-40ed-bd40-74cd4f83b781

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P39

noncomputable section

open Filter MeasureTheory
open scoped Topology

attribute [local instance] Classical.propDecidable

namespace QAlgorithms.Papers.Independent.Dependency50.P39

/-- A binomial term is at most one. -/
lemma X7A20_binom_term (y : ℝ) (h0 : 0 ≤ y) (h1 : y ≤ 1) (n l : ℕ) :
    (Nat.choose (n + l) l : ℝ) * (1 - y) ^ l * y ^ n ≤ 1 := by
  have h := add_pow (1 - y) y (n + l)
  rw [sub_add_cancel, one_pow] at h
  have hmem : l ∈ Finset.range (n + l + 1) := Finset.mem_range.mpr (by omega)
  have := Finset.single_le_sum (f := fun j => (1 - y) ^ j * y ^ (n + l - j) *
      (Nat.choose (n + l) j : ℝ)) (fun j _ => by
        have : 0 ≤ 1 - y := by linarith
        positivity) hmem
  have e : n + l - l = n := by omega
  rw [e] at this
  calc (Nat.choose (n + l) l : ℝ) * (1 - y) ^ l * y ^ n
      = (1 - y) ^ l * y ^ n * (Nat.choose (n + l) l : ℝ) := by ring
    _ ≤ _ := this
    _ = 1 := h.symm

lemma X7A20_sqrt_pow (a : ℝ) (ha : 0 ≤ a) (l : ℕ) : Real.sqrt (a ^ l) = Real.sqrt a ^ l := by
  induction l with
  | zero => simp
  | succ l ih => rw [pow_succ, Real.sqrt_mul (pow_nonneg ha l), ih, pow_succ]

/-- coordinates of a vector as inner products with kets -/
lemma X7A20_coord (v : Fock) (m : ℕ) : v m = inner ℂ (fockKet m) v := by
  rw [fockKet, lp.inner_single_left]
  simp

lemma X7A20_ket_apply (n m : ℕ) : (fockKet n) m = if m = n then 1 else 0 := by
  simp [fockKet, lp.single_apply, Pi.single_apply]

lemma X7A20_inner_ket (m n : ℕ) :
    inner ℂ (fockKet m) (fockKet n) = if m = n then 1 else 0 := by
  rw [fockKet, lp.inner_single_left, X7A20_ket_apply]
  split_ifs <;> simp

/-- weighted composition operator. -/
lemma X7A20_sum_le (g : ℕ → ℕ) (w : ℕ → ℂ) (hw : ∀ m, ‖w m‖ ≤ 1)
    (hinj : ∀ m n, w m ≠ 0 → w n ≠ 0 → g m = g n → m = n) (x : Fock) (s : Finset ℕ) :
    ∑ m ∈ s, ‖w m * x (g m)‖ ^ (2 : ENNReal).toReal ≤ ‖x‖ ^ (2 : ENNReal).toReal := by
  have hp : (0 : ℝ) < (2 : ENNReal).toReal := by norm_num
  calc ∑ m ∈ s, ‖w m * x (g m)‖ ^ (2 : ENNReal).toReal
      ≤ ∑ m ∈ s.filter (fun m => w m ≠ 0), ‖x (g m)‖ ^ (2 : ENNReal).toReal := by
        rw [Finset.sum_filter]
        apply Finset.sum_le_sum
        intro m _
        split_ifs with h
        · rw [norm_mul, Real.mul_rpow (norm_nonneg _) (norm_nonneg _)]
          have h1 : ‖w m‖ ^ (2 : ENNReal).toReal ≤ 1 :=
            Real.rpow_le_one (norm_nonneg _) (hw m) hp.le
          have h2 : 0 ≤ ‖x (g m)‖ ^ (2 : ENNReal).toReal := by positivity
          nlinarith
        · push Not at h
          rw [h, zero_mul, norm_zero, Real.zero_rpow hp.ne']
    _ = ∑ j ∈ (s.filter (fun m => w m ≠ 0)).image g, ‖x j‖ ^ (2 : ENNReal).toReal := by
        rw [Finset.sum_image]
        intro a ha b hb hab
        simp only [Finset.coe_filter, Set.mem_ofPred_eq] at ha hb
        exact hinj a b ha.2 hb.2 hab
    _ ≤ ‖x‖ ^ (2 : ENNReal).toReal := lp.sum_rpow_le_norm_rpow hp x _

def X7A20_op (g : ℕ → ℕ) (w : ℕ → ℂ) (hw : ∀ m, ‖w m‖ ≤ 1)
    (hinj : ∀ m n, w m ≠ 0 → w n ≠ 0 → g m = g n → m = n) : FockOperator :=
  LinearMap.mkContinuous
    { toFun := fun x => ⟨fun m => w m * x (g m), memℓp_gen' (X7A20_sum_le g w hw hinj x)⟩
      map_add' := by
        intro x y
        ext m
        change w m * (x + y) (g m) = w m * x (g m) + w m * y (g m)
        rw [lp.coeFn_add, Pi.add_apply, mul_add]
      map_smul' := by
        intro c x
        ext m
        simp only [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
        change w m * (c * x (g m)) = c * (w m * x (g m))
        ring }
    1 (by
      intro x
      rw [one_mul]
      exact lp.norm_le_of_forall_sum_le (by norm_num) (norm_nonneg _)
        (fun s => X7A20_sum_le g w hw hinj x s))

lemma X7A20_op_apply (g : ℕ → ℕ) (w : ℕ → ℂ) (hw : ∀ m, ‖w m‖ ≤ 1)
    (hinj : ∀ m n, w m ≠ 0 → w n ≠ 0 → g m = g n → m = n) (x : Fock) (m : ℕ) :
    X7A20_op g w hw hinj x m = w m * x (g m) := rfl

/-- Monomial operators: each ket goes to a multiple of a ket, injectively on support. -/
def X7A20_Mono (W : FockOperator) : Prop :=
  ∃ g : ℕ → ℕ, ∃ c : ℕ → ℂ, (∀ n, W (fockKet n) = c n • fockKet (g n)) ∧
    ∀ m n, c m ≠ 0 → c n ≠ 0 → g m = g n → m = n

lemma X7A20_Mono_comp {K L : FockOperator} (hK : X7A20_Mono K) (hL : X7A20_Mono L) :
    X7A20_Mono (K.comp L) := by
  obtain ⟨h, d, hKe, hKi⟩ := hK
  obtain ⟨g, c, hLe, hLi⟩ := hL
  refine ⟨fun n => h (g n), fun n => c n * d (g n), ?_, ?_⟩
  · intro n
    simp only [ContinuousLinearMap.comp_apply, hLe, map_smul, hKe, smul_smul]
  · intro m n hm hn hmn
    have hcm : c m ≠ 0 := left_ne_zero_of_mul hm
    have hcn : c n ≠ 0 := left_ne_zero_of_mul hn
    have hdm : d (g m) ≠ 0 := right_ne_zero_of_mul hm
    have hdn : d (g n) ≠ 0 := right_ne_zero_of_mul hn
    exact hLi m n hcm hcn (hKi _ _ hdm hdn hmn)

lemma X7A20_Mono_diag {W : FockOperator} (hW : X7A20_Mono W) : FockDiagonalEffect W := by
  obtain ⟨g, c, hWe, hWi⟩ := hW
  intro m n hmn
  rw [X7A20_coord, ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_right,
    hWe, hWe, inner_smul_left, inner_smul_right, X7A20_inner_ket]
  by_cases hc : c m = 0
  · simp [hc]
  by_cases hd : c n = 0
  · simp [hd]
  have : g m ≠ g n := fun h => hmn (hWi m n hc hd h)
  simp [this]

/-- realization from a weighted composition operator -/
lemma X7A20_realize (K : ℕ → ℕ → ℂ) (g : ℕ → ℕ) (w : ℕ → ℂ) (hw : ∀ m, ‖w m‖ ≤ 1)
    (hinj : ∀ m n, w m ≠ 0 → w n ≠ 0 → g m = g n → m = n)
    (hK : ∀ m n, K m n = w m * (if g m = n then 1 else 0)) :
    HasFockMatrix (operatorOfMatrix K) K := by
  have hex : ∃ A : FockOperator, HasFockMatrix A K := by
    refine ⟨X7A20_op g w hw hinj, ?_⟩
    intro m n
    rw [X7A20_op_apply, X7A20_ket_apply, hK]
  rw [operatorOfMatrix, dif_pos hex]
  exact Classical.choose_spec hex

lemma X7A20_mono_of_matrix (A : FockOperator) (K : ℕ → ℕ → ℂ) (hA : HasFockMatrix A K)
    (g : ℕ → ℕ) (c : ℕ → ℂ) (hK : ∀ m n, K m n = c n * (if m = g n then 1 else 0))
    (hinj : ∀ m n, c m ≠ 0 → c n ≠ 0 → g m = g n → m = n) : X7A20_Mono A := by
  refine ⟨g, c, ?_, hinj⟩
  intro n
  ext m
  rw [hA m n, hK, lp.coeFn_smul, Pi.smul_apply, X7A20_ket_apply, smul_eq_mul]

lemma X7A20_atten (k : ℝ) (h0 : 0 ≤ k) (h1 : k ≤ 1) :
    AttenuatorRealized k ∧ ∀ l, X7A20_Mono (attenuatorKraus k l) := by
  have hreal : ∀ l, HasFockMatrix (attenuatorKraus k l) (attenuatorMatrix k l) := by
    intro l
    let w : ℕ → ℂ := fun m => ((Real.sqrt (Nat.choose (m + l) l : ℝ) *
      Real.sqrt (1 - k ^ 2) ^ l * k ^ m : ℝ) : ℂ)
    refine X7A20_realize _ (fun m => m + l) w ?_ ?_ ?_
    · intro m
      simp only [w, Complex.norm_real, Real.norm_eq_abs]
      have hk2 : 0 ≤ 1 - k ^ 2 := by nlinarith
      have hC : (0:ℝ) ≤ (Nat.choose (m + l) l : ℝ) := Nat.cast_nonneg _
      rw [abs_of_nonneg (mul_nonneg (mul_nonneg (Real.sqrt_nonneg _)
        (pow_nonneg (Real.sqrt_nonneg _) _)) (pow_nonneg h0 _))]
      have e : Real.sqrt (Nat.choose (m + l) l : ℝ) * Real.sqrt (1 - k ^ 2) ^ l * k ^ m =
          Real.sqrt ((Nat.choose (m + l) l : ℝ) * (1 - k ^ 2) ^ l * (k ^ 2) ^ m) := by
        rw [Real.sqrt_mul (mul_nonneg hC (pow_nonneg hk2 _)), Real.sqrt_mul hC,
          X7A20_sqrt_pow _ hk2, X7A20_sqrt_pow _ (sq_nonneg k), Real.sqrt_sq h0]
      rw [e]
      apply Real.sqrt_le_one.mpr
      exact X7A20_binom_term (k ^ 2) (sq_nonneg k) (by nlinarith) m l
    · intro m n _ _ h
      simpa using h
    · intro m n
      simp only [attenuatorMatrix, w]
      by_cases h : n = m + l
      · subst h; simp
      · have h' : ¬ m + l = n := fun e => h e.symm
        simp [h, h']
  refine ⟨hreal, fun l => ?_⟩
  refine X7A20_mono_of_matrix _ _ (hreal l) (fun n => n - l)
    (fun n => if l ≤ n then attenuatorMatrix k l (n - l) n else 0) ?_ ?_
  · intro m n
    simp only [attenuatorMatrix]
    by_cases h : n = m + l
    · subst h
      simp
    · by_cases hl : l ≤ n
      · have hm : ¬ m = n - l := by omega
        simp [h, hl, hm]
      · simp [h, hl]
  · intro m n hm hn hmn
    have hlm : l ≤ m := by
      by_contra hc; exact hm (by simp [hc])
    have hln : l ≤ n := by
      by_contra hc; exact hn (by simp [hc])
    change m - l = n - l at hmn
    omega

lemma X7A20_amp (k : ℝ) (h1 : 1 ≤ k) :
    AmplifierRealized k ∧ ∀ l, X7A20_Mono (amplifierKraus k l) := by
  have hk0 : 0 < k := by linarith
  have hki0 : 0 ≤ k⁻¹ := inv_nonneg.mpr hk0.le
  have hki1 : k⁻¹ ≤ 1 := inv_le_one_of_one_le₀ h1
  have hreal : ∀ l, HasFockMatrix (amplifierKraus k l) (amplifierMatrix k l) := by
    intro l
    let w : ℕ → ℂ := fun m => if l ≤ m then ((k⁻¹ * Real.sqrt (Nat.choose (m - l + l) l : ℝ) *
      Real.sqrt (1 - (k⁻¹) ^ 2) ^ l * (k⁻¹) ^ (m - l) : ℝ) : ℂ) else 0
    refine X7A20_realize _ (fun m => m - l) w ?_ ?_ ?_
    · intro m
      simp only [w]
      split_ifs with hlm
      · simp only [Complex.norm_real, Real.norm_eq_abs]
        have hk2 : 0 ≤ 1 - (k⁻¹) ^ 2 := by nlinarith
        have hC : (0:ℝ) ≤ (Nat.choose (m - l + l) l : ℝ) := Nat.cast_nonneg _
        rw [abs_of_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hki0 (Real.sqrt_nonneg _))
          (pow_nonneg (Real.sqrt_nonneg _) _)) (pow_nonneg hki0 _))]
        have e : k⁻¹ * Real.sqrt (Nat.choose (m - l + l) l : ℝ) * Real.sqrt (1 - (k⁻¹) ^ 2) ^ l *
            (k⁻¹) ^ (m - l) =
            k⁻¹ * Real.sqrt ((Nat.choose (m - l + l) l : ℝ) * (1 - (k⁻¹) ^ 2) ^ l *
              ((k⁻¹) ^ 2) ^ (m - l)) := by
          rw [Real.sqrt_mul (mul_nonneg hC (pow_nonneg hk2 _)), Real.sqrt_mul hC,
            X7A20_sqrt_pow _ hk2, X7A20_sqrt_pow _ (sq_nonneg _), Real.sqrt_sq hki0]
          ring
        rw [e]
        have hs : Real.sqrt ((Nat.choose (m - l + l) l : ℝ) * (1 - (k⁻¹) ^ 2) ^ l *
              ((k⁻¹) ^ 2) ^ (m - l)) ≤ 1 :=
          Real.sqrt_le_one.mpr (X7A20_binom_term _ (sq_nonneg _) (by nlinarith) _ l)
        have hs0 : 0 ≤ Real.sqrt ((Nat.choose (m - l + l) l : ℝ) * (1 - (k⁻¹) ^ 2) ^ l *
              ((k⁻¹) ^ 2) ^ (m - l)) := Real.sqrt_nonneg _
        nlinarith
      · simp
    · intro m n hm hn h
      have hlm : l ≤ m := by
        by_contra hc; exact hm (by simp [w, hc])
      have hln : l ≤ n := by
        by_contra hc; exact hn (by simp [w, hc])
      change m - l = n - l at h
      omega
    · intro m n
      simp only [amplifierMatrix, w]
      by_cases h : m = n + l
      · subst h
        simp
      · by_cases hl : l ≤ m
        · have hn : ¬ m - l = n := by omega
          simp [h, hl, hn]
        · simp [h, hl]
  refine ⟨hreal, fun l => ?_⟩
  refine X7A20_mono_of_matrix _ _ (hreal l) (fun n => n + l)
    (fun n => amplifierMatrix k l (n + l) n) ?_ ?_
  · intro m n
    simp only [amplifierMatrix]
    by_cases h : m = n + l
    · simp [h]
    · simp [h]
  · intro m n _ _ h
    simpa using h

lemma X7A20_phase (k : ℝ) (hk : 0 < k) (l : ℕ) : X7A20_Mono (phaseKraus k l) := by
  refine ⟨fun j => l - j, fun j => if j ≤ l then phaseCoefficient k l j else 0, ?_, ?_⟩
  · intro j
    rw [phaseKraus, if_neg hk.ne', ContinuousLinearMap.sum_apply]
    simp only [ContinuousLinearMap.smul_apply, fockDyad, InnerProductSpace.rankOne_apply,
      X7A20_inner_ket, smul_smul]
    by_cases hj : j ≤ l
    · rw [Finset.sum_eq_single j]
      · simp [hj]
      · intro b _ hb
        simp [hb]
      · intro h
        exact absurd (Finset.mem_range.mpr (by omega)) h
    · rw [Finset.sum_eq_zero]
      · simp [hj]
      · intro b hb
        have : j ≠ b := by
          intro e; subst e; exact hj (by have := Finset.mem_range.mp hb; omega)
        simp [Ne.symm this]
  · intro m n hm hn h
    have hlm : m ≤ l := by
      by_contra hc; exact hm (by simp [hc])
    have hln : n ≤ l := by
      by_contra hc; exact hn (by simp [hc])
    change l - m = l - n at h
    omega

lemma X7A20_family (F : DiscreteFamily) :
    DiscreteRealized F ∧ ∀ l, X7A20_Mono (discreteKraus F l) := by
  cases F with
  | phase k hk => exact ⟨trivial, fun l => X7A20_phase k hk l⟩
  | loss k h0 h1 => exact X7A20_atten k h0 h1
  | gain k h1 => exact X7A20_amp k h1

end QAlgorithms.Papers.Independent.Dependency50.P39

end

noncomputable section

open Filter MeasureTheory
open scoped Topology

attribute [local instance] Classical.propDecidable

open QAlgorithms.Papers.Independent.Dependency50.P39 in
theorem solution (F G : DiscreteFamily) :
    DiscreteRealized F ∧ DiscreteRealized G ∧
    (∀ ell, FockDiagonalEffect (discreteKraus F ell)) ∧
    (∀ p : ℕ × ℕ,
      FockDiagonalEffect (productKraus (discreteKraus F) (discreteKraus G) p)) := by
  obtain ⟨hF, hFm⟩ := X7A20_family F
  obtain ⟨hG, hGm⟩ := X7A20_family G
  refine ⟨hF, hG, fun l => X7A20_Mono_diag (hFm l), fun p => ?_⟩
  exact X7A20_Mono_diag (X7A20_Mono_comp (hFm p.1) (hGm p.2))

end
