-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Dependency50.P39.krausProductIndependence
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-24T04:24:06.194266+00:00
-- url     : https://prove2.me/submissions/cbc8adf2-b618-4aba-86fb-14879d3393e0

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

namespace QAlgorithms.Papers.Independent.Dependency50.P39

namespace X7KP

lemma entry {Wm Wn : FockOperator} (gm : ℕ → ℕ) (cm : ℕ → ℂ)
    (hm : ∀ x, Wm (fockKet x) = cm x • fockKet (gm x)) (gn : ℕ → ℕ) (cn : ℕ → ℂ)
    (hn : ∀ x, Wn (fockKet x) = cn x • fockKet (gn x)) (a b : ℕ) :
    ((ContinuousLinearMap.adjoint Wm).comp Wn) (fockKet b) a =
      (starRingEnd ℂ) (cm a) * cn b * (if gm a = gn b then 1 else 0) := by
  rw [X7A20_coord, ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_right,
    hm, hn, inner_smul_left, inner_smul_right, X7A20_inner_ket]
  ring

lemma sum_coord {ι : Type*} (s : Finset ι) (g : ι → ℂ) (v : ι → FockOperator) (x : Fock) (a : ℕ) :
    ((∑ i ∈ s, g i • v i) x) a = ∑ i ∈ s, g i * (v i x) a := by
  rw [ContinuousLinearMap.sum_apply]
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih =>
    rw [Finset.sum_insert hj, Finset.sum_insert hj, lp.coeFn_add, Pi.add_apply, ih]
    simp

lemma li_of_entries (v : ℕ × ℕ → FockOperator)
    (h : ∀ (s : Finset (ℕ × ℕ)) (g : ℕ × ℕ → ℂ),
      (∀ a b : ℕ, ∑ i ∈ s, g i * (v i (fockKet b)) a = 0) → ∀ i ∈ s, g i = 0) :
    LinearIndependent ℂ v := by
  rw [linearIndependent_iff']
  intro s g hs
  refine h s g (fun a b => ?_)
  rw [← sum_coord, hs]
  rfl

lemma vanish_of_test (E : ℕ × ℕ → ℕ × ℕ → ℂ)
    (key : ∀ s : Finset (ℕ × ℕ), s.Nonempty →
      ∃ i ∈ s, ∃ t : ℕ × ℕ, E i t ≠ 0 ∧ ∀ j ∈ s, j ≠ i → E j t = 0)
    (s : Finset (ℕ × ℕ)) (g : ℕ × ℕ → ℂ) (hs : ∀ t, ∑ i ∈ s, g i * E i t = 0) :
    ∀ i ∈ s, g i = 0 := by
  by_contra hne
  push Not at hne
  obtain ⟨i, hi, hgi⟩ := hne
  set s' := s.filter (fun j => g j ≠ 0)
  have hne' : s'.Nonempty := ⟨i, Finset.mem_filter.mpr ⟨hi, hgi⟩⟩
  obtain ⟨i0, hi0, t, ht, hz⟩ := key s' hne'
  have h1 := hs t
  rw [← Finset.sum_filter_add_sum_filter_not s (fun j => g j ≠ 0)] at h1
  rw [Finset.sum_eq_zero (s := s.filter (fun j => ¬ g j ≠ 0)) (fun j hj => by
    simp only [Finset.mem_filter, not_not] at hj; simp [hj.2]), add_zero] at h1
  rw [Finset.sum_eq_single i0 (fun j hj hji => by rw [hz j hj hji, mul_zero])
    (fun h => absurd hi0 h)] at h1
  have hg0 : g i0 ≠ 0 := (Finset.mem_filter.mp hi0).2
  exact (mul_ne_zero hg0 ht) h1

lemma phase_apply (k : ℝ) (hk : 0 < k) (l j : ℕ) :
    phaseKraus k l (fockKet j) =
      (if j ≤ l then phaseCoefficient k l j else 0) • fockKet (l - j) := by
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

lemma phase_diag_ne (k : ℝ) (hk : 0 < k) (l : ℕ) : phaseCoefficient k l l ≠ 0 := by
  simp only [phaseCoefficient, Nat.sub_self, pow_zero, mul_one, Nat.choose_self, Nat.cast_one,
    Real.sqrt_one, ne_eq, Complex.ofReal_eq_zero]
  have : 0 < Real.sqrt (1 + k ^ 2) := Real.sqrt_pos.mpr (by positivity)
  positivity

theorem phase_li (k : ℝ) (hk : 0 < k) : LinearIndependent ℂ
    (fun p : ℕ × ℕ => (ContinuousLinearMap.adjoint (phaseKraus k p.1)).comp
      (phaseKraus k p.2)) := by
  set c : ℕ → ℕ → ℂ := fun l j => if j ≤ l then phaseCoefficient k l j else 0
  let E : ℕ × ℕ → ℕ × ℕ → ℂ := fun i t =>
    (starRingEnd ℂ) (c i.1 t.1) * c i.2 t.2 * (if i.1 - t.1 = i.2 - t.2 then 1 else 0)
  refine li_of_entries _ (fun s g hs => vanish_of_test E ?_ s g (fun t => ?_))
  · intro s hs
    obtain ⟨i, hi, hmax⟩ := Finset.exists_max_image s Prod.fst hs
    refine ⟨i, hi, i, ?_, ?_⟩
    · simp only [E, c, le_refl, if_true, Nat.sub_self]
      have h1 := phase_diag_ne k hk i.1
      have h2 := phase_diag_ne k hk i.2
      simp [h1, h2]
    · intro j hj hji
      simp only [E, c]
      by_cases h1 : i.1 ≤ j.1
      · by_cases h2 : i.2 ≤ j.2
        · have := hmax j hj
          have hne : ¬ (j.1 - i.1 = j.2 - i.2) := by
            intro h; apply hji; ext <;> omega
          simp [hne]
        · simp [h2]
      · simp [h1]
  · have := hs t.1 t.2
    rw [← this]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [entry (fun j => i.1 - j) (c i.1) (phase_apply k hk i.1)
      (fun j => i.2 - j) (c i.2) (phase_apply k hk i.2)]

lemma atten_apply (k : ℝ) (h0 : 0 ≤ k) (h1 : k ≤ 1) (l n : ℕ) :
    attenuatorKraus k l (fockKet n) =
      (if l ≤ n then attenuatorMatrix k l (n - l) n else 0) • fockKet (n - l) := by
  ext m
  rw [(X7A20_atten k h0 h1).1 l m n, lp.coeFn_smul, Pi.smul_apply, X7A20_ket_apply, smul_eq_mul]
  simp only [attenuatorMatrix]
  by_cases h : n = m + l
  · subst h; simp
  · by_cases hl : l ≤ n
    · have hm : ¬ m = n - l := by omega
      simp [h, hl, hm]
    · simp [h, hl]

theorem atten_li (k : ℝ) (h0 : 0 ≤ k) (h1 : k < 1) : LinearIndependent ℂ
    (fun p : ℕ × ℕ => (ContinuousLinearMap.adjoint (attenuatorKraus k p.1)).comp
      (attenuatorKraus k p.2)) := by
  set c : ℕ → ℕ → ℂ := fun l j => if l ≤ j then attenuatorMatrix k l (j - l) j else 0
  let E : ℕ × ℕ → ℕ × ℕ → ℂ := fun i t =>
    (starRingEnd ℂ) (c i.1 t.1) * c i.2 t.2 * (if t.1 - i.1 = t.2 - i.2 then 1 else 0)
  have hd : ∀ l, attenuatorMatrix k l 0 l ≠ 0 := by
    intro l
    have hs : 0 < Real.sqrt (1 - k ^ 2) := Real.sqrt_pos.mpr (by nlinarith)
    simp only [attenuatorMatrix, zero_add, if_true, Nat.choose_self, Nat.cast_one, Real.sqrt_one,
      one_mul, pow_zero, mul_one, ne_eq, Complex.ofReal_eq_zero]
    positivity
  refine li_of_entries _ (fun s g hs => vanish_of_test E ?_ s g (fun t => ?_))
  · intro s hs
    obtain ⟨i, hi, hmin⟩ := Finset.exists_min_image s Prod.fst hs
    refine ⟨i, hi, i, ?_, ?_⟩
    · simp only [E, c, le_refl, if_true, Nat.sub_self]
      have h1 := hd i.1
      have h2 := hd i.2
      simp [h1, h2]
    · intro j hj hji
      simp only [E, c]
      by_cases h1 : j.1 ≤ i.1
      · by_cases h2 : j.2 ≤ i.2
        · have := hmin j hj
          have hne : ¬ (i.1 - j.1 = i.2 - j.2) := by
            intro h; apply hji; ext <;> omega
          simp [hne]
        · simp [h2]
      · simp [h1]
  · have := hs t.1 t.2
    rw [← this]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [entry (fun j => j - i.1) (c i.1) (atten_apply k h0 h1.le i.1)
      (fun j => j - i.2) (c i.2) (atten_apply k h0 h1.le i.2)]

end X7KP

end QAlgorithms.Papers.Independent.Dependency50.P39

end


noncomputable section

open Filter MeasureTheory
open scoped Topology

attribute [local instance] Classical.propDecidable

namespace QAlgorithms.Papers.Independent.Dependency50.P39

namespace X7KP

lemma ch_mono (N K t : ℕ) : Nat.choose N K ≤ Nat.choose (N + t) (K + t) := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [show N + (t + 1) = (N + t) + 1 by ring, show K + (t + 1) = (K + t) + 1 by ring,
      Nat.choose_succ_succ]
    omega

/-- `C(a+p,p) (a+1) ≤ C(a+p+t,p+t) (p+1)` for `t ≥ 1`. -/
lemma ch_ratio (a p t : ℕ) (ht : 1 ≤ t) :
    (Nat.choose (a + p) p : ℝ) * (a + 1) ≤ (Nat.choose (a + p + t) (p + t) : ℝ) * (p + 1) := by
  have h1 : (a + p + 1) * Nat.choose (a + p) p = Nat.choose (a + p + 1) (p + 1) * (p + 1) :=
    Nat.add_one_mul_choose_eq (a + p) p
  have h2 := ch_mono (a + p + 1) (p + 1) (t - 1)
  rw [show a + p + 1 + (t - 1) = a + p + t by omega, show p + 1 + (t - 1) = p + t by omega] at h2
  have h1' : ((a + p + 1 : ℕ) : ℝ) * (Nat.choose (a + p) p : ℝ) =
      (Nat.choose (a + p + 1) (p + 1) : ℝ) * ((p + 1 : ℕ) : ℝ) := by exact_mod_cast h1
  have h2' : (Nat.choose (a + p + 1) (p + 1) : ℝ) ≤ (Nat.choose (a + p + t) (p + t) : ℝ) := by
    exact_mod_cast h2
  push_cast at h1'
  have hc : (0:ℝ) ≤ Nat.choose (a + p) p := Nat.cast_nonneg _
  have hp : (0:ℝ) ≤ p := Nat.cast_nonneg _
  nlinarith

/-- growth function `F_{p,q}(a) = √C(a+p,p) √C(a+p,q)`. -/
def F (p q a : ℕ) : ℝ := Real.sqrt (Nat.choose (a + p) p) * Real.sqrt (Nat.choose (a + p) q)

lemma F_le (m n p q a : ℕ) (hpm : p < m) (hrel : p + n = q + m) :
    F p q a ≤ F m n a * Real.sqrt (m / (a + 1)) := by
  set t := m - p with ht
  have ht1 : 1 ≤ t := by omega
  have e1 : a + p + t = a + m := by omega
  have e2 : p + t = m := by omega
  have e3 : q + t = n := by omega
  have b1 := ch_ratio a p t ht1
  rw [e1, e2] at b1
  have b2 := ch_mono (a + p) q t
  rw [e1, e3] at b2
  have b2' : (Nat.choose (a + p) q : ℝ) ≤ Nat.choose (a + m) n := by exact_mod_cast b2
  have hpm' : ((p : ℝ) + 1) ≤ m := by exact_mod_cast hpm
  have ha : (0:ℝ) < a + 1 := by positivity
  unfold F
  rw [← Real.sqrt_mul (Nat.cast_nonneg _), ← Real.sqrt_mul (Nat.cast_nonneg _),
    ← Real.sqrt_mul (by positivity)]
  apply Real.sqrt_le_sqrt
  have hA : (Nat.choose (a + p) p : ℝ) ≤ Nat.choose (a + m) m * (m / (a + 1)) := by
    rw [mul_div_assoc', le_div_iff₀ ha]
    have : (0:ℝ) ≤ Nat.choose (a + m) m := Nat.cast_nonneg _
    nlinarith
  calc (Nat.choose (a + p) p : ℝ) * Nat.choose (a + p) q
      ≤ (Nat.choose (a + m) m * (m / (a + 1))) * Nat.choose (a + m) n :=
        mul_le_mul hA b2' (Nat.cast_nonneg _) (by positivity)
    _ = _ := by ring

lemma F_nonneg (p q a : ℕ) : 0 ≤ F p q a := by unfold F; positivity

lemma F_pos (p q a : ℕ) (hq : q ≤ a + p) : 0 < F p q a := by
  unfold F
  have h1 : (0:ℝ) < Nat.choose (a + p) p := by exact_mod_cast Nat.choose_pos (by omega)
  have h2 : (0:ℝ) < Nat.choose (a + p) q := by exact_mod_cast Nat.choose_pos hq
  positivity

lemma top_vanish (T : Finset (ℕ × ℕ)) (i : ℕ × ℕ) (hi : i ∈ T)
    (hrel : ∀ j ∈ T, j.1 + i.2 = j.2 + i.1) (hmax : ∀ j ∈ T, j.1 ≤ i.1)
    (h : ℕ × ℕ → ℂ) (A : ℕ)
    (hs : ∀ a, A ≤ a → ∑ j ∈ T, h j * ((F j.1 j.2 a : ℝ) : ℂ) = 0) : h i = 0 := by
  set K := ∑ j ∈ T.erase i, ‖h j‖
  have hbound : ∀ a, max A i.2 ≤ a → ‖h i‖ ≤ K * Real.sqrt (i.1 / ((a:ℝ) + 1)) := by
    intro a ha
    have hFi := F_pos i.1 i.2 a (by omega)
    have e := hs a (le_of_max_le_left ha)
    rw [← Finset.add_sum_erase T _ hi] at e
    have e2 : h i * ((F i.1 i.2 a : ℝ) : ℂ) = -∑ j ∈ T.erase i, h j * ((F j.1 j.2 a : ℝ) : ℂ) :=
      eq_neg_of_add_eq_zero_left e
    have hn : ‖h i‖ * F i.1 i.2 a ≤ ∑ j ∈ T.erase i, ‖h j‖ * (F i.1 i.2 a *
        Real.sqrt (i.1 / ((a:ℝ) + 1))) := by
      have := congrArg norm e2
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hFi.le, norm_neg] at this
      rw [this]
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum (fun j hj => ?_))
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (F_nonneg _ _ _)]
      refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
      have hjT := Finset.mem_of_mem_erase hj
      have hji := Finset.ne_of_mem_erase hj
      have hr := hrel j hjT
      have hm := hmax j hjT
      have hlt : j.1 < i.1 := by
        rcases lt_or_eq_of_le hm with h' | h'
        · exact h'
        · exact absurd (Prod.ext h' (by omega)) hji
      exact F_le i.1 i.2 j.1 j.2 a hlt (by omega)
    rw [← Finset.sum_mul] at hn
    have : ‖h i‖ * F i.1 i.2 a ≤ (K * Real.sqrt (i.1 / ((a:ℝ) + 1))) * F i.1 i.2 a := by
      calc _ ≤ _ := hn
        _ = _ := by ring
    exact le_of_mul_le_mul_right this hFi
  have ht : Tendsto (fun a : ℕ => K * Real.sqrt (i.1 / ((a:ℝ) + 1))) atTop (𝓝 0) := by
    have h1 : Tendsto (fun a : ℕ => (i.1 : ℝ) / ((a:ℝ) + 1)) atTop (𝓝 0) := by
      have := (tendsto_const_div_atTop_nhds_zero_nat (i.1 : ℝ)).comp (tendsto_add_atTop_nat 1)
      refine this.congr (fun a => ?_)
      simp
    have h2 := ((Real.continuous_sqrt.tendsto 0).comp h1).const_mul K
    simpa using h2
  have hle : ‖h i‖ ≤ 0 := ge_of_tendsto ht (eventually_atTop.2 ⟨max A i.2, hbound⟩)
  exact norm_le_zero_iff.mp hle

lemma amp_apply (k : ℝ) (h1 : 1 ≤ k) (l n : ℕ) :
    amplifierKraus k l (fockKet n) = amplifierMatrix k l (n + l) n • fockKet (n + l) := by
  ext m
  rw [(X7A20_amp k h1).1 l m n, lp.coeFn_smul, Pi.smul_apply, X7A20_ket_apply, smul_eq_mul]
  by_cases h : m = n + l
  · subst h; simp
  · simp [amplifierMatrix, h]

lemma amp_prod (k : ℝ) (p q a b : ℕ) (hab : a + p = b + q) :
    (starRingEnd ℂ) (amplifierMatrix k p (a + p) a) * amplifierMatrix k q (b + q) b =
      ((k⁻¹ ^ 2 * k⁻¹ ^ (a + b) *
        (Real.sqrt (1 - (k⁻¹) ^ 2) ^ (p + q) * F p q a) : ℝ) : ℂ) := by
  simp only [amplifierMatrix, if_true, Complex.conj_ofReal]
  rw [← Complex.ofReal_mul]
  congr 1
  unfold F
  rw [← hab]
  ring

theorem amp_li (k : ℝ) (hk : 1 < k) : LinearIndependent ℂ
    (fun p : ℕ × ℕ => (ContinuousLinearMap.adjoint (amplifierKraus k p.1)).comp
      (amplifierKraus k p.2)) := by
  set c : ℕ → ℕ → ℂ := fun l x => amplifierMatrix k l (x + l) x
  have hs0 : 0 < Real.sqrt (1 - (k⁻¹) ^ 2) := by
    apply Real.sqrt_pos.mpr
    have : k⁻¹ < 1 := inv_lt_one_of_one_lt₀ hk
    have : 0 < k⁻¹ := inv_pos.mpr (by linarith)
    nlinarith
  have hk0 : k⁻¹ ≠ 0 := inv_ne_zero (by linarith)
  refine li_of_entries _ (fun s g hs => ?_)
  have hs' : ∀ a b : ℕ, ∑ i ∈ s, g i * ((starRingEnd ℂ) (c i.1 a) * c i.2 b *
      (if a + i.1 = b + i.2 then 1 else 0)) = 0 := by
    intro a b
    refine Eq.trans (Finset.sum_congr rfl (fun i _ => ?_)) (hs a b)
    rw [entry (fun x => x + i.1) (c i.1) (amp_apply k hk.le i.1)
      (fun x => x + i.2) (c i.2) (amp_apply k hk.le i.2)]
  by_contra hne
  push Not at hne
  obtain ⟨i0, hi0, hgi0⟩ := hne
  set T := s.filter (fun j => g j ≠ 0 ∧ j.1 + i0.2 = j.2 + i0.1)
  have hT : T.Nonempty := ⟨i0, Finset.mem_filter.mpr ⟨hi0, hgi0, add_comm _ _⟩⟩
  obtain ⟨i, hi, hmax⟩ := Finset.exists_max_image T Prod.fst hT
  have hiT := Finset.mem_filter.mp hi
  have hrel : ∀ j ∈ T, j.1 + i.2 = j.2 + i.1 := by
    intro j hj
    have := (Finset.mem_filter.mp hj).2.2
    have := hiT.2.2
    omega
  have key := top_vanish T i hi hrel hmax
    (fun j => g j * ((Real.sqrt (1 - (k⁻¹) ^ 2) ^ (j.1 + j.2) : ℝ) : ℂ)) i.2 (fun a ha => ?_)
  · have : ((Real.sqrt (1 - (k⁻¹) ^ 2) ^ (i.1 + i.2) : ℝ) : ℂ) ≠ 0 := by
      rw [Complex.ofReal_ne_zero]; positivity
    exact hiT.2.1 ((mul_eq_zero.mp key).resolve_right this)
  · set b := a + i.1 - i.2
    have h := hs' a b
    rw [← Finset.sum_filter_add_sum_filter_not s
      (fun j => g j ≠ 0 ∧ j.1 + i0.2 = j.2 + i0.1)] at h
    rw [Finset.sum_eq_zero (s := s.filter (fun j => ¬ (g j ≠ 0 ∧ j.1 + i0.2 = j.2 + i0.1)))
      (fun j hj => ?_), add_zero] at h
    · have hκ : ((k⁻¹ ^ 2 * k⁻¹ ^ (a + b) : ℝ) : ℂ) ≠ 0 := by
        rw [Complex.ofReal_ne_zero]; positivity
      have h' : ((k⁻¹ ^ 2 * k⁻¹ ^ (a + b) : ℝ) : ℂ) * ∑ j ∈ T,
          g j * ((Real.sqrt (1 - (k⁻¹) ^ 2) ^ (j.1 + j.2) : ℝ) : ℂ) * ((F j.1 j.2 a : ℝ) : ℂ) = 0 := by
        rw [← h, Finset.mul_sum]
        refine Finset.sum_congr rfl (fun j hj => ?_)
        have hab : a + j.1 = b + j.2 := by have := hrel j hj; omega
        simp only [c]
        rw [if_pos hab, mul_one, amp_prod k j.1 j.2 a b hab]
        push_cast; ring
      exact (mul_eq_zero.mp h').resolve_left hκ
    · simp only [Finset.mem_filter, not_and_or, not_not] at hj
      rcases hj.2 with h0 | h0
      · rw [h0, zero_mul]
      · have : ¬ (a + j.1 = b + j.2) := by
          intro e; apply h0; have := hiT.2.2; omega
        rw [if_neg this, mul_zero, mul_zero]

theorem main :
    (∀ k : ℝ, 0 < k → LinearIndependent ℂ
      (fun p : ℕ × ℕ => (ContinuousLinearMap.adjoint (phaseKraus k p.1)).comp
        (phaseKraus k p.2))) ∧
    (∀ k : ℝ, 0 ≤ k → k < 1 → AttenuatorRealized k ∧ LinearIndependent ℂ
      (fun p : ℕ × ℕ => (ContinuousLinearMap.adjoint (attenuatorKraus k p.1)).comp
        (attenuatorKraus k p.2))) ∧
    (∀ k : ℝ, 1 < k → AmplifierRealized k ∧ LinearIndependent ℂ
      (fun p : ℕ × ℕ => (ContinuousLinearMap.adjoint (amplifierKraus k p.1)).comp
        (amplifierKraus k p.2))) :=
  ⟨fun k hk => phase_li k hk,
   fun k h0 h1 => ⟨(X7A20_atten k h0 h1.le).1, atten_li k h0 h1⟩,
   fun k hk => ⟨(X7A20_amp k hk.le).1, amp_li k hk⟩⟩

end X7KP

end QAlgorithms.Papers.Independent.Dependency50.P39

end

noncomputable section

open Filter MeasureTheory
open scoped Topology

attribute [local instance] Classical.propDecidable

open QAlgorithms.Papers.Independent.Dependency50.P39 in
theorem solution :
    (∀ k : ℝ, 0 < k → LinearIndependent ℂ
      (fun p : ℕ × ℕ => (ContinuousLinearMap.adjoint (phaseKraus k p.1)).comp
        (phaseKraus k p.2))) ∧
    (∀ k : ℝ, 0 ≤ k → k < 1 → AttenuatorRealized k ∧ LinearIndependent ℂ
      (fun p : ℕ × ℕ => (ContinuousLinearMap.adjoint (attenuatorKraus k p.1)).comp
        (attenuatorKraus k p.2))) ∧
    (∀ k : ℝ, 1 < k → AmplifierRealized k ∧ LinearIndependent ℂ
      (fun p : ℕ × ℕ => (ContinuousLinearMap.adjoint (amplifierKraus k p.1)).comp
        (amplifierKraus k p.2))) :=
  QAlgorithms.Papers.Independent.Dependency50.P39.X7KP.main

end
