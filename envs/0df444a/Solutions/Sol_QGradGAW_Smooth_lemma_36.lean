-- Prove2me | solution 1 for QGradGAW.Smooth.lemma_36
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T17:41:36.845618+00:00
-- url     : https://prove2.me/submissions/d935b1ce-184e-4a9c-8d9e-1ced7c0ad692

import Mathlib

set_option autoImplicit false
open MeasureTheory ProbabilityTheory

section L36
variable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]

lemma l36_int {d : ℕ} (X : Fin d → Ω → ℝ) (hXm : ∀ i, Measurable (X i))
    (hbdd : ∀ i ω, X i ω ∈ Set.Icc (-(1 / 2 : ℝ)) (1 / 2))
    {ι : Type*} [Fintype ι] (w : ι → Fin d) :
    Integrable (fun ω => ∏ j, X (w j) ω) P := by
  refine Integrable.of_bound (C := 1) ?_ ?_
  · exact (Finset.measurable_prod _ (fun j _ => hXm (w j))).aestronglyMeasurable
  · refine Filter.Eventually.of_forall (fun ω => ?_)
    rw [norm_prod]
    apply Finset.prod_le_one (fun _ _ => norm_nonneg _)
    intro j _
    have := hbdd (w j) ω
    rw [Real.norm_eq_abs, abs_le]
    constructor <;> linarith [this.1, this.2]

lemma l36_nonneg {d : ℕ} (X : Fin d → Ω → ℝ) (hXm : ∀ i, Measurable (X i)) (hind : iIndepFun X P)
    (hmom : ∀ i, ∀ j : ℕ, ∫ ω, X i ω ^ (2 * j + 1) ∂P = 0)
    {ι : Type*} [Fintype ι] (w : ι → Fin d) :
    0 ≤ ∫ ω, ∏ j, X (w j) ω ∂P := by
  classical
  have h1 : ∀ ω, ∏ j, X (w j) ω =
      ∏ i, (X i ω) ^ (Finset.univ.filter (fun j => w j = i)).card := by
    intro ω
    rw [← Finset.prod_fiberwise_of_maps_to (s := Finset.univ) (t := Finset.univ) (g := w)
      (fun x _ => Finset.mem_univ _)]
    apply Finset.prod_congr rfl
    intro i _
    rw [← Finset.prod_const]
    apply Finset.prod_congr rfl
    intro j hj
    rw [(Finset.mem_filter.1 hj).2]
  simp_rw [h1]
  rw [iIndepFun.integral_fun_prod_comp (f := fun i x => x ^ (Finset.univ.filter (fun j => w j = i)).card)
    hind (fun i => (hXm i).aemeasurable) (fun i => (continuous_pow _).aestronglyMeasurable)]
  apply Finset.prod_nonneg
  intro i _
  rcases Nat.even_or_odd (Finset.univ.filter (fun j => w j = i)).card with he | ⟨j, hj⟩
  · exact integral_nonneg (fun ω => he.pow_nonneg _)
  · rw [hj]; exact (hmom i j).ge

lemma l36_expand {d k : ℕ} (X : Fin d → Ω → ℝ) (hXm : ∀ i, Measurable (X i))
    (hbdd : ∀ i ω, X i ω ∈ Set.Icc (-(1 / 2 : ℝ)) (1 / 2))
    (G : (Fin k → Fin d) → ℝ) :
    ∫ ω, (∑ α : Fin k → Fin d, G α * ∏ j, X (α j) ω) ^ 2 ∂P =
      ∑ α : Fin k → Fin d, ∑ β : Fin k → Fin d,
        G α * G β * ∫ ω, ∏ j : Fin k ⊕ Fin k, X (Sum.elim α β j) ω ∂P := by
  have e : ∀ ω, (∑ α : Fin k → Fin d, G α * ∏ j, X (α j) ω) ^ 2 =
      ∑ α : Fin k → Fin d, ∑ β : Fin k → Fin d,
        G α * G β * ∏ j : Fin k ⊕ Fin k, X (Sum.elim α β j) ω := by
    intro ω
    rw [sq, Finset.sum_mul_sum]
    apply Finset.sum_congr rfl; intro α _
    apply Finset.sum_congr rfl; intro β _
    rw [Fintype.prod_sum_type]
    simp only [Sum.elim_inl, Sum.elim_inr]
    ring
  simp_rw [e]
  rw [integral_finsetSum _ (fun α _ => integrable_finsetSum _ (fun β _ =>
    (l36_int P X hXm hbdd (Sum.elim α β)).const_mul _))]
  apply Finset.sum_congr rfl; intro α _
  rw [integral_finsetSum _ (fun β _ => (l36_int P X hXm hbdd (Sum.elim α β)).const_mul _)]
  apply Finset.sum_congr rfl; intro β _
  rw [integral_const_mul]

lemma l36_second {d k : ℕ} (X : Fin d → Ω → ℝ) (hXm : ∀ i, Measurable (X i))
    (hbdd : ∀ i ω, X i ω ∈ Set.Icc (-(1 / 2 : ℝ)) (1 / 2))
    (hind : iIndepFun X P)
    (hmom : ∀ i, ∀ j : ℕ, ∫ ω, X i ω ^ (2 * j + 1) ∂P = 0)
    (H : (Fin k → Fin d) → ℝ) (hH : ∀ α, |H α| ≤ 1) :
    ∫ ω, (∑ α : Fin k → Fin d, H α * ∏ j, X (α j) ω) ^ 2 ∂P ≤
      ∫ ω, (∑ i, X i ω) ^ (2 * k) ∂P := by
  have hpow : ∀ ω, (∑ i, X i ω) ^ k = ∑ α : Fin k → Fin d, ∏ j, X (α j) ω := by
    intro ω
    have := Finset.prod_univ_sum (fun (_ : Fin k) => (Finset.univ : Finset (Fin d)))
      (fun _ i => X i ω)
    simpa [Fintype.piFinset_univ] using this
  have hZ : ∀ ω, (∑ i, X i ω) ^ (2 * k) =
      (∑ α : Fin k → Fin d, (fun _ => (1:ℝ)) α * ∏ j, X (α j) ω) ^ 2 := by
    intro ω
    rw [pow_mul', hpow]
    simp
  simp_rw [hZ]
  rw [l36_expand P X hXm hbdd, l36_expand P X hXm hbdd]
  apply Finset.sum_le_sum; intro α _
  apply Finset.sum_le_sum; intro β _
  have hM := l36_nonneg P X hXm hind hmom (Sum.elim α β)
  have h1 : H α * H β ≤ 1 := by
    calc H α * H β ≤ |H α * H β| := le_abs_self _
      _ = |H α| * |H β| := abs_mul _ _
      _ ≤ 1 * 1 := mul_le_mul (hH α) (hH β) (abs_nonneg _) (by norm_num)
      _ = 1 := by norm_num
  calc H α * H β * ∫ ω, ∏ j : Fin k ⊕ Fin k, X (Sum.elim α β j) ω ∂P
      ≤ 1 * ∫ ω, ∏ j : Fin k ⊕ Fin k, X (Sum.elim α β j) ω ∂P :=
        mul_le_mul_of_nonneg_right h1 hM
    _ = _ := by ring

lemma l36_cosh (x : ℝ) (k : ℕ) : x ^ (2 * k) / ((2 * k).factorial : ℝ) ≤ Real.cosh x := by
  have h := Real.hasSum_cosh x
  exact le_hasSum h k (fun j _ => div_nonneg ((even_two_mul j).pow_nonneg x) (by positivity))

lemma l36_subG {d : ℕ} (X : Fin d → Ω → ℝ) (hXm : ∀ i, Measurable (X i))
    (hbdd : ∀ i ω, X i ω ∈ Set.Icc (-(1 / 2 : ℝ)) (1 / 2))
    (hind : iIndepFun X P)
    (hmom : ∀ i, ∀ j : ℕ, ∫ ω, X i ω ^ (2 * j + 1) ∂P = 0) :
    HasSubgaussianMGF (fun ω => ∑ i ∈ Finset.univ, X i ω)
      (∑ i : Fin d, (‖(1/2:ℝ) - -(1/2)‖₊/2)^2) P := by
  apply HasSubgaussianMGF.sum_of_iIndepFun hind (c := fun _ => (‖(1/2:ℝ) - -(1/2)‖₊/2)^2)
  intro i _
  apply hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero (hXm i).aemeasurable
  · exact Filter.Eventually.of_forall (hbdd i)
  · simpa using hmom i 0

lemma l36_moment {d k : ℕ} (X : Fin d → Ω → ℝ) (hXm : ∀ i, Measurable (X i))
    (hbdd : ∀ i ω, X i ω ∈ Set.Icc (-(1 / 2 : ℝ)) (1 / 2))
    (hind : iIndepFun X P)
    (hmom : ∀ i, ∀ j : ℕ, ∫ ω, X i ω ^ (2 * j + 1) ∂P = 0) (lam : ℝ) (hlam : 0 < lam) :
    ∫ ω, (∑ i, X i ω) ^ (2 * k) ∂P ≤
      ((2 * k).factorial : ℝ) / lam ^ (2 * k) * Real.exp ((d:ℝ) / 4 * lam ^ 2 / 2) := by
  have hG := l36_subG P X hXm hbdd hind hmom
  have hc : ((∑ i : Fin d, (‖(1/2:ℝ) - -(1/2)‖₊/2)^2 : NNReal) : ℝ) = (d:ℝ) / 4 := by
    push_cast
    simp [Real.norm_eq_abs]
    norm_num
    ring
  have h1 := hG.mgf_le lam
  have h2 := hG.mgf_le (-lam)
  rw [hc] at h1 h2
  have hi1 := hG.integrable_exp_mul lam
  have hi2 := hG.integrable_exp_mul (-lam)
  have hZm : Measurable (fun ω => ∑ i, X i ω) := Finset.measurable_sum _ (fun i _ => hXm i)
  have hZb : ∀ ω, |∑ i, X i ω| ≤ d := by
    intro ω
    calc |∑ i, X i ω| ≤ ∑ i, |X i ω| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i : Fin d, (1:ℝ) := by
          apply Finset.sum_le_sum; intro i _
          have := hbdd i ω
          rw [abs_le]; constructor <;> linarith [this.1, this.2]
      _ = d := by simp
  have hZint : Integrable (fun ω => (∑ i, X i ω) ^ (2 * k)) P := by
    refine Integrable.of_bound (C := (d:ℝ)^(2*k)) (hZm.pow_const _).aestronglyMeasurable ?_
    refine Filter.Eventually.of_forall (fun ω => ?_)
    rw [norm_pow, Real.norm_eq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) (hZb ω) _
  have hf : (0:ℝ) < ((2 * k).factorial : ℝ) := by positivity
  have hl : (0:ℝ) < lam ^ (2 * k) := by positivity
  have hpt : ∀ ω, (∑ i, X i ω) ^ (2 * k) ≤ ((2 * k).factorial : ℝ) / lam ^ (2 * k) *
      ((Real.exp (lam * ∑ i, X i ω) + Real.exp (-lam * ∑ i, X i ω)) / 2) := by
    intro ω
    have h := l36_cosh (lam * ∑ i, X i ω) k
    rw [Real.cosh_eq, mul_pow, div_le_iff₀ hf] at h
    rw [div_mul_eq_mul_div, le_div_iff₀ hl, neg_mul]
    calc (∑ i, X i ω) ^ (2 * k) * lam ^ (2 * k) = lam ^ (2 * k) * (∑ i, X i ω) ^ (2 * k) :=
          mul_comm _ _
      _ ≤ _ := h
      _ = _ := mul_comm _ _
  have hint2 : Integrable (fun ω => ((2 * k).factorial : ℝ) / lam ^ (2 * k) *
      ((Real.exp (lam * ∑ i, X i ω) + Real.exp (-lam * ∑ i, X i ω)) / 2)) P :=
    ((hi1.add hi2).div_const 2).const_mul _
  calc ∫ ω, (∑ i, X i ω) ^ (2 * k) ∂P
      ≤ ∫ ω, ((2 * k).factorial : ℝ) / lam ^ (2 * k) *
      ((Real.exp (lam * ∑ i, X i ω) + Real.exp (-lam * ∑ i, X i ω)) / 2) ∂P :=
        integral_mono hZint hint2 hpt
    _ = ((2 * k).factorial : ℝ) / lam ^ (2 * k) *
        ((mgf (fun ω => ∑ i, X i ω) P lam + mgf (fun ω => ∑ i, X i ω) P (-lam)) / 2) := by
        rw [integral_const_mul, integral_div, integral_add hi1 hi2]
        rfl
    _ ≤ ((2 * k).factorial : ℝ) / lam ^ (2 * k) * Real.exp ((d:ℝ) / 4 * lam ^ 2 / 2) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        have h2' : mgf (fun ω => ∑ i, X i ω) P (-lam) ≤ Real.exp ((d:ℝ) / 4 * lam ^ 2 / 2) := by
          have := h2; rwa [neg_sq] at this
        linarith

lemma l36_exp_half : Real.exp (1 / 2) ≤ 2 := by
  have h1 := Real.exp_one_lt_d9
  have h2 : Real.exp (1 / 2) * Real.exp (1 / 2) = Real.exp 1 := by
    rw [← Real.exp_add]; norm_num
  have h3 := Real.exp_pos (1 / 2)
  nlinarith

lemma l36_fact (k : ℕ) (hk : 1 ≤ k) :
    ((2 * k).factorial : ℝ) * Real.exp ((k : ℝ) / 2) ≤ 2 * (2 * (k : ℝ) ^ 2) ^ k := by
  induction k, hk using Nat.le_induction with
  | base =>
    have := l36_exp_half
    norm_num [Nat.factorial]
    linarith
  | succ k hk ih =>
    have hk1 : (1:ℝ) ≤ k := by exact_mod_cast hk
    have hb : 2 * (k:ℝ) ^ k ≤ ((k:ℝ) + 1) ^ k := by
      have h := one_add_mul_le_pow (a := 1 / (k:ℝ)) (by
        have : (0:ℝ) ≤ 1 / (k:ℝ) := by positivity
        linarith) k
      have hkpos : (0:ℝ) < k := by linarith
      have e : ((k:ℝ) + 1) ^ k = (k:ℝ) ^ k * (1 + 1 / (k:ℝ)) ^ k := by
        rw [← mul_pow]; congr 1; field_simp
      rw [e]
      have : 1 + (k:ℝ) * (1 / (k:ℝ)) = 2 := by field_simp; norm_num
      rw [this] at h
      have hp : (0:ℝ) < (k:ℝ) ^ k := by positivity
      nlinarith
    have hc : 4 * (2 * (k:ℝ) ^ 2) ^ k ≤ (2 * ((k:ℝ) + 1) ^ 2) ^ k := by
      have e1 : (2 * ((k:ℝ) + 1) ^ 2) ^ k = 2 ^ k * (((k:ℝ) + 1) ^ k) ^ 2 := by
        rw [mul_pow, ← pow_mul, ← pow_mul, mul_comm 2 k]
      have e2 : (2 * (k:ℝ) ^ 2) ^ k = 2 ^ k * ((k:ℝ) ^ k) ^ 2 := by
        rw [mul_pow, ← pow_mul, ← pow_mul, mul_comm 2 k]
      rw [e1, e2]
      have h2 : (0:ℝ) < 2 ^ k := by positivity
      have h3 : 0 ≤ 2 * (k:ℝ) ^ k := by positivity
      have : (2 * (k:ℝ) ^ k) ^ 2 ≤ (((k:ℝ) + 1) ^ k) ^ 2 := pow_le_pow_left₀ h3 hb 2
      nlinarith
    have hfac : ((2 * (k + 1)).factorial : ℝ) =
        ((2 * (k:ℝ) + 2) * (2 * (k:ℝ) + 1)) * ((2 * k).factorial : ℝ) := by
      rw [show 2 * (k + 1) = (2 * k + 1) + 1 by ring, Nat.factorial_succ, Nat.factorial_succ]
      push_cast; ring
    have hexp : Real.exp (((k + 1 : ℕ) : ℝ) / 2) ≤ Real.exp ((k : ℝ) / 2) * 2 := by
      have : ((k + 1 : ℕ) : ℝ) / 2 = (k : ℝ) / 2 + 1 / 2 := by push_cast; ring
      rw [this, Real.exp_add]
      exact mul_le_mul_of_nonneg_left l36_exp_half (Real.exp_pos _).le
    rw [hfac]
    push_cast
    have hF : (0:ℝ) ≤ ((2 * k).factorial : ℝ) := by positivity
    have hP : (0:ℝ) ≤ (2 * (k:ℝ) ^ 2) ^ k := by positivity
    have hE : (0:ℝ) < Real.exp ((k : ℝ) / 2) := Real.exp_pos _
    have hE' : Real.exp (((k:ℝ) + 1) / 2) ≤ Real.exp ((k : ℝ) / 2) * 2 := by
      have := hexp; push_cast at this; exact this
    calc (2 * (k:ℝ) + 2) * (2 * (k:ℝ) + 1) * ((2 * k).factorial : ℝ) * Real.exp (((k:ℝ) + 1) / 2)
        ≤ (2 * (k:ℝ) + 2) * (2 * (k:ℝ) + 1) * ((2 * k).factorial : ℝ) * (Real.exp ((k : ℝ) / 2) * 2) := by
          apply mul_le_mul_of_nonneg_left hE' (by positivity)
      _ = 2 * ((2 * (k:ℝ) + 2) * (2 * (k:ℝ) + 1)) * (((2 * k).factorial : ℝ) * Real.exp ((k : ℝ) / 2)) := by ring
      _ ≤ 2 * ((2 * (k:ℝ) + 2) * (2 * (k:ℝ) + 1)) * (2 * (2 * (k:ℝ) ^ 2) ^ k) := by
          apply mul_le_mul_of_nonneg_left ih (by positivity)
      _ ≤ 2 * (2 * ((k:ℝ) + 1) ^ 2) * (4 * (2 * (k:ℝ) ^ 2) ^ k) := by
          have : (2 * (k:ℝ) + 2) * (2 * (k:ℝ) + 1) ≤ 4 * ((k:ℝ) + 1) ^ 2 := by nlinarith
          have h5 : 2 * ((2 * (k:ℝ) + 2) * (2 * (k:ℝ) + 1)) * (2 * (2 * (k:ℝ) ^ 2) ^ k)
              = 4 * ((2 * (k:ℝ) + 2) * (2 * (k:ℝ) + 1)) * (2 * (k:ℝ) ^ 2) ^ k := by ring
          rw [h5]
          nlinarith [mul_le_mul_of_nonneg_right this hP]
      _ ≤ 2 * (2 * ((k:ℝ) + 1) ^ 2) * (2 * ((k:ℝ) + 1) ^ 2) ^ k := by
          apply mul_le_mul_of_nonneg_left hc (by positivity)
      _ = 2 * (2 * ((k:ℝ) + 1) ^ 2) ^ (k + 1) := by ring

lemma l36_second_moment {d k : ℕ} (hd : 1 ≤ d) (hk : 1 ≤ k) (X : Fin d → Ω → ℝ)
    (hXm : ∀ i, Measurable (X i))
    (hbdd : ∀ i ω, X i ω ∈ Set.Icc (-(1 / 2 : ℝ)) (1 / 2))
    (hind : iIndepFun X P)
    (hmom : ∀ i, ∀ j : ℕ, ∫ ω, X i ω ^ (2 * j + 1) ∂P = 0)
    (H : (Fin k → Fin d) → ℝ) (hH : ∀ α, |H α| ≤ 1) :
    ∫ ω, (∑ α : Fin k → Fin d, H α * ∏ j, X (α j) ω) ^ 2 ∂P ≤ 2 * ((d : ℝ) * k / 2) ^ k := by
  have h1 := l36_second P X hXm hbdd hind hmom H hH
  have hdr : (0:ℝ) < d := by exact_mod_cast hd
  have hkr : (0:ℝ) < k := by exact_mod_cast hk
  set lam := Real.sqrt (4 * k / d) with hlamdef
  have hlam : 0 < lam := Real.sqrt_pos.2 (by positivity)
  have h2 := l36_moment (k := k) P X hXm hbdd hind hmom lam hlam
  have hl2 : lam ^ 2 = 4 * k / d := Real.sq_sqrt (by positivity)
  have hl2k : lam ^ (2 * k) = (4 * k / d) ^ k := by rw [pow_mul, hl2]
  have hexp : (d:ℝ) / 4 * lam ^ 2 / 2 = k / 2 := by rw [hl2]; field_simp
  rw [hl2k, hexp] at h2
  have h3 := l36_fact k hk
  have e : ((4 * (k:ℝ) / d) ^ k)⁻¹ = ((d:ℝ) / (4 * k)) ^ k := by rw [← inv_pow, inv_div]
  have e2 : 2 * (k:ℝ) ^ 2 * ((d:ℝ) / (4 * k)) = d * k / 2 := by field_simp; ring
  calc _ ≤ _ := h1
    _ ≤ _ := h2
    _ = (((2 * k).factorial : ℝ) * Real.exp ((k:ℝ) / 2)) * ((d:ℝ) / (4 * k)) ^ k := by
        rw [div_eq_mul_inv, e]; ring
    _ ≤ (2 * (2 * (k:ℝ) ^ 2) ^ k) * ((d:ℝ) / (4 * k)) ^ k :=
        mul_le_mul_of_nonneg_right h3 (by positivity)
    _ = 2 * ((d : ℝ) * k / 2) ^ k := by
        rw [mul_assoc, ← mul_pow, e2]

end L36

theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (d k : ℕ) (hd : 1 ≤ d) (hk : 1 ≤ k) (H : (Fin k → Fin d) → ℝ) (hH : ∀ α, |H α| ≤ 1)
    (X : Fin d → Ω → ℝ) (hXm : ∀ i, Measurable (X i)) (hind : iIndepFun X P)
    (hid : ∀ i j, IdentDistrib (X i) (X j) P P)
    (hsymm : ∀ i, IdentDistrib (X i) (fun ω => -X i ω) P P)
    (hbdd : ∀ i ω, X i ω ∈ Set.Icc (-(1 / 2 : ℝ)) (1 / 2))
    (hmom : ∀ i, ∀ j : ℕ, ∫ ω, X i ω ^ (2 * j + 1) ∂P = 0)
    (r : ℝ) (hr : 0 < r) :
    P {ω | Real.sqrt 2 * (r * Real.sqrt ((d : ℝ) * k / 2)) ^ k ≤
        |∑ α : Fin k → Fin d, H α * ∏ j, X (α j) ω|} ≤ ENNReal.ofReal (1 / r ^ (2 * k)) := by
  have hdr : (0:ℝ) < d := by exact_mod_cast hd
  have hkr : (0:ℝ) < k := by exact_mod_cast hk
  set S : Ω → ℝ := fun ω => ∑ α : Fin k → Fin d, H α * ∏ j, X (α j) ω with hS
  set t : ℝ := Real.sqrt 2 * (r * Real.sqrt ((d : ℝ) * k / 2)) ^ k with ht
  have ht0 : 0 < t := by positivity
  have hA : (0:ℝ) < ((d : ℝ) * k / 2) ^ k := by positivity
  have ht2 : t ^ 2 = 2 * r ^ (2 * k) * ((d : ℝ) * k / 2) ^ k := by
    have hq : ((r * Real.sqrt ((d : ℝ) * k / 2)) ^ k) ^ 2 = (r ^ 2 * ((d : ℝ) * k / 2)) ^ k := by
      rw [← pow_mul, mul_comm k 2, pow_mul, mul_pow, Real.sq_sqrt (by positivity)]
    rw [ht, mul_pow, Real.sq_sqrt (by norm_num), hq, mul_pow, ← pow_mul]
    ring
  have hSm : Measurable S :=
    Finset.measurable_sum _ (fun α _ => measurable_const.mul
      (Finset.measurable_prod _ (fun j _ => hXm (α j))))
  have hSb : ∀ ω, |S ω| ≤ (Fintype.card (Fin k → Fin d) : ℝ) := by
    intro ω
    calc |S ω| ≤ ∑ α : Fin k → Fin d, |H α * ∏ j, X (α j) ω| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _α : Fin k → Fin d, (1:ℝ) := by
          apply Finset.sum_le_sum; intro α _
          rw [abs_mul, Finset.abs_prod]
          have h1 : ∏ j, |X (α j) ω| ≤ 1 := by
            apply Finset.prod_le_one (fun _ _ => abs_nonneg _)
            intro j _
            have := hbdd (α j) ω
            rw [abs_le]; constructor <;> linarith [this.1, this.2]
          calc |H α| * ∏ j, |X (α j) ω| ≤ 1 * 1 :=
                mul_le_mul (hH α) h1 (Finset.prod_nonneg (fun _ _ => abs_nonneg _)) (by norm_num)
            _ = 1 := by norm_num
      _ = _ := by simp
  have hSint : Integrable (fun ω => S ω ^ 2) P := by
    refine Integrable.of_bound (C := (Fintype.card (Fin k → Fin d) : ℝ) ^ 2)
      (hSm.pow_const _).aestronglyMeasurable ?_
    refine Filter.Eventually.of_forall (fun ω => ?_)
    rw [norm_pow, Real.norm_eq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) (hSb ω) _
  have hmark := mul_meas_ge_le_integral_of_nonneg (μ := P) (f := fun ω => S ω ^ 2)
    (Filter.Eventually.of_forall (fun ω => sq_nonneg _)) hSint (t ^ 2)
  have hE := l36_second_moment P hd hk X hXm hbdd hind hmom H hH
  have hsub : {ω | t ≤ |S ω|} ⊆ {ω | t ^ 2 ≤ S ω ^ 2} := by
    intro ω hω
    simp only [Set.mem_setOf_eq] at hω ⊢
    calc t ^ 2 ≤ |S ω| ^ 2 := pow_le_pow_left₀ ht0.le hω 2
      _ = S ω ^ 2 := sq_abs _
  have hreal : P.real {ω | t ≤ |S ω|} ≤ 1 / r ^ (2 * k) := by
    have h1 : P.real {ω | t ≤ |S ω|} ≤ P.real {ω | t ^ 2 ≤ S ω ^ 2} :=
      measureReal_mono hsub
    have hr2 : (0:ℝ) < r ^ (2 * k) := by positivity
    have h2 : t ^ 2 * P.real {ω | t ^ 2 ≤ S ω ^ 2} ≤ 2 * ((d : ℝ) * k / 2) ^ k :=
      hmark.trans hE
    obtain ⟨p, hp⟩ : ∃ p, p = P.real {ω | t ^ 2 ≤ S ω ^ 2} := ⟨_, rfl⟩
    rw [← hp] at h1 h2
    rw [ht2] at h2
    have h3 : p ≤ 1 / r ^ (2 * k) := by
      rw [le_div_iff₀ hr2]
      have hpos : 0 < 2 * ((d : ℝ) * k / 2) ^ k := by positivity
      have h4 : (2 * ((d : ℝ) * k / 2) ^ k) * (p * r ^ (2 * k)) ≤
          (2 * ((d : ℝ) * k / 2) ^ k) * 1 := by nlinarith [h2]
      exact le_of_mul_le_mul_left h4 hpos
    exact h1.trans h3
  calc P {ω | t ≤ |S ω|} = ENNReal.ofReal (P.real {ω | t ≤ |S ω|}) :=
        (ofReal_measureReal).symm
    _ ≤ ENNReal.ofReal (1 / r ^ (2 * k)) := ENNReal.ofReal_le_ofReal hreal
