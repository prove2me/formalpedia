-- Prove2me | solution 1 for RWPI.Classif.hinge_inner_sup
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-06T11:42:34.633879+00:00
-- url     : https://prove2.me/submissions/96a5203f-ee71-4f4f-8faf-935fa0f7ccc3

import Definitions.Def_RWPI_Classif_losses
import Mathlib

-- Complete local proof: Solutions.Classif_Holder
set_option autoImplicit false
namespace ClassifNorm
open scoped BigOperators

lemma holder_toReal (p q : ENNReal) (hpq : p.HolderConjugate q)
    (hp : p ≠ ⊤) (hq : q ≠ ⊤) : p.toReal.HolderConjugate q.toReal := by
  have : p.HolderConjugate q := hpq
  refine ⟨?_, ENNReal.toReal_pos (ENNReal.HolderConjugate.ne_zero p q) hp,
    ENNReal.toReal_pos (ENNReal.HolderConjugate.ne_zero q p) hq⟩
  have h := congrArg ENNReal.toReal (ENNReal.HolderConjugate.inv_add_inv_eq_one p q)
  simpa [ENNReal.toReal_add, ENNReal.inv_ne_top,
    ENNReal.HolderConjugate.ne_zero p q, ENNReal.HolderConjugate.ne_zero q p] using h

lemma dot_abs_le_finite {d : ℕ} (p q : ENNReal) (hpq : p.HolderConjugate q)
    (hp : p ≠ ⊤) (hq : q ≠ ⊤) (x y : Fin d → ℝ) :
    |∑ j, x j * y j| ≤ ‖WithLp.toLp p x‖ * ‖WithLp.toLp q y‖ := by
  have : p.HolderConjugate q := hpq
  have : Fact (1 ≤ p) := ⟨ENNReal.HolderConjugate.one_le p q⟩
  have : Fact (1 ≤ q) := ⟨ENNReal.HolderConjugate.one_le q p⟩
  rw [PiLp.norm_eq_sum (ENNReal.toReal_pos (ENNReal.HolderConjugate.ne_zero p q) hp),
    PiLp.norm_eq_sum (ENNReal.toReal_pos (ENNReal.HolderConjugate.ne_zero q p) hq)]
  calc
    |∑ j, x j * y j| ≤ ∑ j, |x j| * |y j| := by
      simpa only [abs_mul] using Finset.abs_sum_le_sum_abs (fun j => x j * y j) Finset.univ
    _ ≤ _ := by
      simpa using Real.inner_le_Lp_mul_Lq Finset.univ (fun j => |x j|)
        (fun j => |y j|) (holder_toReal p q hpq hp hq)

lemma dot_abs_le_one_top {d : ℕ} (x y : Fin d → ℝ) :
    |∑ j, x j * y j| ≤ ‖WithLp.toLp 1 x‖ * ‖WithLp.toLp ⊤ y‖ := by
  calc
    |∑ j, x j * y j| ≤ ∑ j, |x j| * |y j| := by
      simpa only [abs_mul] using Finset.abs_sum_le_sum_abs (fun j => x j * y j) Finset.univ
    _ ≤ ∑ j, |x j| * ‖WithLp.toLp ⊤ y‖ := by
      apply Finset.sum_le_sum
      intro j _
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
      simpa using PiLp.norm_apply_le (WithLp.toLp ⊤ y) j
    _ = _ := by
      rw [← Finset.sum_mul, PiLp.norm_eq_of_L1]
      simp

lemma dot_abs_le {d : ℕ} (p q : ENNReal) (hq : 1 < q)
    (hpq : p.HolderConjugate q) (x y : Fin d → ℝ) :
    |∑ j, x j * y j| ≤ ‖WithLp.toLp p x‖ * ‖WithLp.toLp q y‖ := by
  have : p.HolderConjugate q := hpq
  by_cases hqt : q = ⊤
  · subst q
    have hp : p = 1 := (ENNReal.HolderConjugate.eq_top_iff_eq_one ⊤ p).mp rfl
    subst p
    exact dot_abs_le_one_top x y
  · exact dot_abs_le_finite p q hpq
      ((ENNReal.HolderConjugate.ne_top_iff_ne_one p q).mpr hq.ne') hqt x y

#print axioms dot_abs_le_one_top
#print axioms dot_abs_le
#print axioms holder_toReal
#print axioms dot_abs_le_finite
end ClassifNorm

-- Complete local proof: Solutions.Classif_Norming
set_option autoImplicit false
namespace ClassifNorm
open scoped BigOperators NNReal

lemma norming_finite {d : ℕ} (p q : ENNReal) (hpq : p.HolderConjugate q)
    (hp : p ≠ ⊤) (hq : q ≠ ⊤) (x : Fin d → ℝ) :
    ∃ y : Fin d → ℝ, ‖WithLp.toLp q y‖ ≤ 1 ∧
      ∑ j, x j * y j = ‖WithLp.toLp p x‖ := by
  have : p.HolderConjugate q := hpq
  have : Fact (1 ≤ p) := ⟨ENNReal.HolderConjugate.one_le p q⟩
  have : Fact (1 ≤ q) := ⟨ENNReal.HolderConjugate.one_le q p⟩
  let f : Fin d → ℝ≥0 := fun j => ⟨|x j|, abs_nonneg _⟩
  have hc := holder_toReal p q hpq hp hq
  obtain ⟨g, hg, he⟩ := (NNReal.isGreatest_Lp Finset.univ f hc).1
  let y : Fin d → ℝ := fun j => if 0 ≤ x j then (g j : ℝ) else -(g j : ℝ)
  have hy (j : Fin d) : |y j| = (g j : ℝ) := by
    dsimp [y]
    split_ifs <;> simp
  have hxy (j : Fin d) : x j * y j = |x j| * (g j : ℝ) := by
    dsimp [y]
    split_ifs with h
    · rw [abs_of_nonneg h]
    · rw [abs_of_neg (lt_of_not_ge h)]
      ring
  refine ⟨y, ?_, ?_⟩
  · rw [PiLp.norm_eq_sum hc.symm.pos]
    simp only [Real.norm_eq_abs, hy]
    have hbound := NNReal.rpow_le_one hg (one_div_nonneg.mpr hc.symm.nonneg)
    exact_mod_cast hbound
  · rw [PiLp.norm_eq_sum hc.pos]
    simp only [Real.norm_eq_abs]
    simp_rw [hxy]
    have heR := congrArg (fun z : ℝ≥0 => (z : ℝ)) he
    have hf (j : Fin d) : (f j : ℝ) = |x j| := rfl
    simpa only [NNReal.coe_sum, NNReal.coe_mul, NNReal.coe_rpow, hf] using heR

lemma norming_one_top {d : ℕ} (x : Fin d → ℝ) :
    ∃ y : Fin d → ℝ, ‖WithLp.toLp ⊤ y‖ ≤ 1 ∧
      ∑ j, x j * y j = ‖WithLp.toLp 1 x‖ := by
  let y : Fin d → ℝ := fun j => if 0 ≤ x j then 1 else -1
  refine ⟨y, ?_, ?_⟩
  · rw [PiLp.norm_toLp]
    apply (pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 1)).mpr
    intro j
    dsimp [y]
    split_ifs <;> norm_num
  · rw [PiLp.norm_eq_of_L1]
    apply Finset.sum_congr rfl
    intro j _
    dsimp [y]
    split_ifs with h
    · simp [abs_of_nonneg h]
    · simp [abs_of_neg (lt_of_not_ge h)]

lemma norming {d : ℕ} (p q : ENNReal) (hq : 1 < q)
    (hpq : p.HolderConjugate q) (x : Fin d → ℝ) :
    ∃ y : Fin d → ℝ, ‖WithLp.toLp q y‖ ≤ 1 ∧
      ∑ j, x j * y j = ‖WithLp.toLp p x‖ := by
  have : p.HolderConjugate q := hpq
  by_cases hqt : q = ⊤
  · subst q
    have hp : p = 1 := (ENNReal.HolderConjugate.eq_top_iff_eq_one ⊤ p).mp rfl
    subst p
    exact norming_one_top x
  · exact norming_finite p q hpq
      ((ENNReal.HolderConjugate.ne_top_iff_ne_one p q).mpr hq.ne') hqt x

lemma norming_unit_of_positive {d : ℕ} (p q : ENNReal) (hq : 1 < q)
    (hpq : p.HolderConjugate q) (x : Fin d → ℝ) (hx : 0 < ‖WithLp.toLp p x‖) :
    ∃ y : Fin d → ℝ, ‖WithLp.toLp q y‖ = 1 ∧
      ∑ j, x j * y j = ‖WithLp.toLp p x‖ := by
  obtain ⟨y, hy, hxy⟩ := norming p q hq hpq x
  refine ⟨y, le_antisymm hy ?_, hxy⟩
  have hbound := dot_abs_le p q hq hpq x y
  rw [hxy, abs_of_pos hx] at hbound
  exact le_of_mul_le_mul_left (by simpa only [mul_one] using hbound) hx

#print axioms norming_one_top
#print axioms norming
#print axioms norming_unit_of_positive
#print axioms norming_finite
end ClassifNorm

-- Complete local proof: Solutions.Classif_NormEndpoints
set_option autoImplicit false
open scoped BigOperators
namespace ClassifNorm

lemma dot_abs_le_all {d : ℕ} (p q : ENNReal) (hpq : p.HolderConjugate q)
    (x y : Fin d → ℝ) : |∑ j, x j * y j| ≤ ‖WithLp.toLp p x‖ * ‖WithLp.toLp q y‖ := by
  have : p.HolderConjugate q := hpq
  by_cases hq1 : q = 1
  · subst q
    have hp : p = ⊤ := (ENNReal.HolderConjugate.eq_top_iff_eq_one p 1).mpr rfl
    subst p
    have h := dot_abs_le_one_top y x
    simpa [mul_comm] using h
  · exact dot_abs_le p q (lt_of_le_of_ne (ENNReal.HolderConjugate.one_le q p) (Ne.symm hq1)) hpq x y

lemma norming_top_one {d : ℕ} (x : Fin d → ℝ) :
    ∃ y : Fin d → ℝ, ‖WithLp.toLp 1 y‖ ≤ 1 ∧
      ∑ j, x j * y j = ‖WithLp.toLp ⊤ x‖ := by
  classical
  cases isEmpty_or_nonempty (Fin d) with
  | inl hi =>
    have := hi
    have hx : x = 0 := by ext j; exact isEmptyElim j
    subst x
    refine ⟨0, ?_, ?_⟩ <;> simp
  | inr hi =>
    have := hi
    obtain ⟨j, hj⟩ := (IsGreatest.pi_norm x).1
    let y : Fin d → ℝ := fun i => if i = j then (if 0 ≤ x j then 1 else -1) else 0
    refine ⟨y, ?_, ?_⟩
    · rw [PiLp.norm_eq_of_L1]
      rw [Finset.sum_eq_single j]
      · by_cases hs : 0 ≤ x j <;> simp [y, hs]
      · intro i hi hij
        simp [y, hij]
      · simp
    · rw [PiLp.norm_toLp]
      have hj' : |x j| = ‖x‖ := by simpa [Real.norm_eq_abs] using hj
      by_cases hs : 0 ≤ x j
      · simpa [y, hs, abs_of_nonneg hs] using hj'
      · simpa [y, hs, abs_of_neg (lt_of_not_ge hs)] using hj'

lemma norming_all {d : ℕ} (p q : ENNReal) (hpq : p.HolderConjugate q) (x : Fin d → ℝ) :
    ∃ y : Fin d → ℝ, ‖WithLp.toLp q y‖ ≤ 1 ∧
      ∑ j, x j * y j = ‖WithLp.toLp p x‖ := by
  have : p.HolderConjugate q := hpq
  by_cases hq1 : q = 1
  · subst q
    have hp : p = ⊤ := (ENNReal.HolderConjugate.eq_top_iff_eq_one p 1).mpr rfl
    subst p
    exact norming_top_one x
  · exact norming p q (lt_of_le_of_ne (ENNReal.HolderConjugate.one_le q p) (Ne.symm hq1)) hpq x

lemma norming_unit_all_of_positive {d : ℕ} (p q : ENNReal) (hpq : p.HolderConjugate q)
    (x : Fin d → ℝ) (hx : 0 < ‖WithLp.toLp p x‖) :
    ∃ y : Fin d → ℝ, ‖WithLp.toLp q y‖ = 1 ∧
      ∑ j, x j * y j = ‖WithLp.toLp p x‖ := by
  obtain ⟨y, hy, hxy⟩ := norming_all p q hpq x
  refine ⟨y, le_antisymm hy ?_, hxy⟩
  have hbound := dot_abs_le_all p q hpq x y
  rw [hxy, abs_of_pos hx] at hbound
  exact le_of_mul_le_mul_left (by simpa only [mul_one] using hbound) hx

#print axioms dot_abs_le_all
#print axioms norming_top_one
#print axioms norming_all
#print axioms norming_unit_all_of_positive
end ClassifNorm

-- Complete local proof: Solutions.Classif_Softplus
set_option autoImplicit false
namespace ClassifCodex

noncomputable def softplus (u : ℝ) : ℝ := Real.log (1 + Real.exp u)

lemma softplus_nonnegative (u : ℝ) : 0 ≤ softplus u := by
  exact Real.log_nonneg (by linarith [Real.exp_pos u])

lemma le_softplus (u : ℝ) : u ≤ softplus u := by
  calc
    u = Real.log (Real.exp u) := (Real.log_exp u).symm
    _ ≤ Real.log (1 + Real.exp u) := Real.log_le_log (Real.exp_pos u) (by linarith)

lemma softplus_hasDerivAt (u : ℝ) :
    HasDerivAt softplus (Real.exp u / (1 + Real.exp u)) u := by
  change HasDerivAt (fun x : ℝ => Real.log (1 + Real.exp x))
    (Real.exp u / (1 + Real.exp u)) u
  exact ((Real.hasDerivAt_exp u).const_add 1).log (by positivity)

lemma softplus_lipschitz : LipschitzWith 1 softplus := by
  apply lipschitzWith_of_nnnorm_deriv_le (𝕜 := ℝ)
    (fun u => (softplus_hasDerivAt u).differentiableAt)
  intro u
  rw [(softplus_hasDerivAt u).deriv]
  have hpos : 0 ≤ Real.exp u / (1 + Real.exp u) := by positivity
  have hle : Real.exp u / (1 + Real.exp u) ≤ 1 :=
    (div_le_one (by positivity)).mpr (by linarith)
  have hn : ‖Real.exp u / (1 + Real.exp u)‖ ≤ 1 := by
    rwa [Real.norm_eq_abs, abs_of_nonneg hpos]
  exact_mod_cast hn

#print axioms softplus_nonnegative
#print axioms le_softplus
#print axioms softplus_hasDerivAt
#print axioms softplus_lipschitz
end ClassifCodex

-- Complete local proof: Solutions.Classif_LossBounds
set_option autoImplicit false
open scoped BigOperators
namespace ClassifCodex

noncomputable def margin {d : ℕ} (β : Fin d → ℝ) (y : ℝ) (x : Fin d → ℝ) : ℝ :=
  -(y * (β ⬝ᵥ x))

lemma binary_abs (y : ℝ) (hy : y = 1 ∨ y = -1) : |y| = 1 := by
  rcases hy with rfl | rfl <;> norm_num

lemma margin_sub {d : ℕ} (β x x₀ : Fin d → ℝ) (y : ℝ) :
    margin β y x - margin β y x₀ = -y * (β ⬝ᵥ (x - x₀)) := by
  unfold margin
  rw [dotProduct_sub]
  ring

lemma margin_abs_sub_le {d : ℕ} (p q : ENNReal) (hpq : p.HolderConjugate q)
    (β x x₀ : Fin d → ℝ) (y : ℝ) (hy : y = 1 ∨ y = -1) :
    |margin β y x - margin β y x₀| ≤ ‖WithLp.toLp p β‖ * ‖WithLp.toLp q (x - x₀)‖ := by
  rw [margin_sub, abs_mul, abs_neg, binary_abs y hy, one_mul]
  exact ClassifNorm.dot_abs_le_all p q hpq β (x - x₀)

lemma hinge_scalar_lipschitz : LipschitzWith 1 (fun u : ℝ => max 0 (1 + u)) := by
  have ha : LipschitzWith 1 (fun u : ℝ => 1 + u) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simp [Real.dist_eq]
  simpa using (LipschitzWith.const (α := ℝ) (0 : ℝ)).max ha

lemma logLoss_nonnegative {d : ℕ} (β : Fin d → ℝ) (z : (Fin d → ℝ) × ℝ) :
    0 ≤ RWPI.Classif.logLoss β z := softplus_nonnegative _

lemma hingeLoss_nonnegative {d : ℕ} (β : Fin d → ℝ) (z : (Fin d → ℝ) × ℝ) :
    0 ≤ RWPI.Classif.hingeLoss β z := le_max_left _ _

lemma margin_le_logLoss {d : ℕ} (β x : Fin d → ℝ) (y : ℝ) :
    margin β y x ≤ RWPI.Classif.logLoss β (x, y) := le_softplus _

lemma margin_le_hingeLoss {d : ℕ} (β x : Fin d → ℝ) (y : ℝ) :
    margin β y x ≤ RWPI.Classif.hingeLoss β (x, y) := by
  have h := le_max_right (0 : ℝ) (1 + margin β y x)
  change margin β y x ≤ max 0 (1 + margin β y x)
  linarith

lemma logLoss_abs_sub_le {d : ℕ} (p q : ENNReal) (hpq : p.HolderConjugate q)
    (β x x₀ : Fin d → ℝ) (y : ℝ) (hy : y = 1 ∨ y = -1) :
    |RWPI.Classif.logLoss β (x, y) - RWPI.Classif.logLoss β (x₀, y)| ≤
      ‖WithLp.toLp p β‖ * ‖WithLp.toLp q (x - x₀)‖ := by
  have h := softplus_lipschitz.dist_le_mul (margin β y x) (margin β y x₀)
  have h' : |RWPI.Classif.logLoss β (x, y) - RWPI.Classif.logLoss β (x₀, y)| ≤
      |margin β y x - margin β y x₀| := by
    simp only [Real.dist_eq, NNReal.coe_one, one_mul] at h
    change |RWPI.Classif.logLoss β (x, y) - RWPI.Classif.logLoss β (x₀, y)| ≤
      |margin β y x - margin β y x₀| at h
    exact h
  exact h'.trans (margin_abs_sub_le p q hpq β x x₀ y hy)

lemma hingeLoss_abs_sub_le {d : ℕ} (p q : ENNReal) (hpq : p.HolderConjugate q)
    (β x x₀ : Fin d → ℝ) (y : ℝ) (hy : y = 1 ∨ y = -1) :
    |RWPI.Classif.hingeLoss β (x, y) - RWPI.Classif.hingeLoss β (x₀, y)| ≤
      ‖WithLp.toLp p β‖ * ‖WithLp.toLp q (x - x₀)‖ := by
  have h := hinge_scalar_lipschitz.dist_le_mul (margin β y x) (margin β y x₀)
  have h' : |RWPI.Classif.hingeLoss β (x, y) - RWPI.Classif.hingeLoss β (x₀, y)| ≤
      |margin β y x - margin β y x₀| := by
    simp only [Real.dist_eq, NNReal.coe_one, one_mul] at h
    change |RWPI.Classif.hingeLoss β (x, y) - RWPI.Classif.hingeLoss β (x₀, y)| ≤
      |margin β y x - margin β y x₀| at h
    exact h
  exact h'.trans (margin_abs_sub_le p q hpq β x x₀ y hy)

#print axioms binary_abs
#print axioms margin_sub
#print axioms margin_abs_sub_le
#print axioms hinge_scalar_lipschitz
#print axioms logLoss_nonnegative
#print axioms hingeLoss_nonnegative
#print axioms margin_le_logLoss
#print axioms margin_le_hingeLoss
#print axioms logLoss_abs_sub_le
#print axioms hingeLoss_abs_sub_le
end ClassifCodex

-- Complete local proof: Solutions.Classif_NormingRay
set_option autoImplicit false
namespace ClassifCodex

lemma margin_ray {d : ℕ} (β x₀ v : Fin d → ℝ) (y t B : ℝ)
    (hy : y = 1 ∨ y = -1) (hdot : β ⬝ᵥ v = B) :
    margin β y (x₀ - (t * y) • v) = margin β y x₀ + t * B := by
  unfold margin
  rw [dotProduct_sub, dotProduct_smul, smul_eq_mul, hdot]
  rcases hy with rfl | rfl <;> ring

lemma norming_ray_distance {d : ℕ} (q : ENNReal) (hq : 1 ≤ q)
    (x₀ v : Fin d → ℝ) (y t : ℝ) (hy : y = 1 ∨ y = -1) (ht : 0 ≤ t)
    (hv : ‖WithLp.toLp q v‖ = 1) :
    ‖WithLp.toLp q ((x₀ - (t * y) • v) - x₀)‖ = t := by
  have : Fact (1 ≤ q) := ⟨hq⟩
  have he : (x₀ - (t * y) • v) - x₀ = (-(t * y)) • v := by module
  rw [he]
  change ‖(-(t * y)) • WithLp.toLp q v‖ = t
  rw [norm_smul, hv, mul_one, Real.norm_eq_abs, abs_neg, abs_mul, binary_abs y hy,
    abs_of_nonneg ht, mul_one]

#print axioms margin_ray
#print axioms norming_ray_distance
end ClassifCodex

-- Complete local proof: Solutions.Classif_InnerEnvelope
set_option autoImplicit false
namespace ClassifCodex

lemma inner_envelope_eq_if {d : ℕ} (p q : ENNReal) (hpq : p.HolderConjugate q)
    (β x₀ : Fin d → ℝ) (y : ℝ) (hy : y = 1 ∨ y = -1)
    (l : (Fin d → ℝ) → ℝ)
    (hlip : ∀ x, |l x - l x₀| ≤ ‖WithLp.toLp p β‖ * ‖WithLp.toLp q (x - x₀)‖)
    (hlower : ∀ x, margin β y x ≤ l x) (lam : ℝ) (hlam : 0 ≤ lam) :
    (⨆ x : Fin d → ℝ, ENNReal.ofReal (l x) -
      ENNReal.ofReal lam * ENNReal.ofReal ‖WithLp.toLp q (x - x₀)‖) =
      if ‖WithLp.toLp p β‖ ≤ lam then ENNReal.ofReal (l x₀) else ⊤ := by
  have : p.HolderConjugate q := hpq
  have : Fact (1 ≤ q) := ⟨ENNReal.HolderConjugate.one_le q p⟩
  have he (x : Fin d → ℝ) :
      ENNReal.ofReal (l x) - ENNReal.ofReal lam * ENNReal.ofReal ‖WithLp.toLp q (x - x₀)‖ =
        ENNReal.ofReal (l x - lam * ‖WithLp.toLp q (x - x₀)‖) := by
    rw [ENNReal.ofReal_sub _ (mul_nonneg hlam (norm_nonneg _)), ENNReal.ofReal_mul hlam]
  simp_rw [he]
  by_cases hB : ‖WithLp.toLp p β‖ ≤ lam
  · rw [if_pos hB]
    apply le_antisymm
    · apply iSup_le
      intro x
      apply ENNReal.ofReal_le_ofReal
      have h := (le_abs_self (l x - l x₀)).trans (hlip x)
      have hn := norm_nonneg (WithLp.toLp q (x - x₀))
      nlinarith
    · apply le_iSup_of_le x₀
      simp
  · rw [if_neg hB]
    have hgap : 0 < ‖WithLp.toLp p β‖ - lam := sub_pos.mpr (lt_of_not_ge hB)
    have hβ : 0 < ‖WithLp.toLp p β‖ := by linarith
    obtain ⟨v, hv, hdot⟩ := ClassifNorm.norming_unit_all_of_positive p q hpq β hβ
    apply iSup_eq_top.mpr
    intro r hr
    let a := margin β y x₀
    let t := max 0 ((r.toReal - a + 1) / (‖WithLp.toLp p β‖ - lam))
    have ht : 0 ≤ t := le_max_left _ _
    have htbound : (r.toReal - a + 1) / (‖WithLp.toLp p β‖ - lam) ≤ t := le_max_right _ _
    have hprod : r.toReal - a + 1 ≤ t * (‖WithLp.toLp p β‖ - lam) :=
      (div_le_iff₀ hgap).mp htbound
    let x := x₀ - (t * y) • v
    refine ⟨x, ?_⟩
    apply (ENNReal.lt_ofReal_iff_toReal_lt (ne_of_lt hr)).mpr
    have hnorm := norming_ray_distance q (ENNReal.HolderConjugate.one_le q p) x₀ v y t hy ht hv
    have hmargin := margin_ray β x₀ v y t ‖WithLp.toLp p β‖ hy hdot
    have hl := hlower x
    dsimp [x] at *
    rw [hnorm]
    dsimp [a] at hprod
    nlinarith

#print axioms inner_envelope_eq_if
end ClassifCodex

-- Complete local proof: Solutions.Classif_InnerFormulas
set_option autoImplicit false
namespace ClassifCodex

lemma logistic_inner_formula {d : ℕ} (p q : ENNReal) (hpq : p.HolderConjugate q)
    (β x₀ : Fin d → ℝ) (y₀ : ℝ) (hy₀ : y₀ = 1 ∨ y₀ = -1) (lam : ℝ) (hlam : 0 ≤ lam) :
    (⨆ x : Fin d → ℝ, ENNReal.ofReal (RWPI.Classif.logLoss β (x, y₀)) -
      ENNReal.ofReal lam * ENNReal.ofReal ‖WithLp.toLp q (x - x₀)‖) =
      if ‖WithLp.toLp p β‖ ≤ lam then ENNReal.ofReal (RWPI.Classif.logLoss β (x₀, y₀)) else ⊤ :=
  inner_envelope_eq_if p q hpq β x₀ y₀ hy₀ (fun x => RWPI.Classif.logLoss β (x, y₀))
    (fun x => logLoss_abs_sub_le p q hpq β x x₀ y₀ hy₀)
    (fun x => margin_le_logLoss β x y₀) lam hlam

lemma hinge_inner_formula {d : ℕ} (p q : ENNReal) (hpq : p.HolderConjugate q)
    (β x₀ : Fin d → ℝ) (y₀ : ℝ) (hy₀ : y₀ = 1 ∨ y₀ = -1) (lam : ℝ) (hlam : 0 ≤ lam) :
    (⨆ Δ : Fin d → ℝ, ENNReal.ofReal (RWPI.Classif.hingeLoss β (x₀ + Δ, y₀)) -
      ENNReal.ofReal lam * ENNReal.ofReal ‖WithLp.toLp q Δ‖) =
      if ‖WithLp.toLp p β‖ ≤ lam then ENNReal.ofReal (RWPI.Classif.hingeLoss β (x₀, y₀)) else ⊤ := by
  have he :
      (⨆ Δ : Fin d → ℝ, ENNReal.ofReal (RWPI.Classif.hingeLoss β (x₀ + Δ, y₀)) -
        ENNReal.ofReal lam * ENNReal.ofReal ‖WithLp.toLp q Δ‖) =
      ⨆ x : Fin d → ℝ, ENNReal.ofReal (RWPI.Classif.hingeLoss β (x, y₀)) -
        ENNReal.ofReal lam * ENNReal.ofReal ‖WithLp.toLp q (x - x₀)‖ := by
    apply le_antisymm
    · apply iSup_le
      intro Δ
      apply le_iSup_of_le (x₀ + Δ)
      rw [show x₀ + Δ - x₀ = Δ by abel]
    · apply iSup_le
      intro x
      apply le_iSup_of_le (x - x₀)
      rw [show x₀ + (x - x₀) = x by abel]
  rw [he]
  exact inner_envelope_eq_if p q hpq β x₀ y₀ hy₀ (fun x => RWPI.Classif.hingeLoss β (x, y₀))
    (fun x => hingeLoss_abs_sub_le p q hpq β x x₀ y₀ hy₀)
    (fun x => margin_le_hingeLoss β x y₀) lam hlam

#print axioms logistic_inner_formula
#print axioms hinge_inner_formula
end ClassifCodex

-- Complete local proof: Solutions.Sol_RWPI_Classif_hinge_inner_sup
set_option autoImplicit false
open scoped ENNReal
open RWPI.Classif
theorem solution {d : ℕ} (p q : ℝ≥0∞) (hpq : p.HolderConjugate q)
    (β x₀ : Fin d → ℝ) (y₀ : ℝ) (hy₀ : y₀ = 1 ∨ y₀ = -1) (lam : ℝ) (hlam : 0 ≤ lam) :
    (⨆ Δ : Fin d → ℝ, (ENNReal.ofReal (hingeLoss β (x₀ + Δ, y₀)) -
        ENNReal.ofReal lam * ENNReal.ofReal ‖WithLp.toLp q Δ‖)) =
      if ‖WithLp.toLp p β‖ ≤ lam then ENNReal.ofReal (hingeLoss β (x₀, y₀)) else ⊤ := by
  exact ClassifCodex.hinge_inner_formula p q hpq β x₀ y₀ hy₀ lam hlam

#print axioms solution
