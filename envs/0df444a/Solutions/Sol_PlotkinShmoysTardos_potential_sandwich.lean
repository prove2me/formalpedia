-- Prove2me | solution 1 for PlotkinShmoysTardos.potential_sandwich
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-08T23:33:35.406878+00:00
-- url     : https://prove2.me/submissions/f9981dfa-fc8b-434b-8d46-8f0f766daf70

import Mathlib
import Definitions.Def_PlotkinShmoysTardos_General
import Definitions.Def_PlotkinShmoysTardos_relaxedOptimality
import Definitions.Def_PlotkinShmoysTardos_improveGeneral

set_option linter.unusedVariables false

namespace PlotkinShmoysTardos

private lemma exp_cubic_upper {t : ℝ} (ht : |t| ≤ 1 / 12) :
    Real.exp t ≤ 1 + t + (14 / 27 : ℝ) * t ^ 2 := by
  have ht1 : |t| ≤ 1 := by linarith
  have hb := Real.exp_bound ht1 (n := 3) (by decide)
  have hsum : (∑ m ∈ Finset.range 3, t ^ m / (m.factorial : ℝ)) = 1 + t + t ^ 2 / 2 := by
    simp [Finset.sum_range_succ, Nat.factorial]
  rw [hsum] at hb
  have hle : Real.exp t - (1 + t + t ^ 2 / 2) ≤
      |t| ^ 3 * (((3 : ℕ).succ : ℝ) / ((3 : ℕ).factorial * (3 : ℕ))) :=
    (le_abs_self _).trans hb
  have hfac : (((3 : ℕ).succ : ℝ) / ((3 : ℕ).factorial * (3 : ℕ))) = 2 / 9 := by
    norm_num [Nat.factorial]
  rw [hfac] at hle
  have hpow : |t| ^ 3 ≤ (1 / 12 : ℝ) * t ^ 2 := by
    have hsq : |t| ^ 2 = t ^ 2 := sq_abs t
    have h0 : 0 ≤ t ^ 2 := sq_nonneg t
    calc
      |t| ^ 3 = |t| * |t| ^ 2 := by ring
      _ = |t| * t ^ 2 := by rw [hsq]
      _ ≤ (1 / 12 : ℝ) * t ^ 2 := mul_le_mul_of_nonneg_right ht h0
  linarith

private lemma potential_eq_sum {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b d : Fin m → ℝ)
    (hd : ∀ i, 0 < d i) (α : ℝ) (x : Fin n → ℝ) :
    potential A b d α x = ∑ i : Fin m, Real.exp (α * (A.mulVec x i - b i) / d i) := by
  unfold potential dual dotProduct
  refine Finset.sum_congr rfl fun i _ => ?_
  have hdi : d i ≠ 0 := ne_of_gt (hd i)
  field_simp [hdi]

private lemma potential_pos {m n : ℕ} [NeZero m] (A : Matrix (Fin m) (Fin n) ℝ) (b d : Fin m → ℝ)
    (hd : ∀ i, 0 < d i) (α : ℝ) (x : Fin n → ℝ) :
    0 < potential A b d α x := by
  rw [potential_eq_sum A b d hd]
  exact Finset.sum_pos (fun i _ => Real.exp_pos _) Finset.univ_nonempty

private lemma dual_nonneg {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b d : Fin m → ℝ)
    (hd : ∀ i, 0 < d i) (α : ℝ) (x : Fin n → ℝ) :
    0 ≤ dual A b d α x := by
  intro i
  unfold dual
  exact mul_nonneg (one_div_nonneg.mpr (le_of_lt (hd i))) (le_of_lt (Real.exp_pos _))

private lemma lam_le_rho {m n : ℕ} [NeZero m] (A : Matrix (Fin m) (Fin n) ℝ) (b d : Fin m → ℝ)
    (P : Set (Fin n → ℝ)) (hd : ∀ i, 0 < d i) (ρ : ℝ) (hρ : IsWidthBound A b d P ρ)
    {z : Fin n → ℝ} (hz : z ∈ P) :
    lam A b d z ≤ ρ := by
  unfold lam
  refine Finset.sup'_le Finset.univ_nonempty _ fun i _ => ?_
  rw [div_le_iff₀ (hd i)]
  exact (le_abs_self _).trans (hρ i z hz)

private lemma log_six_m_rho_ge_one {m : ℕ} [NeZero m] {ρ lam0 : ℝ}
    (hl0 : 0 < lam0) (hlam_le : lam0 ≤ ρ) :
    1 ≤ Real.log (6 * (m : ℝ) * ρ / lam0) := by
  have hm1 : (1 : ℝ) ≤ (m : ℝ) := by
    exact_mod_cast Nat.succ_le_of_lt ( Nat.pos_of_ne_zero (NeZero.ne m) )
  have h6 : (6 : ℝ) ≤ 6 * (m : ℝ) * ρ / lam0 := by
    rw [le_div_iff₀ hl0]
    nlinarith
  have hexp1 : Real.exp 1 ≤ 6 * (m : ℝ) * ρ / lam0 := by
    have he : Real.exp 1 < 3 := Real.exp_one_lt_d9.trans (by norm_num)
    linarith
  have hpos : 0 < 6 * (m : ℝ) * ρ / lam0 := by linarith
  exact (Real.le_log_iff_exp_le hpos).mpr hexp1

private lemma alphaOf_pos_and_mul_ge_four {m : ℕ} [NeZero m] {ρ lam0 : ℝ}
    (hl0 : 0 < lam0) (hlam_le : lam0 ≤ ρ) :
    0 < alphaOf m ρ lam0 ∧ 4 ≤ alphaOf m ρ lam0 * lam0 := by
  have hlog : 1 ≤ Real.log (6 * (m : ℝ) * ρ / lam0) := log_six_m_rho_ge_one hl0 hlam_le
  unfold alphaOf
  constructor
  · have h1 : 0 < 4 / lam0 := div_pos (by norm_num) hl0
    have h2 : 0 < Real.log (6 * (m : ℝ) * ρ / lam0) := by linarith
    exact mul_pos h1 h2
  · have hne : lam0 ≠ 0 := ne_of_gt hl0
    have heq : 4 / lam0 * Real.log (6 * (m : ℝ) * ρ / lam0) * lam0 =
        4 * Real.log (6 * (m : ℝ) * ρ / lam0) := by
      field_simp [hne]
    rw [heq]
    linarith

private lemma sigmaOf_bounds {m : ℕ} [NeZero m] {ρ lam0 : ℝ}
    (hl0 : 0 < lam0) (hlam_le : lam0 ≤ ρ) :
    0 < sigmaOf m ρ lam0 ∧ sigmaOf m ρ lam0 ≤ 1 := by
  obtain ⟨hα, hαl⟩ := alphaOf_pos_and_mul_ge_four (m := m) hl0 hlam_le
  have hρ0 : 0 < ρ := lt_of_lt_of_le hl0 hlam_le
  unfold sigmaOf
  have hden : 0 < 24 * alphaOf m ρ lam0 * ρ ^ 2 := by positivity
  constructor
  · exact div_pos hl0 hden
  · rw [div_le_one hden]
    have hsq : lam0 ^ 2 ≤ ρ ^ 2 := by nlinarith
    have h1 : 24 * alphaOf m ρ lam0 * lam0 ^ 2 ≤ 24 * alphaOf m ρ lam0 * ρ ^ 2 := by
      nlinarith
    have h2 : 96 * lam0 ≤ 24 * alphaOf m ρ lam0 * lam0 ^ 2 := by
      calc
        96 * lam0 = 24 * 4 * lam0 := by ring
        _ ≤ 24 * (alphaOf m ρ lam0 * lam0) * lam0 := by nlinarith
        _ = 24 * alphaOf m ρ lam0 * lam0 ^ 2 := by ring
    linarith

private lemma dot_sub_cancel {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b y : Fin m → ℝ)
    (z w : Fin n → ℝ) :
    y ⬝ᵥ (A.mulVec z - b) - y ⬝ᵥ (A.mulVec w - b) =
      ∑ i : Fin m, y i * (A.mulVec z i - A.mulVec w i) := by
  unfold dotProduct
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Pi.sub_apply]
  ring

private lemma mulVec_combo {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (σ : ℝ)
    (z w : Fin n → ℝ) (i : Fin m) :
    A.mulVec ((1 - σ) • z + σ • w) i = (1 - σ) * A.mulVec z i + σ * A.mulVec w i := by
  rw [Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul, Pi.add_apply,
    Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul]

private lemma one_step_potential_decrease {m n : ℕ} [NeZero m]
    (A : Matrix (Fin m) (Fin n) ℝ) (b d : Fin m → ℝ) (P : Set (Fin n → ℝ))
    (hd : ∀ i, 0 < d i) (ρ : ℝ) (hρ : IsWidthBound A b d P ρ)
    (lam0 : ℝ) (hl0 : 0 < lam0) (hlam_le : lam0 ≤ ρ)
    (z xt : Fin n → ℝ) (hz : z ∈ P) (hxt : xt ∈ P)
    (hlz : ¬ lam A b d z < lam0 / 2)
    (hnG2 : ¬ (dual A b d (alphaOf m ρ lam0) z ⬝ᵥ (A.mulVec z - b) -
        dual A b d (alphaOf m ρ lam0) z ⬝ᵥ (A.mulVec xt - b) ≤
        lam A b d z / 5 * (dual A b d (alphaOf m ρ lam0) z ⬝ᵥ d))) :
    potential A b d (alphaOf m ρ lam0)
        ((1 - sigmaOf m ρ lam0) • z + sigmaOf m ρ lam0 • xt) ≤
      (1 - (11 / 810 : ℝ) * (alphaOf m ρ lam0 * sigmaOf m ρ lam0 * lam0)) *
        potential A b d (alphaOf m ρ lam0) z := by
  set α := alphaOf m ρ lam0
  set σ := sigmaOf m ρ lam0
  set y := dual A b d α z
  obtain ⟨hα, _⟩ := alphaOf_pos_and_mul_ge_four (m := m) hl0 hlam_le
  obtain ⟨hσ, _⟩ := sigmaOf_bounds (m := m) hl0 hlam_le
  have hρ0 : 0 < ρ := lt_of_lt_of_le hl0 hlam_le
  have hα_ne : α ≠ 0 := ne_of_gt hα
  have hρ_ne : ρ ≠ 0 := ne_of_gt hρ0
  have h2ασρ : 2 * α * σ * ρ = lam0 / (12 * ρ) := by
    dsimp [σ, sigmaOf]
    field_simp [hα_ne, hρ_ne]
    ring
  have h2ασρ_le : 2 * α * σ * ρ ≤ 1 / 12 := by
    rw [h2ασρ, div_le_iff₀ (by positivity)]
    linarith
  have hsq_bound : 4 * α ^ 2 * σ ^ 2 * ρ ^ 2 = (1 / 6 : ℝ) * (α * σ * lam0) := by
    have hσ_def : σ * (24 * α * ρ ^ 2) = lam0 := by
      dsimp [σ, sigmaOf]
      exact div_mul_cancel₀ lam0 (by positivity)
    calc
      4 * α ^ 2 * σ ^ 2 * ρ ^ 2 = (1 / 6 : ℝ) * (α * σ * (σ * (24 * α * ρ ^ 2))) := by ring
      _ = (1 / 6 : ℝ) * (α * σ * lam0) := by rw [hσ_def]
  let t : Fin m → ℝ := fun i => α * σ * (A.mulVec xt i - A.mulVec z i) / d i
  have ht_abs : ∀ i, |t i| ≤ 2 * α * σ * ρ := by
    intro i
    have hdi : 0 < d i := hd i
    have h1 : |A.mulVec xt i - b i| ≤ ρ * d i := hρ i xt hxt
    have h2 : |A.mulVec z i - b i| ≤ ρ * d i := hρ i z hz
    have hdiff : |A.mulVec xt i - A.mulVec z i| ≤ 2 * ρ * d i := by
      have heq : A.mulVec xt i - A.mulVec z i =
          (A.mulVec xt i - b i) - (A.mulVec z i - b i) := by ring
      rw [heq]
      exact (abs_sub _ _).trans (by linarith)
    dsimp [t]
    rw [abs_div, abs_mul, abs_of_pos (mul_pos hα hσ), abs_of_pos hdi, div_le_iff₀ hdi]
    calc
      α * σ * |A.mulVec xt i - A.mulVec z i| ≤ α * σ * (2 * ρ * d i) :=
        mul_le_mul_of_nonneg_left hdiff (le_of_lt (mul_pos hα hσ))
      _ = 2 * α * σ * ρ * d i := by ring
  have hterm : ∀ i : Fin m,
      Real.exp (α * (A.mulVec ((1 - σ) • z + σ • xt) i - b i) / d i) ≤
        Real.exp (α * (A.mulVec z i - b i) / d i) *
          (1 + t i + (7 / 81 : ℝ) * (α * σ * lam0)) := by
    intro i
    have hdi_ne : d i ≠ 0 := ne_of_gt (hd i)
    have hexp_split :
        α * (A.mulVec ((1 - σ) • z + σ • xt) i - b i) / d i =
          α * (A.mulVec z i - b i) / d i + t i := by
      rw [mulVec_combo]
      dsimp [t]
      ring
    rw [hexp_split, Real.exp_add]
    refine mul_le_mul_of_nonneg_left ?_ (le_of_lt (Real.exp_pos _))
    have hti12 : |t i| ≤ 1 / 12 := (ht_abs i).trans h2ασρ_le
    have hcub := exp_cubic_upper hti12
    have htsq : t i ^ 2 ≤ (1 / 6 : ℝ) * (α * σ * lam0) := by
      have h0 : 0 ≤ |t i| := abs_nonneg _
      have hle_sq : |t i| ^ 2 ≤ (2 * α * σ * ρ) ^ 2 :=
         pow_le_pow_left₀ h0 (ht_abs i) 2
      rw [sq_abs] at hle_sq
      calc
        t i ^ 2 ≤ (2 * α * σ * ρ) ^ 2 := hle_sq
        _ = 4 * α ^ 2 * σ ^ 2 * ρ ^ 2 := by ring
        _ = (1 / 6 : ℝ) * (α * σ * lam0) := hsq_bound
    linarith
  rw [potential_eq_sum A b d hd]
  have hsum_le :
      (∑ i : Fin m, Real.exp (α * (A.mulVec ((1 - σ) • z + σ • xt) i - b i) / d i)) ≤
        ∑ i : Fin m, Real.exp (α * (A.mulVec z i - b i) / d i) *
          (1 + t i + (7 / 81 : ℝ) * (α * σ * lam0)) :=
    Finset.sum_le_sum fun i _ => hterm i
  have hsum_split :
      (∑ i : Fin m, Real.exp (α * (A.mulVec z i - b i) / d i) *
          (1 + t i + (7 / 81 : ℝ) * (α * σ * lam0))) =
        potential A b d α z +
          α * σ * (∑ i : Fin m, y i * (A.mulVec xt i - A.mulVec z i)) +
          (7 / 81 : ℝ) * (α * σ * lam0) * potential A b d α z := by
    rw [potential_eq_sum A b d hd, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hdi_ne : d i ≠ 0 := ne_of_gt (hd i)
    dsimp [y, dual, t]
    field_simp [hdi_ne]
  have hlin :
      ∑ i : Fin m, y i * (A.mulVec xt i - A.mulVec z i) ≤
        -(lam0 / 10) * potential A b d α z := by
    have hnot : lam A b d z / 5 * potential A b d α z <
        y ⬝ᵥ (A.mulVec z - b) - y ⬝ᵥ (A.mulVec xt - b) :=
      lt_of_not_ge hnG2
    rw [dot_sub_cancel] at hnot
    have hneg :
        (∑ i : Fin m, y i * (A.mulVec xt i - A.mulVec z i)) =
          -(∑ i : Fin m, y i * (A.mulVec z i - A.mulVec xt i)) := by
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun i _ => by ring
    have hlz' : lam0 / 2 ≤ lam A b d z := not_lt.mp hlz
    have hΦ_pos : 0 < potential A b d α z := potential_pos A b d hd α z
    have hlam_phi : lam0 / 10 * potential A b d α z ≤ lam A b d z / 5 * potential A b d α z := by
      nlinarith
    linarith
  have hlin_mul :
      α * σ * (∑ i : Fin m, y i * (A.mulVec xt i - A.mulVec z i)) ≤
        -(1 / 10 : ℝ) * (α * σ * lam0) * potential A b d α z := by
    have hαs : 0 < α * σ := mul_pos hα hσ
    nlinarith
  linarith

private lemma callRun_mem_and_upper {m n : ℕ} [NeZero m]
    (A : Matrix (Fin m) (Fin n) ℝ) (b d : Fin m → ℝ) (P : Set (Fin n → ℝ))
    (hd : ∀ i, 0 < d i) (hP : Convex ℝ P) (ρ : ℝ) (hρ : IsWidthBound A b d P ρ)
    (O : (Fin m → ℝ) → (Fin n → ℝ)) (hO : IsMinOracle A P O)
    (x : Fin n → ℝ) (hx : x ∈ P) (hl : 0 < lam A b d x) (k : ℕ) :
    (callRun A b d ρ O x k).x ∈ P ∧
      potential A b d (alphaOf m ρ (lam A b d x)) (callRun A b d ρ O x k).x ≤
        (m : ℝ) * Real.exp (alphaOf m ρ (lam A b d x) * lam A b d x) := by
  set lam0 := lam A b d x
  set α := alphaOf m ρ lam0
  have hlam_le : lam0 ≤ ρ := lam_le_rho A b d P hd ρ hρ hx
  obtain ⟨hα, _⟩ := alphaOf_pos_and_mul_ge_four (m := m) hl hlam_le
  obtain ⟨hσ0, hσ1⟩ := sigmaOf_bounds (m := m) hl hlam_le
  induction k with
  | zero =>
    simp only [callRun, Function.iterate_zero, id_eq]
    refine ⟨hx, ?_⟩
    rw [potential_eq_sum A b d hd]
    have hle : ∀ i ∈ (Finset.univ : Finset (Fin m)),
        Real.exp (α * (A.mulVec x i - b i) / d i) ≤ Real.exp (α * lam0) := by
      intro i _
      rw [Real.exp_le_exp]
      have hi : (A.mulVec x i - b i) / d i ≤ lam0 :=
        Finset.le_sup' (f := fun j => (A.mulVec x j - b j) / d j) (Finset.mem_univ i)
      have heq : α * (A.mulVec x i - b i) / d i = α * ((A.mulVec x i - b i) / d i) :=
        (mul_div_assoc' α _ _).symm
      rw [heq]
      exact mul_le_mul_of_nonneg_left hi (le_of_lt hα)
    calc
      (∑ i : Fin m, Real.exp (α * (A.mulVec x i - b i) / d i)) ≤
          ∑ _i : Fin m, Real.exp (α * lam0) := Finset.sum_le_sum hle
      _ = (m : ℝ) * Real.exp (α * lam0) := by
        simp [Finset.sum_const, nsmul_eq_mul]
  | succ k ih =>
    obtain ⟨hxk, hpotk⟩ := ih
    have hstep_eq : callRun A b d ρ O x (k + 1) =
        callStep A b d ρ O lam0 (callRun A b d ρ O x k) := by
      simp only [callRun, Function.iterate_succ_apply']
      rfl
    rw [hstep_eq]
    set s := callRun A b d ρ O x k
    unfold callStep
    cases htag : s.tag with
    | halved => exact ⟨hxk, hpotk⟩
    | g2 => exact ⟨hxk, hpotk⟩
    | running =>
      dsimp only
      split_ifs with hlt hg2
      · exact ⟨hxk, hpotk⟩
      · exact ⟨hxk, hpotk⟩
      · have hy0 : 0 ≤ dual A b d α s.x := dual_nonneg A b d hd α s.x
        have hxt : O (dual A b d α s.x) ∈ P := (hO _ hy0).1
        have hmem' : (1 - sigmaOf m ρ lam0) • s.x + sigmaOf m ρ lam0 • O (dual A b d α s.x) ∈ P :=
          hP hxk hxt (by linarith) (le_of_lt hσ0) (by ring)
        refine ⟨hmem', ?_⟩
        have hdec := one_step_potential_decrease A b d P hd ρ hρ lam0 hl hlam_le
          s.x (O (dual A b d α s.x)) hxk hxt hlt hg2
        have hpos_pot : 0 < potential A b d α s.x := potential_pos A b d hd α s.x
        have hpos_prod : 0 < (11 / 810 : ℝ) * (α * sigmaOf m ρ lam0 * lam0) := by positivity
        nlinarith

/-- **Potential bounds during one call.** Plotkin–Shmoys–Tardos, TR 999 (1992), §4, p. 27:
"Observe that during a single call to IMPROVE-GENERAL we have `e^{αλ₀/2} ≤ Φ ≤ me^{αλ₀}`."
For a call started at `x ∈ P` with `λ₀ = maxᵢ (aᵢ x − bᵢ)/dᵢ > 0` and `α = 4λ₀⁻¹ ln(6mρλ₀⁻¹)`
(`d > 0`, `P` convex, `ρ` a width bound, `O` a subroutine (10)), every iterate `x_k` of the call
has `Φ(x_k) ≤ m e^{αλ₀}`, and every iterate at which the loop runs (`λ(x_k) ≥ λ₀/2`) has
`e^{αλ₀/2} ≤ Φ(x_k)`. -/
theorem potential_sandwich {m n : ℕ} [NeZero m] (A : Matrix (Fin m) (Fin n) ℝ)
    (b d : Fin m → ℝ) (P : Set (Fin n → ℝ)) (hd : ∀ i, 0 < d i) (hP : Convex ℝ P) (ρ : ℝ)
    (hρ : IsWidthBound A b d P ρ) (O : (Fin m → ℝ) → (Fin n → ℝ)) (hO : IsMinOracle A P O)
    (x : Fin n → ℝ) (hx : x ∈ P) (hl : 0 < lam A b d x) (k : ℕ) :
    potential A b d (alphaOf m ρ (lam A b d x)) (callRun A b d ρ O x k).x ≤
        (m : ℝ) * Real.exp (alphaOf m ρ (lam A b d x) * lam A b d x) ∧
      (lam A b d x / 2 ≤ lam A b d (callRun A b d ρ O x k).x →
        Real.exp (alphaOf m ρ (lam A b d x) * lam A b d x / 2) ≤
          potential A b d (alphaOf m ρ (lam A b d x)) (callRun A b d ρ O x k).x) := by
  refine ⟨(callRun_mem_and_upper A b d P hd hP ρ hρ O hO x hx hl k).2, ?_⟩
  intro hlam_ge
  set lam0 := lam A b d x
  set α := alphaOf m ρ lam0
  set xk := (callRun A b d ρ O x k).x
  have hlam_le : lam0 ≤ ρ := lam_le_rho A b d P hd ρ hρ hx
  obtain ⟨hα, _⟩ := alphaOf_pos_and_mul_ge_four (m := m) hl hlam_le
  obtain ⟨i₀, hi₀_mem, hi₀_eq⟩ :=
    Finset.exists_mem_eq_sup' Finset.univ_nonempty (fun i => (A.mulVec xk i - b i) / d i)
  have hlam_xk : lam A b d xk = (A.mulVec xk i₀ - b i₀) / d i₀ := hi₀_eq
  rw [potential_eq_sum A b d hd]
  have hsingle :
      Real.exp (α * (A.mulVec xk i₀ - b i₀) / d i₀) ≤
        ∑ i : Fin m, Real.exp (α * (A.mulVec xk i - b i) / d i) :=
    Finset.single_le_sum (f := fun i => Real.exp (α * (A.mulVec xk i - b i) / d i))
      (fun i _ => le_of_lt (Real.exp_pos _)) hi₀_mem
  refine le_trans ?_ hsingle
  rw [Real.exp_le_exp]
  have heq : α * (A.mulVec xk i₀ - b i₀) / d i₀ = α * lam A b d xk := by
    rw [hlam_xk, mul_div_assoc']
  rw [heq]
  nlinarith

end PlotkinShmoysTardos

open PlotkinShmoysTardos

theorem solution {m n : ℕ} [NeZero m] (A : Matrix (Fin m) (Fin n) ℝ)
    (b d : Fin m → ℝ) (P : Set (Fin n → ℝ)) (hd : ∀ i, 0 < d i) (hP : Convex ℝ P) (ρ : ℝ)
    (hρ : IsWidthBound A b d P ρ) (O : (Fin m → ℝ) → (Fin n → ℝ)) (hO : IsMinOracle A P O)
    (x : Fin n → ℝ) (hx : x ∈ P) (hl : 0 < lam A b d x) (k : ℕ) :
    potential A b d (alphaOf m ρ (lam A b d x)) (callRun A b d ρ O x k).x ≤
        (m : ℝ) * Real.exp (alphaOf m ρ (lam A b d x) * lam A b d x) ∧
      (lam A b d x / 2 ≤ lam A b d (callRun A b d ρ O x k).x →
        Real.exp (alphaOf m ρ (lam A b d x) * lam A b d x / 2) ≤
          potential A b d (alphaOf m ρ (lam A b d x)) (callRun A b d ρ O x k).x) :=
  PlotkinShmoysTardos.potential_sandwich A b d P hd hP ρ hρ O hO x hx hl k
