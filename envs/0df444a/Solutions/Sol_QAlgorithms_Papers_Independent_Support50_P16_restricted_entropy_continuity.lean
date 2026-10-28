-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Support50.P16.restricted_entropy_continuity
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-27T05:44:45.248981+00:00
-- url     : https://prove2.me/submissions/e2dbc778-358a-4ecc-b8d7-03162ead5beb

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P16

open QAlgorithms Filter
open scoped Matrix ComplexConjugate ComplexOrder ENNReal

attribute [local instance] Classical.propDecidable Classical.decEq

namespace H10


/-- Key matrix bound: for a PSD effect `M` and a density matrix `ρ`,
`0 ≤ Re tr(Mρ) ≤ Re tr(M)`. -/
lemma effect_bounds {I : Type} [Fintype I] [DecidableEq I]
    {M rho : Matrix I I ℂ} (hM : M.PosSemidef) (hrho : IsDensityMatrix rho) :
    0 ≤ (M * rho).trace.re ∧ (M * rho).trace.re ≤ M.trace.re := by
  have hH : rho.IsHermitian := hrho.1.1
  set U := hH.eigenvectorUnitary with hU
  set lam := hH.eigenvalues with hlam
  have hspec : rho = (U : Matrix I I ℂ) * Matrix.diagonal (RCLike.ofReal ∘ lam) * (star U : Matrix I I ℂ) := by
    have := hH.spectral_theorem
    rw [Unitary.conjStarAlgAut_apply] at this
    exact this
  -- N = U* M U is PSD
  set N : Matrix I I ℂ := (star U : Matrix I I ℂ) * M * (U : Matrix I I ℂ) with hN
  have hNpsd : N.PosSemidef := by
    have := hM.conjTranspose_mul_mul_same (U : Matrix I I ℂ)
    simpa [hN, Matrix.star_eq_conjTranspose] using this
  have htr : (M * rho).trace = ∑ i, N i i * (lam i : ℂ) := by
    rw [hspec]
    have : M * ((U : Matrix I I ℂ) * Matrix.diagonal (RCLike.ofReal ∘ lam) * (star U : Matrix I I ℂ))
        = (M * (U : Matrix I I ℂ) * Matrix.diagonal (RCLike.ofReal ∘ lam)) * (star U : Matrix I I ℂ) := by
      simp [Matrix.mul_assoc]
    rw [this, Matrix.trace_mul_comm]
    have : (star U : Matrix I I ℂ) * (M * (U : Matrix I I ℂ) * Matrix.diagonal (RCLike.ofReal ∘ lam))
        = N * Matrix.diagonal (RCLike.ofReal ∘ lam) := by
      simp [hN, Matrix.mul_assoc]
    rw [this]
    simp [Matrix.trace, Matrix.mul_diagonal]
  have htrN : N.trace = M.trace := by
    simp only [hN]
    rw [Matrix.trace_mul_cycle, Unitary.mul_star_self_of_mem U.2, Matrix.one_mul]
  have hlam0 : ∀ i, 0 ≤ lam i := fun i => hrho.1.eigenvalues_nonneg i
  have hsum : ∑ i, lam i = 1 := by
    have h1 := hH.trace_eq_sum_eigenvalues
    rw [hrho.2] at h1
    have := congrArg Complex.re h1
    simp [Complex.re_sum] at this
    simpa [hlam] using this.symm
  have hlam1 : ∀ i, lam i ≤ 1 := by
    intro i
    rw [← hsum]
    exact Finset.single_le_sum (fun j _ => hlam0 j) (Finset.mem_univ i)
  have hNre : ∀ i, 0 ≤ (N i i).re := by
    intro i
    have := hNpsd.diag_nonneg (i := i)
    exact (Complex.nonneg_iff.mp this).1
  have hre : (M * rho).trace.re = ∑ i, (N i i).re * lam i := by
    rw [htr, Complex.re_sum]
    congr 1; ext i
    simp [Complex.mul_re]
  have hMre : M.trace.re = ∑ i, (N i i).re := by
    rw [← htrN]; simp [Matrix.trace, Complex.re_sum]
  constructor
  · rw [hre]
    exact Finset.sum_nonneg fun i _ => mul_nonneg (hNre i) (hlam0 i)
  · rw [hre, hMre]
    apply Finset.sum_le_sum
    intro i _
    calc (N i i).re * lam i ≤ (N i i).re * 1 := by
          exact mul_le_mul_of_nonneg_left (hlam1 i) (hNre i)
      _ = (N i i).re := mul_one _



/-- cutoff of `negMulLog` beyond `1/e` -/
noncomputable def gcut (u : ℝ) : ℝ := if u ≤ (Real.exp 1)⁻¹ then Real.negMulLog u else 0

lemma gcut_nonneg {u : ℝ} (hu : 0 ≤ u) : 0 ≤ gcut u := by
  unfold gcut
  split_ifs with h
  · apply Real.negMulLog_nonneg hu
    calc u ≤ (Real.exp 1)⁻¹ := h
      _ ≤ 1 := by
        rw [inv_le_one₀ (Real.exp_pos 1)]
        have := Real.add_one_le_exp (1 : ℝ); linarith
  · exact le_rfl

lemma negMulLog_monoOn : MonotoneOn Real.negMulLog (Set.Icc 0 (Real.exp 1)⁻¹) := by
  apply monotoneOn_of_deriv_nonneg (convex_Icc _ _)
  · exact Real.continuous_negMulLog.continuousOn
  · rw [interior_Icc]
    exact Real.differentiableOn_negMulLog.mono
      (fun x hx => Set.mem_compl_singleton_iff.mpr hx.1.ne')
  · rw [interior_Icc]
    intro x hx
    rw [Real.deriv_negMulLog hx.1.ne']
    have : Real.log x ≤ Real.log (Real.exp 1)⁻¹ := Real.log_le_log hx.1 hx.2.le
    rw [Real.log_inv, Real.log_exp] at this
    linarith

/-- pointwise continuity estimate for `t ↦ t log t`, ordered case -/
lemma phi_diff_ordered {t t' K : ℝ} (ht : 0 ≤ t) (htt' : t ≤ t') (ht'K : t' ≤ K) (hK : 1 ≤ K) :
    t' * Real.log t' - t * Real.log t ≤ (t' - t) * (Real.log K + 1) ∧
    t * Real.log t - t' * Real.log t' ≤ (t' - t) * (Real.log K + 1) + gcut (t' - t) := by
  have hu0 : 0 ≤ t' - t := by linarith
  have hlogK : 0 ≤ Real.log K := Real.log_nonneg hK
  have hnn : 0 ≤ (t' - t) * (Real.log K + 1) := mul_nonneg hu0 (by linarith)
  have hulogK : 0 ≤ (t' - t) * Real.log K := mul_nonneg hu0 hlogK
  rcases eq_or_lt_of_le hu0 with hu0' | hupos
  · -- u = 0
    have ht'eq : t' = t := by linarith
    rw [ht'eq]
    refine ⟨by simp, ?_⟩
    simp only [sub_self, zero_mul, zero_add]
    exact gcut_nonneg le_rfl
  · have ht'pos : 0 < t' := by linarith
    have hlogt' : Real.log t' ≤ Real.log K := Real.log_le_log ht'pos ht'K
    constructor
    · -- (a)
      rcases eq_or_lt_of_le ht with ht0 | htpos
      · subst ht0
        simp only [Real.log_zero, mul_zero, sub_zero]
        calc t' * Real.log t' ≤ t' * Real.log K := mul_le_mul_of_nonneg_left hlogt' ht'pos.le
          _ ≤ t' * (Real.log K + 1) := by nlinarith
      · have h1 : Real.log t' - Real.log t ≤ (t' - t) / t := by
          rw [← Real.log_div ht'pos.ne' htpos.ne']
          have := Real.log_le_sub_one_of_pos (div_pos ht'pos htpos)
          calc Real.log (t' / t) ≤ t' / t - 1 := this
            _ = (t' - t) / t := by field_simp
        have h2 : t * (Real.log t' - Real.log t) ≤ t' - t := by
          calc t * (Real.log t' - Real.log t) ≤ t * ((t' - t) / t) :=
                mul_le_mul_of_nonneg_left h1 htpos.le
            _ = t' - t := by field_simp
        have h3 : (t' - t) * Real.log t' ≤ (t' - t) * Real.log K :=
          mul_le_mul_of_nonneg_left hlogt' hu0
        calc t' * Real.log t' - t * Real.log t
            = t * (Real.log t' - Real.log t) + (t' - t) * Real.log t' := by ring
          _ ≤ (t' - t) + (t' - t) * Real.log K := add_le_add h2 h3
          _ = (t' - t) * (Real.log K + 1) := by ring
    · -- (b)
      have hb1 : t * Real.log t - t' * Real.log t' ≤ -((t' - t) * Real.log t') := by
        rcases eq_or_lt_of_le ht with ht0 | htpos
        · subst ht0; simp
        · have : Real.log t ≤ Real.log t' := Real.log_le_log htpos htt'
          have : t * (Real.log t - Real.log t') ≤ 0 :=
            mul_nonpos_of_nonneg_of_nonpos htpos.le (by linarith)
          calc t * Real.log t - t' * Real.log t'
              = t * (Real.log t - Real.log t') - (t' - t) * Real.log t' := by ring
            _ ≤ -((t' - t) * Real.log t') := by linarith
      have hb2 : -((t' - t) * Real.log t') ≤ Real.negMulLog (t' - t) := by
        have : Real.log (t' - t) ≤ Real.log t' := Real.log_le_log hupos (by linarith)
        unfold Real.negMulLog
        nlinarith
      unfold gcut
      split_ifs with hcut
      · linarith
      · push Not at hcut
        have : Real.log (Real.exp 1)⁻¹ < Real.log (t' - t) := Real.log_lt_log (by positivity) hcut
        rw [Real.log_inv, Real.log_exp] at this
        have : Real.negMulLog (t' - t) ≤ (t' - t) * 1 := by
          unfold Real.negMulLog; nlinarith
        linarith

lemma phi_diff {t t' K : ℝ} (ht : 0 ≤ t) (ht' : 0 ≤ t') (htK : t ≤ K) (ht'K : t' ≤ K) (hK : 1 ≤ K) :
    |t * Real.log t - t' * Real.log t'| ≤ |t - t'| * (Real.log K + 1) + gcut |t - t'| := by
  rcases le_total t t' with h | h
  · obtain ⟨ha, hb⟩ := phi_diff_ordered ht h ht'K hK
    have habs : |t - t'| = t' - t := by rw [abs_sub_comm]; exact abs_of_nonneg (by linarith)
    rw [habs, abs_le]
    have := gcut_nonneg (by linarith : 0 ≤ t' - t)
    constructor <;> linarith
  · obtain ⟨ha, hb⟩ := phi_diff_ordered ht' h htK hK
    have habs : |t - t'| = t - t' := abs_of_nonneg (by linarith)
    rw [habs, abs_le]
    have := gcut_nonneg (by linarith : 0 ≤ t - t')
    constructor <;> linarith

/-- Jensen step -/
lemma jensen_gcut {m : ℕ} (q u : Fin m → ℝ) (hq : ∀ x, 0 ≤ q x) (hq1 : ∑ x, q x ≤ 1)
    (hu : ∀ x, 0 ≤ u x) (ε : ℝ) (hε : 0 < ε) (hεe : ε ≤ (Real.exp 1)⁻¹)
    (hqu : ∑ x, q x * u x ≤ ε) :
    ∑ x, q x * gcut (u x) ≤ Real.negMulLog ε := by
  set S := Finset.univ.filter (fun x => u x ≤ (Real.exp 1)⁻¹) with hS
  have hsplit : ∑ x, q x * gcut (u x) = ∑ x ∈ S, q x * Real.negMulLog (u x) := by
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun x => u x ≤ (Real.exp 1)⁻¹)]
    have h2 : ∑ x ∈ Finset.univ.filter (fun x => ¬ u x ≤ (Real.exp 1)⁻¹), q x * gcut (u x) = 0 := by
      apply Finset.sum_eq_zero
      intro x hx
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
      simp [gcut, hx]
    rw [h2, add_zero]
    apply Finset.sum_congr rfl
    intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
    simp [gcut, hx]
  rw [hsplit]
  set Q := ∑ x ∈ S, q x with hQ
  set v := ∑ x ∈ S, q x * u x with hv
  have hQ0 : 0 ≤ Q := Finset.sum_nonneg fun x _ => hq x
  have hQ1 : Q ≤ 1 := le_trans (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S)
    (fun x _ _ => hq x)) hq1
  have hv0 : 0 ≤ v := Finset.sum_nonneg fun x _ => mul_nonneg (hq x) (hu x)
  have hvε : v ≤ ε := le_trans (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S)
    (fun x _ _ => mul_nonneg (hq x) (hu x))) hqu
  have hεe1 : ε ≤ 1 := by
    calc ε ≤ (Real.exp 1)⁻¹ := hεe
      _ ≤ 1 := by
        rw [inv_le_one₀ (Real.exp_pos 1)]
        have := Real.add_one_le_exp (1 : ℝ); linarith
  have hmono : Real.negMulLog v ≤ Real.negMulLog ε :=
    negMulLog_monoOn ⟨hv0, le_trans hvε hεe⟩ ⟨hε.le, hεe⟩ hvε
  rcases eq_or_lt_of_le hQ0 with hQz | hQpos
  · -- Q = 0: all q on S vanish
    have hzero : ∀ x ∈ S, q x = 0 := by
      intro x hx
      have := (Finset.sum_eq_zero_iff_of_nonneg (fun y _ => hq y)).mp hQz.symm x hx
      exact this
    calc ∑ x ∈ S, q x * Real.negMulLog (u x) = 0 := by
          apply Finset.sum_eq_zero; intro x hx; rw [hzero x hx]; ring
      _ ≤ Real.negMulLog ε := Real.negMulLog_nonneg hε.le hεe1
  · -- Jensen with weights q/Q
    have hw0 : ∀ x ∈ S, 0 ≤ q x / Q := fun x _ => div_nonneg (hq x) hQ0
    have hw1 : ∑ x ∈ S, q x / Q = 1 := by
      rw [← Finset.sum_div]; exact div_self hQpos.ne'
    have hmem : ∀ x ∈ S, u x ∈ Set.Ici (0 : ℝ) := fun x _ => hu x
    have hJ := Real.concaveOn_negMulLog.le_map_sum hw0 hw1 hmem
    simp only [smul_eq_mul] at hJ
    have hsumv : ∑ x ∈ S, q x / Q * u x = v / Q := by
      rw [hv, Finset.sum_div]
      apply Finset.sum_congr rfl; intro x _; ring
    rw [hsumv] at hJ
    -- ∑ q negMulLog u = Q * ∑ (q/Q) negMulLog u ≤ Q * negMulLog (v/Q)
    have h1 : ∑ x ∈ S, q x * Real.negMulLog (u x) = Q * ∑ x ∈ S, q x / Q * Real.negMulLog (u x) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl; intro x _
      field_simp
    have h2 : Q * Real.negMulLog (v / Q) ≤ Real.negMulLog v := by
      -- concavity with 0
      have hc := Real.concaveOn_negMulLog.2 (show v / Q ∈ Set.Ici (0:ℝ) from div_nonneg hv0 hQ0)
        (show (0:ℝ) ∈ Set.Ici (0:ℝ) from Set.mem_Ici.mpr le_rfl) hQ0 (by linarith : 0 ≤ 1 - Q) (by ring)
      simp only [smul_eq_mul, Real.negMulLog_zero, mul_zero, add_zero] at hc
      have : Q * (v / Q) = v := by field_simp
      rw [this] at hc
      exact hc
    calc ∑ x ∈ S, q x * Real.negMulLog (u x)
        = Q * ∑ x ∈ S, q x / Q * Real.negMulLog (u x) := h1
      _ ≤ Q * Real.negMulLog (v / Q) := mul_le_mul_of_nonneg_left hJ hQ0
      _ ≤ Real.negMulLog v := h2
      _ ≤ Real.negMulLog ε := hmono


/-- classical continuity estimate in nats -/
lemma kl_cont {m : ℕ} (p p' q : Fin m → ℝ) (K ε : ℝ)
    (hp : ∀ x, 0 ≤ p x) (hp' : ∀ x, 0 ≤ p' x) (hq : ∀ x, 0 ≤ q x) (hq1 : ∑ x, q x ≤ 1)
    (hK : 1 ≤ K) (hpK : ∀ x, p x ≤ K * q x) (hp'K : ∀ x, p' x ≤ K * q x)
    (hε : 0 < ε) (hεe : ε ≤ (Real.exp 1)⁻¹) (hdist : ∑ x, |p x - p' x| ≤ ε) :
    ∑ x, p x * (Real.log (p x) - Real.log (q x)) ≤
      ∑ x, p' x * (Real.log (p' x) - Real.log (q x)) + ε * (Real.log K + 1) + Real.negMulLog ε := by
  have hK0 : 0 < K := by linarith
  -- pointwise identity
  have key : ∀ (r : ℝ) (x : Fin m), 0 ≤ r → r ≤ K * q x →
      r * (Real.log r - Real.log (q x)) = q x * ((r / q x) * Real.log (r / q x)) := by
    intro r x hr hrK
    rcases eq_or_lt_of_le (hq x) with hq0 | hqpos
    · have : r = 0 := by
        have : K * q x = 0 := by rw [← hq0]; ring
        linarith
      subst this; rw [← hq0]; simp
    · rcases eq_or_lt_of_le hr with hr0 | hrpos
      · subst hr0; simp
      · rw [Real.log_div hrpos.ne' hqpos.ne']
        field_simp
  have key_nonneg : ∀ (r : ℝ) (x : Fin m), 0 ≤ r → 0 ≤ r / q x := fun r x hr => div_nonneg hr (hq x)
  have key_le : ∀ (r : ℝ) (x : Fin m), 0 ≤ r → r ≤ K * q x → r / q x ≤ K := by
    intro r x hr hrK
    rcases eq_or_lt_of_le (hq x) with hq0 | hqpos
    · rw [← hq0]; simp; exact hK0.le
    · rw [div_le_iff₀ hqpos]; exact hrK
  have key_abs : ∀ x, q x * |p x / q x - p' x / q x| = |p x - p' x| := by
    intro x
    rcases eq_or_lt_of_le (hq x) with hq0 | hqpos
    · have h1 : p x = 0 := by
        have : K * q x = 0 := by rw [← hq0]; ring
        linarith [hpK x, hp x]
      have h2 : p' x = 0 := by
        have : K * q x = 0 := by rw [← hq0]; ring
        linarith [hp'K x, hp' x]
      rw [h1, h2, ← hq0]; simp
    · rw [← sub_div, abs_div, abs_of_pos hqpos]
      field_simp
  rw [Finset.sum_congr rfl (fun x _ => key (p x) x (hp x) (hpK x)),
    Finset.sum_congr rfl (fun x _ => key (p' x) x (hp' x) (hp'K x))]
  have hpt : ∀ x, |p x / q x * Real.log (p x / q x) - p' x / q x * Real.log (p' x / q x)| ≤
      |p x / q x - p' x / q x| * (Real.log K + 1) + gcut |p x / q x - p' x / q x| :=
    fun x => phi_diff (key_nonneg _ x (hp x)) (key_nonneg _ x (hp' x))
      (key_le _ x (hp x) (hpK x)) (key_le _ x (hp' x) (hp'K x)) hK
  have hsum1 : ∑ x, q x * |p x / q x - p' x / q x| ≤ ε := by
    rw [Finset.sum_congr rfl (fun x _ => key_abs x)]; exact hdist
  have hJ : ∑ x, q x * gcut |p x / q x - p' x / q x| ≤ Real.negMulLog ε :=
    jensen_gcut q (fun x => |p x / q x - p' x / q x|) hq hq1 (fun x => abs_nonneg _) ε hε hεe hsum1
  have hlogK : 0 ≤ Real.log K + 1 := by linarith [Real.log_nonneg hK]
  have hmain : ∑ x, q x * (p x / q x * Real.log (p x / q x)) -
      ∑ x, q x * (p' x / q x * Real.log (p' x / q x)) ≤
      ε * (Real.log K + 1) + Real.negMulLog ε := by
    rw [← Finset.sum_sub_distrib]
    calc ∑ x, (q x * (p x / q x * Real.log (p x / q x)) - q x * (p' x / q x * Real.log (p' x / q x)))
        = ∑ x, q x * (p x / q x * Real.log (p x / q x) - p' x / q x * Real.log (p' x / q x)) := by
          apply Finset.sum_congr rfl; intro x _; ring
      _ ≤ ∑ x, q x * |p x / q x * Real.log (p x / q x) - p' x / q x * Real.log (p' x / q x)| := by
          apply Finset.sum_le_sum; intro x _
          exact mul_le_mul_of_nonneg_left (le_abs_self _) (hq x)
      _ ≤ ∑ x, q x * (|p x / q x - p' x / q x| * (Real.log K + 1) + gcut |p x / q x - p' x / q x|) := by
          apply Finset.sum_le_sum; intro x _
          exact mul_le_mul_of_nonneg_left (hpt x) (hq x)
      _ = (Real.log K + 1) * ∑ x, q x * |p x / q x - p' x / q x| +
          ∑ x, q x * gcut |p x / q x - p' x / q x| := by
          rw [Finset.mul_sum, ← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl; intro x _; ring
      _ ≤ (Real.log K + 1) * ε + Real.negMulLog ε :=
          add_le_add (mul_le_mul_of_nonneg_left hsum1 hlogK) hJ
      _ = ε * (Real.log K + 1) + Real.negMulLog ε := by ring
  linarith

open QAlgorithms.Papers.Independent.Support50.P16 in
lemma finiteKL_eq_ofReal {m : ℕ} (p q : Fin m → ℝ) (hg : ∀ x, 0 < p x → 0 < q x) :
    finiteKLBits p q = ENNReal.ofReal ((∑ x, p x * (Real.log (p x) - Real.log (q x))) / Real.log 2) := by
  unfold finiteKLBits
  rw [if_pos hg]
  congr 1
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro x _
  unfold Real.logb
  rw [← sub_div, mul_div_assoc]

lemma guard_of_ratio {m : ℕ} (p q : Fin m → ℝ) (K : ℝ) (hK0 : 0 < K)
    (hpK : ∀ x, p x ≤ K * q x) : ∀ x, 0 < p x → 0 < q x := by
  intro x hx
  by_contra h
  push Not at h
  have : K * q x ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hK0.le h
  linarith [hpK x]

open QAlgorithms.Papers.Independent.Support50.P16 in
lemma finiteKL_cont {m : ℕ} (p p' q : Fin m → ℝ) (K ε : ℝ)
    (hp : ∀ x, 0 ≤ p x) (hp' : ∀ x, 0 ≤ p' x) (hq : ∀ x, 0 ≤ q x) (hq1 : ∑ x, q x ≤ 1)
    (hK : 1 ≤ K) (hpK : ∀ x, p x ≤ K * q x) (hp'K : ∀ x, p' x ≤ K * q x)
    (hε : 0 < ε) (hεe : ε ≤ (Real.exp 1)⁻¹) (hdist : ∑ x, |p x - p' x| ≤ ε) :
    finiteKLBits p q ≤ finiteKLBits p' q +
      ENNReal.ofReal ((ε * (Real.log K + 1) + Real.negMulLog ε) / Real.log 2) := by
  have hK0 : 0 < K := by linarith
  rw [finiteKL_eq_ofReal p q (guard_of_ratio p q K hK0 hpK),
    finiteKL_eq_ofReal p' q (guard_of_ratio p' q K hK0 hp'K)]
  have h := kl_cont p p' q K ε hp hp' hq hq1 hK hpK hp'K hε hεe hdist
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  calc ENNReal.ofReal ((∑ x, p x * (Real.log (p x) - Real.log (q x))) / Real.log 2)
      ≤ ENNReal.ofReal ((∑ x, p' x * (Real.log (p' x) - Real.log (q x))) / Real.log 2 +
          (ε * (Real.log K + 1) + Real.negMulLog ε) / Real.log 2) := by
        apply ENNReal.ofReal_le_ofReal
        rw [← add_div]
        exact div_le_div_of_nonneg_right (by linarith) hlog2.le
    _ ≤ _ := ENNReal.ofReal_add_le

open QAlgorithms.Papers.Independent.Support50.P16 in
lemma finiteKL_ratio {m : ℕ} (p q : Fin m → ℝ) (K : ℝ)
    (hp : ∀ x, 0 ≤ p x) (hp1 : ∑ x, p x = 1) (hK : 1 ≤ K) (hpK : ∀ x, p x ≤ K * q x) :
    finiteKLBits p q ≤ ENNReal.ofReal (Real.logb 2 K) := by
  have hK0 : 0 < K := by linarith
  have hg := guard_of_ratio p q K hK0 hpK
  unfold finiteKLBits
  rw [if_pos hg]
  apply ENNReal.ofReal_le_ofReal
  calc ∑ x, p x * (Real.logb 2 (p x) - Real.logb 2 (q x)) ≤ ∑ x, p x * Real.logb 2 K := by
        apply Finset.sum_le_sum
        intro x _
        rcases eq_or_lt_of_le (hp x) with h0 | hpos
        · rw [← h0]; simp
        · apply mul_le_mul_of_nonneg_left _ (hp x)
          have hqpos := hg x hpos
          rw [← Real.logb_div hpos.ne' hqpos.ne']
          apply Real.logb_le_logb_of_le (by norm_num) (div_pos hpos hqpos)
          rw [div_le_iff₀ hqpos]; exact hpK x
    _ = Real.logb 2 K := by rw [← Finset.sum_mul, hp1, one_mul]

open QAlgorithms.Papers.Independent.Support50.P16 in
lemma finiteKL_mix {m : ℕ} (p q q' : Fin m → ℝ) (c : ℝ)
    (hp : ∀ x, 0 ≤ p x) (hp1 : ∑ x, p x = 1) (hq : ∀ x, 0 ≤ q x)
    (hc : 0 < c) (hqq' : ∀ x, c * q x ≤ q' x) :
    finiteKLBits p q' ≤ finiteKLBits p q + ENNReal.ofReal (-Real.logb 2 c) := by
  by_cases hg : ∀ x, 0 < p x → 0 < q x
  · have hg' : ∀ x, 0 < p x → 0 < q' x := fun x hx =>
      lt_of_lt_of_le (mul_pos hc (hg x hx)) (hqq' x)
    unfold finiteKLBits
    rw [if_pos hg, if_pos hg']
    calc ENNReal.ofReal (∑ x, p x * (Real.logb 2 (p x) - Real.logb 2 (q' x)))
        ≤ ENNReal.ofReal (∑ x, p x * (Real.logb 2 (p x) - Real.logb 2 (q x)) + (-Real.logb 2 c)) := by
          apply ENNReal.ofReal_le_ofReal
          have : ∑ x, p x * (Real.logb 2 (p x) - Real.logb 2 (q x)) + (-Real.logb 2 c) =
              ∑ x, (p x * (Real.logb 2 (p x) - Real.logb 2 (q x)) + p x * (-Real.logb 2 c)) := by
            rw [Finset.sum_add_distrib, ← Finset.sum_mul, hp1, one_mul]
          rw [this]
          apply Finset.sum_le_sum
          intro x _
          rcases eq_or_lt_of_le (hp x) with h0 | hpos
          · rw [← h0]; simp
          · have hqpos := hg x hpos
            have : Real.logb 2 c + Real.logb 2 (q x) ≤ Real.logb 2 (q' x) := by
              rw [← Real.logb_mul hc.ne' hqpos.ne']
              exact Real.logb_le_logb_of_le (by norm_num) (mul_pos hc hqpos) (hqq' x)
            nlinarith
      _ ≤ _ := ENNReal.ofReal_add_le
  · unfold finiteKLBits
    rw [if_neg hg]
    simp


section Laws

open QAlgorithms.Papers.Independent.Support50.P16
open QAlgorithms.Papers.Independent.Information100.P04 (Measurement)

variable {I : Type} [Fintype I] [DecidableEq I]

lemma law_nonneg (T : Measurement I) {rho : Matrix I I ℂ} (hrho : IsDensityMatrix rho) (x) :
    0 ≤ povmOutcomeLaw T rho x :=
  (effect_bounds (T.valid.1 x) hrho).1

lemma law_le_trace (T : Measurement I) {rho : Matrix I I ℂ} (hrho : IsDensityMatrix rho) (x) :
    povmOutcomeLaw T rho x ≤ (T.effect x).trace.re :=
  (effect_bounds (T.valid.1 x) hrho).2

lemma law_sum (T : Measurement I) {rho : Matrix I I ℂ} (hrho : IsDensityMatrix rho) :
    ∑ x, povmOutcomeLaw T rho x = 1 := by
  unfold povmOutcomeLaw effectProb
  rw [← Complex.re_sum, ← Matrix.trace_sum, ← Matrix.sum_mul, T.valid.2, Matrix.one_mul, hrho.2]
  simp

lemma trace_re_nonneg (T : Measurement I) (x) : 0 ≤ (T.effect x).trace.re :=
  (Complex.nonneg_iff.mp (T.valid.1 x).trace_nonneg).1

lemma trace_re_sum (T : Measurement I) :
    ∑ x, (T.effect x).trace.re = Fintype.card I := by
  rw [← Complex.re_sum, ← Matrix.trace_sum, T.valid.2, Matrix.trace_one]
  simp

lemma law_mix (T : Measurement I) (a b : ℝ) (A B : Matrix I I ℂ) (x) :
    povmOutcomeLaw T ((a : ℂ) • A + (b : ℂ) • B) x =
      a * povmOutcomeLaw T A x + b * povmOutcomeLaw T B x := by
  unfold povmOutcomeLaw effectProb
  rw [Matrix.mul_add, Matrix.mul_smul, Matrix.mul_smul, Matrix.trace_add, Matrix.trace_smul,
    Matrix.trace_smul, Complex.add_re, smul_eq_mul, smul_eq_mul, Complex.re_ofReal_mul,
    Complex.re_ofReal_mul]

lemma law_tau (k : ℕ) (hk : 0 < k) (T : Measurement (Fin k)) (x) :
    povmOutcomeLaw T (QAlgorithms.Papers.Independent.Information100.P76.maximallyMixed k) x =
      (T.effect x).trace.re / k := by
  unfold povmOutcomeLaw effectProb QAlgorithms.Papers.Independent.Information100.P76.maximallyMixed
  have : (1 / (k : ℂ)) = ((1 / (k : ℝ) : ℝ) : ℂ) := by push_cast; ring
  rw [this, Matrix.mul_smul, Matrix.mul_one, Matrix.trace_smul, smul_eq_mul, Complex.re_ofReal_mul]
  ring

end Laws

section Main

open QAlgorithms.Papers.Independent.Support50.P16
open QAlgorithms.Papers.Independent.Information100.P04 (Measurement)

/-- finiteness via the maximally mixed reference state -/
lemma rE_le_log (k : ℕ+) (G : Set (Matrix (Fin (k : ℕ)) (Fin (k : ℕ)) ℂ))
    (M : Set (Measurement (Fin (k : ℕ))))
    (htau : QAlgorithms.Papers.Independent.Information100.P76.maximallyMixed k ∈ G)
    (rho : Matrix (Fin (k : ℕ)) (Fin (k : ℕ)) ℂ) (hrho : IsDensityMatrix rho) :
    restrictedEntropy G M rho ≤ ENNReal.ofReal (Real.logb 2 (k : ℝ)) := by
  unfold restrictedEntropy
  refine iInf_le_of_le ⟨_, htau⟩ (iSup_le fun T => ?_)
  have hk : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast k.pos
  have hkpos : (0 : ℝ) < (k : ℝ) := by linarith
  apply finiteKL_ratio _ _ (k : ℝ) (law_nonneg T.val hrho) (law_sum T.val hrho) hk
  intro x
  rw [law_tau k k.pos T.val x, mul_div_cancel₀ _ hkpos.ne']
  exact law_le_trace T.val hrho x

/-- one-sided continuity estimate -/
lemma one_side (k : ℕ+) (G : Set (Matrix (Fin (k : ℕ)) (Fin (k : ℕ)) ℂ))
    (M : Set (Measurement (Fin (k : ℕ))))
    (hstates : ∀ sigma ∈ G, IsDensityMatrix sigma)
    (hstar : ∀ sigma ∈ G, ∀ p : ℝ, 0 ≤ p → p ≤ 1 →
      (p : ℂ) • sigma + ((1-p : ℝ) : ℂ) •
        QAlgorithms.Papers.Independent.Information100.P76.maximallyMixed k ∈ G)
    (rho sigma : Matrix (Fin (k : ℕ)) (Fin (k : ℕ)) ℂ)
    (hrho : IsDensityMatrix rho) (hsigma : IsDensityMatrix sigma)
    (epsilon : ℝ) (heps : 0 < epsilon) (heps1 : epsilon ≤ (Real.exp 1)⁻¹)
    (hdistT : ∀ T ∈ M, ∑ x, |povmOutcomeLaw T rho x - povmOutcomeLaw T sigma x| ≤ epsilon) :
    restrictedEntropy G M rho ≤ restrictedEntropy G M sigma +
      ENNReal.ofReal ((epsilon * (Real.log ((k : ℝ) / epsilon) + 1) + Real.negMulLog epsilon) /
        Real.log 2 + (-Real.logb 2 (1 - epsilon))) := by
  have hk : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast k.pos
  have hkpos : (0 : ℝ) < (k : ℝ) := by linarith
  have hεlt1 : epsilon < 1 := by
    have h1 : (Real.exp 1)⁻¹ < 1 := by
      rw [inv_lt_one₀ (Real.exp_pos 1)]
      have := Real.add_one_le_exp (1 : ℝ); linarith
    linarith
  have hC1 : 0 ≤ (epsilon * (Real.log ((k : ℝ) / epsilon) + 1) + Real.negMulLog epsilon) /
      Real.log 2 := by
    apply div_nonneg _ (Real.log_nonneg (by norm_num))
    apply add_nonneg
    · apply mul_nonneg heps.le
      have : 1 ≤ (k : ℝ) / epsilon := by
        rw [le_div_iff₀ heps]; linarith
      linarith [Real.log_nonneg this]
    · exact Real.negMulLog_nonneg heps.le hεlt1.le
  have hC2 : 0 ≤ -Real.logb 2 (1 - epsilon) := by
    have : Real.logb 2 (1 - epsilon) ≤ 0 :=
      Real.logb_nonpos (by norm_num) (by linarith) (by linarith)
    linarith
  rw [ENNReal.ofReal_add hC1 hC2]
  unfold restrictedEntropy
  rw [ENNReal.iInf_add]
  refine le_iInf fun omega => ?_
  set tau := QAlgorithms.Papers.Independent.Information100.P76.maximallyMixed (k : ℕ) with htau
  have homega' := hstar omega.val omega.2 (1 - epsilon) (by linarith) (by linarith)
  refine iInf_le_of_le ⟨_, homega'⟩ (iSup_le fun T => ?_)
  refine le_trans ?_ (add_le_add (le_iSup (fun T : M => finiteKLBits
    (povmOutcomeLaw T.val sigma) (povmOutcomeLaw T.val omega.val)) T) le_rfl)
  -- pointwise estimate
  have hdens : IsDensityMatrix omega.val := hstates _ omega.2
  set p := povmOutcomeLaw T.val rho with hp
  set p' := povmOutcomeLaw T.val sigma with hp'
  set q := povmOutcomeLaw T.val omega.val with hq
  set t := povmOutcomeLaw T.val tau with ht
  have hq' : povmOutcomeLaw T.val (((1 - epsilon : ℝ) : ℂ) • omega.val +
      ((1 - (1 - epsilon) : ℝ) : ℂ) • tau) = fun x => (1 - epsilon) * q x + epsilon * t x := by
    funext x
    rw [law_mix, sub_sub_cancel]
  simp only [hq']
  have htx : ∀ x, t x = (T.val.effect x).trace.re / k := fun x => law_tau k k.pos T.val x
  have ht0 : ∀ x, 0 ≤ t x := fun x => by rw [htx]; exact div_nonneg (trace_re_nonneg T.val x) hkpos.le
  have htsum : ∑ x, t x = 1 := by
    simp only [htx]
    rw [← Finset.sum_div, trace_re_sum, Fintype.card_fin, div_self hkpos.ne']
  have hq0 : ∀ x, 0 ≤ q x := law_nonneg T.val hdens
  have hqsum : ∑ x, q x = 1 := law_sum T.val hdens
  have hp0 : ∀ x, 0 ≤ p x := law_nonneg T.val hrho
  have hp'0 : ∀ x, 0 ≤ p' x := law_nonneg T.val hsigma
  have hpt : ∀ x, p x ≤ (k : ℝ) * t x := fun x => by
    rw [htx, mul_div_cancel₀ _ hkpos.ne']; exact law_le_trace T.val hrho x
  have hp't : ∀ x, p' x ≤ (k : ℝ) * t x := fun x => by
    rw [htx, mul_div_cancel₀ _ hkpos.ne']; exact law_le_trace T.val hsigma x
  have hq'0 : ∀ x, 0 ≤ (1 - epsilon) * q x + epsilon * t x := fun x =>
    add_nonneg (mul_nonneg (by linarith) (hq0 x)) (mul_nonneg heps.le (ht0 x))
  have hq'sum : ∑ x, ((1 - epsilon) * q x + epsilon * t x) ≤ 1 := by
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hqsum, htsum]; linarith
  have hK : 1 ≤ (k : ℝ) / epsilon := by rw [le_div_iff₀ heps]; linarith
  have hratio : ∀ r : ℝ, 0 ≤ r → (∀ x, r ≤ (k : ℝ) * t x) → False ∨ True := fun _ _ _ => Or.inr trivial
  have hpK : ∀ x, p x ≤ (k : ℝ) / epsilon * ((1 - epsilon) * q x + epsilon * t x) := by
    intro x
    have h1 : (k : ℝ) * t x ≤ (k : ℝ) / epsilon * ((1 - epsilon) * q x + epsilon * t x) := by
      have : (k : ℝ) / epsilon * ((1 - epsilon) * q x + epsilon * t x) =
          (k : ℝ) * t x + (k : ℝ) / epsilon * ((1 - epsilon) * q x) := by
        field_simp; ring
      rw [this]
      have : 0 ≤ (k : ℝ) / epsilon * ((1 - epsilon) * q x) :=
        mul_nonneg (div_nonneg hkpos.le heps.le) (mul_nonneg (by linarith) (hq0 x))
      linarith
    exact le_trans (hpt x) h1
  have hp'K : ∀ x, p' x ≤ (k : ℝ) / epsilon * ((1 - epsilon) * q x + epsilon * t x) := by
    intro x
    have h1 : (k : ℝ) * t x ≤ (k : ℝ) / epsilon * ((1 - epsilon) * q x + epsilon * t x) := by
      have : (k : ℝ) / epsilon * ((1 - epsilon) * q x + epsilon * t x) =
          (k : ℝ) * t x + (k : ℝ) / epsilon * ((1 - epsilon) * q x) := by
        field_simp; ring
      rw [this]
      have : 0 ≤ (k : ℝ) / epsilon * ((1 - epsilon) * q x) :=
        mul_nonneg (div_nonneg hkpos.le heps.le) (mul_nonneg (by linarith) (hq0 x))
      linarith
    exact le_trans (hp't x) h1
  have hstep1 := finiteKL_cont p p' (fun x => (1 - epsilon) * q x + epsilon * t x)
    ((k : ℝ) / epsilon) epsilon hp0 hp'0 hq'0 hq'sum hK hpK hp'K heps heps1 (hdistT T.val T.2)
  have hstep2 := finiteKL_mix p' q (fun x => (1 - epsilon) * q x + epsilon * t x) (1 - epsilon)
    hp'0 (law_sum T.val hsigma) hq0 (by linarith)
    (fun x => by
      have : 0 ≤ epsilon * t x := mul_nonneg heps.le (ht0 x)
      linarith)
  calc finiteKLBits p (fun x => (1 - epsilon) * q x + epsilon * t x)
      ≤ finiteKLBits p' (fun x => (1 - epsilon) * q x + epsilon * t x) +
        ENNReal.ofReal ((epsilon * (Real.log ((k : ℝ) / epsilon) + 1) + Real.negMulLog epsilon) /
          Real.log 2) := hstep1
    _ ≤ (finiteKLBits p' q + ENNReal.ofReal (-Real.logb 2 (1 - epsilon))) +
        ENNReal.ofReal ((epsilon * (Real.log ((k : ℝ) / epsilon) + 1) + Real.negMulLog epsilon) /
          Real.log 2) := add_le_add hstep2 le_rfl
    _ = finiteKLBits p' q + (ENNReal.ofReal ((epsilon * (Real.log ((k : ℝ) / epsilon) + 1) +
          Real.negMulLog epsilon) / Real.log 2) + ENNReal.ofReal (-Real.logb 2 (1 - epsilon))) := by
        ring

/-- the numeric comparison with the printed modulus -/
lemma modulus_bound (k : ℕ+) (epsilon : ℝ) (heps : 0 < epsilon) (heps1 : epsilon ≤ 1 / Real.exp 1) :
    (epsilon * (Real.log ((k : ℝ) / epsilon) + 1) + Real.negMulLog epsilon) / Real.log 2 +
      (-Real.logb 2 (1 - epsilon)) ≤ continuityModulus k epsilon := by
  have hk : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast k.pos
  have hkpos : (0 : ℝ) < (k : ℝ) := by linarith
  have hε25 : epsilon ≤ 2 / 5 := by
    have h := Real.exp_one_gt_d9
    have : 1 / Real.exp 1 ≤ 2 / 5 := by
      rw [div_le_div_iff₀ (Real.exp_pos 1) (by norm_num)]; linarith
    linarith
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog2' := Real.log_two_gt_d9
  unfold continuityModulus
  rw [if_neg heps.ne']
  unfold Real.logb
  have hlogk : 0 ≤ Real.log (k : ℝ) := Real.log_nonneg hk
  have hlog6 : 2 * Real.log 2 ≤ Real.log 6 := by
    have : Real.log 4 ≤ Real.log 6 := Real.log_le_log (by norm_num) (by norm_num)
    have h4 : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast; ring
    linarith
  have hlog1e : -(5 / 3) * epsilon ≤ Real.log (1 - epsilon) := by
    have h := Real.one_sub_inv_le_log_of_pos (by linarith : 0 < 1 - epsilon)
    have hne : (1 - epsilon) ≠ 0 := (by linarith : (0:ℝ) < 1 - epsilon).ne'
    have : 1 - (1 - epsilon)⁻¹ = -(epsilon / (1 - epsilon)) := by
      field_simp
      ring
    rw [this] at h
    have : epsilon / (1 - epsilon) ≤ 5 / 3 * epsilon := by
      rw [div_le_iff₀ (by linarith)]; nlinarith
    linarith
  have hlogdiv : Real.log ((k : ℝ) / epsilon) = Real.log k - Real.log epsilon :=
    Real.log_div hkpos.ne' heps.ne'
  have hlog6k : Real.log (6 * (k : ℝ) / epsilon) = Real.log 6 + Real.log k - Real.log epsilon := by
    rw [Real.log_div (by positivity) heps.ne', Real.log_mul (by norm_num) hkpos.ne']
  have hneg : Real.negMulLog epsilon = -epsilon * Real.log epsilon := rfl
  rw [hlogdiv, hlog6k, hneg]
  have key : epsilon * (Real.log k - Real.log epsilon + 1) + -epsilon * Real.log epsilon -
      Real.log (1 - epsilon) ≤ 2 * epsilon * (Real.log 6 + Real.log k - Real.log epsilon) := by
    nlinarith [mul_nonneg heps.le hlogk]
  calc (epsilon * (Real.log k - Real.log epsilon + 1) + -epsilon * Real.log epsilon) / Real.log 2 +
        -(Real.log (1 - epsilon) / Real.log 2)
      = (epsilon * (Real.log k - Real.log epsilon + 1) + -epsilon * Real.log epsilon -
          Real.log (1 - epsilon)) / Real.log 2 := by ring
    _ ≤ (2 * epsilon * (Real.log 6 + Real.log k - Real.log epsilon)) / Real.log 2 :=
        div_le_div_of_nonneg_right key hlog2.le
    _ = 2 * epsilon * ((Real.log 6 + Real.log k - Real.log epsilon) / Real.log 2) := by ring

end Main


section Final

open QAlgorithms.Papers.Independent.Support50.P16
open QAlgorithms.Papers.Independent.Information100.P04 (Measurement)

lemma modulus_nonneg (k : ℕ+) (epsilon : ℝ) (heps0 : 0 ≤ epsilon) (heps1 : epsilon ≤ 1 / Real.exp 1) :
    0 ≤ continuityModulus k epsilon := by
  unfold continuityModulus
  split_ifs with h
  · exact le_rfl
  · have hpos : 0 < epsilon := lt_of_le_of_ne heps0 (Ne.symm h)
    have hk : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast k.pos
    have hε1 : epsilon ≤ 1 := by
      have : 1 / Real.exp 1 ≤ 1 := by
        rw [div_le_one (Real.exp_pos 1)]
        have := Real.add_one_le_exp (1 : ℝ); linarith
      linarith
    have : 1 ≤ 6 * (k : ℝ) / epsilon := by
      rw [le_div_iff₀ hpos]; linarith
    have := Real.logb_nonneg (b := 2) (by norm_num) this
    positivity

theorem main_theorem (k : ℕ+)
    (G : Set (Matrix (Fin (k : ℕ)) (Fin (k : ℕ)) ℂ))
    (M : Set (Measurement (Fin (k : ℕ))))
    (hstates : ∀ sigma ∈ G, IsDensityMatrix sigma)
    (htau : QAlgorithms.Papers.Independent.Information100.P76.maximallyMixed k ∈ G)
    (hstar : ∀ sigma ∈ G, ∀ p : ℝ, 0 ≤ p → p ≤ 1 →
      (p : ℂ) • sigma + ((1-p : ℝ) : ℂ) •
        QAlgorithms.Papers.Independent.Information100.P76.maximallyMixed k ∈ G)
    (rho sigma : Matrix (Fin (k : ℕ)) (Fin (k : ℕ)) ℂ)
    (hrho : IsDensityMatrix rho) (hsigma : IsDensityMatrix sigma)
    (epsilon : ℝ) (heps0 : 0 ≤ epsilon)
    (hdistance : measurementDistance M rho sigma ≤ epsilon)
    (heps1 : epsilon ≤ 1 / Real.exp 1) :
    restrictedEntropy G M rho ≠ ⊤ ∧ restrictedEntropy G M sigma ≠ ⊤ ∧
    |(restrictedEntropy G M rho).toReal - (restrictedEntropy G M sigma).toReal| ≤
      continuityModulus k epsilon := by
  have hfin1 : restrictedEntropy G M rho ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top (rE_le_log k G M htau rho hrho)
  have hfin2 : restrictedEntropy G M sigma ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top (rE_le_log k G M htau sigma hsigma)
  refine ⟨hfin1, hfin2, ?_⟩
  -- the measured distance controls every test in M
  have hbound : ∀ T : M, ENNReal.ofReal (∑ x, |povmOutcomeLaw T.val rho x -
      povmOutcomeLaw T.val sigma x|) ≤ ENNReal.ofReal 2 := by
    intro T
    apply ENNReal.ofReal_le_ofReal
    calc ∑ x, |povmOutcomeLaw T.val rho x - povmOutcomeLaw T.val sigma x|
        ≤ ∑ x, (povmOutcomeLaw T.val rho x + povmOutcomeLaw T.val sigma x) := by
          apply Finset.sum_le_sum; intro x _
          calc |povmOutcomeLaw T.val rho x - povmOutcomeLaw T.val sigma x|
              ≤ |povmOutcomeLaw T.val rho x| + |povmOutcomeLaw T.val sigma x| := abs_sub _ _
            _ = _ := by
              rw [abs_of_nonneg (law_nonneg T.val hrho x), abs_of_nonneg (law_nonneg T.val hsigma x)]
      _ = 2 := by rw [Finset.sum_add_distrib, law_sum T.val hrho, law_sum T.val hsigma]; norm_num
  have hsup_ne : (⨆ T : M, ENNReal.ofReal (∑ x, |povmOutcomeLaw T.val rho x -
      povmOutcomeLaw T.val sigma x|)) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top (iSup_le hbound)
  have hdistT : ∀ T ∈ M, ∑ x, |povmOutcomeLaw T rho x - povmOutcomeLaw T sigma x| ≤ epsilon := by
    intro T hT
    unfold measurementDistance at hdistance
    have h1 : ENNReal.ofReal (∑ x, |povmOutcomeLaw T rho x - povmOutcomeLaw T sigma x|) ≤
        ⨆ T : M, ENNReal.ofReal (∑ x, |povmOutcomeLaw T.val rho x - povmOutcomeLaw T.val sigma x|) :=
      le_iSup (fun T : M => ENNReal.ofReal (∑ x, |povmOutcomeLaw T.val rho x -
        povmOutcomeLaw T.val sigma x|)) ⟨T, hT⟩
    have h2 := ENNReal.toReal_mono hsup_ne h1
    rw [ENNReal.toReal_ofReal (Finset.sum_nonneg fun x _ => abs_nonneg _)] at h2
    exact le_trans h2 hdistance
  by_cases heps : epsilon = 0
  · -- zero distance: the laws coincide on M
    subst heps
    have hlaw : ∀ T ∈ M, povmOutcomeLaw T rho = povmOutcomeLaw T sigma := by
      intro T hT
      have h := hdistT T hT
      have hzero : ∑ x, |povmOutcomeLaw T rho x - povmOutcomeLaw T sigma x| = 0 :=
        le_antisymm h (Finset.sum_nonneg fun x _ => abs_nonneg _)
      funext x
      have := (Finset.sum_eq_zero_iff_of_nonneg (fun x _ => abs_nonneg _)).mp hzero x
        (Finset.mem_univ x)
      exact sub_eq_zero.mp (abs_eq_zero.mp this)
    have heq : restrictedEntropy G M rho = restrictedEntropy G M sigma := by
      unfold restrictedEntropy
      exact iInf_congr fun omega => iSup_congr fun T => by rw [hlaw T.val T.2]
    rw [heq, sub_self, abs_zero]
    simp [continuityModulus]
  · have hpos : 0 < epsilon := lt_of_le_of_ne heps0 (Ne.symm heps)
    have heps1' : epsilon ≤ (Real.exp 1)⁻¹ := by rw [← one_div]; exact heps1
    have h1 := one_side k G M hstates hstar rho sigma hrho hsigma epsilon hpos heps1' hdistT
    have h2 := one_side k G M hstates hstar sigma rho hsigma hrho epsilon hpos heps1'
      (fun T hT => by
        rw [Finset.sum_congr rfl (fun x _ => abs_sub_comm _ _)]
        exact hdistT T hT)
    set C := (epsilon * (Real.log ((k : ℝ) / epsilon) + 1) + Real.negMulLog epsilon) /
        Real.log 2 + (-Real.logb 2 (1 - epsilon)) with hC
    have hCmod : C ≤ continuityModulus k epsilon := modulus_bound k epsilon hpos heps1
    have hmod0 : 0 ≤ continuityModulus k epsilon := modulus_nonneg k epsilon heps0 heps1
    have h1' : (restrictedEntropy G M rho).toReal ≤
        (restrictedEntropy G M sigma).toReal + max C 0 := by
      have := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hfin2, ENNReal.ofReal_ne_top⟩) h1
      rwa [ENNReal.toReal_add hfin2 ENNReal.ofReal_ne_top, ENNReal.toReal_ofReal'] at this
    have h2' : (restrictedEntropy G M sigma).toReal ≤
        (restrictedEntropy G M rho).toReal + max C 0 := by
      have := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hfin1, ENNReal.ofReal_ne_top⟩) h2
      rwa [ENNReal.toReal_add hfin1 ENNReal.ofReal_ne_top, ENNReal.toReal_ofReal'] at this
    have hmax : max C 0 ≤ continuityModulus k epsilon := max_le hCmod hmod0
    rw [abs_sub_le_iff]
    constructor <;> linarith

end Final

end H10

open QAlgorithms.Papers.Independent.Support50.P16

/-- Proposition 3 of Li--Winter: continuity of the restricted relative entropy. -/
theorem solution (k : ℕ+)
    (G : Set (Matrix (Fin (k : ℕ)) (Fin (k : ℕ)) ℂ))
    (M : Set (QAlgorithms.Papers.Independent.Information100.P04.Measurement (Fin (k : ℕ))))
    (hstates : ∀ sigma ∈ G, IsDensityMatrix sigma)
    (htau : QAlgorithms.Papers.Independent.Information100.P76.maximallyMixed k ∈ G)
    (hstar : ∀ sigma ∈ G, ∀ p : ℝ, 0 ≤ p → p ≤ 1 →
      (p : ℂ) • sigma + ((1-p : ℝ) : ℂ) •
        QAlgorithms.Papers.Independent.Information100.P76.maximallyMixed k ∈ G)
    (rho sigma : Matrix (Fin (k : ℕ)) (Fin (k : ℕ)) ℂ)
    (hrho : IsDensityMatrix rho) (hsigma : IsDensityMatrix sigma)
    (epsilon : ℝ) (heps0 : 0 ≤ epsilon)
    (hdistance : measurementDistance M rho sigma ≤ epsilon)
    (heps1 : epsilon ≤ 1 / Real.exp 1) :
    restrictedEntropy G M rho ≠ ⊤ ∧ restrictedEntropy G M sigma ≠ ⊤ ∧
    |(restrictedEntropy G M rho).toReal - (restrictedEntropy G M sigma).toReal| ≤
      continuityModulus k epsilon :=
  H10.main_theorem k G M hstates htau hstar rho sigma hrho hsigma epsilon heps0 hdistance heps1
