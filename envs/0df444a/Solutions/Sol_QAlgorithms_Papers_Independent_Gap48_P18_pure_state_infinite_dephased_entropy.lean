-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Gap48.P18.pure_state_infinite_dephased_entropy
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T18:34:29.239538+00:00
-- url     : https://prove2.me/submissions/32ddfdd2-ec33-48c6-aaea-c8931fed78ff

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P18

/-! A summable nonnegative sequence with divergent Shannon entropy. -/

noncomputable section
open Finset Filter

namespace X6G18

/-- block weights -/
def w (k : ℕ) : ℝ := 1 / (((k : ℝ) + 1) * ((k : ℝ) + 2))

/-- dyadic-block distribution: on block `k` (`2^k ≤ n+1 < 2^(k+1)`) the value is `w k / 2^k`. -/
def q (n : ℕ) : ℝ := w (Nat.log 2 (n + 1)) / 2 ^ (Nat.log 2 (n + 1))

lemma w_pos (k : ℕ) : 0 < w k := by unfold w; positivity

lemma w_le_one (k : ℕ) : w k ≤ 1 := by
  unfold w
  rw [div_le_one (by positivity)]
  nlinarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]

lemma q_pos (n : ℕ) : 0 < q n := by unfold q; have := w_pos (Nat.log 2 (n+1)); positivity

lemma log_block {k n : ℕ} (h1 : 2 ^ k - 1 ≤ n) (h2 : n < 2 ^ (k + 1) - 1) :
    Nat.log 2 (n + 1) = k := by
  have a : 1 ≤ 2 ^ k := Nat.one_le_two_pow
  have b : 1 ≤ 2 ^ (k+1) := Nat.one_le_two_pow
  rw [Nat.log_eq_iff (Or.inr ⟨by norm_num, by omega⟩)]
  omega

lemma block_sum (F : ℕ → ℝ) (K : ℕ) :
    ∑ n ∈ range (2 ^ K - 1), F (Nat.log 2 (n + 1)) = ∑ k ∈ range K, (2 : ℝ) ^ k * F k := by
  induction K with
  | zero => simp
  | succ K ih =>
    have a : 2 ^ K - 1 ≤ 2 ^ (K + 1) - 1 := by
      have := Nat.pow_le_pow_right (by norm_num : 0 < 2) (Nat.le_succ K); omega
    rw [← Finset.sum_range_add_sum_Ico _ a, ih, Finset.sum_range_succ]
    congr 1
    rw [Finset.sum_congr rfl (g := fun _ => F K) (fun n hn => by
      rw [Finset.mem_Ico] at hn
      simp only [log_block hn.1 hn.2])]
    rw [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul]
    congr 1
    have : 2 ^ (K + 1) - 1 - (2 ^ K - 1) = 2 ^ K := by
      have := Nat.one_le_two_pow (n := K); rw [pow_succ]; omega
    rw [this]; push_cast; ring

lemma w_sum (K : ℕ) : ∑ k ∈ range K, w k = 1 - 1 / ((K : ℝ) + 1) := by
  induction K with
  | zero => simp
  | succ K ih =>
    rw [Finset.sum_range_succ, ih]; unfold w; push_cast
    field_simp; ring

lemma q_partial (N : ℕ) : ∑ n ∈ range N, q n ≤ 1 := by
  have hN : N ≤ 2 ^ N - 1 := by
    have := Nat.lt_two_pow_self (n := N); omega
  calc ∑ n ∈ range N, q n ≤ ∑ n ∈ range (2 ^ N - 1), q n :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.2 hN)
          (fun i _ _ => (q_pos i).le)
    _ = ∑ k ∈ range N, (2 : ℝ) ^ k * (w k / 2 ^ k) := block_sum (fun k => w k / 2 ^ k) N
    _ = ∑ k ∈ range N, w k := by
        apply Finset.sum_congr rfl; intro k _; field_simp
    _ ≤ 1 := by rw [w_sum]; have : (0 : ℝ) ≤ 1 / ((N : ℝ) + 1) := by positivity
                linarith

lemma q_summable : Summable q := summable_of_sum_range_le (fun n => (q_pos n).le) q_partial

lemma ent_block (K : ℕ) :
    ((Real.log 2) * (∑ k ∈ range K, 1 / ((k : ℝ) + 1)) - 2 * Real.log 2)
      ≤ ∑ n ∈ range (2 ^ K - 1), -(q n * Real.log (q n)) := by
  have e : ∑ n ∈ range (2 ^ K - 1), -(q n * Real.log (q n)) =
      ∑ k ∈ range K, (2 : ℝ) ^ k * (-((w k / 2 ^ k) * Real.log (w k / 2 ^ k))) :=
    block_sum (fun k => -((w k / 2 ^ k) * Real.log (w k / 2 ^ k))) K
  rw [e]
  have term : ∀ k ∈ range K, Real.log 2 * (2 / ((k : ℝ) + 2) - 1 / ((k : ℝ) + 1)) ≤
      (2 : ℝ) ^ k * (-((w k / 2 ^ k) * Real.log (w k / 2 ^ k))) := by
    intro k _
    have hw := w_pos k
    have h2 : (0 : ℝ) < 2 ^ k := by positivity
    have hl : Real.log (w k / 2 ^ k) = Real.log (w k) - k * Real.log 2 := by
      rw [Real.log_div hw.ne' h2.ne', Real.log_pow]
    have hlw : Real.log (w k) ≤ 0 := Real.log_nonpos hw.le (w_le_one k)
    have : (2 : ℝ) ^ k * (-((w k / 2 ^ k) * Real.log (w k / 2 ^ k))) =
        w k * (k * Real.log 2 - Real.log (w k)) := by
      rw [hl]; field_simp; ring
    rw [this]
    have e2 : 2 / ((k : ℝ) + 2) - 1 / ((k : ℝ) + 1) = w k * k := by
      unfold w; field_simp; ring
    rw [e2]
    have := mul_nonneg hw.le (neg_nonneg.2 hlw)
    nlinarith
  calc (Real.log 2) * (∑ k ∈ range K, 1 / ((k : ℝ) + 1)) - 2 * Real.log 2
      ≤ ∑ k ∈ range K, Real.log 2 * (2 / ((k : ℝ) + 2) - 1 / ((k : ℝ) + 1)) := by
        rw [← Finset.mul_sum, Finset.sum_sub_distrib]
        have h : ∀ M : ℕ, ∑ k ∈ range M, 2 / ((k : ℝ) + 2) =
            2 * ∑ k ∈ range M, 1 / ((k : ℝ) + 1) - 2 + 2 / ((M : ℝ) + 1) := by
          intro M
          induction M with
          | zero => simp
          | succ M ih =>
            rw [Finset.sum_range_succ, ih, Finset.sum_range_succ]; push_cast
            field_simp; ring
        rw [h]
        have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
        have : (0 : ℝ) ≤ 2 / ((K : ℝ) + 1) := by positivity
        nlinarith
    _ ≤ _ := Finset.sum_le_sum term

/-- the entropy partial sums are unbounded -/
lemma ent_unbounded (B : ℝ) : ∃ N, B ≤ ∑ n ∈ range N, -(q n * Real.log (q n)) := by
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  obtain ⟨K, hK⟩ := (Real.tendsto_sum_range_one_div_nat_succ_atTop.eventually
    (eventually_ge_atTop ((B + 2 * Real.log 2) / Real.log 2))).exists
  refine ⟨2 ^ K - 1, le_trans ?_ (ent_block K)⟩
  rw [div_le_iff₀ hl2] at hK
  nlinarith

end X6G18


noncomputable section
open Finset Filter
open scoped ENNReal

namespace X6G18

open QAlgorithms.Papers.Independent.Dependency50.P33
  (State PureState IsDensity IsTraceClass NuclearExpansion rankOne)
open QAlgorithms.Papers.Independent.Frontier18.P07 (extendedEntropyNats finiteEntropy)

lemma trace_mul_cfc {ι : Type*} [Fintype ι] [DecidableEq ι] {A : Matrix ι ι ℂ}
    (hA : A.IsHermitian) (f : ℝ → ℝ) :
    (A * cfc f A).trace = ∑ i, ((hA.eigenvalues i * f (hA.eigenvalues i) : ℝ) : ℂ) := by
  have h1 : A = cfc (fun x : ℝ => x) A := (cfc_id' ℝ A hA.isSelfAdjoint).symm
  calc (A * cfc f A).trace = (cfc (fun x : ℝ => x) A * cfc f A).trace := by
        conv_lhs => arg 1; arg 1; rw [h1]
    _ = _ := by
      rw [hA.cfc_eq, hA.cfc_eq, Matrix.IsHermitian.cfc, Matrix.IsHermitian.cfc, ← map_mul,
        Matrix.diagonal_mul_diagonal, Unitary.conjStarAlgAut_apply, Matrix.trace_mul_cycle,
        Unitary.star_mul_self_of_mem (hA.eigenvectorUnitary).2, one_mul, Matrix.trace_diagonal]
      apply Finset.sum_congr rfl; intro i _
      simp [Function.comp_apply]

lemma diag_herm {ι : Type*} [Fintype ι] [DecidableEq ι] (v : ι → ℝ) :
    (Matrix.diagonal (fun i => (v i : ℂ))).IsHermitian := by
  rw [Matrix.IsHermitian, Matrix.diagonal_conjTranspose]; congr 1; ext i; simp

lemma sum_eig {ι : Type*} [Fintype ι] [DecidableEq ι] (v : ι → ℝ) (F : ℝ → ℝ) :
    ∑ i, F ((diag_herm v).eigenvalues i) = ∑ i, F (v i) := by
  have hA := diag_herm v
  have h1 := hA.roots_charpoly_eq_eigenvalues
  rw [Matrix.charpoly_diagonal, Polynomial.roots_prod _ _ (by
    simp [Finset.prod_ne_zero_iff, Polynomial.X_sub_C_ne_zero])] at h1
  simp only [Polynomial.roots_X_sub_C] at h1
  have h2 := congrArg (fun s : Multiset ℂ => (s.map (fun z => F z.re)).sum) h1
  simp only [Multiset.map_map, Function.comp_def, Complex.ofReal_re] at h2
  rw [Finset.sum_eq_multiset_sum, Finset.sum_eq_multiset_sum]
  have e : (Finset.univ.val.bind fun i => ({(v i : ℂ)} : Multiset ℂ)) =
      Finset.univ.val.map (fun i => (v i : ℂ)) := by
    simp [Multiset.bind_singleton]
  simp only [e, Multiset.map_map, Function.comp_def, Complex.ofReal_re] at h2
  exact h2.symm

lemma finiteEntropy_diag {ι : Type} [Fintype ι] [DecidableEq ι] (v : ι → ℝ) :
    finiteEntropy (Matrix.diagonal (fun i => (v i : ℂ))) =
      ENNReal.ofReal ((∑ i : ι, v i) * Real.log (∑ i : ι, v i) - ∑ i : ι, v i * Real.log (v i)) := by
  unfold finiteEntropy
  rw [trace_mul_cfc (diag_herm v), Matrix.trace_diagonal, Complex.re_sum, Complex.re_sum]
  simp only [Complex.ofReal_re]
  rw [sum_eig v (fun x => x * Real.log x)]

lemma mul_log_ge (x : ℝ) (hx : 0 ≤ x) : x - 1 ≤ x * Real.log x := by
  rcases hx.eq_or_lt with rfl | hx
  · simp
  · have := Real.one_sub_inv_le_log_of_pos hx
    have e : x * (1 - x⁻¹) = x - 1 := by field_simp
    nlinarith [mul_le_mul_of_nonneg_left this hx.le]

end X6G18

open QAlgorithms.Papers.Independent.Dependency50.P33
  (State PureState IsDensity IsTraceClass NuclearExpansion rankOne)
open QAlgorithms.Papers.Independent.Frontier18.P07 (extendedEntropyNats finiteEntropy)
attribute [local instance] Classical.propDecidable Classical.decEq

open X6G18 in
theorem solution {I : Type} [Countable I] [Infinite I] :
    ∃ rho : PureState I, extendedEntropyNats
      (Matrix.diagonal (Matrix.diag rho.val.coefficients)) = ⊤ := by
  classical
  set e := Infinite.natEmbedding I
  set c : ℝ := ∑' n, q n with hc
  have hcpos : 0 < c := q_summable.tsum_pos (fun n => (q_pos n).le) 0 (q_pos 0)
  set p : ℕ → ℝ := fun n => q n / c with hp
  have hp0 : ∀ n, 0 ≤ p n := fun n => div_nonneg (q_pos n).le hcpos.le
  have hpsum : Summable p := q_summable.div_const c
  have hptsum : ∑' n, p n = 1 := by
    rw [hp]; simp only; rw [tsum_div_const, ← hc, div_self hcpos.ne']
  set f : I → ℝ := Function.extend e p 0 with hf
  have hfe : ∀ n, f (e n) = p n := fun n => e.injective.extend_apply p 0 n
  have hf0 : ∀ i, i ∉ Set.range e → f i = 0 := by
    intro i hi; rw [hf, Function.extend_apply' _ _ _ (by simpa using hi)]; rfl
  have hfnn : ∀ i, 0 ≤ f i := by
    intro i
    by_cases hi : i ∈ Set.range e
    · obtain ⟨n, rfl⟩ := hi; rw [hfe]; exact hp0 n
    · rw [hf0 i hi]
  have hfsum : Summable f := (e.injective.summable_iff hf0).1 (by
    have : f ∘ e = p := funext hfe
    rw [this]; exact hpsum)
  have hftsum : ∑' i, f i = 1 := by
    rw [← e.injective.tsum_eq (f := f) (by
      intro i hi; by_contra h; exact hi (hf0 i h))]
    simp only [hfe]; exact hptsum
  set uf : I → ℂ := fun i => ((Real.sqrt (f i) : ℝ) : ℂ) with huf
  have hunorm : ∀ i, ‖uf i‖ ^ 2 = f i := by
    intro i; simp only [huf, Complex.norm_real, Real.norm_eq_abs, sq_abs]
    exact Real.sq_sqrt (hfnn i)
  have hustar : ∀ i, uf i * star (uf i) = ((f i : ℝ) : ℂ) := by
    intro i
    simp only [huf, Complex.star_def, Complex.conj_ofReal]
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (hfnn i)]
  have hmem : Memℓp uf 2 := by
    rw [memℓp_gen_iff (by norm_num)]
    simp only [ENNReal.toReal_ofNat, Real.rpow_two, hunorm]
    exact hfsum
  set u : QAlgorithms.RealRegisters.Hilbert I := ⟨uf, hmem⟩
  have hu_apply : ∀ i, (u : I → ℂ) i = uf i := fun i => rfl
  have hnorm : ‖u‖ = 1 := by
    rw [lp.norm_eq_tsum_rpow (by norm_num)]
    simp only [ENNReal.toReal_ofNat, Real.rpow_two, hu_apply, hunorm, hftsum]
    simp
  -- density
  have hdens : IsDensity (rankOne u) := by
    refine ⟨⟨NuclearExpansion.mk (fun n => if n = 0 then u else 0)
      (fun n => if n = 0 then u else 0) ?_ ?_⟩, ?_, ?_, ?_⟩
    · apply summable_of_ne_finset_zero (s := {0})
      intro n hn
      simp only [Finset.mem_singleton] at hn
      simp [hn]
    · intro i j
      rw [tsum_eq_single 0 (fun n hn => by simp [hn])]
      simp [rankOne]
    · intro s z
      have : ∑ i ∈ s, ∑ j ∈ s, star (z i) * rankOne u i j * z j =
          (∑ i ∈ s, star (z i) * uf i) * star (∑ i ∈ s, star (z i) * uf i) := by
        rw [star_sum, Finset.sum_mul_sum]
        apply Finset.sum_congr rfl; intro i _
        apply Finset.sum_congr rfl; intro j _
        simp only [rankOne, hu_apply, star_mul, star_star]
        ring
      rw [this, Complex.star_def, Complex.mul_conj]
      exact ⟨Complex.ofReal_im _, by rw [Complex.ofReal_re]; exact Complex.normSq_nonneg _⟩
    · have : (fun i => (rankOne u i i).re) = f := by
        funext i; simp only [rankOne, hu_apply, hustar, Complex.ofReal_re]
      rw [this]; exact hfsum
    · have : (fun i => (rankOne u i i).re) = f := by
        funext i; simp only [rankOne, hu_apply, hustar, Complex.ofReal_re]
      rw [this]; exact hftsum
  refine ⟨⟨⟨rankOne u, hdens⟩, u, hnorm, rfl⟩, ?_⟩
  have hdiag : Matrix.diag (rankOne u) = fun i => ((f i : ℝ) : ℂ) := by
    funext i; simp only [Matrix.diag, rankOne, hu_apply, hustar]
  show extendedEntropyNats (Matrix.diagonal (Matrix.diag (rankOne u))) = ⊤
  rw [hdiag]
  unfold extendedEntropyNats
  rw [iSup_eq_top]
  intro b hb
  -- choose N with large entropy
  have hlogc := abs_nonneg (Real.log c)
  obtain ⟨N, hN⟩ := ent_unbounded (c * (b.toReal + 3 + |Real.log c|))
  refine ⟨(range N).map e, ?_⟩
  rw [Matrix.submatrix_diagonal _ _ Subtype.val_injective, Function.comp_def]
  rw [finiteEntropy_diag (fun i : ((range N).map e) => f i.val)]
  have hsum : ∀ F : ℝ → ℝ, ∑ i : ((range N).map e), F (f i.val) = ∑ n ∈ range N, F (p n) := by
    intro F
    rw [Finset.sum_coe_sort ((range N).map e) (fun i => F (f i)), Finset.sum_map]
    simp only [hfe]
  rw [hsum (fun x => x), hsum (fun x => x * Real.log x)]
  set T := ∑ n ∈ range N, p n
  have hT : 0 ≤ T := Finset.sum_nonneg (fun n _ => hp0 n)
  have hTlog := mul_log_ge T hT
  have hTle : T ≤ 1 := by
    rw [← hptsum]; exact hpsum.sum_le_tsum _ (fun n _ => hp0 n)
  -- entropy of p in terms of q
  have hent : ∑ n ∈ range N, p n * Real.log (p n) =
      (∑ n ∈ range N, q n * Real.log (q n)) / c - Real.log c * T := by
    simp only [T, hp, Finset.mul_sum, Finset.sum_div, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl; intro n _
    rw [Real.log_div (q_pos n).ne' hcpos.ne']
    field_simp
  rw [hent]
  have hneg : ∑ n ∈ range N, -(q n * Real.log (q n)) = -∑ n ∈ range N, q n * Real.log (q n) := by
    rw [Finset.sum_neg_distrib]
  rw [hneg] at hN
  have key : b.toReal + 1 < T * Real.log T -
      ((∑ n ∈ range N, q n * Real.log (q n)) / c - Real.log c * T) := by
    have h1 : -(∑ n ∈ range N, q n * Real.log (q n)) / c ≥ b.toReal + 3 + |Real.log c| := by
      rw [ge_iff_le, le_div_iff₀ hcpos]; linarith
    have h2 : -|Real.log c| ≤ Real.log c * T := by
      have := neg_abs_le (Real.log c)
      rcases le_or_gt 0 (Real.log c) with h | h
      · nlinarith
      · rw [abs_of_neg h]; nlinarith
    have h3 : (∑ n ∈ range N, q n * Real.log (q n)) / c =
        -(-(∑ n ∈ range N, q n * Real.log (q n)) / c) := by ring
    rw [h3]; linarith
  calc b ≤ ENNReal.ofReal b.toReal := ENNReal.le_ofReal_iff_toReal_le hb.ne (by positivity) |>.2 le_rfl
    _ < _ := by
      rw [ENNReal.ofReal_lt_ofReal_iff_of_nonneg ENNReal.toReal_nonneg]
      linarith
