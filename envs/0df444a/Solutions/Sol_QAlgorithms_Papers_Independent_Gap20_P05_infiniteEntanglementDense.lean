-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Gap20.P05.infiniteEntanglementDense
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T05:10:06.566518+00:00
-- url     : https://prove2.me/submissions/8af3bba3-3a21-428d-abed-f4a599979fad

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Gap20_P05
noncomputable section

open Filter

open scoped ENNReal BigOperators Topology

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Gap20.P05
open QAlgorithms.RealRegisters (Hilbert)

open QAlgorithms.Papers.Independent.Dependency50.P33
  (State PureState IsDensity rankOne traceSize traceClosure IsSeparable)

open QAlgorithms.Papers.Independent.Frontier18.P01
  (generalizedRelativeEntropy traceSecond)

open QAlgorithms.Entanglement (partialTransposeFirst)

open QAlgorithms.Papers.Independent.Dependency50.P07 (bipartitePower)

open QAlgorithms.Papers.Independent.Information100.P63 (tensorPower)

open QAlgorithms.Papers.Independent.Gap48.P26 (entropyBits)

open QAlgorithms.Papers.Independent.Frontier18.P07 (extendedEntropyNats finiteEntropy)


lemma s199i_cfc_trace {n : Type*} [Fintype n] [DecidableEq n] {Y : Matrix n n ℂ} (hY : Y.IsHermitian)
    (f : ℝ → ℝ) : (cfc f Y).trace = ∑ i, ((f (hY.eigenvalues i) : ℝ) : ℂ) := by
  rw [hY.cfc_eq f, Matrix.IsHermitian.cfc, Unitary.conjStarAlgAut_apply, Matrix.trace_mul_cycle,
    Unitary.star_mul_self_of_mem hY.eigenvectorUnitary.2, one_mul, Matrix.trace_diagonal]
  rfl

lemma s199i_diag_herm {n : Type*} [Fintype n] [DecidableEq n] (d : n → ℝ) :
    (Matrix.diagonal (fun i => (d i : ℂ))).IsHermitian := by
  rw [Matrix.IsHermitian, Matrix.diagonal_conjTranspose]
  congr 1; funext i; simp

lemma s199i_trace_cfc_diag {n : Type*} [Fintype n] [DecidableEq n] (d : n → ℝ) (f : ℝ → ℝ) :
    (cfc f (Matrix.diagonal (fun i => (d i : ℂ)))).trace = ∑ i, ((f (d i) : ℝ) : ℂ) := by
  have hD := s199i_diag_herm d
  rw [s199i_cfc_trace hD]
  have h1 := hD.roots_charpoly_eq_eigenvalues
  rw [Matrix.charpoly_diagonal, Polynomial.roots_prod _ _ (by
    simp [Finset.prod_ne_zero_iff, Polynomial.X_sub_C_ne_zero])] at h1
  simp only [Polynomial.roots_X_sub_C] at h1
  have h2 : Multiset.map (fun i => (d i : ℂ)) Finset.univ.val =
      Multiset.map (fun i => ((hD.eigenvalues i : ℝ) : ℂ)) Finset.univ.val := by
    have := h1
    rw [Multiset.bind_singleton] at this
    exact this
  have h3 := congrArg (fun m => (Multiset.map (fun z : ℂ => ((f z.re : ℝ) : ℂ)) m).sum) h2
  simp only [Multiset.map_map, Function.comp_def, Complex.ofReal_re] at h3
  exact h3.symm

lemma s199i_finEnt_diag {n : Type} [Fintype n] [DecidableEq n] (d : n → ℝ) :
    finiteEntropy (Matrix.diagonal (fun i => (d i : ℂ))) =
      ENNReal.ofReal ((∑ i, d i) * Real.log (∑ i, d i) - ∑ i, d i * Real.log (d i)) := by
  unfold finiteEntropy
  have hsa : IsSelfAdjoint (Matrix.diagonal (fun i => (d i : ℂ))) := s199i_diag_herm d
  have hfin := (Matrix.diagonal (fun i => (d i : ℂ))).finite_real_spectrum
  have hmul : Matrix.diagonal (fun i => (d i : ℂ)) * cfc Real.log (Matrix.diagonal (fun i => (d i : ℂ)))
      = cfc (fun x => x * Real.log x) (Matrix.diagonal (fun i => (d i : ℂ))) := by
    rw [cfc_mul (fun x => x) Real.log _ (hfin.continuousOn _) (hfin.continuousOn _), cfc_id' ℝ _]
  rw [hmul, s199i_trace_cfc_diag, Matrix.trace_diagonal]
  congr 1
  simp only [Complex.re_sum, Complex.ofReal_re]

open QAlgorithms.Papers.Independent.Dependency50.P33 (NuclearExpansion)

def s199i_exp2 {I : Type} (X : Matrix I I ℂ) (u v u' v' : Hilbert I)
    (hX : ∀ i j, X i j = u i * star (v j) + u' i * star (v' j)) : NuclearExpansion X where
  left n := if n = 0 then u else if n = 1 then u' else 0
  right n := if n = 0 then v else if n = 1 then v' else 0
  summable := by
    apply summable_of_ne_finset_zero (s := Finset.range 2)
    intro n hn
    simp only [Finset.mem_range, not_lt] at hn
    have h0 : n ≠ 0 := by omega
    have h1 : n ≠ 1 := by omega
    simp [h0, h1]
  coefficients i j := by
    rw [hX, tsum_eq_sum (s := Finset.range 2)]
    · simp [Finset.sum_range_succ]
    · intro n hn
      simp only [Finset.mem_range, not_lt] at hn
      have h0 : n ≠ 0 := by omega
      have h1 : n ≠ 1 := by omega
      simp [h0, h1]

theorem s199i_ts2 {I : Type} (X : Matrix I I ℂ) (u v u' v' : Hilbert I)
    (hX : ∀ i j, X i j = u i * star (v j) + u' i * star (v' j)) :
    traceSize X ≤ ENNReal.ofReal (‖u‖ * ‖v‖ + ‖u'‖ * ‖v'‖) := by
  refine (iInf_le _ (s199i_exp2 X u v u' v' hX)).trans (le_of_eq ?_)
  congr 1
  rw [tsum_eq_sum (s := Finset.range 2)]
  · simp [s199i_exp2, Finset.sum_range_succ]
  · intro n hn
    simp only [Finset.mem_range, not_lt] at hn
    have h0 : n ≠ 0 := by omega
    have h1 : n ≠ 1 := by omega
    simp [s199i_exp2, h0, h1]



lemma s199i_traceSecond (v : Hilbert (ℕ × ℕ)) (c : ℕ → ℂ) (i j : ℕ)
    (hi : ∀ r, v (i, r) = if i = r then c i else 0)
    (hj : ∀ r, v (j, r) = if j = r then c j else 0) :
    traceSecond (rankOne v) i j = if i = j then ((‖c i‖ ^ 2 : ℝ) : ℂ) else 0 := by
  unfold traceSecond rankOne
  simp only [hi, hj]
  have e : ∀ r : ℕ, ((if i = r then c i else 0) * star (if j = r then c j else 0)) =
      if r = i then c i * star (if j = i then c j else 0) else 0 := by
    intro r
    by_cases h : r = i
    · subst h; simp
    · simp [Ne.symm h, h]
  simp only [e, tsum_ite_eq]
  by_cases h : i = j
  · subst h
    simp only [if_true]
    rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  · simp [h, Ne.symm h]

/-- block sizes -/
def s199i_M (m : ℕ) : ℕ := 2 ^ (2 ^ (m + 1))

def s199i_q (p : ℕ × ℕ) : ℝ :=
  if p.2 < s199i_M p.1 then (1 / 2 : ℝ) ^ (p.1 + 1) / (s199i_M p.1 : ℝ) else 0

lemma s199i_M_pos (m : ℕ) : (0 : ℝ) < (s199i_M m : ℝ) := by
  unfold s199i_M; positivity

lemma s199i_q_nonneg (p : ℕ × ℕ) : 0 ≤ s199i_q p := by
  unfold s199i_q; split_ifs <;> positivity

lemma s199i_q_le (p : ℕ × ℕ) : s199i_q p ≤ 1 := by
  unfold s199i_q
  split_ifs
  · have h1 : (1 : ℝ) ≤ (s199i_M p.1 : ℝ) := by
      unfold s199i_M; exact_mod_cast Nat.one_le_two_pow
    have h2 : (1 / 2 : ℝ) ^ (p.1 + 1) ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    rw [div_le_one (by linarith)]; linarith
  · norm_num

lemma s199i_q_row (m : ℕ) : HasSum (fun j => s199i_q (m, j)) ((1 / 2 : ℝ) ^ (m + 1)) := by
  have : (1 / 2 : ℝ) ^ (m + 1) = ∑ j ∈ Finset.range (s199i_M m), s199i_q (m, j) := by
    unfold s199i_q
    simp only
    rw [Finset.sum_congr rfl (fun j hj => if_pos (Finset.mem_range.1 hj)), Finset.sum_const,
      Finset.card_range, nsmul_eq_mul]
    field_simp [(s199i_M_pos m).ne']
  rw [this]
  apply hasSum_sum_of_ne_finset_zero
  intro j hj
  unfold s199i_q
  rw [if_neg (by simpa using hj)]

lemma s199i_q_hasSum : HasSum s199i_q 1 := by
  have hs : Summable s199i_q := by
    rw [summable_prod_of_nonneg (fun p => s199i_q_nonneg p)]
    refine ⟨fun m => (s199i_q_row m).summable, ?_⟩
    simp only [fun m => (s199i_q_row m).tsum_eq]
    exact (summable_geometric_two).mul_left (1 / 2) |>.congr (fun m => by ring)
  have := hs.hasSum
  rw [hs.tsum_prod' (fun m => (s199i_q_row m).summable)] at this
  simp only [fun m => (s199i_q_row m).tsum_eq] at this
  convert this using 1
  rw [show (fun m : ℕ => (1 / 2 : ℝ) ^ (m + 1)) = fun m => (1 / 2) * (1 / 2) ^ m from
    funext fun m => by ring, tsum_mul_left, tsum_geometric_two]
  norm_num

/-- coefficient of the high-entropy vector -/
def s199i_c (N : ℕ) (i : ℕ) : ℂ :=
  if N ≤ i then ((Real.sqrt (s199i_q (Nat.unpair (i - N))) : ℝ) : ℂ) else 0

lemma s199i_c_norm (N i : ℕ) :
    ‖s199i_c N i‖ ^ 2 = if N ≤ i then s199i_q (Nat.unpair (i - N)) else 0 := by
  unfold s199i_c
  split_ifs
  · rw [Complex.norm_real, Real.norm_eq_abs, sq_abs, Real.sq_sqrt (s199i_q_nonneg _)]
  · simp

lemma s199i_F_hasSum (N : ℕ) :
    HasSum (fun i => ‖s199i_c N i‖ ^ 2) 1 := by
  simp only [s199i_c_norm]
  rw [← hasSum_nat_add_iff' N]
  have h0 : ∑ i ∈ Finset.range N, (if N ≤ i then s199i_q (Nat.unpair (i - N)) else 0) = 0 :=
    Finset.sum_eq_zero (fun i hi => if_neg (by simpa using hi))
  rw [h0, sub_zero]
  simp only [show ∀ n, N ≤ n + N from fun n => Nat.le_add_left N n, if_true, Nat.add_sub_cancel]
  exact (Nat.pairEquiv.symm.hasSum_iff (f := s199i_q)).2 s199i_q_hasSum

def s199i_chif (N : ℕ) (x : ℕ × ℕ) : ℂ := if x.1 = x.2 then s199i_c N x.1 else 0

lemma s199i_chif_hasSum (N : ℕ) : HasSum (fun x => ‖s199i_chif N x‖ ^ 2) 1 := by
  have hinj : Function.Injective (fun i : ℕ => (i, i)) := fun a b h => (Prod.ext_iff.1 h).1
  rw [← hinj.hasSum_iff]
  · convert s199i_F_hasSum N using 1
    funext i; simp [s199i_chif]
  · intro x hx
    obtain ⟨i, r⟩ := x
    have : i ≠ r := by rintro rfl; exact hx ⟨i, rfl⟩
    simp [s199i_chif, this]

lemma s199i_chi_mem (N : ℕ) : Memℓp (s199i_chif N) 2 := by
  apply memℓp_gen
  have h2 : ((2 : ℝ≥0∞).toReal) = (2 : ℕ) := by norm_num
  rw [h2]
  simp only [Real.rpow_natCast]
  exact (s199i_chif_hasSum N).summable

def s199i_chi (N : ℕ) : Hilbert (ℕ × ℕ) := ⟨s199i_chif N, s199i_chi_mem N⟩

lemma s199i_chi_apply (N : ℕ) (x : ℕ × ℕ) : s199i_chi N x = s199i_chif N x := rfl

lemma s199i_chi_norm (N : ℕ) : ‖s199i_chi N‖ = 1 := by
  have h := lp.norm_rpow_eq_tsum (p := 2) (by norm_num) (s199i_chi N)
  have h2 : ((2 : ℝ≥0∞).toReal) = (2 : ℕ) := by norm_num
  rw [h2] at h
  simp only [Real.rpow_natCast] at h
  simp only [s199i_chi_apply] at h
  rw [(s199i_chif_hasSum N).tsum_eq] at h
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 h

lemma s199i_block_ineq (x M : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hM : 0 < M) :
    x * Real.log M ≤ M * Real.negMulLog (x / M) := by
  rcases hx0.eq_or_lt with h | h
  · subst h; simp
  · have hn := Real.negMulLog_nonneg hx0 hx1
    unfold Real.negMulLog at hn ⊢
    rw [Real.log_div h.ne' hM.ne']
    field_simp
    nlinarith

lemma s199i_block_sum (η : ℝ) (hη0 : 0 < η) (hη1 : η ≤ 1) (m : ℕ) :
    η * Real.log 2 ≤ ∑ j ∈ Finset.range (s199i_M m), Real.negMulLog (η * s199i_q (m, j)) := by
  have e : ∀ j ∈ Finset.range (s199i_M m), Real.negMulLog (η * s199i_q (m, j)) =
      Real.negMulLog ((η * (1 / 2 : ℝ) ^ (m + 1)) / (s199i_M m : ℝ)) := by
    intro j hj
    unfold s199i_q
    simp only
    rw [if_pos (Finset.mem_range.1 hj), mul_div_assoc]
  rw [Finset.sum_congr rfl e, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hw0 : 0 ≤ η * (1 / 2 : ℝ) ^ (m + 1) := by positivity
  have hw1 : η * (1 / 2 : ℝ) ^ (m + 1) ≤ 1 := by
    have : (1 / 2 : ℝ) ^ (m + 1) ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    nlinarith
  refine le_trans (le_of_eq ?_) (s199i_block_ineq _ _ hw0 hw1 (s199i_M_pos m))
  unfold s199i_M
  push_cast
  rw [Real.log_pow]
  push_cast
  have : (1 / 2 : ℝ) ^ (m + 1) * 2 ^ (m + 1) = 1 := by rw [← mul_pow]; norm_num
  linear_combination (-(η * Real.log 2)) * this

lemma s199i_entropy_top (X : Matrix ℕ ℕ ℂ) (N : ℕ) (η : ℝ) (hη0 : 0 < η) (hη1 : η ≤ 1)
    (hX : ∀ i j, N ≤ i → N ≤ j →
      X i j = if i = j then ((η * s199i_q (Nat.unpair (i - N)) : ℝ) : ℂ) else 0) :
    entropyBits X = ⊤ := by
  unfold entropyBits
  have hE : QAlgorithms.Papers.Independent.Frontier18.P07.extendedEntropyNats X = ⊤ := by
    apply ENNReal.eq_top_of_forall_nnreal_le
    intro r
    have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    obtain ⟨K, hK⟩ := exists_nat_gt (((r : ℝ) + 1) / (η * Real.log 2))
    rw [div_lt_iff₀ (by positivity)] at hK
    let T : Finset (Σ _ : ℕ, ℕ) := (Finset.range K).sigma (fun m => Finset.range (s199i_M m))
    let s : Finset ℕ := T.image (fun p => N + Nat.pair p.1 p.2)
    unfold QAlgorithms.Papers.Independent.Frontier18.P07.extendedEntropyNats
    refine le_trans ?_ (le_iSup _ s)
    have hsN : ∀ i ∈ s, N ≤ i := by
      intro i hi
      obtain ⟨p, _, rfl⟩ := Finset.mem_image.1 hi
      omega
    let d : ℕ → ℝ := fun i => η * s199i_q (Nat.unpair (i - N))
    have hsub : X.submatrix (fun i : s => i.val) (fun i : s => i.val) =
        Matrix.diagonal (fun i : s => (d i.val : ℂ)) := by
      ext a b
      rw [Matrix.submatrix_apply, Matrix.diagonal_apply, hX _ _ (hsN _ a.2) (hsN _ b.2)]
      simp only [Subtype.ext_iff, d]
    rw [hsub]
    refine le_trans ?_ (le_of_eq (Eq.symm (?_ : _ = ENNReal.ofReal ((∑ i : s, d i.val) *
      Real.log (∑ i : s, d i.val) - ∑ i : s, d i.val * Real.log (d i.val)))))
    swap
    · convert s199i_finEnt_diag (fun i : s => d i.val) using 2
    rw [Finset.sum_coe_sort s (fun i => d i),
      Finset.sum_coe_sort s (fun i => d i * Real.log (d i))]
    rw [← ENNReal.ofReal_coe_nnreal]
    apply ENNReal.ofReal_le_ofReal
    have hrw : (∑ i ∈ s, d i) * Real.log (∑ i ∈ s, d i) - ∑ i ∈ s, d i * Real.log (d i) =
        ∑ i ∈ s, Real.negMulLog (d i) - Real.negMulLog (∑ i ∈ s, d i) := by
      simp only [Real.negMulLog, Finset.sum_neg_distrib, neg_mul]
      ring
    rw [hrw]
    have hd0 : 0 ≤ ∑ i ∈ s, d i :=
      Finset.sum_nonneg (fun i _ => mul_nonneg hη0.le (s199i_q_nonneg _))
    have h1 := Real.negMulLog_le_one_sub_self hd0
    have hinj : Set.InjOn (fun p : (Σ _ : ℕ, ℕ) => N + Nat.pair p.1 p.2) T := by
      intro p _ q _ hpq
      have h' : Nat.pair p.1 p.2 = Nat.pair q.1 q.2 := by simp only at hpq; omega
      have h'' := congrArg Nat.unpair h'
      simp only [Nat.unpair_pair, Prod.mk.injEq] at h''
      obtain ⟨p1, p2⟩ := p
      obtain ⟨q1, q2⟩ := q
      simp only at h''
      obtain ⟨rfl, rfl⟩ := h''
      rfl
    have hsum : ∑ i ∈ s, Real.negMulLog (d i) =
        ∑ m ∈ Finset.range K, ∑ j ∈ Finset.range (s199i_M m),
          Real.negMulLog (η * s199i_q (m, j)) := by
      rw [Finset.sum_image hinj, Finset.sum_sigma]
      refine Finset.sum_congr rfl (fun m _ => Finset.sum_congr rfl (fun j _ => ?_))
      simp only [d, Nat.add_sub_cancel_left, Nat.unpair_pair]
    have hge : (K : ℝ) * (η * Real.log 2) ≤ ∑ i ∈ s, Real.negMulLog (d i) := by
      rw [hsum]
      have := Finset.sum_le_sum (fun m (_ : m ∈ Finset.range K) => s199i_block_sum η hη0 hη1 m)
      simpa [Finset.sum_const, Finset.card_range, nsmul_eq_mul] using this
    linarith
  rw [hE]
  exact ENNReal.top_div_of_ne_top ENNReal.ofReal_ne_top

lemma s199i_sqrt_ge (η : ℝ) (h0 : 0 ≤ η) (h1 : η ≤ 1) : 1 - η ≤ Real.sqrt (1 - η) := by
  have h : (1 - η) ^ 2 ≤ 1 - η := by nlinarith
  calc 1 - η = Real.sqrt ((1 - η) ^ 2) := (Real.sqrt_sq (by linarith)).symm
    _ ≤ Real.sqrt (1 - η) := Real.sqrt_le_sqrt h


theorem solution (_h : HamiltonianData)
    (psi : Hilbert (ℕ × ℕ)) (hpsi : ‖psi‖ = 1)
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ phi : Hilbert (ℕ × ℕ), ‖phi‖ = 1 ∧
      traceSize (rankOne psi - rankOne phi) < ENNReal.ofReal epsilon ∧
      marginalEntropy (rankOne phi) = ⊤ := by
  set δ := min (epsilon / 16) (1 / 4) with hδ
  have hδ0 : 0 < δ := lt_min (by linarith) (by norm_num)
  have hδ1 : δ ≤ 1 / 4 := min_le_right _ _
  have hδε : δ ≤ epsilon / 16 := min_le_left _ _
  have hconv := lp.hasSum_single (E := fun _ : ℕ × ℕ => ℂ) (p := 2) (by norm_num) psi
  obtain ⟨s₀, hs₀⟩ := Metric.tendsto_atTop.1 hconv δ hδ0
  set a : Hilbert (ℕ × ℕ) := ∑ x ∈ s₀, lp.single 2 x (psi x) with ha_def
  have ha : ‖a - psi‖ < δ := by rw [← dist_eq_norm]; exact hs₀ s₀ le_rfl
  have ha_apply : ∀ y, a y = if y ∈ s₀ then psi y else 0 := by
    intro y
    rw [ha_def, lp.coeFn_sum, Finset.sum_apply]
    simp only [lp.single_apply, Pi.single_apply]
    exact Finset.sum_ite_eq s₀ y (fun c => psi c)
  set N := s₀.sup Prod.fst + 1 with hN
  have haN : ∀ i r, N ≤ i → a (i, r) = 0 := by
    intro i r hi
    rw [ha_apply, if_neg]
    intro hm
    have := Finset.le_sup (f := Prod.fst) hm
    simp only at this
    omega
  have hna : |‖a‖ - 1| < δ := by
    rw [← hpsi]; exact lt_of_le_of_lt (abs_norm_sub_norm_le a psi) ha
  have hapos : 0 < ‖a‖ := by
    have := (abs_lt.1 hna).1; linarith
  set η := δ ^ 2 with hη
  have hη0 : 0 < η := by positivity
  have hηδ : η ≤ δ := by nlinarith
  have hη1 : η ≤ 1 := by linarith
  set t := Real.sqrt (1 - η) / ‖a‖ with ht
  have ht0 : 0 ≤ t := by positivity
  have hta : t * ‖a‖ = Real.sqrt (1 - η) := by rw [ht]; field_simp
  set χ := s199i_chi N
  set phi : Hilbert (ℕ × ℕ) := ((t : ℝ) : ℂ) • a + ((δ : ℝ) : ℂ) • χ with hphi
  -- orthogonality
  have horth : inner ℂ a χ = 0 := by
    rw [lp.inner_eq_tsum]
    have : ∀ x : ℕ × ℕ, inner ℂ (a x) (χ x) = 0 := by
      intro x
      obtain ⟨i, r⟩ := x
      by_cases hi : N ≤ i
      · rw [haN i r hi, inner_zero_left]
      · have : χ (i, r) = 0 := by
          show s199i_chif N (i, r) = 0
          unfold s199i_chif s199i_c
          simp [hi]
        rw [this, inner_zero_right]
    exact (tsum_congr this).trans tsum_zero
  have horth' : inner ℂ (((t : ℝ) : ℂ) • a) (((δ : ℝ) : ℂ) • χ) = 0 := by
    rw [inner_smul_left, inner_smul_right, horth]; simp
  have hphin : ‖phi‖ = 1 := by
    have h := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _ horth'
    rw [← hphi, norm_smul, norm_smul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
      Real.norm_eq_abs, abs_of_nonneg ht0, abs_of_pos hδ0, s199i_chi_norm] at h
    have h2 : ‖phi‖ ^ 2 = 1 := by
      rw [sq, h]
      have : t * ‖a‖ * (t * ‖a‖) = 1 - η := by
        rw [hta, Real.mul_self_sqrt (by linarith)]
      nlinarith
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 h2
  -- distance
  have hdist : ‖psi - phi‖ < 4 * δ := by
    have e : psi - phi = (psi - a) + (((1 - t : ℝ) : ℂ) • a) - ((δ : ℝ) : ℂ) • χ := by
      rw [hphi, Complex.ofReal_sub, Complex.ofReal_one, sub_smul, one_smul]; abel
    rw [e]
    have h1 : ‖(((1 - t : ℝ) : ℂ) • a)‖ ≤ δ + η := by
      rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, ← abs_of_pos hapos, ← abs_mul,
        sub_mul, one_mul, hta]
      have := s199i_sqrt_ge η hη0.le hη1
      have hs1 : Real.sqrt (1 - η) ≤ 1 := by
        rw [Real.sqrt_le_one]; linarith
      rw [abs_le]
      constructor <;> linarith [(abs_lt.1 hna).1, (abs_lt.1 hna).2]
    have h2 : ‖((δ : ℝ) : ℂ) • χ‖ = δ := by
      rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hδ0, s199i_chi_norm, mul_one]
    have h3 : ‖psi - a‖ < δ := by rw [norm_sub_rev]; exact ha
    calc ‖psi - a + ((1 - t : ℝ) : ℂ) • a - ((δ : ℝ) : ℂ) • χ‖
        ≤ ‖psi - a + ((1 - t : ℝ) : ℂ) • a‖ + ‖((δ : ℝ) : ℂ) • χ‖ := norm_sub_le _ _
      _ ≤ ‖psi - a‖ + ‖((1 - t : ℝ) : ℂ) • a‖ + ‖((δ : ℝ) : ℂ) • χ‖ := by
          gcongr; exact norm_add_le _ _
      _ < 4 * δ := by linarith
  refine ⟨phi, hphin, ?_, ?_⟩
  · refine lt_of_le_of_lt (s199i_ts2 _ psi (psi - phi) (psi - phi) phi ?_) ?_
    · intro i j
      simp only [Matrix.sub_apply, rankOne, lp.coeFn_sub, Pi.sub_apply, star_sub]
      ring
    · rw [ENNReal.ofReal_lt_ofReal_iff hepsilon, hpsi, hphin]
      linarith
  · unfold marginalEntropy
    have hrow : ∀ i, N ≤ i → ∀ r, phi (i, r) =
        if i = r then ((δ : ℝ) : ℂ) * s199i_c N i else 0 := by
      intro i hi r
      rw [hphi, lp.coeFn_add, lp.coeFn_smul, lp.coeFn_smul]
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      rw [haN i r hi, mul_zero, zero_add]
      show ((δ : ℝ) : ℂ) * s199i_chif N (i, r) = _
      unfold s199i_chif
      split_ifs <;> simp
    apply s199i_entropy_top _ N η hη0 hη1
    intro i j hi hj
    rw [s199i_traceSecond phi (fun i => ((δ : ℝ) : ℂ) * s199i_c N i) i j (hrow i hi) (hrow j hj)]
    split_ifs with hij
    · congr 2
      rw [norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs, s199i_c_norm, if_pos hi]
    · rfl

