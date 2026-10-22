-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Gap20.P05.exampleOne
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T01:53:24.8098+00:00
-- url     : https://prove2.me/submissions/e11f7bdf-e977-4493-89bb-3fb44b587b15

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


lemma g74r_cfc_trace {n : Type*} [Fintype n] [DecidableEq n] {Y : Matrix n n ℂ} (hY : Y.IsHermitian)
    (f : ℝ → ℝ) : (cfc f Y).trace = ∑ i, ((f (hY.eigenvalues i) : ℝ) : ℂ) := by
  rw [hY.cfc_eq f, Matrix.IsHermitian.cfc, Unitary.conjStarAlgAut_apply, Matrix.trace_mul_cycle,
    Unitary.star_mul_self_of_mem hY.eigenvectorUnitary.2, one_mul, Matrix.trace_diagonal]
  rfl

lemma g74r_diag_herm {n : Type*} [Fintype n] [DecidableEq n] (d : n → ℝ) :
    (Matrix.diagonal (fun i => (d i : ℂ))).IsHermitian := by
  rw [Matrix.IsHermitian, Matrix.diagonal_conjTranspose]
  congr 1; funext i; simp

lemma g74r_trace_cfc_diag {n : Type*} [Fintype n] [DecidableEq n] (d : n → ℝ) (f : ℝ → ℝ) :
    (cfc f (Matrix.diagonal (fun i => (d i : ℂ)))).trace = ∑ i, ((f (d i) : ℝ) : ℂ) := by
  have hD := g74r_diag_herm d
  rw [g74r_cfc_trace hD]
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

lemma g74r_finEnt_diag {n : Type} [Fintype n] [DecidableEq n] (d : n → ℝ) :
    finiteEntropy (Matrix.diagonal (fun i => (d i : ℂ))) =
      ENNReal.ofReal ((∑ i, d i) * Real.log (∑ i, d i) - ∑ i, d i * Real.log (d i)) := by
  unfold finiteEntropy
  have hsa : IsSelfAdjoint (Matrix.diagonal (fun i => (d i : ℂ))) := g74r_diag_herm d
  have hfin := (Matrix.diagonal (fun i => (d i : ℂ))).finite_real_spectrum
  have hmul : Matrix.diagonal (fun i => (d i : ℂ)) * cfc Real.log (Matrix.diagonal (fun i => (d i : ℂ)))
      = cfc (fun x => x * Real.log x) (Matrix.diagonal (fun i => (d i : ℂ))) := by
    rw [cfc_mul (fun x => x) Real.log _ (hfin.continuousOn _) (hfin.continuousOn _), cfc_id' ℝ _]
  rw [hmul, g74r_trace_cfc_diag, Matrix.trace_diagonal]
  congr 1
  simp only [Complex.re_sum, Complex.ofReal_re]

lemma g74r_sum_inter (f : ℕ → ℝ) (N : ℕ) (hf : ∀ i, N ≤ i → f i = 0) (s : Finset ℕ) :
    ∑ i ∈ s, f i = ∑ i ∈ s ∩ Finset.range N, f i := by
  symm
  apply Finset.sum_subset Finset.inter_subset_left
  intro i hi hni
  apply hf
  by_contra hlt
  exact hni (Finset.mem_inter.2 ⟨hi, Finset.mem_range.2 (by omega)⟩)

/-- entropy (bits) of an ℕ-indexed diagonal probability vector supported in range N. -/
lemma g74r_entropyBits_diag (X : Matrix ℕ ℕ ℂ) (d : ℕ → ℝ) (N : ℕ)
    (hX : ∀ i j, X i j = if i = j then (d i : ℂ) else 0) (h0 : ∀ i, 0 ≤ d i) (h1 : ∀ i, d i ≤ 1)
    (hsupp : ∀ i, N ≤ i → d i = 0) (hsum : ∑ i ∈ Finset.range N, d i = 1) :
    entropyBits X =
      ENNReal.ofReal ((∑ i ∈ Finset.range N, Real.negMulLog (d i)) / Real.log 2) := by
  unfold entropyBits
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  rw [ENNReal.ofReal_div_of_pos hl2]
  congr 1
  have hsub : ∀ s : Finset ℕ, X.submatrix
      (fun i : s => i.val) (fun i : s => i.val) = Matrix.diagonal (fun i : s => (d i.val : ℂ)) := by
    intro s; ext a b
    simp only [Matrix.submatrix_apply, Matrix.diagonal_apply, Subtype.ext_iff, hX]
  have hval : ∀ s : Finset ℕ, finiteEntropy (X.submatrix
      (fun i : s => i.val) (fun i : s => i.val)) =
      ENNReal.ofReal (∑ i ∈ s, Real.negMulLog (d i) - Real.negMulLog (∑ i ∈ s, d i)) := by
    intro s
    rw [hsub, g74r_finEnt_diag]
    congr 1
    rw [Finset.sum_coe_sort s (fun i => d i), Finset.sum_coe_sort s (fun i => d i * Real.log (d i))]
    simp only [Real.negMulLog, Finset.sum_neg_distrib, neg_mul]
    ring
  unfold QAlgorithms.Papers.Independent.Frontier18.P07.extendedEntropyNats
  refine Eq.trans (iSup_congr (g := fun s : Finset ℕ => ENNReal.ofReal
    (∑ i ∈ s, Real.negMulLog (d i) - Real.negMulLog (∑ i ∈ s, d i))) (fun s => by convert hval s)) ?_
  apply le_antisymm
  · apply iSup_le
    intro s
    apply ENNReal.ofReal_le_ofReal
    have hT0 : 0 ≤ ∑ i ∈ s, d i := Finset.sum_nonneg (fun i _ => h0 i)
    have hT1 : ∑ i ∈ s, d i ≤ 1 := by
      calc ∑ i ∈ s, d i = ∑ i ∈ s ∩ Finset.range N, d i := g74r_sum_inter d N hsupp s
        _ ≤ ∑ i ∈ Finset.range N, d i :=
            Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_right
              (fun i _ _ => h0 i)
        _ = 1 := hsum
    have hn := Real.negMulLog_nonneg hT0 hT1
    have : ∑ i ∈ s, Real.negMulLog (d i) ≤ ∑ i ∈ Finset.range N, Real.negMulLog (d i) := by
      calc ∑ i ∈ s, Real.negMulLog (d i) = ∑ i ∈ s ∩ Finset.range N, Real.negMulLog (d i) :=
            g74r_sum_inter _ N (fun i hi => by rw [hsupp i hi, Real.negMulLog_zero]) s
        _ ≤ ∑ i ∈ Finset.range N, Real.negMulLog (d i) :=
            Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_right
              (fun i _ _ => Real.negMulLog_nonneg (h0 i) (h1 i))
    linarith
  · refine le_trans (le_of_eq ?_) (le_iSup _ (Finset.range N))
    rw [hsum, Real.negMulLog_one, sub_zero]

lemma g74r_norm_sq (v : Hilbert (ℕ × ℕ)) (c : ℕ → ℂ) (N : ℕ)
    (hv : ∀ i r, v (i, r) = if i = r then c i else 0) (hc : ∀ i, N ≤ i → c i = 0) :
    ‖v‖ ^ 2 = ∑ i ∈ Finset.range N, ‖c i‖ ^ 2 := by
  have h := lp.norm_rpow_eq_tsum (p := 2) (by norm_num) v
  have h2 : ((2 : ℝ≥0∞).toReal) = (2 : ℕ) := by norm_num
  rw [h2] at h
  simp only [Real.rpow_natCast] at h
  rw [h, tsum_eq_sum (s := (Finset.range N).image (fun i => (i, i)))]
  · rw [Finset.sum_image (fun a _ b _ hab => (Prod.ext_iff.1 hab).1)]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hv]; simp
  · intro p hp
    obtain ⟨i, r⟩ := p
    rw [hv]
    by_cases hir : i = r
    · subst hir
      have : N ≤ i := by
        by_contra hlt
        exact hp (Finset.mem_image.2 ⟨i, Finset.mem_range.2 (by omega), rfl⟩)
      simp [hc i this]
    · simp [hir]

lemma g74r_traceSecond (v : Hilbert (ℕ × ℕ)) (c : ℕ → ℂ)
    (hv : ∀ i r, v (i, r) = if i = r then c i else 0) (i j : ℕ) :
    traceSecond (rankOne v) i j = if i = j then ((‖c i‖ ^ 2 : ℝ) : ℂ) else 0 := by
  unfold traceSecond rankOne
  simp only [hv]
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

lemma g74r_single_apply (i r : ℕ) :
    (lp.single 2 ((0 : ℕ), (0 : ℕ)) (1 : ℂ) : Hilbert (ℕ × ℕ)) (i, r) =
      if i = r then (if i = 0 then 1 else 0) else 0 := by
  rw [lp.single_apply, Pi.single_apply]
  by_cases h0 : i = 0 <;> by_cases h1 : r = 0 <;> simp [h0, h1] <;> omega

def g74r_c (k : ℕ) (i : ℕ) : ℂ :=
  if i = 0 then (Real.sqrt (1 - exampleDelta k) : ℂ) else
    if i ≤ k then (Real.sqrt (exampleDelta k / (k : ℝ)) : ℂ) else 0

lemma g74r_vec_apply (k i r : ℕ) :
    exampleVector k (i, r) = if i = r then g74r_c k i else 0 := by
  unfold exampleVector
  rw [lp.coeFn_add, lp.coeFn_smul, lp.coeFn_smul, lp.coeFn_sum]
  simp only [Pi.add_apply, Pi.smul_apply, Finset.sum_apply, smul_eq_mul]
  rw [g74r_single_apply]
  have hs : (∑ j ∈ Finset.range k, (lp.single 2 (j + 1, j + 1) (1 : ℂ) : Hilbert (ℕ × ℕ)) (i, r)) =
      if i = r ∧ 1 ≤ i ∧ i ≤ k then 1 else 0 := by
    simp only [lp.single_apply, Pi.single_apply, Prod.mk.injEq]
    split_ifs with h
    · rw [Finset.sum_eq_single (i - 1)]
      · simp; omega
      · intro b _ hb; simp; omega
      · intro hb; simp at hb; omega
    · apply Finset.sum_eq_zero
      intro b hb
      simp at hb
      simp; omega
  rw [hs]
  unfold g74r_c
  by_cases hir : i = r
  · subst hir
    by_cases h0 : i = 0
    · simp [h0]
    · by_cases hk : i ≤ k
      · simp [h0, hk]
      · simp [h0, hk]
  · simp [hir]

lemma g74r_logK (k : ℕ) : Real.log 2 ≤ Real.log ((k + 2 : ℕ) : ℝ) := by
  apply Real.log_le_log (by norm_num)
  push_cast; linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]

lemma g74r_delta_pos (k : ℕ) : 0 < exampleDelta (k + 2) := by
  unfold exampleDelta
  have := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  exact div_pos this (lt_of_lt_of_le this (g74r_logK k))

lemma g74r_delta_le (k : ℕ) : exampleDelta (k + 2) ≤ 1 := by
  unfold exampleDelta
  have := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  rw [div_le_one (lt_of_lt_of_le this (g74r_logK k))]
  exact g74r_logK k

lemma g74r_delta_tendsto : Tendsto (fun k : ℕ => exampleDelta (k + 2)) atTop (𝓝 0) := by
  unfold exampleDelta
  apply Tendsto.div_atTop tendsto_const_nhds
  apply Real.tendsto_log_atTop.comp
  have : Tendsto (fun k : ℕ => ((k + 2 : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 2)
  exact this

def g74r_d (k : ℕ) (i : ℕ) : ℝ :=
  if i = 0 then 1 - exampleDelta k else if i ≤ k then exampleDelta k / (k : ℝ) else 0

lemma g74r_c_norm (k : ℕ) (i : ℕ) : ‖g74r_c (k + 2) i‖ ^ 2 = g74r_d (k + 2) i := by
  have h0 := g74r_delta_pos k
  have h1 := g74r_delta_le k
  unfold g74r_c g74r_d
  split_ifs
  · rw [Complex.norm_real, Real.norm_eq_abs, sq_abs, Real.sq_sqrt (by linarith)]
  · rw [Complex.norm_real, Real.norm_eq_abs, sq_abs, Real.sq_sqrt (by positivity)]
  · simp

lemma g74r_d_sum (k : ℕ) : ∑ i ∈ Finset.range (k + 2 + 1), g74r_d (k + 2) i = 1 := by
  rw [Finset.sum_range_succ']
  have : ∀ i ∈ Finset.range (k + 2), g74r_d (k + 2) (i + 1) = exampleDelta (k + 2) / ((k + 2 : ℕ) : ℝ) := by
    intro i hi
    rw [Finset.mem_range] at hi
    unfold g74r_d
    rw [if_neg (by omega), if_pos (by omega)]
  rw [Finset.sum_congr rfl this, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  unfold g74r_d
  simp only [if_true]
  have hK : ((k + 2 : ℕ) : ℝ) ≠ 0 := by positivity
  field_simp
  ring

lemma g74r_d_supp (k : ℕ) : ∀ i, k + 2 + 1 ≤ i → g74r_d (k + 2) i = 0 := by
  intro i hi
  unfold g74r_d
  rw [if_neg (by omega), if_neg (by omega)]

lemma g74r_c_supp (k : ℕ) : ∀ i, k + 2 + 1 ≤ i → g74r_c (k + 2) i = 0 := by
  intro i hi
  unfold g74r_c
  rw [if_neg (by omega), if_neg (by omega)]

lemma g74r_H (k : ℕ) : (∑ i ∈ Finset.range (k + 2 + 1), Real.negMulLog (g74r_d (k + 2) i)) / Real.log 2 =
    1 + (Real.negMulLog (1 - exampleDelta (k + 2)) + Real.negMulLog (exampleDelta (k + 2))) / Real.log 2 := by
  rw [Finset.sum_range_succ']
  have : ∀ i ∈ Finset.range (k + 2), Real.negMulLog (g74r_d (k + 2) (i + 1)) =
      Real.negMulLog (exampleDelta (k + 2) / ((k + 2 : ℕ) : ℝ)) := by
    intro i hi
    rw [Finset.mem_range] at hi
    unfold g74r_d
    rw [if_neg (by omega), if_pos (by omega)]
  rw [Finset.sum_congr rfl this, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  unfold g74r_d
  simp only [if_true]
  have hδ := g74r_delta_pos k
  have hK : (0 : ℝ) < ((k + 2 : ℕ) : ℝ) := by positivity
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlK : 0 < Real.log ((k + 2 : ℕ) : ℝ) := lt_of_lt_of_le hl2 (g74r_logK k)
  have hδK : exampleDelta (k + 2) * Real.log ((k + 2 : ℕ) : ℝ) = Real.log 2 := by
    unfold exampleDelta; field_simp
  unfold Real.negMulLog
  rw [Real.log_div hδ.ne' hK.ne']
  field_simp
  linear_combination hδK

open QAlgorithms.Papers.Independent.Dependency50.P33 (NuclearExpansion)

def g74r_exp2 {I : Type} (X : Matrix I I ℂ) (u v u' v' : Hilbert I)
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

theorem g74r_ts2 {I : Type} (X : Matrix I I ℂ) (u v u' v' : Hilbert I)
    (hX : ∀ i j, X i j = u i * star (v j) + u' i * star (v' j)) :
    traceSize X ≤ ENNReal.ofReal (‖u‖ * ‖v‖ + ‖u'‖ * ‖v'‖) := by
  refine (iInf_le _ (g74r_exp2 X u v u' v' hX)).trans (le_of_eq ?_)
  congr 1
  rw [tsum_eq_sum (s := Finset.range 2)]
  · simp [g74r_exp2, Finset.sum_range_succ]
  · intro n hn
    simp only [Finset.mem_range, not_lt] at hn
    have h0 : n ≠ 0 := by omega
    have h1 : n ≠ 1 := by omega
    simp [g74r_exp2, h0, h1]


lemma g74r_norm_one (k : ℕ) : ‖exampleVector (k + 2)‖ = 1 := by
  have h := g74r_norm_sq (exampleVector (k + 2)) (g74r_c (k + 2)) (k + 2 + 1)
    (g74r_vec_apply (k + 2)) (g74r_c_supp k)
  simp only [g74r_c_norm] at h
  rw [g74r_d_sum] at h
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 h

lemma g74r_diff_norm (k : ℕ) : ‖exampleVector (k + 2) - lp.single 2 (0, 0) (1 : ℂ)‖ =
    Real.sqrt ((Real.sqrt (1 - exampleDelta (k + 2)) - 1) ^ 2 + exampleDelta (k + 2)) := by
  have hv : ∀ i r, ((exampleVector (k + 2) - lp.single 2 ((0 : ℕ), (0 : ℕ)) (1 : ℂ) :
      Hilbert (ℕ × ℕ)) : ℕ × ℕ → ℂ) (i, r) =
      if i = r then g74r_c (k + 2) i - (if i = 0 then 1 else 0) else 0 := by
    intro i r
    rw [lp.coeFn_sub, Pi.sub_apply, g74r_vec_apply, g74r_single_apply]
    split_ifs <;> simp
  have h := g74r_norm_sq _ _ (k + 2 + 1) hv (fun i hi => by
    rw [g74r_c_supp k i hi, if_neg (by omega), sub_zero])
  rw [Finset.sum_range_succ'] at h
  have e : ∀ i ∈ Finset.range (k + 2), ‖g74r_c (k + 2) (i + 1) - (if i + 1 = 0 then 1 else 0)‖ ^ 2
      = g74r_d (k + 2) (i + 1) := by
    intro i _
    rw [if_neg (by omega), sub_zero, g74r_c_norm]
  rw [Finset.sum_congr rfl e] at h
  have hs := g74r_d_sum k
  rw [Finset.sum_range_succ'] at hs
  have h0 : ‖g74r_c (k + 2) 0 - (if (0 : ℕ) = 0 then 1 else 0)‖ ^ 2 =
      (Real.sqrt (1 - exampleDelta (k + 2)) - 1) ^ 2 := by
    unfold g74r_c
    simp only [if_true]
    rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  rw [h0] at h
  have hd0 : g74r_d (k + 2) 0 = 1 - exampleDelta (k + 2) := by unfold g74r_d; simp
  rw [hd0] at hs
  rw [← Real.sqrt_sq (norm_nonneg _), h]
  congr 1
  linarith

lemma g74r_ent_vec (k : ℕ) : marginalEntropy (rankOne (exampleVector (k + 2))) =
    ENNReal.ofReal (1 + (Real.negMulLog (1 - exampleDelta (k + 2)) +
      Real.negMulLog (exampleDelta (k + 2))) / Real.log 2) := by
  unfold marginalEntropy
  have h0 := g74r_delta_pos k
  have h1 := g74r_delta_le k
  rw [g74r_entropyBits_diag _ (g74r_d (k + 2)) (k + 2 + 1)
    (fun i j => by rw [g74r_traceSecond _ _ (g74r_vec_apply (k + 2)), g74r_c_norm])
    (fun i => by unfold g74r_d; split_ifs <;> first | linarith | positivity)
    (fun i => by
      unfold g74r_d
      have hK : (1 : ℝ) ≤ ((k + 2 : ℕ) : ℝ) := by push_cast; linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
      split_ifs
      · linarith
      · rw [div_le_one (by linarith)]; linarith
      · norm_num)
    (g74r_d_supp k) (g74r_d_sum k), g74r_H]

lemma g74r_ent_e : marginalEntropy (rankOne (lp.single 2 ((0 : ℕ), (0 : ℕ)) (1 : ℂ))) = 0 := by
  unfold marginalEntropy
  rw [g74r_entropyBits_diag _ (fun i => if i = 0 then 1 else 0) 1
    (fun i j => by
      rw [g74r_traceSecond _ (fun i => if i = 0 then 1 else 0) g74r_single_apply]
      split_ifs <;> simp_all)
    (fun i => by split_ifs <;> norm_num) (fun i => by split_ifs <;> norm_num)
    (fun i hi => by rw [if_neg (by omega)]) (by simp)]
  simp

/-- Example 1, PDF p.3, (4)--(5). Printed: k starts at 1 and delta=1/log k.
Changed: use k+2 and log base two, because the printed first term is undefined
and the asserted entropy limit is one bit. The sequence is the displayed vector,
not an arbitrary convergent family; no uniform energy bound is imposed. -/
theorem solution (_h : HamiltonianData) :
    (∀ k : ℕ, ‖exampleVector (k + 2)‖ = 1) ∧
    Tendsto (fun k : ℕ => traceSize
      (rankOne (exampleVector (k + 2)) - rankOne (lp.single 2 (0, 0) (1 : ℂ))))
      atTop (𝓝 (0 : ℝ≥0∞)) ∧
    Tendsto (fun k : ℕ => marginalEntropy (rankOne (exampleVector (k + 2))))
      atTop (𝓝 (1 : ℝ≥0∞)) ∧
    marginalEntropy (rankOne (lp.single 2 (0, 0) (1 : ℂ))) = 0 := by
  refine ⟨g74r_norm_one, ?_, ?_, g74r_ent_e⟩
  · have hb : ∀ k : ℕ, traceSize
        (rankOne (exampleVector (k + 2)) - rankOne (lp.single 2 (0, 0) (1 : ℂ))) ≤
        ENNReal.ofReal (2 * Real.sqrt ((Real.sqrt (1 - exampleDelta (k + 2)) - 1) ^ 2 +
          exampleDelta (k + 2))) := by
      intro k
      refine (g74r_ts2 _ (exampleVector (k + 2) - lp.single 2 (0, 0) (1 : ℂ))
        (exampleVector (k + 2)) (lp.single 2 (0, 0) (1 : ℂ))
        (exampleVector (k + 2) - lp.single 2 (0, 0) (1 : ℂ)) ?_).trans ?_
      · intro i j
        simp only [Matrix.sub_apply, rankOne, lp.coeFn_sub, Pi.sub_apply, star_sub]
        ring
      · rw [g74r_norm_one, g74r_diff_norm, lp.norm_single (p := 2) (by norm_num), norm_one]
        apply le_of_eq; congr 1; ring
    have ht : Tendsto (fun k : ℕ => ENNReal.ofReal (2 * Real.sqrt ((Real.sqrt
        (1 - exampleDelta (k + 2)) - 1) ^ 2 + exampleDelta (k + 2)))) atTop (𝓝 0) := by
      rw [← ENNReal.ofReal_zero]
      apply ENNReal.tendsto_ofReal
      have hc : Continuous (fun x : ℝ => 2 * Real.sqrt ((Real.sqrt (1 - x) - 1) ^ 2 + x)) := by
        fun_prop
      have := (hc.tendsto 0).comp g74r_delta_tendsto
      simpa [Function.comp_def] using this
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ht
      (fun _ => bot_le) hb
  · simp only [g74r_ent_vec]
    rw [← ENNReal.ofReal_one]
    apply ENNReal.tendsto_ofReal
    have hc : Continuous (fun x : ℝ => 1 + (Real.negMulLog (1 - x) + Real.negMulLog x) / Real.log 2) := by
      fun_prop
    have := (hc.tendsto 0).comp g74r_delta_tendsto
    simpa [Function.comp_def] using this

end
