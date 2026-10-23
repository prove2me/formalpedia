-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Renew46.P43.exactTypeProbability
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T08:25:32.581135+00:00
-- url     : https://prove2.me/submissions/5a854480-6f5c-48d3-8461-35cec7b1d9e7

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P43
noncomputable section

open QAlgorithms QAlgorithms.Papers.Independent.Renew46.P43

open scoped BigOperators Matrix ComplexConjugate ComplexOrder ENNReal Matrix.Norms.L2Operator

open Filter MeasureTheory

open QAlgorithms.Papers.Independent.Information100.P08 (IsPure)

open QAlgorithms.Papers.Independent.Information100.P06 (Below)

open QAlgorithms.Papers.Independent.Information100.P60 (copies relativeBits)

open QAlgorithms.Papers.Independent.Dependency50.P19 (count both)

open QAlgorithms.Papers.Independent.Information100.P22 (coherentInformation)

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Claimed50.P40 (InBlocks)

attribute [local instance] QAlgorithms.Papers.Independent.Renew46.P43.matrixMeasurableSpace

theorem g79c_expY {n d : ℕ} (q : Fin n → Fin d → ℝ) (hq1 : ∀ k, ∑ j, q k j = 1)
    (T : Finset (Fin n)) (j : Fin d) :
    ∑ v : Fin n → Fin d, (∏ k, q k (v k)) * (if ∀ i ∈ T, v i = j then (1:ℝ) else 0)
      = ∏ i ∈ T, q i j := by
  have key : ∀ v : Fin n → Fin d, (∏ k, q k (v k)) * (if ∀ i ∈ T, v i = j then (1:ℝ) else 0)
      = ∏ k, (q k (v k) * (if k ∈ T ∧ v k ≠ j then 0 else 1)) := by
    intro v
    rw [Finset.prod_mul_distrib]
    congr 1
    split_ifs with h
    · symm; apply Finset.prod_eq_one; intro i _
      rw [if_neg]; push_neg; exact fun hi => h i hi
    · push_neg at h; obtain ⟨i, hi, hne⟩ := h
      symm; apply Finset.prod_eq_zero (Finset.mem_univ i); simp [hi, hne]
  simp_rw [key]
  rw [← Fintype.prod_sum (fun k c => q k c * if k ∈ T ∧ c ≠ j then (0:ℝ) else 1)]
  have hf : ∀ k, ∑ c, q k c * (if k ∈ T ∧ c ≠ j then (0:ℝ) else 1) = if k ∈ T then q k j else 1 := by
    intro k
    by_cases hk : k ∈ T
    · simp [hk]
    · simp [hk, hq1]
  simp_rw [hf]
  rw [Finset.prod_ite_mem, Finset.univ_inter]

theorem g79c_varT {n d : ℕ} (q : Fin n → Fin d → ℝ) (hq1 : ∀ k, ∑ j, q k j = 1)
    (T : Finset (Fin n)) (j : Fin d) :
    ∑ v : Fin n → Fin d, (∏ k, q k (v k)) * (((T.filter (fun k => v k = j)).card : ℝ) - ∑ k ∈ T, q k j) ^ 2
      = ∑ k ∈ T, (q k j - q k j ^ 2) := by
  set X : Fin n → (Fin n → Fin d) → ℝ := fun k v => if v k = j then 1 else 0 with hX
  have hc : ∀ v : Fin n → Fin d, ((T.filter (fun k => v k = j)).card : ℝ) - ∑ k ∈ T, q k j
      = ∑ k ∈ T, (X k v - q k j) := by
    intro v
    rw [Finset.sum_sub_distrib]
    simp only [hX]
    rw [Finset.natCast_card_filter]
  have h2 : ∀ k l, ∑ v : Fin n → Fin d, (∏ i, q i (v i)) * ((X k v - q k j) * (X l v - q l j))
      = if k = l then q k j - q k j ^ 2 else 0 := by
    intro k l
    have e1 : ∀ v : Fin n → Fin d, X k v * X l v = if ∀ i ∈ ({k, l} : Finset (Fin n)), v i = j then 1 else 0 := by
      intro v; simp only [hX, Finset.mem_insert, Finset.mem_singleton, forall_eq_or_imp, forall_eq]
      split_ifs <;> simp_all
    have Ek : ∀ k, ∑ v : Fin n → Fin d, (∏ i, q i (v i)) * X k v = q k j := by
      intro k; have := g79c_expY q hq1 {k} j; simpa [hX] using this
    have E0 : ∑ v : Fin n → Fin d, (∏ i, q i (v i)) * 1 = 1 := by
      have := g79c_expY q hq1 ∅ j; simpa using this
    have Ekl : ∑ v : Fin n → Fin d, (∏ i, q i (v i)) * (X k v * X l v) = ∏ i ∈ ({k, l} : Finset (Fin n)), q i j := by
      simp_rw [e1]; exact g79c_expY q hq1 _ j
    have expand : ∀ v : Fin n → Fin d, (∏ i, q i (v i)) * ((X k v - q k j) * (X l v - q l j))
        = (∏ i, q i (v i)) * (X k v * X l v) - q l j * ((∏ i, q i (v i)) * X k v)
          - q k j * ((∏ i, q i (v i)) * X l v) + q k j * q l j * ((∏ i, q i (v i)) * 1) := by
      intro v; ring
    simp_rw [expand]
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
      ← Finset.mul_sum, ← Finset.mul_sum, Ekl, Ek, Ek, E0]
    by_cases hkl : k = l
    · subst hkl; simp; ring
    · simp [hkl]; ring
  simp_rw [hc, sq, Finset.sum_mul_sum, Finset.mul_sum]
  refine (Finset.sum_comm.trans (Finset.sum_congr rfl fun k _ => Finset.sum_comm)).trans ?_
  simp_rw [h2]
  simp [sq]

theorem g79c_badT {n d : ℕ} (q : Fin n → Fin d → ℝ) (hq0 : ∀ k j, 0 ≤ q k j)
    (hq1 : ∀ k, ∑ j, q k j = 1) (T : Finset (Fin n)) (j : Fin d) (P : ℝ)
    (hP : ∀ k ∈ T, q k j = P) (A : ℝ) (hA : 0 < A) :
    ∑ v ∈ Finset.univ.filter (fun v : Fin n → Fin d =>
      ¬ |((T.filter (fun k => v k = j)).card : ℝ) - T.card * P| ≤
        A * Real.sqrt (T.card) * Real.sqrt (P * (1 - P))),
      ∏ k, q k (v k) ≤ 1 / A ^ 2 := by
  set N : ℝ := (T.card : ℝ) with hN
  set t := A * Real.sqrt N * Real.sqrt (P * (1 - P)) with ht
  have ht0 : 0 ≤ t := by positivity
  have hπ0 : ∀ v : Fin n → Fin d, 0 ≤ ∏ k, q k (v k) := fun v => Finset.prod_nonneg fun k _ => hq0 _ _
  have hvar := g79c_varT q hq1 T j
  have hm : ∑ k ∈ T, q k j = N * P := by
    rw [Finset.sum_congr rfl hP, Finset.sum_const, nsmul_eq_mul]
  have hv2 : ∑ k ∈ T, (q k j - q k j ^ 2) = N * (P * (1 - P)) := by
    rw [Finset.sum_congr rfl (fun k hk => by rw [hP k hk]), Finset.sum_const, nsmul_eq_mul]; ring
  rw [hm, hv2] at hvar
  set Var := ∑ v : Fin n → Fin d, (∏ k, q k (v k)) * (((T.filter (fun k => v k = j)).card : ℝ) - N * P) ^ 2 with hVar
  have hBadle : ∑ v ∈ Finset.univ.filter (fun v : Fin n → Fin d =>
      ¬ |((T.filter (fun k => v k = j)).card : ℝ) - N * P| ≤ t), (∏ k, q k (v k)) * t ^ 2 ≤ Var := by
    calc _ ≤ ∑ v ∈ Finset.univ.filter (fun v : Fin n → Fin d =>
      ¬ |((T.filter (fun k => v k = j)).card : ℝ) - N * P| ≤ t),
        (∏ k, q k (v k)) * (((T.filter (fun k => v k = j)).card : ℝ) - N * P) ^ 2 := by
          apply Finset.sum_le_sum; intro v hv
          simp only [Finset.mem_filter, not_le] at hv
          apply mul_le_mul_of_nonneg_left _ (hπ0 v)
          rw [← sq_abs (((T.filter (fun k => v k = j)).card : ℝ) - N * P)]
          nlinarith [hv.2]
      _ ≤ Var := Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          (fun v _ _ => mul_nonneg (hπ0 v) (sq_nonneg _))
  rw [← Finset.sum_mul] at hBadle
  have hN0 : 0 ≤ N := by positivity
  by_cases hpos : 0 < N * (P * (1 - P))
  · have hs : 0 < P * (1 - P) := by
      by_contra h; push_neg at h; nlinarith
    have ht2 : t ^ 2 = A ^ 2 * (N * (P * (1 - P))) := by
      rw [ht, mul_pow, mul_pow, Real.sq_sqrt hs.le, Real.sq_sqrt hN0]; ring
    rw [ht2, hvar] at hBadle
    rw [le_div_iff₀ (by positivity)]
    by_contra hc
    have hc' := lt_of_not_ge hc
    nlinarith [mul_lt_mul_of_pos_right hc' hpos]
  · push_neg at hpos
    have hVnn : 0 ≤ Var := Finset.sum_nonneg fun v _ => mul_nonneg (hπ0 v) (sq_nonneg _)
    have hV0 : Var = 0 := by linarith
    have hall := (Finset.sum_eq_zero_iff_of_nonneg (fun v _ => mul_nonneg (hπ0 v) (sq_nonneg _))).1 hV0
    have : ∑ v ∈ Finset.univ.filter (fun v : Fin n → Fin d =>
      ¬ |((T.filter (fun k => v k = j)).card : ℝ) - N * P| ≤ t), ∏ k, q k (v k) = 0 := by
      apply Finset.sum_eq_zero; intro v hv
      simp only [Finset.mem_filter, not_le] at hv
      have h1 := hall v (Finset.mem_univ v)
      have h2 : 0 < (((T.filter (fun k => v k = j)).card : ℝ) - N * P) ^ 2 := by
        rw [← sq_abs]; exact pow_pos (lt_of_le_of_lt ht0 hv.2) 2
      rcases mul_eq_zero.1 h1 with h | h
      · exact h
      · exact absurd h h2.ne'
    rw [this]; positivity

theorem g79c_prob2 {n d a : ℕ} (q : Fin n → Fin d → ℝ) (hq0 : ∀ k j, 0 ≤ q k j)
    (hq1 : ∀ k, ∑ j, q k j = 1) (w : Fin n → Fin a) (P : Fin a → Fin d → ℝ)
    (hP : ∀ k r, q k r = P (w k) r) (A : ℝ) (hA : 0 < A) :
    1 - (a : ℝ) * d / A ^ 2 ≤ ∑ v ∈ Finset.univ.filter (fun v : Fin n → Fin d => ∀ x r,
      |((Finset.univ.filter fun k => w k = x ∧ v k = r).card : ℝ) - count w x * P x r| ≤
        A * Real.sqrt (count w x) * Real.sqrt (P x r * (1 - P x r))),
      ∏ k, q k (v k) := by
  have hπ0 : ∀ v : Fin n → Fin d, 0 ≤ ∏ k, q k (v k) := fun v => Finset.prod_nonneg fun k _ => hq0 _ _
  have htot : ∑ v : Fin n → Fin d, ∏ k, q k (v k) = 1 := by
    rw [← Fintype.prod_sum (fun k c => q k c)]; simp [hq1]
  set C : Fin a → Fin d → (Fin n → Fin d) → Prop := fun x r v =>
    |((Finset.univ.filter fun k => w k = x ∧ v k = r).card : ℝ) - count w x * P x r| ≤
        A * Real.sqrt (count w x) * Real.sqrt (P x r * (1 - P x r)) with hC
  have hbad : ∀ x r, ∑ v ∈ Finset.univ.filter (fun v => ¬ C x r v), ∏ k, q k (v k) ≤ 1 / A ^ 2 := by
    intro x r
    have := g79c_badT q hq0 hq1 (Finset.univ.filter fun k => w k = x) r (P x r)
      (fun k hk => by rw [hP]; simp only [Finset.mem_filter] at hk; rw [hk.2]) A hA
    convert this using 3
    simp only [hC, count, Finset.filter_filter]
  have hsplit := Finset.sum_filter_add_sum_filter_not (Finset.univ : Finset (Fin n → Fin d))
    (fun v : Fin n → Fin d => ∀ x r, C x r v) (fun v => ∏ k, q k (v k))
  rw [htot] at hsplit
  have hpt : ∀ v : Fin n → Fin d, (if ¬ ∀ x r, C x r v then ∏ k, q k (v k) else 0)
      ≤ ∑ xr : Fin a × Fin d, (if ¬ C xr.1 xr.2 v then ∏ k, q k (v k) else 0) := by
    intro v
    by_cases h : ∀ x r, C x r v
    · rw [if_neg (not_not.2 h)]
      exact Finset.sum_nonneg fun j _ => by split_ifs <;> simp [hπ0 v]
    · rw [if_pos h]
      push_neg at h; obtain ⟨x, r, hj⟩ := h
      have := Finset.single_le_sum (f := fun xr : Fin a × Fin d => if ¬ C xr.1 xr.2 v then ∏ k, q k (v k) else 0)
        (fun j _ => by split_ifs <;> simp [hπ0 v]) (Finset.mem_univ (x, r))
      simpa [hj] using this
  have hrest : ∑ v ∈ Finset.univ.filter (fun v : Fin n → Fin d => ¬ ∀ x r, C x r v), ∏ k, q k (v k)
      ≤ ∑ xr : Fin a × Fin d, ∑ v ∈ Finset.univ.filter (fun v => ¬ C xr.1 xr.2 v), ∏ k, q k (v k) := by
    rw [Finset.sum_filter]
    refine (Finset.sum_le_sum fun v _ => hpt v).trans (le_of_eq ?_)
    rw [Finset.sum_comm]
    simp_rw [Finset.sum_filter]
  have hb : ∑ xr : Fin a × Fin d, ∑ v ∈ Finset.univ.filter (fun v => ¬ C xr.1 xr.2 v), ∏ k, q k (v k)
      ≤ ∑ xr : Fin a × Fin d, 1 / A ^ 2 := Finset.sum_le_sum fun xr _ => hbad xr.1 xr.2
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin, nsmul_eq_mul] at hb
  push_cast at hb
  have : (a:ℝ) * d * (1 / A ^ 2) = a * d / A ^ 2 := by ring
  linarith
lemma g79c_trace_cfc_eq {X Y : Type*} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
    (P : Matrix X X ℂ) (Q : Matrix Y Y ℂ) (hP : P.IsHermitian) (hQ : Q.IsHermitian)
    (f : ℝ → ℝ) (hf : f 0 = 0) (htr : ∀ k : ℕ, (P ^ (k + 1)).trace = (Q ^ (k + 1)).trace) :
    (cfc f P).trace = (cfc f Q).trace := by
  classical
  set S : Finset ℝ := (P.finite_real_spectrum.union Q.finite_real_spectrum).toFinset ∪ {0} with hS
  set p : Polynomial ℝ := Lagrange.interpolate S id f with hp
  have hev : ∀ x ∈ S, p.eval x = f x := by
    intro x hx
    have := Lagrange.eval_interpolate_at_node (s := S) (v := id) f (Set.injOn_id _) hx
    exact this
  have hPe : cfc f P = Polynomial.aeval P p := by
    rw [← cfc_polynomial p P hP.isSelfAdjoint]
    apply cfc_congr
    intro x hx
    exact (hev x (by simp [hS, hx])).symm
  have hQe : cfc f Q = Polynomial.aeval Q p := by
    rw [← cfc_polynomial p Q hQ.isSelfAdjoint]
    apply cfc_congr
    intro x hx
    exact (hev x (by simp [hS, hx])).symm
  have h0 : p.coeff 0 = 0 := by
    rw [Polynomial.coeff_zero_eq_eval_zero, hev 0 (by simp [hS]), hf]
  rw [hPe, hQe, Polynomial.aeval_eq_sum_range, Polynomial.aeval_eq_sum_range,
    Matrix.trace_sum, Matrix.trace_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Matrix.trace_smul, Matrix.trace_smul]
  rcases i with _ | k
  · simp [h0]
  · rw [htr k]

lemma g79c_cfc_trace {n : Type*} [Fintype n] [DecidableEq n] {Y : Matrix n n ℂ} (hY : Y.IsHermitian)
    (f : ℝ → ℝ) : (cfc f Y).trace = ∑ i, ((f (hY.eigenvalues i) : ℝ) : ℂ) := by
  rw [hY.cfc_eq f, Matrix.IsHermitian.cfc, Unitary.conjStarAlgAut_apply, Matrix.trace_mul_cycle,
    Unitary.star_mul_self_of_mem hY.eigenvectorUnitary.2, one_mul, Matrix.trace_diagonal]
  rfl

lemma g79c_diag_herm {n : Type*} [Fintype n] [DecidableEq n] (d : n → ℝ) :
    (Matrix.diagonal (fun i => (d i : ℂ))).IsHermitian := by
  rw [Matrix.IsHermitian, Matrix.diagonal_conjTranspose]
  congr 1; funext i; simp

lemma g79c_trace_cfc_diag {n : Type*} [Fintype n] [DecidableEq n] (d : n → ℝ) (f : ℝ → ℝ) :
    (cfc f (Matrix.diagonal (fun i => (d i : ℂ)))).trace = ∑ i, ((f (d i) : ℝ) : ℂ) := by
  have hD := g79c_diag_herm d
  rw [g79c_cfc_trace hD]
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

lemma g79c_vn_diag {n : Type*} [Fintype n] [DecidableEq n] (d : n → ℝ) :
    vnEntropy (Matrix.diagonal (fun i => (d i : ℂ))) = -∑ i, d i * Real.logb 2 (d i) := by
  unfold vnEntropy
  rw [g79c_trace_cfc_diag]
  simp

theorem g79c_atom_sum {d : ℕ} (S : FineResolution d) : ∑ j, S.atom j = 1 := by
  have hU := (Matrix.mem_unitaryGroup_iff).1 S.basis.2
  ext a b
  rw [← hU]
  simp [Matrix.sum_apply, FineResolution.atom, Matrix.mul_apply, Matrix.star_apply, RCLike.star_def]

theorem g79c_wt_mul {n d : ℕ} (A B : Fin n → Matrix (Fin d) (Fin d) ℂ) :
    wordTensor A * wordTensor B = wordTensor (fun k => A k * B k) := by
  ext a b
  simp only [Matrix.mul_apply, wordTensor]
  rw [Fintype.prod_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [← Finset.prod_mul_distrib]

theorem g79c_wt_conjT {n d : ℕ} (A : Fin n → Matrix (Fin d) (Fin d) ℂ) :
    (wordTensor A)ᴴ = wordTensor (fun k => (A k)ᴴ) := by
  ext a b
  simp [Matrix.conjTranspose_apply, wordTensor]

theorem g79c_wt_one {n d : ℕ} : wordTensor (fun _ : Fin n => (1 : Matrix (Fin d) (Fin d) ℂ)) = 1 := by
  ext a b
  simp only [wordTensor, Matrix.one_apply]
  by_cases h : a = b
  · subst h; simp
  · rw [if_neg h]
    have : ∃ k, a k ≠ b k := by
      by_contra h'; push_neg at h'; exact h (funext h')
    obtain ⟨k, hk⟩ := this
    exact Finset.prod_eq_zero (Finset.mem_univ k) (by simp [hk])

theorem g79c_wt_trace {n d : ℕ} (A : Fin n → Matrix (Fin d) (Fin d) ℂ) :
    (wordTensor A).trace = ∏ k, (A k).trace := by
  simp only [Matrix.trace, Matrix.diag, wordTensor]
  rw [Fintype.prod_sum]

theorem g79c_wt_expand {n d : ℕ} (c : Fin n → Fin d → ℂ) (B : Fin n → Fin d → Matrix (Fin d) (Fin d) ℂ) :
    wordTensor (fun k => ∑ r, c k r • B k r) = ∑ j : Fin n → Fin d, (∏ k, c k (j k)) • wordTensor (fun k => B k (j k)) := by
  ext a b
  simp only [wordTensor, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  rw [Fintype.prod_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← Finset.prod_mul_distrib]

theorem g79c_atom_mul {d : ℕ} (S : FineResolution d) (r r' : Fin d) :
    S.atom r * S.atom r' = if r = r' then S.atom r else 0 := by
  have hU := (Matrix.mem_unitaryGroup_iff').1 S.basis.2
  have hU' : ∀ i j, ∑ b, conj ((S.basis : Matrix (Fin d) (Fin d) ℂ) b i) * (S.basis : Matrix (Fin d) (Fin d) ℂ) b j
      = if i = j then 1 else 0 := by
    intro i j
    have := congrFun (congrFun hU i) j
    simpa [Matrix.mul_apply, Matrix.star_apply, Matrix.one_apply, RCLike.star_def] using this
  ext a b
  simp only [Matrix.mul_apply, FineResolution.atom]
  have : ∀ c, (S.basis : Matrix (Fin d) (Fin d) ℂ) a r * conj ((S.basis : Matrix (Fin d) (Fin d) ℂ) c r) *
      ((S.basis : Matrix (Fin d) (Fin d) ℂ) c r' * conj ((S.basis : Matrix (Fin d) (Fin d) ℂ) b r'))
      = ((S.basis : Matrix (Fin d) (Fin d) ℂ) a r * conj ((S.basis : Matrix (Fin d) (Fin d) ℂ) b r')) *
        (conj ((S.basis : Matrix (Fin d) (Fin d) ℂ) c r) * (S.basis : Matrix (Fin d) (Fin d) ℂ) c r') := by
    intro c; ring
  simp_rw [this]
  rw [← Finset.mul_sum, hU']
  split_ifs with h
  · subst h; simp [FineResolution.atom]
  · simp

theorem g79c_atom_conjT {d : ℕ} (S : FineResolution d) (r : Fin d) : (S.atom r)ᴴ = S.atom r := by
  ext a b; simp [FineResolution.atom, Matrix.conjTranspose_apply, mul_comm]

theorem g79c_atom_tr {d : ℕ} (S : FineResolution d) (r : Fin d) : (S.atom r).trace = 1 := by
  have hU := (Matrix.mem_unitaryGroup_iff').1 S.basis.2
  have := congrFun (congrFun hU r) r
  simp only [Matrix.mul_apply, Matrix.star_apply, Matrix.one_apply_eq, RCLike.star_def] at this
  rw [← this]
  simp [Matrix.trace, FineResolution.atom, mul_comm]

theorem g79c_state_eq {d : ℕ} (S : FineResolution d) :
    S.state = ∑ r, ((S.weight r : ℝ) : ℂ) • S.atom r := by
  ext a b
  simp only [FineResolution.state, QAlgorithms.Papers.Independent.Dependency50.P19.Spectrum.density,
    QAlgorithms.conjSuperop, Matrix.mul_apply, Matrix.diagonal_apply, Matrix.sum_apply, Matrix.smul_apply,
    FineResolution.atom, Matrix.conjTranspose_apply, smul_eq_mul]
  simp [Finset.sum_mul, RCLike.star_def]
  refine Finset.sum_congr rfl fun r _ => ?_
  ring

theorem g79c_vn_state {d : ℕ} (S : FineResolution d) :
    vnEntropy S.state = -∑ r, S.weight r * Real.logb 2 (S.weight r) := by
  have hU := (Matrix.mem_unitaryGroup_iff').1 S.basis.2
  set U : Matrix (Fin d) (Fin d) ℂ := (S.basis : Matrix (Fin d) (Fin d) ℂ)
  have hU' : Uᴴ * U = 1 := hU
  set D := Matrix.diagonal (fun i => ((S.weight i : ℝ) : ℂ))
  have hst : S.state = U * D * Uᴴ := rfl
  have hD := g79c_diag_herm S.weight
  have hP : (U * D * Uᴴ).IsHermitian := by
    unfold Matrix.IsHermitian; rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose, hD.eq, Matrix.mul_assoc]
  have hpow : ∀ k : ℕ, (U * D * Uᴴ) ^ (k+1) = U * D ^ (k+1) * Uᴴ := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ, ih, pow_succ]
      calc U * D ^ (k + 1) * Uᴴ * (U * D * Uᴴ) = U * D ^ (k+1) * (Uᴴ * U) * D * Uᴴ := by
            simp only [Matrix.mul_assoc]
        _ = _ := by rw [hU', Matrix.mul_one, pow_succ D (k+1)]; simp only [Matrix.mul_assoc]
  unfold vnEntropy
  rw [hst, g79c_trace_cfc_eq (U * D * Uᴴ) D hP hD _ (by simp) (fun k => by
    rw [hpow, Matrix.trace_mul_cycle, hU', Matrix.one_mul])]
  rw [g79c_trace_cfc_diag]
  simp

theorem g79c_real {p : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1) :
    0 ≤ -Real.logb 2 p ∧ Real.sqrt (p * (1 - p)) * (-Real.logb 2 p) ≤ varianceConstant := by
  have hl : 0 ≤ -Real.logb 2 p := by
    have := Real.logb_nonpos (b := 2) (by norm_num) h0 h1; linarith
  refine ⟨hl, ?_⟩
  rcases h0.lt_or_eq with hp | hp
  · have hs : Real.sqrt (p * (1 - p)) ≤ Real.sqrt p := Real.sqrt_le_sqrt (by nlinarith)
    have hu : 0 < Real.sqrt p := Real.sqrt_pos.2 hp
    set u := Real.sqrt p
    have hpu : p = u ^ 2 := (Real.sq_sqrt h0).symm
    have hlog : Real.log p = 2 * Real.log u := by rw [hpu, Real.log_pow]; push_cast; ring
    have key : -(u * Real.log u) ≤ 1 / Real.exp 1 := by
      have := Real.log_le_sub_one_of_pos (x := 1 / (Real.exp 1 * u)) (by positivity)
      rw [Real.log_div (by norm_num) (by positivity), Real.log_one, Real.log_mul (by positivity) hu.ne',
        Real.log_exp] at this
      have h2 : -Real.log u ≤ 1 / (Real.exp 1 * u) := by linarith
      have h3 : u * (-Real.log u) ≤ u * (1 / (Real.exp 1 * u)) := mul_le_mul_of_nonneg_left h2 hu.le
      rw [show u * (1 / (Real.exp 1 * u)) = 1 / Real.exp 1 by field_simp] at h3
      linarith
    have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    calc Real.sqrt (p * (1 - p)) * (-Real.logb 2 p) ≤ u * (-Real.logb 2 p) := mul_le_mul_of_nonneg_right hs hl
      _ = 2 * (-(u * Real.log u)) / Real.log 2 := by
          rw [Real.logb, hlog]; ring
      _ ≤ 2 * (1 / Real.exp 1) / Real.log 2 := by gcongr
      _ = varianceConstant := by
          rw [varianceConstant, Real.logb, Real.log_exp]; ring
  · subst hp
    have : 0 ≤ varianceConstant := by
      rw [varianceConstant]; have := Real.logb_nonneg (b := 2) (by norm_num) (Real.one_le_exp (by norm_num : (0:ℝ) ≤ 1)); positivity
    simpa using this
section g79c_frame
variable {I ι : Type*} [Fintype I] [DecidableEq I] [Fintype ι] [DecidableEq ι]

theorem g79c_comb (A : ι → Matrix I I ℂ) (hmul : ∀ i j, A i * A j = if i = j then A i else 0)
    (f g : ι → ℂ) : (∑ i, f i • A i) * (∑ i, g i • A i) = ∑ i, (f i * g i) • A i := by
  rw [Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp_rw [smul_mul_smul, hmul]
  simp [smul_smul]

theorem g79c_psd_A (A : ι → Matrix I I ℂ) (hmul : ∀ i j, A i * A j = if i = j then A i else 0)
    (hherm : ∀ i, (A i)ᴴ = A i) (i : ι) : (A i).PosSemidef := by
  have : A i = (A i)ᴴ * A i := by rw [hherm, hmul]; simp
  rw [this]; exact Matrix.posSemidef_conjTranspose_mul_self _

theorem g79c_psd_comb (A : ι → Matrix I I ℂ) (hmul : ∀ i j, A i * A j = if i = j then A i else 0)
    (hherm : ∀ i, (A i)ᴴ = A i) (c : ι → ℝ) (hc : ∀ i, 0 ≤ c i) :
    (∑ i, ((c i : ℝ) : ℂ) • A i).PosSemidef := by
  apply Matrix.posSemidef_sum
  intro i _
  exact (g79c_psd_A A hmul hherm i).smul (by exact_mod_cast hc i)

theorem g79c_tr_comb (A : ι → Matrix I I ℂ) (htr : ∀ i, (A i).trace = 1) (f : ι → ℂ) :
    (∑ i, f i • A i).trace = ∑ i, f i := by
  rw [Matrix.trace_sum]; simp [Matrix.trace_smul, htr]

theorem g79c_b_bounds (A : ι → Matrix I I ℂ) (hmul : ∀ i j, A i * A j = if i = j then A i else 0)
    (hherm : ∀ i, (A i)ᴴ = A i) (htr : ∀ i, (A i).trace = 1) (B : Matrix I I ℂ) (hB : IsEffect B) (i : ι) :
    0 ≤ (A i * B).trace.re ∧ (A i * B).trace.re ≤ 1 := by
  have key : ∀ C : Matrix I I ℂ, C.PosSemidef → 0 ≤ (A i * C).trace.re := by
    intro C hC
    have h1 : (A i * C).trace = ((A i)ᴴ * C * A i).trace := by
      rw [hherm, Matrix.trace_mul_cycle, hmul]; simp
    rw [h1]
    have := (hC.conjTranspose_mul_mul_same (A i)).trace_nonneg
    exact (Complex.nonneg_iff.1 this).1
  refine ⟨key B hB.1, ?_⟩
  have := key (1 - B) hB.2
  rw [Matrix.mul_sub, Matrix.trace_sub, Matrix.mul_one, htr, Complex.sub_re, Complex.one_re] at this
  linarith
end g79c_frame

theorem g79c_fib {n a d : ℕ} (w : Fin n → Fin a) (j : Fin n → Fin d) (f : Fin a → Fin d → ℝ) :
    ∑ k, f (w k) (j k) = ∑ x, ∑ r, ((Finset.univ.filter fun t => w t = x ∧ j t = r).card : ℝ) * f x r := by
  rw [← Finset.sum_fiberwise (s := Finset.univ) (g := fun k => (w k, j k)) (f := fun k => f (w k) (j k)),
    Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun r _ => ?_
  rw [Finset.sum_congr rfl (g := fun _ => f x r) (fun k hk => by
    simp only [Finset.mem_filter, Prod.mk.injEq] at hk; rw [hk.2.1, hk.2.2])]
  simp [Prod.mk.injEq]

theorem g79c_dev {n a d : ℕ} (w : Fin n → Fin a) (j : Fin n → Fin d) (P : Fin a → Fin d → ℝ)
    (hP0 : ∀ x r, 0 ≤ P x r) (hP1 : ∀ x r, P x r ≤ 1) (δ : ℝ) (hδ : 0 < δ)
    (htyp : ∀ x r, |((Finset.univ.filter fun t => w t = x ∧ j t = r).card : ℝ) - count w x * P x r| ≤
        δ * Real.sqrt (count w x) * Real.sqrt (P x r * (1 - P x r))) :
    (∀ k, 0 < P (w k) (j k)) ∧
    |∑ k, (-Real.logb 2 (P (w k) (j k))) - ∑ x, (count w x : ℝ) * (-∑ r, P x r * Real.logb 2 (P x r))| ≤
      varianceConstant * d * Real.sqrt a * δ * Real.sqrt n := by
  constructor
  · intro k
    rcases (hP0 (w k) (j k)).lt_or_eq with h | h
    · exact h
    · exfalso
      have := htyp (w k) (j k)
      rw [← h] at this
      simp only [mul_zero, sub_zero, zero_mul, Real.sqrt_zero] at this
      have h0 : ((Finset.univ.filter fun t => w t = w k ∧ j t = j k).card : ℝ) = 0 := by
        have := abs_nonneg ((Finset.univ.filter fun t => w t = w k ∧ j t = j k).card : ℝ)
        have h2 := abs_eq_zero.1 (le_antisymm (by assumption) this)
        exact h2
      have h1 : k ∈ Finset.univ.filter fun t => w t = w k ∧ j t = j k := by simp
      have := Finset.card_pos.2 ⟨k, h1⟩
      have : (0:ℝ) < (Finset.univ.filter fun t => w t = w k ∧ j t = j k).card := by exact_mod_cast this
      linarith
  · set N : Fin a → Fin d → ℝ := fun x r => ((Finset.univ.filter fun t => w t = x ∧ j t = r).card : ℝ)
    set c : Fin a → ℝ := fun x => (count w x : ℝ)
    rw [g79c_fib w j (fun x r => -Real.logb 2 (P x r))]
    have heq : ∑ x, ∑ r, N x r * (-Real.logb 2 (P x r)) - ∑ x, c x * (-∑ r, P x r * Real.logb 2 (P x r))
        = ∑ x, ∑ r, (N x r - c x * P x r) * (-Real.logb 2 (P x r)) := by
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [neg_eq_neg_one_mul, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun r _ => ?_
      ring
    rw [heq]
    have hK : ∀ x r, |(N x r - c x * P x r) * (-Real.logb 2 (P x r))| ≤ δ * Real.sqrt (c x) * varianceConstant := by
      intro x r
      obtain ⟨hl, hv⟩ := g79c_real (hP0 x r) (hP1 x r)
      rw [abs_mul, abs_of_nonneg hl]
      calc |N x r - c x * P x r| * (-Real.logb 2 (P x r))
          ≤ (δ * Real.sqrt (c x) * Real.sqrt (P x r * (1 - P x r))) * (-Real.logb 2 (P x r)) :=
            mul_le_mul_of_nonneg_right (htyp x r) hl
        _ = δ * Real.sqrt (c x) * (Real.sqrt (P x r * (1 - P x r)) * (-Real.logb 2 (P x r))) := by ring
        _ ≤ δ * Real.sqrt (c x) * varianceConstant := by
            apply mul_le_mul_of_nonneg_left hv; positivity
    have hsum_c : ∑ x, c x = n := by
      have := Finset.sum_fiberwise (s := Finset.univ) (g := w) (f := fun _ => (1:ℝ))
      simp only [Finset.sum_const, nsmul_eq_mul, mul_one, Finset.card_univ, Fintype.card_fin] at this
      simpa [c, count] using this
    have hsqrt : ∑ x, Real.sqrt (c x) ≤ Real.sqrt a * Real.sqrt n := by
      rw [← Real.sqrt_mul (by positivity)]
      apply Real.le_sqrt_of_sq_le
      have := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin a))) (f := fun x => Real.sqrt (c x))
      simp only [Finset.card_univ, Fintype.card_fin] at this
      have h2 : ∑ x, Real.sqrt (c x) ^ 2 = n := by
        rw [← hsum_c]; refine Finset.sum_congr rfl fun x _ => ?_
        rw [Real.sq_sqrt (by positivity)]
      rw [h2] at this; exact this
    have hV0 : 0 ≤ varianceConstant := by
      rw [varianceConstant]; have := Real.logb_nonneg (b := 2) (by norm_num) (Real.one_le_exp (by norm_num : (0:ℝ) ≤ 1)); positivity
    calc |∑ x, ∑ r, (N x r - c x * P x r) * (-Real.logb 2 (P x r))|
        ≤ ∑ x, ∑ r, |(N x r - c x * P x r) * (-Real.logb 2 (P x r))| := by
          refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun x _ => ?_)
          exact Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ x : Fin a, ∑ r : Fin d, δ * Real.sqrt (c x) * varianceConstant :=
          Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun r _ => hK x r
      _ = varianceConstant * d * δ * ∑ x, Real.sqrt (c x) := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Finset.mul_sum]
          refine Finset.sum_congr rfl fun x _ => ?_; ring
      _ ≤ varianceConstant * d * δ * (Real.sqrt a * Real.sqrt n) := by
          apply mul_le_mul_of_nonneg_left hsqrt; positivity
      _ = _ := by ring

theorem g79c_count_comp {n d : ℕ} (j : Fin n → Fin d) (σ : Equiv.Perm (Fin n)) (r : Fin d) :
    count (j ∘ σ) r = count j r := by
  simp only [count, Function.comp]
  exact Finset.card_bij (fun k _ => σ k) (by simp) (fun a _ b _ h => σ.injective h)
    (fun b hb => ⟨σ.symm b, by simpa using hb, by simp⟩)

theorem g79c_exists_perm {n d : ℕ} (j0 j : Fin n → Fin d) (h : ∀ r, count j r = count j0 r) :
    ∃ σ : Equiv.Perm (Fin n), j0 ∘ σ = j := by
  have e : ∀ r, {a // j a = r} ≃ {b // j0 b = r} := fun r =>
    Fintype.equivOfCardEq (by rw [Fintype.card_subtype, Fintype.card_subtype]; exact h r)
  refine ⟨Equiv.ofFiberEquiv e, ?_⟩
  funext a
  exact Equiv.ofFiberEquiv_map e a

theorem g79c_card_type {n d : ℕ} (j0 : Fin n → Fin d) :
    (Finset.univ.filter (fun j : Fin n → Fin d => ∀ r, count j r = count j0 r)).card *
      ∏ r, (count j0 r).factorial = n.factorial := by
  set T := Finset.univ.filter (fun j : Fin n → Fin d => ∀ r, count j r = count j0 r) with hT
  have hstab : Fintype.card {g : Equiv.Perm (Fin n) // j0 ∘ g = j0} = ∏ r, (count j0 r).factorial := by
    rw [DomMulAct.stabilizer_card]
    refine Finset.prod_congr rfl fun r _ => ?_
    rw [Fintype.card_subtype]; rfl
  have hfib : ∀ j ∈ T, (Finset.univ.filter (fun σ : Equiv.Perm (Fin n) => j0 ∘ σ = j)).card
      = Fintype.card {g : Equiv.Perm (Fin n) // j0 ∘ g = j0} := by
    intro j hj
    simp only [hT, Finset.mem_filter] at hj
    obtain ⟨σ0, hσ0⟩ := g79c_exists_perm j0 j hj.2
    rw [Fintype.card_subtype]
    refine Finset.card_bij (fun σ _ => σ0.symm.trans σ) ?_ ?_ ?_
    · intro σ hσ
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hσ ⊢
      funext k
      have := congrFun hσ (σ0.symm k)
      have h2 := congrFun hσ0 (σ0.symm k)
      simp only [Function.comp, Equiv.apply_symm_apply] at this h2
      simp only [Function.comp, Equiv.trans_apply]
      rw [this, ← h2]
    · intro a _ b _ hab
      refine Equiv.ext fun k => ?_
      have := congrFun (congrArg (fun e : Equiv.Perm (Fin n) => (e : Fin n → Fin n)) hab) (σ0 k)
      simpa using this
    · intro g hg
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hg
      refine ⟨σ0.trans g, ?_, ?_⟩
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        funext k
        have := congrFun hg (σ0 k)
        simp only [Function.comp, Equiv.trans_apply] at this ⊢
        rw [this, ← hσ0]; rfl
      · ext k; simp
  have hcard : (Finset.univ : Finset (Equiv.Perm (Fin n))).card
      = ∑ j ∈ T, (Finset.univ.filter (fun σ : Equiv.Perm (Fin n) => j0 ∘ σ = j)).card := by
    apply Finset.card_eq_sum_card_fiberwise
    intro σ _
    simp only [hT, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq]
    exact fun r => g79c_count_comp j0 σ r
  rw [Finset.card_univ, Fintype.card_perm, Fintype.card_fin, Finset.sum_congr rfl hfib,
    Finset.sum_const, smul_eq_mul, hstab] at hcard
  exact hcard.symm

theorem g79c_fact_ineq (c c' : ℕ) : c.factorial * c ^ c' ≤ c'.factorial * c ^ c := by
  rcases le_total c' c with h | h
  · have h1 := Nat.factorial_mul_descFactorial (Nat.sub_le c c')
    have h2 := Nat.descFactorial_le_pow c (c - c')
    rw [Nat.sub_sub_self h] at h1
    calc c.factorial * c ^ c' = c'.factorial * c.descFactorial (c - c') * c ^ c' := by rw [h1]
      _ ≤ c'.factorial * c ^ (c - c') * c ^ c' := by gcongr
      _ = c'.factorial * c ^ c := by rw [mul_assoc, ← pow_add, Nat.sub_add_cancel h]
  · obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le h
    have h1 := Nat.factorial_mul_pow_le_factorial (m := c) (n := m)
    calc c.factorial * c ^ (c + m) = c.factorial * c ^ m * c ^ c := by rw [pow_add]; ring
      _ ≤ c.factorial * (c + 1) ^ m * c ^ c := by gcongr; omega
      _ ≤ (c + m).factorial * c ^ c := by gcongr

theorem g79c_sum_count {n d : ℕ} (j : Fin n → Fin d) : ∑ r, count j r = n := by
  have := Finset.card_eq_sum_card_fiberwise (s := Finset.univ) (t := Finset.univ) (f := j) (by simp)
  simpa [count] using this.symm

theorem g79c_type_lower {n d : ℕ} (hn : 0 < n) (j0 : Fin n → Fin d) :
    1 ≤ ((n:ℝ) + 1) ^ d * ((Finset.univ.filter (fun j : Fin n → Fin d => ∀ r, count j r = count j0 r)).card *
      ∏ r, ((count j0 r : ℝ) / n) ^ (count j0 r)) := by
  set T := Finset.univ.filter (fun j : Fin n → Fin d => ∀ r, count j r = count j0 r)
  set c := count j0
  have hc : ∑ r, c r = n := g79c_sum_count j0
  have hnR : (0:ℝ) < n := by exact_mod_cast hn
  have hT : T.card * ∏ r, (c r).factorial = n.factorial := g79c_card_type j0
  -- multinomial theorem
  have hmt := Finset.sum_pow_eq_sum_piAntidiag (Finset.univ : Finset (Fin d)) (fun r => (c r : ℝ) / n) n
  have hs1 : ∑ r, (c r : ℝ) / n = 1 := by
    rw [← Finset.sum_div, div_eq_one_iff_eq hnR.ne']; exact_mod_cast hc
  rw [hs1, one_pow] at hmt
  -- each term bounded
  have hterm : ∀ k ∈ Finset.piAntidiag (Finset.univ : Finset (Fin d)) n,
      (Nat.multinomial Finset.univ k : ℝ) * ∏ r, ((c r : ℝ) / n) ^ k r ≤ T.card * ∏ r, ((c r : ℝ) / n) ^ c r := by
    intro k hk
    rw [Finset.mem_piAntidiag] at hk
    have hks : ∑ r, k r = n := hk.1
    have hspec := Nat.multinomial_spec (s := Finset.univ) (f := k)
    rw [hks] at hspec
    have hnat : Nat.multinomial Finset.univ k * (∏ r, c r ^ k r) ≤ T.card * ∏ r, c r ^ c r := by
      have hpos : 0 < (∏ r, (c r).factorial) * ∏ r, (k r).factorial := by positivity
      refine le_of_mul_le_mul_right ?_ hpos
      have hprod : ∏ r, ((c r).factorial * c r ^ k r) ≤ ∏ r, ((k r).factorial * c r ^ c r) :=
        Finset.prod_le_prod' fun r _ => g79c_fact_ineq (c r) (k r)
      rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib] at hprod
      calc Nat.multinomial Finset.univ k * (∏ r, c r ^ k r) * ((∏ r, (c r).factorial) * ∏ r, (k r).factorial)
          = n.factorial * ((∏ r, (c r).factorial) * ∏ r, c r ^ k r) := by rw [← hspec]; ring
        _ ≤ n.factorial * ((∏ r, (k r).factorial) * ∏ r, c r ^ c r) := by gcongr
        _ = T.card * (∏ r, c r ^ c r) * ((∏ r, (c r).factorial) * ∏ r, (k r).factorial) := by
            rw [← hT]; ring
    have hdiv : ∀ m : Fin d → ℕ, ∑ r, m r = n → ∏ r, ((c r : ℝ) / n) ^ m r = (∏ r, (c r : ℝ) ^ m r) / (n:ℝ) ^ n := by
      intro m hm
      simp_rw [div_pow]
      rw [Finset.prod_div_distrib, Finset.prod_pow_eq_pow_sum, hm]
    rw [hdiv k hks, hdiv c hc, mul_div_assoc', mul_div_assoc']
    apply div_le_div_of_nonneg_right _ (by positivity)
    exact_mod_cast hnat
  have hcardk : ((Finset.piAntidiag (Finset.univ : Finset (Fin d)) n).card : ℝ) ≤ ((n:ℝ) + 1) ^ d := by
    have hsub : Finset.piAntidiag (Finset.univ : Finset (Fin d)) n ⊆ Fintype.piFinset (fun _ => Finset.range (n+1)) := by
      intro k hk
      rw [Finset.mem_piAntidiag] at hk
      rw [Fintype.mem_piFinset]
      intro r
      rw [Finset.mem_range, Nat.lt_succ_iff, ← hk.1]
      exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ r)
    have := Finset.card_le_card hsub
    rw [Fintype.card_piFinset] at this
    simp only [Finset.card_range, Finset.prod_const, Finset.card_univ, Fintype.card_fin] at this
    exact_mod_cast this
  have hnn : 0 ≤ (T.card : ℝ) * ∏ r, ((c r : ℝ) / n) ^ c r := by positivity
  calc (1:ℝ) = ∑ k ∈ Finset.piAntidiag (Finset.univ : Finset (Fin d)) n,
        (Nat.multinomial Finset.univ k : ℝ) * ∏ r, ((c r : ℝ) / n) ^ k r := hmt
    _ ≤ ∑ k ∈ Finset.piAntidiag (Finset.univ : Finset (Fin d)) n, (T.card : ℝ) * ∏ r, ((c r : ℝ) / n) ^ c r :=
        Finset.sum_le_sum hterm
    _ = ((Finset.piAntidiag (Finset.univ : Finset (Fin d)) n).card : ℝ) * ((T.card : ℝ) * ∏ r, ((c r : ℝ) / n) ^ c r) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right hcardk hnn
section G78A
open Polynomial
lemma g79c_cfc_diag {X : Type*} [Fintype X] [DecidableEq X] (d : X → ℝ) (f : ℝ → ℝ) :
    cfc f (Matrix.diagonal (fun i => (d i : ℂ))) = Matrix.diagonal (fun i => (f (d i) : ℂ)) := by
  set A := Matrix.diagonal (fun i => (d i : ℂ)) with hA
  have hsa : IsSelfAdjoint A := by
    rw [IsSelfAdjoint, Matrix.star_eq_conjTranspose, hA, Matrix.diagonal_conjTranspose]
    congr 1; funext i; simp
  set S : Finset ℝ := Finset.univ.image d
  let p : ℝ[X] := Lagrange.interpolate S id f
  have hp : ∀ i, p.eval (d i) = f (d i) := by
    intro i
    have := Lagrange.eval_interpolate_at_node (s := S) (v := id) (r := f) (i := d i)
      (Set.injOn_id _) (Finset.mem_image_of_mem d (Finset.mem_univ i))
    exact this
  have hspec : ∀ x ∈ spectrum ℝ A, ∃ i, d i = x := by
    intro x hx
    rw [← spectrum.preimage_algebraMap ℂ, Set.mem_preimage, hA, spectrum_diagonal,
      Set.mem_range] at hx
    obtain ⟨i, hi⟩ := hx
    exact ⟨i, by rw [Complex.coe_algebraMap] at hi; exact_mod_cast hi⟩
  have h1 : cfc f A = cfc p.eval A := by
    apply cfc_congr
    intro x hx
    obtain ⟨i, rfl⟩ := hspec x hx
    exact (hp i).symm
  rw [h1, cfc_polynomial p A]
  rw [hA, show Matrix.diagonal (fun i => (d i : ℂ)) =
    Matrix.diagonalAlgHom ℝ (fun i => (d i : ℂ)) from rfl, Polynomial.aeval_algHom_apply]
  rw [show Matrix.diagonal (fun i => (f (d i) : ℂ)) =
    Matrix.diagonalAlgHom ℝ (fun i => (f (d i) : ℂ)) from rfl]
  congr 1
  funext i
  rw [Polynomial.aeval_pi_apply₂]
  rw [show ((d i : ℝ) : ℂ) = algebraMap ℝ ℂ (d i) from rfl, Polynomial.aeval_algebraMap_apply,
    Polynomial.aeval_def, Algebra.algebraMap_self, ← Polynomial.eval, hp]
  rfl
end G78A

theorem g79c_cfc_conj {d : ℕ} (S : FineResolution d) (v : Fin d → ℝ) (f : ℝ → ℝ) :
    cfc f ((S.basis : Matrix (Fin d) (Fin d) ℂ) * Matrix.diagonal (fun i => (v i : ℂ)) *
      (S.basis : Matrix (Fin d) (Fin d) ℂ)ᴴ) =
    (S.basis : Matrix (Fin d) (Fin d) ℂ) * Matrix.diagonal (fun i => (f (v i) : ℂ)) *
      (S.basis : Matrix (Fin d) (Fin d) ℂ)ᴴ := by
  set u : unitary (Matrix (Fin d) (Fin d) ℂ) := S.basis
  set U : Matrix (Fin d) (Fin d) ℂ := (S.basis : Matrix (Fin d) (Fin d) ℂ)
  set D := Matrix.diagonal (fun i => (v i : ℂ))
  set φ := Unitary.conjStarAlgAut ℝ (Matrix (Fin d) (Fin d) ℂ) u
  have hφ : ∀ x, φ x = U * x * Uᴴ := by
    intro x; simp [φ, Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose, U, u]
  have hDsa : IsSelfAdjoint D := by
    rw [IsSelfAdjoint, Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose]
    congr 1; funext i; simp
  have hPsa : IsSelfAdjoint (U * D * Uᴴ) := by
    rw [IsSelfAdjoint, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose, show Dᴴ = D from hDsa, Matrix.mul_assoc]
  have hfin : (spectrum ℝ (U * D * Uᴴ)).Finite := Matrix.finite_real_spectrum
  set T : Finset ℝ := hfin.toFinset ∪ Finset.univ.image v
  set p : Polynomial ℝ := Lagrange.interpolate T id f
  have hp : ∀ x ∈ T, p.eval x = f x := by
    intro x hx
    exact Lagrange.eval_interpolate_at_node (s := T) (v := id) f (Set.injOn_id _) hx
  have h1 : cfc f (U * D * Uᴴ) = Polynomial.aeval (U * D * Uᴴ) p := by
    rw [← cfc_polynomial p (U * D * Uᴴ) hPsa]
    apply cfc_congr
    intro x hx
    exact (hp x (by simp [T, hx])).symm
  have h2 : Polynomial.aeval D p = Matrix.diagonal (fun i => (f (v i) : ℂ)) := by
    rw [← cfc_polynomial p D hDsa, g79c_cfc_diag]
    congr 1; funext i
    rw [hp (v i) (by simp [T])]
  have h3 : Polynomial.aeval (U * D * Uᴴ) p = U * Polynomial.aeval D p * Uᴴ := by
    rw [← hφ, ← hφ]
    exact Polynomial.aeval_algHom_apply (φ : Matrix (Fin d) (Fin d) ℂ →ₐ[ℝ] Matrix (Fin d) (Fin d) ℂ) D p
  rw [h1, h3, h2]

theorem g79c_conj_density {d : ℕ} (U : Matrix (Fin d) (Fin d) ℂ) (hU : Uᴴ * U = 1) (w : Fin d → ℝ)
    (h0 : ∀ i, 0 ≤ w i) (h1 : ∑ i, w i = 1) :
    IsDensityMatrix (U * Matrix.diagonal (fun i => (w i : ℂ)) * Uᴴ) := by
  refine ⟨(Matrix.PosSemidef.diagonal (fun i => by simpa using h0 i)).mul_mul_conjTranspose_same U, ?_⟩
  rw [Matrix.trace_mul_cycle, hU, Matrix.one_mul, Matrix.trace_diagonal]
  exact_mod_cast h1

theorem g79c_trace_conj {d : ℕ} (U : Matrix (Fin d) (Fin d) ℂ) (hU : Uᴴ * U = 1) (M : Matrix (Fin d) (Fin d) ℂ) :
    (U * M * Uᴴ).trace = M.trace := by
  rw [Matrix.trace_mul_cycle, hU, Matrix.one_mul]

theorem g79c_relbits {d : ℕ} (S : FineResolution d) (nu : PMF (Fin d)) :
    relativeBits (changeSpectrum S nu).state S.state =
      if (∀ r, S.weight r = 0 → (nu r).toReal = 0) then
        ENNReal.ofReal (∑ r, ((nu r).toReal * Real.log (nu r).toReal - (nu r).toReal * Real.log (S.weight r))) /
          ENNReal.ofReal (Real.log 2)
      else ⊤ := by
  have hUu := (Matrix.mem_unitaryGroup_iff').1 S.basis.2
  set U : Matrix (Fin d) (Fin d) ℂ := (S.basis : Matrix (Fin d) (Fin d) ℂ) with hUdef
  have hU : Uᴴ * U = 1 := hUu
  set ν : Fin d → ℝ := fun r => (nu r).toReal with hν
  set p : Fin d → ℝ := S.weight with hp
  have hσ : (changeSpectrum S nu).state = U * Matrix.diagonal (fun i => (ν i : ℂ)) * Uᴴ := rfl
  have hρ : S.state = U * Matrix.diagonal (fun i => (p i : ℂ)) * Uᴴ := rfl
  have hν0 : ∀ i, 0 ≤ ν i := fun i => ENNReal.toReal_nonneg
  have hν1 : ∑ i, ν i = 1 := (changeSpectrum S nu).total
  have hdσ : IsDensityMatrix (changeSpectrum S nu).state := by
    rw [hσ]; exact g79c_conj_density U hU ν hν0 hν1
  have hdρ : IsDensityMatrix S.state := by
    rw [hρ]; exact g79c_conj_density U hU p S.nonneg S.total
  unfold relativeBits
  rw [dif_pos ⟨hdσ, hdρ⟩]
  unfold QAlgorithms.QuantumLoss.umegakiEntropy
  have hker : (LinearMap.ker S.state.mulVecLin ≤ LinearMap.ker (changeSpectrum S nu).state.mulVecLin) ↔
      (∀ r, p r = 0 → ν r = 0) := by
    rw [hσ, hρ]
    have e : ∀ (D : Matrix (Fin d) (Fin d) ℂ) y, (U * D * Uᴴ) *ᵥ y = U *ᵥ (D *ᵥ (Uᴴ *ᵥ y)) := by
      intro D y; rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc]
    have cancel : ∀ z, Uᴴ *ᵥ (U *ᵥ z) = z := by
      intro z; rw [Matrix.mulVec_mulVec, hU, Matrix.one_mulVec]
    have dsingle : ∀ (w : Fin d → ℝ) (r : Fin d), Matrix.diagonal (fun i => (w i : ℂ)) *ᵥ Pi.single r 1
        = Pi.single r (w r : ℂ) := by
      intro w r; funext i
      rw [Matrix.mulVec_diagonal]
      by_cases hi : i = r
      · subst hi; simp
      · simp [Pi.single_apply, hi]
    constructor
    · intro h r hr
      set x : Fin d → ℂ := U *ᵥ Pi.single r 1
      have hx : x ∈ LinearMap.ker (U * Matrix.diagonal (fun i => (p i : ℂ)) * Uᴴ).mulVecLin := by
        simp only [LinearMap.mem_ker, Matrix.mulVecLin_apply, x]
        rw [e, cancel, dsingle, hr]; simp
      have := h hx
      simp only [LinearMap.mem_ker, Matrix.mulVecLin_apply, x] at this
      rw [e, cancel, dsingle] at this
      have h2 := congrArg (fun y => Uᴴ *ᵥ y) this
      simp only [cancel, Matrix.mulVec_zero] at h2
      have h3 := congrFun h2 r
      simpa using h3
    · intro h x hx
      simp only [LinearMap.mem_ker, Matrix.mulVecLin_apply] at hx ⊢
      rw [e] at hx ⊢
      have h2 := congrArg (fun y => Uᴴ *ᵥ y) hx
      simp only [cancel, Matrix.mulVec_zero] at h2
      have h3 : Matrix.diagonal (fun i => (ν i : ℂ)) *ᵥ (Uᴴ *ᵥ x) = 0 := by
        funext i
        have := congrFun h2 i
        rw [Matrix.mulVec_diagonal] at this ⊢
        simp only [Pi.zero_apply] at this ⊢
        rcases mul_eq_zero.1 this with h4 | h4
        · rw [h i (by exact_mod_cast h4)]; simp
        · rw [h4, mul_zero]
      rw [h3, Matrix.mulVec_zero]
  by_cases hs : ∀ r, p r = 0 → ν r = 0
  · rw [if_pos (hker.2 hs), if_pos hs]
    congr 2
    rw [hσ, hρ, g79c_cfc_conj, g79c_cfc_conj]
    have : U * Matrix.diagonal (fun i => ((ν i * Real.log (ν i) : ℝ) : ℂ)) * Uᴴ -
        U * Matrix.diagonal (fun i => (ν i : ℂ)) * Uᴴ * (U * Matrix.diagonal (fun i => (Real.log (p i) : ℂ)) * Uᴴ)
        = U * Matrix.diagonal (fun i => ((ν i * Real.log (ν i) - ν i * Real.log (p i) : ℝ) : ℂ)) * Uᴴ := by
      rw [show U * Matrix.diagonal (fun i => (ν i : ℂ)) * Uᴴ * (U * Matrix.diagonal (fun i => (Real.log (p i) : ℂ)) * Uᴴ)
          = U * (Matrix.diagonal (fun i => (ν i : ℂ)) * Matrix.diagonal (fun i => (Real.log (p i) : ℂ))) * Uᴴ by
          simp only [Matrix.mul_assoc]; rw [← Matrix.mul_assoc Uᴴ U, hU, Matrix.one_mul]]
      rw [Matrix.diagonal_mul_diagonal, ← Matrix.sub_mul, ← Matrix.mul_sub, Matrix.diagonal_sub]
      congr 3; funext i; push_cast; ring
    rw [this, g79c_trace_conj U hU, Matrix.trace_diagonal, Complex.re_sum]
    simp only [Complex.ofReal_re, Finset.sum_sub_distrib]
    rfl
  · rw [if_neg (fun h => hs (hker.1 h)), if_neg hs]
    exact ENNReal.top_div_of_ne_top ENNReal.ofReal_ne_top

/-- Corollary II.13, PDF p.31: the nonzero exact-type projector guard is explicit.
A simultaneous fine basis represents every commuting pair, including degeneracies;
unsupported nu has divergence +infinity and contributes zero. -/
theorem solution {d : ℕ} (rho : FineResolution d) (nu : PMF (Fin d))
    (n : ℕ) (hn : 0 < n)
    (hrealizable : varianceProjector (changeSpectrum rho nu) n 0 ≠ 0) :
    let Pi := varianceProjector (changeSpectrum rho nu) n 0
    let tail := divergenceTail n (relativeBits (changeSpectrum rho nu).state rho.state)
    (n + 1 : ℝ)^(-(d : ℤ)) * tail ≤ effectProb (copies n rho.state) Pi ∧
    effectProb (copies n rho.state) Pi ≤ tail := by
  intro Pi tail
  set A : (Fin n → Fin d) → Matrix (Fin n → Fin d) (Fin n → Fin d) ℂ :=
    fun j => wordTensor (fun k => rho.atom (j k)) with hA
  have hmul : ∀ i j, A i * A j = if i = j then A i else 0 := by
    intro i j; simp only [hA]; rw [g79c_wt_mul]; simp_rw [g79c_atom_mul]
    split_ifs with hij
    · subst hij; simp
    · obtain ⟨k, hk⟩ : ∃ k, i k ≠ j k := by
        by_contra h'; push_neg at h'; exact hij (funext h')
      ext x y; simp only [wordTensor, Matrix.zero_apply]
      exact Finset.prod_eq_zero (Finset.mem_univ k) (by simp [hk])
  have htr : ∀ i, (A i).trace = 1 := by
    intro i; simp only [hA]; rw [g79c_wt_trace]; simp [g79c_atom_tr]
  set ν : Fin d → ℝ := fun r => (nu r).toReal with hνdef
  set p : Fin d → ℝ := rho.weight with hpdef
  have hν0 : ∀ r, 0 ≤ ν r := fun r => ENNReal.toReal_nonneg
  have hν1 : ∑ r, ν r = 1 := (changeSpectrum rho nu).total
  have hlaw' : ∀ r, ((changeSpectrum rho nu).law r).toReal = ν r := by
    intro r
    simp [FineResolution.law, ENNReal.toReal_ofReal ((changeSpectrum rho nu).nonneg r), changeSpectrum, hνdef]
  set typ := varianceSet (changeSpectrum rho nu).law n 0 with htypdef
  have hmem : ∀ j, j ∈ typ ↔ ∀ r, (count j r : ℝ) = n * ν r := by
    intro j
    simp only [htypdef, varianceSet, Finset.mem_filter, Finset.mem_univ, true_and, zero_mul,
      abs_nonpos_iff, sub_eq_zero, hlaw']
  have hPi : Pi = ∑ j ∈ typ, A j := rfl
  obtain ⟨j0, hj0⟩ : typ.Nonempty := by
    by_contra hne
    rw [Finset.not_nonempty_iff_eq_empty] at hne
    exact hrealizable (by show (∑ j ∈ typ, A j) = 0; rw [hne, Finset.sum_empty])
  set c := count j0 with hcdef
  have hc : ∀ r, (c r : ℝ) = n * ν r := (hmem j0).1 hj0
  have hnR : (0:ℝ) < n := by exact_mod_cast hn
  have hνc : ∀ r, ν r = c r / n := fun r => by rw [hc r]; field_simp
  have hmem2 : ∀ j ∈ typ, ∀ r, count j r = c r := by
    intro j hj r
    have := (hmem j).1 hj r
    rw [← hc r] at this; exact_mod_cast this
  have htypeq : typ = Finset.univ.filter (fun j : Fin n → Fin d => ∀ r, count j r = count j0 r) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro hj r; exact hmem2 j hj r
    · intro hj; rw [hmem]; intro r; rw [← hc r]; exact_mod_cast hj r
  have hprodpow : ∀ (f : Fin d → ℝ) (j : Fin n → Fin d), ∏ k, f (j k) = ∏ r, f r ^ count j r := by
    intro f j
    rw [← Finset.prod_fiberwise (s := Finset.univ) (g := j) (f := fun k => f (j k))]
    refine Finset.prod_congr rfl fun r _ => ?_
    rw [Finset.prod_congr rfl (g := fun _ => f r) (fun k hk => by simp only [Finset.mem_filter] at hk; rw [hk.2]),
      Finset.prod_const]
    rfl
  -- effect probability
  have hcopies : copies n rho.state = ∑ j, ((∏ k, p (j k) : ℝ) : ℂ) • A j := by
    have : copies n rho.state = wordTensor (fun _ : Fin n => rho.state) := by
      ext a b; rfl
    rw [this]
    simp_rw [g79c_state_eq]
    rw [g79c_wt_expand]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [hpdef, Complex.ofReal_prod]
    rfl
  set E := effectProb (copies n rho.state) Pi with hEdef
  have hE : E = typ.card * ∏ r, p r ^ c r := by
    simp only [hEdef, effectProb]
    have hPi2 : Pi = ∑ j, ((if j ∈ typ then (1:ℝ) else 0 : ℝ) : ℂ) • A j := by
      rw [hPi]
      have : ∀ j, ((if j ∈ typ then (1:ℝ) else 0 : ℝ) : ℂ) • A j = if j ∈ typ then A j else 0 := by
        intro j; split_ifs <;> simp
      simp_rw [this]; rw [Finset.sum_ite_mem, Finset.univ_inter]
    rw [hcopies, hPi2, g79c_comb A hmul, g79c_tr_comb A htr]
    simp only [Complex.re_sum, ← Complex.ofReal_mul, Complex.ofReal_re]
    have : ∀ j, (∏ k, p (j k)) * (if j ∈ typ then (1:ℝ) else 0) = if j ∈ typ then ∏ r, p r ^ c r else 0 := by
      intro j; split_ifs with hj
      · rw [mul_one, hprodpow]; refine Finset.prod_congr rfl fun r _ => ?_; rw [hmem2 j hj r]
      · simp
    simp_rw [this]; rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul]
  have hνsum : (typ.card : ℝ) * ∏ r, ν r ^ c r ≤ 1 := by
    have h1 : ∑ j : Fin n → Fin d, ∏ k, ν (j k) = 1 := by
      rw [← Fintype.prod_sum (fun _ r => ν r)]; simp [hν1]
    have h2 : ∑ j ∈ typ, ∏ k, ν (j k) = typ.card * ∏ r, ν r ^ c r := by
      rw [Finset.sum_congr rfl (g := fun _ => ∏ r, ν r ^ c r) (fun j hj => by
        rw [hprodpow]; refine Finset.prod_congr rfl fun r _ => ?_; rw [hmem2 j hj r]),
        Finset.sum_const, nsmul_eq_mul]
    rw [← h2, ← h1]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun j _ _ => Finset.prod_nonneg fun k _ => hν0 _)
  have hlow := g79c_type_lower hn j0
  rw [← htypeq] at hlow
  simp only [← hcdef] at hlow
  simp_rw [← hνc] at hlow
  have hzpow : ((n:ℝ) + 1) ^ (-(d:ℤ)) = (((n:ℝ) + 1) ^ d)⁻¹ := by
    rw [zpow_neg, zpow_natCast]
  have hpos1 : (0:ℝ) < ((n:ℝ) + 1) ^ d := by positivity
  show ((n:ℝ) + 1) ^ (-(d:ℤ)) * tail ≤ E ∧ E ≤ tail
  simp only [tail]
  rw [g79c_relbits]
  by_cases hs : ∀ r, rho.weight r = 0 → (nu r).toReal = 0
  · rw [if_pos hs]
    set K := ∑ r, ((nu r).toReal * Real.log (nu r).toReal - (nu r).toReal * Real.log (rho.weight r)) with hK
    have hK0 : 0 ≤ K := by
      have hterm : ∀ r, ν r - p r ≤ (nu r).toReal * Real.log (nu r).toReal - (nu r).toReal * Real.log (rho.weight r) := by
        intro r
        change ν r - p r ≤ ν r * Real.log (ν r) - ν r * Real.log (p r)
        rcases (hν0 r).lt_or_eq with hpos | h0
        · have hp : 0 < p r := by
            rcases (rho.nonneg r).lt_or_eq with h | h
            · exact h
            · exact absurd (hs r h.symm) hpos.ne'
          have := Real.log_le_sub_one_of_pos (x := p r / ν r) (by positivity)
          rw [Real.log_div hp.ne' hpos.ne'] at this
          have h2 : ν r * (Real.log (p r) - Real.log (ν r)) ≤ ν r * (p r / ν r - 1) :=
            mul_le_mul_of_nonneg_left this hpos.le
          have h3 : ν r * (p r / ν r - 1) = p r - ν r := by field_simp
          rw [h3] at h2
          linarith [h2, mul_sub (ν r) (Real.log (p r)) (Real.log (ν r))]
        · rw [← h0]; simp; exact rho.nonneg r
      have := Finset.sum_le_sum fun r (_ : r ∈ Finset.univ) => hterm r
      rw [Finset.sum_sub_distrib, hν1] at this
      have hp1 : ∑ r, p r = 1 := rho.total
      rw [hp1] at this
      linarith
    have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    rw [← ENNReal.ofReal_div_of_pos hl2]
    have htail : divergenceTail n (ENNReal.ofReal (K / Real.log 2)) = Real.exp (-(n * K)) := by
      simp only [divergenceTail, ENNReal.ofReal_ne_top, if_false, exp2]
      rw [ENNReal.toReal_ofReal (div_nonneg hK0 hl2.le), Real.rpow_def_of_pos (by norm_num)]
      congr 1; field_simp
    rw [htail]
    have hkey : ∏ r, p r ^ c r = (∏ r, ν r ^ c r) * Real.exp (-(n * K)) := by
      have hr : ∀ r, p r ^ c r = ν r ^ c r * Real.exp (c r * (Real.log (p r) - Real.log (ν r))) := by
        intro r
        rcases Nat.eq_zero_or_pos (c r) with h0 | hcpos
        · rw [h0]; simp
        · have hcpos' : (0:ℝ) < c r := by exact_mod_cast hcpos
          have hνpos : 0 < ν r := by rw [hνc r]; positivity
          have hp : 0 < p r := by
            rcases (rho.nonneg r).lt_or_eq with h | h
            · exact h
            · exact absurd (hs r h.symm) hνpos.ne'
          have e1 : Real.exp (c r * Real.log (p r)) = p r ^ c r := by rw [Real.exp_nat_mul, Real.exp_log hp]
          have e2 : Real.exp (c r * Real.log (ν r)) = ν r ^ c r := by rw [Real.exp_nat_mul, Real.exp_log hνpos]
          have hne : ν r ^ c r ≠ 0 := pow_ne_zero _ hνpos.ne'
          rw [mul_sub, Real.exp_sub, e1, e2]
          field_simp
      rw [Finset.prod_congr rfl fun r _ => hr r, Finset.prod_mul_distrib, ← Real.exp_sum]
      congr 2
      rw [hK, Finset.mul_sum, ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun r _ => ?_
      rw [hc r]; change _ = -(n * (ν r * Real.log (ν r) - ν r * Real.log (p r))); ring
    rw [hE, hkey]
    have hexp : 0 < Real.exp (-(n * K)) := Real.exp_pos _
    constructor
    · rw [hzpow, ← mul_assoc]
      apply mul_le_mul_of_nonneg_right _ hexp.le
      rw [inv_le_iff_one_le_mul₀' hpos1]
      simpa [mul_assoc] using hlow
    · calc (typ.card : ℝ) * ((∏ r, ν r ^ c r) * Real.exp (-(n * K)))
          = ((typ.card : ℝ) * ∏ r, ν r ^ c r) * Real.exp (-(n * K)) := by ring
        _ ≤ 1 * Real.exp (-(n * K)) := mul_le_mul_of_nonneg_right hνsum hexp.le
        _ = _ := one_mul _
  · rw [if_neg hs]
    push_neg at hs
    obtain ⟨r, hpr, hνr⟩ := hs
    have hE0 : E = 0 := by
      rw [hE]
      have hcr : c r ≠ 0 := by
        intro h0; apply hνr; change ν r = 0; rw [hνc r, h0]; simp
      apply mul_eq_zero_of_right
      apply Finset.prod_eq_zero (Finset.mem_univ r)
      change p r ^ c r = 0
      rw [show p r = 0 from hpr]; exact zero_pow hcr
    rw [hE0]
    simp [divergenceTail]



end
