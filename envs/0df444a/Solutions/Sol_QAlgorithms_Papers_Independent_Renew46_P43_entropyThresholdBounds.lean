-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Renew46.P43.entropyThresholdBounds
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T08:48:31.517998+00:00
-- url     : https://prove2.me/submissions/6da64cb7-0f77-44a8-9b86-8448876123db

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

theorem g79c_relbits2 {d : ℕ} (S T : FineResolution d) (hb : T.basis = S.basis) :
    relativeBits T.state S.state =
      if (∀ r, S.weight r = 0 → T.weight r = 0) then
        ENNReal.ofReal (∑ r, (T.weight r * Real.log (T.weight r) - T.weight r * Real.log (S.weight r))) /
          ENNReal.ofReal (Real.log 2)
      else ⊤ := by
  have hUu := (Matrix.mem_unitaryGroup_iff').1 S.basis.2
  set U : Matrix (Fin d) (Fin d) ℂ := (S.basis : Matrix (Fin d) (Fin d) ℂ) with hUdef
  have hU : Uᴴ * U = 1 := hUu
  set ν : Fin d → ℝ := T.weight with hν
  set p : Fin d → ℝ := S.weight with hp
  have hσ : T.state = U * Matrix.diagonal (fun i => (ν i : ℂ)) * Uᴴ := by
    simp only [FineResolution.state, QAlgorithms.Papers.Independent.Dependency50.P19.Spectrum.density,
      QAlgorithms.conjSuperop, hUdef, hν, hb]
  have hρ : S.state = U * Matrix.diagonal (fun i => (p i : ℂ)) * Uᴴ := rfl
  have hν0 : ∀ i, 0 ≤ ν i := T.nonneg
  have hν1 : ∑ i, ν i = 1 := T.total
  have hdσ : IsDensityMatrix T.state := by
    rw [hσ]; exact g79c_conj_density U hU ν hν0 hν1
  have hdρ : IsDensityMatrix S.state := by
    rw [hρ]; exact g79c_conj_density U hU p S.nonneg S.total
  unfold relativeBits
  rw [dif_pos ⟨hdσ, hdρ⟩]
  unfold QAlgorithms.QuantumLoss.umegakiEntropy
  have hker : (LinearMap.ker S.state.mulVecLin ≤ LinearMap.ker T.state.mulVecLin) ↔
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
  · rw [if_neg (fun h => hs (hker.1 h)), if_neg hs]
    exact ENNReal.top_div_of_ne_top ENNReal.ofReal_ne_top


theorem g79c_ct_prod {n a d : ℕ} (w : Fin n → Fin a) (j : Fin n → Fin d) (f : Fin a → Fin d → ℝ) :
    ∏ k, f (w k) (j k) = ∏ x, ∏ s, f x s ^ (Finset.univ.filter fun t => w t = x ∧ j t = s).card := by
  rw [← Finset.prod_fiberwise (s := Finset.univ) (g := fun k => (w k, j k)) (f := fun k => f (w k) (j k)),
    Fintype.prod_prod_type]
  refine Finset.prod_congr rfl fun x _ => Finset.prod_congr rfl fun s _ => ?_
  rw [Finset.prod_congr rfl (g := fun _ => f x s) (fun k hk => by
    simp only [Finset.mem_filter, Prod.mk.injEq] at hk; rw [hk.2.1, hk.2.2]), Finset.prod_const]
  simp [Prod.mk.injEq]

theorem g79c_ct_sum {n a d : ℕ} (w : Fin n → Fin a) (j : Fin n → Fin d) (x : Fin a) :
    ∑ s, (Finset.univ.filter fun t => w t = x ∧ j t = s).card = count w x := by
  have := Finset.card_eq_sum_card_fiberwise (s := Finset.univ.filter fun t => w t = x) (t := Finset.univ)
    (f := j) (by simp)
  simp only [Finset.filter_filter] at this
  simpa [count] using this.symm

theorem g79c_pow_exp {m : ℕ} {Q p : ℝ} (hQ : m ≠ 0 → 0 < Q) (hp : m ≠ 0 → 0 < p) :
    p ^ m = Q ^ m * Real.exp (m * (Real.log p - Real.log Q)) := by
  rcases Nat.eq_zero_or_pos m with h0 | hm
  · subst h0; simp
  · have hQ' := hQ hm.ne'; have hp' := hp hm.ne'
    have e1 : Real.exp (m * Real.log p) = p ^ m := by rw [Real.exp_nat_mul, Real.exp_log hp']
    have e2 : Real.exp (m * Real.log Q) = Q ^ m := by rw [Real.exp_nat_mul, Real.exp_log hQ']
    have hne : Q ^ m ≠ 0 := pow_ne_zero _ hQ'.ne'
    rw [mul_sub, Real.exp_sub, e1, e2]; field_simp

theorem g79c_pow_exp1 {m : ℕ} {Q : ℝ} (hQ : m ≠ 0 → 0 < Q) :
    Q ^ m = Real.exp (m * Real.log Q) := by
  rcases Nat.eq_zero_or_pos m with h0 | hm
  · subst h0; simp
  · rw [Real.exp_nat_mul, Real.exp_log (hQ hm.ne')]

theorem g79c_gibbs_term {q p : ℝ} (hq : 0 ≤ q) (hp : 0 ≤ p) (hs : p = 0 → q = 0) :
    q - p ≤ q * Real.log q - q * Real.log p := by
  rcases hq.lt_or_eq with hpos | h0
  · have hp' : 0 < p := by
      rcases hp.lt_or_eq with h | h
      · exact h
      · exact absurd (hs h.symm) hpos.ne'
    have := Real.log_le_sub_one_of_pos (x := p / q) (by positivity)
    rw [Real.log_div hp'.ne' hpos.ne'] at this
    have h2 : q * (Real.log p - Real.log q) ≤ q * (p / q - 1) := mul_le_mul_of_nonneg_left this hpos.le
    have h3 : q * (p / q - 1) = p - q := by field_simp
    rw [h3] at h2
    linarith [h2, mul_sub q (Real.log p) (Real.log q)]
  · rw [← h0]; simp; exact hp

theorem g79c_tail_anti (n : ℕ) {D1 D2 : ℝ≥0∞} (h : D1 ≤ D2) : divergenceTail n D2 ≤ divergenceTail n D1 := by
  unfold divergenceTail
  by_cases h2 : D2 = ⊤
  · rw [if_pos h2]; split_ifs
    · exact le_rfl
    · rw [exp2]; positivity
  · have h1 : D1 ≠ ⊤ := ne_top_of_le_ne_top h2 h
    rw [if_neg h2, if_neg h1, exp2, exp2]
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    have := ENNReal.toReal_mono h2 h
    have hn : (0:ℝ) ≤ n := by positivity
    nlinarith

theorem g79c_tail_nonneg (n : ℕ) (D : ℝ≥0∞) : 0 ≤ divergenceTail n D := by
  unfold divergenceTail; split_ifs
  · exact le_rfl
  · rw [exp2]; positivity

theorem g79c_card_types {n a d : ℕ} (w : Fin n → Fin a) :
    ((Finset.univ.image (fun j : Fin n → Fin d => fun x r =>
      (Finset.univ.filter fun t => w t = x ∧ j t = r).card)).card : ℝ) ≤ ((n:ℝ) + 1) ^ (a * d) := by
  have hsub : Finset.univ.image (fun j : Fin n → Fin d => fun x r =>
      (Finset.univ.filter fun t => w t = x ∧ j t = r).card) ⊆
      Fintype.piFinset (fun _ : Fin a => Fintype.piFinset (fun _ : Fin d => Finset.range (n+1))) := by
    intro f hf
    simp only [Finset.mem_image, Finset.mem_univ, true_and] at hf
    obtain ⟨j, rfl⟩ := hf
    simp only [Fintype.mem_piFinset, Finset.mem_range]
    intro x r
    have := Finset.card_le_univ (Finset.univ.filter fun t => w t = x ∧ j t = r)
    simp only [Fintype.card_fin] at this
    omega
  have := Finset.card_le_card hsub
  rw [Fintype.card_piFinset] at this
  simp only [Fintype.card_piFinset, Finset.card_range, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin] at this
  rw [← pow_mul, mul_comm d a] at this
  exact_mod_cast this

theorem g79c_cond {a d n : ℕ} (ha : 0 < a) (hd : 0 < d) (hn : 0 < n)
    (W : FiniteChannel a (fullAlgebra d hd)) (S : Fin a → FineResolution d)
    (hS : ∀ x, (S x).state = W.state x)
    (w : Fin n → Fin a) (P : PMF (Fin a))
    (htype : ∀ x, empiricalWeight w x = (P x).toReal) (L : ℝ) :
    (lowConditionalProjector S w L).trace.re ≤ (n+1 : ℝ)^(a*d) * exp2 (n * L) ∧
    effectProb (wordTensor (fun i => W.state (w i))) (lowConditionalProjector S w L) ≥
      1 - (n+1 : ℝ)^(a*d) * divergenceTail n (individualExponent W P L) := by
  set A : (Fin n → Fin d) → Matrix (Fin n → Fin d) (Fin n → Fin d) ℂ :=
    fun j => wordTensor (fun k => (S (w k)).atom (j k)) with hA
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
  set ct : (Fin n → Fin d) → Fin a → Fin d → ℕ :=
    fun j x s => (Finset.univ.filter fun t => w t = x ∧ j t = s).card with hct
  set Ty := Finset.univ.image ct with hTy
  set T : (Fin a → Fin d → ℕ) → Finset (Fin n → Fin d) := fun r => Finset.univ.filter (fun j => ct j = r) with hT
  have hCEP : ∀ r, conditionalExactProjector S w r = ∑ j ∈ T r, A j := by
    intro r
    unfold conditionalExactProjector
    congr 1
    ext j
    simp only [hT, hct, Finset.mem_filter, Finset.mem_univ, true_and, funext_iff]
  set low : (Fin a → Fin d → ℕ) → Prop := fun r =>
    (∑ x, empiricalWeight w x * vnEntropy (conditionalTypeState S w r x)) ≤ L with hlow
  set R := Ty.filter low with hR
  have hPi : lowConditionalProjector S w L = ∑ r ∈ R, ∑ j ∈ T r, A j := by
    unfold lowConditionalProjector
    simp_rw [hCEP]
    rfl
  set N : Fin a → ℕ := fun x => count w x with hN
  have hnR : (0:ℝ) < n := by exact_mod_cast hn
  have hNsum : ∀ j x, ∑ s, ct j x s = N x := fun j x => g79c_ct_sum w j x
  have hrle : ∀ r ∈ Ty, ∀ x s, r x s ≤ N x := by
    intro r hr x s
    simp only [hTy, Finset.mem_image, Finset.mem_univ, true_and] at hr
    obtain ⟨j, rfl⟩ := hr
    rw [← hNsum j x]
    exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ s)
  have hrsum : ∀ r ∈ Ty, ∀ x, ∑ s, r x s = N x := by
    intro r hr x
    simp only [hTy, Finset.mem_image, Finset.mem_univ, true_and] at hr
    obtain ⟨j, rfl⟩ := hr
    exact hNsum j x
  set Q : (Fin a → Fin d → ℕ) → Fin a → Fin d → ℝ := fun r x s =>
    if N x = 0 then (S x).weight s else (r x s : ℝ) / N x with hQ
  have hQ0 : ∀ r x s, 0 ≤ Q r x s := by
    intro r x s; simp only [hQ]; split_ifs
    · exact (S x).nonneg s
    · positivity
  have hQ1 : ∀ r ∈ Ty, ∀ x, ∑ s, Q r x s = 1 := by
    intro r hr x; simp only [hQ]; split_ifs with h0
    · exact (S x).total
    · rw [← Finset.sum_div]
      have : (N x : ℝ) ≠ 0 := by exact_mod_cast h0
      rw [div_eq_one_iff_eq this]; exact_mod_cast hrsum r hr x
  have hQpos : ∀ r ∈ Ty, ∀ x s, r x s ≠ 0 → 0 < Q r x s := by
    intro r hr x s hrs
    have hN0 : N x ≠ 0 := by have := hrle r hr x s; omega
    simp only [hQ, if_neg hN0]
    have : (0:ℝ) < r x s := by exact_mod_cast Nat.pos_of_ne_zero hrs
    have : (0:ℝ) < N x := by exact_mod_cast Nat.pos_of_ne_zero hN0
    positivity
  have hrNQ : ∀ r ∈ Ty, ∀ x s, (r x s : ℝ) = N x * Q r x s := by
    intro r hr x s
    simp only [hQ]; split_ifs with h0
    · have := hrle r hr x s; rw [h0] at this
      have : r x s = 0 := by omega
      rw [this, h0]; simp
    · have : (N x : ℝ) ≠ 0 := by exact_mod_cast h0
      field_simp
  let FR : ∀ r ∈ Ty, Fin a → FineResolution d := fun r hr x =>
    ⟨Q r x, hQ0 r x, hQ1 r hr x, (S x).basis⟩
  have hcts : ∀ r (hr : r ∈ Ty) x, conditionalTypeState S w r x = (FR r hr x).state := by
    intro r hr x
    unfold conditionalTypeState
    rw [g79c_state_eq (FR r hr x)]
    split_ifs with h0
    · rw [g79c_state_eq (S x)]
      refine Finset.sum_congr rfl fun s _ => ?_
      simp only [FR, hQ, hN]; rw [if_pos h0]; rfl
    · refine Finset.sum_congr rfl fun s _ => ?_
      simp only [FR, hQ, hN]; rw [if_neg h0]; rfl
  have hvn : ∀ r (hr : r ∈ Ty) x, vnEntropy (FR r hr x).state = -(∑ s, Q r x s * Real.log (Q r x s)) / Real.log 2 := by
    intro r hr x
    rw [g79c_vn_state]
    simp only [FR, Real.logb, Finset.sum_div, ← Finset.sum_neg_distrib, neg_div]
    refine Finset.sum_congr rfl fun s _ => ?_
    ring
  -- probability of a type, and the type-class bound
  set pw : Fin a → Fin d → ℝ := fun x s => (S x).weight s with hpw
  set lam : (Fin n → Fin d) → ℝ := fun j => ∏ k, pw (w k) (j k) with hlam
  have hprodT : ∀ (f : Fin a → Fin d → ℝ) r, ∀ j ∈ T r, ∏ k, f (w k) (j k) = ∏ x, ∏ s, f x s ^ r x s := by
    intro f r j hj
    simp only [hT, Finset.mem_filter, Finset.mem_univ, true_and] at hj
    rw [g79c_ct_prod]; rw [← hj]
  have hTbound : ∀ r ∈ Ty, (T r).card * ∏ x, ∏ s, Q r x s ^ r x s ≤ 1 := by
    intro r hr
    have h1 : ∑ j : Fin n → Fin d, ∏ k, Q r (w k) (j k) = 1 := by
      rw [← Fintype.prod_sum (fun k s => Q r (w k) s)]; simp [hQ1 r hr]
    have h2 : ∑ j ∈ T r, ∏ k, Q r (w k) (j k) = (T r).card * ∏ x, ∏ s, Q r x s ^ r x s := by
      rw [Finset.sum_congr rfl (hprodT (Q r) r), Finset.sum_const, nsmul_eq_mul]
    rw [← h2, ← h1]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun j _ _ => Finset.prod_nonneg fun k _ => hQ0 _ _ _)
  have hProb : ∀ r, ∑ j ∈ T r, lam j = (T r).card * ∏ x, ∏ s, pw x s ^ r x s := by
    intro r
    rw [Finset.sum_congr rfl (hprodT pw r), Finset.sum_const, nsmul_eq_mul]
  have hQexp : ∀ r ∈ Ty, ∏ x, ∏ s, Q r x s ^ r x s = Real.exp (∑ x, (N x : ℝ) * ∑ s, Q r x s * Real.log (Q r x s)) := by
    intro r hr
    rw [Finset.prod_congr rfl fun x _ => Finset.prod_congr rfl fun s _ => g79c_pow_exp1 (hQpos r hr x s)]
    simp_rw [← Real.exp_sum]
    congr 1
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [hrNQ r hr x s]; ring
  -- clause 1
  have hc1 : (lowConditionalProjector S w L).trace.re ≤ (n+1 : ℝ)^(a*d) * exp2 (n * L) := by
    rw [hPi, Matrix.trace_sum]
    simp_rw [Matrix.trace_sum, htr]
    simp only [Finset.sum_const, nsmul_eq_mul, mul_one, Complex.re_sum, Complex.natCast_re]
    have hexp2 : exp2 (n * L) = Real.exp (n * L * Real.log 2) := by
      rw [exp2, Real.rpow_def_of_pos (by norm_num)]; ring_nf
    have hb : ∀ r ∈ R, ((T r).card : ℝ) ≤ exp2 (n * L) := by
      intro r hrR
      simp only [hR, Finset.mem_filter] at hrR
      obtain ⟨hr, hl⟩ := hrR
      have h1 := hTbound r hr
      rw [hQexp r hr] at h1
      have hl' : -(∑ x, (N x : ℝ) * ∑ s, Q r x s * Real.log (Q r x s)) ≤ n * L * Real.log 2 := by
        simp only [hlow] at hl
        simp_rw [hcts r hr, hvn r hr] at hl
        have hl2 : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
        have : ∑ x, empiricalWeight w x * (-(∑ s, Q r x s * Real.log (Q r x s)) / Real.log 2)
            = (-(∑ x, (N x : ℝ) * ∑ s, Q r x s * Real.log (Q r x s))) / (n * Real.log 2) := by
          simp only [empiricalWeight, hN]
          rw [eq_div_iff (by positivity), Finset.sum_mul, ← Finset.sum_neg_distrib]
          refine Finset.sum_congr rfl fun x _ => ?_
          field_simp
        rw [this, div_le_iff₀ (by positivity)] at hl
        linarith
      rw [hexp2]
      have hpos := Real.exp_pos (∑ x, (N x : ℝ) * ∑ s, Q r x s * Real.log (Q r x s))
      have h3 : Real.exp (-(∑ x, (N x : ℝ) * ∑ s, Q r x s * Real.log (Q r x s))) ≤ Real.exp (n * L * Real.log 2) :=
        Real.exp_le_exp.2 hl'
      rw [Real.exp_neg] at h3
      calc ((T r).card : ℝ) = (T r).card * Real.exp (∑ x, (N x : ℝ) * ∑ s, Q r x s * Real.log (Q r x s)) *
            (Real.exp (∑ x, (N x : ℝ) * ∑ s, Q r x s * Real.log (Q r x s)))⁻¹ := by
              rw [mul_assoc, mul_inv_cancel₀ hpos.ne', mul_one]
        _ ≤ 1 * (Real.exp (∑ x, (N x : ℝ) * ∑ s, Q r x s * Real.log (Q r x s)))⁻¹ :=
            mul_le_mul_of_nonneg_right h1 (by positivity)
        _ ≤ _ := by rw [one_mul]; exact h3
    calc ∑ r ∈ R, ((T r).card : ℝ) ≤ ∑ r ∈ R, exp2 (n * L) := Finset.sum_le_sum hb
      _ = R.card * exp2 (n * L) := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (n+1 : ℝ)^(a*d) * exp2 (n * L) := by
          apply mul_le_mul_of_nonneg_right _ (by rw [exp2]; positivity)
          refine le_trans ?_ (g79c_card_types (d := d) w)
          exact_mod_cast Finset.card_le_card (Finset.filter_subset _ _)
  refine ⟨hc1, ?_⟩
  have hl2 : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hWS : (wordTensor (fun i => W.state (w i)) : Matrix (Fin n → Fin d) (Fin n → Fin d) ℂ)
      = wordTensor (fun i => (S (w i)).state) := by
    congr 1; funext i; exact (hS (w i)).symm
  have hWT : (wordTensor (fun i => W.state (w i)) : Matrix (Fin n → Fin d) (Fin n → Fin d) ℂ)
      = ∑ j, ((lam j : ℝ) : ℂ) • A j := by
    rw [hWS]
    simp_rw [g79c_state_eq]
    rw [g79c_wt_expand]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [hlam, hpw, Complex.ofReal_prod]
    rfl
  have hMA : ∀ j, ((∑ i, ((lam i : ℝ) : ℂ) • A i) * A j).trace = (lam j : ℂ) := by
    intro j
    rw [Finset.sum_mul]
    simp_rw [Matrix.smul_mul, hmul, smul_ite, smul_zero]
    rw [Finset.sum_ite_eq']
    simp [Matrix.trace_smul, htr]
  have hEP : effectProb (wordTensor (fun i => W.state (w i))) (lowConditionalProjector S w L)
      = ∑ r ∈ R, ∑ j ∈ T r, lam j := by
    show (((wordTensor (fun i => W.state (w i)) : Matrix (Fin n → Fin d) (Fin n → Fin d) ℂ)) *
      lowConditionalProjector S w L).trace.re = _
    rw [hWT, hPi, Matrix.mul_sum]
    simp_rw [Matrix.mul_sum, Matrix.trace_sum, hMA]
    simp [Complex.re_sum]
  have htot : ∑ r ∈ Ty, ∑ j ∈ T r, lam j = 1 := by
    rw [Finset.sum_fiberwise_of_maps_to (fun j _ => Finset.mem_image_of_mem ct (Finset.mem_univ j))]
    simp only [hlam]
    rw [← Fintype.prod_sum (fun k s => pw (w k) s)]
    simp [hpw, (S _).total]
  have hsplit := Finset.sum_filter_add_sum_filter_not Ty low (fun r => ∑ j ∈ T r, lam j)
  rw [htot] at hsplit
  set tl := divergenceTail n (individualExponent W P L) with htl
  have hbad : ∀ r ∈ Ty, ¬ low r → ∑ j ∈ T r, lam j ≤ tl := by
    intro r hr hnl
    have hUx : ∀ x, ((S x).basis : Matrix (Fin d) (Fin d) ℂ)ᴴ * ((S x).basis : Matrix (Fin d) (Fin d) ℂ) = 1 :=
      fun x => (Matrix.mem_unitaryGroup_iff').1 (S x).basis.2
    let V : FiniteChannel a (fullAlgebra d hd) :=
      { alphabet_pos := W.alphabet_pos
        state := fun x => (FR r hr x).state
        valid := fun x => ⟨g79c_conj_density _ (hUx x) (Q r x) (hQ0 r x) (hQ1 r hr x),
          fun _ _ h => absurd rfl h⟩ }
    have hlt : L < letterOutputEntropy P V.state := by
      unfold letterOutputEntropy
      simp only [hlow, not_le] at hnl
      simp_rw [hcts r hr] at hnl
      simp_rw [← htype]
      exact hnl
    have hle : individualExponent W P L ≤ conditionalDivergence P V.state W.state :=
      sInf_le ⟨V, hlt, rfl⟩
    refine le_trans ?_ (g79c_tail_anti n hle)
    rw [hProb r]
    by_cases hsupp : ∀ x s, pw x s = 0 → Q r x s = 0
    · set K : Fin a → ℝ := fun x => ∑ s, (Q r x s * Real.log (Q r x s) - Q r x s * Real.log (pw x s)) with hK
      have hK0 : ∀ x, 0 ≤ K x := by
        intro x
        have := Finset.sum_le_sum fun s (_ : s ∈ Finset.univ) =>
          g79c_gibbs_term (hQ0 r x s) ((S x).nonneg s) (hsupp x s)
        rw [Finset.sum_sub_distrib, hQ1 r hr x] at this
        have hp1 : ∑ s, pw x s = 1 := (S x).total
        rw [hp1] at this
        simp only [hK]; linarith
      have hrel : ∀ x, relativeBits (V.state x) (W.state x) = ENNReal.ofReal (K x / Real.log 2) := by
        intro x
        rw [← hS x]
        show relativeBits (FR r hr x).state (S x).state = _
        rw [g79c_relbits2 (S x) (FR r hr x) rfl, if_pos (hsupp x), ENNReal.ofReal_div_of_pos hl2]
      have hcd : conditionalDivergence P V.state W.state =
          ENNReal.ofReal (∑ x, (P x).toReal * (K x / Real.log 2)) := by
        unfold conditionalDivergence
        simp_rw [hrel]
        simp_rw [← ENNReal.ofReal_mul ENNReal.toReal_nonneg]
        rw [ENNReal.ofReal_sum_of_nonneg]
        intro x _
        exact mul_nonneg ENNReal.toReal_nonneg (div_nonneg (hK0 x) hl2.le)
      have hX0 : 0 ≤ ∑ x, (P x).toReal * (K x / Real.log 2) :=
        Finset.sum_nonneg fun x _ => mul_nonneg ENNReal.toReal_nonneg (div_nonneg (hK0 x) hl2.le)
      have htail : divergenceTail n (conditionalDivergence P V.state W.state) =
          Real.exp (-(∑ x, (N x : ℝ) * K x)) := by
        rw [hcd]
        simp only [divergenceTail, ENNReal.ofReal_ne_top, if_false, exp2]
        rw [ENNReal.toReal_ofReal hX0, Real.rpow_def_of_pos (by norm_num)]
        congr 1
        have hXv : (∑ x, (P x).toReal * (K x / Real.log 2)) * (n * Real.log 2) = ∑ x, (N x : ℝ) * K x := by
          rw [Finset.sum_mul]; refine Finset.sum_congr rfl fun x _ => ?_
          rw [← htype x]; simp only [empiricalWeight, hN]; field_simp
        rw [← hXv]; ring
      rw [htail]
      have hpexp : ∏ x, ∏ s, pw x s ^ r x s = (∏ x, ∏ s, Q r x s ^ r x s) * Real.exp (-(∑ x, (N x : ℝ) * K x)) := by
        have hpp : ∀ x s, r x s ≠ 0 → 0 < pw x s := by
          intro x s hrs
          have hq := hQpos r hr x s hrs
          rcases ((S x).nonneg s).lt_or_eq with h | h
          · exact h
          · exact absurd (hsupp x s h.symm) hq.ne'
        rw [Finset.prod_congr rfl fun x _ => Finset.prod_congr rfl fun s _ =>
          g79c_pow_exp (hQpos r hr x s) (hpp x s)]
        simp_rw [Finset.prod_mul_distrib, ← Real.exp_sum]
        congr 2
        rw [← Finset.sum_neg_distrib]
        refine Finset.sum_congr rfl fun x _ => ?_
        simp only [hK, Finset.mul_sum, ← Finset.sum_neg_distrib]
        refine Finset.sum_congr rfl fun s _ => ?_
        rw [hrNQ r hr x s]; ring
      rw [hpexp, ← mul_assoc]
      calc ((T r).card : ℝ) * (∏ x, ∏ s, Q r x s ^ r x s) * Real.exp (-(∑ x, (N x : ℝ) * K x))
          ≤ 1 * Real.exp (-(∑ x, (N x : ℝ) * K x)) :=
            mul_le_mul_of_nonneg_right (hTbound r hr) (Real.exp_pos _).le
        _ = _ := one_mul _
    · push_neg at hsupp
      obtain ⟨x, s, hp0, hq0⟩ := hsupp
      have hrs : r x s ≠ 0 := by
        intro h0
        apply hq0
        simp only [hQ]; split_ifs with hN0
        · exact hp0
        · rw [h0]; simp
      have : ∏ x, ∏ s, pw x s ^ r x s = 0 := by
        apply Finset.prod_eq_zero (Finset.mem_univ x)
        apply Finset.prod_eq_zero (Finset.mem_univ s)
        rw [hp0]; exact zero_pow hrs
      rw [this, mul_zero]
      exact g79c_tail_nonneg n _
  have htl0 : 0 ≤ tl := g79c_tail_nonneg n _
  rw [hEP, ge_iff_le]
  have h1 : ∑ r ∈ Ty.filter (fun r => ¬ low r), ∑ j ∈ T r, lam j ≤ ∑ r ∈ Ty.filter (fun r => ¬ low r), tl :=
    Finset.sum_le_sum fun r hr => by
      simp only [Finset.mem_filter] at hr; exact hbad r hr.1 hr.2
  rw [Finset.sum_const, nsmul_eq_mul] at h1
  have h2 : ((Ty.filter (fun r => ¬ low r)).card : ℝ) ≤ (n+1 : ℝ)^(a*d) := by
    refine le_trans ?_ (g79c_card_types (d := d) w)
    exact_mod_cast Finset.card_le_card (Finset.filter_subset _ _)
  have h3 := mul_le_mul_of_nonneg_right h2 htl0
  linarith

theorem g79c_high {d n : ℕ} (hn : 0 < n) (rho : FineResolution d) (L : ℝ) :
    effectProb (copies n rho.state) (highEntropyProjector rho n L) ≥
      1 - (n+1 : ℝ)^d * divergenceTail n (lowEntropyDivergence rho.state L) := by
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
  set ct : (Fin n → Fin d) → Fin d → ℕ := fun j s => count j s with hct
  set Ty := countTypes d n with hTy
  have hTy' : Ty = Finset.univ.image ct := rfl
  set T : (Fin d → ℕ) → Finset (Fin n → Fin d) := fun r => Finset.univ.filter (fun j => ct j = r) with hT
  have hEPr : ∀ r, exactProjector rho n r = ∑ j ∈ T r, A j := by
    intro r
    unfold exactProjector
    congr 1
    ext j
    simp only [hT, hct, Finset.mem_filter, Finset.mem_univ, true_and, funext_iff]
  set high : (Fin d → ℕ) → Prop := fun r => L ≤ vnEntropy (spectralTypeState rho n r) with hhigh
  set R := Ty.filter high with hR
  have hPi : highEntropyProjector rho n L = ∑ r ∈ R, ∑ j ∈ T r, A j := by
    unfold highEntropyProjector
    simp_rw [hEPr]
    rfl
  have hnR : (0:ℝ) < n := by exact_mod_cast hn
  have hrsum : ∀ r ∈ Ty, ∑ s, r s = n := by
    intro r hr
    rw [hTy'] at hr
    simp only [Finset.mem_image, Finset.mem_univ, true_and] at hr
    obtain ⟨j, rfl⟩ := hr
    exact g79c_sum_count j
  set Q : (Fin d → ℕ) → Fin d → ℝ := fun r s => (r s : ℝ) / n with hQ
  have hQ0 : ∀ r s, 0 ≤ Q r s := fun r s => by positivity
  have hQ1 : ∀ r ∈ Ty, ∑ s, Q r s = 1 := by
    intro r hr; simp only [hQ]; rw [← Finset.sum_div, div_eq_one_iff_eq hnR.ne']; exact_mod_cast hrsum r hr
  have hQpos : ∀ r s, r s ≠ 0 → 0 < Q r s := by
    intro r s hrs; simp only [hQ]
    have : (0:ℝ) < r s := by exact_mod_cast Nat.pos_of_ne_zero hrs
    positivity
  have hrNQ : ∀ r s, (r s : ℝ) = n * Q r s := by
    intro r s; simp only [hQ]; field_simp
  let FR : ∀ r ∈ Ty, FineResolution d := fun r hr => ⟨Q r, hQ0 r, hQ1 r hr, rho.basis⟩
  have hsts : ∀ r (hr : r ∈ Ty), spectralTypeState rho n r = (FR r hr).state := by
    intro r hr
    unfold spectralTypeState
    rw [g79c_state_eq (FR r hr)]
    rfl
  set pw : Fin d → ℝ := rho.weight with hpw
  set lam : (Fin n → Fin d) → ℝ := fun j => ∏ k, pw (j k) with hlam
  have hprodT : ∀ (f : Fin d → ℝ) r, ∀ j ∈ T r, ∏ k, f (j k) = ∏ s, f s ^ r s := by
    intro f r j hj
    simp only [hT, Finset.mem_filter, Finset.mem_univ, true_and] at hj
    rw [← hj]
    rw [← Finset.prod_fiberwise (s := Finset.univ) (g := j) (f := fun k => f (j k))]
    refine Finset.prod_congr rfl fun s _ => ?_
    rw [Finset.prod_congr rfl (g := fun _ => f s) (fun k hk => by simp only [Finset.mem_filter] at hk; rw [hk.2]),
      Finset.prod_const]
    rfl
  have hTbound : ∀ r ∈ Ty, (T r).card * ∏ s, Q r s ^ r s ≤ 1 := by
    intro r hr
    have h1 : ∑ j : Fin n → Fin d, ∏ k, Q r (j k) = 1 := by
      rw [← Fintype.prod_sum (fun k s => Q r s)]; simp [hQ1 r hr]
    have h2 : ∑ j ∈ T r, ∏ k, Q r (j k) = (T r).card * ∏ s, Q r s ^ r s := by
      rw [Finset.sum_congr rfl (hprodT (Q r) r), Finset.sum_const, nsmul_eq_mul]
    rw [← h2, ← h1]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun j _ _ => Finset.prod_nonneg fun k _ => hQ0 _ _)
  have hProb : ∀ r, ∑ j ∈ T r, lam j = (T r).card * ∏ s, pw s ^ r s := by
    intro r
    rw [Finset.sum_congr rfl (hprodT pw r), Finset.sum_const, nsmul_eq_mul]
  have hl2 : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hcop : copies n rho.state = ∑ j, ((lam j : ℝ) : ℂ) • A j := by
    have : copies n rho.state = wordTensor (fun _ : Fin n => rho.state) := by
      ext a b; rfl
    rw [this]
    simp_rw [g79c_state_eq]
    rw [g79c_wt_expand]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [hlam, hpw, Complex.ofReal_prod]
    rfl
  have hMA : ∀ j, ((∑ i, ((lam i : ℝ) : ℂ) • A i) * A j).trace = (lam j : ℂ) := by
    intro j
    rw [Finset.sum_mul]
    simp_rw [Matrix.smul_mul, hmul, smul_ite, smul_zero]
    rw [Finset.sum_ite_eq']
    simp [Matrix.trace_smul, hA, g79c_wt_trace, g79c_atom_tr]
  have hEP : effectProb (copies n rho.state) (highEntropyProjector rho n L) = ∑ r ∈ R, ∑ j ∈ T r, lam j := by
    simp only [effectProb]
    rw [hcop, hPi, Matrix.mul_sum]
    simp_rw [Matrix.mul_sum, Matrix.trace_sum, hMA]
    simp [Complex.re_sum]
  have htot : ∑ r ∈ Ty, ∑ j ∈ T r, lam j = 1 := by
    rw [hTy', Finset.sum_fiberwise_of_maps_to (fun j _ => Finset.mem_image_of_mem ct (Finset.mem_univ j))]
    simp only [hlam]
    rw [← Fintype.prod_sum (fun k s => pw s)]
    simp [hpw, rho.total]
  have hsplit := Finset.sum_filter_add_sum_filter_not Ty high (fun r => ∑ j ∈ T r, lam j)
  rw [htot] at hsplit
  set tl := divergenceTail n (lowEntropyDivergence rho.state L) with htl
  have hbad : ∀ r ∈ Ty, ¬ high r → ∑ j ∈ T r, lam j ≤ tl := by
    intro r hr hnh
    have hU : (rho.basis : Matrix (Fin d) (Fin d) ℂ)ᴴ * (rho.basis : Matrix (Fin d) (Fin d) ℂ) = 1 :=
      (Matrix.mem_unitaryGroup_iff').1 rho.basis.2
    have hden : IsDensityMatrix (FR r hr).state := g79c_conj_density _ hU (Q r) (hQ0 r) (hQ1 r hr)
    have hvle : vnEntropy (FR r hr).state ≤ L := by
      simp only [hhigh, not_le] at hnh
      rw [hsts r hr] at hnh; exact hnh.le
    have hle : lowEntropyDivergence rho.state L ≤ relativeBits (FR r hr).state rho.state :=
      sInf_le ⟨(FR r hr).state, hden, hvle, rfl⟩
    refine le_trans ?_ (g79c_tail_anti n hle)
    rw [hProb r]
    by_cases hsupp : ∀ s, pw s = 0 → Q r s = 0
    · set K : ℝ := ∑ s, (Q r s * Real.log (Q r s) - Q r s * Real.log (pw s)) with hK
      have hK0 : 0 ≤ K := by
        have := Finset.sum_le_sum fun s (_ : s ∈ Finset.univ) =>
          g79c_gibbs_term (hQ0 r s) (rho.nonneg s) (hsupp s)
        rw [Finset.sum_sub_distrib, hQ1 r hr] at this
        have hp1 : ∑ s, pw s = 1 := rho.total
        rw [hp1] at this
        simp only [hK]; linarith
      have hrel : relativeBits (FR r hr).state rho.state = ENNReal.ofReal (K / Real.log 2) := by
        rw [g79c_relbits2 rho (FR r hr) rfl, if_pos hsupp, ENNReal.ofReal_div_of_pos hl2]
      have htail : divergenceTail n (relativeBits (FR r hr).state rho.state) = Real.exp (-(n * K)) := by
        rw [hrel]
        simp only [divergenceTail, ENNReal.ofReal_ne_top, if_false, exp2]
        rw [ENNReal.toReal_ofReal (div_nonneg hK0 hl2.le), Real.rpow_def_of_pos (by norm_num)]
        congr 1; field_simp
      rw [htail]
      have hpexp : ∏ s, pw s ^ r s = (∏ s, Q r s ^ r s) * Real.exp (-(n * K)) := by
        have hpp : ∀ s, r s ≠ 0 → 0 < pw s := by
          intro s hrs
          have hq := hQpos r s hrs
          rcases (rho.nonneg s).lt_or_eq with h | h
          · exact h
          · exact absurd (hsupp s h.symm) hq.ne'
        rw [Finset.prod_congr rfl fun s _ => g79c_pow_exp (hQpos r s) (hpp s)]
        rw [Finset.prod_mul_distrib, ← Real.exp_sum]
        congr 2
        rw [hK, Finset.mul_sum, ← Finset.sum_neg_distrib]
        refine Finset.sum_congr rfl fun s _ => ?_
        rw [hrNQ r s]; ring
      rw [hpexp, ← mul_assoc]
      calc ((T r).card : ℝ) * (∏ s, Q r s ^ r s) * Real.exp (-(n * K))
          ≤ 1 * Real.exp (-(n * K)) := mul_le_mul_of_nonneg_right (hTbound r hr) (Real.exp_pos _).le
        _ = _ := one_mul _
    · push_neg at hsupp
      obtain ⟨s, hp0, hq0⟩ := hsupp
      have hrs : r s ≠ 0 := by
        intro h0; apply hq0; simp only [hQ]; rw [h0]; simp
      have : ∏ s, pw s ^ r s = 0 := by
        apply Finset.prod_eq_zero (Finset.mem_univ s)
        rw [hp0]; exact zero_pow hrs
      rw [this, mul_zero]
      exact g79c_tail_nonneg n _
  have htl0 : 0 ≤ tl := g79c_tail_nonneg n _
  rw [hEP, ge_iff_le]
  have h1 : ∑ r ∈ Ty.filter (fun r => ¬ high r), ∑ j ∈ T r, lam j ≤ ∑ r ∈ Ty.filter (fun r => ¬ high r), tl :=
    Finset.sum_le_sum fun r hr => by
      simp only [Finset.mem_filter] at hr; exact hbad r hr.1 hr.2
  rw [Finset.sum_const, nsmul_eq_mul] at h1
  have h2 : ((Ty.filter (fun r => ¬ high r)).card : ℝ) ≤ (n+1 : ℝ)^d := by
    have hsub : Ty ⊆ Fintype.piFinset (fun _ : Fin d => Finset.range (n+1)) := by
      intro f hf
      rw [hTy'] at hf
      simp only [Finset.mem_image, Finset.mem_univ, true_and] at hf
      obtain ⟨j, rfl⟩ := hf
      simp only [Fintype.mem_piFinset, Finset.mem_range]
      intro s
      have := Finset.card_le_univ (Finset.univ.filter fun t => j t = s)
      simp only [Fintype.card_fin] at this
      simp only [hct, count]; omega
    have := (Finset.card_le_card (Finset.filter_subset (fun r => ¬ high r) Ty)).trans (Finset.card_le_card hsub)
    rw [Fintype.card_piFinset] at this
    simp only [Finset.card_range, Finset.prod_const, Finset.card_univ, Fintype.card_fin] at this
    exact_mod_cast this
  have h3 := mul_le_mul_of_nonneg_right h2 htl0
  linarith

/-- Lemma II.14, PDF p.31: all three inequalities, for arbitrary REAL L. Empty
entropy constraints give +infinity, and all spectral sums range only over realizable types. -/
theorem solution {a d n : ℕ} (ha : 0 < a) (hd : 0 < d) (hn : 0 < n)
    (W : FiniteChannel a (fullAlgebra d hd)) (S : Fin a → FineResolution d)
    (hS : ∀ x, (S x).state = W.state x) (rho : FineResolution d)
    (w : Fin n → Fin a) (P : PMF (Fin a))
    (htype : ∀ x, empiricalWeight w x = (P x).toReal) (L : ℝ) :
    (lowConditionalProjector S w L).trace.re ≤ (n+1 : ℝ)^(a*d) * exp2 (n * L) ∧
    effectProb (wordTensor (fun i => W.state (w i))) (lowConditionalProjector S w L) ≥
      1 - (n+1 : ℝ)^(a*d) * divergenceTail n (individualExponent W P L) ∧
    effectProb (copies n rho.state) (highEntropyProjector rho n L) ≥
      1 - (n+1 : ℝ)^d * divergenceTail n (lowEntropyDivergence rho.state L) := by
  obtain ⟨h1, h2⟩ := g79c_cond ha hd hn W S hS w P htype L
  exact ⟨h1, h2, g79c_high hn rho L⟩



end
