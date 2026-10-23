-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Renew46.P43.conditionalTypical
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T08:10:38.714199+00:00
-- url     : https://prove2.me/submissions/b75e1dcf-b053-4c7f-9581-2c45983af0d4

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

/-- Lemma II.10, PDF p.29: every concentration, sandwich, rank and shadow clause.
P is the word's actual empirical distribution, rather than an unconstrained free law. -/
theorem solution {a d n : ℕ} (ha : 0 < a) (hn : 0 < n)
    (S : Fin a → FineResolution d) (w : Fin n → Fin a) (delta : ℝ) (hdelta : 0 < delta) :
    let Pi := conditionalVarianceProjector S w delta
    let rho := wordTensor (fun k => (S (w k)).state)
    let h := wordConditionalEntropy S w
    let correction := varianceConstant * d * Real.sqrt a * delta * Real.sqrt n
    effectProb rho Pi ≥ 1 - (a : ℝ) * d / delta^2 ∧
    Below ((exp2 (-n * h - correction) : ℂ) • Pi) (Pi * rho * Pi) ∧
    Below (Pi * rho * Pi) ((exp2 (-n * h + correction) : ℂ) • Pi) ∧
    Pi.trace.re ≤ exp2 (n * h + correction) ∧
    Pi.trace.re ≥ (1 - (a : ℝ) * d / delta^2) * exp2 (n * h - correction) ∧
    ∀ (B : Matrix (Fin n → Fin d) (Fin n → Fin d) ℂ) (eta : ℝ),
      IsShadow rho B eta →
      B.trace.re ≥ (eta - (a : ℝ) * d / delta^2) * exp2 (n * h - correction) := by
  intro Pi rho h correction
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
  have hherm : ∀ i, (A i)ᴴ = A i := by
    intro i; simp only [hA]; rw [g79c_wt_conjT]; simp_rw [g79c_atom_conjT]
  have htr : ∀ i, (A i).trace = 1 := by
    intro i; simp only [hA]; rw [g79c_wt_trace]; simp [g79c_atom_tr]
  have hsumA : ∑ j, A j = 1 := by
    have := g79c_wt_expand (fun _ _ => (1:ℂ)) (fun k r => (S (w k)).atom r)
    simp only [one_smul, Finset.prod_const_one] at this
    rw [← this]; simp_rw [g79c_atom_sum]; exact g79c_wt_one
  set P : Fin a → Fin d → ℝ := fun x r => ((S x).law r).toReal with hPdef
  have hlaw : ∀ x r, P x r = (S x).weight r := by
    intro x r; simp [P, FineResolution.law, ENNReal.toReal_ofReal ((S x).nonneg r)]
  have hP0 : ∀ x r, 0 ≤ P x r := fun x r => by rw [hlaw]; exact (S x).nonneg r
  have hPs : ∀ x, ∑ r, P x r = 1 := fun x => by simp_rw [hlaw]; exact (S x).total
  have hP1 : ∀ x r, P x r ≤ 1 := fun x r => by
    rw [← hPs x]; exact Finset.single_le_sum (fun r _ => hP0 x r) (Finset.mem_univ r)
  set q : Fin n → Fin d → ℝ := fun k r => P (w k) r with hqdef
  have hq0 : ∀ k r, 0 ≤ q k r := fun k r => hP0 _ _
  have hq1 : ∀ k, ∑ r, q k r = 1 := fun k => hPs _
  set lam : (Fin n → Fin d) → ℝ := fun j => ∏ k, q k (j k) with hlamdef
  have hlam0 : ∀ j, 0 ≤ lam j := fun j => Finset.prod_nonneg fun k _ => hq0 _ _
  have htot : ∑ j, lam j = 1 := by
    simp only [hlamdef]; rw [← Fintype.prod_sum (fun k c => q k c)]; simp [hq1]
  set typ := Finset.univ.filter (fun v : Fin n → Fin d => ∀ x r,
      |((Finset.univ.filter fun k => w k = x ∧ v k = r).card : ℝ) - count w x * P x r| ≤
        delta * Real.sqrt (count w x) * Real.sqrt (P x r * (1 - P x r))) with htyp
  have hprob : 1 - (a : ℝ) * d / delta ^ 2 ≤ ∑ j ∈ typ, lam j :=
    g79c_prob2 q hq0 hq1 w P (fun k r => rfl) delta hdelta
  set e : (Fin n → Fin d) → ℝ := fun j => if j ∈ typ then 1 else 0 with he
  have hPi : Pi = ∑ j, ((e j : ℝ) : ℂ) • A j := by
    show (∑ j ∈ typ, A j) = _
    have : ∀ j, ((e j : ℝ) : ℂ) • A j = if j ∈ typ then A j else 0 := by
      intro j; simp only [he]; split_ifs <;> simp
    simp_rw [this]; rw [Finset.sum_ite_mem, Finset.univ_inter]
  have hrho : rho = ∑ j, ((lam j : ℝ) : ℂ) • A j := by
    show wordTensor (fun k => (S (w k)).state) = _
    simp_rw [g79c_state_eq]
    rw [g79c_wt_expand]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [hlamdef, hqdef, hlaw, Complex.ofReal_prod]
    rfl
  -- n * h
  have hnh : (n : ℝ) * h = ∑ x, (count w x : ℝ) * (-∑ r, P x r * Real.logb 2 (P x r)) := by
    simp only [h, wordConditionalEntropy, empiricalWeight, Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [g79c_vn_state]
    simp_rw [hlaw]
    have : (n:ℝ) ≠ 0 := by exact_mod_cast hn.ne'
    field_simp
  -- typical eigenvalue bounds
  have hbounds : ∀ j ∈ typ, exp2 (-n * h - correction) ≤ lam j ∧ lam j ≤ exp2 (-n * h + correction) := by
    intro j hj
    simp only [htyp, Finset.mem_filter] at hj
    obtain ⟨hpos, hdev⟩ := g79c_dev w j P hP0 hP1 delta hdelta hj.2
    rw [← hnh] at hdev
    have hlog : Real.logb 2 (lam j) = ∑ k, Real.logb 2 (q k (j k)) := by
      simp only [hlamdef]
      rw [Real.logb_prod]; intro k _; exact (hpos k).ne'
    have hlpos : 0 < lam j := Finset.prod_pos fun k _ => hpos k
    have hl : lam j = exp2 (Real.logb 2 (lam j)) := by
      rw [exp2, Real.rpow_logb (by norm_num) (by norm_num) hlpos]
    have hsum : ∑ k, (-Real.logb 2 (P (w k) (j k))) = -Real.logb 2 (lam j) := by
      rw [hlog, Finset.sum_neg_distrib]
    rw [hsum] at hdev
    have hc : correction = varianceConstant * d * Real.sqrt a * delta * Real.sqrt n := rfl
    rw [← hc] at hdev
    obtain ⟨h1, h2⟩ := abs_le.1 hdev
    constructor
    · rw [hl, exp2, exp2]; apply Real.rpow_le_rpow_of_exponent_le (by norm_num); linarith
    · rw [hl, exp2, exp2]; apply Real.rpow_le_rpow_of_exponent_le (by norm_num); linarith
  set cl := exp2 (-n * h - correction) with hcl
  set ch := exp2 (-n * h + correction) with hch
  have hcl0 : 0 < cl := by rw [hcl, exp2]; positivity
  have hch0 : 0 < ch := by rw [hch, exp2]; positivity
  have hclch : cl * exp2 (n * h + correction) = 1 := by
    rw [hcl, exp2, exp2, ← Real.rpow_add (by norm_num)]; ring_nf; simp
  have hchcl : ch * exp2 (n * h - correction) = 1 := by
    rw [hch, exp2, exp2, ← Real.rpow_add (by norm_num)]; ring_nf; simp
  have hPRP : Pi * rho * Pi = ∑ j, ((e j * lam j : ℝ) : ℂ) • A j := by
    rw [hPi, hrho, g79c_comb A hmul, g79c_comb A hmul]
    refine Finset.sum_congr rfl fun j _ => ?_
    congr 1; simp only [he]; split_ifs <;> simp
  have htrPi : Pi.trace.re = typ.card := by
    rw [hPi, g79c_tr_comb A htr]
    simp only [he, Complex.re_sum, Complex.ofReal_re]
    rw [← Finset.sum_filter]; simp
  have hEP : effectProb rho Pi = ∑ j ∈ typ, lam j := by
    simp only [effectProb]
    rw [hrho, hPi, g79c_comb A hmul, g79c_tr_comb A htr]
    simp only [Complex.re_sum, ← Complex.ofReal_mul, Complex.ofReal_re]
    have : ∀ j, lam j * e j = if j ∈ typ then lam j else 0 := by
      intro j; simp only [he]; split_ifs <;> simp
    simp_rw [this]; rw [Finset.sum_ite_mem, Finset.univ_inter]
  have hsumtyp_le : ∑ j ∈ typ, lam j ≤ 1 := by
    rw [← htot]; exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun j _ _ => hlam0 j)
  have hcardlow : (typ.card : ℝ) * cl ≤ ∑ j ∈ typ, lam j := by
    rw [← nsmul_eq_mul, ← Finset.sum_const]
    exact Finset.sum_le_sum fun j hj => (hbounds j hj).1
  have hcardhigh : ∑ j ∈ typ, lam j ≤ (typ.card : ℝ) * ch := by
    rw [← nsmul_eq_mul, ← Finset.sum_const]
    exact Finset.sum_le_sum fun j hj => (hbounds j hj).2
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hEP]; exact hprob
  · unfold Below
    have : Pi * rho * Pi - (cl : ℂ) • Pi = ∑ j, ((if j ∈ typ then lam j - cl else 0 : ℝ) : ℂ) • A j := by
      rw [hPRP, hPi, Finset.smul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [smul_smul, ← sub_smul]; congr 1; simp only [he]; split_ifs <;> push_cast <;> ring
    rw [this]
    apply g79c_psd_comb A hmul hherm
    intro j; split_ifs with hj
    · linarith [(hbounds j hj).1]
    · exact le_rfl
  · unfold Below
    have : (ch : ℂ) • Pi - Pi * rho * Pi = ∑ j, ((if j ∈ typ then ch - lam j else 0 : ℝ) : ℂ) • A j := by
      rw [hPRP, hPi, Finset.smul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [smul_smul, ← sub_smul]; congr 1; simp only [he]; split_ifs <;> push_cast <;> ring
    rw [this]
    apply g79c_psd_comb A hmul hherm
    intro j; split_ifs with hj
    · linarith [(hbounds j hj).2]
    · exact le_rfl
  · rw [htrPi]
    have : (typ.card : ℝ) * cl ≤ 1 := hcardlow.trans hsumtyp_le
    have h2 : (typ.card : ℝ) = (typ.card : ℝ) * cl * exp2 (n * h + correction) := by
      rw [mul_assoc, hclch, mul_one]
    rw [h2]
    have h3 : 0 ≤ exp2 (n * h + correction) := by rw [exp2]; positivity
    nlinarith
  · rw [htrPi, ge_iff_le]
    have h3 : 0 ≤ exp2 (n * h - correction) := by rw [exp2]; positivity
    calc (1 - (a : ℝ) * d / delta ^ 2) * exp2 (n * h - correction)
        ≤ (∑ j ∈ typ, lam j) * exp2 (n * h - correction) := mul_le_mul_of_nonneg_right hprob h3
      _ ≤ ((typ.card : ℝ) * ch) * exp2 (n * h - correction) := mul_le_mul_of_nonneg_right hcardhigh h3
      _ = typ.card := by rw [mul_assoc, hchcl, mul_one]
  · intro B eta hsh
    obtain ⟨hB, heta⟩ := hsh
    have hb := g79c_b_bounds A hmul hherm htr B hB
    set b : (Fin n → Fin d) → ℝ := fun j => (A j * B).trace.re with hbdef
    have hEB : effectProb rho B = ∑ j, lam j * b j := by
      simp only [effectProb]
      rw [hrho, Finset.sum_mul, Matrix.trace_sum, Complex.re_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul, Complex.re_ofReal_mul]
    have hBtr : B.trace.re = ∑ j, b j := by
      simp only [hbdef]
      rw [← Complex.re_sum, ← Matrix.trace_sum, ← Finset.sum_mul, hsumA, Matrix.one_mul]
    have hsplit := Finset.sum_filter_add_sum_filter_not (Finset.univ : Finset (Fin n → Fin d))
      (fun j => j ∈ typ) (fun j => lam j * b j)
    have hsplit2 := Finset.sum_filter_add_sum_filter_not (Finset.univ : Finset (Fin n → Fin d))
      (fun j => j ∈ typ) (fun j => lam j)
    have hsplit3 := Finset.sum_filter_add_sum_filter_not (Finset.univ : Finset (Fin n → Fin d))
      (fun j => j ∈ typ) (fun j => b j)
    have hft : Finset.univ.filter (fun j => j ∈ typ) = typ := by ext j; simp
    rw [hft] at hsplit hsplit2 hsplit3
    have h1 : ∑ j ∈ typ, lam j * b j ≤ ch * ∑ j ∈ typ, b j := by
      rw [Finset.mul_sum]; exact Finset.sum_le_sum fun j hj =>
        mul_le_mul_of_nonneg_right (hbounds j hj).2 (hb j).1
    have h2 : ∑ j ∈ Finset.univ.filter (fun j => j ∉ typ), lam j * b j ≤
        ∑ j ∈ Finset.univ.filter (fun j => j ∉ typ), lam j :=
      Finset.sum_le_sum fun j _ => by nlinarith [(hb j).1, (hb j).2, hlam0 j]
    have h3 : 0 ≤ ∑ j ∈ Finset.univ.filter (fun j => j ∉ typ), b j :=
      Finset.sum_nonneg fun j _ => (hb j).1
    have key : eta - (a : ℝ) * d / delta ^ 2 ≤ ch * B.trace.re := by
      rw [hEB] at heta
      rw [hBtr]
      have : ch * ∑ j ∈ typ, b j ≤ ch * ∑ j, b j := by
        apply mul_le_mul_of_nonneg_left _ hch0.le; linarith
      linarith
    rw [ge_iff_le]
    have h4 : 0 ≤ exp2 (n * h - correction) := by rw [exp2]; positivity
    calc (eta - (a : ℝ) * d / delta ^ 2) * exp2 (n * h - correction)
        ≤ (ch * B.trace.re) * exp2 (n * h - correction) := mul_le_mul_of_nonneg_right key h4
      _ = B.trace.re := by rw [mul_comm ch, mul_assoc, hchcl, mul_one]



end
