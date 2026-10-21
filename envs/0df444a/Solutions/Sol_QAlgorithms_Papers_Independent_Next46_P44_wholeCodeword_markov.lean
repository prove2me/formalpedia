-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Next46.P44.wholeCodeword_markov
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-20T21:10:12.352091+00:00
-- url     : https://prove2.me/submissions/ccce9353-76fb-4c1b-9777-da19f6adbbad

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P44
open QAlgorithms QAlgorithms.Papers.Independent.Next46.P44
open scoped Matrix ComplexConjugate ComplexOrder

lemma g63c_trace_cfc_family {X J κ : Type*} [Fintype X] [DecidableEq X] [Fintype J] [DecidableEq J]
    [Fintype κ] [DecidableEq κ]
    (P : Matrix X X ℂ) (Q : J → Matrix κ κ ℂ) (hP : P.IsHermitian) (hQ : ∀ j, (Q j).IsHermitian)
    (f : ℝ → ℝ) (hf : f 0 = 0)
    (htr : ∀ k : ℕ, (P ^ (k + 1)).trace = ∑ j, ((Q j) ^ (k + 1)).trace) :
    (cfc f P).trace = ∑ j, (cfc f (Q j)).trace := by
  classical
  set S : Finset ℝ := P.finite_real_spectrum.toFinset ∪
    Finset.univ.biUnion (fun j => (Q j).finite_real_spectrum.toFinset) ∪ {0} with hS
  set p : Polynomial ℝ := Lagrange.interpolate S id f with hp
  have hev : ∀ x ∈ S, p.eval x = f x := by
    intro x hx
    exact Lagrange.eval_interpolate_at_node (s := S) (v := id) f (Set.injOn_id _) hx
  have hPe : cfc f P = Polynomial.aeval P p := by
    rw [← cfc_polynomial p P hP.isSelfAdjoint]
    apply cfc_congr
    intro x hx
    exact (hev x (by simp [hS, hx])).symm
  have hQe : ∀ j, cfc f (Q j) = Polynomial.aeval (Q j) p := by
    intro j
    rw [← cfc_polynomial p (Q j) (hQ j).isSelfAdjoint]
    apply cfc_congr
    intro x hx
    refine (hev x ?_).symm
    simp only [hS, Finset.mem_union, Finset.mem_biUnion, Set.Finite.mem_toFinset]
    exact Or.inl (Or.inr ⟨j, Finset.mem_univ _, hx⟩)
  have h0 : p.coeff 0 = 0 := by
    rw [Polynomial.coeff_zero_eq_eval_zero, hev 0 (by simp [hS]), hf]
  simp_rw [hQe]
  rw [hPe, Polynomial.aeval_eq_sum_range' (Nat.lt_succ_self _) ]
  simp_rw [Polynomial.aeval_eq_sum_range' (Nat.lt_succ_self p.natDegree)]
  rw [Matrix.trace_sum]
  simp_rw [Matrix.trace_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  simp_rw [Matrix.trace_smul]
  rcases i with _ | k
  · simp [h0]
  · rw [htr k, Finset.smul_sum]

/-- block-diagonal (up to reindexing) matrices -/
lemma g63c_trace_cfc_block {X J κ : Type*} [Fintype X] [DecidableEq X] [Fintype J] [DecidableEq J]
    [Fintype κ] [DecidableEq κ] (e : X ≃ κ × J)
    (P : Matrix X X ℂ) (Q : J → Matrix κ κ ℂ) (hQ : ∀ j, (Q j).IsHermitian)
    (hPQ : ∀ u v, P u v = if (e u).2 = (e v).2 then Q (e u).2 (e u).1 (e v).1 else 0)
    (f : ℝ → ℝ) (hf : f 0 = 0) :
    (cfc f P).trace = ∑ j, (cfc f (Q j)).trace := by
  have hP : P = (Matrix.blockDiagonal Q).submatrix e e := by
    ext u v; rw [hPQ]; rfl
  have hH : P.IsHermitian := by
    rw [hP]; exact (Matrix.isHermitian_blockDiagonal_iff.2 hQ).submatrix _
  refine g63c_trace_cfc_family P Q hH hQ f hf (fun k => ?_)
  have : P ^ (k+1) = (Matrix.blockDiagonal Q ^ (k+1)).submatrix e e := by
    rw [hP]
    have := map_pow (Matrix.reindexAlgEquiv ℂ ℂ e.symm) (Matrix.blockDiagonal Q) (k+1)
    simpa [Matrix.coe_reindexAlgEquiv, Matrix.reindex_apply] using this.symm
  rw [this, ← Matrix.blockDiagonal_pow]
  rw [show ((Matrix.blockDiagonal (Q ^ (k+1))).submatrix e e).trace
      = (Matrix.blockDiagonal (Q ^ (k+1))).trace from ?_]
  · rw [Matrix.trace_blockDiagonal]; rfl
  · simp only [Matrix.trace, Matrix.diag_apply, Matrix.submatrix_apply]
    exact Equiv.sum_comp e (fun i => Matrix.blockDiagonal (Q ^ (k+1)) i i)

lemma g63c_ent_smul {κ : Type*} [Fintype κ] [DecidableEq κ] (R : Matrix κ κ ℂ) (s : ℝ)
    (hs : 0 ≤ s) (hR : s ≠ 0 → R.IsHermitian) :
    vnEntropy ((s : ℂ) • R) = -(s * Real.logb 2 s) * R.trace.re + s * vnEntropy R := by
  rcases eq_or_lt_of_le hs with h0 | hpos
  · subst h0; simp [vnEntropy]
  have hR' := hR hpos.ne'
  have hsm : (s : ℂ) • R = s • R := by
    ext i j; simp
  unfold vnEntropy
  rw [hsm, ← cfc_comp_smul s (fun x : ℝ => x * Real.logb 2 x) R
    ((R.finite_real_spectrum.image _).continuousOn _) hR'.isSelfAdjoint]
  have hc : cfc (fun y : ℝ => (fun x : ℝ => x * Real.logb 2 x) (s • y)) R =
      cfc (fun x : ℝ => (s * Real.logb 2 s) * x + s * (x * Real.logb 2 x)) R := by
    apply cfc_congr
    intro x _
    simp only [smul_eq_mul]
    rcases eq_or_ne x 0 with hx | hx
    · subst hx; simp
    · rw [Real.logb_mul hpos.ne' hx]; ring
  rw [hc, cfc_add (hf := (R.finite_real_spectrum).continuousOn _)
    (hg := (R.finite_real_spectrum).continuousOn _),
    cfc_const_mul_id _ R hR'.isSelfAdjoint,
    cfc_const_mul s (fun x : ℝ => x * Real.logb 2 x) R ((R.finite_real_spectrum).continuousOn _)]
  simp [Matrix.trace_add, Matrix.trace_smul]
  ring

lemma g63c_ent_scalar (r : ℝ) (hr : 0 ≤ r) :
    vnEntropy ((r : ℂ) • (1 : Matrix Unit Unit ℂ)) = -(r * Real.logb 2 r) := by
  rw [g63c_ent_smul _ r hr (fun _ => Matrix.isHermitian_one)]
  simp [vnEntropy]

lemma g63c_ent_scalar' (r : ℝ) :
    vnEntropy ((r : ℂ) • (1 : Matrix Unit Unit ℂ)) = -(r * Real.logb 2 r) := by
  have : (r : ℂ) • (1 : Matrix Unit Unit ℂ) = algebraMap ℝ (Matrix Unit Unit ℂ) r := by
    ext i j; simp [Matrix.algebraMap_matrix_apply, Matrix.one_apply]
  unfold vnEntropy
  rw [this, cfc_algebraMap, Matrix.trace, Fintype.sum_unique, Matrix.diag_apply,
    Matrix.algebraMap_matrix_apply, if_pos rfl]
  simp

lemma g63c_tr_real {κ : Type*} [Fintype κ] (M : Matrix κ κ ℂ) (hM : M.IsHermitian) :
    ((M.trace.re : ℝ) : ℂ) = M.trace := by
  apply Complex.ext
  · simp
  · simp only [Complex.ofReal_im, Matrix.trace, Matrix.diag_apply, Complex.im_sum]
    symm
    refine Finset.sum_eq_zero (fun i _ => ?_)
    have := hM.apply i i
    exact (Complex.conj_eq_iff_im.1 this)

lemma g63c_herm_smul {κ : Type*} [Fintype κ] (R : Matrix κ κ ℂ) (s : ℝ)
    (hR : s ≠ 0 → R.IsHermitian) : ((s : ℂ) • R).IsHermitian := by
  rcases eq_or_ne s 0 with h | h
  · subst h; simp
  · have hR' := hR h
    unfold Matrix.IsHermitian
    rw [Matrix.conjTranspose_smul, hR'.eq]
    simp

lemma g63c_ent_block {X J κ : Type*} [Fintype X] [DecidableEq X] [Fintype J] [DecidableEq J]
    [Fintype κ] [DecidableEq κ] (e : X ≃ κ × J)
    (P : Matrix X X ℂ) (Q : J → Matrix κ κ ℂ) (hQ : ∀ j, (Q j).IsHermitian)
    (hPQ : ∀ u v, P u v = if (e u).2 = (e v).2 then Q (e u).2 (e u).1 (e v).1 else 0) :
    vnEntropy P = ∑ j, vnEntropy (Q j) := by
  unfold vnEntropy
  rw [g63c_trace_cfc_block e P Q hQ hPQ _ (by simp)]
  simp [Complex.re_sum]

def g63c_SP {ι κ : Type*} (f : Matrix ι ι ℂ → Matrix κ κ ℂ) : Prop := ∀ X, f Xᴴ = (f X)ᴴ

lemma g63c_SP_id {ι : Type*} : g63c_SP (id : Matrix ι ι ℂ → Matrix ι ι ℂ) := fun _ => rfl

lemma g63c_SP_conj {ι κ : Type*} [Fintype ι] (A : Matrix κ ι ℂ) : g63c_SP (conjSuperop A) := by
  intro X; simp [conjSuperop, Matrix.conjTranspose_mul, Matrix.mul_assoc]

lemma g63c_SP_channel {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] (Φ : Superop ι κ)
    (h : IsChannel Φ) : g63c_SP Φ := by
  obtain ⟨m, E, -, hE⟩ := h
  intro X
  rw [hE, hE]
  simp [krausApply, Matrix.conjTranspose_sum, Matrix.conjTranspose_mul, Matrix.mul_assoc]

lemma g63c_SP_pi {ι : Type*} [Fintype ι] [DecidableEq ι] {k : ℕ}
    (Φ : Fin k → Superop ι ι) (h : ∀ i, g63c_SP (Φ i)) : g63c_SP (piSuperop Φ) := by
  intro X
  ext y y'
  simp only [piSuperop, Matrix.conjTranspose_apply, Matrix.of_apply, star_sum, star_mul',
    star_prod]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun x _ => Finset.sum_congr rfl (fun x' _ => ?_))
  congr 1
  refine Finset.prod_congr rfl (fun i _ => ?_)
  have := congrFun (congrFun (h i (Matrix.single (x i) (x' i) 1)) (y i)) (y' i)
  rw [Matrix.conjTranspose_single, star_one] at this
  rw [this, Matrix.conjTranspose_apply]

lemma g63c_SP_onSub {n : ℕ} {H : Type*} (s : Fin n → Prop) [DecidablePred s]
    (f : Superop ({i // s i} → H) ({i // s i} → H)) (hf : g63c_SP f) :
    g63c_SP (onSubsystem s f) := by
  intro X
  ext x y
  simp only [onSubsystem, Matrix.conjTranspose_apply]
  have := congrFun (congrFun (hf (fun z w => X (replaceSubsystem s y z) (replaceSubsystem s x w)))
    (fun i => x i.val)) (fun i => y i.val)
  rw [Matrix.conjTranspose_apply] at this
  rw [← this]
  congr 1

lemma g63c_SP_comp {ι κ μ : Type*} (f : Matrix ι ι ℂ → Matrix κ κ ℂ) (g : Matrix κ κ ℂ → Matrix μ μ ℂ)
    (hf : g63c_SP f) (hg : g63c_SP g) : g63c_SP (fun X => g (f X)) := by
  intro X; simp only [hf X, hg (f X)]

lemma g63c_SP_step {n : ℕ} {H K : Type*} [Fintype H] [DecidableEq H] [Fintype K]
    (C : FeedbackProtocol n H K) (t : Fin n) (k : K) : g63c_SP (C.step t k) := by
  unfold FeedbackProtocol.step
  refine g63c_SP_comp _ _ (g63c_SP_comp _ _ (g63c_SP_pi _ (fun i => ?_))
    (g63c_SP_onSub _ _ (g63c_SP_conj _))) (g63c_SP_onSub _ _ (g63c_SP_channel _ (C.response_cptp t k)))
  by_cases hi : i = t
  · simp only [hi, if_true]; exact g63c_SP_channel _ C.channel_cptp
  · simp only [hi, if_false]; exact g63c_SP_id

lemma g63c_branch_herm {n : ℕ} {H K : Type*} [Fintype H] [DecidableEq H] [Fintype K]
    (C : FeedbackProtocol n H K) (rho : Matrix (Fin n → H) (Fin n → H) ℂ) (hr : rho.IsHermitian)
    (h : Fin n → K) : (C.branch rho h).IsHermitian := by
  unfold FeedbackProtocol.branch
  generalize List.ofFn (fun t : Fin n => (t, h t)) = l
  induction l generalizing rho with
  | nil => simpa using hr
  | cons a l ih =>
    simp only [List.foldl_cons]
    apply ih
    unfold Matrix.IsHermitian
    rw [← g63c_SP_step C a.1 a.2 rho, hr.eq]

theorem solution {n : ℕ} (hn : 0 < n)
    {S A H K : Type*} [Fintype S] [DecidableEq S] [Nonempty S] [Fintype A] [DecidableEq A]
    [Nonempty A] [Fintype H] [DecidableEq H] [Nonempty H]
    [Fintype K] [DecidableEq K] [Nonempty K]
    (src : FiniteAEPSource S) (c : (Fin n → S) → (Fin n → A))
    (rho : (Fin n → A) → Matrix (Fin n → H) (Fin n → H) ℂ)
    (hrho : ∀ m, IsDensityMatrix (rho (c m))) (C : FeedbackProtocol n H K) :
    conditionalInfo (terminalState src c rho C) = 0 := by
  classical
  set p := src.probability n with hp
  set R : (Fin n → A) → (Fin n → K) → Matrix (Fin n → H) (Fin n → H) ℂ :=
    fun a h => C.branch (rho a) h with hRdef
  have hR : ∀ m h, (R (c m) h).IsHermitian := fun m h =>
    g63c_branch_herm C _ (hrho m).1.isHermitian h
  set q : (Fin n → A) → ℝ := fun a => ∑ m, if c m = a then p m else 0 with hq
  have hq0 : ∀ a, 0 ≤ q a := fun a =>
    Finset.sum_nonneg (fun m _ => by split_ifs; exacts [src.nonnegative _ _, le_rfl])
  have hqR : ∀ a h, q a ≠ 0 → (R a h).IsHermitian := by
    intro a h hqa
    obtain ⟨m, -, hm⟩ := Finset.exists_ne_zero_of_sum_ne_zero hqa
    have : c m = a := by by_contra hc; simp [hc] at hm
    subst this; exact hR m h
  set T : (Fin n → A) → ℝ := fun a => ∑ h, (R a h).trace.re with hT
  set X := terminalState src c rho C with hX
  have hXe : ∀ u v, X u v = if u.1 = v.1 ∧ u.2.1 = c u.1 ∧ v.2.1 = c u.1 then
      (p u.1 : ℂ) * (if u.2.2.1 = v.2.2.1 then R (c u.1) u.2.2.1 u.2.2.2 v.2.2.2 else 0)
      else 0 := by
    intro u v
    simp only [hX, terminalState, FeedbackProtocol.receiver, hRdef, hp]
    congr
  have hsR : ∀ (m : Fin n → S) (a : Fin n → A) (h : Fin n → K),
      (if a = c m then p m else 0) ≠ 0 → (R a h).IsHermitian := by
    intro m a h hne
    by_cases hac : a = c m
    · subst hac; exact hR m h
    · simp [hac] at hne
  have hs0 : ∀ (m : Fin n → S) (a : Fin n → A), 0 ≤ (if a = c m then p m else 0) := by
    intro m a; split_ifs; exacts [src.nonnegative _ _, le_rfl]
  -- S(MAZ)
  have hS1 : vnEntropy X = ∑ m, (-(p m * Real.logb 2 (p m)) * T (c m) +
      p m * ∑ h, vnEntropy (R (c m) h)) := by
    let e1 : (Fin n → S) × ((Fin n → A) × ((Fin n → K) × (Fin n → H))) ≃
        (Fin n → H) × ((Fin n → S) × ((Fin n → A) × (Fin n → K))) :=
      { toFun := fun u => (u.2.2.2, (u.1, (u.2.1, u.2.2.1)))
        invFun := fun w => (w.2.1, (w.2.2.1, (w.2.2.2, w.1)))
        left_inv := fun _ => rfl, right_inv := fun _ => rfl }
    rw [g63c_ent_block e1 X (fun j => (((if j.2.1 = c j.1 then p j.1 else 0 : ℝ)) : ℂ) • R j.2.1 j.2.2)
      (fun j => g63c_herm_smul _ _ (hsR j.1 j.2.1 j.2.2))]
    · rw [Fintype.sum_prod_type]
      refine Finset.sum_congr rfl (fun m _ => ?_)
      rw [Fintype.sum_prod_type, Finset.sum_eq_single (c m)]
      · simp only [eq_self_iff_true, if_true]
        rw [Finset.sum_congr rfl (fun h _ => g63c_ent_smul (R (c m) h) (p m) (src.nonnegative _ _)
          (fun _ => hR m h)), Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
      · intro a _ ha
        refine Finset.sum_eq_zero (fun h _ => ?_)
        simp [ha, vnEntropy]
      · simp
    · rintro ⟨m, a, h, x⟩ ⟨m', a', h', x'⟩
      rw [hXe]
      simp only [e1, Equiv.coe_fn_mk, Prod.mk.injEq, Matrix.smul_apply, smul_eq_mul]
      split_ifs <;> (try simp_all) <;> aesop
  have hqC : ∀ a, ((q a : ℝ) : ℂ) = ∑ m, if c m = a then (p m : ℂ) else 0 := by
    intro a; simp only [hq]; push_cast; refine Finset.sum_congr rfl (fun m _ => ?_)
    split_ifs <;> simp
  -- traceLeft entries
  have hL : ∀ a z a' z', traceLeft X (a, z) (a', z') =
      if a = a' ∧ z.1 = z'.1 then (q a : ℂ) * R a z.1 z.2 z'.2 else 0 := by
    rintro a ⟨h, x⟩ a' ⟨h', x'⟩
    simp only [traceLeft, Matrix.of_apply, hXe]
    by_cases ha : a = a'
    · subst ha
      by_cases hh : h = h'
      · subst hh
        simp only [true_and, if_true, and_self, hqC, Finset.sum_mul]
        refine Finset.sum_congr rfl (fun m _ => ?_)
        by_cases hc : a = c m
        · subst hc; simp
        · simp [hc, Ne.symm hc]
      · simp [hh]
    · simp only [ha, false_and, if_false]
      refine Finset.sum_eq_zero (fun m _ => ?_)
      rw [if_neg]
      rintro ⟨-, h1, h2⟩
      exact ha (h1.trans h2.symm)
  have hTC : ∀ a, (∀ h, (R a h).IsHermitian) →
      ((T a : ℝ) : ℂ) = ∑ z : (Fin n → K) × (Fin n → H), R a z.1 z.2 z.2 := by
    intro a ha
    rw [Fintype.sum_prod_type]
    simp only [hT]; push_cast
    refine Finset.sum_congr rfl (fun h _ => ?_)
    rw [g63c_tr_real _ (ha h)]; rfl
  -- S(AZ)
  have hS3 : vnEntropy (traceLeft X) = ∑ a, (-(q a * Real.logb 2 (q a)) * T a +
      q a * ∑ h, vnEntropy (R a h)) := by
    let e3 : (Fin n → A) × ((Fin n → K) × (Fin n → H)) ≃
        (Fin n → H) × ((Fin n → A) × (Fin n → K)) :=
      { toFun := fun u => (u.2.2, (u.1, u.2.1))
        invFun := fun w => (w.2.1, (w.2.2, w.1))
        left_inv := fun _ => rfl, right_inv := fun _ => rfl }
    rw [g63c_ent_block e3 (traceLeft X) (fun j => ((q j.1 : ℝ) : ℂ) • R j.1 j.2)
      (fun j => g63c_herm_smul _ _ (hqR j.1 j.2))]
    · rw [Fintype.sum_prod_type]
      refine Finset.sum_congr rfl (fun a _ => ?_)
      rw [Finset.sum_congr rfl (fun h _ => g63c_ent_smul (R a h) (q a) (hq0 a) (hqR a h)),
        Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    · rintro ⟨a, h, x⟩ ⟨a', h', x'⟩
      rw [hL]
      simp only [e3, Equiv.coe_fn_mk, Prod.mk.injEq, Matrix.smul_apply, smul_eq_mul]
  -- S(A)
  have hS4 : vnEntropy (traceRight (traceLeft X)) =
      ∑ a, -(q a * T a * Real.logb 2 (q a * T a)) := by
    let e4 : (Fin n → A) ≃ Unit × (Fin n → A) :=
      { toFun := fun a => ((), a), invFun := fun w => w.2,
        left_inv := fun _ => rfl, right_inv := fun _ => rfl }
    rw [g63c_ent_block e4 _ (fun a => ((q a * T a : ℝ) : ℂ) • (1 : Matrix Unit Unit ℂ))
      (fun a => g63c_herm_smul _ _ (fun _ => Matrix.isHermitian_one))]
    · exact Finset.sum_congr rfl (fun a _ => g63c_ent_scalar' _)
    · intro a a'
      simp only [traceRight, Matrix.of_apply, hL, and_true, e4, Equiv.coe_fn_mk,
        Matrix.smul_apply, smul_eq_mul, Matrix.one_apply_eq, mul_one]
      by_cases ha : a = a'
      · subst ha
        simp only [if_true]
        rcases eq_or_ne (q a) 0 with h0 | h0
        · simp [h0]
        · rw [Complex.ofReal_mul, hTC a (fun h => hqR a h h0), Finset.mul_sum]
      · simp [ha]
  -- S(MA)
  have hS2 : vnEntropy (Matrix.of (fun u v : (Fin n → S) × (Fin n → A) =>
      ∑ z : (Fin n → K) × (Fin n → H), X (u.1, (u.2, z)) (v.1, (v.2, z)))) =
      ∑ m, -(p m * T (c m) * Real.logb 2 (p m * T (c m))) := by
    let e2 : (Fin n → S) × (Fin n → A) ≃ Unit × ((Fin n → S) × (Fin n → A)) :=
      { toFun := fun a => ((), a), invFun := fun w => w.2,
        left_inv := fun _ => rfl, right_inv := fun _ => rfl }
    rw [g63c_ent_block e2 _ (fun j => (((if j.2 = c j.1 then p j.1 * T j.2 else 0 : ℝ)) : ℂ) •
      (1 : Matrix Unit Unit ℂ))
      (fun a => g63c_herm_smul _ _ (fun _ => Matrix.isHermitian_one))]
    · rw [Fintype.sum_prod_type]
      refine Finset.sum_congr rfl (fun m _ => ?_)
      rw [Finset.sum_eq_single (c m)]
      · rw [g63c_ent_scalar', if_pos rfl]
      · intro a _ ha
        rw [if_neg ha, g63c_ent_scalar']; simp
      · simp
    · rintro ⟨m, a⟩ ⟨m', a'⟩
      simp only [Matrix.of_apply, hXe, e2, Equiv.coe_fn_mk, Matrix.smul_apply, smul_eq_mul,
        Matrix.one_apply_eq, mul_one, if_true]
      by_cases hc : m = m' ∧ a = c m ∧ a' = c m
      · obtain ⟨rfl, rfl, rfl⟩ := hc
        simp only [and_self, if_true]
        rw [Complex.ofReal_mul, hTC (c m) (hR m), Finset.mul_sum]
      · rw [Finset.sum_eq_zero (fun z _ => if_neg hc)]
        split_ifs with h1 h2
        · exfalso; apply hc; simp only [Prod.mk.injEq] at h1; obtain ⟨rfl, rfl⟩ := h1
          exact ⟨rfl, h2, h2⟩
        · simp
        · rfl
  have heta : ∀ x y : ℝ, x * y * Real.logb 2 (x * y) =
      x * y * Real.logb 2 x + x * y * Real.logb 2 y := by
    intro x y
    rcases eq_or_ne x 0 with hx | hx
    · simp [hx]
    rcases eq_or_ne y 0 with hy | hy
    · simp [hy]
    rw [Real.logb_mul hx hy]; ring
  have hqF : ∀ F : (Fin n → A) → ℝ, ∑ a, q a * F a = ∑ m, p m * F (c m) := by
    intro F
    simp only [hq, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun m _ => ?_)
    simp only [ite_mul, zero_mul]
    rw [Finset.sum_ite_eq]
    simp
  set G : (Fin n → A) → ℝ := fun a => T a * Real.logb 2 (T a) + ∑ h, vnEntropy (R a h) with hG
  have h1 := hqF G
  unfold conditionalInfo
  rw [hS2, hS3, hS4, hS1]
  simp only [heta]
  have A1 : ∑ m, -(p m * T (c m) * Real.logb 2 (p m) + p m * T (c m) * Real.logb 2 (T (c m))) -
      ∑ m, (-(p m * Real.logb 2 (p m)) * T (c m) + p m * ∑ h, vnEntropy (R (c m) h)) =
      -∑ m, p m * G (c m) := by
    rw [← Finset.sum_sub_distrib, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl (fun m _ => ?_)
    simp only [hG]; ring
  have A2 : ∑ a, (-(q a * Real.logb 2 (q a)) * T a + q a * ∑ h, vnEntropy (R a h)) -
      ∑ a, -(q a * T a * Real.logb 2 (q a) + q a * T a * Real.logb 2 (T a)) =
      ∑ a, q a * G a := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    simp only [hG]; ring
  linarith
