-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Claimed50.P38.coherentInformation_convexCombination
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T09:43:27.050859+00:00
-- url     : https://prove2.me/submissions/cc948080-64cf-4a58-847b-fce7f9fc0dcb

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P38
noncomputable section

open QAlgorithms QAlgorithms.Papers QAlgorithms.Papers.Independent QAlgorithms.Papers.Independent.Claimed50 QAlgorithms.Papers.Independent.Claimed50.P38

open scoped ComplexConjugate Matrix

open Filter

open QAlgorithms.Papers.Independent.Information100.P58 (Word)

section G68ILIB
open QAlgorithms QAlgorithms.Papers.Independent.Claimed50.P38
open scoped ComplexConjugate Matrix ComplexOrder
open QAlgorithms.Papers.Independent.Information100.P58 (Word)

lemma g68i_tens_single {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (M : Superop A A) (u v α β : A × B) :
    tensorSuperop M (completeDephasing (A := B)) (Matrix.single u v 1) α β =
      M (Matrix.single u.1 v.1 1) α.1 β.1 *
        (if u.2 = α.2 ∧ v.2 = β.2 ∧ α.2 = β.2 then 1 else 0) := by
  unfold tensorSuperop
  rw [Finset.sum_eq_single u, Finset.sum_eq_single v]
  · simp only [Matrix.single_apply_same, one_mul, completeDephasing]
    by_cases h : α.2 = β.2
    · simp only [h, if_true, Matrix.single_apply]
      by_cases h1 : u.2 = β.2 <;> by_cases h2 : v.2 = β.2 <;> simp [h1, h2, eq_comm]
    · simp [h]
  · intro j _ hj; simp [Matrix.single_apply, Ne.symm hj]
  · intro h; simp at h
  · intro i _ hi
    refine Finset.sum_eq_zero (fun j _ => ?_)
    simp [Matrix.single_apply, Ne.symm hi]
  · intro h; simp at h

lemma g68i_pi_smul {ι κ : Type*} [Fintype ι] [DecidableEq ι] {k : ℕ}
    (Φ : Fin k → Superop ι κ) (c : ℂ) (X : Matrix (Fin k → ι) (Fin k → ι) ℂ) :
    piSuperop Φ (c • X) = c • piSuperop Φ X := by
  ext y y'
  simp only [piSuperop, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc]

lemma g68i_pi_zero {ι κ : Type*} [Fintype ι] [DecidableEq ι] {k : ℕ}
    (Φ : Fin k → Superop ι κ) :
    piSuperop Φ (0 : Matrix (Fin k → ι) (Fin k → ι) ℂ) = 0 := by
  ext y y'
  simp [piSuperop]

lemma g68i_deph_apply {d delta n : ℕ} (M : Superop (Fin d) (Fin d))
    (R : Matrix (Word n d × Word n delta) (Word n d × Word n delta) ℂ)
    (a b : Word n d × Word n delta) :
    dephasedPower M n R a b =
      if a.2 = b.2 then piSuperop (fun _ : Fin n => M) (conditionalBlock R a.2) a.1 b.1 else 0 := by
  unfold dephasedPower piSuperop
  simp only [Matrix.of_apply, g68i_tens_single, Finset.prod_mul_distrib, Finset.prod_boole]
  let e : (Word n d × Word n delta) ≃ (Fin n → Fin d × Fin delta) :=
    { toFun := fun p k => (p.1 k, p.2 k), invFun := fun x => (fun k => (x k).1, fun k => (x k).2),
      left_inv := fun _ => rfl, right_inv := fun _ => rfl }
  rw [← e.sum_comp]
  simp_rw [← e.sum_comp (fun x => _ * _)]
  simp only [e, Equiv.coe_fn_mk, Finset.mem_univ, true_implies]
  have hc : ∀ p q : Word n d × Word n delta,
      (∀ i, p.2 i = a.2 i ∧ q.2 i = b.2 i ∧ a.2 i = b.2 i) ↔ (p.2 = a.2 ∧ q.2 = b.2 ∧ a.2 = b.2) := by
    intro p q
    simp only [funext_iff, forall_and]
  simp only [hc, Fintype.sum_prod_type]
  split_ifs with h
  · refine Finset.sum_congr rfl (fun x _ => ?_)
    rw [Fintype.sum_eq_single a.2 (fun x1 hx1 => Finset.sum_eq_zero (fun x2 _ =>
      Finset.sum_eq_zero (fun x3 _ => by simp [hx1])))]
    refine Finset.sum_congr rfl (fun x2 _ => ?_)
    rw [Fintype.sum_eq_single b.2 (fun x3 hx3 => by simp [hx3])]
    simp [h, conditionalBlock]
  · simp [h]

open scoped ComplexOrder in
lemma g68i_block_psd {A B : Type*} [Fintype A] [Fintype B]
    (R : Matrix (A × B) (A × B) ℂ) (hR : R.PosSemidef) (b : B) :
    (conditionalBlock R b).PosSemidef := by
  have : conditionalBlock R b = R.submatrix (fun i => (i, b)) (fun i => (i, b)) := rfl
  rw [this]; exact hR.submatrix _

open scoped ComplexOrder in
lemma g68i_weight_nonneg {A B : Type*} [Fintype A] [Fintype B]
    (R : Matrix (A × B) (A × B) ℂ) (hR : R.PosSemidef) (b : B) : 0 ≤ branchWeight R b := by
  have := (g68i_block_psd R hR b).trace_nonneg
  exact (Complex.nonneg_iff.1 this).1

open scoped ComplexOrder in
lemma g68i_block_zero {A B : Type*} [Fintype A] [Fintype B]
    (R : Matrix (A × B) (A × B) ℂ) (hR : R.PosSemidef) (b : B) (hw : ¬ 0 < branchWeight R b) :
    conditionalBlock R b = 0 := by
  have hP := g68i_block_psd R hR b
  have h0 : branchWeight R b = 0 := le_antisymm (not_lt.1 hw) (g68i_weight_nonneg R hR b)
  have ht := hP.trace_nonneg
  rw [Complex.nonneg_iff] at ht
  apply hP.trace_eq_zero_iff.1
  apply Complex.ext
  · simpa [branchWeight] using h0
  · simpa using ht.2.symm

lemma g68i_weight_smul {d delta n : ℕ} (Φ : Fin n → Superop (Fin d) (Fin d))
    (R : Matrix (Word n d × Word n delta) (Word n d × Word n delta) ℂ) (hR : R.PosSemidef)
    (a0 : Word n d) (c : Word n delta) :
    (branchWeight R c : ℂ) • piSuperop Φ (conditionalState a0 R c) =
      piSuperop Φ (conditionalBlock R c) := by
  unfold conditionalState
  split_ifs with h
  · rw [g68i_pi_smul, smul_smul, mul_inv_cancel₀ (by exact_mod_cast h.ne'), one_smul]
  · have h0 : branchWeight R c = 0 := le_antisymm (not_lt.1 h) (g68i_weight_nonneg R hR c)
    rw [g68i_block_zero R hR c h, h0, g68i_pi_zero]
    simp

lemma g68i_pure_ket {B : Type*} [DecidableEq B] (c x y : B) :
    pureDensity (ket c) x y = if x = c ∧ y = c then 1 else 0 := by
  simp only [pureDensity, ket, Matrix.of_apply]
  by_cases hx : x = c <;> by_cases hy : y = c <;> simp [hx, hy, EuclideanSpace.single_apply]

theorem g68i_deph_block (d delta n : ℕ)
    (M : Superop (Fin d) (Fin d))
    (R : Matrix (Word n d × Word n delta) (Word n d × Word n delta) ℂ)
    (hR : IsDensityMatrix R) (a0 : Word n d) :
    dephasedPower M n R = ∑ b : Word n delta,
      (branchWeight R b : ℂ) • Matrix.kronecker
        (piSuperop (fun _ : Fin n => M) (conditionalState a0 R b))
        (pureDensity (ket b)) := by
  ext ⟨a1, a2⟩ ⟨b1, b2⟩
  rw [g68i_deph_apply, Matrix.sum_apply]
  simp only [Matrix.smul_apply, Matrix.kronecker, Matrix.kroneckerMap_apply, g68i_pure_ket,
    smul_eq_mul]
  rw [Fintype.sum_eq_single a2 (fun c hc => by simp [Ne.symm hc])]
  by_cases h1 : a2 = b2
  · subst h1
    simp only [and_self, if_true, mul_one, if_pos rfl]
    rw [← g68i_weight_smul _ R hR.1 a0]
    simp [Matrix.smul_apply]
  · simp [h1, Ne.symm h1]

lemma g68i_withRef_apply {A C : Type*} (f : Superop A A) (X : Matrix (A × C) (A × C) ℂ)
    (x y : A × C) :
    withReference f X x y = f (Matrix.of fun i i' => X (i, x.2) (i', y.2)) x.1 y.1 := rfl

lemma g68i_purified_apply {d delta n : ℕ} {C : Type*} (M : Superop (Fin d) (Fin d))
    (psi : EuclideanSpace ℂ ((Word n d × Word n delta) × C))
    (a b : (Word n d × C) × Word n delta) :
    purifiedOutput M n psi a b = if a.2 = b.2 then piSuperop (fun _ : Fin n => M)
      (Matrix.of fun x x' => psi ((x, a.2), a.1.2) * conj (psi ((x', a.2), b.1.2))) a.1.1 b.1.1
      else 0 := by
  unfold purifiedOutput
  rw [g68i_withRef_apply, g68i_deph_apply]
  rfl

lemma g68i_weight_psi {d delta n : ℕ} {C : Type*} [Fintype C]
    (R : Matrix (Word n d × Word n delta) (Word n d × Word n delta) ℂ)
    (psi : EuclideanSpace ℂ ((Word n d × Word n delta) × C))
    (hpurifies : traceRight (pureDensity psi) = R) (b : Word n delta) :
    branchWeight R b = ∑ x : Word n d, ∑ c : C, Complex.normSq (psi ((x, b), c)) := by
  rw [← hpurifies]
  simp only [branchWeight, conditionalBlock, Matrix.trace, Matrix.diag_apply, traceRight,
    pureDensity, Matrix.of_apply, Complex.re_sum, Complex.mul_conj, Complex.ofReal_re]

lemma g68i_psi_zero {d delta n : ℕ} {C : Type*} [Fintype C]
    (R : Matrix (Word n d × Word n delta) (Word n d × Word n delta) ℂ)
    (psi : EuclideanSpace ℂ ((Word n d × Word n delta) × C))
    (hpurifies : traceRight (pureDensity psi) = R) (b : Word n delta)
    (hw : ¬ 0 < branchWeight R b) (x : Word n d) (c : C) : psi ((x, b), c) = 0 := by
  rw [g68i_weight_psi R psi hpurifies b] at hw
  have h0 : ∑ x : Word n d, ∑ c : C, Complex.normSq (psi ((x, b), c)) = 0 :=
    le_antisymm (not_lt.1 hw) (Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg
      (fun _ _ => Complex.normSq_nonneg _)))
  rw [Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => Finset.sum_nonneg
      (fun _ _ => Complex.normSq_nonneg _))] at h0
  have h1 := h0 x (Finset.mem_univ _)
  rw [Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => Complex.normSq_nonneg _)] at h1
  exact Complex.normSq_eq_zero.1 (h1 c (Finset.mem_univ _))

lemma g68i_purif_smul {d delta n : ℕ} {C : Type*} [Fintype C] [DecidableEq C]
    (Φ : Fin n → Superop (Fin d) (Fin d))
    (R : Matrix (Word n d × Word n delta) (Word n d × Word n delta) ℂ)
    (psi : EuclideanSpace ℂ ((Word n d × Word n delta) × C))
    (hpurifies : traceRight (pureDensity psi) = R) (a0 : Word n d) (c0 : C)
    (b : Word n delta) (c c' : C) :
    (branchWeight R b : ℂ) • piSuperop Φ (Matrix.of fun x x' =>
        pureDensity (conditionalPurification a0 c0 R psi b) (x, c) (x', c')) =
      piSuperop Φ (Matrix.of fun x x' => psi ((x, b), c) * conj (psi ((x', b), c'))) := by
  rw [← g68i_pi_smul]
  congr 1
  ext x x'
  simp only [Matrix.smul_apply, Matrix.of_apply, pureDensity, conditionalPurification, smul_eq_mul]
  split_ifs with h
  · have hs : ((Real.sqrt (branchWeight R b) : ℂ)) ^ 2 = (branchWeight R b : ℂ) := by
      rw [← Complex.ofReal_pow, Real.sq_sqrt h.le]
    have hs0 : ((Real.sqrt (branchWeight R b) : ℂ)) ≠ 0 := by
      exact_mod_cast (Real.sqrt_pos.2 h).ne'
    simp only [PiLp.toLp_apply, map_div₀, Complex.conj_ofReal]
    rw [← hs]
    field_simp
  · rw [g68i_psi_zero R psi hpurifies b h x c]
    have h0 : branchWeight R b = 0 := by
      rw [g68i_weight_psi R psi hpurifies b]
      refine Finset.sum_eq_zero (fun x _ => Finset.sum_eq_zero (fun c _ => ?_))
      rw [g68i_psi_zero R psi hpurifies b h x c]; simp
    simp [h0]

theorem g68i_purif_block (d delta n : ℕ) {C : Type*} [Fintype C] [DecidableEq C]
    (M : Superop (Fin d) (Fin d))
    (R : Matrix (Word n d × Word n delta) (Word n d × Word n delta) ℂ)
    (psi : EuclideanSpace ℂ ((Word n d × Word n delta) × C))
    (hpurifies : traceRight (pureDensity psi) = R)
    (a0 : Word n d) (c0 : C) :
    purifiedOutput M n psi = ∑ b : Word n delta,
      (branchWeight R b : ℂ) • Matrix.kronecker
        (withReference (piSuperop (fun _ : Fin n => M))
          (pureDensity (conditionalPurification a0 c0 R psi b)))
        (pureDensity (ket b)) := by
  ext ⟨⟨a1, c⟩, a2⟩ ⟨⟨b1, c'⟩, b2⟩
  rw [g68i_purified_apply, Matrix.sum_apply]
  simp only [Matrix.smul_apply, Matrix.kronecker, Matrix.kroneckerMap_apply, g68i_pure_ket,
    smul_eq_mul]
  rw [Fintype.sum_eq_single a2 (fun c hc => by simp [Ne.symm hc])]
  by_cases h1 : a2 = b2
  · subst h1
    simp only [and_self, if_true, mul_one, if_pos rfl]
    rw [← g68i_purif_smul _ R psi hpurifies a0 c0, g68i_withRef_apply]
    simp [Matrix.smul_apply]
  · simp [h1, Ne.symm h1]

lemma g68i_tp_channel {ι : Type*} [Fintype ι] [DecidableEq ι] (Φ : Superop ι ι)
    (h : IsChannel Φ) (X : Matrix ι ι ℂ) : (Φ X).trace = X.trace := by
  obtain ⟨m, E, hK, hE⟩ := h
  rw [hE]
  simp only [krausApply, Matrix.trace_sum]
  simp_rw [Matrix.trace_mul_cycle (E _) X]
  rw [← Matrix.trace_sum, ← Finset.sum_mul]
  unfold IsKrausFamily at hK
  rw [hK, one_mul]

lemma g68i_tp_pi {ι : Type*} [Fintype ι] [DecidableEq ι] {k : ℕ}
    (Φ : Fin k → Superop ι ι) (h : ∀ i X, (Φ i X).trace = X.trace)
    (X : Matrix (Fin k → ι) (Fin k → ι) ℂ) : (piSuperop Φ X).trace = X.trace := by
  simp only [Matrix.trace, Matrix.diag_apply, piSuperop, Matrix.of_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum]
  have hp : ∀ x' : Fin k → ι, ∑ y : Fin k → ι, ∏ i, Φ i (Matrix.single (x i) (x' i) 1) (y i) (y i)
      = if x = x' then 1 else 0 := by
    intro x'
    have := (Finset.prod_univ_sum (fun _ : Fin k => (Finset.univ : Finset ι))
      (fun i t => Φ i (Matrix.single (x i) (x' i) 1) t t)).symm
    rw [Fintype.piFinset_univ] at this
    rw [this]
    have h2 : ∀ i, ∑ t, Φ i (Matrix.single (x i) (x' i) 1) t t = if x i = x' i then 1 else 0 := by
      intro i
      have := h i (Matrix.single (x i) (x' i) 1)
      simp only [Matrix.trace, Matrix.diag_apply] at this
      rw [this]
      by_cases hx : x i = x' i
      · simp [hx, Matrix.single_apply]
      · rw [if_neg hx]
        refine Finset.sum_eq_zero (fun t _ => ?_)
        simp only [Matrix.single_apply]
        split_ifs with h3
        · exact absurd (h3.1.trans h3.2.symm) hx
        · rfl
    simp_rw [h2]
    rw [Finset.prod_boole]
    simp [funext_iff]
  simp_rw [hp, mul_ite, mul_one, mul_zero]
  simp

lemma g68i_SP_pi {ι : Type*} [Fintype ι] [DecidableEq ι] {k : ℕ}
    (Φ : Fin k → Superop ι ι) (h : ∀ i X, Φ i Xᴴ = (Φ i X)ᴴ) (X : Matrix (Fin k → ι) (Fin k → ι) ℂ) :
    piSuperop Φ Xᴴ = (piSuperop Φ X)ᴴ := by
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

lemma g68i_SP_channel {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] (Φ : Superop ι κ)
    (h : IsChannel Φ) (X : Matrix ι ι ℂ) : Φ Xᴴ = (Φ X)ᴴ := by
  obtain ⟨m, E, -, hE⟩ := h
  rw [hE, hE]
  simp [krausApply, Matrix.conjTranspose_sum, Matrix.conjTranspose_mul, Matrix.mul_assoc]

lemma g68i_withRef_SP {A C : Type*} (f : Superop A A) (h : ∀ X, f Xᴴ = (f X)ᴴ)
    (X : Matrix (A × C) (A × C) ℂ) : withReference f Xᴴ = (withReference f X)ᴴ := by
  ext x y
  rw [Matrix.conjTranspose_apply, g68i_withRef_apply, g68i_withRef_apply]
  have : (Matrix.of fun i i' => Xᴴ (i, x.2) (i', y.2)) =
      (Matrix.of fun i i' => X (i, y.2) (i', x.2))ᴴ := by
    ext i i'; simp [Matrix.conjTranspose_apply]
  rw [this, h, Matrix.conjTranspose_apply]

lemma g68i_withRef_tp {A C : Type*} [Fintype A] [Fintype C] (f : Superop A A)
    (h : ∀ X, (f X).trace = X.trace)
    (X : Matrix (A × C) (A × C) ℂ) : (withReference f X).trace = X.trace := by
  simp only [Matrix.trace, Matrix.diag_apply, g68i_withRef_apply, Fintype.sum_prod_type]
  rw [Finset.sum_comm, Finset.sum_comm (f := fun x y => X (x, y) (x, y))]
  refine Finset.sum_congr rfl (fun c _ => ?_)
  have := h (Matrix.of fun i i' => X (i, c) (i', c))
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.of_apply] at this
  rw [this]
lemma g68i_trace_cfc_family {X J κ : Type*} [Fintype X] [DecidableEq X] [Fintype J] [DecidableEq J]
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
lemma g68i_trace_cfc_block {X J κ : Type*} [Fintype X] [DecidableEq X] [Fintype J] [DecidableEq J]
    [Fintype κ] [DecidableEq κ] (e : X ≃ κ × J)
    (P : Matrix X X ℂ) (Q : J → Matrix κ κ ℂ) (hQ : ∀ j, (Q j).IsHermitian)
    (hPQ : ∀ u v, P u v = if (e u).2 = (e v).2 then Q (e u).2 (e u).1 (e v).1 else 0)
    (f : ℝ → ℝ) (hf : f 0 = 0) :
    (cfc f P).trace = ∑ j, (cfc f (Q j)).trace := by
  have hP : P = (Matrix.blockDiagonal Q).submatrix e e := by
    ext u v; rw [hPQ]; rfl
  have hH : P.IsHermitian := by
    rw [hP]; exact (Matrix.isHermitian_blockDiagonal_iff.2 hQ).submatrix _
  refine g68i_trace_cfc_family P Q hH hQ f hf (fun k => ?_)
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

lemma g68i_ent_smul {κ : Type*} [Fintype κ] [DecidableEq κ] (R : Matrix κ κ ℂ) (s : ℝ)
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

lemma g68i_ent_scalar (r : ℝ) (hr : 0 ≤ r) :
    vnEntropy ((r : ℂ) • (1 : Matrix Unit Unit ℂ)) = -(r * Real.logb 2 r) := by
  rw [g68i_ent_smul _ r hr (fun _ => Matrix.isHermitian_one)]
  simp [vnEntropy]

lemma g68i_ent_scalar' (r : ℝ) :
    vnEntropy ((r : ℂ) • (1 : Matrix Unit Unit ℂ)) = -(r * Real.logb 2 r) := by
  have : (r : ℂ) • (1 : Matrix Unit Unit ℂ) = algebraMap ℝ (Matrix Unit Unit ℂ) r := by
    ext i j; simp [Matrix.algebraMap_matrix_apply, Matrix.one_apply]
  unfold vnEntropy
  rw [this, cfc_algebraMap, Matrix.trace, Fintype.sum_unique, Matrix.diag_apply,
    Matrix.algebraMap_matrix_apply, if_pos rfl]
  simp

lemma g68i_tr_real {κ : Type*} [Fintype κ] (M : Matrix κ κ ℂ) (hM : M.IsHermitian) :
    ((M.trace.re : ℝ) : ℂ) = M.trace := by
  apply Complex.ext
  · simp
  · simp only [Complex.ofReal_im, Matrix.trace, Matrix.diag_apply, Complex.im_sum]
    symm
    refine Finset.sum_eq_zero (fun i _ => ?_)
    have := hM.apply i i
    exact (Complex.conj_eq_iff_im.1 this)

lemma g68i_herm_smul {κ : Type*} [Fintype κ] (R : Matrix κ κ ℂ) (s : ℝ)
    (hR : s ≠ 0 → R.IsHermitian) : ((s : ℂ) • R).IsHermitian := by
  rcases eq_or_ne s 0 with h | h
  · subst h; simp
  · have hR' := hR h
    unfold Matrix.IsHermitian
    rw [Matrix.conjTranspose_smul, hR'.eq]
    simp

lemma g68i_ent_block {X J κ : Type*} [Fintype X] [DecidableEq X] [Fintype J] [DecidableEq J]
    [Fintype κ] [DecidableEq κ] (e : X ≃ κ × J)
    (P : Matrix X X ℂ) (Q : J → Matrix κ κ ℂ) (hQ : ∀ j, (Q j).IsHermitian)
    (hPQ : ∀ u v, P u v = if (e u).2 = (e v).2 then Q (e u).2 (e u).1 (e v).1 else 0) :
    vnEntropy P = ∑ j, vnEntropy (Q j) := by
  unfold vnEntropy
  rw [g68i_trace_cfc_block e P Q hQ hPQ _ (by simp)]
  simp [Complex.re_sum]

def g68i_SP {ι κ : Type*} (f : Matrix ι ι ℂ → Matrix κ κ ℂ) : Prop := ∀ X, f Xᴴ = (f X)ᴴ

lemma g68i_pure_herm {ι : Type*} (ψ : EuclideanSpace ℂ ι) : (pureDensity ψ).IsHermitian := by
  ext a b
  simp [pureDensity, Matrix.conjTranspose_apply, mul_comm]

lemma g68i_block_herm {A B : Type*} (R : Matrix (A × B) (A × B) ℂ) (hR : R.IsHermitian) (b : B) :
    (conditionalBlock R b).IsHermitian := by
  ext i j
  have := congrFun (congrFun hR (i, b)) (j, b)
  simpa [conditionalBlock, Matrix.conjTranspose_apply] using this

lemma g68i_block_trace {A B : Type*} [Fintype A] (R : Matrix (A × B) (A × B) ℂ) (hR : R.IsHermitian)
    (b : B) : (conditionalBlock R b).trace = (branchWeight R b : ℂ) :=
  (g68i_tr_real _ (g68i_block_herm R hR b)).symm

lemma g68i_pure_ket_trace {B : Type*} [Fintype B] [DecidableEq B] (c : B) :
    (pureDensity (ket c)).trace = 1 := by
  simp [Matrix.trace, g68i_pure_ket]

lemma g68i_cond_herm {A B : Type*} [Fintype A] [DecidableEq A] (a0 : A)
    (R : Matrix (A × B) (A × B) ℂ) (hR : R.IsHermitian) (b : B) :
    (conditionalState a0 R b).IsHermitian := by
  unfold conditionalState
  split_ifs
  · rw [← Complex.ofReal_inv]; exact g68i_herm_smul _ _ (fun _ => g68i_block_herm R hR b)
  · exact g68i_pure_herm _

lemma g68i_cond_trace {A B : Type*} [Fintype A] [DecidableEq A] (a0 : A)
    (R : Matrix (A × B) (A × B) ℂ) (hR : R.IsHermitian) (b : B) :
    (conditionalState a0 R b).trace = 1 := by
  unfold conditionalState
  split_ifs with h
  · rw [Matrix.trace_smul, g68i_block_trace R hR, smul_eq_mul, inv_mul_cancel₀]
    exact_mod_cast h.ne'
  · exact g68i_pure_ket_trace a0

lemma g68i_logb_conv (d : ℕ) (hd : 2 ≤ d) (w : ℝ) :
    w * Real.logb 2 w / Real.logb 2 d = w * Real.logb d w := by
  have h2 : Real.log 2 ≠ 0 := by positivity
  have hd' : Real.log d ≠ 0 := by
    have : (1:ℝ) < d := by exact_mod_cast (by omega : 1 < d)
    exact (Real.log_pos this).ne'
  unfold Real.logb
  field_simp

theorem g68i_deph_entropy (d delta n : ℕ) (hd : 2 ≤ d)
    (M : Superop (Fin d) (Fin d)) (hM : IsChannel M)
    (R : Matrix (Word n d × Word n delta) (Word n d × Word n delta) ℂ)
    (hR : IsDensityMatrix R) (a0 : Word n d) :
    entropyD d (dephasedPower M n R) = flagEntropy d R +
      ∑ b : Word n delta, branchWeight R b *
        entropyD d (piSuperop (fun _ : Fin n => M) (conditionalState a0 R b)) := by
  have hRH : R.IsHermitian := hR.1.isHermitian
  have hSP : ∀ X, piSuperop (fun _ : Fin n => M) Xᴴ = (piSuperop (fun _ : Fin n => M) X)ᴴ :=
    g68i_SP_pi _ (fun _ => g68i_SP_channel M hM)
  have hTP : ∀ X, (piSuperop (fun _ : Fin n => M) X).trace = X.trace :=
    g68i_tp_pi _ (fun _ => g68i_tp_channel M hM)
  have hQ : ∀ b, (piSuperop (fun _ : Fin n => M) (conditionalBlock R b)).IsHermitian := by
    intro b
    unfold Matrix.IsHermitian
    rw [← hSP, (g68i_block_herm R hRH b).eq]
  have hP := g68i_ent_block (Equiv.refl _) (dephasedPower M n R)
    (fun b => piSuperop (fun _ : Fin n => M) (conditionalBlock R b)) hQ
    (fun u v => g68i_deph_apply M R u v)
  have hρ : ∀ b, (piSuperop (fun _ : Fin n => M) (conditionalState a0 R b)).IsHermitian := by
    intro b
    unfold Matrix.IsHermitian
    rw [← hSP, (g68i_cond_herm a0 R hRH b).eq]
  have hent : ∀ b, vnEntropy (piSuperop (fun _ : Fin n => M) (conditionalBlock R b)) =
      -(branchWeight R b * Real.logb 2 (branchWeight R b)) +
        branchWeight R b * vnEntropy (piSuperop (fun _ : Fin n => M) (conditionalState a0 R b)) := by
    intro b
    rw [← g68i_weight_smul _ R hR.1 a0, g68i_ent_smul _ _ (g68i_weight_nonneg R hR.1 b)
      (fun _ => hρ b), hTP, g68i_cond_trace a0 R hRH b]
    simp
  unfold entropyD flagEntropy
  rw [hP]
  simp_rw [hent]
  rw [Finset.sum_add_distrib, add_div, Finset.sum_div, Finset.sum_div, ← Finset.sum_neg_distrib]
  congr 1
  · refine Finset.sum_congr rfl (fun b _ => ?_)
    rw [neg_div, g68i_logb_conv d hd]
  · refine Finset.sum_congr rfl (fun b _ => ?_)
    ring

def g68i_Y {d delta n : ℕ} {C : Type*}
    (psi : EuclideanSpace ℂ ((Word n d × Word n delta) × C)) (b : Word n delta) :
    Matrix (Word n d × C) (Word n d × C) ℂ :=
  Matrix.of fun z z' => psi ((z.1, b), z.2) * conj (psi ((z'.1, b), z'.2))

lemma g68i_Y_eq {d delta n : ℕ} {C : Type*} [Fintype C] [DecidableEq C]
    (R : Matrix (Word n d × Word n delta) (Word n d × Word n delta) ℂ)
    (psi : EuclideanSpace ℂ ((Word n d × Word n delta) × C))
    (hpurifies : traceRight (pureDensity psi) = R) (a0 : Word n d) (c0 : C)
    (b : Word n delta) :
    (branchWeight R b : ℂ) • pureDensity (conditionalPurification a0 c0 R psi b) = g68i_Y psi b := by
  ext ⟨x, c⟩ ⟨x', c'⟩
  simp only [Matrix.smul_apply, Matrix.of_apply, pureDensity, conditionalPurification, smul_eq_mul,
    g68i_Y]
  split_ifs with h
  · have hs : ((Real.sqrt (branchWeight R b) : ℂ)) ^ 2 = (branchWeight R b : ℂ) := by
      rw [← Complex.ofReal_pow, Real.sq_sqrt h.le]
    have hs0 : ((Real.sqrt (branchWeight R b) : ℂ)) ≠ 0 := by
      exact_mod_cast (Real.sqrt_pos.2 h).ne'
    simp only [PiLp.toLp_apply, map_div₀, Complex.conj_ofReal]
    rw [← hs]
    field_simp
  · rw [g68i_psi_zero R psi hpurifies b h x c]
    have h0 : branchWeight R b = 0 := by
      rw [g68i_weight_psi R psi hpurifies b]
      refine Finset.sum_eq_zero (fun x _ => Finset.sum_eq_zero (fun c _ => ?_))
      rw [g68i_psi_zero R psi hpurifies b h x c]; simp
    simp [h0]

lemma g68i_Y_trace {d delta n : ℕ} {C : Type*} [Fintype C]
    (R : Matrix (Word n d × Word n delta) (Word n d × Word n delta) ℂ)
    (psi : EuclideanSpace ℂ ((Word n d × Word n delta) × C))
    (hpurifies : traceRight (pureDensity psi) = R) (b : Word n delta) :
    (g68i_Y psi b).trace = (branchWeight R b : ℂ) := by
  rw [g68i_weight_psi R psi hpurifies b]
  simp only [Matrix.trace, Matrix.diag_apply, g68i_Y, Matrix.of_apply, Fintype.sum_prod_type,
    Complex.ofReal_sum, Complex.mul_conj]

lemma g68i_Y_herm {d delta n : ℕ} {C : Type*}
    (psi : EuclideanSpace ℂ ((Word n d × Word n delta) × C)) (b : Word n delta) :
    (g68i_Y psi b).IsHermitian := by
  ext z z'
  simp [g68i_Y, Matrix.conjTranspose_apply, mul_comm]

lemma g68i_purif_trace {d delta n : ℕ} {C : Type*} [Fintype C] [DecidableEq C]
    (R : Matrix (Word n d × Word n delta) (Word n d × Word n delta) ℂ)
    (psi : EuclideanSpace ℂ ((Word n d × Word n delta) × C))
    (hpurifies : traceRight (pureDensity psi) = R) (a0 : Word n d) (c0 : C)
    (b : Word n delta) :
    (pureDensity (conditionalPurification a0 c0 R psi b)).trace = 1 := by
  by_cases h : 0 < branchWeight R b
  · have := congrArg Matrix.trace (g68i_Y_eq R psi hpurifies a0 c0 b)
    rw [Matrix.trace_smul, g68i_Y_trace R psi hpurifies b, smul_eq_mul] at this
    have hw : (branchWeight R b : ℂ) ≠ 0 := by exact_mod_cast h.ne'
    calc _ = (branchWeight R b : ℂ)⁻¹ * ((branchWeight R b : ℂ) *
          (pureDensity (conditionalPurification a0 c0 R psi b)).trace) := by
            rw [← mul_assoc, inv_mul_cancel₀ hw, one_mul]
      _ = 1 := by rw [this, inv_mul_cancel₀ hw]
  · simp only [conditionalPurification, if_neg h]
    exact g68i_pure_ket_trace _

lemma g68i_withRef_pi_smul {d n : ℕ} {C : Type*} (Φ : Fin n → Superop (Fin d) (Fin d)) (c : ℂ)
    (X : Matrix (Word n d × C) (Word n d × C) ℂ) :
    withReference (piSuperop Φ) (c • X) = c • withReference (piSuperop Φ) X := by
  ext x y
  rw [Matrix.smul_apply, g68i_withRef_apply, g68i_withRef_apply, ← Matrix.smul_apply,
    ← g68i_pi_smul]
  rfl

theorem g68i_purif_entropy (d delta n : ℕ) (hd : 2 ≤ d) {C : Type*} [Fintype C] [DecidableEq C]
    (M : Superop (Fin d) (Fin d)) (hM : IsChannel M)
    (R : Matrix (Word n d × Word n delta) (Word n d × Word n delta) ℂ)
    (psi : EuclideanSpace ℂ ((Word n d × Word n delta) × C))
    (hpurifies : traceRight (pureDensity psi) = R)
    (a0 : Word n d) (c0 : C) :
    entropyD d (purifiedOutput M n psi) = flagEntropy d R +
      ∑ b : Word n delta, branchWeight R b *
        entropyD d (withReference (piSuperop (fun _ : Fin n => M))
          (pureDensity (conditionalPurification a0 c0 R psi b))) := by
  set F := withReference (C := C) (piSuperop (fun _ : Fin n => M)) with hF
  have hSP : ∀ X, F Xᴴ = (F X)ᴴ :=
    g68i_withRef_SP _ (g68i_SP_pi _ (fun _ => g68i_SP_channel M hM))
  have hTP : ∀ X, (F X).trace = X.trace :=
    g68i_withRef_tp _ (g68i_tp_pi _ (fun _ => g68i_tp_channel M hM))
  have hQ : ∀ b, (F (g68i_Y psi b)).IsHermitian := by
    intro b
    unfold Matrix.IsHermitian
    rw [← hSP, (g68i_Y_herm psi b).eq]
  have hP := g68i_ent_block (Equiv.refl _) (purifiedOutput M n psi)
    (fun b => F (g68i_Y psi b)) hQ
    (fun u v => by rw [g68i_purified_apply]; rfl)
  have hσ : ∀ b, (F (pureDensity (conditionalPurification a0 c0 R psi b))).IsHermitian := by
    intro b
    unfold Matrix.IsHermitian
    rw [← hSP, (g68i_pure_herm _).eq]
  have hw0 : ∀ b, 0 ≤ branchWeight R b := by
    intro b; rw [g68i_weight_psi R psi hpurifies b]
    exact Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => Complex.normSq_nonneg _))
  have hent : ∀ b, vnEntropy (F (g68i_Y psi b)) =
      -(branchWeight R b * Real.logb 2 (branchWeight R b)) +
        branchWeight R b * vnEntropy (F (pureDensity (conditionalPurification a0 c0 R psi b))) := by
    intro b
    rw [← g68i_Y_eq R psi hpurifies a0 c0 b, hF, g68i_withRef_pi_smul, ← hF,
      g68i_ent_smul _ _ (hw0 b) (fun _ => hσ b), hTP, g68i_purif_trace R psi hpurifies a0 c0 b]
    simp
  unfold entropyD flagEntropy
  rw [hP]
  simp_rw [hent]
  rw [Finset.sum_add_distrib, add_div, Finset.sum_div, Finset.sum_div, ← Finset.sum_neg_distrib]
  congr 1
  · refine Finset.sum_congr rfl (fun b _ => ?_)
    rw [neg_div, g68i_logb_conv d hd]
  · refine Finset.sum_congr rfl (fun b _ => ?_)
    ring

end G68ILIB

/-- Giovannetti, arXiv:quant-ph/0406111v3, PDF p.4, Eq.(24) and following
sentence. Coherent information is EXACTLY a convex combination: the weights
are nonnegative and sum to one, and the Shannon terms cancel. -/
theorem solution
    (d delta n : ℕ) (hd : 2 ≤ d) (hdelta : 0 < delta) (hn : 0 < n)
    {C : Type*} [Fintype C] [DecidableEq C]
    (M : Superop (Fin d) (Fin d)) (hM : IsChannel M)
    (R : Matrix (Word n d × Word n delta) (Word n d × Word n delta) ℂ)
    (hR : IsDensityMatrix R)
    (psi : EuclideanSpace ℂ ((Word n d × Word n delta) × C))
    (hpsi : IsState psi) (hpurifies : traceRight (pureDensity psi) = R)
    (a0 : Word n d) (c0 : C) :
    (∀ b : Word n delta, 0 ≤ branchWeight R b) ∧
    (∑ b : Word n delta, branchWeight R b = 1) ∧
    entropyD d (dephasedPower M n R) - entropyD d (purifiedOutput M n psi) =
      ∑ b : Word n delta, branchWeight R b *
        (entropyD d (piSuperop (fun _ : Fin n => M) (conditionalState a0 R b)) -
          entropyD d (withReference (piSuperop (fun _ : Fin n => M))
            (pureDensity (conditionalPurification a0 c0 R psi b)))) := by
  refine ⟨fun b => g68i_weight_nonneg R hR.1 b, ?_, ?_⟩
  · have h1 : R.trace = 1 := hR.2
    have : ∑ b : Word n delta, (conditionalBlock R b).trace = R.trace := by
      simp only [Matrix.trace, Matrix.diag_apply, conditionalBlock, Fintype.sum_prod_type]
      exact Finset.sum_comm
    unfold branchWeight
    rw [← Complex.re_sum, this, h1, Complex.one_re]
  · rw [g68i_deph_entropy d delta n hd M hM R hR a0,
      g68i_purif_entropy d delta n hd M hM R psi hpurifies a0 c0]
    rw [add_sub_add_left_eq_sub, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun b _ => ?_)
    ring



end
