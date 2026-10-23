-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Claimed50.P20.erasureHolevo
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T21:47:41.574567+00:00
-- url     : https://prove2.me/submissions/a731a159-22a7-4d28-a0be-13e1e4593c33

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P20
noncomputable section

open QAlgorithms
open scoped BigOperators Matrix ComplexConjugate ComplexOrder

namespace X7Y10EH

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

lemma g68i_herm_smul {κ : Type*} [Fintype κ] (R : Matrix κ κ ℂ) (s : ℝ)
    (hR : s ≠ 0 → R.IsHermitian) : ((s : ℂ) • R).IsHermitian := by
  rcases eq_or_ne s 0 with h | h
  · subst h; simp
  · have hR' := hR h
    unfold Matrix.IsHermitian
    rw [Matrix.conjTranspose_smul, hR'.eq]
    simp

lemma g73f_cfc_trace {n : Type*} [Fintype n] [DecidableEq n] {Y : Matrix n n ℂ} (hY : Y.IsHermitian)
    (f : ℝ → ℝ) : (cfc f Y).trace = ∑ i, ((f (hY.eigenvalues i) : ℝ) : ℂ) := by
  rw [hY.cfc_eq f, Matrix.IsHermitian.cfc, Unitary.conjStarAlgAut_apply, Matrix.trace_mul_cycle,
    Unitary.star_mul_self_of_mem hY.eigenvectorUnitary.2, one_mul, Matrix.trace_diagonal]
  rfl

lemma g73f_term_le (D μ : ℝ) (hD : 0 < D) (hμ : 0 ≤ μ) :
    -(μ * Real.log μ) - μ * Real.log D ≤ 1 / D - μ := by
  rcases hμ.eq_or_lt with h | h
  · subst h; simp; positivity
  · have h1 := Real.log_le_sub_one_of_pos (show 0 < 1 / (D * μ) by positivity)
    rw [one_div, Real.log_inv, Real.log_mul hD.ne' h.ne'] at h1
    have h2 : μ * ((D * μ)⁻¹ - 1) = 1 / D - μ := by field_simp
    nlinarith [mul_le_mul_of_nonneg_left h1 h.le]

lemma g73f_ent_le_log {n : Type*} [Fintype n] (μ : n → ℝ) (hμ : ∀ i, 0 ≤ μ i)
    (hs : ∑ i, μ i = 1) (hn : 0 < Fintype.card n) :
    -∑ i, μ i * Real.logb 2 (μ i) ≤ Real.logb 2 (Fintype.card n) := by
  have hD : (0:ℝ) < Fintype.card n := by exact_mod_cast hn
  have key : ∑ i, (-(μ i * Real.log (μ i)) - μ i * Real.log (Fintype.card n)) ≤
      ∑ _i : n, (1 / (Fintype.card n : ℝ)) - ∑ i, μ i := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_le_sum fun i _ => g73f_term_le _ _ hD (hμ i)
  rw [Finset.sum_sub_distrib, ← Finset.sum_mul, hs, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul] at key
  rw [mul_one_div_cancel hD.ne'] at key
  simp only [Real.logb, ← Finset.sum_neg_distrib]
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have : ∑ i, -(μ i * (Real.log (μ i) / Real.log 2)) = (∑ i, -(μ i * Real.log (μ i))) / Real.log 2 := by
    rw [Finset.sum_div]; congr 1; ext i; ring
  rw [this, div_le_div_iff_of_pos_right hl]
  linarith

lemma g73f_diag_herm {n : Type*} [Fintype n] [DecidableEq n] (d : n → ℝ) :
    (Matrix.diagonal (fun i => (d i : ℂ))).IsHermitian := by
  rw [Matrix.IsHermitian, Matrix.diagonal_conjTranspose]
  congr 1; funext i; simp

lemma g73f_trace_cfc_diag {n : Type*} [Fintype n] [DecidableEq n] (d : n → ℝ) (f : ℝ → ℝ) :
    (cfc f (Matrix.diagonal (fun i => (d i : ℂ)))).trace = ∑ i, ((f (d i) : ℝ) : ℂ) := by
  have hD := g73f_diag_herm d
  rw [g73f_cfc_trace hD]
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

lemma g73f_vn_diag {n : Type*} [Fintype n] [DecidableEq n] (d : n → ℝ) :
    vnEntropy (Matrix.diagonal (fun i => (d i : ℂ))) = -∑ i, d i * Real.logb 2 (d i) := by
  unfold vnEntropy
  rw [g73f_trace_cfc_diag]
  simp

open QAlgorithms.Papers.Independent.Dependency50.P41 (qubitErasure)

lemma X7_density_ent_bounds (ρ : Matrix (Fin 2) (Fin 2) ℂ) (h : IsDensityMatrix ρ) :
    0 ≤ vnEntropy ρ ∧ vnEntropy ρ ≤ 1 := by
  have hH := h.1.isHermitian
  have hsum : ∑ i, hH.eigenvalues i = 1 := by
    have := hH.trace_eq_sum_eigenvalues
    rw [h.2] at this
    have h2 := congrArg Complex.re this
    simp at h2
    rw [Fin.sum_univ_two]; exact h2.symm
  have hnn : ∀ i, 0 ≤ hH.eigenvalues i := fun i => h.1.eigenvalues_nonneg i
  have hle : ∀ i, hH.eigenvalues i ≤ 1 := fun i => by
    rw [← hsum]; exact Finset.single_le_sum (fun j _ => hnn j) (Finset.mem_univ i)
  have hv : vnEntropy ρ = -∑ i, hH.eigenvalues i * Real.logb 2 (hH.eigenvalues i) := by
    unfold vnEntropy; rw [g73f_cfc_trace hH]; simp [Complex.re_sum]
  rw [hv]
  constructor
  · rw [neg_nonneg]; apply Finset.sum_nonpos; intro i _
    exact mul_nonpos_of_nonneg_of_nonpos (hnn i) (Real.logb_nonpos (by norm_num) (hnn i) (hle i))
  · calc _ ≤ Real.logb 2 (Fintype.card (Fin 2)) := g73f_ent_le_log _ hnn hsum (by simp)
      _ = 1 := by simp

lemma X7_fromBlocks_pow {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (A : Matrix m m ℂ) (D : Matrix n n ℂ) (k : ℕ) :
    (Matrix.fromBlocks A 0 0 D) ^ k = Matrix.fromBlocks (A ^ k) 0 0 (D ^ k) := by
  induction k with
  | zero => simp [Matrix.fromBlocks_one]
  | succ k ih => rw [pow_succ, ih, Matrix.fromBlocks_multiply]; simp [pow_succ]

def X7_e3 : Fin 3 ≃ Fin 2 ⊕ Fin 1 where
  toFun x := if h : x.val < 2 then Sum.inl ⟨x.val, h⟩ else Sum.inr 0
  invFun := Sum.elim (fun i => ⟨i.val, by omega⟩) (fun _ => 2)
  left_inv x := by fin_cases x <;> rfl
  right_inv y := by rcases y with y | y <;> fin_cases y <;> rfl

lemma X7_submatrix_pow {X Y : Type*} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
    (e : X ≃ Y) (M : Matrix Y Y ℂ) (k : ℕ) :
    (M.submatrix e e) ^ k = (M ^ k).submatrix e e := by
  have := map_pow (Matrix.reindexAlgEquiv ℂ ℂ e.symm) M k
  simpa [Matrix.coe_reindexAlgEquiv, Matrix.reindex_apply] using this.symm

lemma X7_trace_fromBlocks {m n : Type*} [Fintype m] [Fintype n]
    (A : Matrix m m ℂ) (B : Matrix m n ℂ) (C : Matrix n m ℂ) (D : Matrix n n ℂ) :
    (Matrix.fromBlocks A B C D).trace = A.trace + D.trace := by
  simp [Matrix.trace, Fintype.sum_sum_type]

lemma X7_trace_submatrix {X Y : Type*} [Fintype X] [Fintype Y]
    (e : X ≃ Y) (M : Matrix Y Y ℂ) : (M.submatrix e e).trace = M.trace := by
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.submatrix_apply]
  exact Equiv.sum_comp e (fun i => M i i)

lemma X7_erasure_entropy [DecidableEq (Fin 3)] (ε : ℝ) (he0 : 0 ≤ ε) (he1 : ε ≤ 1)
    (ρ : Matrix (Fin 2) (Fin 2) ℂ) (h : IsDensityMatrix ρ) :
    vnEntropy (qubitErasure ε ρ) =
      -(ε * Real.logb 2 ε) - (1 - ε) * Real.logb 2 (1 - ε) + (1 - ε) * vnEntropy ρ := by
  have hρH := h.1.isHermitian
  set A : Matrix (Fin 2) (Fin 2) ℂ := ((1 - ε : ℝ) : ℂ) • ρ with hA
  set D : Matrix (Fin 1) (Fin 1) ℂ := ((ε : ℝ) : ℂ) • 1 with hD
  set Q := Matrix.fromBlocks A 0 0 D with hQ
  have htr : ρ.trace = ρ 0 0 + ρ 1 1 := by simp [Matrix.trace, Fin.sum_univ_two]
  have h2 := h.2
  rw [htr] at h2
  have hP : qubitErasure ε ρ = Q.submatrix X7_e3 X7_e3 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [qubitErasure, QAlgorithms.Papers.Independent.Information100.P58.singleErasure, Q, A, D,
        X7_e3, Matrix.trace, Fin.sum_univ_two, h2]
  have hAH : A.IsHermitian := g68i_herm_smul ρ _ (fun _ => hρH)
  have hDH : D.IsHermitian := g68i_herm_smul _ _ (fun _ => Matrix.isHermitian_one)
  have hQH : Q.IsHermitian := Matrix.IsHermitian.fromBlocks hAH (by simp) hDH
  have hPH : (qubitErasure ε ρ).IsHermitian := by rw [hP]; exact hQH.submatrix _
  let dg : Fin 2 → ℝ := fun i => if i = 0 then ε else 0
  let Qf : Fin 2 → Matrix (Fin 2) (Fin 2) ℂ := fun j =>
    if j = 0 then A else Matrix.diagonal (fun i => ((dg i : ℝ) : ℂ))
  have hQf : ∀ j, (Qf j).IsHermitian := by
    intro j; by_cases hj : j = 0
    · simp only [Qf, hj, if_true]; exact hAH
    · simp only [Qf, hj, if_false]; exact g73f_diag_herm dg
  have hkey : (cfc (fun x : ℝ => x * Real.logb 2 x) (qubitErasure ε ρ)).trace =
      ∑ j, (cfc (fun x : ℝ => x * Real.logb 2 x) (Qf j)).trace := by
    refine g68i_trace_cfc_family _ Qf hPH hQf _ (by simp) (fun k => ?_)
    rw [hP, X7_submatrix_pow, X7_trace_submatrix, hQ, X7_fromBlocks_pow, X7_trace_fromBlocks,
      Fin.sum_univ_two]
    simp only [Qf, dg, if_true, show (1 : Fin 2) ≠ 0 from by decide, if_false]
    congr 1
    rw [Matrix.diagonal_pow, Matrix.trace_diagonal, Fin.sum_univ_two, hD, smul_pow, one_pow,
      Matrix.trace_smul, Matrix.trace_one]
    simp
  have hvn : vnEntropy (qubitErasure ε ρ) = ∑ j, vnEntropy (Qf j) := by
    unfold vnEntropy
    rw [hkey, Complex.re_sum, ← Finset.sum_neg_distrib]
  rw [hvn, Fin.sum_univ_two]
  simp only [Qf, if_true, show (1 : Fin 2) ≠ 0 from by decide, if_false]
  rw [hA, g68i_ent_smul ρ (1 - ε) (by linarith) (fun _ => hρH), g73f_vn_diag, Fin.sum_univ_two]
  simp only [dg, if_true, show (1 : Fin 2) ≠ 0 from by decide, if_false, h.2]
  simp
  ring

lemma X7_avg_density (e : QAlgorithms.Papers.Independent.Information100.P08.Ensemble (Fin 2)) :
    IsDensityMatrix (QAlgorithms.Papers.Independent.Information100.P08.ensembleAverage e) := by
  unfold QAlgorithms.Papers.Independent.Information100.P08.ensembleAverage
  simp only [← Complex.coe_smul]
  refine ⟨Matrix.posSemidef_sum _ (fun j _ => (e.density j).1.smul (by exact_mod_cast e.nonneg j)), ?_⟩
  rw [Matrix.trace_sum]
  simp only [Matrix.trace_smul, (e.density _).2, smul_eq_mul, mul_one]
  exact_mod_cast e.total

def X7_e0 : QAlgorithms.Papers.Independent.Information100.P08.Ensemble (Fin 2) where
  size := 2
  prob := fun _ => 1 / 2
  state := fun x => Matrix.diagonal (fun i => ((if i = x then 1 else 0 : ℝ) : ℂ))
  nonneg := fun _ => by norm_num
  total := by simp
  density := by
    intro x
    refine ⟨Matrix.PosSemidef.diagonal ?_, ?_⟩
    · intro i; simp only [Pi.zero_apply]; split_ifs <;> simp
    · simp [Matrix.trace_diagonal, Fin.sum_univ_two]
      fin_cases x <;> simp

theorem X7_main [DecidableEq (Fin 3)] (ε : ℝ) (he0 : 0 ≤ ε) (he1 : ε ≤ 1) :
    QAlgorithms.Papers.Independent.Information100.P08.channelHolevo (qubitErasure ε) = 1 - ε ∧
      IsGreatest {v | ∃ e : QAlgorithms.Papers.Independent.Information100.P08.Ensemble (Fin 2),
        v = QAlgorithms.Papers.Independent.Information100.P08.outputHolevo (qubitErasure ε) e}
        (1 - ε) := by
  have hG : IsGreatest {v | ∃ e : QAlgorithms.Papers.Independent.Information100.P08.Ensemble (Fin 2),
        v = QAlgorithms.Papers.Independent.Information100.P08.outputHolevo (qubitErasure ε) e}
        (1 - ε) := by
    constructor
    · refine ⟨X7_e0, ?_⟩
      unfold QAlgorithms.Papers.Independent.Information100.P08.outputHolevo
        QAlgorithms.Papers.Independent.Information100.P08.ensembleAverage
      let st : Fin 2 → Matrix (Fin 2) (Fin 2) ℂ :=
        fun x => Matrix.diagonal (fun i => ((if i = x then 1 else 0 : ℝ) : ℂ))
      have hst : ∀ x, IsDensityMatrix (st x) := fun x => X7_e0.density x
      change 1 - ε = vnEntropy (qubitErasure ε (∑ x : Fin 2, (1 / 2 : ℝ) • st x)) -
        ∑ x : Fin 2, (1 / 2 : ℝ) * vnEntropy (qubitErasure ε (st x))
      have havg : (∑ x : Fin 2, (1 / 2 : ℝ) • st x) =
          Matrix.diagonal (fun _ => ((1 / 2 : ℝ) : ℂ)) := by
        ext a b
        fin_cases a <;> fin_cases b <;>
          simp [st, Matrix.sum_apply, Fin.sum_univ_two, Matrix.diagonal_apply] <;> norm_num
      have hdavg : IsDensityMatrix (Matrix.diagonal (fun _ : Fin 2 => ((1 / 2 : ℝ) : ℂ))) := by
        rw [← havg]; exact X7_avg_density X7_e0
      rw [havg, X7_erasure_entropy ε he0 he1 _ hdavg]
      simp only [fun x => X7_erasure_entropy ε he0 he1 _ (hst x)]
      have hS1 : vnEntropy (Matrix.diagonal (fun _ : Fin 2 => ((1 / 2 : ℝ) : ℂ))) = 1 := by
        rw [g73f_vn_diag]; simp [Fin.sum_univ_two, Real.logb_inv]
      have hS0 : ∀ x, vnEntropy (st x) = 0 := by
        intro x
        simp only [st]
        rw [g73f_vn_diag]
        fin_cases x <;> simp [Fin.sum_univ_two]
      simp only [hS0, hS1, Fin.sum_univ_two]
      ring
    · rintro v ⟨e, rfl⟩
      unfold QAlgorithms.Papers.Independent.Information100.P08.outputHolevo
      have hd := X7_avg_density e
      rw [X7_erasure_entropy ε he0 he1 _ hd]
      simp only [fun x => X7_erasure_entropy ε he0 he1 _ (e.density x)]
      have hb := X7_density_ent_bounds _ hd
      have hnn : 0 ≤ ∑ x, e.prob x * vnEntropy (e.state x) :=
        Finset.sum_nonneg fun x _ => mul_nonneg (e.nonneg x) (X7_density_ent_bounds _ (e.density x)).1
      have hexp : ∑ x, e.prob x * (-(ε * Real.logb 2 ε) - (1 - ε) * Real.logb 2 (1 - ε) +
          (1 - ε) * vnEntropy (e.state x)) =
          (-(ε * Real.logb 2 ε) - (1 - ε) * Real.logb 2 (1 - ε)) +
            (1 - ε) * ∑ x, e.prob x * vnEntropy (e.state x) := by
        rw [Finset.mul_sum]
        have : ∑ x, e.prob x * (-(ε * Real.logb 2 ε) - (1 - ε) * Real.logb 2 (1 - ε) +
            (1 - ε) * vnEntropy (e.state x)) =
            ∑ x, (e.prob x * (-(ε * Real.logb 2 ε) - (1 - ε) * Real.logb 2 (1 - ε)) +
              (1 - ε) * (e.prob x * vnEntropy (e.state x))) := by
          refine Finset.sum_congr rfl fun x _ => by ring
        rw [this, Finset.sum_add_distrib, ← Finset.sum_mul, e.total, one_mul]
      rw [hexp]
      have h1e : 0 ≤ 1 - ε := by linarith
      nlinarith [mul_nonneg h1e hnn, mul_le_mul_of_nonneg_left hb.2 h1e]
  exact ⟨hG.csSup_eq, hG⟩

end X7Y10EH

open scoped BigOperators Matrix ComplexConjugate ComplexOrder

open Filter

open QAlgorithms.Papers.Independent.Information100.P08 (Ensemble PureEnsemble channelHolevo)

open QAlgorithms.Papers.Independent.Information100.P62 (tensorChannel)

open QAlgorithms.Papers.Independent.Dependency50.P23 (IsHadamard)

open QAlgorithms.Papers.Independent.Dependency50.P41 (qubitErasure)

open QAlgorithms.Papers.Independent.Information100.P27 (qubitDephasing)

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Claimed50.P20 in
theorem solution (epsilon : ℝ) (he0 : 0 ≤ epsilon) (he1 : epsilon ≤ 1) :
    channelHolevo (qubitErasure epsilon) = 1 - epsilon ∧
      IsGreatest {v | ∃ e : Ensemble (Fin 2),
        v = QAlgorithms.Papers.Independent.Information100.P08.outputHolevo (qubitErasure epsilon) e}
        (1 - epsilon) :=
  X7Y10EH.X7_main epsilon he0 he1

end
