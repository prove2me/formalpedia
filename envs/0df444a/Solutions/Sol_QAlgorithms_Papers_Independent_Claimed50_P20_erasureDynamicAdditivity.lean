-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Claimed50.P20.erasureDynamicAdditivity
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T23:44:42.640577+00:00
-- url     : https://prove2.me/submissions/6e00768d-ad05-4eea-a060-c9f39773d1d7

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P20
import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P41
import Definitions.Def_QAlgorithms_Defs_QuantumInformation
import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P42
import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P33

-- ===== EDX =====
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

open QAlgorithms.Papers.Independent.Information100.P62 (tensorChannel)

lemma X7_trace_cfc_two {X Y Z : Type*} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
    [Fintype Z] [DecidableEq Z]
    (P : Matrix X X ℂ) (A : Matrix Y Y ℂ) (D : Matrix Z Z ℂ)
    (hP : P.IsHermitian) (hA : A.IsHermitian) (hD : D.IsHermitian) (f : ℝ → ℝ) (hf : f 0 = 0)
    (htr : ∀ k : ℕ, (P ^ (k + 1)).trace = (A ^ (k + 1)).trace + (D ^ (k + 1)).trace) :
    (cfc f P).trace = (cfc f A).trace + (cfc f D).trace := by
  classical
  set S : Finset ℝ := P.finite_real_spectrum.toFinset ∪ A.finite_real_spectrum.toFinset ∪
    D.finite_real_spectrum.toFinset ∪ {0} with hS
  set p : Polynomial ℝ := Lagrange.interpolate S id f with hp
  have hev : ∀ x ∈ S, p.eval x = f x := fun x hx =>
    Lagrange.eval_interpolate_at_node (s := S) (v := id) f (Set.injOn_id _) hx
  have hPe : cfc f P = Polynomial.aeval P p := by
    rw [← cfc_polynomial p P hP.isSelfAdjoint]
    apply cfc_congr; intro x hx; exact (hev x (by simp [hS, hx])).symm
  have hAe : cfc f A = Polynomial.aeval A p := by
    rw [← cfc_polynomial p A hA.isSelfAdjoint]
    apply cfc_congr; intro x hx; exact (hev x (by simp [hS, hx])).symm
  have hDe : cfc f D = Polynomial.aeval D p := by
    rw [← cfc_polynomial p D hD.isSelfAdjoint]
    apply cfc_congr; intro x hx; exact (hev x (by simp [hS, hx])).symm
  have h0 : p.coeff 0 = 0 := by
    rw [Polynomial.coeff_zero_eq_eval_zero, hev 0 (by simp [hS]), hf]
  rw [hPe, hAe, hDe]
  simp_rw [Polynomial.aeval_eq_sum_range' (Nat.lt_succ_self p.natDegree)]
  simp_rw [Matrix.trace_sum, Matrix.trace_smul]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rcases i with _ | k
  · simp [h0]
  · rw [htr k, smul_add]

lemma X7_ent_fromBlocks {Y Z : Type*} [Fintype Y] [DecidableEq Y] [Fintype Z] [DecidableEq Z]
    (A : Matrix Y Y ℂ) (D : Matrix Z Z ℂ) (hA : A.IsHermitian) (hD : D.IsHermitian) :
    vnEntropy (Matrix.fromBlocks A 0 0 D) = vnEntropy A + vnEntropy D := by
  unfold vnEntropy
  rw [X7_trace_cfc_two _ A D (Matrix.IsHermitian.fromBlocks hA (by simp) hD) hA hD _ (by simp)
    (fun k => by rw [X7_fromBlocks_pow, X7_trace_fromBlocks])]
  simp only [Complex.add_re]; ring

lemma X7_ent_submatrix {X Y : Type*} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
    (e : X ≃ Y) (M : Matrix Y Y ℂ) (hM : M.IsHermitian) :
    vnEntropy (M.submatrix e e) = vnEntropy M := by
  have := X7_trace_cfc_two (M.submatrix e e) M (0 : Matrix Empty Empty ℂ) (hM.submatrix _) hM
    Matrix.isHermitian_zero (fun x => x * Real.logb 2 x) (by simp)
    (fun k => by rw [X7_submatrix_pow, X7_trace_submatrix]; simp [Matrix.trace])
  unfold vnEntropy; rw [this]; simp [Matrix.trace]

lemma X7_trR (A B : Type*) [Fintype A] [Fintype B] (M : Matrix (A × B) (A × B) ℂ) :
    (QAlgorithms.traceRight M).trace = M.trace := by
  simp only [Matrix.trace, QAlgorithms.traceRight, Matrix.diag, Matrix.of_apply, Fintype.sum_prod_type]

lemma X7_trL (A B : Type*) [Fintype A] [Fintype B] (M : Matrix (A × B) (A × B) ℂ) :
    (QAlgorithms.traceLeft M).trace = M.trace := by
  simp only [Matrix.trace, QAlgorithms.traceLeft, Matrix.diag, Matrix.of_apply, Fintype.sum_prod_type]
  exact Finset.sum_comm

lemma X7_trR_psd {A B : Type*} [Fintype A] [Fintype B] (M : Matrix (A × B) (A × B) ℂ)
    (hM : M.PosSemidef) : (QAlgorithms.traceRight M).PosSemidef := by
  have : QAlgorithms.traceRight M = ∑ b, M.submatrix (fun a => (a, b)) (fun a => (a, b)) := by
    ext a a'; simp [QAlgorithms.traceRight, Matrix.sum_apply]
  rw [this]
  exact Matrix.posSemidef_sum _ fun a _ => hM.submatrix _

lemma X7_trL_psd {A B : Type*} [Fintype A] [Fintype B] (M : Matrix (A × B) (A × B) ℂ)
    (hM : M.PosSemidef) : (QAlgorithms.traceLeft M).PosSemidef := by
  have : QAlgorithms.traceLeft M = ∑ a, M.submatrix (fun b => (a, b)) (fun b => (a, b)) := by
    ext b b'; simp [QAlgorithms.traceLeft, Matrix.sum_apply]
  rw [this]
  exact Matrix.posSemidef_sum _ fun a _ => hM.submatrix _

lemma X7_trR_dens {A B : Type*} [Fintype A] [Fintype B] (M : Matrix (A × B) (A × B) ℂ)
    (hM : IsDensityMatrix M) : IsDensityMatrix (QAlgorithms.traceRight M) :=
  ⟨X7_trR_psd M hM.1, by rw [X7_trR]; exact hM.2⟩

lemma X7_trL_dens {A B : Type*} [Fintype A] [Fintype B] (M : Matrix (A × B) (A × B) ℂ)
    (hM : IsDensityMatrix M) : IsDensityMatrix (QAlgorithms.traceLeft M) :=
  ⟨X7_trL_psd M hM.1, by rw [X7_trL]; exact hM.2⟩

lemma X7_N_block (ε : ℝ) (ρ : Matrix (Fin 2) (Fin 2) ℂ) (h2 : ρ.trace = 1) :
    qubitErasure ε ρ =
      (Matrix.fromBlocks (((1 - ε : ℝ) : ℂ) • ρ) 0 0 (((ε : ℝ) : ℂ) • (1 : Matrix (Fin 1) (Fin 1) ℂ))).submatrix
        X7_e3 X7_e3 := by
  have htr : ρ.trace = ρ 0 0 + ρ 1 1 := by simp [Matrix.trace, Fin.sum_univ_two]
  rw [htr] at h2
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [qubitErasure, QAlgorithms.Papers.Independent.Information100.P58.singleErasure,
      X7_e3, Matrix.trace, Fin.sum_univ_two, h2]

lemma X7_N_herm_tr (ε : ℝ) (ρ : Matrix (Fin 2) (Fin 2) ℂ) (h : IsDensityMatrix ρ) :
    (qubitErasure ε ρ).IsHermitian ∧ (qubitErasure ε ρ).trace = 1 := by
  rw [X7_N_block ε ρ h.2]
  refine ⟨(Matrix.IsHermitian.fromBlocks (g68i_herm_smul ρ _ (fun _ => h.1.isHermitian)) (by simp)
    (g68i_herm_smul _ _ (fun _ => Matrix.isHermitian_one))).submatrix _, ?_⟩
  rw [X7_trace_submatrix, X7_trace_fromBlocks, Matrix.trace_smul, Matrix.trace_smul, h.2]
  simp

def X7_eR (R : Type*) : R × Fin 3 ≃ (R × Fin 2) ⊕ R :=
  ((Equiv.prodCongr (Equiv.refl R) X7_e3).trans (Equiv.prodSumDistrib R (Fin 2) (Fin 1))).trans
    (Equiv.sumCongr (Equiv.refl _) (Equiv.prodUnique R (Fin 1)))

lemma X7_idT_block {R : Type*} [Fintype R] (ε : ℝ) (σ : Matrix (R × Fin 2) (R × Fin 2) ℂ) :
    idTensorSuperop (R := R) (qubitErasure ε) σ =
      (Matrix.fromBlocks (((1 - ε : ℝ) : ℂ) • σ) 0 0
        (((ε : ℝ) : ℂ) • QAlgorithms.traceRight σ)).submatrix (X7_eR R) (X7_eR R) := by
  ext ⟨p, x⟩ ⟨q, y⟩
  fin_cases x <;> fin_cases y <;>
    simp [idTensorSuperop, qubitErasure, QAlgorithms.Papers.Independent.Information100.P58.singleErasure,
      X7_eR, X7_e3, QAlgorithms.traceRight, Matrix.trace, Fin.sum_univ_two] <;> ring

lemma X7_idT_entropy {R : Type*} [Fintype R] [DecidableEq R] [DecidableEq (R × Fin 3)]
    (ε : ℝ) (he0 : 0 ≤ ε) (he1 : ε ≤ 1)
    (σ : Matrix (R × Fin 2) (R × Fin 2) ℂ) (hσ : IsDensityMatrix σ) :
    vnEntropy (idTensorSuperop (R := R) (qubitErasure ε) σ) =
      -(ε * Real.logb 2 ε) - (1 - ε) * Real.logb 2 (1 - ε) + (1 - ε) * vnEntropy σ +
        ε * vnEntropy (QAlgorithms.traceRight σ) := by
  have hσH := hσ.1.isHermitian
  have hRH := (X7_trR_psd σ hσ.1).isHermitian
  have h1 := g68i_herm_smul σ (1 - ε) (fun _ => hσH)
  have h2 := g68i_herm_smul _ ε (fun _ => hRH)
  rw [X7_idT_block, X7_ent_submatrix _ _ (Matrix.IsHermitian.fromBlocks h1 (by simp) h2),
    X7_ent_fromBlocks _ _ h1 h2, g68i_ent_smul σ (1 - ε) (by linarith) (fun _ => hσH),
    g68i_ent_smul _ ε he0 (fun _ => hRH), X7_trR, hσ.2]
  simp
  ring

lemma X7_idT_herm_tr {R : Type*} [Fintype R] (ε : ℝ)
    (σ : Matrix (R × Fin 2) (R × Fin 2) ℂ) (hσ : IsDensityMatrix σ) :
    (idTensorSuperop (R := R) (qubitErasure ε) σ).IsHermitian ∧
      (idTensorSuperop (R := R) (qubitErasure ε) σ).trace = 1 := by
  classical
  rw [X7_idT_block]
  refine ⟨(Matrix.IsHermitian.fromBlocks (g68i_herm_smul σ _ (fun _ => hσ.1.isHermitian)) (by simp)
    (g68i_herm_smul _ _ (fun _ => (X7_trR_psd σ hσ.1).isHermitian))).submatrix _, ?_⟩
  rw [X7_trace_submatrix, X7_trace_fromBlocks, Matrix.trace_smul, Matrix.trace_smul, X7_trR, hσ.2]
  simp

def X7_e2 : Fin 3 × Fin 3 ≃ (Fin 2 × Fin 3) ⊕ Fin 3 :=
  ((Equiv.prodCongr X7_e3 (Equiv.refl (Fin 3))).trans (Equiv.sumProdDistrib (Fin 2) (Fin 1) (Fin 3))).trans
    (Equiv.sumCongr (Equiv.refl _) (Equiv.uniqueProd (Fin 3) (Fin 1)))

lemma X7_N_add (ε : ℝ) (X Y : Matrix (Fin 2) (Fin 2) ℂ) :
    qubitErasure ε (X + Y) = qubitErasure ε X + qubitErasure ε Y := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [qubitErasure, QAlgorithms.Papers.Independent.Information100.P58.singleErasure,
      Matrix.trace_add] <;> ring

lemma X7_N_lin (ε : ℝ) (X : Matrix (Fin 2) (Fin 2) ℂ) (x y : Fin 3) :
    qubitErasure ε X x y = ∑ k, ∑ l, X k l * qubitErasure ε (Matrix.single k l 1) x y := by
  fin_cases x <;> fin_cases y <;>
    simp [qubitErasure, QAlgorithms.Papers.Independent.Information100.P58.singleErasure,
      Fin.sum_univ_two, Matrix.single_apply, Matrix.trace] <;> ring

set_option maxHeartbeats 4000000 in
lemma X7_N_single (ε : ℝ) (i j : Fin 2) (x y : Fin 3) :
    qubitErasure ε (Matrix.single i j 1) x y =
      if x.val < 2 ∧ y.val < 2 then (if i.val = x.val ∧ j.val = y.val then ((1 - ε : ℝ) : ℂ) else 0)
      else if x.val = 2 ∧ y.val = 2 then (if i = j then ((ε : ℝ) : ℂ) else 0) else 0 := by
  fin_cases i <;> fin_cases j <;> fin_cases x <;> fin_cases y <;>
    simp [qubitErasure, QAlgorithms.Papers.Independent.Information100.P58.singleErasure,
      Matrix.single_apply, Matrix.trace, Fin.sum_univ_two]

lemma X7_T_entry (ε : ℝ) (ρ : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) (a b a' b' : Fin 3) :
    tensorChannel (qubitErasure ε) (qubitErasure ε) ρ (a, b) (a', b') =
      ∑ i, ∑ j, qubitErasure ε (Matrix.single i j 1) a a' *
        qubitErasure ε (Matrix.of fun k l => ρ (i, k) (j, l)) b b' := by
  simp only [tensorChannel]
  simp_rw [X7_N_lin ε (Matrix.of fun k l => ρ (_, k) (_, l)) b b', Matrix.of_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
    Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => by ring

lemma X7_trL_split (ρ : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) :
    QAlgorithms.traceLeft ρ = Matrix.of (fun k l => ρ (0, k) (0, l)) + Matrix.of (fun k l => ρ (1, k) (1, l)) := by
  ext k l; simp [QAlgorithms.traceLeft, Fin.sum_univ_two]

lemma X7_T_block (ε : ℝ) (ρ : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) :
    tensorChannel (qubitErasure ε) (qubitErasure ε) ρ =
      (Matrix.fromBlocks (((1 - ε : ℝ) : ℂ) • idTensorSuperop (R := Fin 2) (qubitErasure ε) ρ) 0 0
        (((ε : ℝ) : ℂ) • qubitErasure ε (QAlgorithms.traceLeft ρ))).submatrix X7_e2 X7_e2 := by
  ext ⟨a, b⟩ ⟨a', b'⟩
  rw [X7_T_entry, X7_trL_split, X7_N_add]
  fin_cases a <;> fin_cases a' <;>
    simp [X7_N_single, X7_e2, X7_e3, idTensorSuperop, Fin.sum_univ_two]

lemma X7_T_entropy [DecidableEq (Fin 3 × Fin 3)] (ε : ℝ) (he0 : 0 ≤ ε) (he1 : ε ≤ 1)
    (ρ : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) (h : IsDensityMatrix ρ) :
    vnEntropy (tensorChannel (qubitErasure ε) (qubitErasure ε) ρ) =
      2 * (-(ε * Real.logb 2 ε) - (1 - ε) * Real.logb 2 (1 - ε)) + (1 - ε) ^ 2 * vnEntropy ρ +
        ε * (1 - ε) * (vnEntropy (QAlgorithms.traceRight ρ) + vnEntropy (QAlgorithms.traceLeft ρ)) := by
  obtain ⟨hXH, hXt⟩ := X7_idT_herm_tr (R := Fin 2) ε ρ h
  obtain ⟨hYH, hYt⟩ := X7_N_herm_tr ε _ (X7_trL_dens ρ h)
  have h1 := g68i_herm_smul _ (1 - ε) (fun _ => hXH)
  have h2 := g68i_herm_smul _ ε (fun _ => hYH)
  rw [X7_T_block, X7_ent_submatrix _ _ (Matrix.IsHermitian.fromBlocks h1 (by simp) h2),
    X7_ent_fromBlocks _ _ h1 h2, g68i_ent_smul _ (1 - ε) (by linarith) (fun _ => hXH),
    g68i_ent_smul _ ε he0 (fun _ => hYH), hXt, hYt, X7_idT_entropy ε he0 he1 ρ h,
    X7_erasure_entropy ε he0 he1 _ (X7_trL_dens ρ h)]
  simp
  ring


end X7Y10EH

end


-- ===== KFA =====

/-! Generic: two families with equal Gram data are related by a unitary matrix. -/

noncomputable section

namespace X4KF
open scoped Matrix ComplexConjugate InnerProductSpace

variable {P : Type*} [Fintype P]

/-- equal Gram data ⇒ a linear isometry of the whole space sends `β` to `α`. -/
lemma gram_iso {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
    (α β : P → V) (h : ∀ p q, ⟪β p, β q⟫_ℂ = ⟪α p, α q⟫_ℂ) :
    ∃ T : V →ₗᵢ[ℂ] V, ∀ p, T (β p) = α p := by
  classical
  let F : (P → ℂ) →ₗ[ℂ] V := Fintype.linearCombination ℂ β
  let G : (P → ℂ) →ₗ[ℂ] V := Fintype.linearCombination ℂ α
  have hinner : ∀ c c' : P → ℂ, ⟪F c, F c'⟫_ℂ = ⟪G c, G c'⟫_ℂ := by
    intro c c'
    simp only [F, G, Fintype.linearCombination_apply, sum_inner, inner_sum, inner_smul_left,
      inner_smul_right, h]
  have hnorm : ∀ c, ‖G c‖ = ‖F c‖ := by
    intro c
    have h1 := hinner c c
    rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at h1
    have h2 : ‖F c‖ ^ 2 = ‖G c‖ ^ 2 := by exact_mod_cast h1
    nlinarith [norm_nonneg (F c), norm_nonneg (G c), sq_nonneg (‖F c‖ - ‖G c‖),
      sq_nonneg (‖F c‖ + ‖G c‖)]
  have hker : LinearMap.ker F ≤ LinearMap.ker G := by
    intro c hc
    rw [LinearMap.mem_ker] at hc ⊢
    rw [← norm_eq_zero, hnorm, hc, norm_zero]
  let L0 : LinearMap.range F →ₗ[ℂ] V :=
    ((LinearMap.ker F).liftQ G hker).comp F.quotKerEquivRange.symm.toLinearMap
  have hL0 : ∀ c, L0 ⟨F c, LinearMap.mem_range_self F c⟩ = G c := by
    intro c
    simp only [L0, LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe]
    have : F.quotKerEquivRange.symm ⟨F c, LinearMap.mem_range_self F c⟩ =
        (LinearMap.ker F).mkQ c := by
      rw [LinearEquiv.symm_apply_eq]
      rfl
    rw [this]
    rfl
  let L : LinearMap.range F →ₗᵢ[ℂ] V :=
    { toLinearMap := L0
      norm_map' := by
        rintro ⟨x, c, rfl⟩
        change ‖L0 ⟨F c, LinearMap.mem_range_self F c⟩‖ = ‖F c‖
        rw [hL0, hnorm] }
  refine ⟨L.extend, fun p => ?_⟩
  have hb : β p = F (Pi.single p 1) := by
    simp [F, Fintype.linearCombination_apply_single]
  have ha : α p = G (Pi.single p 1) := by
    simp [G, Fintype.linearCombination_apply_single]
  have := LinearIsometry.extend_apply L ⟨F (Pi.single p 1), LinearMap.mem_range_self F _⟩
  rw [hb, ha]
  change L.extend ((⟨F (Pi.single p 1), LinearMap.mem_range_self F _⟩ : LinearMap.range F) : V) = _
  rw [this]
  exact hL0 _

/-- matrix form on `EuclideanSpace ℂ (Fin L)`: equal Gram data ⇒ `α p = U β p` for a unitary `U`. -/
lemma gram_unitary {L : ℕ} [DecidableEq (Fin L)] (α β : P → Fin L → ℂ)
    (h : ∀ p q, ∑ l, conj (β p l) * β q l = ∑ l, conj (α p l) * α q l) :
    ∃ U : Matrix.unitaryGroup (Fin L) ℂ, ∀ p k,
      α p k = ∑ l, (U : Matrix (Fin L) (Fin L) ℂ) k l * β p l := by
  have hin : ∀ x y : Fin L → ℂ, ⟪(WithLp.toLp 2 x : EuclideanSpace ℂ (Fin L)), WithLp.toLp 2 y⟫_ℂ =
      ∑ l, conj (x l) * y l := by
    intro x y
    simp [PiLp.inner_apply, RCLike.inner_apply, mul_comm]
  obtain ⟨T, hT⟩ := gram_iso (V := EuclideanSpace ℂ (Fin L)) (fun p => WithLp.toLp 2 (α p))
    (fun p => WithLp.toLp 2 (β p)) (by
      intro p q
      rw [hin, hin, h])
  let U : Matrix (Fin L) (Fin L) ℂ := fun k l => T (EuclideanSpace.single l 1) k
  have hcol : ∀ l l', ∑ k, conj (U k l) * U k l' = if l = l' then 1 else 0 := by
    intro l l'
    have := T.inner_map_map (EuclideanSpace.single l (1 : ℂ)) (EuclideanSpace.single l' 1)
    have e1 := hin (T (EuclideanSpace.single l (1 : ℂ))).ofLp (T (EuclideanSpace.single l' (1 : ℂ))).ofLp
    simp only [WithLp.toLp_ofLp] at e1
    rw [e1] at this
    simp only [U]
    rw [this, EuclideanSpace.inner_single_left]
    simp [PiLp.single_apply]
  have hU : star U * U = 1 := by
    ext l l'
    simp only [Matrix.mul_apply, Matrix.star_apply, RCLike.star_def, Matrix.one_apply]
    exact hcol l l'
  refine ⟨⟨U, Matrix.mem_unitaryGroup_iff'.mpr hU⟩, fun p k => ?_⟩
  have hx : (WithLp.toLp 2 (β p) : EuclideanSpace ℂ (Fin L)) =
      ∑ l, β p l • EuclideanSpace.single l (1 : ℂ) := by
    ext i
    simp [Pi.single_apply]
  have := congrArg (fun v : EuclideanSpace ℂ (Fin L) => v k) (hT p)
  simp only at this
  rw [← this, hx, map_sum]
  simp only [map_smul, WithLp.ofLp_sum, WithLp.ofLp_smul, Finset.sum_apply, Pi.smul_apply,
    smul_eq_mul, U]
  exact Finset.sum_congr rfl fun l _ => mul_comm _ _

end X4KF

end

-- ===== KFD =====

noncomputable section

open QAlgorithms QAlgorithms.Papers.Independent.Support50.P41
open QAlgorithms.Papers.Independent.Gap20.P06 (dilationChannel)
open scoped Matrix ComplexConjugate ComplexOrder ENNReal

attribute [local instance] Classical.propDecidable Classical.decEq
local instance (priority := 2000) instKFD (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _

namespace X4KF
open Matrix

variable {d e : ℕ}

/-- `e_i ⊗ η` -/
def wv (eta : EuclideanSpace ℂ (Fin e)) (i : Fin d) : Fin d × Fin e → ℂ :=
  fun p => (if p.1 = i then 1 else 0) * eta p.2

/-- `U (e_i ⊗ η)` -/
def uv (U : Matrix (Fin d × Fin e) (Fin d × Fin e) ℂ) (eta : EuclideanSpace ℂ (Fin e)) (i : Fin d) :
    Fin d × Fin e → ℂ := U *ᵥ wv eta i

lemma prod_eq (v : EuclideanSpace ℂ (Fin d)) (eta : EuclideanSpace ℂ (Fin e)) :
    (fun p : Fin d × Fin e => v p.1 * eta p.2) = ∑ i, v i • wv eta i := by
  ext p
  simp only [wv, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [Finset.sum_eq_single p.1 (fun b _ hb => by simp [Ne.symm hb]) (by simp)]
  simp

lemma act_prod (U : Matrix (Fin d × Fin e) (Fin d × Fin e) ℂ) (v : EuclideanSpace ℂ (Fin d))
    (eta : EuclideanSpace ℂ (Fin e)) (p : Fin d × Fin e) :
    act U (WithLp.toLp 2 fun p => v p.1 * eta p.2) p = ∑ i, v i * uv U eta i p := by
  simp only [act]
  change (U *ᵥ fun p : Fin d × Fin e => v p.1 * eta p.2) p = _
  rw [prod_eq, Matrix.mulVec_sum]
  simp [uv, Matrix.mulVec_smul]

lemma kron_eq (eta : EuclideanSpace ℂ (Fin e)) (i j : Fin d) :
    Matrix.kronecker (Matrix.single i j (1 : ℂ)) (pureDensity eta) =
      vecMulVec (wv eta i) (star (wv eta j)) := by
  ext ⟨a, f⟩ ⟨b, g⟩
  simp only [Matrix.kronecker, Matrix.kroneckerMap_apply, Matrix.single_apply, pureDensity,
    Matrix.of_apply, vecMulVec_apply, wv, Pi.star_apply, RCLike.star_def]
  by_cases ha : a = i <;> by_cases hb : b = j
  · subst ha; subst hb; simp
  · simp [ha, hb, Ne.symm hb]
  · simp [ha, Ne.symm ha]
  · simp [ha, Ne.symm ha]

lemma chan_entry (U : Matrix.unitaryGroup (Fin d × Fin e) ℂ) (eta : EuclideanSpace ℂ (Fin e))
    (i j a b : Fin d) :
    dilationChannel U eta (Matrix.single i j 1) a b =
      ∑ f, conj (uv U eta j (b, f)) * uv U eta i (a, f) := by
  simp only [dilationChannel, conjSuperop, traceRight, Matrix.of_apply]
  rw [kron_eq, Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, ← Matrix.star_mulVec]
  refine Finset.sum_congr rfl fun f _ => ?_
  simp only [vecMulVec_apply, Pi.star_apply, RCLike.star_def, uv]
  ring

lemma kron_mulVec (W : Matrix (Fin e) (Fin e) ℂ) (x : Fin d × Fin e → ℂ) (a : Fin d) (f : Fin e) :
    (Matrix.kronecker (1 : Matrix (Fin d) (Fin d) ℂ) W *ᵥ x) (a, f) = ∑ g, W f g * x (a, g) := by
  simp only [Matrix.mulVec, dotProduct, Fintype.sum_prod_type, Matrix.kronecker,
    Matrix.kroneckerMap_apply, Matrix.one_apply]
  rw [Finset.sum_eq_single a (fun b _ hb => by simp [Ne.symm hb]) (by simp)]
  simp

theorem env_freedom [NeZero d] [NeZero e]
    (U V : Matrix.unitaryGroup (Fin d × Fin e) ℂ)
    (eta zeta : EuclideanSpace ℂ (Fin e))
    (hsame : ∀ X, dilationChannel U eta X = dilationChannel V zeta X) :
    ∃ W : Matrix.unitaryGroup (Fin e) ℂ,
      ∀ v : EuclideanSpace ℂ (Fin d),
        act (V : Matrix (Fin d × Fin e) (Fin d × Fin e) ℂ)
          (WithLp.toLp 2 fun p => v p.1 * zeta p.2) =
        act (Matrix.kronecker (1 : Matrix (Fin d) (Fin d) ℂ)
          (W : Matrix (Fin e) (Fin e) ℂ))
          (act (U : Matrix (Fin d × Fin e) (Fin d × Fin e) ℂ)
            (WithLp.toLp 2 fun p => v p.1 * eta p.2)) := by
  obtain ⟨W, hW⟩ := gram_unitary (L := e) (P := Fin d × Fin d)
    (fun p f => uv V zeta p.1 (p.2, f)) (fun p f => uv U eta p.1 (p.2, f)) (by
      rintro ⟨j, b⟩ ⟨i, a⟩
      simp only
      rw [← chan_entry, ← chan_entry, hsame])
  refine ⟨W, fun v => ?_⟩
  ext ⟨a, f⟩
  rw [act_prod]
  simp only [act]
  rw [kron_mulVec]
  have : ∀ g, (act (U : Matrix (Fin d × Fin e) (Fin d × Fin e) ℂ)
      (WithLp.toLp 2 fun p => v p.1 * eta p.2)).ofLp (a, g) = ∑ i, v i * uv U eta i (a, g) :=
    fun g => act_prod _ v eta (a, g)
  simp only [act] at this
  simp only [this]
  have hW' : ∀ i, uv V zeta i (a, f) = ∑ g, (W : Matrix (Fin e) (Fin e) ℂ) f g * uv U eta i (a, g) :=
    fun i => hW (i, a) f
  simp only [hW', Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun g _ => Finset.sum_congr rfl fun i _ => ?_
  ring

end X4KF

end

-- ===== KFF =====

noncomputable section

open QAlgorithms QAlgorithms.Papers.Independent.Support50.P41
open QAlgorithms.Papers.Independent.Dependency50.P45 (entropyExchange)
open QAlgorithms.Papers.Independent.Information100.P08 (canonicalPurification)
open QAlgorithms.Papers.Independent.Information100.P50 (complementaryMap)
open scoped Matrix ComplexConjugate ComplexOrder ENNReal

attribute [local instance] Classical.propDecidable Classical.decEq
local instance (priority := 2000) instKFF (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _

namespace X4KF
open Matrix Polynomial

-- entropy swap S(VVᴴ) = S((VᴴV)ᵀ), copied from Solutions/X4/TRC.lean
theorem x4_tr_aeval {ι : Type} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℂ) (p : ℝ[X]) :
    (aeval M p).trace = ∑ i ∈ Finset.range (p.natDegree + 1), (p.coeff i : ℂ) * (M ^ i).trace := by
  rw [aeval_eq_sum_range, Matrix.trace_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.trace_smul]
  simp [Complex.real_smul]

theorem x4_tr_cfc_eq {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (M1 : Matrix ι ι ℂ) (M2 : Matrix κ κ ℂ) (h1 : M1.IsHermitian) (h2 : M2.IsHermitian)
    (h : ∀ k : ℕ, 1 ≤ k → (M1 ^ k).trace = (M2 ^ k).trace) (f : ℝ → ℝ) (hf : f 0 = 0) :
    (cfc f M1).trace = (cfc f M2).trace := by
  classical
  let S : Finset ℝ := Finset.univ.image h1.eigenvalues ∪ Finset.univ.image h2.eigenvalues ∪ {0}
  let p : ℝ[X] := Lagrange.interpolate S id f
  have hp : ∀ x ∈ S, p.eval x = f x := fun x hx =>
    Lagrange.eval_interpolate_at_node (v := id) (r := f) (Set.injOn_id _) hx
  have e1 : cfc f M1 = cfc (fun x => p.eval x) M1 := by
    apply cfc_congr
    intro x hx
    rw [h1.spectrum_real_eq_range_eigenvalues] at hx
    obtain ⟨i, rfl⟩ := hx
    exact (hp _ (by simp [S])).symm
  have e2 : cfc f M2 = cfc (fun x => p.eval x) M2 := by
    apply cfc_congr
    intro x hx
    rw [h2.spectrum_real_eq_range_eigenvalues] at hx
    obtain ⟨i, rfl⟩ := hx
    exact (hp _ (by simp [S])).symm
  have h0 : p.coeff 0 = 0 := by
    rw [coeff_zero_eq_eval_zero, hp 0 (by simp [S]), hf]
  rw [e1, e2, cfc_polynomial p M1, cfc_polynomial p M2, x4_tr_aeval, x4_tr_aeval]
  refine Finset.sum_congr rfl fun i _ => ?_
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · simp [h0]
  · rw [h i hi]

theorem x4_pow_mul {ι κ : Type} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (V : Matrix ι κ ℂ) (W : Matrix κ ι ℂ) (k : ℕ) :
    (V * W) ^ (k + 1) = V * (W * V) ^ k * W := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, ih, pow_succ]
    simp only [Matrix.mul_assoc]

theorem x4_tr_pow_swap {ι κ : Type} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (V : Matrix ι κ ℂ) (W : Matrix κ ι ℂ) (k : ℕ) (hk : 1 ≤ k) :
    ((V * W) ^ k).trace = ((W * V) ^ k).trace := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le' hk
  rw [x4_pow_mul, Matrix.mul_assoc, Matrix.trace_mul_comm, Matrix.mul_assoc, ← pow_succ]

/-- tr f(V Vᴴ) = tr f((Vᴴ V)ᵀ) when f 0 = 0. -/
theorem x4_ent_swap {ι κ : Type} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (V : Matrix ι κ ℂ) :
    QAlgorithms.vnEntropy (V * Vᴴ) = QAlgorithms.vnEntropy ((Vᴴ * V)ᵀ) := by
  unfold QAlgorithms.vnEntropy
  rw [x4_tr_cfc_eq (V * Vᴴ) ((Vᴴ * V)ᵀ) (isHermitian_mul_conjTranspose_self V)
    (isHermitian_conjTranspose_mul_self V).transpose _ _ (by simp)]
  intro k hk
  rw [← Matrix.transpose_pow, Matrix.trace_transpose, x4_tr_pow_swap _ _ k hk]

variable {d m : ℕ}

/-- the coefficient matrix `V_{(r,y),k} = ((1 ⊗ A_k) ψ)(r,y)` -/
def Vm {R : Type} [Fintype R] (A : Fin m → Matrix (Fin d) (Fin d) ℂ)
    (psi : EuclideanSpace ℂ (R × Fin d)) : Matrix (R × Fin d) (Fin m) ℂ :=
  fun p k => ∑ i, A k p.2 i * psi (p.1, i)

lemma idT_eq {R : Type} [Fintype R] (A : Fin m → Matrix (Fin d) (Fin d) ℂ)
    (psi : EuclideanSpace ℂ (R × Fin d)) :
    idTensorSuperop (R := R) (krausApply A) (pureDensity psi) = Vm A psi * (Vm A psi)ᴴ := by
  ext p q
  simp only [idTensorSuperop, krausApply, pureDensity, Matrix.of_apply, Matrix.sum_apply,
    Matrix.mul_apply, Vm, conjTranspose_apply, RCLike.star_def, map_sum, map_mul]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.sum_mul_sum]
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

lemma perm3 {α β γ M : Type*} [Fintype α] [Fintype β] [Fintype γ] [AddCommMonoid M]
    (f : α → β → γ → M) : ∑ r, ∑ a, ∑ b, f r a b = ∑ a, ∑ b, ∑ r, f r a b := by
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun a _ => Finset.sum_comm

lemma gram_eq {R : Type} [Fintype R] (A : Fin m → Matrix (Fin d) (Fin d) ℂ)
    (psi : EuclideanSpace ℂ (R × Fin d)) (rho : Matrix (Fin d) (Fin d) ℂ)
    (hK : ∀ j j', ∑ r, psi (r, j) * conj (psi (r, j')) = rho j j') :
    ((Vm A psi)ᴴ * Vm A psi)ᵀ = Matrix.of fun k l => (A k * rho * (A l)ᴴ).trace := by
  ext k l
  simp only [Matrix.transpose_apply, Matrix.mul_apply, conjTranspose_apply, RCLike.star_def,
    Vm, Matrix.of_apply, Matrix.trace, Matrix.diag, Fintype.sum_prod_type, map_sum, map_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun y _ => ?_
  simp_rw [← hK]
  simp only [Finset.sum_mul, Finset.mul_sum]
  rw [perm3, Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
    Finset.sum_congr rfl fun r _ => ?_
  ring

/-- core: for any purification-type vector, the output entropy is the exchange-matrix entropy. -/
theorem ent_core {R : Type} [Fintype R] (A : Fin m → Matrix (Fin d) (Fin d) ℂ)
    (psi : EuclideanSpace ℂ (R × Fin d)) (rho : Matrix (Fin d) (Fin d) ℂ)
    (hK : ∀ j j', ∑ r, psi (r, j) * conj (psi (r, j')) = rho j j') :
    vnEntropy (idTensorSuperop (R := R) (krausApply A) (pureDensity psi)) =
      vnEntropy (Matrix.of fun k l => (A k * rho * (A l)ᴴ).trace) := by
  rw [idT_eq, x4_ent_swap, gram_eq A psi rho hK]

lemma sqrt_gram {I : Type} [Fintype I] [DecidableEq I] (rho : Matrix I I ℂ) (hrho : rho.PosSemidef)
    (j j' : I) : ∑ r, cfc Real.sqrt rho j r * conj (cfc Real.sqrt rho j' r) = rho j j' := by
  have hS : (cfc Real.sqrt rho)ᴴ = cfc Real.sqrt rho := by
    have : IsSelfAdjoint (cfc Real.sqrt rho) := cfc_predicate _ _
    exact this
  have hsa : IsSelfAdjoint rho := hrho.1
  have hmul : cfc Real.sqrt rho * cfc Real.sqrt rho = rho := by
    rw [← cfc_mul (fun x : ℝ => Real.sqrt x) (fun x : ℝ => Real.sqrt x) rho]
    conv_rhs => rw [← cfc_id' ℝ rho]
    apply cfc_congr
    intro x hx
    have : 0 ≤ x := by
      have := hrho.1.spectrum_real_eq_range_eigenvalues ▸ hx
      obtain ⟨i, rfl⟩ := this
      exact hrho.eigenvalues_nonneg i
    exact Real.mul_self_sqrt this
  have := congrFun (congrFun hmul j) j'
  rw [Matrix.mul_apply] at this
  rw [← this]
  refine Finset.sum_congr rfl fun r _ => ?_
  congr 1
  have h2 := congrFun (congrFun hS j') r
  rw [conjTranspose_apply, RCLike.star_def] at h2
  rw [← h2]
  simp

theorem ent_exchange [NeZero d] (Phi : Superop (Fin d) (Fin d)) (A : Fin m → Matrix (Fin d) (Fin d) ℂ)
    (hA : ∀ X, Phi X = krausApply A X)
    (rho : Matrix (Fin d) (Fin d) ℂ) (hrho : rho.PosSemidef) :
    entropyExchange Phi rho = vnEntropy (Matrix.of fun k l => (A k * rho * (A l)ᴴ).trace) := by
  have hPhi : Phi = krausApply A := funext hA
  subst hPhi
  unfold entropyExchange
  simp only
  apply ent_core
  intro j j'
  simp only [canonicalPurification]
  set e := Fintype.equivFin (Fin d)
  have hpsd : (show Matrix (Fin (Fintype.card (Fin d))) (Fin (Fintype.card (Fin d))) ℂ from
      fun i j => rho (e.symm i) (e.symm j)).PosSemidef := hrho.submatrix e.symm
  have := @sqrt_gram (Fin (Fintype.card (Fin d))) _ (instDecidableEqFin _) _ hpsd (e j) (e j')
  simp only [Equiv.symm_apply_apply] at this
  rw [← this]
  exact Fintype.sum_equiv e _ _ (fun r => rfl)

end X4KF

end

-- ===== KFG =====

noncomputable section

open QAlgorithms QAlgorithms.Papers.Independent.Support50.P41
open QAlgorithms.Papers.Independent.Dependency50.P40 (IsPurification)
open QAlgorithms.Papers.Independent.Dependency50.P45 (entropyExchange)
open QAlgorithms.Papers.Independent.Information100.P50 (complementaryMap)
open QAlgorithms.Papers.Independent.Gap20.P06 (dilationChannel environmentOutput)
open scoped Matrix ComplexConjugate ComplexOrder ENNReal

attribute [local instance] Classical.propDecidable Classical.decEq
attribute [local instance 2000] instKFF

namespace X4KF
open Matrix

variable {d m : ℕ}

lemma perm3b {α β γ M : Type*} [Fintype α] [Fintype β] [Fintype γ] [AddCommMonoid M]
    (f : α → β → γ → M) : ∑ a, ∑ b, ∑ y, f a b y = ∑ y, ∑ b, ∑ a, f a b y := by
  rw [perm3 f, Finset.sum_comm]

lemma cm_eq (A : Fin m → Matrix (Fin d) (Fin d) ℂ) (rho : Matrix (Fin d) (Fin d) ℂ) (k l : Fin m) :
    complementaryMap A rho k l = (A k * rho * (A l)ᴴ).trace := by
  change (∑ a, ∑ b, (∑ y, A k y a * conj (A l y b)) * rho a b) = _
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, conjTranspose_apply, RCLike.star_def,
    Finset.sum_mul]
  rw [perm3b]
  refine Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun b _ =>
    Finset.sum_congr rfl fun a _ => ?_
  ring

lemma W_density (A : Fin m → Matrix (Fin d) (Fin d) ℂ) (hA : IsKrausFamily A)
    (rho : Matrix (Fin d) (Fin d) ℂ) (hrho : IsDensityMatrix rho) :
    IsDensityMatrix (Matrix.of fun k l => (A k * rho * (A l)ᴴ).trace) := by
  refine ⟨?_, ?_⟩
  · let psi : EuclideanSpace ℂ (Fin d × Fin d) := WithLp.toLp 2 fun z => cfc Real.sqrt rho z.2 z.1
    have hK : ∀ j j', ∑ r, psi (r, j) * conj (psi (r, j')) = rho j j' :=
      fun j j' => sqrt_gram rho hrho.1 j j'
    rw [← gram_eq A psi rho hK]
    exact (Matrix.posSemidef_conjTranspose_mul_self _).transpose
  · simp only [Matrix.trace, Matrix.diag, Matrix.of_apply]
    have : ∑ k, ∑ i, (A k * rho * (A k)ᴴ) i i = ((∑ k, (A k)ᴴ * A k) * rho).trace := by
      rw [Matrix.sum_mul, Matrix.trace_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      change (A k * rho * (A k)ᴴ).trace = _
      rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc]
    rw [this, hA, Matrix.one_mul, hrho.2]

theorem exchange (Phi : Superop (Fin d) (Fin d)) [NeZero d] (A : Fin m → Matrix (Fin d) (Fin d) ℂ)
    (hA : OperatorSum Phi A)
    (rho : Matrix (Fin d) (Fin d) ℂ) (hrho : IsDensityMatrix rho) :
    (∀ k l, complementaryMap A rho k l = (A k * rho * (A l)ᴴ).trace) ∧
    IsDensityMatrix (complementaryMap A rho) ∧
    entropyExchange Phi rho = vnEntropy (complementaryMap A rho) := by
  have hW : complementaryMap A rho = Matrix.of fun k l => (A k * rho * (A l)ᴴ).trace := by
    ext k l; exact cm_eq A rho k l
  refine ⟨cm_eq A rho, ?_, ?_⟩
  · rw [hW]; exact W_density A hA.1 rho hrho
  · rw [hW]; exact ent_exchange Phi A hA.2 rho hrho.1

theorem intrinsic {a b : ℕ} [NeZero d]
    (Phi : Superop (Fin d) (Fin d)) (hPhi : IsChannel Phi)
    (rho : Matrix (Fin d) (Fin d) ℂ) (hrho : IsDensityMatrix rho)
    (psi : EuclideanSpace ℂ (Fin a × Fin d)) (hpsi : IsPurification rho psi)
    (phi : EuclideanSpace ℂ (Fin b × Fin d)) (hphi : IsPurification rho phi) :
    vnEntropy (idTensorSuperop Phi (pureDensity psi)) = entropyExchange Phi rho ∧
    vnEntropy (idTensorSuperop Phi (pureDensity phi)) = entropyExchange Phi rho := by
  obtain ⟨n, E, -, hE⟩ := hPhi
  have hP : Phi = krausApply E := funext hE
  rw [ent_exchange Phi E hE rho hrho.1, hP]
  refine ⟨ent_core E psi rho fun j j' => ?_, ent_core E phi rho fun j j' => ?_⟩
  · have := congrFun (congrFun hpsi.2 j) j'
    simpa [traceLeft, pureDensity] using this
  · have := congrFun (congrFun hphi.2 j) j'
    simpa [traceLeft, pureDensity] using this

variable {e : ℕ}

/-- `I ⊗ |η⟩` -/
def Keta (eta : EuclideanSpace ℂ (Fin e)) : Matrix (Fin d × Fin e) (Fin d) ℂ :=
  Matrix.of fun p j => if p.1 = j then eta p.2 else 0

lemma kron_K (eta : EuclideanSpace ℂ (Fin e)) (X : Matrix (Fin d) (Fin d) ℂ) :
    Matrix.kronecker X (pureDensity eta) =
      (Keta (d := d) eta * X * (Keta (d := d) eta)ᴴ : Matrix (Fin d × Fin e) (Fin d × Fin e) ℂ) := by
  ext ⟨j, g⟩ ⟨j', g'⟩
  simp only [Matrix.kronecker, Matrix.kroneckerMap_apply, pureDensity, Matrix.of_apply,
    Matrix.mul_apply, Keta, conjTranspose_apply, RCLike.star_def]
  rw [Finset.sum_eq_single j' (fun b _ hb => by simp [Ne.symm hb]) (by simp)]
  rw [Finset.sum_eq_single j (fun b _ hb => by simp [Ne.symm hb]) (by simp)]
  simp
  ring

/-- Kraus operators of the dilation: `A_f = (I ⊗ ⟨f|) U (I ⊗ |η⟩)` -/
def Adil (U : Matrix (Fin d × Fin e) (Fin d × Fin e) ℂ) (eta : EuclideanSpace ℂ (Fin e)) (f : Fin e) :
    Matrix (Fin d) (Fin d) ℂ :=
  fun a j => (U * Keta (d := d) eta : Matrix (Fin d × Fin e) (Fin d) ℂ) (a, f) j

lemma reassoc (U : Matrix (Fin d × Fin e) (Fin d × Fin e) ℂ) (eta : EuclideanSpace ℂ (Fin e))
    (X : Matrix (Fin d) (Fin d) ℂ) :
    U * (Keta (d := d) eta * X * (Keta (d := d) eta)ᴴ : Matrix (Fin d × Fin e) (Fin d × Fin e) ℂ) * Uᴴ =
      ((U * Keta (d := d) eta : Matrix (Fin d × Fin e) (Fin d) ℂ) * X *
        (U * Keta (d := d) eta : Matrix (Fin d × Fin e) (Fin d) ℂ)ᴴ :
          Matrix (Fin d × Fin e) (Fin d × Fin e) ℂ) := by
  rw [Matrix.conjTranspose_mul]
  simp only [Matrix.mul_assoc]

lemma dil_kraus (U : Matrix.unitaryGroup (Fin d × Fin e) ℂ) (eta : EuclideanSpace ℂ (Fin e))
    (X : Matrix (Fin d) (Fin d) ℂ) :
    dilationChannel U eta X = krausApply (Adil (U : Matrix _ _ ℂ) eta) X := by
  simp only [dilationChannel, conjSuperop]
  rw [kron_K, reassoc]
  ext a b
  simp only [traceRight, krausApply, Matrix.of_apply, Matrix.sum_apply]
  refine Finset.sum_congr rfl fun f _ => ?_
  simp only [Matrix.mul_apply, conjTranspose_apply, Adil]

lemma env_eq (U : Matrix.unitaryGroup (Fin d × Fin e) ℂ) (eta : EuclideanSpace ℂ (Fin e))
    (rho : Matrix (Fin d) (Fin d) ℂ) :
    environmentOutput U eta rho =
      Matrix.of fun k l => (Adil (U : Matrix _ _ ℂ) eta k * rho * (Adil (U : Matrix _ _ ℂ) eta l)ᴴ).trace := by
  simp only [environmentOutput, conjSuperop]
  rw [kron_K, reassoc]
  ext k l
  simp only [traceLeft, Matrix.of_apply, Matrix.trace, Matrix.diag]
  refine Finset.sum_congr rfl fun a _ => ?_
  simp only [Matrix.mul_apply, conjTranspose_apply, Adil]

theorem environment [NeZero d] [NeZero e]
    (U : Matrix.unitaryGroup (Fin d × Fin e) ℂ) (eta : EuclideanSpace ℂ (Fin e))
    (rho : Matrix (Fin d) (Fin d) ℂ) (hrho : IsDensityMatrix rho) :
    entropyExchange (dilationChannel U eta) rho = vnEntropy (environmentOutput U eta rho) := by
  have h1 := ent_exchange (d := d) (m := e) (dilationChannel U eta)
    (Adil (d := d) (e := e) (U : Matrix (Fin d × Fin e) (Fin d × Fin e) ℂ) eta)
    (fun X => dil_kraus U eta X) rho hrho.1
  rw [h1, env_eq]

end X4KF

end

-- ===== DP =====

noncomputable section

namespace QAlgorithms.Papers.Independent.Support50.P41

open QAlgorithms

open QAlgorithms.Entanglement (IsCompletelyPositive)

open QAlgorithms.Papers.Independent.Dependency50.P40 (IsPurification purificationFidelity)

open QAlgorithms.Papers.Independent.Dependency50.P45 (entropyExchange)

open QAlgorithms.Papers.Independent.Information100.P08 (canonicalPurification)

open QAlgorithms.Papers.Independent.Information100.P34 (choi dephasing)

open QAlgorithms.Papers.Independent.Dependency50.P38 (vectorizeInputFirst)

open QAlgorithms.Papers.Independent.Gap20.P06 (dilationChannel environmentOutput dilatedVector)

open QAlgorithms.Papers.Independent.Information100.P50 (complementaryMap)

open QAlgorithms.Papers.Independent.Renew46.P43 (IsCountablePOVM classicalKLTerm countableEntropy)

open scoped Matrix ComplexConjugate ComplexOrder ENNReal

attribute [local instance] Classical.propDecidable Classical.decEq

-- The accepted generic dilation functions fix classical equality on each factor.
-- Match that instance for Fin before forming their product unitary groups.

local instance (priority := 2000) instDP (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _


namespace X4DP
open Matrix X4KF
open scoped InnerProductSpace

variable {d e : ℕ}

lemma gram_unitary2 {P ι : Type*} [Fintype P] [Fintype ι] [DecidableEq ι] (α β : P → ι → ℂ)
    (h : ∀ p q, ∑ l, conj (β p l) * β q l = ∑ l, conj (α p l) * α q l) :
    ∃ U : Matrix.unitaryGroup ι ℂ, ∀ p k,
      α p k = ∑ l, (U : Matrix ι ι ℂ) k l * β p l := by
  have hin : ∀ x y : ι → ℂ, ⟪(WithLp.toLp 2 x : EuclideanSpace ℂ ι), WithLp.toLp 2 y⟫_ℂ =
      ∑ l, conj (x l) * y l := by
    intro x y
    simp [PiLp.inner_apply, RCLike.inner_apply, mul_comm]
  obtain ⟨T, hT⟩ := gram_iso (V := EuclideanSpace ℂ ι) (fun p => WithLp.toLp 2 (α p))
    (fun p => WithLp.toLp 2 (β p)) (by
      intro p q
      rw [hin, hin, h])
  let U : Matrix ι ι ℂ := fun k l => T (EuclideanSpace.single l 1) k
  have hcol : ∀ l l', ∑ k, conj (U k l) * U k l' = if l = l' then 1 else 0 := by
    intro l l'
    have := T.inner_map_map (EuclideanSpace.single l (1 : ℂ)) (EuclideanSpace.single l' 1)
    have e1 := hin (T (EuclideanSpace.single l (1 : ℂ))).ofLp (T (EuclideanSpace.single l' (1 : ℂ))).ofLp
    simp only [WithLp.toLp_ofLp] at e1
    rw [e1] at this
    simp only [U]
    rw [this, EuclideanSpace.inner_single_left]
    simp [PiLp.single_apply]
  have hU : star U * U = 1 := by
    ext l l'
    simp only [Matrix.mul_apply, Matrix.star_apply, RCLike.star_def, Matrix.one_apply]
    exact hcol l l'
  refine ⟨⟨U, Matrix.mem_unitaryGroup_iff'.mpr hU⟩, fun p k => ?_⟩
  have hx : (WithLp.toLp 2 (β p) : EuclideanSpace ℂ ι) =
      ∑ l, β p l • EuclideanSpace.single l (1 : ℂ) := by
    ext i
    simp [Pi.single_apply]
  have := congrArg (fun v : EuclideanSpace ℂ ι => v k) (hT p)
  simp only at this
  rw [← this, hx, map_sum]
  simp only [map_smul, WithLp.ofLp_sum, WithLp.ofLp_smul, Finset.sum_apply, Pi.smul_apply,
    smul_eq_mul, U]
  exact Finset.sum_congr rfl fun l _ => mul_comm _ _

lemma adil_uv (U : Matrix (Fin d × Fin e) (Fin d × Fin e) ℂ) (eta : EuclideanSpace ℂ (Fin e))
    (f : Fin e) (a i : Fin d) : Adil U eta f a i = uv U eta i (a, f) := by
  simp only [Adil, uv, wv, Keta, Matrix.mul_apply, Matrix.mulVec, dotProduct, Matrix.of_apply]
  refine Finset.sum_congr rfl fun p _ => ?_
  split_ifs with h1 h2 h2 <;> simp_all

lemma conj_entry' (A X : Matrix (Fin d) (Fin d) ℂ) (i j : Fin d) :
    (A * X * Aᴴ) i j = ∑ a, ∑ b, X a b * (A i a * conj (A j b)) := by
  simp only [Matrix.mul_apply, conjTranspose_apply, RCLike.star_def, Finset.sum_mul]
  rw [Finset.sum_comm]; refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a _ => by ring

lemma dil_entry (U : Matrix.unitaryGroup (Fin d × Fin e) ℂ) (eta : EuclideanSpace ℂ (Fin e))
    (X : Matrix (Fin d) (Fin d) ℂ) (a b : Fin d) :
    dilationChannel U eta X a b =
      ∑ i, ∑ j, X i j * ∑ f, uv (U : Matrix _ _ ℂ) eta i (a, f) * conj (uv (U : Matrix _ _ ℂ) eta j (b, f)) := by
  rw [dil_kraus]
  simp only [krausApply, Matrix.sum_apply, conj_entry', adil_uv, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]

lemma phi_entry {Phi : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d) (Fin d) ℂ}
    (X : Matrix (Fin d) (Fin d) ℂ) (a b : Fin d) :
    Phi X a b = ∑ i, ∑ j, X i j * choi Phi (i, a) (j, b) := by
  conv_lhs => rw [Matrix.matrix_eq_sum_single X]
  simp only [map_sum, Matrix.sum_apply, choi]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [show Matrix.single i j (X i j) = X i j • Matrix.single i j (1:ℂ) by simp, map_smul]
  rfl

lemma tr_choi {Phi : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d) (Fin d) ℂ}
    (hTP : ∀ X, (Phi X).trace = X.trace) (r r' : Fin d) :
    ∑ q, choi Phi (r, q) (r', q) = if r = r' then 1 else 0 := by
  have := hTP (Matrix.single r r' 1)
  simp only [Matrix.trace, Matrix.diag] at this
  simp only [choi, this, Matrix.single_apply]
  rw [Finset.sum_eq_single r (by intro b _ hb; simp [Ne.symm hb]) (by simp)]
  simp [eq_comm]

lemma sq_d [NeZero d] : ((Real.sqrt d : ℂ)) * (Real.sqrt d : ℂ) = d := by
  rw [← Complex.ofReal_mul, Real.mul_self_sqrt (Nat.cast_nonneg _)]; simp

lemma sqd_ne [NeZero d] : (Real.sqrt d : ℂ) ≠ 0 := by
  have : (0:ℝ) < Real.sqrt d := Real.sqrt_pos.2 (by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne d))
  exact_mod_cast this.ne'

lemma dcv [NeZero d] (U : Matrix.unitaryGroup (Fin d × Fin e) ℂ) (eta : EuclideanSpace ℂ (Fin e))
    (r q : Fin d) (f : Fin e) :
    dilationChoiVector U eta ((r, q), f) = (Real.sqrt d : ℂ)⁻¹ * uv (U : Matrix _ _ ℂ) eta r (q, f) := by
  simp only [dilationChoiVector, dilatedVector, act, PiLp.toLp_apply, uv, wv, Matrix.mulVec,
    dotProduct, Fintype.sum_prod_type, Matrix.kronecker, Matrix.kroneckerMap_apply, Matrix.one_apply,
    finiteMaxEntangled, Fintype.card_fin, Finset.mul_sum]
  rw [Finset.sum_eq_single r (fun b _ hb => by simp [Ne.symm hb]) (by simp)]
  refine Finset.sum_congr rfl fun q' _ => Finset.sum_congr rfl fun f' _ => ?_
  by_cases h : r = q'
  · subst h; simp; ring
  · simp [h, Ne.symm h]

lemma state_of {ι : Type*} [Fintype ι] (v : EuclideanSpace ℂ ι) (h : ∑ p, conj (v p) * v p = 1) :
    IsState v := by
  have h2 : ‖v‖ ^ 2 = 1 := by
    rw [EuclideanSpace.norm_sq_eq]
    have : ((∑ p, ‖v p‖ ^ 2 : ℝ) : ℂ) = 1 := by
      rw [← h]; push_cast; exact Finset.sum_congr rfl fun p _ => (RCLike.conj_mul _).symm
    exact_mod_cast this
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 h2

lemma state_sum {ι : Type*} [Fintype ι] (v : EuclideanSpace ℂ ι) (h : IsState v) :
    ∑ p, conj (v p) * v p = 1 := by
  have h2 : ‖v‖ ^ 2 = 1 := by rw [show ‖v‖ = 1 from h]; norm_num
  rw [EuclideanSpace.norm_sq_eq] at h2
  have : ((∑ p, ‖v p‖ ^ 2 : ℝ) : ℂ) = 1 := by exact_mod_cast h2
  rw [← this]; push_cast; exact Finset.sum_congr rfl fun p _ => RCLike.conj_mul _

end X4DP

end QAlgorithms.Papers.Independent.Support50.P41

end


-- ===== FanoLib =====

/-! Generic: Schur concavity of von Neumann entropy and the (quantum) Fano bound. -/

noncomputable section

namespace X4FN
open Matrix Real QAlgorithms
open scoped Matrix ComplexConjugate ComplexOrder

/-- classical Fano / grouping bound. -/
lemma fano_classical {ι : Type*} [Fintype ι] [DecidableEq ι] (p : ι → ℝ) (h0 : ∀ i, 0 ≤ p i)
    (h1 : ∑ i, p i = 1) (i0 : ι) (hN : 2 ≤ Fintype.card ι) :
    ∑ i, negMulLog (p i) ≤
      binEntropy (p i0) + (1 - p i0) * Real.log ((Fintype.card ι : ℝ) - 1) := by
  set t := Finset.univ.erase i0
  have hct : (t.card : ℝ) = (Fintype.card ι : ℝ) - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ]
    have : 1 ≤ Fintype.card ι := by omega
    push_cast [this]; ring
  have hpos : (0:ℝ) < t.card := by
    rw [hct]; have : (2:ℝ) ≤ Fintype.card ι := by exact_mod_cast hN
    linarith
  have hs : ∑ i ∈ t, p i = 1 - p i0 := by
    rw [← h1, ← Finset.add_sum_erase _ _ (Finset.mem_univ i0)]; ring
  have hsplit : ∑ i, negMulLog (p i) = negMulLog (p i0) + ∑ i ∈ t, negMulLog (p i) :=
    (Finset.add_sum_erase _ _ (Finset.mem_univ i0)).symm
  -- Jensen with uniform weights on t
  have hJ := concaveOn_negMulLog.le_map_sum (t := t) (w := fun _ => (t.card : ℝ)⁻¹) (p := p)
    (fun _ _ => by positivity) (by simp [Finset.sum_const, hpos.ne']) (fun i _ => h0 i)
  simp only [smul_eq_mul, ← Finset.mul_sum, hs] at hJ
  have hJ' : ∑ i ∈ t, negMulLog (p i) ≤ t.card * negMulLog ((t.card : ℝ)⁻¹ * (1 - p i0)) := by
    have := mul_le_mul_of_nonneg_left hJ hpos.le
    rwa [← mul_assoc, mul_inv_cancel₀ hpos.ne', one_mul] at this
  have hval : (t.card : ℝ) * negMulLog ((t.card : ℝ)⁻¹ * (1 - p i0)) =
      negMulLog (1 - p i0) + (1 - p i0) * Real.log (t.card) := by
    rcases eq_or_ne (1 - p i0) 0 with hz | hz
    · rw [hz]; simp
    · simp only [negMulLog]
      rw [Real.log_mul (inv_ne_zero hpos.ne') hz, Real.log_inv]
      field_simp
      ring
  rw [hsplit, binEntropy_eq_negMulLog_add_negMulLog_one_sub, ← hct]
  linarith

/-- trace of a cfc over a general finite index. -/
lemma cfc_trace {ι : Type*} [Fintype ι] [DecidableEq ι] {Y : Matrix ι ι ℂ} (hY : Y.IsHermitian)
    (f : ℝ → ℝ) : (cfc f Y).trace = ∑ i, ((f (hY.eigenvalues i) : ℝ) : ℂ) := by
  rw [hY.cfc_eq f, Matrix.IsHermitian.cfc, Unitary.conjStarAlgAut_apply, Matrix.trace_mul_cycle,
    Unitary.star_mul_self_of_mem hY.eigenvectorUnitary.2, one_mul, Matrix.trace_diagonal]
  rfl

lemma vn_eig {ι : Type*} [Fintype ι] [DecidableEq ι] {Y : Matrix ι ι ℂ} (hY : Y.IsHermitian) :
    vnEntropy Y = (∑ i, negMulLog (hY.eigenvalues i)) / Real.log 2 := by
  unfold vnEntropy
  rw [cfc_trace hY]
  simp only [Complex.re_sum, Complex.ofReal_re, negMulLog, Real.logb, Finset.sum_div,
    ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

lemma ds_sums {ι : Type*} [Fintype ι] [DecidableEq ι] (W : Matrix ι ι ℂ)
    (hW : W ∈ Matrix.unitaryGroup ι ℂ) :
    (∀ i, ∑ k, Complex.normSq (W k i) = 1) ∧ (∀ k, ∑ i, Complex.normSq (W k i) = 1) := by
  constructor
  · intro i
    have := congrFun (congrFun (Matrix.mem_unitaryGroup_iff'.1 hW) i) i
    simp only [Matrix.mul_apply, star_apply, RCLike.star_def, Matrix.one_apply_eq] at this
    have h2 : ((∑ k, Complex.normSq (W k i) : ℝ) : ℂ) = 1 := by
      rw [← this]; push_cast; simp only [Complex.normSq_eq_conj_mul_self]
    exact_mod_cast h2
  · intro k
    have := congrFun (congrFun (Matrix.mem_unitaryGroup_iff.1 hW) k) k
    simp only [Matrix.mul_apply, star_apply, RCLike.star_def, Matrix.one_apply_eq] at this
    have h2 : ((∑ i, Complex.normSq (W k i) : ℝ) : ℂ) = 1 := by
      rw [← this]; push_cast; simp only [Complex.normSq_eq_conj_mul_self]
      exact Finset.sum_congr rfl fun i _ => mul_comm _ _
    exact_mod_cast h2

lemma jensen_ds {ι : Type*} [Fintype ι] (lam : ι → ℝ) (hl0 : ∀ k, 0 ≤ lam k) (w : ι → ι → ℝ)
    (hw0 : ∀ i k, 0 ≤ w i k) (hcol : ∀ i, ∑ k, w i k = 1) (hrow : ∀ k, ∑ i, w i k = 1) :
    ∑ k, negMulLog (lam k) ≤ ∑ i, negMulLog (∑ k, w i k * lam k) := by
  calc ∑ k, negMulLog (lam k) = ∑ k, ∑ i, w i k * negMulLog (lam k) := by
        simp only [← Finset.sum_mul, hrow, one_mul]
    _ = ∑ i, ∑ k, w i k * negMulLog (lam k) := Finset.sum_comm
    _ ≤ ∑ i, negMulLog (∑ k, w i k * lam k) := by
        refine Finset.sum_le_sum fun i _ => ?_
        have := concaveOn_negMulLog.le_map_sum (t := Finset.univ) (w := w i) (p := lam)
          (fun k _ => hw0 i k) (hcol i) (fun k _ => hl0 k)
        simpa only [smul_eq_mul] using this

lemma diag_conj {ι : Type*} [Fintype ι] [DecidableEq ι] (U V : Matrix ι ι ℂ) (lam : ι → ℝ) (i : ι) :
    (Uᴴ * (V * diagonal (RCLike.ofReal ∘ lam : ι → ℂ) * star V) * U : Matrix ι ι ℂ) i i =
      ∑ k, ((Complex.normSq ((star V * U) k i) * lam k : ℝ) : ℂ) := by
  have hm : Uᴴ * (V * diagonal (RCLike.ofReal ∘ lam : ι → ℂ) * star V) * U =
      (star V * U)ᴴ * diagonal (RCLike.ofReal ∘ lam : ι → ℂ) * (star V * U) := by
    simp only [conjTranspose_mul, Matrix.mul_assoc, Matrix.star_eq_conjTranspose,
      conjTranspose_conjTranspose]
  rw [hm, Matrix.mul_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [mul_diagonal, conjTranspose_apply, RCLike.star_def]
  simp only [Function.comp_apply, Complex.ofReal_mul, Complex.normSq_eq_conj_mul_self]
  exact mul_right_comm (G := ℂ) _ _ _

/-- Schur concavity: the entropy of a basis diagonal dominates the von Neumann entropy. -/
lemma schur {ι : Type*} [Fintype ι] [DecidableEq ι] {σ : Matrix ι ι ℂ} (hσ : σ.PosSemidef)
    (U : Matrix ι ι ℂ) (hU : U ∈ Matrix.unitaryGroup ι ℂ) :
    (∀ i, 0 ≤ ((Uᴴ * σ * U) i i).re) ∧ ∑ i, ((Uᴴ * σ * U) i i).re = (σ.trace).re ∧
    vnEntropy σ ≤ (∑ i, negMulLog ((Uᴴ * σ * U) i i).re) / Real.log 2 := by
  obtain ⟨V, lam, hl0, htr, hvn, hV⟩ : ∃ (V : Matrix.unitaryGroup ι ℂ) (lam : ι → ℝ),
      (∀ k, 0 ≤ lam k) ∧ σ.trace = ∑ k, (lam k : ℂ) ∧
      vnEntropy σ = (∑ k, negMulLog (lam k)) / Real.log 2 ∧
      σ = (V : Matrix ι ι ℂ) * diagonal (RCLike.ofReal ∘ lam : ι → ℂ) * star (V : Matrix ι ι ℂ) :=
    ⟨hσ.1.eigenvectorUnitary, hσ.1.eigenvalues, hσ.eigenvalues_nonneg,
      by rw [hσ.1.trace_eq_sum_eigenvalues]; rfl, vn_eig hσ.1, by
      conv_lhs => rw [hσ.1.spectral_theorem]
      rw [Unitary.conjStarAlgAut_apply]⟩
  have hW : star (V : Matrix ι ι ℂ) * U ∈ Matrix.unitaryGroup ι ℂ :=
    Submonoid.mul_mem _ (Unitary.star_mem V.2) hU
  obtain ⟨hcol, hrow⟩ := ds_sums _ hW
  have hdiag : ∀ i, ((Uᴴ * σ * U) i i).re =
      ∑ k, Complex.normSq ((star (V : Matrix ι ι ℂ) * U) k i) * lam k := by
    intro i
    rw [hV, diag_conj, Complex.re_sum]; simp
  refine ⟨fun i => by
    rw [hdiag]; exact Finset.sum_nonneg fun k _ => mul_nonneg (Complex.normSq_nonneg _) (hl0 k),
    ?_, ?_⟩
  · simp only [hdiag]
    rw [Finset.sum_comm]
    simp only [← Finset.sum_mul, hrow, one_mul]
    rw [htr]; simp
  · rw [hvn]
    have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    refine div_le_div_of_nonneg_right ?_ hl2.le
    simp only [hdiag]
    exact jensen_ds _ hl0 _ (fun _ _ => Complex.normSq_nonneg _) hcol hrow

/-- quantum Fano bound for a density matrix and unit vector. -/
theorem fano {ι : Type*} [Fintype ι] [DecidableEq ι] {σ : Matrix ι ι ℂ} (hσ : σ.PosSemidef)
    (htr : σ.trace = 1) (ψ : ι → ℂ) (hψ : ∑ i, conj (ψ i) * ψ i = 1)
    (hN : 2 ≤ Fintype.card ι) :
    ((∑ a, ∑ b, conj (ψ a) * σ a b * ψ b).re ≤ 1) ∧
    vnEntropy σ ≤ binEntropy2 (∑ a, ∑ b, conj (ψ a) * σ a b * ψ b).re +
      (1 - (∑ a, ∑ b, conj (ψ a) * σ a b * ψ b).re) * Real.logb 2 ((Fintype.card ι : ℝ) - 1) := by
  have hne : Nonempty ι := Fintype.card_pos_iff.1 (by omega)
  obtain ⟨i0⟩ := hne
  obtain ⟨U, hU⟩ := QAlgorithms.Papers.Independent.Support50.P41.X4DP.gram_unitary2 (P := Unit) (fun _ => ψ) (fun _ => Pi.single i0 1) (by
    intro p q
    simp only [hψ]
    rw [Finset.sum_eq_single i0 (fun b _ hb => by simp [hb]) (by simp)]
    simp)
  have hcol : ∀ k, ψ k = (U : Matrix ι ι ℂ) k i0 := by
    intro k; rw [hU () k]
    rw [Finset.sum_eq_single i0 (fun b _ hb => by simp [hb]) (by simp)]
    simp
  obtain ⟨h0, h1, h2⟩ := schur hσ (U : Matrix ι ι ℂ) U.2
  set p := fun i => (((U : Matrix ι ι ℂ)ᴴ * σ * U) i i).re
  have hp0 : p i0 = (∑ a, ∑ b, conj (ψ a) * σ a b * ψ b).re := by
    simp only [p, Matrix.mul_apply, conjTranspose_apply, RCLike.star_def, hcol, Finset.sum_mul]
    rw [Finset.sum_comm]
  rw [htr, Complex.one_re] at h1
  have hF := fano_classical p h0 h1 i0 hN
  rw [← hp0]
  refine ⟨h1 ▸ Finset.single_le_sum (fun i _ => h0 i) (Finset.mem_univ i0), h2.trans ?_⟩
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  rw [div_le_iff₀ hl2]
  simp only [binEntropy2, Real.logb]
  calc _ ≤ _ := hF
    _ = _ := by field_simp

lemma vn_nonneg {ι : Type*} [Fintype ι] [DecidableEq ι] {σ : Matrix ι ι ℂ} (hσ : σ.PosSemidef)
    (htr : σ.trace = 1) : 0 ≤ vnEntropy σ := by
  rw [vn_eig hσ.1]
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine div_nonneg (Finset.sum_nonneg fun k _ => ?_) hl2.le
  have h0 := hσ.eigenvalues_nonneg
  have hs : ∑ k, hσ.1.eigenvalues k = 1 := by
    have := congrArg Complex.re (hσ.1.trace_eq_sum_eigenvalues.symm.trans htr)
    simpa [Complex.re_sum] using this
  exact Real.negMulLog_nonneg (h0 k) (hs ▸ Finset.single_le_sum (fun i _ => h0 i) (Finset.mem_univ k))

lemma fano_one {ι : Type*} [Fintype ι] [DecidableEq ι] {σ : Matrix ι ι ℂ} (hσ : σ.PosSemidef)
    (htr : σ.trace = 1) (ψ : ι → ℂ) (hψ : ∑ i, conj (ψ i) * ψ i = 1)
    (h1 : Fintype.card ι = 1) :
    (∑ a, ∑ b, conj (ψ a) * σ a b * ψ b).re = 1 ∧ vnEntropy σ = 0 := by
  obtain ⟨x, hx⟩ := Fintype.card_eq_one_iff.1 h1
  have hs : ∀ f : ι → ℂ, ∑ i, f i = f x := fun f =>
    Fintype.sum_eq_single x (fun y hy => absurd (hx y) hy)
  rw [hs] at hψ
  have hσx : σ x x = 1 := by rw [← htr, Matrix.trace, hs]; rfl
  refine ⟨by rw [hs, hs, hσx, mul_one, hψ, Complex.one_re], le_antisymm ?_ (vn_nonneg hσ htr)⟩
  obtain ⟨-, -, h2⟩ := schur hσ 1 (one_mem _)
  refine h2.trans (le_of_eq ?_)
  rw [Fintype.sum_eq_single x (fun y hy => absurd (hx y) hy)]
  simp [hσx]

end X4FN

end

-- ===== SFB =====

/-! Generic: `Σ_k |tr(ρ E_k)|² ≤ F(ρ, Σ_k E_k ρ E_kᴴ)²` for PSD `ρ`. -/

noncomputable section

namespace X4SF
open Matrix QAlgorithms
open scoped Matrix ComplexOrder ComplexConjugate

variable {ι K : Type*} [Fintype ι] [DecidableEq ι] [Fintype K]

lemma sq_sqrt (ρ : Matrix ι ι ℂ) (h : ρ.PosSemidef) : cfc Real.sqrt ρ * cfc Real.sqrt ρ = ρ := by
  open scoped MatrixOrder in
  have h0 : 0 ≤ ρ := h.nonneg
  have := CFC.sqrt_mul_sqrt_self ρ h0
  rwa [CFC.sqrt_eq_real_sqrt ρ h0, cfcₙ_eq_cfc] at this

lemma herm_sqrt (ρ : Matrix ι ι ℂ) : (cfc Real.sqrt ρ).IsHermitian :=
  (cfc_predicate Real.sqrt ρ : IsSelfAdjoint _)

lemma cfc_trace {Y : Matrix ι ι ℂ} (hY : Y.IsHermitian)
    (f : ℝ → ℝ) : (cfc f Y).trace = ∑ i, ((f (hY.eigenvalues i) : ℝ) : ℂ) := by
  rw [hY.cfc_eq f, Matrix.IsHermitian.cfc, Unitary.conjStarAlgAut_apply, Matrix.trace_mul_cycle,
    Unitary.star_mul_self_of_mem hY.eigenvectorUnitary.2, one_mul, Matrix.trace_diagonal]
  rfl

lemma diag_of {Y : Matrix ι ι ℂ} (hY : Y.IsHermitian) :
    star (hY.eigenvectorUnitary : Matrix ι ι ℂ) * Y * (hY.eigenvectorUnitary : Matrix ι ι ℂ) =
      diagonal (fun i => ((hY.eigenvalues i : ℝ) : ℂ)) := by
  set U : Matrix ι ι ℂ := (hY.eigenvectorUnitary : Matrix ι ι ℂ)
  have hU : star U * U = 1 := Unitary.star_mul_self_of_mem hY.eigenvectorUnitary.2
  conv_lhs => rw [hY.spectral_theorem, Unitary.conjStarAlgAut_apply]
  change star U * (U * _ * star U) * U = _
  rw [show star U * (U * diagonal (RCLike.ofReal ∘ hY.eigenvalues) * star U) * U =
    (star U * U) * diagonal (RCLike.ofReal ∘ hY.eigenvalues) * (star U * U) by
      simp only [Matrix.mul_assoc]]
  rw [hU, Matrix.one_mul, Matrix.mul_one]
  rfl

theorem key (ρ : Matrix ι ι ℂ) (hρ : ρ.PosSemidef) (E : K → Matrix ι ι ℂ) :
    ∑ k, Complex.normSq ((ρ * E k).trace) ≤ rootFidelity ρ (∑ k, E k * ρ * (E k)ᴴ) ^ 2 := by
  set R := cfc Real.sqrt ρ with hRdef
  have hR : Rᴴ = R := herm_sqrt ρ
  have hRR : R * R = ρ := sq_sqrt ρ hρ
  set H := R * (∑ k, E k * ρ * (E k)ᴴ) * R with hHdef
  have hHpsd : H.PosSemidef := by
    have : (∑ k, E k * ρ * (E k)ᴴ).PosSemidef :=
      Matrix.posSemidef_sum _ fun k _ => hρ.mul_mul_conjTranspose_same (E k)
    have := this.conjTranspose_mul_mul_same R
    rwa [hR] at this
  have hH : H.IsHermitian := hHpsd.1
  set U : Matrix ι ι ℂ := (hH.eigenvectorUnitary : Matrix ι ι ℂ)
  have hD : Uᴴ * H * U = diagonal (fun i => ((hH.eigenvalues i : ℝ) : ℂ)) := by
    rw [← Matrix.star_eq_conjTranspose]; exact diag_of hH
  have hU' : U * Uᴴ = 1 := by
    rw [← Matrix.star_eq_conjTranspose]; exact Unitary.mul_star_self_of_mem hH.eigenvectorUnitary.2
  set lam := hH.eigenvalues
  set G : K → Matrix ι ι ℂ := fun k => Uᴴ * (R * E k * R) * U
  have e : ∀ k, G k * (G k)ᴴ = Uᴴ * (R * (E k * ρ * (E k)ᴴ) * R) * U := by
    intro k
    simp only [G, Matrix.conjTranspose_mul, hR, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc U Uᴴ, hU', Matrix.one_mul, ← Matrix.mul_assoc R R, hRR]
  have hGG : ∑ k, G k * (G k)ᴴ = diagonal (fun i => ((lam i : ℝ) : ℂ)) := by
    rw [← hD, Finset.sum_congr rfl fun k _ => e k, ← Finset.sum_mul, ← Matrix.mul_sum,
      ← Finset.sum_mul, ← Matrix.mul_sum, hHdef]
  have htr : ∀ k, (ρ * E k).trace = ∑ i, G k i i := by
    intro k
    change _ = (G k).trace
    rw [show G k = Uᴴ * (R * E k * R) * U from rfl, Matrix.trace_mul_cycle,
      hU', Matrix.one_mul, ← hRR, Matrix.mul_assoc, Matrix.trace_mul_comm R]
  have hrow : ∀ i, ∑ k, Complex.normSq (G k i i) ≤ lam i := by
    intro i
    have h1 := congrArg (fun M => (M i i).re) hGG
    simp only [Matrix.sum_apply, Matrix.diagonal_apply_eq, Complex.ofReal_re, Complex.re_sum,
      Matrix.mul_apply, Matrix.conjTranspose_apply, RCLike.star_def, Complex.mul_conj] at h1
    rw [← h1]
    refine Finset.sum_le_sum fun k _ => ?_
    exact Finset.single_le_sum (f := fun j => Complex.normSq (G k i j))
      (fun j _ => Complex.normSq_nonneg _) (Finset.mem_univ i)
  have hRF : rootFidelity ρ (∑ k, E k * ρ * (E k)ᴴ) = ∑ i, Real.sqrt (lam i) := by
    unfold rootFidelity
    rw [← hRdef, ← hHdef, cfc_trace hH, Complex.re_sum]
    simp [lam]
  -- triangle inequality in ℓ²(K)
  let a : ι → EuclideanSpace ℂ K := fun i => WithLp.toLp 2 fun k => G k i i
  have hna : ∀ i, ‖a i‖ ≤ Real.sqrt (lam i) := by
    intro i
    rw [EuclideanSpace.norm_eq]
    refine Real.sqrt_le_sqrt ?_
    refine le_trans (le_of_eq ?_) (hrow i)
    refine Finset.sum_congr rfl fun k _ => ?_
    simp [a, Complex.sq_norm]
  have hsum : ‖∑ i, a i‖ ≤ ∑ i, Real.sqrt (lam i) :=
    (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => hna i)
  have hlhs : ∑ k, Complex.normSq ((ρ * E k).trace) = ‖∑ i, a i‖ ^ 2 := by
    rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [htr k, ← Complex.sq_norm]
    simp [a, WithLp.ofLp_sum]
  rw [hlhs, hRF]
  exact pow_le_pow_left₀ (norm_nonneg _) hsum 2

end X4SF

end

-- ===== SUB =====

/-! Generic: subadditivity of von Neumann entropy, `S(AB) ≤ S(A) + S(B)`. -/

noncomputable section

namespace X4SU
open Matrix Real QAlgorithms
open scoped Matrix ComplexConjugate ComplexOrder Kronecker

/-- one term of the classical bound. -/
lemma term {r a b : ℝ} (hr : 0 ≤ r) (ha : r ≤ a) (hb : r ≤ b) :
    negMulLog r ≤ -(r * Real.log a) - r * Real.log b + a * b - r := by
  rcases hr.eq_or_lt with rfl | hr
  · simp; exact mul_nonneg (by linarith) (by linarith)
  · have ha' : 0 < a := hr.trans_le ha
    have hb' : 0 < b := hr.trans_le hb
    have hx : 0 < a * b / r := by positivity
    have h := Real.log_le_sub_one_of_pos hx
    rw [Real.log_div (by positivity) hr.ne', Real.log_mul ha'.ne' hb'.ne'] at h
    have h2 := mul_le_mul_of_nonneg_left h hr.le
    rw [show r * (a * b / r - 1) = a * b - r by field_simp] at h2
    simp only [negMulLog]
    nlinarith

/-- classical subadditivity of Shannon entropy. -/
lemma classical {A B : Type*} [Fintype A] [Fintype B] (r : A × B → ℝ) (h0 : ∀ p, 0 ≤ r p)
    (h1 : ∑ p, r p = 1) :
    ∑ p, negMulLog (r p) ≤ ∑ i, negMulLog (∑ j, r (i, j)) + ∑ j, negMulLog (∑ i, r (i, j)) := by
  have hle : ∀ p, negMulLog (r p) ≤ -(r p * Real.log (∑ j, r (p.1, j))) -
      r p * Real.log (∑ i, r (i, p.2)) + (∑ j, r (p.1, j)) * (∑ i, r (i, p.2)) - r p := by
    intro p
    refine term (h0 p) ?_ ?_
    · exact Finset.single_le_sum (f := fun j => r (p.1, j)) (fun j _ => h0 _) (Finset.mem_univ p.2)
    · exact Finset.single_le_sum (f := fun i => r (i, p.2)) (fun i _ => h0 _) (Finset.mem_univ p.1)
  refine (Finset.sum_le_sum fun p _ => hle p).trans (le_of_eq ?_)
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_neg_distrib]
  have e1 : ∑ p : A × B, r p * Real.log (∑ j, r (p.1, j)) = ∑ i, (∑ j, r (i, j)) * Real.log (∑ j, r (i, j)) := by
    rw [Fintype.sum_prod_type]; simp [Finset.sum_mul]
  have e2 : ∑ p : A × B, r p * Real.log (∑ i, r (i, p.2)) = ∑ j, (∑ i, r (i, j)) * Real.log (∑ i, r (i, j)) := by
    rw [Fintype.sum_prod_type, Finset.sum_comm]; simp [Finset.sum_mul]
  have e3 : ∑ p : A × B, (∑ j, r (p.1, j)) * (∑ i, r (i, p.2)) = 1 := by
    rw [Fintype.sum_prod_type]
    simp_rw [← Finset.mul_sum, ← Finset.sum_mul]
    rw [Finset.sum_comm (f := fun i y => r (y, i))]
    have : ∑ x, ∑ y, r (x, y) = 1 := by rw [← h1, Fintype.sum_prod_type]
    rw [this]; ring
  rw [e1, e2, e3, h1]
  simp only [negMulLog, neg_mul, Finset.sum_neg_distrib]
  ring

lemma pull4 {α β γ δ M : Type*} [Fintype α] [Fintype β] [Fintype γ] [Fintype δ] [AddCommMonoid M]
    (f : α → β → γ → δ → M) :
    ∑ a, ∑ b, ∑ c, ∑ d, f a b c d = ∑ b, ∑ c, ∑ d, ∑ a, f a b c d := by
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Finset.sum_comm]

variable {A B : Type*} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

lemma marg_left (ω : Matrix (A × B) (A × B) ℂ) (UA : Matrix A A ℂ) (UB : Matrix B B ℂ)
    (hUB : UB * UBᴴ = 1) (i : A) :
    ∑ j, ((UA ⊗ₖ UB)ᴴ * ω * (UA ⊗ₖ UB)) (i, j) (i, j) = (UAᴴ * traceRight ω * UA) i i := by
  have hd : ∀ s t : B, ∑ j, conj (UB s j) * UB t j = if t = s then 1 else 0 := by
    intro s t
    have := congrFun (congrFun hUB t) s
    rw [Matrix.mul_apply, Matrix.one_apply] at this
    rw [← this]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [conjTranspose_apply, RCLike.star_def, mul_comm]
  simp only [Matrix.mul_apply, conjTranspose_apply, kroneckerMap_apply, traceRight, Matrix.of_apply,
    RCLike.star_def, map_mul, Fintype.sum_prod_type, Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_comm.trans (Finset.sum_congr rfl fun x _ => ?_)
  rw [pull4]
  have e : ∀ (x1 : B) (x2 : A) (x3 : B), ∑ j, conj (UA x2 i) * conj (UB x3 j) * ω (x2, x3) (x, x1) *
      (UA x i * UB x1 j) = conj (UA x2 i) * ω (x2, x3) (x, x1) * UA x i * (if x1 = x3 then 1 else 0) := by
    intro x1 x2 x3
    rw [← hd x3 x1, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  simp_rw [e, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  exact Finset.sum_comm

lemma marg_right (ω : Matrix (A × B) (A × B) ℂ) (UA : Matrix A A ℂ) (UB : Matrix B B ℂ)
    (hUA : UA * UAᴴ = 1) (j : B) :
    ∑ i, ((UA ⊗ₖ UB)ᴴ * ω * (UA ⊗ₖ UB)) (i, j) (i, j) = (UBᴴ * traceLeft ω * UB) j j := by
  have hd : ∀ s t : A, ∑ i, conj (UA s i) * UA t i = if t = s then 1 else 0 := by
    intro s t
    have := congrFun (congrFun hUA t) s
    rw [Matrix.mul_apply, Matrix.one_apply] at this
    rw [← this]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [conjTranspose_apply, RCLike.star_def, mul_comm]
  simp only [Matrix.mul_apply, conjTranspose_apply, kroneckerMap_apply, traceLeft, Matrix.of_apply,
    RCLike.star_def, map_mul, Fintype.sum_prod_type, Finset.sum_mul, Finset.mul_sum]
  rw [pull4]
  have e : ∀ (b : A) (c : B) (d : A), ∑ a, ∑ x, conj (UA d a) * conj (UB x j) * ω (d, x) (b, c) *
      (UA b a * UB c j) = (∑ x, conj (UB x j) * ω (d, x) (b, c) * UB c j) * (if b = d then 1 else 0) := by
    intro b c d
    rw [Finset.sum_comm, ← hd d b, Finset.sum_mul]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    ring
  simp_rw [e, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Finset.sum_comm]

lemma herm_right {ω : Matrix (A × B) (A × B) ℂ} (h : ω.IsHermitian) : (traceRight ω).IsHermitian := by
  ext i j
  have := fun s => congrFun (congrFun h (i, s)) (j, s)
  simp only [conjTranspose_apply, traceRight, Matrix.of_apply, star_sum] at this ⊢
  exact Finset.sum_congr rfl fun s _ => this s

lemma herm_left {ω : Matrix (A × B) (A × B) ℂ} (h : ω.IsHermitian) : (traceLeft ω).IsHermitian := by
  ext i j
  have := fun s => congrFun (congrFun h (s, i)) (s, j)
  simp only [conjTranspose_apply, traceLeft, Matrix.of_apply, star_sum] at this ⊢
  exact Finset.sum_congr rfl fun s _ => this s

/-- subadditivity of von Neumann entropy. -/
theorem subadd (ω : Matrix (A × B) (A × B) ℂ) (hω : ω.PosSemidef) (htr : ω.trace = 1) :
    vnEntropy ω ≤ vnEntropy (traceRight ω) + vnEntropy (traceLeft ω) := by
  have hA := herm_right hω.1
  have hB := herm_left hω.1
  set UA : Matrix A A ℂ := (hA.eigenvectorUnitary : Matrix A A ℂ)
  set UB : Matrix B B ℂ := (hB.eigenvectorUnitary : Matrix B B ℂ)
  have hUA : UA * UAᴴ = 1 := by
    rw [← Matrix.star_eq_conjTranspose]; exact Unitary.mul_star_self_of_mem hA.eigenvectorUnitary.2
  have hUB : UB * UBᴴ = 1 := by
    rw [← Matrix.star_eq_conjTranspose]; exact Unitary.mul_star_self_of_mem hB.eigenvectorUnitary.2
  have hU : UA ⊗ₖ UB ∈ Matrix.unitaryGroup (A × B) ℂ :=
    Matrix.kronecker_mem_unitary hA.eigenvectorUnitary.2 hB.eigenvectorUnitary.2
  obtain ⟨h0, h1, h2⟩ := X4FN.schur hω _ hU
  set r : A × B → ℝ := fun p => (((UA ⊗ₖ UB)ᴴ * ω * (UA ⊗ₖ UB)) p p).re with hr
  have hra : ∀ i, ∑ j, r (i, j) = hA.eigenvalues i := by
    intro i
    simp only [r]
    rw [← Complex.re_sum, marg_left ω UA UB hUB i, ← Matrix.star_eq_conjTranspose, X4SF.diag_of hA,
      diagonal_apply_eq, Complex.ofReal_re]
  have hrb : ∀ j, ∑ i, r (i, j) = hB.eigenvalues j := by
    intro j
    simp only [r]
    rw [← Complex.re_sum, marg_right ω UA UB hUA j, ← Matrix.star_eq_conjTranspose, X4SF.diag_of hB,
      diagonal_apply_eq, Complex.ofReal_re]
  have hc := classical r h0 (by rw [h1, htr, Complex.one_re])
  simp only [hra, hrb] at hc
  rw [X4FN.vn_eig hA, X4FN.vn_eig hB, ← add_div]
  refine h2.trans (div_le_div_of_nonneg_right hc (Real.log_pos (by norm_num)).le)

end X4SU

end

-- ===== ZEA =====

noncomputable section

namespace X4ZE
open Matrix QAlgorithms Real
open scoped Matrix ComplexConjugate ComplexOrder

/-- a unit vector `v` with `v v† = Σ φ_k φ_k†` forces every `φ_k ∈ span v`. -/
lemma rank1_split {α ι : Type*} [Fintype α] [Fintype ι] (v : α → ℂ) (hv : ∑ a, v a * conj (v a) = 1)
    (φ : ι → α → ℂ) (h : ∀ a b, v a * conj (v b) = ∑ k, φ k a * conj (φ k b)) (k : ι) :
    ∀ a, φ k a = (∑ b, conj (v b) * φ k b) * v a := by
  set c := ∑ b, conj (v b) * φ k b
  set ψ : α → ℂ := fun a => φ k a - c * v a
  have nsq : ∀ u w : α → ℂ, ((Complex.normSq (∑ a, conj (u a) * w a) : ℝ) : ℂ) =
      ∑ a, ∑ b, conj (u a) * (w a * conj (w b)) * u b := by
    intro u w
    rw [Complex.normSq_eq_conj_mul_self, map_sum, Finset.sum_mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    simp only [map_mul, Complex.conj_conj]; ring
  have hQ : ∀ ψ : α → ℂ, Complex.normSq (∑ a, conj (ψ a) * v a) =
      ∑ j, Complex.normSq (∑ a, conj (ψ a) * φ j a) := by
    intro ψ
    have : ((Complex.normSq (∑ a, conj (ψ a) * v a) : ℝ) : ℂ) =
        ((∑ j, Complex.normSq (∑ a, conj (ψ a) * φ j a) : ℝ) : ℂ) := by
      rw [nsq]; push_cast; simp_rw [nsq, h, Finset.mul_sum, Finset.sum_mul]
      calc ∑ a, ∑ b, ∑ j, conj (ψ a) * (φ j a * conj (φ j b)) * ψ b
          = ∑ a, ∑ j, ∑ b, conj (ψ a) * (φ j a * conj (φ j b)) * ψ b :=
            Finset.sum_congr rfl fun a _ => Finset.sum_comm
        _ = _ := Finset.sum_comm
    exact_mod_cast this
  have hψv : ∑ a, conj (ψ a) * v a = 0 := by
    have : ∑ a, conj (v a) * ψ a = 0 := by
      simp only [ψ, mul_sub, Finset.sum_sub_distrib]
      have : ∑ a, conj (v a) * (c * v a) = c * ∑ a, v a * conj (v a) := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun a _ => by ring
      rw [this, hv, mul_one]; simp [c]
    have := congrArg conj this
    rw [map_sum, map_zero] at this
    rw [← this]; exact Finset.sum_congr rfl fun a _ => by simp [mul_comm]
  have hψφ : ∑ a, conj (ψ a) * φ k a = ∑ a, conj (ψ a) * ψ a := by
    have : ∀ a, φ k a = ψ a + c * v a := fun a => by simp [ψ]
    simp_rw [this, mul_add, Finset.sum_add_distrib]
    have : ∑ a, conj (ψ a) * (c * v a) = c * ∑ a, conj (ψ a) * v a := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun a _ => by ring
    rw [this, hψv, mul_zero, add_zero]
  have hz := hQ ψ
  rw [hψv, map_zero] at hz
  have hk := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => Complex.normSq_nonneg _)).1 hz.symm k
    (Finset.mem_univ k)
  rw [hψφ, Complex.normSq_eq_zero] at hk
  have hn : ∑ a, Complex.normSq (ψ a) = 0 := by
    have : ((∑ a, Complex.normSq (ψ a) : ℝ) : ℂ) = 0 := by
      push_cast; rw [← hk]
      exact Finset.sum_congr rfl fun a _ => by rw [Complex.normSq_eq_conj_mul_self]
    exact_mod_cast this
  intro a
  have := (Finset.sum_eq_zero_iff_of_nonneg (fun a _ => Complex.normSq_nonneg _)).1 hn a
    (Finset.mem_univ a)
  rw [Complex.normSq_eq_zero] at this
  simp only [ψ, sub_eq_zero] at this
  exact this

/-- spectral decomposition as a sum of eigenprojectors. -/
lemma spec_sum {I : Type*} [Fintype I] [DecidableEq I] {ρ : Matrix I I ℂ} (h : ρ.IsHermitian) :
    ρ = ∑ k, ((h.eigenvalues k : ℝ) : ℂ) • pureDensity (h.eigenvectorBasis k) := by
  conv_lhs => rw [h.spectral_theorem, Unitary.conjStarAlgAut_apply]
  ext a b
  simp only [Matrix.mul_apply, diagonal, Matrix.of_apply, Matrix.sum_apply, Matrix.smul_apply,
    pureDensity, smul_eq_mul, Function.comp_apply, Matrix.star_apply, RCLike.star_def,
    mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true, ite_mul, zero_mul,
    Finset.sum_ite_eq, Matrix.IsHermitian.eigenvectorUnitary_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [RCLike.ofReal_eq_complex_ofReal]
  ring

lemma cfc_trace {ι : Type*} [Fintype ι] [DecidableEq ι] {Y : Matrix ι ι ℂ} (hY : Y.IsHermitian)
    (f : ℝ → ℝ) : (cfc f Y).trace = ∑ i, ((f (hY.eigenvalues i) : ℝ) : ℂ) := by
  rw [hY.cfc_eq f, Matrix.IsHermitian.cfc, Unitary.conjStarAlgAut_apply, Matrix.trace_mul_cycle,
    Unitary.star_mul_self_of_mem hY.eigenvectorUnitary.2, one_mul, Matrix.trace_diagonal]
  rfl

lemma vn_eig {ι : Type*} [Fintype ι] [DecidableEq ι] {Y : Matrix ι ι ℂ} (hY : Y.IsHermitian) :
    vnEntropy Y = (∑ i, negMulLog (hY.eigenvalues i)) / Real.log 2 := by
  unfold vnEntropy
  rw [cfc_trace hY]
  simp only [Complex.re_sum, Complex.ofReal_re, negMulLog, Real.logb, Finset.sum_div,
    ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- zero entropy density matrix is a pure projector. -/
lemma pure_of_vn {I : Type*} [Fintype I] [DecidableEq I] {ρ : Matrix I I ℂ} (hρ : ρ.PosSemidef)
    (h1 : ρ.trace = 1) (h0 : vnEntropy ρ = 0) :
    ∃ w : EuclideanSpace ℂ I, ‖w‖ = 1 ∧ ρ = pureDensity w := by
  set h := hρ.1
  set lam := h.eigenvalues
  set v := h.eigenvectorBasis
  have hv : ∀ k, ‖v k‖ = 1 := fun k => v.orthonormal.1 k
  have hl0 : ∀ k, 0 ≤ lam k := hρ.eigenvalues_nonneg
  have hsum : ∑ k, lam k = 1 := by
    have := h.trace_eq_sum_eigenvalues
    rw [h1] at this
    have h3 : ((∑ k, lam k : ℝ) : ℂ) = 1 := by push_cast; exact this.symm
    exact_mod_cast h3
  have hle1 : ∀ k, lam k ≤ 1 := fun k => by
    rw [← hsum]; exact Finset.single_le_sum (fun j _ => hl0 j) (Finset.mem_univ k)
  have hS : ∑ k, negMulLog (lam k) = 0 := by
    rw [vn_eig h] at h0
    rcases div_eq_zero_iff.1 h0 with h0 | h0
    · exact h0
    · exfalso; exact (Real.log_pos (by norm_num : (1:ℝ) < 2)).ne' h0
  have h01 : ∀ k, lam k = 0 ∨ lam k = 1 := by
    intro k
    have := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => Real.negMulLog_nonneg (hl0 j) (hle1 j))).1
      hS k (Finset.mem_univ k)
    rcases (hl0 k).eq_or_lt with h | h
    · exact Or.inl h.symm
    rcases (hle1 k).eq_or_lt with h' | h'
    · exact Or.inr h'
    exfalso
    have : lam k * Real.log (lam k) < 0 := mul_neg_of_pos_of_neg h (Real.log_neg h h')
    rw [Real.negMulLog] at *; linarith
  obtain ⟨i0, hi0⟩ : ∃ i0, lam i0 = 1 := by
    by_contra hc
    push Not at hc
    have : ∑ k, lam k = 0 := Finset.sum_eq_zero fun k _ => (h01 k).resolve_right (hc k)
    linarith
  have hother : ∀ k, k ≠ i0 → lam k = 0 := by
    have hs := Finset.add_sum_erase Finset.univ lam (Finset.mem_univ i0)
    rw [hsum, hi0] at hs
    have h0 : ∑ k ∈ Finset.univ.erase i0, lam k = 0 := by linarith
    intro k hk
    exact (Finset.sum_eq_zero_iff_of_nonneg (fun k _ => hl0 k)).1 h0 k
      (Finset.mem_erase.2 ⟨hk, Finset.mem_univ k⟩)
  refine ⟨v i0, hv i0, ?_⟩
  rw [spec_sum h]
  rw [Finset.sum_eq_single i0 (fun k _ hk => by simp [lam, hother k hk]) (by simp)]
  simp [lam, hi0]
  rfl

lemma unit_sum {I : Type*} [Fintype I] (v : EuclideanSpace ℂ I) (hv : ‖v‖ = 1) :
    ∑ i, v i * conj (v i) = 1 := by
  have h1 : ∑ i, ‖v i‖ ^ 2 = 1 := by
    rw [← EuclideanSpace.norm_sq_eq, hv, one_pow]
  have : ∑ i, v i * conj (v i) = ((∑ i, ‖v i‖ ^ 2 : ℝ) : ℂ) := by
    push_cast
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]; push_cast; rfl
  rw [this, h1]; simp

end X4ZE

end

-- ===== LEA =====

/-! Generic von Neumann entropy facts: scaling, orthogonal rank-one sums, `S(Σσ) ≤ ΣS(σ)`
for unnormalized PSD terms, and concavity `Σ (S(σ_m) + p_m log p_m) ≤ S(Σσ)`. -/

noncomputable section

namespace X4LE
open Matrix Real QAlgorithms
open scoped Matrix ComplexConjugate ComplexOrder

lemma cfc_diag {ι : Type*} [Fintype ι] [DecidableEq ι] (d : ι → ℝ) (f : ℝ → ℝ) :
    cfc f (diagonal (fun i => (d i : ℂ))) = diagonal (fun i => (f (d i) : ℂ)) := by
  classical
  let S : Finset ℝ := Finset.univ.image d
  let p : Polynomial ℝ := Lagrange.interpolate S id f
  have hp : ∀ x ∈ S, p.eval x = f x := fun x hx =>
    Lagrange.eval_interpolate_at_node (v := id) (r := f) (Set.injOn_id _) hx
  have hD : IsSelfAdjoint (diagonal (fun i => (d i : ℂ))) := by
    rw [IsSelfAdjoint, star_eq_conjTranspose, diagonal_conjTranspose]
    congr 1; funext i; simp
  have hspec : ∀ x ∈ spectrum ℝ (diagonal (fun i => (d i : ℂ))), x ∈ S := by
    intro x hx
    rw [← spectrum.preimage_algebraMap ℂ, Set.mem_preimage, spectrum_diagonal] at hx
    obtain ⟨i, hi⟩ := hx
    have : d i = x := by simpa using hi
    simp [S, ← this]
  rw [cfc_congr (g := fun x => p.eval x) (fun x hx => (hp x (hspec x hx)).symm),
    cfc_polynomial p _ hD]
  have : Polynomial.aeval (diagonal (fun i => (d i : ℂ))) p =
      diagonal (Polynomial.aeval (fun i => (d i : ℂ)) p) :=
    (Polynomial.aeval_algHom_apply (diagonalAlgHom ℝ) (fun i => (d i : ℂ)) p)
  rw [this, Polynomial.aeval_pi_apply]
  congr 1; funext i
  have h := Polynomial.aeval_algebraMap_apply ℂ (d i) p
  simp only [Complex.coe_algebraMap] at h
  rw [h, Polynomial.coe_aeval_eq_eval, hp _ (by simp [S] : d i ∈ S)]

lemma vn_diag {ι : Type*} [Fintype ι] [DecidableEq ι] (x : ι → ℝ) :
    vnEntropy (diagonal fun i => (x i : ℂ)) = -∑ i, x i * Real.logb 2 (x i) := by
  unfold vnEntropy
  rw [cfc_diag, Matrix.trace_diagonal, Complex.re_sum]
  simp

lemma nml (x : ℝ) : negMulLog x / Real.log 2 = -(x * Real.logb 2 x) := by
  simp only [negMulLog, Real.logb]; ring

lemma cont_xlog : Continuous (fun x : ℝ => x * Real.logb 2 x) := by
  have : (fun x : ℝ => x * Real.logb 2 x) = fun x => (x * Real.log x) / Real.log 2 := by
    funext x; rw [Real.logb]; ring
  rw [this]; exact Real.continuous_mul_log.div_const _

/-- scaling of the (unnormalized) entropy. -/
lemma vn_smul {ι : Type*} [Fintype ι] [DecidableEq ι] {X : Matrix ι ι ℂ} (hX : X.IsHermitian)
    {c : ℝ} (hc : 0 < c) :
    vnEntropy ((c : ℂ) • X) = c * vnEntropy X - c * Real.logb 2 c * X.trace.re := by
  have hsa : IsSelfAdjoint X := hX
  have e1 : (c : ℂ) • X = c • X := by rw [Complex.coe_smul]
  unfold vnEntropy
  rw [e1, ← cfc_comp_smul c (fun x : ℝ => x * Real.logb 2 x) X cont_xlog.continuousOn]
  have hf : ∀ x : ℝ, (c • x) * Real.logb 2 (c • x) =
      (c * Real.logb 2 c) * x + c * (x * Real.logb 2 x) := by
    intro x
    rcases eq_or_ne x 0 with rfl | hx
    · simp
    · rw [smul_eq_mul, Real.logb_mul hc.ne' hx]; ring
  rw [cfc_congr (g := fun x => (c * Real.logb 2 c) * x + c * (x * Real.logb 2 x))
    (fun x _ => hf x)]
  rw [cfc_add (a := X) (fun x => (c * Real.logb 2 c) * x) (fun x => c * (x * Real.logb 2 x))
    (by fun_prop) ((continuous_const.mul cont_xlog).continuousOn),
    cfc_const_mul_id (c * Real.logb 2 c) X, cfc_const_mul c (fun x => x * Real.logb 2 x) X cont_xlog.continuousOn]
  simp only [Matrix.trace_add, Matrix.trace_smul, Complex.add_re, Complex.real_smul,
    Complex.re_ofReal_mul]
  ring

/-- entropy of a sum of mutually orthogonal rank-one terms. -/
lemma orth_ent {ι T : Type} [Fintype ι] [DecidableEq ι] [Fintype T] [DecidableEq T]
    (φ : T → ι → ℂ) (h : ∀ t t', t ≠ t' → ∑ i, φ t i * conj (φ t' i) = 0) :
    vnEntropy (∑ t, Matrix.of fun a b => φ t a * conj (φ t b)) =
      -∑ t, (∑ i, ‖φ t i‖ ^ 2) * Real.logb 2 (∑ i, ‖φ t i‖ ^ 2) := by
  set V : Matrix ι T ℂ := Matrix.of fun i t => φ t i
  have hV : (∑ t, Matrix.of fun a b => φ t a * conj (φ t b)) = V * Vᴴ := by
    ext a b; simp [V, Matrix.mul_apply, Matrix.sum_apply, conjTranspose_apply]
  rw [hV, X4KF.x4_ent_swap]
  have hD : (Vᴴ * V)ᵀ = diagonal fun t => ((∑ i, ‖φ t i‖ ^ 2 : ℝ) : ℂ) := by
    ext t t'
    simp only [transpose_apply, Matrix.mul_apply, conjTranspose_apply, V, Matrix.of_apply,
      diagonal_apply, RCLike.star_def]
    split_ifs with htt
    · subst htt; push_cast
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]; push_cast; ring
    · rw [← h t t' htt]
      exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  rw [hD, vn_diag]

/-- square-root eigen-amplitudes of a PSD matrix. -/
def amp {ι : Type} [Fintype ι] [DecidableEq ι] {σ : Matrix ι ι ℂ} (hσ : σ.PosSemidef) (k a : ι) : ℂ :=
  ((Real.sqrt (hσ.1.eigenvalues k) : ℝ) : ℂ) * hσ.1.eigenvectorBasis k a

lemma amp_decomp {ι : Type} [Fintype ι] [DecidableEq ι] {σ : Matrix ι ι ℂ} (hσ : σ.PosSemidef) :
    σ = ∑ k, Matrix.of fun a b => amp hσ k a * conj (amp hσ k b) := by
  conv_lhs => rw [X4ZE.spec_sum hσ.1]
  refine Finset.sum_congr rfl fun k _ => ?_
  ext a b
  have hs : ((Real.sqrt (hσ.1.eigenvalues k) : ℝ) : ℂ) * ((Real.sqrt (hσ.1.eigenvalues k) : ℝ) : ℂ) =
      ((hσ.1.eigenvalues k : ℝ) : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (hσ.eigenvalues_nonneg k)]
  simp only [Matrix.smul_apply, pureDensity, Matrix.of_apply, smul_eq_mul, amp, map_mul,
    Complex.conj_ofReal]
  rw [← hs]; ring

lemma amp_inner {ι : Type} [Fintype ι] [DecidableEq ι] {σ : Matrix ι ι ℂ} (hσ : σ.PosSemidef)
    (k k' : ι) : ∑ a, amp hσ k a * conj (amp hσ k' a) =
      if k = k' then ((hσ.1.eigenvalues k : ℝ) : ℂ) else 0 := by
  have ho := hσ.1.eigenvectorBasis.orthonormal
  have hin : ∑ a, hσ.1.eigenvectorBasis k a * conj (hσ.1.eigenvectorBasis k' a) =
      if k = k' then 1 else 0 := by
    have := orthonormal_iff_ite.1 ho k' k
    rw [EuclideanSpace.inner_eq_star_dotProduct] at this
    have e : (if k = k' then (1:ℂ) else 0) = if k' = k then 1 else 0 := by
      by_cases h : k = k' <;> simp [h, eq_comm]
    rw [e, ← this]
    simp [dotProduct, mul_comm]
  simp only [amp, map_mul, Complex.conj_ofReal]
  have : ∀ a, ((Real.sqrt (hσ.1.eigenvalues k) : ℝ) : ℂ) * hσ.1.eigenvectorBasis k a *
      (((Real.sqrt (hσ.1.eigenvalues k') : ℝ) : ℂ) * conj (hσ.1.eigenvectorBasis k' a)) =
      (((Real.sqrt (hσ.1.eigenvalues k) : ℝ) : ℂ) * ((Real.sqrt (hσ.1.eigenvalues k') : ℝ) : ℂ)) *
        (hσ.1.eigenvectorBasis k a * conj (hσ.1.eigenvectorBasis k' a)) := fun a => by ring
  simp only [this, ← Finset.mul_sum, hin]
  split_ifs with h
  · subst h
    rw [mul_one, ← Complex.ofReal_mul, Real.mul_self_sqrt (hσ.eigenvalues_nonneg k)]
  · simp

lemma amp_norm {ι : Type} [Fintype ι] [DecidableEq ι] {σ : Matrix ι ι ℂ} (hσ : σ.PosSemidef)
    (k : ι) : ∑ a, ‖amp hσ k a‖ ^ 2 = hσ.1.eigenvalues k := by
  have h := amp_inner hσ k k
  rw [if_pos rfl] at h
  have : ((∑ a, ‖amp hσ k a‖ ^ 2 : ℝ) : ℂ) = ∑ a, amp hσ k a * conj (amp hσ k a) := by
    push_cast
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]; push_cast; ring
  exact_mod_cast this.trans h

lemma vn_amp {ι : Type} [Fintype ι] [DecidableEq ι] {σ : Matrix ι ι ℂ} (hσ : σ.PosSemidef) :
    vnEntropy σ = -∑ k, hσ.1.eigenvalues k * Real.logb 2 (hσ.1.eigenvalues k) := by
  rw [X4ZE.vn_eig hσ.1, Finset.sum_div, ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun k _ => nml _

/-- finite mixtures of rank-one terms: entropy ≤ Shannon entropy of the weights. -/
lemma fin_bound {ι T : Type} [Fintype ι] [DecidableEq ι] [Fintype T] [DecidableEq T]
    (φ : T → ι → ℂ) :
    vnEntropy (∑ t, Matrix.of fun a b => φ t a * conj (φ t b)) ≤
      -∑ t, (∑ i, ‖φ t i‖ ^ 2) * Real.logb 2 (∑ i, ‖φ t i‖ ^ 2) := by
  set V : Matrix ι T ℂ := Matrix.of fun i t => φ t i
  have hV : (∑ t, Matrix.of fun a b => φ t a * conj (φ t b)) = V * Vᴴ := by
    ext a b; simp [V, Matrix.mul_apply, Matrix.sum_apply, conjTranspose_apply]
  rw [hV, X4KF.x4_ent_swap]
  have hG : ((Vᴴ * V)ᵀ).PosSemidef := (Matrix.posSemidef_conjTranspose_mul_self V).transpose
  obtain ⟨-, -, h⟩ := X4FN.schur hG 1 (one_mem _)
  refine h.trans (le_of_eq ?_)
  rw [Finset.sum_div, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [← nml]
  congr 2
  rw [conjTranspose_one, Matrix.one_mul, Matrix.mul_one]
  simp only [Matrix.transpose_apply, Matrix.mul_apply, conjTranspose_apply, V, Matrix.of_apply,
    RCLike.star_def, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Complex.conj_mul', ← Complex.ofReal_pow, Complex.ofReal_re]

/-- `S(Σ σ_m) ≤ Σ S(σ_m)` for unnormalized PSD terms. -/
theorem subconc {ι M : Type} [Fintype ι] [DecidableEq ι] [Fintype M] [DecidableEq M]
    (σ : M → Matrix ι ι ℂ) (hσ : ∀ m, (σ m).PosSemidef) :
    vnEntropy (∑ m, σ m) ≤ ∑ m, vnEntropy (σ m) := by
  have e : ∑ m, σ m = ∑ t : M × ι, Matrix.of fun a b => amp (hσ t.1) t.2 a * conj (amp (hσ t.1) t.2 b) := by
    rw [Fintype.sum_prod_type]
    exact Finset.sum_congr rfl fun m _ => amp_decomp (hσ m)
  rw [e]
  refine (fin_bound _).trans (le_of_eq ?_)
  rw [Fintype.sum_prod_type, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [vn_amp (hσ m)]
  simp only [amp_norm]

/-- block-diagonal (classical-quantum) assembly. -/
def blk {ι M : Type} [DecidableEq M] (σ : M → Matrix ι ι ℂ) : Matrix (M × ι) (M × ι) ℂ :=
  fun x y => if x.1 = y.1 then σ x.1 x.2 y.2 else 0

lemma blk_decomp {ι M : Type} [Fintype ι] [DecidableEq ι] [Fintype M] [DecidableEq M]
    (σ : M → Matrix ι ι ℂ) (hσ : ∀ m, (σ m).PosSemidef) :
    blk σ = ∑ t : M × ι, Matrix.of fun x y =>
      (if x.1 = t.1 then amp (hσ t.1) t.2 x.2 else 0) *
        conj (if y.1 = t.1 then amp (hσ t.1) t.2 y.2 else 0) := by
  ext x y
  rw [Matrix.sum_apply, Fintype.sum_prod_type, Finset.sum_eq_single x.1]
  · obtain ⟨x1, x2⟩ := x; obtain ⟨y1, y2⟩ := y
    by_cases h : x1 = y1
    · subst h
      simp only [blk, Matrix.of_apply, if_true]
      conv_lhs => rw [amp_decomp (hσ x1)]
      simp [Matrix.sum_apply]
    · simp [blk, Matrix.of_apply, h, Ne.symm h]
  · intro m _ hm
    refine Finset.sum_eq_zero fun k _ => ?_
    simp [Matrix.of_apply, Ne.symm hm]
  · simp

lemma vn_blk {ι M : Type} [Fintype ι] [DecidableEq ι] [Fintype M] [DecidableEq M]
    (σ : M → Matrix ι ι ℂ) (hσ : ∀ m, (σ m).PosSemidef) :
    vnEntropy (blk σ) = ∑ m, vnEntropy (σ m) := by
  rw [blk_decomp σ hσ, orth_ent]
  · rw [Fintype.sum_prod_type, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [vn_amp (hσ m)]
    congr 1
    refine Finset.sum_congr rfl fun k _ => ?_
    have : ∑ x : M × ι, ‖(if x.1 = m then amp (hσ m) k x.2 else 0)‖ ^ 2 =
        (hσ m).1.eigenvalues k := by
      rw [Fintype.sum_prod_type, Finset.sum_eq_single m (fun b _ hb => by simp [hb]) (by simp)]
      simp [amp_norm]
    rw [this]
  · intro t t' htt
    rw [Fintype.sum_prod_type]
    by_cases h1 : t.1 = t'.1
    · rw [Finset.sum_eq_single t.1 (fun b _ hb => by simp [hb]) (by simp)]
      simp only [if_true, ← h1]
      rw [amp_inner, if_neg]
      intro h2; exact htt (Prod.ext h1 h2)
    · refine Finset.sum_eq_zero fun m _ => Finset.sum_eq_zero fun a _ => ?_
      by_cases hm : m = t.1
      · subst hm; simp [Ne.symm h1, h1]
      · simp [hm]

/-- concavity: `Σ (S(σ_m) + p_m log p_m) ≤ S(Σ σ_m)` with `p_m = tr σ_m`, `Σ p_m = 1`. -/
theorem conc {ι M : Type} [Fintype ι] [DecidableEq ι] [Fintype M] [DecidableEq M]
    (σ : M → Matrix ι ι ℂ) (hσ : ∀ m, (σ m).PosSemidef) (h1 : ∑ m, (σ m).trace = 1) :
    ∑ m, (vnEntropy (σ m) + (σ m).trace.re * Real.logb 2 (σ m).trace.re) ≤
      vnEntropy (∑ m, σ m) := by
  have hpsd : (blk σ).PosSemidef := by
    rw [blk_decomp σ hσ]
    refine Matrix.posSemidef_sum _ fun t _ => ?_
    have := Matrix.posSemidef_vecMulVec_self_star (fun x : M × ι =>
      if x.1 = t.1 then amp (hσ t.1) t.2 x.2 else 0)
    convert this using 1
    ext x y; simp [vecMulVec_apply]
  have htr : (blk σ).trace = 1 := by
    rw [← h1, Matrix.trace, Fintype.sum_prod_type]
    simp [blk, Matrix.trace]
  have hsub := X4SU.subadd (blk σ) hpsd htr
  have hR : traceRight (blk σ) = diagonal fun m => (((σ m).trace.re : ℝ) : ℂ) := by
    ext m m'
    simp only [traceRight, Matrix.of_apply, blk, diagonal_apply]
    split_ifs with h
    · subst h
      have hn := Complex.nonneg_iff.1 (hσ m).trace_nonneg
      have hre : (((σ m).trace.re : ℝ) : ℂ) = (σ m).trace :=
        Complex.ext (by simp) (by simp [hn.2])
      rw [hre]; rfl
    · simp
  have hL : traceLeft (blk σ) = ∑ m, σ m := by
    ext a b; simp [traceLeft, blk, Matrix.sum_apply]
  rw [hR, hL, vn_diag, vn_blk σ hσ] at hsub
  rw [Finset.sum_add_distrib]
  linarith

end X4LE

end

-- ===== LEB =====

/-! Kraus branches of a bipartite pure vector: Bob marginals, the unnormalized entanglement
functional `Gv` and its monotonicity under Alice-side Kraus families. -/

noncomputable section

namespace X4LE
open Matrix Real QAlgorithms
open QAlgorithms.Papers.Independent.Support50.P42
open QAlgorithms.Papers.Independent.Next46.P39 (rectAct)
open scoped Matrix ComplexConjugate ComplexOrder

variable {a b : ℕ}

/-- reshaped coefficient matrix. -/
def Mv {α β : Type} (v : EuclideanSpace ℂ (α × β)) : Matrix α β ℂ := Matrix.of fun x y => v (x, y)

lemma akb_apply {c : ℕ} (A : Matrix (Fin c) (Fin a) ℂ) (ψ : EuclideanSpace ℂ (Fin a × Fin b))
    (x : Fin c × Fin b) : aliceKetBranch A ψ x = ∑ τ, A x.1 τ * ψ (τ, x.2) := by
  unfold aliceKetBranch rectAct
  simp only [PiLp.toLp_apply, Matrix.mulVec, dotProduct, Fintype.sum_prod_type,
    Matrix.kroneckerMap_apply, Matrix.kronecker, Matrix.one_apply]
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [Finset.sum_eq_single x.2]
  · simp
  · intro β _ hβ; simp [Ne.symm hβ]
  · simp

lemma Mv_akb {c : ℕ} (A : Matrix (Fin c) (Fin a) ℂ) (ψ : EuclideanSpace ℂ (Fin a × Fin b)) :
    Mv (aliceKetBranch A ψ) = A * Mv ψ := by
  ext x y; simp [Mv, akb_apply, Matrix.mul_apply]

lemma tl_eq {α β : Type} [Fintype α] [Fintype β] (v : EuclideanSpace ℂ (α × β)) :
    traceLeft (pureDensity v) = ((Mv v)ᴴ * Mv v)ᵀ := by
  ext y y'
  simp [traceLeft, pureDensity, Mv, Matrix.mul_apply, mul_comm]

lemma tr_eq {α β : Type} [Fintype α] [Fintype β] (v : EuclideanSpace ℂ (α × β)) :
    traceRight (pureDensity v) = Mv v * (Mv v)ᴴ := by
  ext y y'
  simp [traceRight, pureDensity, Mv, Matrix.mul_apply]

lemma tl_psd {α β : Type} [Fintype α] [Fintype β] (v : EuclideanSpace ℂ (α × β)) :
    (traceLeft (pureDensity v)).PosSemidef := by
  rw [tl_eq]; exact (posSemidef_conjTranspose_mul_self _).transpose

lemma tl_trace {α β : Type} [Fintype α] [Fintype β] (v : EuclideanSpace ℂ (α × β)) :
    (traceLeft (pureDensity v)).trace = ((‖v‖ ^ 2 : ℝ) : ℂ) := by
  rw [EuclideanSpace.norm_sq_eq]
  push_cast
  simp only [Matrix.trace, traceLeft, pureDensity, Matrix.diag, Matrix.of_apply,
    Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]; push_cast; rfl

lemma tl_trace_re {α β : Type} [Fintype α] [Fintype β] (v : EuclideanSpace ℂ (α × β)) :
    (traceLeft (pureDensity v)).trace.re = ‖v‖ ^ 2 := by
  rw [tl_trace]; exact_mod_cast Complex.ofReal_re _

lemma vn_zero {ι : Type*} [Fintype ι] [DecidableEq ι] : vnEntropy (0 : Matrix ι ι ℂ) = 0 := by
  unfold vnEntropy; simp

lemma tl_smul {α β : Type} [Fintype α] (c : ℂ) (M : Matrix (α × β) (α × β) ℂ) :
    traceLeft (c • M) = c • traceLeft M := by
  ext; simp [traceLeft, Finset.mul_sum]

lemma pd_smul {α : Type} (c : ℂ) (v : EuclideanSpace ℂ α) :
    pureDensity (c • v) = ((‖c‖ ^ 2 : ℝ) : ℂ) • pureDensity v := by
  ext x y
  simp only [pureDensity, Matrix.of_apply, Matrix.smul_apply, PiLp.smul_apply, smul_eq_mul, map_mul]
  have : c * conj c = ((‖c‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  rw [← this]; ring

/-- Kraus completeness: the Bob marginal is unchanged on average. -/
lemma tl_sum {M : Type} [Fintype M] (c : M → ℕ) (A : ∀ m, Matrix (Fin (c m)) (Fin a) ℂ)
    (hA : ∑ m, (A m)ᴴ * A m = 1) (ψ : EuclideanSpace ℂ (Fin a × Fin b)) :
    ∑ m, traceLeft (pureDensity (aliceKetBranch (A m) ψ)) = traceLeft (pureDensity ψ) := by
  simp only [tl_eq, Mv_akb, conjTranspose_mul]
  rw [← Matrix.transpose_sum]
  congr 1
  have : ∀ m, (Mv ψ)ᴴ * (A m)ᴴ * (A m * Mv ψ) = (Mv ψ)ᴴ * ((A m)ᴴ * A m) * Mv ψ := fun m => by
    simp only [Matrix.mul_assoc]
  simp only [this]
  rw [← Matrix.sum_mul, ← Matrix.mul_sum, hA, Matrix.mul_one]

lemma akb_smul {c : ℕ} (A : Matrix (Fin c) (Fin a) ℂ) (z : ℂ) (ψ : EuclideanSpace ℂ (Fin a × Fin b)) :
    aliceKetBranch A (z • ψ) = z • aliceKetBranch A ψ := by
  ext x; simp only [akb_apply, PiLp.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => by ring

/-- unnormalized entanglement functional: `‖v‖² · S(Bob marginal of v/‖v‖)`. -/
def Gv {α β : Type} [Fintype α] [Fintype β] [DecidableEq β] (v : EuclideanSpace ℂ (α × β)) : ℝ :=
  vnEntropy (traceLeft (pureDensity v)) + ‖v‖ ^ 2 * Real.logb 2 (‖v‖ ^ 2)

lemma Gv_zero {α β : Type} [Fintype α] [Fintype β] [DecidableEq β] :
    Gv (0 : EuclideanSpace ℂ (α × β)) = 0 := by
  have : pureDensity (0 : EuclideanSpace ℂ (α × β)) = 0 := by ext; simp [pureDensity]
  have h2 : traceLeft (0 : Matrix (α × β) (α × β) ℂ) = 0 := by ext; simp [traceLeft]
  simp [Gv, this, h2, vn_zero]

lemma Gv_smul {α β : Type} [Fintype α] [Fintype β] [DecidableEq β] (z : ℂ)
    (v : EuclideanSpace ℂ (α × β)) : Gv (z • v) = ‖z‖ ^ 2 * Gv v := by
  rcases eq_or_ne z 0 with rfl | hz
  · simp [Gv_zero]
  rcases eq_or_ne v 0 with rfl | hv
  · simp [Gv_zero]
  have hz2 : 0 < ‖z‖ ^ 2 := by positivity
  have hv2 : 0 < ‖v‖ ^ 2 := by have := norm_pos_iff.2 hv; positivity
  unfold Gv
  rw [pd_smul, tl_smul, vn_smul (tl_psd v).1 hz2, tl_trace_re, norm_smul, mul_pow,
    Real.logb_mul hz2.ne' hv2.ne']
  ring

lemma Gv_unit {α β : Type} [Fintype α] [Fintype β] [DecidableEq β] (v : EuclideanSpace ℂ (α × β))
    (hv : ‖v‖ = 1) : Gv v = vnEntropy (traceLeft (pureDensity v)) := by
  simp [Gv, hv]

lemma Gv_branch {α β : Type} [Fintype α] [Fintype β] [DecidableEq β] (v : EuclideanSpace ℂ (α × β)) :
    Gv v = vnEntropy (traceLeft (pureDensity v)) +
      (traceLeft (pureDensity v)).trace.re * Real.logb 2 (traceLeft (pureDensity v)).trace.re := by
  rw [tl_trace_re]; rfl

/-- monotonicity of `Gv` under any Alice-side Kraus family (outputs may differ). -/
theorem mono {M : Type} [Fintype M] [DecidableEq M] (c : M → ℕ)
    (A : ∀ m, Matrix (Fin (c m)) (Fin a) ℂ) (hA : ∑ m, (A m)ᴴ * A m = 1)
    (ψ : EuclideanSpace ℂ (Fin a × Fin b)) :
    ∑ m, Gv (aliceKetBranch (A m) ψ) ≤ Gv ψ := by
  rcases eq_or_ne ψ 0 with rfl | hψ
  · have : ∀ m, aliceKetBranch (A m) (0 : EuclideanSpace ℂ (Fin a × Fin b)) = 0 := fun m => by
      have := akb_smul (A m) 0 (0 : EuclideanSpace ℂ (Fin a × Fin b)); simpa using this
    simp [this, Gv_zero]
  have hn : 0 < ‖ψ‖ := norm_pos_iff.2 hψ
  set u : EuclideanSpace ℂ (Fin a × Fin b) := ((‖ψ‖⁻¹ : ℝ) : ℂ) • ψ
  have hu : ‖u‖ = 1 := by
    simp only [u, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_inv, abs_norm]
    field_simp
  have hψu : ψ = ((‖ψ‖ : ℝ) : ℂ) • u := by
    simp only [u, smul_smul, ← Complex.ofReal_mul, mul_inv_cancel₀ hn.ne', Complex.ofReal_one,
      one_smul]
  rw [hψu]
  simp only [akb_smul, Gv_smul, ← Finset.mul_sum]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  rw [Gv_unit u hu, ← tl_sum c A hA u]
  simp only [Gv_branch]
  refine conc _ (fun m => tl_psd _) ?_
  rw [← Matrix.trace_sum, tl_sum c A hA u, tl_trace, hu]; simp

/-- swap of the two tensor factors. -/
def swapV {α β : Type} (v : EuclideanSpace ℂ (α × β)) : EuclideanSpace ℂ (β × α) :=
  WithLp.toLp 2 fun p => v (p.2, p.1)

lemma norm_swapV {α β : Type} [Fintype α] [Fintype β] (v : EuclideanSpace ℂ (α × β)) :
    ‖swapV v‖ = ‖v‖ := by
  have : ‖swapV v‖ ^ 2 = ‖v‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type,
      Fintype.sum_prod_type, Finset.sum_comm]
    rfl
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 this

lemma Gv_swap {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    (v : EuclideanSpace ℂ (α × β)) : Gv (swapV v) = Gv v := by
  unfold Gv
  rw [norm_swapV]
  congr 1
  have e1 : traceLeft (pureDensity (swapV v)) = Mv v * (Mv v)ᴴ := by
    ext; simp [traceLeft, pureDensity, swapV, Mv, Matrix.mul_apply]
  rw [e1, X4KF.x4_ent_swap, tl_eq]

end X4LE

end

-- ===== ERA =====

/-! Generic entropy facts: scaling with `c ≥ 0`, additivity on orthogonal PSD summands,
invariance under isometric conjugation, pure states, and the qubit bound `S ≤ 1`. -/

noncomputable section

namespace X4ER
open Matrix Real QAlgorithms
open scoped Matrix ComplexConjugate ComplexOrder

lemma vn_smul0 {ι : Type*} [Fintype ι] [DecidableEq ι] {X : Matrix ι ι ℂ} (hX : X.IsHermitian)
    {c : ℝ} (hc : 0 ≤ c) :
    vnEntropy ((c : ℂ) • X) = c * vnEntropy X - c * Real.logb 2 c * X.trace.re := by
  rcases hc.eq_or_lt with rfl | hc'
  · simp [X4LE.vn_zero]
  · exact X4LE.vn_smul hX hc'

lemma amp_orth {ι : Type} [Fintype ι] [DecidableEq ι] {X Y : Matrix ι ι ℂ}
    (hX : X.PosSemidef) (hY : Y.PosSemidef) (hXY : X * Y = 0) (k l : ι) :
    ∑ a, X4LE.amp hX k a * conj (X4LE.amp hY l a) = 0 := by
  set v := hX.1.eigenvectorBasis k
  set w := hY.1.eigenvectorBasis l
  set lam := hX.1.eigenvalues k
  set mu := hY.1.eigenvalues l
  have hv : ∀ a, ∑ b, X a b * v b = lam * v a := by
    intro a
    have := congrFun (hX.1.mulVec_eigenvectorBasis k) a
    simpa [Matrix.mulVec, dotProduct] using this
  have hw : ∀ a, ∑ b, Y a b * w b = mu * w a := by
    intro a
    have := congrFun (hY.1.mulVec_eigenvectorBasis l) a
    simpa [Matrix.mulVec, dotProduct] using this
  have key : ((lam : ℂ) * mu) * ∑ a, v a * conj (w a) = 0 := by
    have e1 : ((lam : ℂ) * mu) * ∑ a, v a * conj (w a) =
        ∑ a, (∑ b, X a b * v b) * conj (∑ c, Y a c * w c) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [hv a, hw a, map_mul, Complex.conj_ofReal]; ring
    rw [e1]
    have e2 : ∀ a, (∑ b, X a b * v b) * conj (∑ c, Y a c * w c) =
        ∑ b, ∑ c, v b * conj (w c) * (conj (X b a) * conj (Y a c)) := by
      intro a
      rw [map_sum, Finset.sum_mul_sum]
      refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun c _ => ?_
      have hx : X a b = conj (X b a) := by
        have := congrFun (congrFun hX.1.eq b) a
        rw [conjTranspose_apply] at this
        rw [← this]; simp
      rw [hx, map_mul]; ring
    simp only [e2]
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun b _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun c _ => ?_
    rw [← Finset.mul_sum]
    have : ∑ a, conj (X b a) * conj (Y a c) = conj ((X * Y) b c) := by
      rw [Matrix.mul_apply, map_sum]; simp [map_mul]
    rw [this, hXY]; simp
  have e : ∑ a, X4LE.amp hX k a * conj (X4LE.amp hY l a) =
      ((Real.sqrt lam : ℝ) : ℂ) * ((Real.sqrt mu : ℝ) : ℂ) * ∑ a, v a * conj (w a) := by
    simp only [X4LE.amp, map_mul, Complex.conj_ofReal, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => by ring
  rw [e]
  by_cases h0 : (lam : ℂ) * mu = 0
  · rcases mul_eq_zero.1 h0 with h | h
    · have : lam = 0 := by exact_mod_cast h
      simp [this]
    · have : mu = 0 := by exact_mod_cast h
      simp [this]
  · rw [(mul_eq_zero.1 key).resolve_left h0, mul_zero]

/-- entropy is additive on PSD summands with orthogonal supports. -/
lemma vn_add_orth {ι : Type} [Fintype ι] [DecidableEq ι] {X Y : Matrix ι ι ℂ}
    (hX : X.PosSemidef) (hY : Y.PosSemidef) (hXY : X * Y = 0) :
    vnEntropy (X + Y) = vnEntropy X + vnEntropy Y := by
  have hYX : Y * X = 0 := by
    have := congrArg conjTranspose hXY
    rwa [conjTranspose_mul, hX.1.eq, hY.1.eq, conjTranspose_zero] at this
  set φ : ι ⊕ ι → ι → ℂ := fun t => Sum.elim (X4LE.amp hX) (X4LE.amp hY) t
  have hdec : X + Y = ∑ t, Matrix.of fun a b => φ t a * conj (φ t b) := by
    conv_lhs => rw [X4LE.amp_decomp hX, X4LE.amp_decomp hY]
    rw [Fintype.sum_sum_type]; rfl
  have horth : ∀ t t', t ≠ t' → ∑ i, φ t i * conj (φ t' i) = 0 := by
    intro t t' htt
    rcases t with k | k <;> rcases t' with l | l
    · simp only [φ, Sum.elim_inl]
      rw [X4LE.amp_inner, if_neg (fun h => htt (by rw [h]))]
    · exact amp_orth hX hY hXY k l
    · exact amp_orth hY hX hYX k l
    · simp only [φ, Sum.elim_inr]
      rw [X4LE.amp_inner, if_neg (fun h => htt (by rw [h]))]
  rw [hdec, X4LE.orth_ent φ horth, Fintype.sum_sum_type, X4LE.vn_amp hX, X4LE.vn_amp hY]
  simp only [φ, Sum.elim_inl, Sum.elim_inr, X4LE.amp_norm]
  ring

/-- entropy is invariant under conjugation by an isometry. -/
lemma vn_conj_iso {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    {X : Matrix ι ι ℂ} (hX : X.PosSemidef) (J : Matrix κ ι ℂ) (hJ : Jᴴ * J = 1) :
    vnEntropy (J * X * Jᴴ) = vnEntropy X := by
  set V : Matrix ι ι ℂ := Matrix.of fun a k => X4LE.amp hX k a
  have hV : X = V * Vᴴ := by
    conv_lhs => rw [X4LE.amp_decomp hX]
    ext a b; simp [V, Matrix.mul_apply, Matrix.sum_apply, conjTranspose_apply]
  have h1 : J * X * Jᴴ = (J * V) * (J * V)ᴴ := by
    rw [hV, conjTranspose_mul]; simp only [Matrix.mul_assoc]
  have h2 : (J * V)ᴴ * (J * V) = Vᴴ * V := by
    rw [conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc Jᴴ, hJ, Matrix.one_mul]
  rw [h1, X4KF.x4_ent_swap, h2, ← X4KF.x4_ent_swap, ← hV]

lemma vn_pure {ι : Type} [Fintype ι] [DecidableEq ι] (ψ : EuclideanSpace ℂ ι) (hψ : ‖ψ‖ = 1) :
    vnEntropy (pureDensity ψ) = 0 := by
  have h : pureDensity ψ = ∑ _t : Unit, Matrix.of fun a b => ψ a * conj (ψ b) := by
    simp [pureDensity]
  rw [h, X4LE.orth_ent (fun _ a => ψ a) (fun t t' h => absurd (Subsingleton.elim t t') h)]
  have : ∑ i, ‖ψ i‖ ^ 2 = 1 := by rw [← EuclideanSpace.norm_sq_eq, hψ, one_pow]
  simp [this]

lemma qubit_le {X : Matrix (Fin 2) (Fin 2) ℂ} (hX : X.PosSemidef) (htr : X.trace = 1) :
    vnEntropy X ≤ 1 := by
  rw [X4LE.vn_amp hX, Fin.sum_univ_two]
  have hs : hX.1.eigenvalues 0 + hX.1.eigenvalues 1 = 1 := by
    have := hX.1.trace_eq_sum_eigenvalues
    rw [htr, Fin.sum_univ_two] at this
    have h2 := congrArg Complex.re this
    simpa using h2.symm
  set p := hX.1.eigenvalues 0
  have h1 : hX.1.eigenvalues 1 = 1 - p := by linarith
  rw [h1]
  have hb := Real.binEntropy_le_log_two (p := p)
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have : -(p * Real.logb 2 p + (1 - p) * Real.logb 2 (1 - p)) = Real.binEntropy p / Real.log 2 := by
    simp only [Real.binEntropy, Real.log_inv, Real.logb]; field_simp; ring
  rw [this, div_le_one hl2]; exact hb

end X4ER

end

-- ===== QSQ =====

/-! Extensions of a pure multipartite state are products `ψψ† ⊗ τ`; complementary
register marginals of the pure part have equal entropy, so the total and dual
conditional informations agree on every extension. -/

noncomputable section

namespace X4QS
open Matrix QAlgorithms Real
open scoped Matrix ComplexConjugate ComplexOrder Kronecker
open QAlgorithms.Papers.Independent.Claimed50.P33

/-- `S(X ⊗ Y) = S(X) tr Y + tr X S(Y)` for PSD `X`, `Y`. -/
lemma vn_kron {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    {X : Matrix ι ι ℂ} {Y : Matrix κ κ ℂ} (hX : X.PosSemidef) (hY : Y.PosSemidef) :
    vnEntropy (X ⊗ₖ Y) = vnEntropy X * Y.trace.re + X.trace.re * vnEntropy Y := by
  set φ : ι × κ → ι × κ → ℂ := fun t p => X4LE.amp hX t.1 p.1 * X4LE.amp hY t.2 p.2
  have hdec : X ⊗ₖ Y = ∑ t, Matrix.of fun a b => φ t a * conj (φ t b) := by
    conv_lhs => rw [X4LE.amp_decomp hX, X4LE.amp_decomp hY]
    ext ⟨a1, a2⟩ ⟨b1, b2⟩
    simp only [kroneckerMap_apply, Matrix.sum_apply, Matrix.of_apply, φ, Fintype.sum_prod_type,
      Finset.sum_mul_sum, map_mul]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => by ring
  have horth : ∀ t t', t ≠ t' → ∑ p, φ t p * conj (φ t' p) = 0 := by
    intro t t' htt
    have e : ∑ p, φ t p * conj (φ t' p) =
        (∑ a, X4LE.amp hX t.1 a * conj (X4LE.amp hX t'.1 a)) *
          (∑ b, X4LE.amp hY t.2 b * conj (X4LE.amp hY t'.2 b)) := by
      simp only [φ, Fintype.sum_prod_type, Finset.sum_mul_sum, map_mul]
      refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => by ring
    rw [e, X4LE.amp_inner, X4LE.amp_inner]
    obtain ⟨t1, t2⟩ := t; obtain ⟨t1', t2'⟩ := t'
    by_cases h1 : t1 = t1'
    · have h2 : t2 ≠ t2' := fun h2 => htt (by rw [h1, h2])
      simp [h2]
    · simp [h1]
  have hnorm : ∀ t : ι × κ, ∑ p, ‖φ t p‖ ^ 2 = hX.1.eigenvalues t.1 * hY.1.eigenvalues t.2 := by
    intro t
    simp only [φ, norm_mul, mul_pow, Fintype.sum_prod_type, ← Finset.sum_mul_sum,
      X4LE.amp_norm]
  rw [hdec, X4LE.orth_ent φ horth]
  simp only [hnorm]
  rw [X4LE.vn_amp hX, X4LE.vn_amp hY, hX.1.trace_eq_sum_eigenvalues,
    hY.1.trace_eq_sum_eigenvalues]
  simp only [Complex.re_sum, Complex.ofReal_re, Fintype.sum_prod_type]
  have key : ∀ x y : ℝ, 0 ≤ x → 0 ≤ y →
      x * y * Real.logb 2 (x * y) = y * (x * Real.logb 2 x) + x * (y * Real.logb 2 y) := by
    intro x y hx hy
    rcases hx.eq_or_lt with rfl | hx'
    · simp
    rcases hy.eq_or_lt with rfl | hy'
    · simp
    rw [Real.logb_mul hx'.ne' hy'.ne']; ring
  simp only [fun j k => key _ _ (hX.eigenvalues_nonneg j) (hY.eigenvalues_nonneg k),
    Finset.sum_add_distrib, neg_mul, ← Finset.sum_mul, ← Finset.mul_sum, Finset.sum_neg_distrib]
  have e1 : ∀ x : ℝ, (RCLike.ofReal x : ℂ).re = x := fun x => rfl
  simp only [e1]
  ring

variable {m : ℕ} {D : Fin m → Type} [∀ i, Fintype (D i)]

/-- glue an assignment on `s` with one on its complement `u`. -/
def merge {s u : Finset (Fin m)} (h : ∀ i, i ∈ u ↔ i ∉ s) (a : SubBasis D s) (z : SubBasis D u) :
    RegisterBasis D :=
  fun i => if hi : i ∈ s then a ⟨i, hi⟩ else z ⟨i, (h i).2 hi⟩

lemma merge_comm {s u : Finset (Fin m)} (h : ∀ i, i ∈ u ↔ i ∉ s) (h' : ∀ i, i ∈ s ↔ i ∉ u)
    (a : SubBasis D s) (z : SubBasis D u) : merge h' z a = merge h a z := by
  funext i
  simp only [merge]
  by_cases hs : i ∈ s
  · have hu : i ∉ u := (h' i).1 hs
    simp [hs, hu]
  · have hu : i ∈ u := (h i).2 hs
    simp [hs, hu]

lemma sum_marg {M : Type*} [AddCommMonoid M] {s u : Finset (Fin m)} (h : ∀ i, i ∈ u ↔ i ∉ s)
    (a b : SubBasis D s) (F : RegisterBasis D → RegisterBasis D → M) (P : RegisterBasis D → RegisterBasis D → Prop)
    {inst : ∀ x y, Decidable (P x y)}
    (hP : ∀ x y, P x y ↔ ((∀ i (hi : i ∈ s), x i = a ⟨i,hi⟩ ∧ y i = b ⟨i,hi⟩) ∧ (∀ i, i ∉ s → x i = y i))) :
    ∑ x, ∑ y, (if P x y then F x y else 0) = ∑ z : SubBasis D u, F (merge h a z) (merge h b z) := by
  classical
  let r : RegisterBasis D → SubBasis D u := fun x i => x i.1
  have inner : ∀ x, ∑ y, (if P x y then F x y else 0) =
      if (∀ i (hi : i ∈ s), x i = a ⟨i,hi⟩) then F x (merge h b (r x)) else 0 := by
    intro x
    have hc : ∀ y, P x y ↔ ((∀ i (hi : i ∈ s), x i = a ⟨i,hi⟩) ∧ y = merge h b (r x)) := by
      intro y
      rw [hP]
      constructor
      · rintro ⟨h1, h2⟩
        refine ⟨fun i hi => (h1 i hi).1, ?_⟩
        funext i
        simp only [merge, r]
        split_ifs with hi
        · exact (h1 i hi).2
        · exact (h2 i hi).symm
      · rintro ⟨h1, rfl⟩
        refine ⟨fun i hi => ⟨h1 i hi, by simp [merge, hi]⟩, fun i hi => by simp [merge, hi, r]⟩
    rw [Finset.sum_congr rfl fun y _ => if_congr (hc y) rfl rfl]
    by_cases hx : ∀ i (hi : i ∈ s), x i = a ⟨i,hi⟩
    · rw [if_pos hx, Finset.sum_congr rfl fun y _ => if_congr (and_iff_right hx) rfl rfl]
      simp
    · rw [if_neg hx]; exact Finset.sum_eq_zero fun y _ => if_neg (fun h => hx h.1)
  simp only [inner]
  rw [← Finset.sum_filter]
  refine Finset.sum_nbij' r (merge h a) ?_ ?_ ?_ ?_ ?_
  · intros; exact Finset.mem_univ _
  · intro z _
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    intro i hi; simp [merge, hi]
  · intro x hx
    replace hx := (Finset.mem_filter.1 (Finset.mem_coe.1 hx)).2
    funext i
    simp only [merge, r]
    split_ifs with hi
    · exact (hx i hi).symm
    · rfl
  · intro z _
    funext i
    have hi : i.1 ∉ s := (h i.1).1 i.2
    simp [r, merge, hi]
  · intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
    congr 1
    funext i
    simp only [merge, r]
    split_ifs with hi
    · exact hx i hi
    · rfl

/-- the reshaped pure amplitudes. -/
def P (ψ : RegisterBasis D → ℂ) {s u : Finset (Fin m)} (h : ∀ i, i ∈ u ↔ i ∉ s) :
    Matrix (SubBasis D s) (SubBasis D u) ℂ := Matrix.of fun a z => ψ (merge h a z)

/-- every extension of a pure state is a product. -/
lemma ext_prod {I E : Type} [Fintype I] [DecidableEq I] [Fintype E] [DecidableEq E]
    (ψ : EuclideanSpace ℂ I) (hψ : ‖ψ‖ = 1)
    (σ : Matrix (I × E) (I × E) ℂ) (hσ : σ.PosSemidef) (hf : forgetEnvironment σ = pureDensity ψ) :
    ∃ τ : Matrix E E ℂ, τ.PosSemidef ∧ ∀ x f y g, σ (x, f) (y, g) = ψ x * conj (ψ y) * τ f g := by
  have hv := X4ZE.unit_sum ψ hψ
  have hsplit0 : ∀ (kf : (I × E) × E) (a : I), X4LE.amp hσ kf.1 (a, kf.2) =
      (∑ b, conj (ψ b) * X4LE.amp hσ kf.1 (b, kf.2)) * ψ a := by
    intro kf
    refine X4ZE.rank1_split (fun a => ψ a) hv (fun kf a => X4LE.amp hσ kf.1 (a, kf.2)) ?_ kf
    intro a b
    have := congrFun (congrFun hf a) b
    simp only [forgetEnvironment, pureDensity, Matrix.of_apply] at this
    rw [← this]
    conv_lhs => enter [2, e]; rw [X4LE.amp_decomp hσ]
    simp only [Matrix.sum_apply, Matrix.of_apply, Fintype.sum_prod_type]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_comm
  have hsplit : ∀ k f a, X4LE.amp hσ k (a, f) =
      (∑ b, conj (ψ b) * X4LE.amp hσ k (b, f)) * ψ a := fun k f a => hsplit0 (k, f) a
  set α : (I × E) → E → ℂ := fun k f => ∑ b, conj (ψ b) * X4LE.amp hσ k (b, f)
  refine ⟨Matrix.of fun f g => ∑ k, α k f * conj (α k g), ?_, ?_⟩
  · have : (Matrix.of fun f g => ∑ k, α k f * conj (α k g)) =
        (Matrix.of fun f k => α k f) * (Matrix.of fun f k => α k f)ᴴ := by
      ext f g; simp [Matrix.mul_apply, conjTranspose_apply]
    rw [this]; exact posSemidef_self_mul_conjTranspose _
  · intro x f y g
    conv_lhs => rw [X4LE.amp_decomp hσ]
    simp only [Matrix.sum_apply, Matrix.of_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hsplit k f x, hsplit k g y]
    simp only [map_mul, α]; ring

lemma marg_eq {e : Type} [Fintype e] (ψ : RegisterBasis D → ℂ) (τ : Matrix e e ℂ)
    (σ : Matrix (RegisterBasis D × e) (RegisterBasis D × e) ℂ)
    (hprod : ∀ x f y g, σ (x, f) (y, g) = ψ x * conj (ψ y) * τ f g)
    {s u : Finset (Fin m)} (h : ∀ i, i ∈ u ↔ i ∉ s) :
    registerMarginal σ s = (P ψ h * (P ψ h)ᴴ) ⊗ₖ τ := by
  ext ⟨a, f⟩ ⟨b, g⟩
  simp only [registerMarginal]
  refine (sum_marg h a b (fun x y => σ (x, f) (y, g)) _ (fun x y => Iff.rfl)).trans ?_
  simp only [hprod, kroneckerMap_apply, Matrix.mul_apply, conjTranspose_apply, P, Matrix.of_apply,
    RCLike.star_def, Finset.sum_mul]

open Classical in
lemma ent_eq {e : Type} [Fintype e] [DecidableEq e] (ψ : RegisterBasis D → ℂ) (τ : Matrix e e ℂ)
    (hτ : τ.PosSemidef)
    (σ : Matrix (RegisterBasis D × e) (RegisterBasis D × e) ℂ)
    (hprod : ∀ x f y g, σ (x, f) (y, g) = ψ x * conj (ψ y) * τ f g)
    {s u : Finset (Fin m)} (h : ∀ i, i ∈ u ↔ i ∉ s) :
    entropyAt σ s = vnEntropy (P ψ h * (P ψ h)ᴴ) * τ.trace.re +
      (P ψ h * (P ψ h)ᴴ).trace.re * vnEntropy τ := by
  classical
  unfold entropyAt
  rw [marg_eq ψ τ σ hprod h]
  convert vn_kron (posSemidef_self_mul_conjTranspose (P ψ h)) hτ

lemma swapP (ψ : RegisterBasis D → ℂ) {s u : Finset (Fin m)} (h : ∀ i, i ∈ u ↔ i ∉ s)
    (h' : ∀ i, i ∈ s ↔ i ∉ u) : P ψ h' = (P ψ h)ᵀ := by
  ext z a; simp [P, merge_comm h h']

open Classical in
lemma ent_compl {e : Type} [Fintype e] [DecidableEq e] (ψ : RegisterBasis D → ℂ) (τ : Matrix e e ℂ)
    (hτ : τ.PosSemidef)
    (σ : Matrix (RegisterBasis D × e) (RegisterBasis D × e) ℂ)
    (hprod : ∀ x f y g, σ (x, f) (y, g) = ψ x * conj (ψ y) * τ f g) (s : Finset (Fin m)) :
    entropyAt σ s = entropyAt σ sᶜ := by
  classical
  have h : ∀ i, i ∈ sᶜ ↔ i ∉ s := fun i => Finset.mem_compl
  have h' : ∀ i, i ∈ s ↔ i ∉ sᶜ := fun i => by simp
  rw [ent_eq ψ τ hτ σ hprod h, ent_eq ψ τ hτ σ hprod h', swapP ψ h h']
  have hG : (P ψ h)ᵀ * ((P ψ h)ᵀ)ᴴ = ((P ψ h)ᴴ * P ψ h)ᵀ := by
    ext z z'; simp [Matrix.mul_apply, conjTranspose_apply, mul_comm]
  rw [hG, ← X4KF.x4_ent_swap, Matrix.trace_transpose, Matrix.trace_mul_comm]

section
attribute [local instance] Classical.propDecidable Classical.decEq

theorem key (hm : 2 ≤ m) [∀ i, Nonempty (D i)] (ψ : EuclideanSpace ℂ (RegisterBasis D)) (hψ : ‖ψ‖ = 1)
    {e : ℕ} (σ : Matrix (RegisterBasis D × Fin e) (RegisterBasis D × Fin e) ℂ)
    (hσ : IsDensityMatrix σ) (hf : forgetEnvironment σ = pureDensity ψ) :
    conditionalMultipartiteInformation .total σ (singleParties m) ∅ =
      conditionalMultipartiteInformation .dual σ (singleParties m) ∅ := by
  classical
  obtain ⟨τ, hτ, hprod⟩ := ext_prod ψ hψ σ hσ.1 hf
  have hE := ent_compl (fun x => ψ x) τ hτ σ hprod
  have h1 : ∀ i : Fin m, (Finset.univ.erase i).biUnion (singleParties m) = {i}ᶜ := by
    intro i; ext j; simp [singleParties, eq_comm]
  have h2 : allParties (singleParties m) = (∅ : Finset (Fin m))ᶜ := by
    ext j; simp [allParties, singleParties]
  simp only [conditionalMultipartiteInformation, Finset.union_empty, h1, h2]
  simp only [singleParties]
  rw [← hE ∅, Finset.sum_congr rfl fun i _ => (hE {i}).symm]
  ring

end

end X4QS

end

-- ===== ERB =====

/-! Qubit erasure on one pure input with an arbitrary reference: closed forms for the output,
its marginals and their entropies. -/

noncomputable section

namespace X4EB
open Matrix Real QAlgorithms
open scoped Matrix ComplexConjugate ComplexOrder Kronecker
open QAlgorithms.Papers.Independent.Dependency50.P41 (qubitErasure)

attribute [local instance] Classical.propDecidable Classical.decEq

variable {r : ℕ}

lemma pd_psd {ι : Type*} [Fintype ι] (v : EuclideanSpace ℂ ι) : (pureDensity v).PosSemidef := by
  have : pureDensity v = vecMulVec (WithLp.ofLp v) (star (WithLp.ofLp v)) := by
    ext a b; simp [pureDensity, vecMulVec_apply]
  rw [this]; exact Matrix.posSemidef_vecMulVec_self_star _

/-- embedded input amplitudes. -/
def phi (ψ : EuclideanSpace ℂ (Fin r × Fin 2)) : EuclideanSpace ℂ (Fin r × Fin 3) :=
  WithLp.toLp 2 fun p => if h : p.2.val < 2 then ψ (p.1, ⟨p.2.val, h⟩) else 0

/-- the reference marginal. -/
def rhoR (ψ : EuclideanSpace ℂ (Fin r × Fin 2)) : Matrix (Fin r) (Fin r) ℂ :=
  traceRight (pureDensity ψ)

/-- the flag projector `|2⟩⟨2|`. -/
def e2 : Matrix (Fin 3) (Fin 3) ℂ := pureDensity (EuclideanSpace.single (2 : Fin 3) (1 : ℂ))

/-- embedding `Fin 2 → Fin 3`. -/
def J : Matrix (Fin 3) (Fin 2) ℂ := Matrix.of fun x a => if x.val = a.val then 1 else 0

lemma J_iso : Jᴴ * J = 1 := by
  ext a b; fin_cases a <;> fin_cases b <;> simp [J, Matrix.mul_apply, Fin.sum_univ_three]

lemma out_apply (ε : ℝ) (ψ : EuclideanSpace ℂ (Fin r × Fin 2)) (i j : Fin r) (x y : Fin 3) :
    idTensorSuperop (qubitErasure ε) (pureDensity ψ) (i, x) (j, y) =
      (1 - ε : ℂ) * phi ψ (i, x) * conj (phi ψ (j, y)) +
        (if x = 2 ∧ y = 2 then (ε : ℂ) * rhoR ψ i j else 0) := by
  fin_cases x <;> fin_cases y <;>
    simp [idTensorSuperop, qubitErasure,
      QAlgorithms.Papers.Independent.Information100.P58.singleErasure, phi, rhoR, traceRight,
      pureDensity, Matrix.trace, Fin.sum_univ_two] <;> ring

lemma out_eq (ε : ℝ) (ψ : EuclideanSpace ℂ (Fin r × Fin 2)) :
    idTensorSuperop (qubitErasure ε) (pureDensity ψ) =
      ((1 - ε : ℝ) : ℂ) • pureDensity (phi ψ) + (ε : ℂ) • (rhoR ψ ⊗ₖ e2) := by
  ext ⟨i, x⟩ ⟨j, y⟩
  rw [out_apply]
  fin_cases x <;> fin_cases y <;> simp [pureDensity, e2, kroneckerMap_apply, mul_assoc]

lemma rhoR_psd (ψ : EuclideanSpace ℂ (Fin r × Fin 2)) : (rhoR ψ).PosSemidef := by
  have : rhoR ψ = (Matrix.of fun i a => ψ (i, a)) * (Matrix.of fun i a => ψ (i, a))ᴴ := by
    ext i j; simp [rhoR, traceRight, pureDensity, Matrix.mul_apply, conjTranspose_apply]
  rw [this]; exact posSemidef_self_mul_conjTranspose _

lemma rhoR_trace (ψ : EuclideanSpace ℂ (Fin r × Fin 2)) (hψ : ‖ψ‖ = 1) : (rhoR ψ).trace = 1 := by
  have h := X4ZE.unit_sum ψ hψ
  rw [← h]
  simp [rhoR, traceRight, pureDensity, Matrix.trace, Fintype.sum_prod_type]

lemma phi_norm (ψ : EuclideanSpace ℂ (Fin r × Fin 2)) (hψ : ‖ψ‖ = 1) : ‖phi ψ‖ = 1 := by
  have h : ‖phi ψ‖ ^ 2 = ‖ψ‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type,
      Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [phi, Fin.sum_univ_three, Fin.sum_univ_two]
  rw [hψ, one_pow] at h
  have := norm_nonneg (phi ψ)
  nlinarith

lemma e2_psd : e2.PosSemidef := pd_psd _

/-- binary entropy (bits) written with `logb`. -/
def hb (ε : ℝ) : ℝ := -((1 - ε) * Real.logb 2 (1 - ε)) - ε * Real.logb 2 ε

lemma smul_psd {ι : Type*} [Fintype ι] {X : Matrix ι ι ℂ} (hX : X.PosSemidef) {c : ℝ} (hc : 0 ≤ c) :
    ((c : ℂ) • X).PosSemidef := hX.smul (by exact_mod_cast hc)

lemma pd_trace {ι : Type} [Fintype ι] (v : EuclideanSpace ℂ ι) (hv : ‖v‖ = 1) :
    (pureDensity v).trace = 1 := by
  rw [← X4ZE.unit_sum v hv]; simp [pureDensity, Matrix.trace]

lemma e2_trace : e2.trace = 1 := pd_trace _ (by simp)

lemma e2_ent : vnEntropy e2 = 0 := X4ER.vn_pure _ (by simp)

lemma ent_out (ε : ℝ) (h0 : 0 ≤ ε) (h1 : ε ≤ 1) (ψ : EuclideanSpace ℂ (Fin r × Fin 2)) (hψ : ‖ψ‖ = 1) :
    vnEntropy (idTensorSuperop (qubitErasure ε) (pureDensity ψ)) = hb ε + ε * vnEntropy (rhoR ψ) := by
  rw [out_eq]
  have hA := pd_psd (phi ψ)
  have hB : (rhoR ψ ⊗ₖ e2).PosSemidef := (rhoR_psd ψ).kronecker e2_psd
  have hAB : pureDensity (phi ψ) * (rhoR ψ ⊗ₖ e2) = 0 := by
    ext ⟨i, x⟩ ⟨j, y⟩
    simp [Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_three, e2, pureDensity, phi,
      kroneckerMap_apply]
  rw [X4ER.vn_add_orth (smul_psd hA (by linarith)) (smul_psd hB h0)
    (by rw [Matrix.smul_mul, Matrix.mul_smul, hAB, smul_zero, smul_zero]),
    X4ER.vn_smul0 hA.1 (by linarith), X4ER.vn_smul0 hB.1 h0, X4ER.vn_pure _ (phi_norm ψ hψ),
    pd_trace _ (phi_norm ψ hψ), X4QS.vn_kron (rhoR_psd ψ) e2_psd, e2_ent, e2_trace, Matrix.trace_kronecker,
    rhoR_trace ψ hψ, e2_trace]
  simp [hb]; ring

lemma tl_out (ε : ℝ) (ψ : EuclideanSpace ℂ (Fin r × Fin 2)) (hψ : ‖ψ‖ = 1) :
    traceLeft (idTensorSuperop (qubitErasure ε) (pureDensity ψ)) =
      ((1 - ε : ℝ) : ℂ) • (J * traceLeft (pureDensity ψ) * Jᴴ) + (ε : ℂ) • e2 := by
  have htr' : ∑ i, rhoR ψ i i = 1 := rhoR_trace ψ hψ
  ext x y
  simp only [traceLeft, Matrix.of_apply, out_apply]
  fin_cases x <;> fin_cases y <;>
    simp [phi, J, e2, pureDensity, Matrix.mul_apply, Fin.sum_univ_two, Fin.sum_univ_three,
      conjTranspose_apply, Finset.sum_add_distrib] <;>
    (try rw [← Finset.mul_sum, htr', mul_one]) <;> simp [Finset.mul_sum] <;> ring_nf

lemma tr_out (ε : ℝ) (ψ : EuclideanSpace ℂ (Fin r × Fin 2)) :
    traceRight (idTensorSuperop (qubitErasure ε) (pureDensity ψ)) = rhoR ψ := by
  ext i j
  simp only [traceRight, Matrix.of_apply, out_apply, Fin.sum_univ_three]
  simp [phi, rhoR, traceRight, pureDensity, Fin.sum_univ_two]
  ring

lemma ent_RA (ψ : EuclideanSpace ℂ (Fin r × Fin 2)) :
    vnEntropy (rhoR ψ) = vnEntropy (traceLeft (pureDensity ψ)) := by
  set M : Matrix (Fin r) (Fin 2) ℂ := Matrix.of fun i a => ψ (i, a)
  have e1 : rhoR ψ = M * Mᴴ := by
    ext; simp [rhoR, traceRight, pureDensity, M, Matrix.mul_apply, conjTranspose_apply]
  have e2' : traceLeft (pureDensity ψ) = (Mᴴ * M)ᵀ := by
    ext; simp [traceLeft, pureDensity, M, Matrix.mul_apply, conjTranspose_apply, mul_comm]
  rw [e1, e2', X4KF.x4_ent_swap]

lemma ent_flag (ε : ℝ) (h0 : 0 ≤ ε) (h1 : ε ≤ 1) {Z : Matrix (Fin 2) (Fin 2) ℂ} (hZ : Z.PosSemidef)
    (htr : Z.trace = 1) :
    vnEntropy (((1 - ε : ℝ) : ℂ) • (J * Z * Jᴴ) + (ε : ℂ) • e2) = (1 - ε) * vnEntropy Z + hb ε := by
  have hA : (J * Z * Jᴴ).PosSemidef := hZ.mul_mul_conjTranspose_same J
  have hAB : J * Z * Jᴴ * e2 = 0 := by
    ext x y
    fin_cases x <;> fin_cases y <;>
      simp [Matrix.mul_apply, Fin.sum_univ_three, Fin.sum_univ_two, J, e2, pureDensity,
        conjTranspose_apply]
  have htrA : (J * Z * Jᴴ).trace = 1 := by
    rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, J_iso, Matrix.one_mul, htr]
  rw [X4ER.vn_add_orth (smul_psd hA (by linarith)) (smul_psd e2_psd h0)
    (by rw [Matrix.smul_mul, Matrix.mul_smul, hAB, smul_zero, smul_zero]),
    X4ER.vn_smul0 hA.1 (by linarith), X4ER.vn_smul0 e2_psd.1 h0, X4ER.vn_conj_iso hZ J J_iso,
    e2_ent, htrA, e2_trace]
  simp [hb]; ring

end X4EB

end

-- ===== ERC =====

/-! The dynamic score of the qubit erasure channel on an arbitrary pure ensemble:
`(1+μ)(1-ε) S(Z̄) + coeff · Σ p_x S(Z_x)`. -/

noncomputable section

namespace X4EC
open Matrix Real QAlgorithms X4EB
open scoped Matrix ComplexConjugate ComplexOrder Kronecker
open QAlgorithms.Papers.Independent.Claimed50.P20
open QAlgorithms.Papers.Independent.Dependency50.P41 (qubitErasure)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- input marginals. -/
def Z (e : DynamicPureEnsemble (Fin 2)) (x : Fin e.ensemble.size) : Matrix (Fin 2) (Fin 2) ℂ :=
  traceLeft (pureDensity (e.ensemble.vector x))

/-- average input marginal. -/
def Zbar (e : DynamicPureEnsemble (Fin 2)) : Matrix (Fin 2) (Fin 2) ℂ :=
  ∑ x, e.ensemble.prob x • Z e x

lemma Z_psd (e : DynamicPureEnsemble (Fin 2)) (x : Fin e.ensemble.size) : (Z e x).PosSemidef := by
  have : Z e x = (Matrix.of fun a i => (e.ensemble.vector x) (i, a)) *
      (Matrix.of fun a i => (e.ensemble.vector x) (i, a))ᴴ := by
    ext a b; simp [Z, traceLeft, pureDensity, Matrix.mul_apply, conjTranspose_apply]
  rw [this]; exact posSemidef_self_mul_conjTranspose _

lemma Z_trace (e : DynamicPureEnsemble (Fin 2)) (x : Fin e.ensemble.size) : (Z e x).trace = 1 := by
  rw [Z, X4LE.tl_trace, e.ensemble.normalized x]; simp

lemma Zbar_psd (e : DynamicPureEnsemble (Fin 2)) : (Zbar e).PosSemidef := by
  refine posSemidef_sum _ fun x _ => ?_
  rw [← Complex.coe_smul]; exact smul_psd (Z_psd e x) (e.ensemble.nonneg x)

lemma Zbar_trace (e : DynamicPureEnsemble (Fin 2)) : (Zbar e).trace = 1 := by
  rw [Zbar, Matrix.trace_sum]
  simp only [Matrix.trace_smul, Z_trace]
  have := e.ensemble.total
  rw [← Complex.ofReal_inj] at this
  push_cast at this
  simpa [Complex.real_smul] using this

lemma avg (ε : ℝ) (e : DynamicPureEnsemble (Fin 2)) :
    ∑ x, e.ensemble.prob x • traceLeft (pureOutputs (qubitErasure ε) e x) =
      ((1 - ε : ℝ) : ℂ) • (X4EB.J * Zbar e * X4EB.Jᴴ) + (ε : ℂ) • X4EB.e2 := by
  simp only [pureOutputs]
  rw [Finset.sum_congr rfl fun x _ => by
    rw [tl_out ε _ (e.ensemble.normalized x)]]
  simp only [smul_add, Finset.sum_add_distrib]
  congr 1
  · rw [Zbar, Matrix.mul_sum, Matrix.sum_mul, Finset.smul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Matrix.mul_smul, Matrix.smul_mul, smul_comm]; rfl
  · rw [← Finset.sum_smul, e.ensemble.total, one_smul]

theorem score (ε lam mu : ℝ) (h0 : 0 ≤ ε) (h1 : ε ≤ 1) (e : DynamicPureEnsemble (Fin 2)) :
    dynamicScore (qubitErasure ε) lam mu e =
      (1 + mu) * (1 - ε) * vnEntropy (Zbar e) +
        erasureCoefficient ε lam mu * ∑ x, e.ensemble.prob x * vnEntropy (Z e x) := by
  have hA : vnEntropy (∑ x, e.ensemble.prob x • traceLeft (pureOutputs (qubitErasure ε) e x)) =
      (1 - ε) * vnEntropy (Zbar e) + hb ε := by
    rw [avg, ent_flag ε h0 h1 (Zbar_psd e) (Zbar_trace e)]
  have hL : ∀ x, vnEntropy (traceLeft (pureOutputs (qubitErasure ε) e x)) =
      (1 - ε) * vnEntropy (Z e x) + hb ε := by
    intro x
    rw [pureOutputs, tl_out ε _ (e.ensemble.normalized x)]
    exact ent_flag ε h0 h1 (Z_psd e x) (Z_trace e x)
  have hR : ∀ x, vnEntropy (traceRight (pureOutputs (qubitErasure ε) e x)) = vnEntropy (Z e x) := by
    intro x; rw [pureOutputs, tr_out, ent_RA]; rfl
  have hO : ∀ x, vnEntropy (pureOutputs (qubitErasure ε) e x) = hb ε + ε * vnEntropy (Z e x) := by
    intro x; rw [pureOutputs, ent_out ε h0 h1 _ (e.ensemble.normalized x), ent_RA]; rfl
  have htot := e.ensemble.total
  simp only [dynamicScore, bounds, jointMutual, conditionalCoherent, cqHolevoBits,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons, hA, hL, hR, hO, erasureCoefficient]
  set S := ∑ x, e.ensemble.prob x * vnEntropy (Z e x)
  have e1 : ∑ x, e.ensemble.prob x * (vnEntropy (Z e x) - (hb ε + ε * vnEntropy (Z e x))) =
      (1 - ε) * S - hb ε := by
    rw [show (∑ x, e.ensemble.prob x * (vnEntropy (Z e x) - (hb ε + ε * vnEntropy (Z e x)))) =
        (1 - ε) * S - hb ε * ∑ x, e.ensemble.prob x by
      simp only [S, Finset.mul_sum, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun x _ => by ring, htot, mul_one]
  have f2 : ∑ x, e.ensemble.prob x * ((1 - ε) * vnEntropy (Z e x) + hb ε - (hb ε + ε * vnEntropy (Z e x))) =
      (1 - 2 * ε) * S := by
    simp only [S, Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => by ring
  have e3 : ∑ x, e.ensemble.prob x * ((1 - ε) * vnEntropy (Z e x) + hb ε) = (1 - ε) * S + hb ε := by
    rw [show (∑ x, e.ensemble.prob x * ((1 - ε) * vnEntropy (Z e x) + hb ε)) =
        (1 - ε) * S + hb ε * ∑ x, e.ensemble.prob x by
      simp only [S, Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun x _ => by ring, htot, mul_one]
  rw [e1, f2, e3]
  ring

end X4EC

end

-- ===== ERD =====

noncomputable section

open Matrix Real QAlgorithms X4EB X4EC
open scoped Matrix ComplexConjugate ComplexOrder
open QAlgorithms.Papers.Independent.Claimed50.P20
open QAlgorithms.Papers.Independent.Dependency50.P41 (qubitErasure)

attribute [local instance] Classical.propDecidable Classical.decEq

namespace X4ES

lemma ent_nonneg {ι : Type} [Fintype ι] [DecidableEq ι] {X : Matrix ι ι ℂ} (hX : X.PosSemidef)
    (htr : X.trace = 1) : 0 ≤ vnEntropy X := by
  rw [X4LE.vn_amp hX, neg_nonneg]
  have hs : ∑ k, hX.1.eigenvalues k = 1 := by
    have := hX.1.trace_eq_sum_eigenvalues
    rw [htr] at this
    have h2 := congrArg Complex.re this
    simpa using h2.symm
  refine Finset.sum_nonpos fun k _ => ?_
  have h0 := hX.eigenvalues_nonneg k
  have h1 : hX.1.eigenvalues k ≤ 1 := by
    rw [← hs]
    exact Finset.single_le_sum (fun j _ => hX.eigenvalues_nonneg j) (Finset.mem_univ k)
  exact mul_nonpos_of_nonneg_of_nonpos h0 (Real.logb_nonpos (by norm_num) h0 h1)

/-- the classical witness ensemble `{|0⟩, |1⟩}` with weights `1/2`. -/
def wit : DynamicPureEnsemble (Fin 2) where
  referenceDim := 1
  referencePositive := Nat.one_pos
  ensemble :=
    { size := 2
      prob := fun _ => 1 / 2
      vector := fun x => EuclideanSpace.single ((0 : Fin 1), (⟨x.val, x.isLt⟩ : Fin 2)) 1
      nonneg := fun _ => by norm_num
      total := by norm_num
      normalized := fun _ => by simp }

lemma wit_Z (x : Fin wit.ensemble.size) :
    Z wit x = diagonal fun b => ((if b.val = x.val then 1 else 0 : ℝ) : ℂ) := by
  obtain ⟨xv, hx⟩ := x
  change xv < 2 at hx
  ext a b
  interval_cases xv <;> fin_cases a <;> fin_cases b <;>
    simp [Z, traceLeft, pureDensity, wit, PiLp.single_apply, diagonal] <;>
    erw [Fin.sum_univ_one] <;> (try simp) <;> erw [Matrix.of_apply] <;> simp

lemma wit_ent (x : Fin wit.ensemble.size) : vnEntropy (Z wit x) = 0 := by
  rw [wit_Z, X4LE.vn_diag]
  simp only [Fin.sum_univ_two]
  split_ifs <;> simp

lemma wit_bar : vnEntropy (Zbar wit) = 1 := by
  have : Zbar wit = diagonal fun _ => ((1 / 2 : ℝ) : ℂ) := by
    simp only [Zbar, wit_Z]
    ext a b
    fin_cases a <;> fin_cases b <;>
      simp [Matrix.sum_apply, diagonal, wit] <;> erw [Fin.sum_univ_two] <;> norm_num
  rw [this, X4LE.vn_diag, Fin.sum_univ_two]
  rw [show (1 / 2 : ℝ) = 2⁻¹ by norm_num, Real.logb_inv, Real.logb_self_eq_one (by norm_num)]
  ring

lemma wit_score (ε lam mu : ℝ) (h0 : 0 ≤ ε) (h1 : ε ≤ 1) :
    dynamicScore (qubitErasure ε) lam mu wit = (1 + mu) * (1 - ε) := by
  rw [score ε lam mu h0 h1, wit_bar]
  simp [wit_ent]

lemma score_le (ε lam mu : ℝ) (h0 : 0 ≤ ε) (h1 : ε ≤ 1) (hmu : 0 ≤ mu)
    (hc : erasureCoefficient ε lam mu ≤ 0) (e : DynamicPureEnsemble (Fin 2)) :
    dynamicScore (qubitErasure ε) lam mu e ≤ (1 + mu) * (1 - ε) := by
  rw [score ε lam mu h0 h1]
  have hS := X4ER.qubit_le (Zbar_psd e) (Zbar_trace e)
  have hT : 0 ≤ ∑ x, e.ensemble.prob x * vnEntropy (Z e x) :=
    Finset.sum_nonneg fun x _ => mul_nonneg (e.ensemble.nonneg x) (ent_nonneg (Z_psd e x) (Z_trace e x))
  have hk : 0 ≤ (1 + mu) * (1 - ε) := mul_nonneg (by linarith) (by linarith)
  nlinarith [mul_nonpos_of_nonpos_of_nonneg hc hT]

lemma escore (ε lam mu p : ℝ) :
    erasureScore ε lam mu p = (1 + mu) * (1 - ε) + erasureCoefficient ε lam mu * binEntropy2 p := by
  simp [erasureScore, erasureBounds, erasureCoefficient]; ring

lemma bin_bounds (p : ℝ) (h0 : 0 ≤ p) (h1 : p ≤ 1 / 2) : 0 ≤ binEntropy2 p ∧ binEntropy2 p ≤ 1 := by
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨div_nonneg (Real.binEntropy_nonneg h0 (by linarith)) hl2.le, ?_⟩
  rw [binEntropy2, div_le_one hl2]; exact Real.binEntropy_le_log_two

lemma bin_half : binEntropy2 (1 / 2) = 1 := by
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  rw [binEntropy2, one_div, Real.binEntropy_two_inv, div_self hl2.ne']

lemma bin_zero : binEntropy2 0 = 0 := by simp [binEntropy2]

end X4ES


end

-- ===== EDA =====

/-! Two uses of the qubit erasure channel with an arbitrary reference: block decomposition
of `id_R ⊗ (N ⊗ N)` and the resulting entropy formula. -/

noncomputable section

namespace X4ED
open Matrix Real QAlgorithms X7Y10EH
open scoped Matrix ComplexConjugate ComplexOrder
open QAlgorithms.Papers.Independent.Dependency50.P41 (qubitErasure)
open QAlgorithms.Papers.Independent.Information100.P62 (tensorChannel)

abbrev T2 (ε : ℝ) := tensorChannel (qubitErasure ε) (qubitErasure ε)

def eB (R : Type*) : R × (Fin 3 × Fin 3) ≃ ((R × Fin 2) × Fin 3) ⊕ (R × Fin 3) :=
  (Equiv.prodCongr (Equiv.refl R) X7_e2).trans ((Equiv.prodSumDistrib R _ _).trans
    (Equiv.sumCongr (Equiv.prodAssoc R (Fin 2) (Fin 3)).symm (Equiv.refl _)))

def eM (R : Type*) : Fin 2 × (R × Fin 2) ≃ R × (Fin 2 × Fin 2) where
  toFun p := (p.2.1, (p.1, p.2.2))
  invFun q := (q.2.1, (q.1, q.2.2))
  left_inv _ := rfl
  right_inv _ := rfl

variable {R : Type*} [Fintype R]

def sA (σ : Matrix (R × (Fin 2 × Fin 2)) (R × (Fin 2 × Fin 2)) ℂ) :
    Matrix ((R × Fin 2) × Fin 2) ((R × Fin 2) × Fin 2) ℂ :=
  σ.submatrix (Equiv.prodAssoc R (Fin 2) (Fin 2)) (Equiv.prodAssoc R (Fin 2) (Fin 2))

def sM (σ : Matrix (R × (Fin 2 × Fin 2)) (R × (Fin 2 × Fin 2)) ℂ) : Matrix (R × Fin 2) (R × Fin 2) ℂ :=
  traceLeft (σ.submatrix (eM R) (eM R))

lemma blk (ε : ℝ) (σ : Matrix (R × (Fin 2 × Fin 2)) (R × (Fin 2 × Fin 2)) ℂ) :
    idTensorSuperop (R := R) (T2 ε) σ =
      (fromBlocks (((1 - ε : ℝ) : ℂ) • idTensorSuperop (R := R × Fin 2) (qubitErasure ε) (sA σ)) 0 0
        (((ε : ℝ) : ℂ) • idTensorSuperop (R := R) (qubitErasure ε) (sM σ))).submatrix (eB R) (eB R) := by
  ext ⟨r, a, b⟩ ⟨r', a', b'⟩
  have hM : (Matrix.of fun k l => (sM σ) (r, k) (r', l)) =
      Matrix.of (fun k l => σ (r, (0, k)) (r', (0, l))) + Matrix.of (fun k l => σ (r, (1, k)) (r', (1, l))) := by
    ext k l; simp [sM, traceLeft, eM, Fin.sum_univ_two]
  simp only [idTensorSuperop, Matrix.of_apply, T2]
  rw [X7_T_entry]
  fin_cases a <;> fin_cases a' <;>
    simp [X7_N_single, eB, X7_e2, X7_e3, Fin.sum_univ_two, sA, hM] <;>
    (rw [← mul_add, ← Matrix.add_apply, ← X7_N_add]; rfl)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- the binary entropy of the erasure flag. -/
def hf (ε : ℝ) : ℝ := -(ε * Real.logb 2 ε) - (1 - ε) * Real.logb 2 (1 - ε)

lemma sA_dens {σ : Matrix (R × (Fin 2 × Fin 2)) (R × (Fin 2 × Fin 2)) ℂ} (h : IsDensityMatrix σ) :
    IsDensityMatrix (sA σ) :=
  ⟨h.1.submatrix _, by rw [sA, X7_trace_submatrix]; exact h.2⟩

lemma sM_dens {σ : Matrix (R × (Fin 2 × Fin 2)) (R × (Fin 2 × Fin 2)) ℂ} (h : IsDensityMatrix σ) :
    IsDensityMatrix (sM σ) :=
  X7_trL_dens _ ⟨h.1.submatrix _, by rw [X7_trace_submatrix]; exact h.2⟩

lemma trR_sM (σ : Matrix (R × (Fin 2 × Fin 2)) (R × (Fin 2 × Fin 2)) ℂ) :
    traceRight (sM σ) = traceRight σ := by
  ext i j
  simp only [traceRight, sM, traceLeft, Matrix.of_apply, Matrix.submatrix_apply, eM,
    Equiv.coe_fn_mk, Fintype.sum_prod_type]
  exact Finset.sum_comm

variable [DecidableEq R]

lemma ent (ε : ℝ) (h0 : 0 ≤ ε) (h1 : ε ≤ 1)
    (σ : Matrix (R × (Fin 2 × Fin 2)) (R × (Fin 2 × Fin 2)) ℂ) (hσ : IsDensityMatrix σ) :
    vnEntropy (idTensorSuperop (R := R) (T2 ε) σ) =
      2 * hf ε + (1 - ε) ^ 2 * vnEntropy σ +
        ε * (1 - ε) * (vnEntropy (traceRight (sA σ)) + vnEntropy (sM σ)) +
        ε ^ 2 * vnEntropy (traceRight σ) := by
  obtain ⟨hXH, hXt⟩ := X7_idT_herm_tr (R := R × Fin 2) ε _ (sA_dens hσ)
  obtain ⟨hYH, hYt⟩ := X7_idT_herm_tr (R := R) ε _ (sM_dens hσ)
  have k1 := g68i_herm_smul _ (1 - ε) (fun _ => hXH)
  have k2 := g68i_herm_smul _ ε (fun _ => hYH)
  rw [blk, X7_ent_submatrix _ _ (Matrix.IsHermitian.fromBlocks k1 (by simp) k2),
    X7_ent_fromBlocks _ _ k1 k2, g68i_ent_smul _ (1 - ε) (by linarith) (fun _ => hXH),
    g68i_ent_smul _ ε h0 (fun _ => hYH), hXt, hYt, X7_idT_entropy ε h0 h1 _ (sA_dens hσ),
    X7_idT_entropy ε h0 h1 _ (sM_dens hσ), trR_sM]
  have : vnEntropy (sA σ) = vnEntropy σ := X7_ent_submatrix _ _ hσ.1.isHermitian
  rw [this]
  simp [hf]
  ring

/-- `T2` as an `ℝ`-linear map. -/
def TL (ε : ℝ) : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ →ₗ[ℝ] Matrix (Fin 3 × Fin 3) (Fin 3 × Fin 3) ℂ where
  toFun := T2 ε
  map_add' X Y := by
    ext a b; simp [tensorChannel, add_mul, Finset.sum_add_distrib]
  map_smul' c X := by
    ext a b; simp [tensorChannel, Finset.mul_sum, mul_assoc]

lemma T2_sum (ε : ℝ) {ι : Type*} (s : Finset ι) (p : ι → ℝ) (X : ι → Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) :
    T2 ε (∑ i ∈ s, p i • X i) = ∑ i ∈ s, p i • T2 ε (X i) := by
  calc T2 ε (∑ i ∈ s, p i • X i) = TL ε (∑ i ∈ s, p i • X i) := rfl
    _ = ∑ i ∈ s, TL ε (p i • X i) := map_sum _ _ _
    _ = _ := by simp only [map_smul]; rfl

lemma trL_out (ε : ℝ) (σ : Matrix (R × (Fin 2 × Fin 2)) (R × (Fin 2 × Fin 2)) ℂ) :
    traceLeft (idTensorSuperop (R := R) (T2 ε) σ) = T2 ε (traceLeft σ) := by
  have e : traceLeft σ = ∑ r : R, (1 : ℝ) • Matrix.of fun i i' => σ (r, i) (r, i') := by
    ext i j; simp [traceLeft, Matrix.sum_apply]
  rw [e, T2_sum]
  ext a b
  simp [traceLeft, idTensorSuperop, Matrix.sum_apply]

lemma T2_trace (ε : ℝ) (X : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) : (T2 ε X).trace = X.trace := by
  simp only [Matrix.trace, Matrix.diag, T2, tensorChannel, Fintype.sum_prod_type, Fin.sum_univ_two,
    Fin.sum_univ_three, X7_N_single]
  simp
  ring

lemma trR_out (ε : ℝ) (σ : Matrix (R × (Fin 2 × Fin 2)) (R × (Fin 2 × Fin 2)) ℂ) :
    traceRight (idTensorSuperop (R := R) (T2 ε) σ) = traceRight σ := by
  ext r r'
  have := T2_trace ε (Matrix.of fun i i' => σ (r, i) (r', i'))
  simp only [Matrix.trace, Matrix.diag] at this
  simp only [traceRight, idTensorSuperop, Matrix.of_apply]
  rw [this]; rfl

end X4ED

end


-- ===== EDB =====

/-! Two-use erasure on pure inputs and the closed form of the dynamic score. -/

noncomputable section

namespace X4ED
open Matrix Real QAlgorithms X7Y10EH
open scoped Matrix ComplexConjugate ComplexOrder
open QAlgorithms.Papers.Independent.Dependency50.P41 (qubitErasure)
open QAlgorithms.Papers.Independent.Information100.P62 (tensorChannel)
open QAlgorithms.Papers.Independent.Claimed50.P20

attribute [local instance] Classical.propDecidable Classical.decEq

lemma comp {X Y : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
    (ω : Matrix (X × Y) (X × Y) ℂ) (M : Matrix X Y ℂ)
    (h : ∀ x y x' y', ω (x, y) (x', y') = M x y * conj (M x' y')) :
    vnEntropy (traceRight ω) = vnEntropy (traceLeft ω) := by
  have e1 : traceRight ω = M * Mᴴ := by
    ext; simp [traceRight, h, Matrix.mul_apply, conjTranspose_apply]
  have e2 : traceLeft ω = (Mᴴ * M)ᵀ := by
    ext; simp [traceLeft, h, Matrix.mul_apply, conjTranspose_apply, mul_comm]
  rw [e1, e2, X4KF.x4_ent_swap]

variable {r : ℕ}

lemma P1 (ψ : EuclideanSpace ℂ (Fin r × (Fin 2 × Fin 2))) :
    vnEntropy (traceRight (pureDensity ψ)) = vnEntropy (traceLeft (pureDensity ψ)) :=
  comp _ (Matrix.of fun i q => ψ (i, q)) (fun _ _ _ _ => by simp [pureDensity])

lemma P2 (ψ : EuclideanSpace ℂ (Fin r × (Fin 2 × Fin 2))) :
    vnEntropy (traceRight (sA (pureDensity ψ))) = vnEntropy (traceLeft (traceLeft (pureDensity ψ))) := by
  rw [comp _ (Matrix.of fun (p : Fin r × Fin 2) b => ψ (p.1, (p.2, b)))
    (fun _ _ _ _ => by simp [pureDensity, sA])]
  congr 1
  ext b b'
  simp [traceLeft, sA, Fintype.sum_prod_type, Fin.sum_univ_two, Finset.sum_add_distrib]

lemma P3 (ψ : EuclideanSpace ℂ (Fin r × (Fin 2 × Fin 2))) :
    vnEntropy (sM (pureDensity ψ)) = vnEntropy (traceRight (traceLeft (pureDensity ψ))) := by
  rw [sM, ← comp _ (Matrix.of fun (i : Fin 2) (p : Fin r × Fin 2) => ψ (p.1, (i, p.2)))
    (fun _ _ _ _ => by simp [pureDensity, eM])]
  congr 1
  ext a a'
  simp only [traceRight, traceLeft, Matrix.of_apply, Matrix.submatrix_apply, eM, Equiv.coe_fn_mk,
    Fintype.sum_prod_type]
  exact Finset.sum_comm

lemma pd_dens {ι : Type} [Fintype ι] (ψ : EuclideanSpace ℂ ι) (h : ‖ψ‖ = 1) :
    IsDensityMatrix (pureDensity ψ) := ⟨X4EB.pd_psd ψ, X4EB.pd_trace ψ h⟩

lemma ent_pure (ε : ℝ) (h0 : 0 ≤ ε) (h1 : ε ≤ 1) (ψ : EuclideanSpace ℂ (Fin r × (Fin 2 × Fin 2)))
    (hψ : ‖ψ‖ = 1) :
    vnEntropy (idTensorSuperop (R := Fin r) (T2 ε) (pureDensity ψ)) =
      2 * hf ε + ε * (1 - ε) * (vnEntropy (traceRight (traceLeft (pureDensity ψ))) +
        vnEntropy (traceLeft (traceLeft (pureDensity ψ)))) +
        ε ^ 2 * vnEntropy (traceLeft (pureDensity ψ)) := by
  rw [ent ε h0 h1 _ (pd_dens ψ hψ), P1, P2, P3, X4ER.vn_pure ψ hψ]
  ring

/-! The score. -/

def tau (e : DynamicPureEnsemble (Fin 2 × Fin 2)) (x : Fin e.ensemble.size) :
    Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  traceLeft (pureDensity (e.ensemble.vector x))

def taub (e : DynamicPureEnsemble (Fin 2 × Fin 2)) : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  ∑ x, e.ensemble.prob x • tau e x

def uu (M : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) : ℝ :=
  vnEntropy (traceRight M) + vnEntropy (traceLeft M)

lemma tau_dens (e : DynamicPureEnsemble (Fin 2 × Fin 2)) (x : Fin e.ensemble.size) :
    IsDensityMatrix (tau e x) := X7_trL_dens _ (pd_dens _ (e.ensemble.normalized x))

lemma taub_dens (e : DynamicPureEnsemble (Fin 2 × Fin 2)) : IsDensityMatrix (taub e) := by
  refine ⟨Matrix.posSemidef_sum _ fun x _ => (tau_dens e x).1.smul (e.ensemble.nonneg x), ?_⟩
  rw [taub, Matrix.trace_sum]
  simp only [Matrix.trace_smul, (tau_dens e _).2]
  simp only [Complex.real_smul, mul_one]
  exact_mod_cast e.ensemble.total

lemma lin {n : ℕ} (p : Fin n → ℝ) (hp : ∑ x, p x = 1) (a b c : ℝ) (f g : Fin n → ℝ) :
    ∑ x, p x * (a + b * f x + c * g x) = a + b * ∑ x, p x * f x + c * ∑ x, p x * g x := by
  have : ∀ x, p x * (a + b * f x + c * g x) = a * p x + b * (p x * f x) + c * (p x * g x) :=
    fun x => by ring
  simp only [this, Finset.sum_add_distrib, ← Finset.mul_sum, hp]
  ring

theorem score2 (ε lam mu : ℝ) (h0 : 0 ≤ ε) (h1 : ε ≤ 1) (e : DynamicPureEnsemble (Fin 2 × Fin 2)) :
    dynamicScore (T2 ε) lam mu e =
      (1 + mu) * ((1 - ε) ^ 2 * vnEntropy (taub e) + ε * (1 - ε) * uu (taub e)) +
      ((1 - ε ^ 2) + lam * (1 - 2 * ε) - mu * ε ^ 2) *
        ∑ x, e.ensemble.prob x * vnEntropy (tau e x) -
      (1 + mu) * ε * (1 - ε) * ∑ x, e.ensemble.prob x * uu (tau e x) := by
  set p := e.ensemble.prob
  have hp : ∑ x, p x = 1 := e.ensemble.total
  have vR : ∀ x, vnEntropy (traceRight (pureOutputs (T2 ε) e x)) = vnEntropy (tau e x) := fun x => by
    rw [pureOutputs, trR_out, P1]; rfl
  have vρ : ∀ x, vnEntropy (pureOutputs (T2 ε) e x) =
      2 * hf ε + ε * (1 - ε) * uu (tau e x) + ε ^ 2 * vnEntropy (tau e x) := fun x => by
    rw [pureOutputs, ent_pure ε h0 h1 _ (e.ensemble.normalized x)]; rfl
  have vL : ∀ x, vnEntropy (traceLeft (pureOutputs (T2 ε) e x)) =
      2 * hf ε + (1 - ε) ^ 2 * vnEntropy (tau e x) + ε * (1 - ε) * uu (tau e x) := fun x => by
    rw [pureOutputs, trL_out]
    show vnEntropy (tensorChannel _ _ (tau e x)) = _
    rw [X7_T_entropy ε h0 h1 _ (tau_dens e x)]
    simp only [hf, uu, tau]
  have avg : ∑ x, p x • traceLeft (pureOutputs (T2 ε) e x) = T2 ε (taub e) := by
    rw [taub, T2_sum]
    exact Finset.sum_congr rfl fun x _ => by rw [pureOutputs, trL_out]; rfl
  have vA : vnEntropy (T2 ε (taub e)) =
      2 * hf ε + (1 - ε) ^ 2 * vnEntropy (taub e) + ε * (1 - ε) * uu (taub e) := by
    show vnEntropy (tensorChannel _ _ (taub e)) = _
    rw [X7_T_entropy ε h0 h1 _ (taub_dens e)]
    simp only [hf, uu]
  have sJ : ∑ x, p x * (vnEntropy (traceRight (pureOutputs (T2 ε) e x)) -
      vnEntropy (pureOutputs (T2 ε) e x)) =
      -(2 * hf ε) + (1 - ε ^ 2) * ∑ x, p x * vnEntropy (tau e x) +
        (-(ε * (1 - ε))) * ∑ x, p x * uu (tau e x) := by
    rw [← lin p hp]
    exact Finset.sum_congr rfl fun x _ => by rw [vR, vρ]; ring
  have sC : ∑ x, p x * (vnEntropy (traceLeft (pureOutputs (T2 ε) e x)) -
      vnEntropy (pureOutputs (T2 ε) e x)) =
      0 + (1 - 2 * ε) * ∑ x, p x * vnEntropy (tau e x) + 0 * ∑ x, p x * uu (tau e x) := by
    rw [← lin p hp]
    exact Finset.sum_congr rfl fun x _ => by rw [vL, vρ]; ring
  have sH : ∑ x, p x * vnEntropy (traceLeft (pureOutputs (T2 ε) e x)) =
      2 * hf ε + (1 - ε) ^ 2 * ∑ x, p x * vnEntropy (tau e x) +
        (ε * (1 - ε)) * ∑ x, p x * uu (tau e x) := by
    rw [← lin p hp]
    exact Finset.sum_congr rfl fun x _ => by rw [vL]
  simp only [dynamicScore, bounds, jointMutual, conditionalCoherent, cqHolevoBits,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons]
  rw [avg, vA, sJ, sC, sH]
  ring

end X4ED

end


-- ===== ESA =====

/-! Qubit erasure: the three bound coordinates of any pure ensemble, and an explicit
ensemble family realizing `erasureBounds ε p`. -/

noncomputable section

namespace X4SA
open Matrix Real QAlgorithms X4EB X4EC X4ES
open scoped Matrix ComplexConjugate ComplexOrder
open QAlgorithms.Papers.Independent.Claimed50.P20
open QAlgorithms.Papers.Independent.Dependency50.P41 (qubitErasure)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- average input-marginal entropy weight. -/
def T (e : DynamicPureEnsemble (Fin 2)) : ℝ := ∑ x, e.ensemble.prob x * vnEntropy (Z e x)

theorem bounds_eq (ε : ℝ) (h0 : 0 ≤ ε) (h1 : ε ≤ 1) (e : DynamicPureEnsemble (Fin 2)) :
    bounds (qubitErasure ε) e =
      ![(1 - ε) * (vnEntropy (Zbar e) + T e), (1 - 2 * ε) * T e,
        (1 - ε) * vnEntropy (Zbar e) - ε * T e] := by
  have hA : vnEntropy (∑ x, e.ensemble.prob x • traceLeft (pureOutputs (qubitErasure ε) e x)) =
      (1 - ε) * vnEntropy (Zbar e) + hb ε := by
    rw [avg, ent_flag ε h0 h1 (Zbar_psd e) (Zbar_trace e)]
  have hL : ∀ x, vnEntropy (traceLeft (pureOutputs (qubitErasure ε) e x)) =
      (1 - ε) * vnEntropy (Z e x) + hb ε := by
    intro x
    rw [pureOutputs, tl_out ε _ (e.ensemble.normalized x)]
    exact ent_flag ε h0 h1 (Z_psd e x) (Z_trace e x)
  have hR : ∀ x, vnEntropy (traceRight (pureOutputs (qubitErasure ε) e x)) = vnEntropy (Z e x) := by
    intro x; rw [pureOutputs, tr_out, ent_RA]; rfl
  have hO : ∀ x, vnEntropy (pureOutputs (qubitErasure ε) e x) = hb ε + ε * vnEntropy (Z e x) := by
    intro x; rw [pureOutputs, ent_out ε h0 h1 _ (e.ensemble.normalized x), ent_RA]; rfl
  have htot := e.ensemble.total
  have e1 : ∑ x, e.ensemble.prob x * (vnEntropy (Z e x) - (hb ε + ε * vnEntropy (Z e x))) =
      (1 - ε) * T e - hb ε := by
    rw [show (∑ x, e.ensemble.prob x * (vnEntropy (Z e x) - (hb ε + ε * vnEntropy (Z e x)))) =
        (1 - ε) * T e - hb ε * ∑ x, e.ensemble.prob x by
      simp only [T, Finset.mul_sum, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun x _ => by ring, htot, mul_one]
  have f2 : ∑ x, e.ensemble.prob x * ((1 - ε) * vnEntropy (Z e x) + hb ε - (hb ε + ε * vnEntropy (Z e x))) =
      (1 - 2 * ε) * T e := by
    simp only [T, Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => by ring
  have e3 : ∑ x, e.ensemble.prob x * ((1 - ε) * vnEntropy (Z e x) + hb ε) = (1 - ε) * T e + hb ε := by
    rw [show (∑ x, e.ensemble.prob x * ((1 - ε) * vnEntropy (Z e x) + hb ε)) =
        (1 - ε) * T e + hb ε * ∑ x, e.ensemble.prob x by
      simp only [T, Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun x _ => by ring, htot, mul_one]
  ext i
  fin_cases i <;>
    simp only [bounds, jointMutual, conditionalCoherent, cqHolevoBits, hA, hL, hR, hO,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
      Matrix.tail_cons, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk] <;>
    simp only [e1, f2] <;> (try rw [Finset.sum_sub_distrib.symm]) <;> (try simp only [e3]) <;> ring_nf

lemma T_bounds (e : DynamicPureEnsemble (Fin 2)) : 0 ≤ T e ∧ T e ≤ 1 := by
  constructor
  · exact Finset.sum_nonneg fun x _ =>
      mul_nonneg (e.ensemble.nonneg x) (ent_nonneg (Z_psd e x) (Z_trace e x))
  · calc T e ≤ ∑ x, e.ensemble.prob x * 1 :=
          Finset.sum_le_sum fun x _ => mul_le_mul_of_nonneg_left
            (X4ER.qubit_le (Z_psd e x) (Z_trace e x)) (e.ensemble.nonneg x)
      _ = 1 := by simp [e.ensemble.total]

end X4SA

end

-- ===== ESB =====

/-! The ensemble `{√p|00⟩+√(1-p)|11⟩, √(1-p)|00⟩+√p|11⟩}` with weights `1/2`:
average marginal `I/2`, each marginal of entropy `h₂(p)`. -/

noncomputable section

namespace X4SB
open Matrix Real QAlgorithms X4EB X4EC X4ES X4SA
open scoped Matrix ComplexConjugate ComplexOrder
open QAlgorithms.Papers.Independent.Claimed50.P20
open QAlgorithms.Papers.Independent.Dependency50.P41 (qubitErasure)

attribute [local instance] Classical.propDecidable Classical.decEq

def am (p : ℝ) (x i : Fin 2) : ℝ := if x.val = i.val then Real.sqrt p else Real.sqrt (1 - p)

def vec (p : ℝ) (x : Fin 2) : EuclideanSpace ℂ (Fin 2 × Fin 2) :=
  WithLp.toLp 2 fun q => if q.1 = q.2 then ((am p x q.2 : ℝ) : ℂ) else 0

lemma am_sq (p : ℝ) (h0 : 0 ≤ p) (h1 : p ≤ 1) (x i : Fin 2) :
    am p x i ^ 2 = if x.val = i.val then p else 1 - p := by
  unfold am; split_ifs
  · exact Real.sq_sqrt h0
  · exact Real.sq_sqrt (by linarith)

lemma vec_norm (p : ℝ) (h0 : 0 ≤ p) (h1 : p ≤ 1) (x : Fin 2) : ‖vec p x‖ = 1 := by
  have h : ‖vec p x‖ ^ 2 = 1 := by
    rw [EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type]
    simp only [vec, Fin.sum_univ_two]
    try simp only [PiLp.toLp_apply]
    simp [Complex.norm_real, am_sq p h0 h1]
    fin_cases x <;> simp <;> ring
  have := norm_nonneg (vec p x)
  nlinarith

def ens (p : ℝ) (h0 : 0 ≤ p) (h1 : p ≤ 1) : DynamicPureEnsemble (Fin 2) where
  referenceDim := 2
  referencePositive := by norm_num
  ensemble :=
    { size := 2
      prob := fun _ => 1 / 2
      vector := fun x => vec p x
      nonneg := fun _ => by norm_num
      total := by norm_num
      normalized := fun x => vec_norm p h0 h1 x }

lemma ens_Z (p : ℝ) (h0 : 0 ≤ p) (h1 : p ≤ 1) (x : Fin (ens p h0 h1).ensemble.size) :
    Z (ens p h0 h1) x = diagonal fun a => ((am p x a ^ 2 : ℝ) : ℂ) := by
  ext a b
  simp only [Z, traceLeft, pureDensity, Matrix.of_apply, diagonal_apply]
  erw [Fin.sum_univ_two]
  simp only [ens, vec, PiLp.toLp_apply]
  fin_cases a <;> fin_cases b <;> simp [pow_two]

lemma ent_am (p : ℝ) (h0 : 0 ≤ p) (h1 : p ≤ 1) (x : Fin 2) :
    -∑ a, am p x a ^ 2 * Real.logb 2 (am p x a ^ 2) = binEntropy2 p := by
  rw [Fin.sum_univ_two, am_sq p h0 h1, am_sq p h0 h1, binEntropy2]
  simp only [Real.binEntropy, Real.log_inv, Real.logb]
  fin_cases x <;> simp <;> ring

lemma ens_T (p : ℝ) (h0 : 0 ≤ p) (h1 : p ≤ 1) : T (ens p h0 h1) = binEntropy2 p := by
  unfold T
  have : ∀ x : Fin (ens p h0 h1).ensemble.size, vnEntropy (Z (ens p h0 h1) x) = binEntropy2 p := by
    intro x
    rw [ens_Z, X4LE.vn_diag]
    exact ent_am p h0 h1 x
  simp only [this]
  erw [Fin.sum_univ_two]
  simp [ens]; ring

lemma ens_bar (p : ℝ) (h0 : 0 ≤ p) (h1 : p ≤ 1) : vnEntropy (Zbar (ens p h0 h1)) = 1 := by
  have : Zbar (ens p h0 h1) = diagonal fun _ => ((1 / 2 : ℝ) : ℂ) := by
    unfold Zbar
    simp only [ens_Z]
    erw [Fin.sum_univ_two]
    ext a b
    simp only [Matrix.add_apply, Matrix.smul_apply, diagonal_apply]
    split_ifs with hab
    · subst hab
      have e0 := am_sq p h0 h1 0 a
      have e1 := am_sq p h0 h1 1 a
      simp only [ens]
      fin_cases a <;> simp at e0 e1 <;> simp [e0, e1, Complex.real_smul] <;> push_cast <;> ring
    · simp
  rw [this, X4LE.vn_diag, Fin.sum_univ_two]
  rw [show (1 / 2 : ℝ) = 2⁻¹ by norm_num, Real.logb_inv, Real.logb_self_eq_one (by norm_num)]
  ring

end X4SB

end

-- ===== EDC =====

/-! Two-use erasure: upper bound on the dynamic score, optimal ensembles, single-use value. -/

noncomputable section

namespace X4ED
open Matrix Real QAlgorithms X7Y10EH
open scoped Matrix ComplexConjugate ComplexOrder
open QAlgorithms.Papers.Independent.Dependency50.P41 (qubitErasure)
open QAlgorithms.Papers.Independent.Information100.P62 (tensorChannel)
open QAlgorithms.Papers.Independent.Claimed50.P20

attribute [local instance] Classical.propDecidable Classical.decEq

lemma uu_le (M : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) (h : IsDensityMatrix M) : uu M ≤ 2 := by
  have h1 := X4ER.qubit_le (X7_trR_dens M h).1 (X7_trR_dens M h).2
  have h2 := X4ER.qubit_le (X7_trL_dens M h).1 (X7_trL_dens M h).2
  unfold uu; linarith

lemma sub_le (M : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) (h : IsDensityMatrix M) :
    vnEntropy M ≤ uu M := X4SU.subadd M h.1 h.2

theorem upper (ε lam mu : ℝ) (h0 : 0 ≤ ε) (h1 : ε ≤ 1) (hmu : 0 ≤ mu)
    (e : DynamicPureEnsemble (Fin 2 × Fin 2)) :
    dynamicScore (T2 ε) lam mu e ≤ 2 * ((1 + mu) * (1 - ε) + max (erasureCoefficient ε lam mu) 0) := by
  rw [score2 ε lam mu h0 h1]
  set p := e.ensemble.prob
  have hp : ∑ x, p x = 1 := e.ensemble.total
  set A := ∑ x, p x * vnEntropy (tau e x)
  set U := ∑ x, p x * uu (tau e x)
  have hA0 : 0 ≤ A := Finset.sum_nonneg fun x _ =>
    mul_nonneg (e.ensemble.nonneg x) (X4ES.ent_nonneg (tau_dens e x).1 (tau_dens e x).2)
  have hAU : A ≤ U := Finset.sum_le_sum fun x _ =>
    mul_le_mul_of_nonneg_left (sub_le _ (tau_dens e x)) (e.ensemble.nonneg x)
  have hU2 : U ≤ 2 := by
    calc U ≤ ∑ x, p x * 2 := Finset.sum_le_sum fun x _ =>
          mul_le_mul_of_nonneg_left (uu_le _ (tau_dens e x)) (e.ensemble.nonneg x)
      _ = 2 := by rw [← Finset.sum_mul, hp, one_mul]
  have hS := sub_le _ (taub_dens e)
  have hS2 := uu_le _ (taub_dens e)
  set c := erasureCoefficient ε lam mu
  have hc : c = (1 - ε) + lam * (1 - 2 * ε) - mu * ε := rfl
  have q1 : 0 ≤ (1 + mu) * (1 - ε) ^ 2 * (uu (taub e) - vnEntropy (taub e)) :=
    mul_nonneg (by positivity) (by linarith)
  have q2 : 0 ≤ (1 + mu) * ε * (1 - ε) * (U - A) :=
    mul_nonneg (mul_nonneg (mul_nonneg (by linarith) h0) (by linarith)) (by linarith)
  have q3 : 0 ≤ (1 + mu) * (1 - ε) * (2 - uu (taub e)) :=
    mul_nonneg (mul_nonneg (by linarith) (by linarith)) (by linarith)
  have q4 : 0 ≤ max c 0 * (2 - A) := mul_nonneg (le_max_right _ _) (by linarith)
  have q5 : 0 ≤ (max c 0 - c) * A := mul_nonneg (by linarith [le_max_left c 0]) hA0
  nlinarith [q1, q2, q3, q4, q5]

/-! Diagonal states. -/

lemma trR_diag (d : Fin 2 × Fin 2 → ℝ) :
    traceRight (diagonal fun q => (d q : ℂ)) = diagonal fun a => ((∑ b, d (a, b) : ℝ) : ℂ) := by
  ext a a'
  by_cases h : a = a'
  · subst h; simp [traceRight, diagonal]
  · simp [traceRight, diagonal, h]

lemma trL_diag (d : Fin 2 × Fin 2 → ℝ) :
    traceLeft (diagonal fun q => (d q : ℂ)) = diagonal fun b => ((∑ a, d (a, b) : ℝ) : ℂ) := by
  ext b b'
  by_cases h : b = b'
  · subst h; simp [traceLeft, diagonal]
  · simp [traceLeft, diagonal, h]

def D4 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ := diagonal fun _ => ((1 / 4 : ℝ) : ℂ)

lemma logb_four : Real.logb 2 4 = 2 := by
  rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.logb_pow, Real.logb_self_eq_one (by norm_num)]
  norm_num

lemma logb4 : Real.logb 2 (1 / 4) = -2 := by
  rw [one_div, Real.logb_inv, show (4 : ℝ) = 2 ^ 2 by norm_num, Real.logb_pow,
    Real.logb_self_eq_one (by norm_num)]
  norm_num

lemma logb2 : Real.logb 2 (1 / 2) = -1 := by
  rw [one_div, Real.logb_inv, Real.logb_self_eq_one (by norm_num)]

lemma D4_ent : vnEntropy D4 = 2 := by
  rw [D4, X4LE.vn_diag]; simp [logb4, logb_four]

lemma D4_uu : uu D4 = 2 := by
  have e1 : traceRight D4 = diagonal fun _ => ((1 / 2 : ℝ) : ℂ) := by
    rw [D4, trR_diag]; congr 1; ext a; simp [Fin.sum_univ_two]; norm_num
  have e2 : traceLeft D4 = diagonal fun _ => ((1 / 2 : ℝ) : ℂ) := by
    rw [D4, trL_diag]; congr 1; ext a; simp [Fin.sum_univ_two]; norm_num
  rw [uu, e1, e2, X4LE.vn_diag]; simp [logb2]; norm_num

lemma vn01 {ι : Type} [Fintype ι] [DecidableEq ι] (d : ι → ℝ) (h : ∀ q, d q = 0 ∨ d q = 1) :
    vnEntropy (diagonal fun q => (d q : ℂ)) = 0 := by
  rw [X4LE.vn_diag, neg_eq_zero]
  refine Finset.sum_eq_zero fun q _ => ?_
  rcases h q with h | h <;> simp [h]

/-! Classical ensemble of the four product basis states (no reference). -/

def g4 : Fin 4 ≃ Fin 2 × Fin 2 := (finCongr (by norm_num : 4 = 2 * 2)).trans finProdFinEquiv.symm

def eC : DynamicPureEnsemble (Fin 2 × Fin 2) where
  referenceDim := 1
  referencePositive := Nat.one_pos
  ensemble :=
    { size := 4
      prob := fun _ => 1 / 4
      vector := fun x => EuclideanSpace.single ((0 : Fin 1), g4 x) 1
      nonneg := fun _ => by norm_num
      total := by simp
      normalized := fun _ => by simp }

lemma pd_single {ι : Type*} {_ : DecidableEq ι} (i a b : ι) :
    pureDensity (EuclideanSpace.single i (1 : ℂ)) a b = if a = i ∧ b = i then 1 else 0 := by
  simp only [pureDensity, Matrix.of_apply, PiLp.single_apply]
  by_cases ha : a = i <;> by_cases hb : b = i <;> simp [ha, hb]

lemma eC_vec (x : Fin eC.ensemble.size) : eC.ensemble.vector x = EuclideanSpace.single ((0 : Fin 1), g4 x) 1 := rfl

lemma eC_tau (x : Fin eC.ensemble.size) :
    tau eC x = diagonal fun q => ((if q = g4 x then 1 else 0 : ℝ) : ℂ) := by
  ext q q'
  change ∑ y : Fin 1, pureDensity (EuclideanSpace.single ((0 : Fin 1), g4 x) (1 : ℂ)) (y, q) (y, q') = _
  rw [Fin.sum_univ_one, pd_single, diagonal_apply]
  simp only [Prod.mk.injEq, true_and]
  by_cases h1 : q = g4 x <;> by_cases h2 : q' = g4 x
  · simp [h1, h2]
  · subst h1; simp [h2, Ne.symm h2]
  · simp [h1, h2]
  · simp [h1, h2]

lemma eC_taub : taub eC = D4 := by
  ext q q'
  simp only [taub, Matrix.sum_apply, Matrix.smul_apply, eC_tau, D4, diagonal_apply]
  by_cases h : q = q'
  · subst h
    simp only [if_true]
    show ∑ x : Fin 4, (1 / 4 : ℝ) • (((if q = g4 x then 1 else 0 : ℝ)) : ℂ) = _
    rw [Equiv.sum_comp g4 (fun y => (1 / 4 : ℝ) • (((if q = y then 1 else 0 : ℝ)) : ℂ)),
      Fintype.sum_eq_single q (fun y hy => by rw [if_neg (Ne.symm hy)]; simp)]
    simp
  · simp [h]

lemma eC_vals (x : Fin eC.ensemble.size) : vnEntropy (tau eC x) = 0 ∧ uu (tau eC x) = 0 := by
  rw [eC_tau]
  refine ⟨vn01 _ (fun q => by split_ifs <;> simp), ?_⟩
  rw [uu, trR_diag, trL_diag]
  obtain ⟨a0, b0⟩ := g4 x
  rw [vn01 _ (fun a => by fin_cases a0 <;> fin_cases b0 <;> fin_cases a <;> simp [Fin.sum_univ_two]),
    vn01 _ (fun a => by fin_cases a0 <;> fin_cases b0 <;> fin_cases a <;> simp [Fin.sum_univ_two])]
  simp

/-! Maximally entangled input with a four-dimensional reference. -/

def psiE : EuclideanSpace ℂ (Fin 4 × (Fin 2 × Fin 2)) :=
  WithLp.toLp 2 fun p => if p.1 = g4.symm p.2 then (1 / 2 : ℂ) else 0

lemma psiE_norm : ‖psiE‖ = 1 := by
  rw [EuclideanSpace.norm_eq, Real.sqrt_eq_one, Fintype.sum_prod_type, Finset.sum_comm]
  simp only [psiE, PiLp.toLp_apply, apply_ite (fun z : ℂ => ‖z‖ ^ 2), norm_zero]
  simp [Finset.sum_ite_eq']
  norm_num

def eE : DynamicPureEnsemble (Fin 2 × Fin 2) where
  referenceDim := 4
  referencePositive := by norm_num
  ensemble :=
    { size := 1
      prob := fun _ => 1
      vector := fun _ => psiE
      nonneg := fun _ => by norm_num
      total := by simp
      normalized := fun _ => psiE_norm }

lemma eE_tau (x : Fin eE.ensemble.size) : tau eE x = D4 := by
  ext q q'
  change ∑ r : Fin 4, psiE (r, q) * conj (psiE (r, q')) = _
  simp only [psiE, PiLp.toLp_apply, D4, diagonal_apply, ite_mul, zero_mul, mul_ite, mul_zero]
  by_cases h : q = q'
  · subst h; simp [Finset.sum_ite_eq', map_ofNat]; norm_num
  · have h' : g4.symm q ≠ g4.symm q' := g4.symm.injective.ne h
    simp [Finset.sum_ite_eq', h, Ne.symm h']

lemma eE_taub : taub eE = D4 := by
  change ∑ x : Fin 1, (1 : ℝ) • tau eE x = D4
  rw [Fin.sum_univ_one, one_smul]; exact eE_tau _

lemma eE_score (ε lam mu : ℝ) (h0 : 0 ≤ ε) (h1 : ε ≤ 1) :
    dynamicScore (T2 ε) lam mu eE = 2 * ((1 + mu) * (1 - ε) + erasureCoefficient ε lam mu) := by
  rw [score2 ε lam mu h0 h1, eE_taub, D4_ent, D4_uu]
  simp only [eE_tau, D4_ent, D4_uu, ← Finset.sum_mul, eE.ensemble.total]
  simp only [erasureCoefficient]
  ring

lemma eC_score (ε lam mu : ℝ) (h0 : 0 ≤ ε) (h1 : ε ≤ 1) :
    dynamicScore (T2 ε) lam mu eC = 2 * ((1 + mu) * (1 - ε)) := by
  rw [score2 ε lam mu h0 h1, eC_taub, D4_ent, D4_uu]
  have a1 : ∀ x, vnEntropy (tau eC x) = 0 := fun x => (eC_vals x).1
  have a2 : ∀ x, uu (tau eC x) = 0 := fun x => (eC_vals x).2
  simp only [a1, a2, mul_zero, Finset.sum_const_zero]
  ring

open X4EB X4EC X4ES X4SA X4SB in
lemma d1 (ε lam mu : ℝ) (h0 : 0 ≤ ε) (h1 : ε ≤ 1) (hmu : 0 ≤ mu) :
    dynamic (qubitErasure ε) lam mu = (1 + mu) * (1 - ε) + max (erasureCoefficient ε lam mu) 0 := by
  set c := erasureCoefficient ε lam mu
  have hk : 0 ≤ (1 + mu) * (1 - ε) := mul_nonneg (by linarith) (by linarith)
  by_cases hc : c < 0
  · have hG : IsGreatest (dynamicValues (qubitErasure ε) lam mu) ((1 + mu) * (1 - ε)) := by
      refine ⟨⟨wit, (wit_score ε lam mu h0 h1).symm⟩, ?_⟩
      rintro v ⟨e, rfl⟩
      exact score_le ε lam mu h0 h1 hmu hc.le e
    rw [max_eq_right hc.le, add_zero]
    exact hG.csSup_eq
  · push Not at hc
    have hG : IsGreatest (dynamicValues (qubitErasure ε) lam mu) ((1 + mu) * (1 - ε) + c) := by
      refine ⟨⟨ens (1 / 2) (by norm_num) (by norm_num), ?_⟩, ?_⟩
      · rw [score ε lam mu h0 h1, ens_bar]
        have := ens_T (1 / 2) (by norm_num) (by norm_num)
        unfold T at this
        rw [this, bin_half]; ring
      · rintro v ⟨e, rfl⟩
        rw [score ε lam mu h0 h1]
        have hS := X4ER.qubit_le (Zbar_psd e) (Zbar_trace e)
        have hT := (T_bounds e).2
        unfold T at hT
        nlinarith [mul_le_mul_of_nonneg_left hT hc, mul_le_mul_of_nonneg_left hS hk]
    rw [max_eq_left hc]
    exact hG.csSup_eq

theorem main (ε lam mu : ℝ) (h0 : 0 ≤ ε) (h1 : ε ≤ 1) (hmu : 0 ≤ mu) :
    dynamic (T2 ε) lam mu = dynamic (qubitErasure ε) lam mu + dynamic (qubitErasure ε) lam mu := by
  set c := erasureCoefficient ε lam mu
  have hG : IsGreatest (dynamicValues (T2 ε) lam mu) (2 * ((1 + mu) * (1 - ε) + max c 0)) := by
    refine ⟨?_, ?_⟩
    · by_cases hc : 0 ≤ c
      · exact ⟨eE, by rw [eE_score ε lam mu h0 h1, max_eq_left hc]⟩
      · exact ⟨eC, by rw [eC_score ε lam mu h0 h1, max_eq_right (le_of_not_ge hc), add_zero]⟩
    · rintro v ⟨e, rfl⟩
      exact upper ε lam mu h0 h1 hmu e
  rw [d1 ε lam mu h0 h1 hmu]
  refine hG.csSup_eq.trans ?_
  ring

end X4ED

end


-- ===== EDSol =====

noncomputable section

open scoped BigOperators Matrix ComplexConjugate ComplexOrder
open QAlgorithms.Papers.Independent.Claimed50.P20
open QAlgorithms.Papers.Independent.Information100.P62 (tensorChannel)
open QAlgorithms.Papers.Independent.Dependency50.P41 (qubitErasure)

attribute [local instance] Classical.propDecidable Classical.decEq

theorem solution
    (epsilon lambda mu : ℝ) (he0 : 0 ≤ epsilon) (he1 : epsilon ≤ 1)
    (hlambda : 0 ≤ lambda) (hmu : 0 ≤ mu) :
    dynamic (tensorChannel (qubitErasure epsilon) (qubitErasure epsilon)) lambda mu =
      dynamic (qubitErasure epsilon) lambda mu + dynamic (qubitErasure epsilon) lambda mu :=
  X4ED.main epsilon lambda mu he0 he1 hmu

end

