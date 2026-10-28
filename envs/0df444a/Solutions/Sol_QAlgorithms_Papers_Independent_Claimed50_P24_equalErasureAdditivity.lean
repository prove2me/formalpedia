-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Claimed50.P24.equalErasureAdditivity
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T08:17:39.207131+00:00
-- url     : https://prove2.me/submissions/5e766af0-c2fd-4120-988f-754bc22bbe68

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P20
import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P41
import Definitions.Def_QAlgorithms_Defs_QuantumInformation
import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P42
import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P33
import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P24

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

lemma qe_apply (ε : ℝ) (ρ : Matrix (Fin 2) (Fin 2) ℂ) (x y : Fin 3) :
    qubitErasure ε ρ x y =
      if hx : x.val < 2 then (if hy : y.val < 2 then (1 - (ε : ℂ)) * ρ ⟨x.val, hx⟩ ⟨y.val, hy⟩ else 0)
      else (if y.val < 2 then 0 else (ε : ℂ) * ρ.trace) := by
  by_cases hx : x.val < 2 <;> by_cases hy : y.val < 2 <;>
    simp only [qubitErasure, Matrix.of_apply, hx, hy, dif_pos, dif_neg, not_false_eq_true,
      if_true, if_false] <;> rfl


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
    rw [qe_apply, h.2]
    fin_cases i <;> fin_cases j <;> simp [Q, A, D, X7_e3]
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
  ext x y
  rw [qe_apply, h2]
  fin_cases x <;> fin_cases y <;> simp [X7_e3]

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
  simp only [idTensorSuperop, Matrix.of_apply, qe_apply]
  fin_cases x <;> fin_cases y <;>
    simp [X7_eR, X7_e3, QAlgorithms.traceRight, Matrix.trace, Fin.sum_univ_two] <;> ring

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
  simp only [Matrix.add_apply, qe_apply, Matrix.trace_add]
  split_ifs <;> ring

lemma X7_N_lin (ε : ℝ) (X : Matrix (Fin 2) (Fin 2) ℂ) (x y : Fin 3) :
    qubitErasure ε X x y = ∑ k, ∑ l, X k l * qubitErasure ε (Matrix.single k l 1) x y := by
  fin_cases x <;> fin_cases y <;>
    simp only [qe_apply, Matrix.trace, Matrix.diag, Fin.sum_univ_two, Matrix.single_apply] <;>
    simp <;> ring

lemma X7_N_single (ε : ℝ) (i j : Fin 2) (x y : Fin 3) :
    qubitErasure ε (Matrix.single i j 1) x y =
      if x.val < 2 ∧ y.val < 2 then (if i.val = x.val ∧ j.val = y.val then ((1 - ε : ℝ) : ℂ) else 0)
      else if x.val = 2 ∧ y.val = 2 then (if i = j then ((ε : ℝ) : ℂ) else 0) else 0 := by
  fin_cases i <;> fin_cases j <;> fin_cases x <;> fin_cases y <;>
    simp [qe_apply, Matrix.single_apply, Matrix.trace, Fin.sum_univ_two]

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

variable {e : ℕ}

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

end X4DP

end QAlgorithms.Papers.Independent.Support50.P41

end


-- ===== FanoLib =====

/-! Generic: Schur concavity of von Neumann entropy and the (quantum) Fano bound. -/

noncomputable section

namespace X4FN
open Matrix Real QAlgorithms
open scoped Matrix ComplexConjugate ComplexOrder

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

end X4FN

end

-- ===== SFB =====

/-! Generic: `Σ_k |tr(ρ E_k)|² ≤ F(ρ, Σ_k E_k ρ E_kᴴ)²` for PSD `ρ`. -/

noncomputable section

namespace X4SF
open Matrix QAlgorithms
open scoped Matrix ComplexOrder ComplexConjugate

variable {ι K : Type*} [Fintype ι] [DecidableEq ι] [Fintype K]

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

lemma vn_zero {ι : Type*} [Fintype ι] [DecidableEq ι] : vnEntropy (0 : Matrix ι ι ℂ) = 0 := by
  unfold vnEntropy; simp

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

variable {m : ℕ} {D : Fin m → Type} [∀ i, Fintype (D i)]

section
attribute [local instance] Classical.propDecidable Classical.decEq

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

/-- binary entropy (bits) written with `logb`. -/
def hb (ε : ℝ) : ℝ := -((1 - ε) * Real.logb 2 (1 - ε)) - ε * Real.logb 2 ε

lemma smul_psd {ι : Type*} [Fintype ι] {X : Matrix ι ι ℂ} (hX : X.PosSemidef) {c : ℝ} (hc : 0 ≤ c) :
    ((c : ℂ) • X).PosSemidef := hX.smul (by exact_mod_cast hc)

lemma pd_trace {ι : Type} [Fintype ι] (v : EuclideanSpace ℂ ι) (hv : ‖v‖ = 1) :
    (pureDensity v).trace = 1 := by
  rw [← X4ZE.unit_sum v hv]; simp [pureDensity, Matrix.trace]

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

variable {R : Type*} [Fintype R]

attribute [local instance] Classical.propDecidable Classical.decEq

/-- the binary entropy of the erasure flag. -/
def hf (ε : ℝ) : ℝ := -(ε * Real.logb 2 ε) - (1 - ε) * Real.logb 2 (1 - ε)

variable [DecidableEq R]

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

variable {r : ℕ}

lemma pd_dens {ι : Type} [Fintype ι] (ψ : EuclideanSpace ℂ ι) (h : ‖ψ‖ = 1) :
    IsDensityMatrix (pureDensity ψ) := ⟨X4EB.pd_psd ψ, X4EB.pd_trace ψ h⟩

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

end X4ED

end


-- ===== ERP =====

/-! Erasure dilation (`Option A` flag): receiver/complement closed forms, flag entropy,
and concavity of von Neumann entropy for probability mixtures. -/

noncomputable section

namespace X4EP
open Matrix Real QAlgorithms
open scoped Matrix ComplexConjugate ComplexOrder
open QAlgorithms.Papers.Independent.Information100.P67
  (receiverChannel complementaryChannel erasureDilation)

attribute [local instance] Classical.propDecidable Classical.decEq

variable {A : Type} [Fintype A] [DecidableEq A]

/-- embedding `A → Option A`. -/
def Jo : Matrix (Option A) A ℂ := Matrix.of fun b a => if b = some a then 1 else 0

/-- the flag projector `|none⟩⟨none|`. -/
def fl : Matrix (Option A) (Option A) ℂ := pureDensity (EuclideanSpace.single (none : Option A) 1)

lemma Jo_iso : (Jo (A := A))ᴴ * Jo (A := A) = 1 := by
  ext a b
  simp [Jo, Matrix.mul_apply, Fintype.sum_option, conjTranspose_apply, Matrix.one_apply, eq_comm]

lemma fl_psd : (fl : Matrix (Option A) (Option A) ℂ).PosSemidef := X4EB.pd_psd _
lemma fl_trace : (fl : Matrix (Option A) (Option A) ℂ).trace = 1 := X4EB.pd_trace _ (by simp)
lemma fl_ent : vnEntropy (fl : Matrix (Option A) (Option A) ℂ) = 0 := X4ER.vn_pure _ (by simp)

lemma sq_c {c : ℝ} (h : 0 ≤ c) : ((Real.sqrt c : ℝ) : ℂ) * ((Real.sqrt c : ℝ) : ℂ) = (c : ℂ) := by
  rw [← Complex.ofReal_mul, Real.mul_self_sqrt h]

lemma rec_eq (ε : ℝ) (h0 : 0 ≤ ε) (h1 : ε ≤ 1) (σ : Matrix A A ℂ) :
    receiverChannel (erasureDilation (A := A) ε) σ =
      ((1 - ε : ℝ) : ℂ) • (Jo (A := A) * σ * (Jo (A := A))ᴴ) + ((ε : ℝ) : ℂ) • (σ.trace • fl) := by
  have hs1 := sq_c (show 0 ≤ 1 - ε by linarith)
  have hs2 := sq_c h0
  ext b b'
  rcases b with _ | a <;> rcases b' with _ | a' <;>
    simp [receiverChannel, traceRight, erasureDilation, Matrix.mul_apply, Fintype.sum_option,
      conjTranspose_apply, Jo, fl, pureDensity, Matrix.trace, apply_ite (starRingEnd ℂ), mul_ite,
      Finset.sum_ite_eq, Finset.sum_ite_eq']
  · rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    linear_combination σ x x * hs2
  · push_cast at hs1
    linear_combination σ a a' * hs1

lemma comp_eq (ε : ℝ) (h0 : 0 ≤ ε) (h1 : ε ≤ 1) (σ : Matrix A A ℂ) :
    complementaryChannel (erasureDilation (A := A) ε) σ =
      ((ε : ℝ) : ℂ) • (Jo (A := A) * σ * (Jo (A := A))ᴴ) + ((1 - ε : ℝ) : ℂ) • (σ.trace • fl) := by
  have hs1 := sq_c (show 0 ≤ 1 - ε by linarith)
  have hs2 := sq_c h0
  ext b b'
  rcases b with _ | a <;> rcases b' with _ | a' <;>
    simp [complementaryChannel, traceLeft, erasureDilation, Matrix.mul_apply, Fintype.sum_option,
      conjTranspose_apply, Jo, fl, pureDensity, Matrix.trace, apply_ite (starRingEnd ℂ), mul_ite,
      Finset.sum_ite_eq, Finset.sum_ite_eq']
  · push_cast at hs1
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    linear_combination σ x x * hs1
  · linear_combination σ a a' * hs2

/-- entropy of a flagged mixture `a·X ⊕ b·|none⟩⟨none|` for a density `X`. -/
lemma flag_ent {X : Matrix A A ℂ} (hX : X.PosSemidef) (htr : X.trace = 1) {a b : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) :
    vnEntropy ((a : ℂ) • (Jo (A := A) * X * (Jo (A := A))ᴴ) + (b : ℂ) • ((1 : ℂ) • fl)) =
      a * vnEntropy X - a * Real.logb 2 a - b * Real.logb 2 b := by
  rw [one_smul]
  have hJ : (Jo (A := A) * X * (Jo (A := A))ᴴ).PosSemidef := hX.mul_mul_conjTranspose_same _
  have hAB : Jo (A := A) * X * (Jo (A := A))ᴴ * fl = 0 := by
    ext u v
    simp [Matrix.mul_apply, Fintype.sum_option, Jo, fl, pureDensity, conjTranspose_apply]
  have htrJ : (Jo (A := A) * X * (Jo (A := A))ᴴ).trace = 1 := by
    rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, Jo_iso, Matrix.one_mul, htr]
  rw [X4ER.vn_add_orth (X4EB.smul_psd hJ ha) (X4EB.smul_psd fl_psd hb)
    (by rw [Matrix.smul_mul, Matrix.mul_smul, hAB, smul_zero, smul_zero]),
    X4ER.vn_smul0 hJ.1 ha, X4ER.vn_smul0 fl_psd.1 hb, X4ER.vn_conj_iso hX _ Jo_iso, fl_ent,
    htrJ, fl_trace]
  simp; ring

/-- concavity of entropy for probability mixtures of densities. -/
lemma concave {ι M : Type} [Fintype ι] [DecidableEq ι] [Fintype M] [DecidableEq M]
    (q : M → ℝ) (τ : M → Matrix ι ι ℂ) (hq : ∀ m, 0 ≤ q m) (hs : ∑ m, q m = 1)
    (hτ : ∀ m, (τ m).PosSemidef) (ht : ∀ m, (τ m).trace = 1) :
    ∑ m, q m * vnEntropy (τ m) ≤ vnEntropy (∑ m, ((q m : ℝ) : ℂ) • τ m) := by
  have h := X4LE.conc (fun m => ((q m : ℝ) : ℂ) • τ m) (fun m => X4EB.smul_psd (hτ m) (hq m))
    (by simp [Matrix.trace_smul, ht, ← Complex.ofReal_sum, hs])
  refine le_trans (le_of_eq ?_) h
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [X4ER.vn_smul0 (hτ m).1 (hq m), Matrix.trace_smul, ht m]
  simp

end X4EP

end

-- ===== ERQ =====

/-! Erasure dilation on two-label ensembles: the dynamic objective equals
`(1+μ)(1-ε) I₁ + (λ(1-2ε) - με) I₂` with `I₁ ≤ 1`, `0 ≤ I₂ ≤ 1`, and the boundary
ensembles realize `I₁ = 1`, `I₂ = h₂(ν)`. -/

noncomputable section

namespace X4EQ
open Matrix Real QAlgorithms X4EP
open scoped Matrix ComplexConjugate ComplexOrder
open QAlgorithms.Papers.Independent.Claimed50.P24
open QAlgorithms.Papers.Independent.Information100.P67
  (receiverChannel complementaryChannel erasureDilation)

attribute [local instance] Classical.propDecidable Classical.decEq

abbrev V (ε : ℝ) := erasureDilation (A := Fin 2) ε

lemma rec_ent (ε : ℝ) (h0 : 0 ≤ ε) (h1 : ε ≤ 1) {σ : Matrix (Fin 2) (Fin 2) ℂ} (hσ : σ.PosSemidef)
    (htr : σ.trace = 1) :
    vnEntropy (receiverChannel (V ε) σ) = (1 - ε) * vnEntropy σ + X4EB.hb ε := by
  rw [rec_eq ε h0 h1, htr, flag_ent hσ htr (by linarith) h0, X4EB.hb]; ring

lemma comp_ent (ε : ℝ) (h0 : 0 ≤ ε) (h1 : ε ≤ 1) {σ : Matrix (Fin 2) (Fin 2) ℂ} (hσ : σ.PosSemidef)
    (htr : σ.trace = 1) :
    vnEntropy (complementaryChannel (V ε) σ) = ε * vnEntropy σ + X4EB.hb ε := by
  rw [comp_eq ε h0 h1, htr, flag_ent hσ htr h0 (by linarith), X4EB.hb]; ring

variable (A : TwoLabelEnsemble (Fin 2))

/-- `S(avg) - Σ p S(σ)`. -/
def I1 : ℝ := vnEntropy A.average - ∑ x, ∑ y, A.prob x y * vnEntropy (A.state x y)
/-- `Σ px S(ρ_x) - Σ p S(σ)`. -/
def I2 : ℝ := ∑ x, A.px x * vnEntropy (A.inputX x) - ∑ x, ∑ y, A.prob x y * vnEntropy (A.state x y)

variable {A}

lemma px_sum (hA : A.Valid) : ∑ x, A.px x = 1 := hA.2.2.2.1

lemma px_nonneg (hA : A.Valid) (x : Fin A.nx) : 0 ≤ A.px x :=
  Finset.sum_nonneg fun y _ => hA.2.2.1 x y

lemma avg_dens (hA : A.Valid) : A.average.PosSemidef ∧ A.average.trace = 1 := by
  refine ⟨posSemidef_sum _ fun x _ => posSemidef_sum _ fun y _ =>
    X4EB.smul_psd (hA.2.2.2.2 x y).1 (hA.2.2.1 x y), ?_⟩
  rw [TwoLabelEnsemble.average, Matrix.trace_sum]
  simp only [Matrix.trace_sum, Matrix.trace_smul, (fun x y => (hA.2.2.2.2 x y).2), smul_eq_mul, mul_one]
  exact_mod_cast hA.2.2.2.1

lemma inX_dens (hA : A.Valid) (x : Fin A.nx) : (A.inputX x).PosSemidef ∧ (A.inputX x).trace = 1 := by
  unfold TwoLabelEnsemble.inputX
  split_ifs with h
  · exact ⟨X4EB.pd_psd _, X4EB.pd_trace _ (by simp [ket])⟩
  · have hpos : 0 < A.px x := lt_of_le_of_ne (px_nonneg hA x) (Ne.symm h)
    refine ⟨posSemidef_sum _ fun y _ =>
      X4EB.smul_psd (hA.2.2.2.2 x y).1 (div_nonneg (hA.2.2.1 x y) hpos.le), ?_⟩
    rw [Matrix.trace_sum]
    simp only [Matrix.trace_smul, (fun y => (hA.2.2.2.2 x y).2), smul_eq_mul, mul_one]
    rw [← Complex.ofReal_sum, ← Finset.sum_div]
    have : ∑ y, A.prob x y = A.px x := rfl
    rw [this, div_self h]; simp

lemma dsum {m n : ℕ} (f g : Fin m → Fin n → ℝ) (c h : ℝ) :
    ∑ x, ∑ y, f x y * (c * g x y + h) = c * ∑ x, ∑ y, f x y * g x y + h * ∑ x, ∑ y, f x y := by
  simp only [mul_add, Finset.sum_add_distrib, Finset.mul_sum]
  congr 1 <;> refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => by ring

lemma ssum {m : ℕ} (f g : Fin m → ℝ) (c h : ℝ) :
    ∑ x, f x * (c * g x + h) = c * ∑ x, f x * g x + h * ∑ x, f x := by
  simp only [mul_add, Finset.sum_add_distrib, Finset.mul_sum]
  congr 1 <;> refine Finset.sum_congr rfl fun x _ => by ring

theorem obj_eq (ε lam mu : ℝ) (h0 : 0 ≤ ε) (h1 : ε ≤ 1) (hA : A.Valid) :
    infoXYB (V ε) A = (1 - ε) * I1 A ∧ infoYBX (V ε) A = (1 - ε) * I2 A ∧
      infoYEX (V ε) A = ε * I2 A ∧
      dynamicObjective (V ε) lam mu A =
        (1 + mu) * (1 - ε) * I1 A + (lam * (1 - 2 * ε) - mu * ε) * I2 A := by
  have htot : ∑ x, ∑ y, A.prob x y = 1 := hA.2.2.2.1
  have hpx := px_sum hA
  have hR : ∀ x y, vnEntropy (receiverChannel (V ε) (A.state x y)) =
      (1 - ε) * vnEntropy (A.state x y) + X4EB.hb ε := fun x y =>
    rec_ent ε h0 h1 (hA.2.2.2.2 x y).1 (hA.2.2.2.2 x y).2
  have hE : ∀ x y, vnEntropy (complementaryChannel (V ε) (A.state x y)) =
      ε * vnEntropy (A.state x y) + X4EB.hb ε := fun x y =>
    comp_ent ε h0 h1 (hA.2.2.2.2 x y).1 (hA.2.2.2.2 x y).2
  have hRX : ∀ x, vnEntropy (receiverChannel (V ε) (A.inputX x)) =
      (1 - ε) * vnEntropy (A.inputX x) + X4EB.hb ε := fun x =>
    rec_ent ε h0 h1 (inX_dens hA x).1 (inX_dens hA x).2
  have hEX : ∀ x, vnEntropy (complementaryChannel (V ε) (A.inputX x)) =
      ε * vnEntropy (A.inputX x) + X4EB.hb ε := fun x =>
    comp_ent ε h0 h1 (inX_dens hA x).1 (inX_dens hA x).2
  have hB : vnEntropy (receiverChannel (V ε) A.average) = (1 - ε) * vnEntropy A.average + X4EB.hb ε :=
    rec_ent ε h0 h1 (avg_dens hA).1 (avg_dens hA).2
  have a1 : infoXYB (V ε) A = (1 - ε) * I1 A := by
    simp only [infoXYB, entropyB, hB, hR, dsum, htot, I1]; ring
  have a2 : infoYBX (V ε) A = (1 - ε) * I2 A := by
    simp only [infoYBX, entropyBX, hRX, hR]; rw [dsum, ssum, htot, hpx]; unfold I2; ring
  have a3 : infoYEX (V ε) A = ε * I2 A := by
    simp only [infoYEX, entropyEX, hEX, hE]; rw [dsum, ssum, htot, hpx]; unfold I2; ring
  refine ⟨a1, a2, a3, ?_⟩
  simp only [dynamicObjective, a1, a2, a3]; ring

lemma I1_le (hA : A.Valid) : I1 A ≤ 1 := by
  have hS := X4ER.qubit_le (avg_dens hA).1 (avg_dens hA).2
  have hT : 0 ≤ ∑ x, ∑ y, A.prob x y * vnEntropy (A.state x y) :=
    Finset.sum_nonneg fun x _ => Finset.sum_nonneg fun y _ =>
      mul_nonneg (hA.2.2.1 x y) (X4ES.ent_nonneg (hA.2.2.2.2 x y).1 (hA.2.2.2.2 x y).2)
  unfold I1; linarith

lemma I2_nonneg (hA : A.Valid) : 0 ≤ I2 A := by
  unfold I2
  rw [sub_nonneg]
  refine Finset.sum_le_sum fun x _ => ?_
  by_cases h : A.px x = 0
  · have hz : ∀ y, A.prob x y = 0 := by
      intro y
      have := (Finset.sum_eq_zero_iff_of_nonneg (fun y _ => hA.2.2.1 x y)).1 h y (Finset.mem_univ y)
      exact this
    simp [hz, h]
  · have hpos : 0 < A.px x := lt_of_le_of_ne (px_nonneg hA x) (Ne.symm h)
    have hc := concave (fun y => A.prob x y / A.px x) (fun y => A.state x y)
      (fun y => div_nonneg (hA.2.2.1 x y) hpos.le)
      (by rw [← Finset.sum_div]; exact div_self h)
      (fun y => (hA.2.2.2.2 x y).1) (fun y => (hA.2.2.2.2 x y).2)
    have hin : A.inputX x = ∑ y, ((A.prob x y / A.px x : ℝ) : ℂ) • A.state x y := by
      simp [TwoLabelEnsemble.inputX, h]
    rw [hin]
    calc ∑ y, A.prob x y * vnEntropy (A.state x y)
        = A.px x * ∑ y, A.prob x y / A.px x * vnEntropy (A.state x y) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun y _ => by field_simp
      _ ≤ A.px x * vnEntropy (∑ y, ((A.prob x y / A.px x : ℝ) : ℂ) • A.state x y) :=
          mul_le_mul_of_nonneg_left hc hpos.le

lemma I2_le (hA : A.Valid) : I2 A ≤ 1 := by
  have hT : 0 ≤ ∑ x, ∑ y, A.prob x y * vnEntropy (A.state x y) :=
    Finset.sum_nonneg fun x _ => Finset.sum_nonneg fun y _ =>
      mul_nonneg (hA.2.2.1 x y) (X4ES.ent_nonneg (hA.2.2.2.2 x y).1 (hA.2.2.2.2 x y).2)
  have hS : ∑ x, A.px x * vnEntropy (A.inputX x) ≤ 1 := by
    calc ∑ x, A.px x * vnEntropy (A.inputX x) ≤ ∑ x, A.px x * 1 :=
          Finset.sum_le_sum fun x _ => mul_le_mul_of_nonneg_left
            (X4ER.qubit_le (inX_dens hA x).1 (inX_dens hA x).2) (px_nonneg hA x)
      _ = 1 := by simp [px_sum hA]
  unfold I2; linarith

end X4EQ

end

-- ===== EEA =====

/-! Two uses of the erasure dilation (Claimed50.P24): the receiver and complementary channels of the
product dilation are relabelled `N_ε ⊗ N_ε` and `N_{1-ε} ⊗ N_{1-ε}`. -/

noncomputable section

namespace X4EE
open Matrix Real QAlgorithms X7Y10EH X4ED
open scoped Matrix ComplexConjugate ComplexOrder
open QAlgorithms.Papers.Independent.Dependency50.P41 (qubitErasure)
open QAlgorithms.Papers.Independent.Information100.P62 (tensorChannel)
open QAlgorithms.Papers.Independent.Claimed50.P24
open QAlgorithms.Papers.Independent.Information100.P67
  (receiverChannel complementaryChannel erasureDilation)

attribute [local instance] Classical.propDecidable Classical.decEq

section gen
variable {I B E J D F : Type} [Fintype I] [Fintype B] [Fintype E] [Fintype J] [Fintype D] [Fintype F]

lemma conj_form (U : Matrix (B × E) I ℂ) (X : Matrix I I ℂ) (p q : B × E) :
    (U * X * Uᴴ) p q = ∑ a, ∑ a', X a a' * (U p a * conj (U q a')) := by
  simp only [Matrix.mul_apply, conjTranspose_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun a' _ => ?_
  simp [RCLike.star_def]; ring

lemma rec_single (V : Matrix (B × E) I ℂ) (i j : I) (b b' : B) :
    receiverChannel V (Matrix.single i j 1) b b' = ∑ e, V (b, e) i * conj (V (b', e) j) := by
  simp [receiverChannel, traceRight, conj_form, Matrix.single_apply, ite_and]

lemma comp_single (V : Matrix (B × E) I ℂ) (i j : I) (e e' : E) :
    complementaryChannel V (Matrix.single i j 1) e e' = ∑ b, V (b, e) i * conj (V (b, e') j) := by
  simp [complementaryChannel, traceLeft, conj_form, Matrix.single_apply, ite_and]

lemma rec_prod (V : Matrix (B × E) I ℂ) (W : Matrix (D × F) J ℂ) (X : Matrix (I × J) (I × J) ℂ) :
    receiverChannel (productDilation V W) X = tensorChannel (receiverChannel V) (receiverChannel W) X := by
  ext ⟨b1, b2⟩ ⟨b1', b2'⟩
  simp only [tensorChannel, rec_single]
  simp only [receiverChannel, traceRight, Matrix.of_apply, conj_form, productDilation]
  simp only [Fintype.sum_prod_type, Finset.mul_sum, Finset.sum_mul]
  simp only [← Fintype.sum_prod_type']
  exact Fintype.sum_equiv
    ({ toFun := fun t => (t.2.2.1, (t.2.2.2.2.1, (t.2.2.2.1, (t.2.2.2.2.2, (t.2.1, t.1)))))
       invFun := fun t => (t.2.2.2.2.2, (t.2.2.2.2.1, (t.1, (t.2.2.1, (t.2.1, t.2.2.2.1)))))
       left_inv := fun _ => rfl
       right_inv := fun _ => rfl } : E × (F × (I × (J × (I × J)))) ≃ I × (I × (J × (J × (F × E)))))
    _ _ (fun t => by simp only [Equiv.coe_fn_mk, map_mul]; ring)

lemma comp_prod (V : Matrix (B × E) I ℂ) (W : Matrix (D × F) J ℂ) (X : Matrix (I × J) (I × J) ℂ) :
    complementaryChannel (productDilation V W) X =
      tensorChannel (complementaryChannel V) (complementaryChannel W) X := by
  ext ⟨e1, e2⟩ ⟨e1', e2'⟩
  simp only [tensorChannel, comp_single]
  simp only [complementaryChannel, traceLeft, Matrix.of_apply, conj_form, productDilation]
  simp only [Fintype.sum_prod_type, Finset.mul_sum, Finset.sum_mul]
  simp only [← Fintype.sum_prod_type']
  exact Fintype.sum_equiv
    ({ toFun := fun t => (t.2.2.1, (t.2.2.2.2.1, (t.2.2.2.1, (t.2.2.2.2.2, (t.2.1, t.1)))))
       invFun := fun t => (t.2.2.2.2.2, (t.2.2.2.2.1, (t.1, (t.2.2.1, (t.2.1, t.2.2.2.1)))))
       left_inv := fun _ => rfl
       right_inv := fun _ => rfl } : B × (D × (I × (J × (I × J)))) ≃ I × (I × (J × (J × (D × B)))))
    _ _ (fun t => by simp only [Equiv.coe_fn_mk, map_mul]; ring)

end gen

end X4EE

end

noncomputable section

namespace X4EE
open Matrix Real QAlgorithms X7Y10EH X4ED
open scoped Matrix ComplexConjugate ComplexOrder
open QAlgorithms.Papers.Independent.Dependency50.P41 (qubitErasure)
open QAlgorithms.Papers.Independent.Information100.P62 (tensorChannel)
open QAlgorithms.Papers.Independent.Claimed50.P24
open QAlgorithms.Papers.Independent.Information100.P67
  (receiverChannel complementaryChannel erasureDilation)

attribute [local instance] Classical.propDecidable Classical.decEq

def fO : Option (Fin 2) ≃ Fin 3 where
  toFun o := o.elim 2 (fun i => ⟨i.val, by omega⟩)
  invFun x := if h : x.val < 2 then some ⟨x.val, h⟩ else none
  left_inv o := by rcases o with _ | i <;> [rfl; (fin_cases i <;> rfl)]
  right_inv x := by fin_cases x <;> rfl

lemma rec1 (ε : ℝ) (h0 : 0 ≤ ε) (h1 : ε ≤ 1) (σ : Matrix (Fin 2) (Fin 2) ℂ) :
    receiverChannel (erasureDilation (A := Fin 2) ε) σ = (qubitErasure ε σ).submatrix fO fO := by
  rw [X4EP.rec_eq ε h0 h1]
  ext b b'
  rcases b with _ | i <;> rcases b' with _ | j <;> (try fin_cases i) <;> (try fin_cases j) <;>
    simp [X4EP.Jo, X4EP.fl, pureDensity, Matrix.mul_apply, conjTranspose_apply, Fintype.sum_option,
      X7Y10EH.qe_apply, fO, Matrix.trace, Fin.sum_univ_two, PiLp.single_apply] <;> ring

lemma comp1 (ε : ℝ) (h0 : 0 ≤ ε) (h1 : ε ≤ 1) (σ : Matrix (Fin 2) (Fin 2) ℂ) :
    complementaryChannel (erasureDilation (A := Fin 2) ε) σ = (qubitErasure (1 - ε) σ).submatrix fO fO := by
  rw [X4EP.comp_eq ε h0 h1]
  ext b b'
  rcases b with _ | i <;> rcases b' with _ | j <;> (try fin_cases i) <;> (try fin_cases j) <;>
    simp [X4EP.Jo, X4EP.fl, pureDensity, Matrix.mul_apply, conjTranspose_apply, Fintype.sum_option,
      X7Y10EH.qe_apply, fO, Matrix.trace, Fin.sum_univ_two, PiLp.single_apply]

def fOO : Option (Fin 2) × Option (Fin 2) ≃ Fin 3 × Fin 3 := Equiv.prodCongr fO fO

abbrev V2 (ε : ℝ) := productDilation (erasureDilation (A := Fin 2) ε) (erasureDilation (A := Fin 2) ε)

lemma rec2 (ε : ℝ) (h0 : 0 ≤ ε) (h1 : ε ≤ 1) (X : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) :
    receiverChannel (V2 ε) X = (T2 ε X).submatrix fOO fOO := by
  rw [rec_prod]
  ext a b
  simp only [tensorChannel, rec1 ε h0 h1, Matrix.submatrix_apply, fOO, Equiv.prodCongr_apply, Prod.map]
  congr!

lemma comp2 (ε : ℝ) (h0 : 0 ≤ ε) (h1 : ε ≤ 1) (X : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) :
    complementaryChannel (V2 ε) X = (T2 (1 - ε) X).submatrix fOO fOO := by
  rw [comp_prod]
  ext a b
  simp only [tensorChannel, comp1 ε h0 h1, Matrix.submatrix_apply, fOO, Equiv.prodCongr_apply, Prod.map]
  congr!

lemma T2_herm (ε : ℝ) (ρ : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) (h : IsDensityMatrix ρ) :
    (T2 ε ρ).IsHermitian := by
  obtain ⟨hXH, -⟩ := X7_idT_herm_tr (R := Fin 2) ε ρ h
  obtain ⟨hYH, -⟩ := X7_N_herm_tr ε _ (X7_trL_dens ρ h)
  have k1 := g68i_herm_smul _ (1 - ε) (fun _ => hXH)
  have k2 := g68i_herm_smul _ ε (fun _ => hYH)
  show (tensorChannel _ _ ρ).IsHermitian
  rw [X7_T_block]
  exact (Matrix.IsHermitian.fromBlocks k1 (by simp) k2).submatrix _

lemma R2 (ε : ℝ) (h0 : 0 ≤ ε) (h1 : ε ≤ 1) (ρ : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)
    (h : IsDensityMatrix ρ) :
    vnEntropy (receiverChannel (V2 ε) ρ) = 2 * hf ε + (1 - ε) ^ 2 * vnEntropy ρ + ε * (1 - ε) * uu ρ := by
  rw [rec2 ε h0 h1, X7_ent_submatrix _ _ (T2_herm ε ρ h)]
  show vnEntropy (tensorChannel _ _ ρ) = _
  rw [X7_T_entropy ε h0 h1 ρ h]
  simp only [hf, uu]

lemma E2 (ε : ℝ) (h0 : 0 ≤ ε) (h1 : ε ≤ 1) (ρ : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)
    (h : IsDensityMatrix ρ) :
    vnEntropy (complementaryChannel (V2 ε) ρ) = 2 * hf ε + ε ^ 2 * vnEntropy ρ + ε * (1 - ε) * uu ρ := by
  rw [comp2 ε h0 h1, X7_ent_submatrix _ _ (T2_herm (1 - ε) ρ h)]
  show vnEntropy (tensorChannel _ _ ρ) = _
  rw [X7_T_entropy (1 - ε) (by linarith) (by linarith) ρ h]
  simp only [hf, uu, sub_sub_cancel]
  ring

end X4EE

end


-- ===== ERW =====

/-! `boundaryEnsemble ν` is valid with `I₁ = 1` and `I₂ = h₂(ν)`. -/

noncomputable section

namespace X4EW
open Matrix Real QAlgorithms X4EP X4EQ
open scoped Matrix ComplexConjugate ComplexOrder
open QAlgorithms.Papers.Independent.Claimed50.P24

attribute [local instance] Classical.propDecidable Classical.decEq

lemma ket_norm (y : Fin 2) : ‖ket y‖ = 1 := by simp [ket]

lemma bvalid (ν : ℝ) (h0 : 0 ≤ ν) (h1 : ν ≤ 1) : (boundaryEnsemble ν).Valid := by
  refine ⟨by norm_num, by norm_num, ?_, ?_, ?_⟩
  · intro x y; simp only [boundaryEnsemble]; split_ifs <;> linarith
  · change (∑ x : Fin 2, ∑ y : Fin 2, if x = y then ν / 2 else (1 - ν) / 2) = 1
    simp only [Fin.sum_univ_two]; norm_num; ring
  · intro x y
    exact ⟨X4EB.pd_psd _, X4EB.pd_trace _ (ket_norm y)⟩

lemma bpx (ν : ℝ) (x : Fin (boundaryEnsemble ν).nx) : (boundaryEnsemble ν).px x = 1 / 2 := by
  change (∑ y : Fin 2, if x = y then ν / 2 else (1 - ν) / 2) = 1 / 2
  rw [Fin.sum_univ_two]
  fin_cases x <;> simp <;> ring

lemma bavg (ν : ℝ) : (boundaryEnsemble ν).average = diagonal fun _ => ((1 / 2 : ℝ) : ℂ) := by
  ext a b
  change (∑ x : Fin 2, ∑ y : Fin 2,
    (((if x = y then ν / 2 else (1 - ν) / 2 : ℝ) : ℂ) • pureDensity (ket y))) a b = _
  simp only [Fin.sum_univ_two, Matrix.add_apply, Matrix.smul_apply]
  fin_cases a <;> fin_cases b <;> simp [pureDensity, ket, diagonal] <;> push_cast <;> ring

lemma binX (ν : ℝ) (x : Fin (boundaryEnsemble ν).nx) :
    (boundaryEnsemble ν).inputX x =
      diagonal fun y : Fin 2 => (((if x.val = y.val then ν else 1 - ν) : ℝ) : ℂ) := by
  have hpx := bpx ν x
  rw [TwoLabelEnsemble.inputX, if_neg (by rw [hpx]; norm_num), hpx]
  ext a b
  change (∑ y : Fin 2, (((if x = y then ν / 2 else (1 - ν) / 2 : ℝ) / (1 / 2) : ℝ) : ℂ) •
    pureDensity (ket y)) a b = _
  simp only [Fin.sum_univ_two, Matrix.add_apply, Matrix.smul_apply]
  have hx : x.val < 2 := x.isLt
  obtain ⟨xv, hxv⟩ := x
  interval_cases xv <;> fin_cases a <;> fin_cases b <;>
    simp [pureDensity, ket, diagonal] <;> push_cast <;> ring

lemma half_ent : vnEntropy (diagonal fun _ : Fin 2 => ((1 / 2 : ℝ) : ℂ)) = 1 := by
  rw [X4LE.vn_diag, Fin.sum_univ_two]
  rw [show (1 / 2 : ℝ) = 2⁻¹ by norm_num, Real.logb_inv, Real.logb_self_eq_one (by norm_num)]
  ring

theorem bnd (ν : ℝ) (h0 : 0 ≤ ν) (h1 : ν ≤ 1) :
    (boundaryEnsemble ν).Valid ∧ I1 (boundaryEnsemble ν) = 1 ∧
      I2 (boundaryEnsemble ν) = binEntropy2 ν := by
  have hS : ∀ x y, vnEntropy ((boundaryEnsemble ν).state x y) = 0 := fun x y =>
    X4ER.vn_pure _ (ket_norm y)
  have hS' : ∀ y : Fin 2, vnEntropy (pureDensity (ket y)) = 0 := fun y => X4ER.vn_pure _ (ket_norm y)
  refine ⟨bvalid ν h0 h1, ?_, ?_⟩
  · simp only [I1, hS, hS', mul_zero, Finset.sum_const_zero, sub_zero, bavg, half_ent]
  · simp only [I2, hS, hS', mul_zero, Finset.sum_const_zero, sub_zero]
    have : ∀ x, vnEntropy ((boundaryEnsemble ν).inputX x) = binEntropy2 ν := by
      intro x
      rw [binX, X4LE.vn_diag, Fin.sum_univ_two, binEntropy2]
      simp only [Real.binEntropy, Real.log_inv, Real.logb]
      obtain ⟨xv, hxv⟩ := x
      change xv < 2 at hxv
      interval_cases xv <;> simp <;> ring
    simp only [this, bpx]
    erw [Fin.sum_univ_two]; ring

end X4EW

end

-- ===== EEB =====

/-! Claimed50.P24 Lemma 10: two equal erasure channels, closed form of the dynamic objective on
two-label ensembles over `Fin 2 × Fin 2`, its maximum, and additivity. -/

noncomputable section

namespace X4EE
open Matrix Real QAlgorithms X7Y10EH X4ED
open scoped Matrix ComplexConjugate ComplexOrder
open QAlgorithms.Papers.Independent.Claimed50.P24
open QAlgorithms.Papers.Independent.Information100.P67
  (receiverChannel complementaryChannel erasureDilation)

attribute [local instance] Classical.propDecidable Classical.decEq

variable {A : TwoLabelEnsemble (Fin 2 × Fin 2)}

lemma px_sum (hA : A.Valid) : ∑ x, A.px x = 1 := hA.2.2.2.1

lemma px_nonneg (hA : A.Valid) (x : Fin A.nx) : 0 ≤ A.px x :=
  Finset.sum_nonneg fun y _ => hA.2.2.1 x y

lemma avg_dens (hA : A.Valid) : IsDensityMatrix A.average := by
  refine ⟨posSemidef_sum _ fun x _ => posSemidef_sum _ fun y _ =>
    X4EB.smul_psd (hA.2.2.2.2 x y).1 (hA.2.2.1 x y), ?_⟩
  rw [TwoLabelEnsemble.average, Matrix.trace_sum]
  simp only [Matrix.trace_sum, Matrix.trace_smul, (fun x y => (hA.2.2.2.2 x y).2), smul_eq_mul, mul_one]
  exact_mod_cast hA.2.2.2.1

lemma inX_dens (hA : A.Valid) (x : Fin A.nx) : IsDensityMatrix (A.inputX x) := by
  unfold TwoLabelEnsemble.inputX
  split_ifs with h
  · exact ⟨X4EB.pd_psd _, X4EB.pd_trace _ (by simp [ket])⟩
  · have hpos : 0 < A.px x := lt_of_le_of_ne (px_nonneg hA x) (Ne.symm h)
    refine ⟨posSemidef_sum _ fun y _ =>
      X4EB.smul_psd (hA.2.2.2.2 x y).1 (div_nonneg (hA.2.2.1 x y) hpos.le), ?_⟩
    rw [Matrix.trace_sum]
    simp only [Matrix.trace_smul, (fun y => (hA.2.2.2.2 x y).2), smul_eq_mul, mul_one]
    rw [← Complex.ofReal_sum, ← Finset.sum_div]
    have : ∑ y, A.prob x y = A.px x := rfl
    rw [this, div_self h]; simp

lemma dsum3 {m n : ℕ} (f g k : Fin m → Fin n → ℝ) (a b c : ℝ) :
    ∑ x, ∑ y, f x y * (a + b * g x y + c * k x y) =
      a * ∑ x, ∑ y, f x y + b * ∑ x, ∑ y, f x y * g x y + c * ∑ x, ∑ y, f x y * k x y := by
  simp only [mul_add, Finset.sum_add_distrib, Finset.mul_sum]
  congr 1; congr 1
  all_goals refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => by ring

lemma ssum3 {m : ℕ} (f g k : Fin m → ℝ) (a b c : ℝ) :
    ∑ x, f x * (a + b * g x + c * k x) = a * ∑ x, f x + b * ∑ x, f x * g x + c * ∑ x, f x * k x := by
  simp only [mul_add, Finset.sum_add_distrib, Finset.mul_sum]
  congr 1; congr 1
  all_goals refine Finset.sum_congr rfl fun x _ => by ring

variable (A)
def Bv : ℝ := ∑ x, A.px x * vnEntropy (A.inputX x)
def B12 : ℝ := ∑ x, A.px x * uu (A.inputX x)
def Cc : ℝ := ∑ x, ∑ y, A.prob x y * vnEntropy (A.state x y)
def C12 : ℝ := ∑ x, ∑ y, A.prob x y * uu (A.state x y)
variable {A}

theorem obj2 (ε lam mu : ℝ) (h0 : 0 ≤ ε) (h1 : ε ≤ 1) (hA : A.Valid) :
    dynamicObjective (V2 ε) lam mu A =
      (1 + mu) * ((1 - ε) ^ 2 * (vnEntropy A.average - Cc A) + ε * (1 - ε) * (uu A.average - C12 A)) +
      lam * (1 - 2 * ε) * (Bv A - Cc A) - mu * (ε ^ 2 * (Bv A - Cc A) + ε * (1 - ε) * (B12 A - C12 A)) := by
  have htot : ∑ x, ∑ y, A.prob x y = 1 := hA.2.2.2.1
  have hpx := px_sum hA
  have hR : ∀ x y, vnEntropy (receiverChannel (V2 ε) (A.state x y)) =
      2 * hf ε + (1 - ε) ^ 2 * vnEntropy (A.state x y) + ε * (1 - ε) * uu (A.state x y) := fun x y =>
    R2 ε h0 h1 _ (hA.2.2.2.2 x y)
  have hE : ∀ x y, vnEntropy (complementaryChannel (V2 ε) (A.state x y)) =
      2 * hf ε + ε ^ 2 * vnEntropy (A.state x y) + ε * (1 - ε) * uu (A.state x y) := fun x y =>
    E2 ε h0 h1 _ (hA.2.2.2.2 x y)
  have hRX : ∀ x, vnEntropy (receiverChannel (V2 ε) (A.inputX x)) =
      2 * hf ε + (1 - ε) ^ 2 * vnEntropy (A.inputX x) + ε * (1 - ε) * uu (A.inputX x) := fun x =>
    R2 ε h0 h1 _ (inX_dens hA x)
  have hEX : ∀ x, vnEntropy (complementaryChannel (V2 ε) (A.inputX x)) =
      2 * hf ε + ε ^ 2 * vnEntropy (A.inputX x) + ε * (1 - ε) * uu (A.inputX x) := fun x =>
    E2 ε h0 h1 _ (inX_dens hA x)
  have hB := R2 ε h0 h1 _ (avg_dens hA)
  have a1 : infoXYB (V2 ε) A = (1 - ε) ^ 2 * (vnEntropy A.average - Cc A) +
      ε * (1 - ε) * (uu A.average - C12 A) := by
    simp only [infoXYB, entropyB, hB, hR]; rw [dsum3, htot]; unfold Cc C12; ring
  have a2 : infoYBX (V2 ε) A = (1 - ε) ^ 2 * (Bv A - Cc A) + ε * (1 - ε) * (B12 A - C12 A) := by
    simp only [infoYBX, entropyBX, hRX, hR]; rw [dsum3, ssum3, htot, hpx]; unfold Bv B12 Cc C12; ring
  have a3 : infoYEX (V2 ε) A = ε ^ 2 * (Bv A - Cc A) + ε * (1 - ε) * (B12 A - C12 A) := by
    simp only [infoYEX, entropyEX, hEX, hE]; rw [dsum3, ssum3, htot, hpx]; unfold Bv B12 Cc C12; ring
  simp only [dynamicObjective, a1, a2, a3]; ring

lemma Cc_le_Bv (hA : A.Valid) : Cc A ≤ Bv A := by
  unfold Cc Bv
  refine Finset.sum_le_sum fun x _ => ?_
  by_cases h : A.px x = 0
  · have hz : ∀ y, A.prob x y = 0 := fun y =>
      (Finset.sum_eq_zero_iff_of_nonneg (fun y _ => hA.2.2.1 x y)).1 h y (Finset.mem_univ y)
    simp [hz, h]
  · have hpos : 0 < A.px x := lt_of_le_of_ne (px_nonneg hA x) (Ne.symm h)
    have hc := X4EP.concave (fun y => A.prob x y / A.px x) (fun y => A.state x y)
      (fun y => div_nonneg (hA.2.2.1 x y) hpos.le)
      (by rw [← Finset.sum_div]; exact div_self h)
      (fun y => (hA.2.2.2.2 x y).1) (fun y => (hA.2.2.2.2 x y).2)
    have hin : A.inputX x = ∑ y, ((A.prob x y / A.px x : ℝ) : ℂ) • A.state x y := by
      simp [TwoLabelEnsemble.inputX, h]
    rw [hin]
    calc ∑ y, A.prob x y * vnEntropy (A.state x y)
        = A.px x * ∑ y, A.prob x y / A.px x * vnEntropy (A.state x y) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun y _ => by field_simp
      _ ≤ A.px x * vnEntropy (∑ y, ((A.prob x y / A.px x : ℝ) : ℂ) • A.state x y) :=
          mul_le_mul_of_nonneg_left hc hpos.le

theorem upper2 (ε lam mu : ℝ) (h0 : 0 ≤ ε) (h1 : ε ≤ 1) (hmu : 0 ≤ mu) (hA : A.Valid) :
    dynamicObjective (V2 ε) lam mu A ≤
      2 * ((1 + mu) * (1 - ε) + max (lam * (1 - 2 * ε) - mu * ε) 0) := by
  rw [obj2 ε lam mu h0 h1 hA]
  set c := lam * (1 - 2 * ε) - mu * ε
  have hpx := px_sum hA
  have hS := sub_le _ (avg_dens hA)
  have hS2 := uu_le _ (avg_dens hA)
  have hC0 : 0 ≤ Cc A := Finset.sum_nonneg fun x _ => Finset.sum_nonneg fun y _ =>
    mul_nonneg (hA.2.2.1 x y) (X4ES.ent_nonneg (hA.2.2.2.2 x y).1 (hA.2.2.2.2 x y).2)
  have hCC : Cc A ≤ C12 A := Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun y _ =>
    mul_le_mul_of_nonneg_left (sub_le _ (hA.2.2.2.2 x y)) (hA.2.2.1 x y)
  have hBB : Bv A ≤ B12 A := Finset.sum_le_sum fun x _ =>
    mul_le_mul_of_nonneg_left (sub_le _ (inX_dens hA x)) (px_nonneg hA x)
  have hB2 : Bv A ≤ 2 := by
    calc Bv A ≤ ∑ x, A.px x * 2 := Finset.sum_le_sum fun x _ =>
          mul_le_mul_of_nonneg_left ((sub_le _ (inX_dens hA x)).trans (uu_le _ (inX_dens hA x)))
            (px_nonneg hA x)
      _ = 2 := by rw [← Finset.sum_mul, hpx, one_mul]
  have hCB := Cc_le_Bv hA
  have q1 : 0 ≤ (1 + mu) * (1 - ε) ^ 2 * (uu A.average - vnEntropy A.average) :=
    mul_nonneg (by positivity) (by linarith)
  have q2 : 0 ≤ (1 + mu) * (1 - ε) * (2 - uu A.average) :=
    mul_nonneg (mul_nonneg (by linarith) (by linarith)) (by linarith)
  have q3 : 0 ≤ mu * ε * (1 - ε) * (B12 A - Bv A) :=
    mul_nonneg (mul_nonneg (mul_nonneg hmu h0) (by linarith)) (by linarith)
  have q4 : 0 ≤ ε * (1 - ε) * (C12 A - Cc A) := mul_nonneg (mul_nonneg h0 (by linarith)) (by linarith)
  have q5 : 0 ≤ (1 + mu) * (1 - ε) * Cc A := mul_nonneg (mul_nonneg (by linarith) (by linarith)) hC0
  have q6 : 0 ≤ max c 0 * (2 - (Bv A - Cc A)) := mul_nonneg (le_max_right _ _) (by linarith)
  have q7 : 0 ≤ (max c 0 - c) * (Bv A - Cc A) := mul_nonneg (by linarith [le_max_left c 0]) (by linarith)
  nlinarith [q1, q2, q3, q4, q5, q6, q7]

end X4EE

end


-- ===== EEC =====

/-! Claimed50.P24 Lemma 10: optimal two-use ensembles and additivity. -/

noncomputable section

namespace X4EE
open Matrix Real QAlgorithms X7Y10EH X4ED
open scoped Matrix ComplexConjugate ComplexOrder
open QAlgorithms.Papers.Independent.Claimed50.P24
open QAlgorithms.Papers.Independent.Information100.P67
  (receiverChannel complementaryChannel erasureDilation)

attribute [local instance] Classical.propDecidable Classical.decEq

lemma cs (r : ℝ) (M : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) : ((r : ℝ) : ℂ) • M = r • M := by
  ext; simp

lemma sumD4 : ∑ x : Fin 4, (1 / 4 : ℝ) • tau eC x = D4 := eC_taub

/-- `|ab⟩` labelled by `y`, a single `x`. -/
def eQ : TwoLabelEnsemble (Fin 2 × Fin 2) where
  nx := 1
  ny := 4
  prob := fun _ _ => 1 / 4
  state := fun _ y => tau eC y

/-- `|ab⟩` labelled by `x`, a single `y`. -/
def eK : TwoLabelEnsemble (Fin 2 × Fin 2) where
  nx := 4
  ny := 1
  prob := fun _ _ => 1 / 4
  state := fun x _ => tau eC x

lemma eQ_valid : eQ.Valid :=
  ⟨by norm_num [eQ], by norm_num [eQ], fun _ _ => show (0 : ℝ) ≤ 1 / 4 by norm_num,
    show ∑ x : Fin 1, ∑ y : Fin 4, (1 / 4 : ℝ) = 1 by simp,
    fun _ y => tau_dens eC y⟩

lemma eK_valid : eK.Valid :=
  ⟨by norm_num [eK], by norm_num [eK], fun _ _ => show (0 : ℝ) ≤ 1 / 4 by norm_num,
    show ∑ x : Fin 4, ∑ y : Fin 1, (1 / 4 : ℝ) = 1 by simp,
    fun x _ => tau_dens eC x⟩

lemma eQ_px (x : Fin eQ.nx) : eQ.px x = 1 := by
  show ∑ y : Fin 4, (1 / 4 : ℝ) = 1
  simp

lemma eK_px (x : Fin eK.nx) : eK.px x = 1 / 4 := by
  show ∑ y : Fin 1, (1 / 4 : ℝ) = 1 / 4
  simp

lemma eQ_inX (x : Fin eQ.nx) : eQ.inputX x = D4 := by
  rw [TwoLabelEnsemble.inputX, if_neg (by rw [eQ_px]; norm_num)]
  simp only [eQ_px, div_one, cs]
  exact sumD4

lemma eK_inX (x : Fin eK.nx) : eK.inputX x = tau eC x := by
  rw [TwoLabelEnsemble.inputX, if_neg (by rw [eK_px]; norm_num)]
  simp only [eK_px, cs]
  change ∑ y : Fin 1, ((1 / 4 : ℝ) / (1 / 4)) • tau eC x = tau eC x
  simp

lemma eQ_avg : eQ.average = D4 := by
  change ∑ x : Fin 1, ∑ y : Fin 4, (((1 / 4 : ℝ) : ℝ) : ℂ) • tau eC y = D4
  simp only [cs, Fin.sum_univ_one]
  exact sumD4

lemma eK_avg : eK.average = D4 := by
  change ∑ x : Fin 4, ∑ y : Fin 1, (((1 / 4 : ℝ) : ℝ) : ℂ) • tau eC x = D4
  simp only [cs, Fin.sum_univ_one]
  exact sumD4

theorem eQ_obj (ε lam mu : ℝ) (h0 : 0 ≤ ε) (h1 : ε ≤ 1) :
    dynamicObjective (V2 ε) lam mu eQ = 2 * ((1 + mu) * (1 - ε) + (lam * (1 - 2 * ε) - mu * ε)) := by
  rw [obj2 ε lam mu h0 h1 eQ_valid, eQ_avg, D4_ent, D4_uu]
  have hB : Bv eQ = 2 := by
    unfold Bv
    rw [Finset.sum_congr rfl (fun x _ => by rw [eQ_inX, eQ_px, D4_ent, one_mul])]
    change ∑ x : Fin 1, (2 : ℝ) = 2
    simp
  have hB2 : B12 eQ = 2 := by
    unfold B12
    rw [Finset.sum_congr rfl (fun x _ => by rw [eQ_inX, eQ_px, D4_uu, one_mul])]
    change ∑ x : Fin 1, (2 : ℝ) = 2
    simp
  have hC : Cc eQ = 0 := by
    simp only [Cc]; refine Finset.sum_eq_zero fun x _ => Finset.sum_eq_zero fun y _ => ?_
    simp [eQ, (eC_vals y).1]
  have hC2 : C12 eQ = 0 := by
    simp only [C12]; refine Finset.sum_eq_zero fun x _ => Finset.sum_eq_zero fun y _ => ?_
    simp [eQ, (eC_vals y).2]
  rw [hB, hB2, hC, hC2]; ring

theorem eK_obj (ε lam mu : ℝ) (h0 : 0 ≤ ε) (h1 : ε ≤ 1) :
    dynamicObjective (V2 ε) lam mu eK = 2 * ((1 + mu) * (1 - ε)) := by
  rw [obj2 ε lam mu h0 h1 eK_valid, eK_avg, D4_ent, D4_uu]
  have hB : Bv eK = 0 := by
    simp only [Bv]; refine Finset.sum_eq_zero fun x _ => ?_
    rw [eK_inX, (eC_vals x).1, mul_zero]
  have hB2 : B12 eK = 0 := by
    simp only [B12]; refine Finset.sum_eq_zero fun x _ => ?_
    rw [eK_inX, (eC_vals x).2, mul_zero]
  have hC : Cc eK = 0 := by
    simp only [Cc]; refine Finset.sum_eq_zero fun x _ => Finset.sum_eq_zero fun y _ => ?_
    simp [eK, (eC_vals x).1]
  have hC2 : C12 eK = 0 := by
    simp only [C12]; refine Finset.sum_eq_zero fun x _ => Finset.sum_eq_zero fun y _ => ?_
    simp [eK, (eC_vals x).2]
  rw [hB, hB2, hC, hC2]; ring

open X4EQ X4EW in
theorem one (ε lam mu : ℝ) (h0 : 0 ≤ ε) (h1 : ε ≤ 1) (hmu : 0 ≤ mu) :
    IsGreatest (values (dynamicObjective (erasureDilation (A := Fin 2) ε) lam mu))
      ((1 + mu) * (1 - ε) + max (lam * (1 - 2 * ε) - mu * ε) 0) := by
  set c := lam * (1 - 2 * ε) - mu * ε
  have hk : 0 ≤ (1 + mu) * (1 - ε) := mul_nonneg (by linarith) (by linarith)
  have hb0 : binEntropy2 0 = 0 := X4ES.bin_zero
  have hbh : binEntropy2 (1 / 2) = 1 := X4ES.bin_half
  by_cases hc : c < 0
  · rw [max_eq_right hc.le, add_zero]
    obtain ⟨hv0, hI10, hI20⟩ := bnd 0 le_rfl zero_le_one
    refine ⟨⟨boundaryEnsemble 0, hv0, ?_⟩, ?_⟩
    · rw [(obj_eq ε lam mu h0 h1 hv0).2.2.2, hI10, hI20, hb0]; ring
    · rintro v ⟨A, hA, rfl⟩
      rw [(obj_eq ε lam mu h0 h1 hA).2.2.2]
      nlinarith [mul_le_mul_of_nonneg_left (I1_le hA) hk,
        mul_nonpos_of_nonpos_of_nonneg hc.le (I2_nonneg hA)]
  · push Not at hc
    rw [max_eq_left hc]
    obtain ⟨hv, hI1, hI2⟩ := bnd (1 / 2) (by norm_num) (by norm_num)
    refine ⟨⟨boundaryEnsemble (1 / 2), hv, ?_⟩, ?_⟩
    · rw [(obj_eq ε lam mu h0 h1 hv).2.2.2, hI1, hI2, hbh]; ring
    · rintro v ⟨A, hA, rfl⟩
      rw [(obj_eq ε lam mu h0 h1 hA).2.2.2]
      nlinarith [mul_le_mul_of_nonneg_left (I1_le hA) hk,
        mul_le_mul_of_nonneg_left (I2_le hA) hc]

theorem two (ε lam mu : ℝ) (h0 : 0 ≤ ε) (h1 : ε ≤ 1) (hmu : 0 ≤ mu) :
    IsGreatest (values (dynamicObjective (V2 ε) lam mu))
      (2 * ((1 + mu) * (1 - ε) + max (lam * (1 - 2 * ε) - mu * ε) 0)) := by
  refine ⟨?_, ?_⟩
  · by_cases hc : 0 ≤ lam * (1 - 2 * ε) - mu * ε
    · exact ⟨eQ, eQ_valid, by rw [eQ_obj ε lam mu h0 h1, max_eq_left hc]⟩
    · exact ⟨eK, eK_valid, by rw [eK_obj ε lam mu h0 h1, max_eq_right (le_of_not_ge hc), add_zero]⟩
  · rintro v ⟨A, hA, rfl⟩
    exact upper2 ε lam mu h0 h1 hmu hA

theorem main (ε lam mu : ℝ) (h0 : 0 ≤ ε) (h1 : ε ≤ 1) (hmu : 0 ≤ mu) :
    AdditiveMax (values (dynamicObjective (erasureDilation (A := Fin 2) ε) lam mu))
      (values (dynamicObjective (erasureDilation (A := Fin 2) ε) lam mu))
      (values (dynamicObjective (V2 ε) lam mu)) := by
  refine ⟨_, _, one ε lam mu h0 h1 hmu, one ε lam mu h0 h1 hmu, ?_⟩
  convert two ε lam mu h0 h1 hmu using 1
  ring

end X4EE

end


-- ===== EESol =====

noncomputable section

open scoped Matrix ComplexConjugate
open QAlgorithms.Papers.Independent.Claimed50.P24
open QAlgorithms.Papers.Independent.Information100.P67
  (IsIsometry receiverChannel complementaryChannel erasureDilation)

attribute [local instance] Classical.propDecidable Classical.decEq

theorem solution (eps lam mu : ℝ) (he0 : 0 ≤ eps) (he1 : eps ≤ 1)
    (hlam : 0 ≤ lam) (hmu : 0 ≤ mu) :
    AdditiveMax (values (dynamicObjective (erasureDilation (A := Fin 2) eps) lam mu))
      (values (dynamicObjective (erasureDilation (A := Fin 2) eps) lam mu))
      (values (dynamicObjective
        (productDilation (erasureDilation (A := Fin 2) eps) (erasureDilation (A := Fin 2) eps)) lam mu)) :=
  X4EE.main eps lam mu he0 he1 hmu

end

