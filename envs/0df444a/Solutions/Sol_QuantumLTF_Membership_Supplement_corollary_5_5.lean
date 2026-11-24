-- Prove2me | solution 1 for QuantumLTF.Membership.Supplement.corollary_5_5
-- status  : ACCEPTED   (prove)
-- author  : @stockfish-soup
-- created : 2026-11-24T19:53:17.257116+00:00
-- url     : https://prove2.me/submissions/2a0863fd-81a0-4fe4-8cf1-dad6732aa3d9

import Mathlib
import Definitions.Def_QAlgorithms_Defs_MatrixDistances
import Theorems.Thm_BenyOreshkov_AQEC_traceNorm_dual
import Theorems.Thm_QAlgorithms_Papers_Independent_Frontier30_P28_trace_norm_contraction
import Definitions.Def_QuantumLTF_Membership_Supplement_padKet
import Definitions.Def_QuantumLTF_Membership_Supplement_measChannelOut
import Theorems.Thm_QuantumLTF_Membership_Supplement_hermite_band_bounds_53
import Definitions.Def_QuantumLTF_Membership_Supplement_dirTensorPow

set_option autoImplicit false
set_option linter.unusedSimpArgs false

open scoped Matrix ComplexOrder MatrixOrder

noncomputable def section5_reindex_hom {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β] (e : α ≃ β) :
    Matrix α α ℂ ≃⋆ₐ[ℂ] Matrix β β ℂ :=
  { Matrix.reindexAlgEquiv ℂ ℂ e with
    map_smul' := by intro r A; ext i j; rfl
    map_star' := by intro A; ext i j; rfl }

theorem section5_trace_size_reindex {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β] (e : α ≃ β) (A : Matrix α α ℂ) :
    (cfc Real.sqrt ((A.submatrix e.symm e.symm).conjTranspose *
      A.submatrix e.symm e.symm)).trace.re =
      (cfc Real.sqrt (A.conjTranspose * A)).trace.re := by
  let F := section5_reindex_hom e
  have hmul : (A.submatrix e.symm e.symm).conjTranspose * A.submatrix e.symm e.symm =
      F (A.conjTranspose * A) := by
    exact (F.map_mul (star A) A).symm.trans (by rfl)
  rw [hmul]
  have hfc : F (cfc Real.sqrt (A.conjTranspose * A)) = cfc Real.sqrt (F (A.conjTranspose * A)) :=
    F.toStarAlgHom.map_cfc Real.sqrt (A.conjTranspose * A)
      Real.continuous_sqrt.continuousOn F.toAlgEquiv.toLinearMap.continuous_of_finiteDimensional
      (by change star (star A * A) = star A * A; simp)
      (by change star (F (star A * A)) = F (star A * A)
          rw [← map_star]; congr 1; simp)
  rw [← hfc]
  exact congrArg Complex.re (Equiv.sum_comp e.symm
    (fun i : α => cfc Real.sqrt (A.conjTranspose * A) i i))

theorem section5_trace_size_diagonal {α : Type*} [Fintype α] [DecidableEq α] (r : α → ℝ) :
    (cfc Real.sqrt ((Matrix.diagonal (fun i => (r i : ℂ))).conjTranspose *
      Matrix.diagonal (fun i => (r i : ℂ)))).trace.re = ∑ i, |r i| := by
  have hm : (Matrix.diagonal (fun i => (r i : ℂ))).conjTranspose *
      Matrix.diagonal (fun i => (r i : ℂ)) =
        Matrix.diagonal (fun i => (((r i)^2 : ℝ) : ℂ)) := by
    simp [Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal, pow_two]
  rw [hm]
  have hdiag : cfc Real.sqrt (Matrix.diagonal (fun i => (((r i)^2 : ℝ) : ℂ))) =
      Matrix.diagonal (fun i => ((|r i| : ℝ) : ℂ)) := by
    have hA : 0 ≤ Matrix.diagonal (fun i : α => (((r i)^2 : ℝ) : ℂ)) :=
      (Matrix.PosSemidef.diagonal (fun i => by
        change (0 : ℂ) ≤ (((r i)^2 : ℝ) : ℂ)
        exact Complex.zero_le_real.mpr (sq_nonneg (r i)))).nonneg
    have hB : 0 ≤ Matrix.diagonal (fun i : α => ((|r i| : ℝ) : ℂ)) :=
      (Matrix.PosSemidef.diagonal (fun i => by
        change (0 : ℂ) ≤ ((|r i| : ℝ) : ℂ)
        exact Complex.zero_le_real.mpr (abs_nonneg (r i)))).nonneg
    have hcfc : CFC.sqrt (Matrix.diagonal (fun i : α => (((r i)^2 : ℝ) : ℂ))) =
        cfc Real.sqrt (Matrix.diagonal (fun i : α => (((r i)^2 : ℝ) : ℂ))) := by
      rw [CFC.sqrt_eq_real_sqrt _ hA, cfcₙ_eq_cfc (hf0 := by simp)]
    rw [← hcfc]
    apply CFC.sqrt_unique (hb := hB)
    simp only [Matrix.diagonal_mul_diagonal, ← Complex.ofReal_mul]
    congr 1
    funext i
    congr 1
    exact (pow_two (|r i|)).symm.trans (sq_abs (r i))
  rw [hdiag]
  simp [Matrix.trace_diagonal, Real.sqrt_sq_eq_abs]


set_option autoImplicit false
open QAlgorithms
open scoped MatrixOrder ComplexOrder

theorem section5_traceNorm_wilde {ι : Type} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) : QAlgorithms.traceNorm A = WildeQIT.traceNorm A := by
  unfold QAlgorithms.traceNorm WildeQIT.traceNorm
  have hpos : 0 ≤ A.conjTranspose * A :=
    (Matrix.posSemidef_conjTranspose_mul_self A).nonneg
  rw [CFC.sqrt_eq_real_sqrt _ hpos, cfcₙ_eq_cfc (hf0 := by simp)]

theorem section5_unitary_act_norm {ι : Type} [Fintype ι] [DecidableEq ι]
    (U : Matrix ι ι ℂ) (hU : U ∈ Matrix.unitaryGroup ι ℂ)
    (x : EuclideanSpace ℂ ι) : ‖act U x‖ = ‖x‖ := by
  have huu : U.conjTranspose * U = 1 := by
    simpa only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_conjTranspose] using
      Matrix.mem_unitaryGroup_iff.mp (Unitary.star_mem hU)
  have hi : inner ℂ (act U x) (act U x) = inner ℂ x x := by
    simp only [EuclideanSpace.inner_eq_star_dotProduct, act, WithLp.ofLp_toLp]
    rw [Matrix.star_mulVec, dotProduct_comm, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul, huu,
      Matrix.vecMul_one]
    exact dotProduct_comm _ _
  have hn : ‖act U x‖^2 = ‖x‖^2 := by
    calc
      _ = (inner ℂ (act U x) (act U x)).re := norm_sq_eq_re_inner (𝕜 := ℂ) _
      _ = (inner ℂ x x).re := congrArg Complex.re hi
      _ = _ := (norm_sq_eq_re_inner (𝕜 := ℂ) x).symm
  nlinarith [norm_nonneg (act U x), norm_nonneg x]

noncomputable def section5_outer {ι : Type} (x y : EuclideanSpace ℂ ι) : Matrix ι ι ℂ :=
  fun i j => x i * star (y j)

theorem section5_outer_trace_mul {ι : Type} [Fintype ι]
    (x y : EuclideanSpace ℂ ι) (U : Matrix ι ι ℂ) :
    (section5_outer x y * U).trace = inner ℂ y (act U x) := by
  classical
  change (∑ i : ι, ∑ j : ι, x i * star (y j) * U j i) =
    ∑ i : ι, (∑ j : ι, U i j * x j) * star (y i)
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

theorem section5_pure_trace_distance {ι : Type} [Fintype ι] [DecidableEq ι]
    (x y : EuclideanSpace ℂ ι) (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) :
    QAlgorithms.traceNorm (section5_outer x x - section5_outer y y) / 2 ≤ ‖x-y‖ := by
  classical
  let D := section5_outer x x - section5_outer y y
  obtain ⟨U, hU, heq⟩ := (BenyOreshkov.AQEC.traceNorm_dual D).1.1
  have hdecomp : D = section5_outer (x-y) x + section5_outer y (x-y) := by
    ext i j
    change x i * star (x j) - y i * star (y j) =
      (x i-y i) * star (x j) + y i * star (x j-y j)
    rw [star_sub]
    ring
  have ht : (D * U).trace = inner ℂ x (act U (x-y)) + inner ℂ (x-y) (act U y) := by
    rw [hdecomp, add_mul, Matrix.trace_add, section5_outer_trace_mul,
      section5_outer_trace_mul]
  have hbound : ‖(D*U).trace‖ ≤ 2 * ‖x-y‖ := by
    rw [ht]
    calc
      _ ≤ ‖inner ℂ x (act U (x-y))‖ + ‖inner ℂ (x-y) (act U y)‖ := norm_add_le _ _
      _ ≤ ‖x‖ * ‖act U (x-y)‖ + ‖x-y‖ * ‖act U y‖ :=
        add_le_add (norm_inner_le_norm _ _) (norm_inner_le_norm _ _)
      _ = 2 * ‖x-y‖ := by rw [section5_unitary_act_norm U hU,
          section5_unitary_act_norm U hU, hx, hy]; ring
  rw [section5_traceNorm_wilde, heq]
  linarith


set_option autoImplicit false
open QAlgorithms
open scoped MatrixOrder ComplexOrder

theorem section5_channel_trace_contraction {α β : Type*}
    [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    [Nonempty α] [Nonempty β]
    (Φ : Matrix α α ℂ →ₗ[ℂ] Matrix β β ℂ)
    (hpos : ∀ A, A.PosSemidef → (Φ A).PosSemidef)
    (htrace : ∀ A, (Φ A).trace = A.trace)
    (A : Matrix α α ℂ) : traceNorm (Φ A) ≤ traceNorm A := by
  classical
  let ea := Fintype.equivFin α
  let eb := Fintype.equivFin β
  let Fa := section5_reindex_hom ea
  let Fb := section5_reindex_hom eb
  let T := Fb.toAlgEquiv.toLinearMap.comp
    (Φ.comp Fa.symm.toAlgEquiv.toLinearMap)
  have hposT : ∀ B, B.PosSemidef → (T B).PosSemidef := by
    intro B hB
    change ((Φ (B.submatrix ea ea)).submatrix eb.symm eb.symm).PosSemidef
    exact (hpos _ (hB.submatrix ea)).submatrix eb.symm
  have htraceT : ∀ B, (T B).trace = B.trace := by
    intro B
    change (∑ i, Φ (B.submatrix ea ea) (eb.symm i) (eb.symm i)) = B.trace
    exact (Equiv.sum_comp eb.symm (fun i : β => Φ (B.submatrix ea ea) i i)).trans
      ((htrace (B.submatrix ea ea)).trans (Equiv.sum_comp ea (fun i => B i i)))
  have hh := (QAlgorithms.Papers.Independent.Frontier30.P28.trace_norm_contraction
    (Fintype.card α) (Fintype.card β) Fintype.card_pos Fintype.card_pos T hposT htraceT).2
      (Fa A)
  have hT : T (Fa A) = Fb (Φ A) := by
    change Fb (Φ (Fa.symm (Fa A))) = _
    rw [Fa.symm_apply_apply]
  rw [hT] at hh
  have hnA : traceNorm (Fa A) = traceNorm A := section5_trace_size_reindex ea A
  have hnB : traceNorm (Fb (Φ A)) = traceNorm (Φ A) := section5_trace_size_reindex eb (Φ A)
  rwa [hnA, hnB] at hh

theorem section5_conversion_robustness {α β : Type}
    [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    [Nonempty α] [Nonempty β]
    (Φ : Matrix α α ℂ →ₗ[ℂ] Matrix β β ℂ)
    (hpos : ∀ A, A.PosSemidef → (Φ A).PosSemidef)
    (htrace : ∀ A, (Φ A).trace = A.trace)
    (x y : EuclideanSpace ℂ α) (hx : ‖x‖ = 1) (hy : ‖y‖ = 1)
    (σ : Matrix β β ℂ) (hexact : Φ (section5_outer y y) = σ) :
    traceNorm (Φ (section5_outer x x) - σ) / 2 ≤ ‖x-y‖ := by
  rw [← hexact, ← map_sub]
  have hh := section5_channel_trace_contraction Φ hpos htrace
    (section5_outer x x - section5_outer y y)
  exact (div_le_div_of_nonneg_right hh (by norm_num)).trans
    (section5_pure_trace_distance x y hx hy)


set_option autoImplicit false
open QAlgorithms QuantumLTF.Membership.Supplement

noncomputable def section5_append_equiv (N a : ℕ) :
    Qubits (N+a) ≃ Qubits N × Qubits a where
  toFun z := (fun i => z (Fin.castAdd a i), fun j => z (Fin.natAdd N j))
  invFun p := Fin.append p.1 p.2
  left_inv z := by
    funext i
    exact Fin.addCases (fun j => by simp) (fun j => by simp) i
  right_inv p := by
    ext i <;> simp

theorem section5_padKet_norm {N a : ℕ} (ψ : EuclideanSpace ℂ (Qubits N)) :
    ‖padKet a ψ‖ = ‖ψ‖ := by
  classical
  have hsq : ‖padKet a ψ‖^2 = ‖ψ‖^2 := by
    rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
    calc
      _ = ∑ p : Qubits N × Qubits a,
          if p.2 = (fun _ => false) then ‖ψ p.1‖^2 else 0 := by
        apply Fintype.sum_equiv (section5_append_equiv N a) _ _
        intro z
        by_cases h : ∀ j : Fin a, z (Fin.natAdd N j) = false
        · have he : ((section5_append_equiv N a) z).2 = (fun _ => false) := funext h
          simp only [if_pos he]
          change ‖if ∀ j : Fin a, z (Fin.natAdd N j) = false then
            ψ (fun i => z (Fin.castAdd a i)) else 0‖^2 = ‖ψ (fun i => z (Fin.castAdd a i))‖^2
          rw [if_pos h]
        · have he : ((section5_append_equiv N a) z).2 ≠ (fun _ => false) := by
            intro he
            exact h (congrFun he)
          simp only [if_neg he]
          change ‖if ∀ j : Fin a, z (Fin.natAdd N j) = false then
            ψ (fun i => z (Fin.castAdd a i)) else 0‖^2 = 0
          rw [if_neg h]
          simp
      _ = _ := by simp [Fintype.sum_prod_type]
  nlinarith [norm_nonneg (padKet a ψ), norm_nonneg ψ]

theorem section5_padKet_sub {N a : ℕ} (ψ φ : EuclideanSpace ℂ (Qubits N)) :
    padKet a (ψ-φ) = padKet a ψ - padKet a φ := by
  classical
  ext z
  change (if ∀ j : Fin a, z (Fin.natAdd N j) = false then
      ψ (fun i => z (Fin.castAdd a i)) - φ (fun i => z (Fin.castAdd a i)) else 0) =
    (if ∀ j : Fin a, z (Fin.natAdd N j) = false then ψ (fun i => z (Fin.castAdd a i)) else 0) -
      (if ∀ j : Fin a, z (Fin.natAdd N j) = false then φ (fun i => z (Fin.castAdd a i)) else 0)
  split_ifs <;> simp

theorem section5_padKet_distance {N a : ℕ} (ψ φ : EuclideanSpace ℂ (Qubits N)) :
    ‖padKet a ψ - padKet a φ‖ = ‖ψ-φ‖ := by
  rw [← section5_padKet_sub, section5_padKet_norm]


set_option autoImplicit false
open QAlgorithms QuantumLTF.Membership.Supplement
open scoped ComplexOrder ComplexConjugate MatrixOrder

noncomputable def section5_kraus_map {α β τ : Type*} [Fintype α] [Fintype β] [Fintype τ]
    (B : τ → Matrix β α ℂ) : Matrix α α ℂ →ₗ[ℂ] Matrix β β ℂ where
  toFun A := ∑ t, B t * A * (B t).conjTranspose
  map_add' A D := by simp [Matrix.mul_add, Matrix.add_mul, Finset.sum_add_distrib]
  map_smul' c A := by simp [Matrix.mul_smul, Matrix.smul_mul, Finset.smul_sum]

theorem section5_kraus_map_positive {α β τ : Type*}
    [Fintype α] [Fintype β] [Fintype τ] (B : τ → Matrix β α ℂ)
    (A : Matrix α α ℂ) (hA : A.PosSemidef) : (section5_kraus_map B A).PosSemidef := by
  classical
  exact Matrix.posSemidef_sum Finset.univ (fun t _ => hA.mul_mul_conjTranspose_same (B t))

theorem section5_kraus_map_trace {α β τ : Type*}
    [Fintype α] [Fintype β] [Fintype τ] [DecidableEq α]
    (B : τ → Matrix β α ℂ) (hB : ∑ t, (B t).conjTranspose * B t = 1)
    (A : Matrix α α ℂ) : (section5_kraus_map B A).trace = A.trace := by
  classical
  change (∑ t, B t * A * (B t).conjTranspose).trace = A.trace
  rw [Matrix.trace_sum]
  simp_rw [show ∀ t, (B t * A * (B t).conjTranspose).trace =
      ((B t).conjTranspose * B t * A).trace by
    intro t; exact Matrix.trace_mul_cycle (B t) A (B t).conjTranspose]
  rw [← Matrix.trace_sum, ← Finset.sum_mul, hB, one_mul]

noncomputable def section5_partial_trace {α β γ : Type*}
    [Fintype α] [Fintype β] [Fintype γ] (e : α ≃ β × γ) :
    Matrix α α ℂ →ₗ[ℂ] Matrix β β ℂ where
  toFun A := ∑ u : γ, A.submatrix (fun y => e.symm (y,u)) (fun y => e.symm (y,u))
  map_add' A B := by simp [Matrix.submatrix_add, Finset.sum_add_distrib]
  map_smul' c A := by simp [Matrix.submatrix_smul, Finset.smul_sum]

theorem section5_partial_trace_positive {α β γ : Type*}
    [Fintype α] [Fintype β] [Fintype γ] (e : α ≃ β × γ)
    (A : Matrix α α ℂ) (hA : A.PosSemidef) : (section5_partial_trace e A).PosSemidef := by
  classical
  exact Matrix.posSemidef_sum Finset.univ (fun u _ => hA.submatrix _)

theorem section5_partial_trace_trace {α β γ : Type*}
    [Fintype α] [Fintype β] [Fintype γ] (e : α ≃ β × γ)
    (A : Matrix α α ℂ) : (section5_partial_trace e A).trace = A.trace := by
  classical
  change (∑ u : γ, A.submatrix (fun y => e.symm (y,u)) (fun y => e.symm (y,u))).trace = A.trace
  rw [Matrix.trace_sum]
  change (∑ u : γ, ∑ y : β, A (e.symm (y,u)) (e.symm (y,u))) = A.trace
  rw [Finset.sum_comm]
  exact (Fintype.sum_prod_type (fun p : β × γ => A (e.symm p) (e.symm p))).symm.trans
    (Equiv.sum_comp e.symm (fun i => A i i))

noncomputable def section5_out_equiv {m o : ℕ} (out : Fin o ↪ Fin m) :
    Qubits m ≃ Qubits o × ({j : Fin m // ¬ ∃ i : Fin o, out i = j} → Bool) where
  toFun z := (z ∘ out, fun j => z j)
  invFun p j := if h : ∃ i : Fin o, out i = j then p.1 h.choose else p.2 ⟨j,h⟩
  left_inv z := by
    funext j
    change (if h : ∃ i : Fin o, out i = j then z (out h.choose) else z j) = z j
    split_ifs with h
    · change z (out h.choose) = z j
      rw [h.choose_spec]
    · rfl
  right_inv p := by
    apply Prod.ext
    · funext i
      have hi : ∃ i' : Fin o, out i' = out i := ⟨i,rfl⟩
      change (if h : ∃ i' : Fin o, out i' = out i then p.1 h.choose else _) = p.1 i
      rw [dif_pos hi, out.injective hi.choose_spec]
    · funext j
      change (if h : ∃ i : Fin o, out i = j.val then p.1 h.choose else _) = p.2 j
      rw [dif_neg j.property]

theorem section5_out_equiv_restrict {m o : ℕ} (out : Fin o ↪ Fin m)
    (p : Qubits o × ({j : Fin m // ¬ ∃ i : Fin o, out i = j} → Bool)) :
    (section5_out_equiv out).symm p ∘ out = p.1 :=
  congrArg Prod.fst ((section5_out_equiv out).apply_symm_apply p)

theorem section5_out_equiv_rest {m o : ℕ} (out : Fin o ↪ Fin m) (z z' : Qubits m) :
    (∀ j : Fin m, (∀ i : Fin o, out i ≠ j) → z j = z' j) ↔
      (section5_out_equiv out z).2 = (section5_out_equiv out z').2 := by
  constructor
  · intro h
    funext j
    exact h j.val (fun i hi => j.property ⟨i,hi⟩)
  · intro h j hj
    exact congrFun h ⟨j, by rintro ⟨i,hi⟩; exact hj i hi⟩

noncomputable def section5_meas_projector {m r : ℕ} (meas : Fin r ↪ Fin m) (t : Qubits r) :
    Matrix (Qubits m) (Qubits m) ℂ := Matrix.diagonal (fun z => if z ∘ meas = t then 1 else 0)

theorem section5_meas_projector_square {m r : ℕ} (meas : Fin r ↪ Fin m) (t : Qubits r) :
    (section5_meas_projector meas t).conjTranspose * section5_meas_projector meas t =
      section5_meas_projector meas t := by
  classical
  simp only [section5_meas_projector, Matrix.diagonal_conjTranspose,
    Matrix.diagonal_mul_diagonal]
  congr 1
  funext z
  split_ifs <;> simp_all

theorem section5_meas_projector_sum {m r : ℕ} (meas : Fin r ↪ Fin m) :
    ∑ t : Qubits r, section5_meas_projector meas t = 1 := by
  classical
  ext z z'
  by_cases h : z = z'
  · subst z'
    simp [section5_meas_projector, Matrix.sum_apply, Matrix.diagonal_apply, eq_comm]
  · simp [section5_meas_projector, Matrix.sum_apply, Matrix.diagonal_apply, h]

theorem section5_measured_kraus_complete {m r : ℕ}
    (V : Matrix (Qubits m) (Qubits m) ℂ)
    (W : Qubits r → Matrix (Qubits m) (Qubits m) ℂ)
    (hV : V ∈ Matrix.unitaryGroup (Qubits m) ℂ)
    (hW : ∀ t, W t ∈ Matrix.unitaryGroup (Qubits m) ℂ)
    (meas : Fin r ↪ Fin m) :
    ∑ t : Qubits r, (W t * section5_meas_projector meas t * V).conjTranspose *
      (W t * section5_meas_projector meas t * V) = 1 := by
  classical
  have unitary_left (U : Matrix (Qubits m) (Qubits m) ℂ)
      (hU : U ∈ Matrix.unitaryGroup (Qubits m) ℂ) : U.conjTranspose * U = 1 := by
    simpa only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_conjTranspose] using
      Matrix.mem_unitaryGroup_iff.mp (Unitary.star_mem hU)
  have hbranch (t : Qubits r) :
      (W t * section5_meas_projector meas t * V).conjTranspose *
        (W t * section5_meas_projector meas t * V) =
      V.conjTranspose * section5_meas_projector meas t * V := by
    simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (W t).conjTranspose (W t), unitary_left _ (hW t), one_mul]
    rw [← Matrix.mul_assoc (section5_meas_projector meas t).conjTranspose,
      section5_meas_projector_square]
  simp_rw [hbranch]
  rw [← Finset.sum_mul, ← Finset.mul_sum, section5_meas_projector_sum, mul_one]
  exact unitary_left V hV

theorem section5_outer_act {α : Type} [Fintype α]
    (B : Matrix α α ℂ) (ψ : EuclideanSpace ℂ α) :
    section5_outer (act B ψ) (act B ψ) = B * section5_outer ψ ψ * B.conjTranspose := by
  change Matrix.vecMulVec (B.mulVec ψ.ofLp) (star (B.mulVec ψ.ofLp)) =
    B * Matrix.vecMulVec ψ.ofLp (star ψ.ofLp) * B.conjTranspose
  rw [Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, Matrix.star_mulVec]

theorem section5_partial_trace_sum {Y E : Type*} [Fintype Y] [Fintype E]
    [DecidableEq Y] [DecidableEq E]
    (f : Y × E → ℂ) (y y' : Y) :
    (∑ p : Y × E, ∑ p' : Y × E,
      if p.1 = y ∧ p'.1 = y' ∧ p.2 = p'.2 then f p * star (f p') else 0) =
      ∑ u : E, f (y,u) * star (f (y',u)) := by
  classical
  simp [Fintype.sum_prod_type, ite_and, Finset.sum_ite_irrel, eq_comm]

theorem section5_partial_trace_outer_entry {m o : ℕ}
    (out : Fin o ↪ Fin m) (ψ : EuclideanSpace ℂ (Qubits m)) (y y' : Qubits o) :
    (section5_partial_trace (section5_out_equiv out) (section5_outer ψ ψ)) y y' =
      ∑ z : Qubits m, ∑ z' : Qubits m,
        if z ∘ out = y ∧ z' ∘ out = y' ∧
            ∀ j : Fin m, (∀ i : Fin o, out i ≠ j) → z j = z' j then
          ψ z * conj (ψ z') else 0 := by
  classical
  let E := section5_out_equiv out
  let Env := {j : Fin m // ¬ ∃ i : Fin o, out i = j} → Bool
  let f : Qubits m → Qubits m → ℂ := fun z z' =>
    if z ∘ out = y ∧ z' ∘ out = y' ∧
        ∀ j : Fin m, (∀ i : Fin o, out i ≠ j) → z j = z' j then
      ψ z * conj (ψ z') else 0
  have hsum : (∑ z : Qubits m, ∑ z' : Qubits m, f z z') =
      ∑ p : Qubits o × Env, ∑ p' : Qubits o × Env, f (E.symm p) (E.symm p') := by
    calc
      _ = ∑ p : Qubits o × Env, ∑ z' : Qubits m, f (E.symm p) z' :=
        (Equiv.sum_comp E.symm (fun z : Qubits m => ∑ z' : Qubits m, f z z')).symm
      _ = _ := Finset.sum_congr rfl (fun p _ =>
        (Equiv.sum_comp E.symm (f (E.symm p))).symm)
  change (∑ u : Env, (section5_outer ψ ψ).submatrix
    (fun y => E.symm (y,u)) (fun y => E.symm (y,u))) y y' = ∑ z, ∑ z', f z z'
  rw [Matrix.sum_apply]
  rw [hsum]
  dsimp only [f]
  simp_rw [section5_out_equiv_rest]
  simp only [E, section5_out_equiv_restrict, Equiv.apply_symm_apply]
  change (∑ u : Env, ψ ((section5_out_equiv out).symm (y,u)) *
    conj (ψ ((section5_out_equiv out).symm (y',u)))) = _
  exact (section5_partial_trace_sum (fun p => ψ ((section5_out_equiv out).symm p)) y y').symm

theorem section5_measured_channel_linear_extension {m r o : ℕ}
    (V : Matrix (Qubits m) (Qubits m) ℂ)
    (W : Qubits r → Matrix (Qubits m) (Qubits m) ℂ)
    (hV : V ∈ Matrix.unitaryGroup (Qubits m) ℂ)
    (hW : ∀ t, W t ∈ Matrix.unitaryGroup (Qubits m) ℂ)
    (meas : Fin r ↪ Fin m) (out : Fin o ↪ Fin m) :
    ∃ Φ : Matrix (Qubits m) (Qubits m) ℂ →ₗ[ℂ] Matrix (Qubits o) (Qubits o) ℂ,
      (∀ A, A.PosSemidef → (Φ A).PosSemidef) ∧
      (∀ A, (Φ A).trace = A.trace) ∧
      ∀ ψ : EuclideanSpace ℂ (Qubits m),
        Φ (section5_outer ψ ψ) = measChannelOut V W meas out ψ := by
  classical
  let B := fun t : Qubits r => W t * section5_meas_projector meas t * V
  let T := section5_kraus_map B
  let R := section5_partial_trace (section5_out_equiv out)
  refine ⟨R.comp T, ?_, ?_, ?_⟩
  · intro A hA
    exact section5_partial_trace_positive _ _ (section5_kraus_map_positive B A hA)
  · intro A
    exact (section5_partial_trace_trace _ _).trans
      (section5_kraus_map_trace B (section5_measured_kraus_complete V W hV hW meas) A)
  · intro ψ
    have hbranch (t : Qubits r) :
        (act (B t) ψ).ofLp = Matrix.mulVec (W t)
          (fun z => if z ∘ meas = t then (act V ψ) z else 0) := by
      change Matrix.mulVec (W t * section5_meas_projector meas t * V) ψ.ofLp = _
      rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
      congr 1
      funext z
      simp [section5_meas_projector, act, Matrix.mulVec_diagonal]
    change R (∑ t : Qubits r, B t * section5_outer ψ ψ * (B t).conjTranspose) = _
    simp_rw [← section5_outer_act]
    rw [map_sum]
    ext y y'
    rw [Matrix.sum_apply]
    change (∑ t : Qubits r, R (section5_outer (act (B t) ψ) (act (B t) ψ)) y y') = _
    simp only [R, section5_partial_trace_outer_entry]
    simp_rw [show ∀ t z, act (B t) ψ z = Matrix.mulVec (W t)
      (fun z => if z ∘ meas = t then (act V ψ) z else 0) z by
        intro t z; exact congrFun (hbranch t) z]
    rfl

theorem section5_measChannelOut_pad_stability {N e r o : ℕ}
    (V : Matrix (Qubits (N+e)) (Qubits (N+e)) ℂ)
    (W : Qubits r → Matrix (Qubits (N+e)) (Qubits (N+e)) ℂ)
    (hV : V ∈ Matrix.unitaryGroup (Qubits (N+e)) ℂ)
    (hW : ∀ t, W t ∈ Matrix.unitaryGroup (Qubits (N+e)) ℂ)
    (meas : Fin r ↪ Fin (N+e)) (out : Fin o ↪ Fin (N+e))
    (ψ φ : EuclideanSpace ℂ (Qubits N)) (hψ : ‖ψ‖ = 1) (hφ : ‖φ‖ = 1) :
    traceNorm (measChannelOut V W meas out (padKet e ψ) -
      measChannelOut V W meas out (padKet e φ)) / 2 ≤ ‖ψ-φ‖ := by
  obtain ⟨Φ,hpos,htrace,hΦ⟩ := section5_measured_channel_linear_extension V W hV hW meas out
  have hh := section5_conversion_robustness Φ hpos htrace (padKet e ψ) (padKet e φ)
    ((section5_padKet_norm ψ).trans hψ) ((section5_padKet_norm φ).trans hφ)
    (measChannelOut V W meas out (padKet e φ)) (hΦ _)
  rw [hΦ, section5_padKet_distance] at hh
  exact hh


set_option autoImplicit false
open QAlgorithms QuantumLTF.Membership QuantumLTF.Membership.Supplement

theorem solution {n K D q s e r : ℕ}
    (hK : 1 ≤ K) (hD : 2*K+1 ≤ D) (hq : D ≤ 2^q)
    (V : Matrix (Qubits (n*q+e)) (Qubits (n*q+e)) ℂ)
    (W : Qubits r → Matrix (Qubits (n*q+e)) (Qubits (n*q+e)) ℂ)
    (hV : V ∈ Matrix.unitaryGroup (Qubits (n*q+e)) ℂ)
    (hW : ∀ t, W t ∈ Matrix.unitaryGroup (Qubits (n*q+e)) ℂ)
    (meas : Fin r ↪ Fin (n*q+e)) (out : Fin (K*s) ↪ Fin (n*q+e))
    (w : EuclideanSpace ℝ (Fin n)) (hw : ‖w‖ = 1)
    (F : EuclideanSpace ℂ (Qubits (n*q))) (hF : ‖F‖ = 1)
    (ξ : ℝ) (hξ : ‖F-bandKet n q K w‖ ≤ ξ)
    (hexact : measChannelOut V W meas out (padKet e (bandKet n q K w)) =
      dirTensorPow s K w) :
    traceNorm (measChannelOut V W meas out (padKet e F) - dirTensorPow s K w) / 2 ≤ ξ := by
  have hband : ‖bandKet n q K w‖ = 1 :=
    (hermite_band_bounds_53.2.1 n K D q 0 hK hD hq w hw 0).1
  have hh := section5_measChannelOut_pad_stability V W hV hW meas out F
    (bandKet n q K w) hF hband
  rw [hexact] at hh
  exact hh.trans hξ
