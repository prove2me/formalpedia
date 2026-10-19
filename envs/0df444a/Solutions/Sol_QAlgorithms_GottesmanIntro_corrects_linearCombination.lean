-- Prove2me | solution 1 for QAlgorithms.GottesmanIntro.corrects_linearCombination
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T23:35:58.713158+00:00
-- url     : https://prove2.me/submissions/1384c9b9-6751-4aaa-b622-a5921cf72dc7

import Definitions.Def_QAlgorithms_Defs_FTCircuit
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

set_option autoImplicit false
open QAlgorithms QAlgorithms.Stabilizer
open scoped ComplexConjugate Matrix

namespace CorrectableSpan
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private lemma act_lin (A : Matrix ι ι ℂ) (v : EuclideanSpace ℂ ι) :
    act A v = Matrix.toEuclideanLin A v := rfl

omit [DecidableEq ι] in
private lemma act_pure (x v : EuclideanSpace ℂ ι) :
    act (pureDensity x) v = inner ℂ x v • x := by
  ext i
  simp only [act, pureDensity, Matrix.mulVec, dotProduct, Matrix.of_apply,
    WithLp.ofLp_toLp, PiLp.smul_apply, smul_eq_mul]
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  simp only [dotProduct, Pi.star_apply]
  simp_rw [mul_assoc, mul_comm (x i), ← Finset.sum_mul]
  simp only [Complex.star_def, mul_comm]

omit [DecidableEq ι] in
private lemma pure_conj (A : Matrix ι ι ℂ) (v : EuclideanSpace ℂ ι) :
    A * pureDensity v * Aᴴ = pureDensity (act A v) := by
  ext i j
  simp only [Matrix.mul_apply, pureDensity, Matrix.of_apply, Matrix.conjTranspose_apply,
    act, Matrix.mulVec, dotProduct, WithLp.ofLp_toLp]
  simp only [map_sum, map_mul, Complex.star_def, Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  ring

omit [Fintype ι] [DecidableEq ι] in
private lemma pure_smul (c : ℂ) (v : EuclideanSpace ℂ ι) :
    pureDensity (c • v) = (c * conj c) • pureDensity v := by
  ext i j
  simp only [pureDensity, Matrix.of_apply, PiLp.smul_apply, smul_eq_mul,
    map_mul, Matrix.smul_apply]
  ring

omit [DecidableEq ι] in
private lemma trace_pure (v : EuclideanSpace ℂ ι) :
    (pureDensity v).trace = ((‖v‖ ^ 2 : ℝ) : ℂ) := by
  change (∑ i, v i * conj (v i)) = ((‖v‖ ^ 2 : ℝ) : ℂ)
  rw [EuclideanSpace.norm_sq_eq, Complex.ofReal_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]

private lemma trace_kraus {m : ℕ} (R : Fin m → Matrix ι ι ℂ)
    (hR : IsKrausFamily R) (ρ : Matrix ι ι ℂ) :
    (krausApply R ρ).trace = ρ.trace := by
  simp only [krausApply, Matrix.trace_sum]
  conv_lhs => arg 2; ext j; rw [Matrix.trace_mul_cycle]
  rw [← Matrix.trace_sum, ← Finset.sum_mul, hR, Matrix.one_mul]

private lemma kraus_collinear {m : ℕ} (R : Fin m → Matrix ι ι ℂ)
    (v ψ : EuclideanSpace ℂ ι) (c : ℂ)
    (h : krausApply R (pureDensity v) = c • pureDensity ψ) :
    ∀ j, act (R j) v ∈ Submodule.span ℂ {ψ} := by
  intro j
  rw [← (Submodule.span ℂ {ψ}).orthogonal_orthogonal]
  apply (Submodule.mem_orthogonal _ _).2
  intro w hw
  have hwψ : inner ℂ w ψ = 0 :=
    Submodule.mem_orthogonal_singleton_iff_inner_left.mp hw
  have heq := congrArg (fun M => (inner ℂ w (act M w)).re) h
  have form : ∀ x : EuclideanSpace ℂ ι,
      inner ℂ w (act (pureDensity x) w) = (‖inner ℂ x w‖ : ℂ) ^ 2 := by
    intro x
    rw [act_pure, inner_smul_right, ← inner_conj_symm w x]
    simpa only [mul_comm] using Complex.conj_mul' (inner ℂ x w)
  have hs : act (krausApply R (pureDensity v)) w =
      ∑ a, act (pureDensity (act (R a) v)) w := by
    simp only [krausApply, pure_conj, act_lin, map_sum, LinearMap.sum_apply]
  rw [hs] at heq
  have hs' : act (c • pureDensity ψ) w = c • act (pureDensity ψ) w := by
    simp [act_lin]
  rw [hs', act_pure, inner_smul_right, inner_smul_right, hwψ, mul_zero, mul_zero] at heq
  have hz : ∑ a, ‖inner ℂ (act (R a) v) w‖ ^ 2 = 0 := by
    simpa only [inner_sum, form, Complex.re_sum, ← Complex.ofReal_pow, Complex.ofReal_re,
      Complex.zero_re] using heq
  have hj := (Finset.sum_eq_zero_iff_of_nonneg (fun a _ => sq_nonneg
    ‖inner ℂ (act (R a) v) w‖)).mp hz j (Finset.mem_univ j)
  have hz' : inner ℂ (act (R j) v) w = 0 := norm_eq_zero.mp (sq_eq_zero_iff.mp hj)
  exact (inner_eq_zero_symm).mp hz'

private lemma kraus_of_collinear {m : ℕ} (R : Fin m → Matrix ι ι ℂ)
    (hR : IsKrausFamily R) (v ψ : EuclideanSpace ℂ ι) (hψ : ‖ψ‖ = 1)
    (h : ∀ j, act (R j) v ∈ Submodule.span ℂ {ψ}) :
    krausApply R (pureDensity v) = ((‖v‖ ^ 2 : ℝ) : ℂ) • pureDensity ψ := by
  choose c hc using fun j => Submodule.mem_span_singleton.mp (h j)
  have heq : krausApply R (pureDensity v) =
      (∑ j, c j * conj (c j)) • pureDensity ψ := by
    simp only [krausApply, pure_conj, ← hc, pure_smul, Finset.sum_smul]
  have htrace := congrArg Matrix.trace heq
  rw [trace_kraus R hR, Matrix.trace_smul, trace_pure, trace_pure, hψ] at htrace
  norm_num only [one_pow, Complex.ofReal_one, smul_eq_mul, mul_one] at htrace
  rw [heq, ← htrace]

private noncomputable def admissible {m : ℕ} (R : Fin m → Matrix ι ι ℂ)
    (C : Submodule ℂ (EuclideanSpace ℂ ι)) : Submodule ℂ (Matrix ι ι ℂ) where
  carrier := {E | ∀ ψ ∈ C, ‖ψ‖ = 1 → ∀ j,
    act (R j) (act E ψ) ∈ Submodule.span ℂ {ψ}}
  zero_mem' := by
    intro ψ _ _ j
    simp [act_lin]
  add_mem' := by
    intro A B hA hB ψ hψ hu j
    simpa [act_lin, map_add] using (Submodule.span ℂ {ψ}).add_mem
      (hA ψ hψ hu j) (hB ψ hψ hu j)
  smul_mem' := by
    intro c A hA ψ hψ hu j
    simpa [act_lin, map_smul] using (Submodule.span ℂ {ψ}).smul_mem c (hA ψ hψ hu j)

private theorem corrects_span (C : Submodule ℂ (EuclideanSpace ℂ ι))
    (S : Set (Matrix ι ι ℂ)) (h : Corrects C S) :
    Corrects C (Submodule.span ℂ S : Set (Matrix ι ι ℂ)) := by
  obtain ⟨Φ, ⟨m, R, hR, hΦ⟩, h⟩ := h
  have hs : Submodule.span ℂ S ≤ admissible R C := by
    apply Submodule.span_le.mpr
    intro E hE ψ hψ hu j
    apply kraus_collinear R (act E ψ) ψ ((‖act E ψ‖ ^ 2 : ℝ) : ℂ)
    rw [← hΦ]
    exact h E hE ψ hψ hu
  refine ⟨Φ, ⟨m, R, hR, hΦ⟩, ?_⟩
  intro E hE ψ hψ hu
  rw [hΦ]
  exact kraus_of_collinear R hR (act E ψ) ψ hu (hs hE ψ hψ hu)

end CorrectableSpan

namespace PauliExpansion
private noncomputable def coeff (a b : Bool) : Pauli → ℂ
  | .I => if a = b then 1 / 2 else 0
  | .X => if a = b then 0 else 1 / 2
  | .Y => if a = b then 0 else if a then -Complex.I / 2 else Complex.I / 2
  | .Z => if a = b then if a then -1 / 2 else 1 / 2 else 0

private lemma coeff_expansion (a b y z : Bool) :
    (∑ p : Pauli, coeff a b p * p.mat y z) = if y = a ∧ z = b then 1 else 0 := by
  have hp : (Finset.univ : Finset Pauli) = {.I, .X, .Y, .Z} := rfl
  rw [hp, Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_singleton]
  cases a <;> cases b <;> cases y <;> cases z <;>
    norm_num [coeff, Pauli.mat, pauliX, pauliY, pauliZ, Matrix.one_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one] <;> ring_nf <;> norm_num

private lemma pauli_expand {k : ℕ} (M : Matrix (Qubits k) (Qubits k) ℂ) :
    M = ∑ a : Qubits k, ∑ b : Qubits k, ∑ o : Fin k → Pauli,
      (M a b * ∏ q, coeff (a q) (b q) (o q)) • pauliOps o := by
  apply Matrix.ext
  intro y z
  simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, pauliOps,
    PauliString.toMatrix, Matrix.of_apply, ZMod.val_zero, pow_zero, one_mul]
  have hstep : ∀ a b : Qubits k,
      (∑ o : Fin k → Pauli, (M a b * ∏ q, coeff (a q) (b q) (o q)) *
        ∏ q, (o q).mat (y q) (z q)) =
      M a b * ∏ q, (if y q = a q ∧ z q = b q then (1 : ℂ) else 0) := by
    intro a b
    calc
      _ = M a b * ∑ o : Fin k → Pauli,
          ∏ q, coeff (a q) (b q) (o q) * (o q).mat (y q) (z q) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro o _
        rw [Finset.prod_mul_distrib]
        ring
      _ = _ := by
        rw [← Fintype.prod_sum (fun (q : Fin k) (p : Pauli) =>
          coeff (a q) (b q) p * p.mat (y q) (z q))]
        simp_rw [coeff_expansion]
  simp_rw [hstep]
  have hprod : ∀ a b : Qubits k,
      (∏ q, (if y q = a q ∧ z q = b q then (1 : ℂ) else 0)) =
        if y = a ∧ z = b then 1 else 0 := by
    intro a b
    by_cases h : y = a ∧ z = b
    · simp [h.1, h.2]
    · rw [if_neg h]
      have hn : ∃ q, ¬ (y q = a q ∧ z q = b q) := by
        by_contra hc
        push Not at hc
        exact h ⟨funext fun q => (hc q).1, funext fun q => (hc q).2⟩
      obtain ⟨q, hq⟩ := hn
      exact Finset.prod_eq_zero (Finset.mem_univ q) (if_neg hq)
  simp_rw [hprod]
  simp only [mul_ite, mul_one, mul_zero, ite_and]
  simp

private noncomputable def extendOps {k n : ℕ} (w : Fin k ↪ Fin n)
    (o : Fin k → Pauli) (q : Fin n) : Pauli :=
  if h : ∃ i, w i = q then o h.choose else .I

private lemma extend_on {k n : ℕ} (w : Fin k ↪ Fin n)
    (o : Fin k → Pauli) (i : Fin k) : extendOps w o (w i) = o i := by
  have h : ∃ j, w j = w i := ⟨i, rfl⟩
  rw [extendOps, dif_pos h]
  congr 1
  exact w.injective (Exists.choose_spec (show ∃ j, w j = w i from ⟨i, rfl⟩))

private lemma extend_off {k n : ℕ} (w : Fin k ↪ Fin n)
    (o : Fin k → Pauli) (q : Fin n) (hq : q ∉ Set.range w) :
    extendOps w o q = .I := dif_neg hq

private lemma embed_pauli {k n : ℕ} (w : Fin k ↪ Fin n) (o : Fin k → Pauli) :
    embedOp (pauliOps o) w = pauliOps (extendOps w o) := by
  classical
  apply Matrix.ext
  intro y z
  simp only [embedOp, pauliOps, PauliString.toMatrix, Matrix.of_apply, ZMod.val_zero,
    pow_zero, one_mul]
  by_cases h : ∀ a : Fin n, a ∉ Set.range w → y a = z a
  · rw [if_pos h]
    have hp : (∏ q : Fin n, (extendOps w o q).mat (y q) (z q)) =
        ∏ q ∈ Finset.univ.image w, (extendOps w o q).mat (y q) (z q) := by
      symm
      apply Finset.prod_subset (Finset.subset_univ _)
      intro q _ hq
      have hq' : q ∉ Set.range w := by simpa using hq
      rw [extend_off w o q hq', Pauli.mat, Matrix.one_apply, if_pos (h q hq')]
    rw [hp, Finset.prod_image w.injective.injOn]
    simp only [extend_on, Function.comp_apply]
  · rw [if_neg h]
    push Not at h
    obtain ⟨q, hq, hne⟩ := h
    symm
    apply Finset.prod_eq_zero (Finset.mem_univ q)
    rw [extend_off w o q hq, Pauli.mat, Matrix.one_apply, if_neg hne]

private lemma supported_weight {k n : ℕ} (F : Finset (Fin n)) (w : Fin k ↪ Fin n)
    (hw : Set.range w ⊆ (F : Set (Fin n))) (o : Fin k → Pauli) :
    opsWeight (extendOps w o) ≤ F.card := by
  apply Finset.card_le_card
  intro q hq
  have hne : extendOps w o q ≠ .I := (Finset.mem_filter.mp hq).2
  by_contra hn
  exact hne (extend_off w o q (fun hr => hn (hw hr)))

private noncomputable def embedLinear {k n : ℕ} (w : Fin k ↪ Fin n) :
    Matrix (Qubits k) (Qubits k) ℂ →ₗ[ℂ] Matrix (Qubits n) (Qubits n) ℂ where
  toFun M := embedOp M w
  map_add' A B := by
    apply Matrix.ext
    intro y z
    simp only [embedOp, Matrix.of_apply, Matrix.add_apply]
    split_ifs <;> simp
  map_smul' c A := by
    apply Matrix.ext
    intro y z
    simp only [embedOp, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul]
    split_ifs <;> simp

private theorem acts_mem_pauliSpan {n t : ℕ} (E : Matrix (Qubits n) (Qubits n) ℂ)
    (hE : ActsOnAtMost t E) : E ∈ pauliSpan n t := by
  classical
  obtain ⟨F, hF, k, w, M, hw, rfl⟩ := hE
  have hexp := congrArg (embedLinear w) (pauli_expand M)
  simp only [map_sum, map_smul] at hexp
  rw [show embedOp M w = embedLinear w M from rfl, hexp]
  apply Submodule.sum_mem
  intro a _
  apply Submodule.sum_mem
  intro b _
  apply Submodule.sum_mem
  intro o _
  apply Submodule.smul_mem
  change embedOp (pauliOps o) w ∈ pauliSpan n t
  rw [embed_pauli]
  apply Submodule.subset_span
  refine ⟨⟨0, extendOps w o⟩, (supported_weight F w hw o).trans hF, rfl⟩

end PauliExpansion

theorem solution (n : ℕ) (C : Submodule ℂ (EuclideanSpace ℂ (Qubits n))) :
    (∀ A B : Matrix (Qubits n) (Qubits n) ℂ, Corrects C {A, B} →
      Corrects C (Submodule.span ℂ {A, B} : Set (Matrix (Qubits n) (Qubits n) ℂ))) ∧
    ∀ t : ℕ, Corrects C {M | ∃ P : PauliString n, P.weight ≤ t ∧ M = P.toMatrix} →
      Corrects C {E | ActsOnAtMost t E} := by
  constructor
  · intro A B h
    exact CorrectableSpan.corrects_span C {A, B} h
  · intro t h
    obtain ⟨R, hR, hcorrect⟩ := CorrectableSpan.corrects_span C _ h
    refine ⟨R, hR, ?_⟩
    intro E hE ψ hψ hu
    exact hcorrect E (PauliExpansion.acts_mem_pauliSpan E hE) ψ hψ hu
