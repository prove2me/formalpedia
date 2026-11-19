-- Prove2me | solution 1 for QMaxCutBeyond.TwoQubit.weighted_eq_18_19
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-19T05:40:14.866197+00:00
-- url     : https://prove2.me/submissions/f3733b0b-0065-4115-aad6-6eee34c30b7c

import Mathlib
import Definitions.Def_QMaxCutBeyond_TwoQubit_Setting

namespace QMaxCutBeyond.TwoQubit

open Matrix

private lemma totalWeight_eq_sum_lt {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (w : Sym2 (Fin n) → ℝ) :
    totalWeight G w = ∑ i : Fin n, ∑ j : Fin n, if i < j ∧ G.Adj i j then w s(i, j) else 0 := by
  unfold totalWeight
  have hR : (∑ i : Fin n, ∑ j : Fin n, if i < j ∧ G.Adj i j then w s(i, j) else 0) =
      ∑ p ∈ Finset.univ.filter (fun p : Fin n × Fin n => p.1 < p.2 ∧ G.Adj p.1 p.2), w s(p.1, p.2) := by
    rw [Finset.sum_filter, Fintype.sum_prod_type]
  rw [hR]
  refine (Finset.sum_bij (fun p _ => s(p.1, p.2)) ?_ ?_ ?_ ?_).symm
  · intro p hp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
    exact G.mem_edgeFinset.mpr hp.2
  · intro p hp q hq h
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp hq
    rw [Sym2.eq_iff] at h
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Prod.ext h1 h2
    · exfalso; exact absurd (h1 ▸ hp.1) (not_lt.mpr (le_of_lt (h2 ▸ hq.1)))
  · intro e he
    rw [G.mem_edgeFinset] at he
    induction e using Sym2.ind with
    | _ a b =>
      have hab : a ≠ b := G.ne_of_adj he
      rcases lt_or_gt_of_ne hab with h | h
      · exact ⟨(a, b), Finset.mem_filter.mpr ⟨Finset.mem_univ _, h, he⟩, rfl⟩
      · exact ⟨(b, a), Finset.mem_filter.mpr ⟨Finset.mem_univ _, h, he.symm⟩, Sym2.eq_swap⟩
  · intro _ _; rfl

private noncomputable def hamX {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (w : Sym2 (Fin n) → ℝ) : Op n :=
  ∑ i, ∑ j, if i < j ∧ G.Adj i j then
    ((-(1 / 2) * w s(i, j) : ℝ) : ℂ) • (onSite i pauliX * onSite j pauliX) else 0

private noncomputable def hamY {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (w : Sym2 (Fin n) → ℝ) : Op n :=
  ∑ i, ∑ j, if i < j ∧ G.Adj i j then
    ((-(1 / 2) * w s(i, j) : ℝ) : ℂ) • (onSite i pauliY * onSite j pauliY) else 0

private lemma hamiltonian_decomp {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (w : Sym2 (Fin n) → ℝ) :
    hamiltonian G w = ((totalWeight G w / 2 : ℝ) : ℂ) • (1 : Op n) +
      hamX G w + hamY G w + hamZ G w := by
  unfold hamiltonian hamX hamY hamZ
  rw [totalWeight_eq_sum_lt G w]
  have hhalf : ((∑ i : Fin n, ∑ j : Fin n, if i < j ∧ G.Adj i j then w s(i, j) else 0) / 2 : ℝ) =
      ∑ i : Fin n, ∑ j : Fin n, if i < j ∧ G.Adj i j then w s(i, j) / 2 else 0 := by
    simp only [Finset.sum_div]; refine Finset.sum_congr rfl fun i _ => ?_
    refine Finset.sum_congr rfl fun j _ => ?_; split_ifs <;> ring
  rw [hhalf]
  push_cast
  rw [Finset.sum_smul]
  simp_rw [Finset.sum_smul]
  simp only [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  split_ifs with h
  · unfold edgeTerm
    ext x y
    simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply, Matrix.one_apply,
      smul_eq_mul]
    push_cast
    ring
  · simp

private lemma onSite_pauliZ_apply {n : ℕ} (i : Fin n) (x y : Config n) :
    onSite i pauliZ x y = if x = y then (if x i = 0 then 1 else -1) else 0 := by
  unfold onSite pauliZ
  by_cases hxy : x = y
  · subst hxy
    simp only [↓reduceIte, mul_one]
    have hxi : x i = 0 ∨ x i = 1 := by omega
    rcases hxi with h | h <;> simp [h]
  · simp only [hxy, ↓reduceIte]
    by_cases hother : ∀ j, j ≠ i → x j = y j
    · have hne : x i ≠ y i := fun h => hxy (funext fun j => if hj : j = i then hj ▸ h else hother j hj)
      have hxi : x i = 0 ∨ x i = 1 := by omega
      have hyi : y i = 0 ∨ y i = 1 := by omega
      rcases hxi with hx | hx <;> rcases hyi with hy | hy <;> simp_all
    · simp [hother]

private lemma hamZ_diag {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (w : Sym2 (Fin n) → ℝ) (x y : Config n) (hxy : x ≠ y) :
    hamZ G w x y = 0 := by
  unfold hamZ
  simp only [Matrix.sum_apply, Matrix.ite_apply, Matrix.zero_apply, Matrix.smul_apply,
    Matrix.mul_apply, onSite_pauliZ_apply]
  refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_
  by_cases h : i < j ∧ G.Adj i j
  · rw [if_pos h]
    simp only [smul_eq_mul]
    have h0 : ∑ z : Config n, (if x = z then (if x i = 0 then (1 : ℂ) else -1) else 0) *
        (if z = y then (if z j = 0 then (1 : ℂ) else -1) else 0) = 0 := by
      refine Finset.sum_eq_zero fun z _ => ?_
      by_cases hxz : x = z
      · by_cases hzy : z = y
        · exact absurd (hxz.trans hzy) hxy
        · simp [hzy]
      · simp [hxz]
    rw [h0, mul_zero]
  · rw [if_neg h]

private lemma hamZ_diag_real {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (w : Sym2 (Fin n) → ℝ) (x : Config n) :
    (hamZ G w x x).im = 0 := by
  unfold hamZ
  simp only [Matrix.sum_apply, Complex.im_sum]
  refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_
  split_ifs with h
  · simp only [Matrix.smul_apply, smul_eq_mul, Matrix.mul_apply, onSite_pauliZ_apply]
    rw [Finset.sum_eq_single x]
    · simp only [↓reduceIte]
      have h1 : ((if x i = 0 then (1 : ℂ) else -1) * (if x j = 0 then (1 : ℂ) else -1)).im = 0 := by
        split_ifs <;> simp
      have h2 : (((-(1 / 2) * w s(i, j) : ℝ) : ℂ) *
          ((if x i = 0 then (1 : ℂ) else -1) * (if x j = 0 then (1 : ℂ) else -1))).im = 0 := by
        split_ifs <;> simp
      exact h2
    · intro z _ hz; simp [hz.symm]
    · intro hx; exact absurd (Finset.mem_univ _) hx
  · simp

private lemma energy_hamZ_eq {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (w : Sym2 (Fin n) → ℝ) (ψ : Config n → ℂ) :
    energy (hamZ G w) ψ = ∑ x : Config n, ‖ψ x‖ ^ 2 * (hamZ G w x x).re := by
  unfold energy
  simp only [dotProduct, Matrix.mulVec, Pi.star_apply]
  have hterm : ∀ x : Config n,
      star (ψ x) * (∑ y : Config n, hamZ G w x y * ψ y) =
      ((‖ψ x‖ ^ 2 : ℝ) : ℂ) * hamZ G w x x := by
    intro x
    rw [Finset.sum_eq_single x]
    · have hnorm : star (ψ x) * ψ x = ((‖ψ x‖ ^ 2 : ℝ) : ℂ) := by
        rw [Complex.star_def, mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
      calc star (ψ x) * (hamZ G w x x * ψ x)
          = (star (ψ x) * ψ x) * hamZ G w x x := by ring
        _ = ((‖ψ x‖ ^ 2 : ℝ) : ℂ) * hamZ G w x x := by rw [hnorm]
    · intro y _ hy; rw [hamZ_diag G w x y hy.symm, zero_mul]
    · intro hx; exact absurd (Finset.mem_univ _) hx
  simp_rw [hterm, Complex.re_sum, Complex.re_ofReal_mul]

private lemma energy_hamZ_basisState {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (w : Sym2 (Fin n) → ℝ) (z : Config n) :
    energy (hamZ G w) (basisState z) = (hamZ G w z z).re := by
  rw [energy_hamZ_eq, Finset.sum_eq_single z]
  · simp [basisState]
  · intro x _ hx; simp [basisState, hx]
  · intro hz; exact absurd (Finset.mem_univ _) hz

private noncomputable def tensorOpGen {n : ℕ} (A : Fin n → Matrix (Fin 2) (Fin 2) ℂ) : Op n :=
  fun x y => ∏ k : Fin n, A k (x k) (y k)

private lemma tensorOpGen_mul {n : ℕ} (A B : Fin n → Matrix (Fin 2) (Fin 2) ℂ) :
    tensorOpGen A * tensorOpGen B = tensorOpGen (fun k => A k * B k) := by
  ext x z
  simp only [tensorOpGen, Matrix.mul_apply]
  have h1 : ∀ y : Config n,
      (∏ k : Fin n, A k (x k) (y k)) * (∏ k : Fin n, B k (y k) (z k)) =
      ∏ k : Fin n, (A k (x k) (y k) * B k (y k) (z k)) := fun y => (Finset.prod_mul_distrib).symm
  simp_rw [h1]
  exact (Fintype.prod_sum (fun k b => A k (x k) b * B k b (z k))).symm

private noncomputable def tensorOp {n : ℕ} (U : Matrix (Fin 2) (Fin 2) ℂ) : Op n :=
  tensorOpGen (fun _ => U)

private lemma tensorOp_mul {n : ℕ} (U V : Matrix (Fin 2) (Fin 2) ℂ) :
    tensorOp (n := n) U * tensorOp (n := n) V = tensorOp (n := n) (U * V) :=
  tensorOpGen_mul _ _

private lemma tensorOp_conjTranspose {n : ℕ} (U : Matrix (Fin 2) (Fin 2) ℂ) :
    (tensorOp (n := n) U)ᴴ = tensorOp (n := n) Uᴴ := by
  ext x y
  simp only [tensorOp, tensorOpGen, Matrix.conjTranspose_apply, star_prod]

private lemma tensorOp_one {n : ℕ} : tensorOp (n := n) 1 = 1 := by
  ext x y
  simp only [tensorOp, tensorOpGen, Matrix.one_apply]
  by_cases hxy : x = y
  · subst hxy; simp
  · rw [if_neg hxy]
    have hex : ∃ k : Fin n, x k ≠ y k := by
      by_contra h; push_neg at h; exact hxy (funext h)
    rcases hex with ⟨k, hk⟩
    exact Finset.prod_eq_zero (Finset.mem_univ k) (by simp [hk])

private lemma isUnitState_mulVec {n : ℕ} (U : Matrix (Fin 2) (Fin 2) ℂ) (hU : Uᴴ * U = 1)
    (ψ : Config n → ℂ) (hψ : IsUnitState ψ) :
    IsUnitState (tensorOp (n := n) U *ᵥ ψ) := by
  unfold IsUnitState at hψ ⊢
  have hnorm : ∀ φ : Config n → ℂ, ∑ x : Config n, ‖φ x‖ ^ 2 = (star φ ⬝ᵥ φ).re := by
    intro φ
    simp only [dotProduct, Pi.star_apply, Complex.re_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Complex.star_def, mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.ofReal_re]
  rw [hnorm]
  have hdot : star (tensorOp (n := n) U *ᵥ ψ) ⬝ᵥ (tensorOp (n := n) U *ᵥ ψ) = star ψ ⬝ᵥ ψ := by
    rw [Matrix.star_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul,
      tensorOp_conjTranspose, tensorOp_mul, hU, tensorOp_one, Matrix.vecMul_one]
  rw [hdot, ← hnorm, hψ]

private lemma tensorOp_conj_onSite {n : ℕ} (U : Matrix (Fin 2) (Fin 2) ℂ) (hU : Uᴴ * U = 1)
    (i : Fin n) (σ : Matrix (Fin 2) (Fin 2) ℂ) :
    (tensorOp (n := n) U)ᴴ * onSite i σ * tensorOp (n := n) U = onSite i (Uᴴ * σ * U) := by
  have h1 : ∀ A : Matrix (Fin 2) (Fin 2) ℂ,
      onSite (n := n) i A = tensorOpGen (fun k => if k = i then A else 1) := by
    intro A; ext x y
    unfold onSite tensorOpGen
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i)]
    have hrest : ∏ k ∈ Finset.univ.erase i, (if k = i then A else 1) (x k) (y k) =
        if ∀ j, j ≠ i → x j = y j then 1 else 0 := by
      by_cases hother : ∀ j, j ≠ i → x j = y j
      · rw [if_pos hother]
        refine Finset.prod_eq_one fun k hk => ?_
        have hki : k ≠ i := (Finset.mem_erase.mp hk).1
        simp [hki, hother k hki, Matrix.one_apply]
      · rw [if_neg hother]
        push_neg at hother
        rcases hother with ⟨j, hji, hxy⟩
        exact Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hji, Finset.mem_univ _⟩) (by simp [hji, hxy])
    simp [hrest]
  rw [h1 σ, h1 (Uᴴ * σ * U), tensorOp_conjTranspose]
  change tensorOpGen (fun _ => Uᴴ) * tensorOpGen (fun k => if k = i then σ else 1) *
      tensorOpGen (fun _ => U) = tensorOpGen (fun k => if k = i then Uᴴ * σ * U else 1)
  rw [tensorOpGen_mul, tensorOpGen_mul]
  congr 1; ext k
  by_cases hki : k = i
  · subst hki; simp
  · simp [hki, hU]

private noncomputable def UX : Matrix (Fin 2) (Fin 2) ℂ :=
  ((Real.sqrt 2 : ℂ)⁻¹) • !![(1 : ℂ), 1; 1, -1]

private noncomputable def UY : Matrix (Fin 2) (Fin 2) ℂ :=
  ((Real.sqrt 2 : ℂ)⁻¹) • !![(1 : ℂ), 1; Complex.I, -Complex.I]

private lemma UX_unitary : UXᴴ * UX = 1 := by
  have hsq : (Real.sqrt 2 : ℂ) ^ 2 = 2 := by
    norm_cast; exact Real.sq_sqrt (by norm_num)
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [UX, Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_two, Complex.conj_ofReal] <;>
    ring_nf <;> simp [hsq] <;> norm_num

private lemma UY_unitary : UYᴴ * UY = 1 := by
  have hsq : (Real.sqrt 2 : ℂ) ^ 2 = 2 := by
    norm_cast; exact Real.sq_sqrt (by norm_num)
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [UY, Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_two, Complex.conj_ofReal] <;>
    ring_nf <;> simp [hsq] <;> norm_num

private lemma UX_conj_pauliZ : UXᴴ * pauliZ * UX = pauliX := by
  have hsq : (Real.sqrt 2 : ℂ) ^ 2 = 2 := by
    norm_cast; exact Real.sq_sqrt (by norm_num)
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [UX, pauliZ, pauliX, Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_two,
      Complex.conj_ofReal] <;>
    ring_nf <;> simp [hsq] <;> norm_num

private lemma UY_conj_pauliY : UYᴴ * pauliY * UY = pauliZ := by
  have hsq : (Real.sqrt 2 : ℂ) ^ 2 = 2 := by
    norm_cast; exact Real.sq_sqrt (by norm_num)
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [UY, pauliZ, pauliY, Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_two,
      Complex.conj_ofReal] <;>
    ring_nf <;> simp [hsq] <;> norm_num

private lemma UX_mul_conjTranspose : UX * UXᴴ = 1 := by
  have hsq : (Real.sqrt 2 : ℂ) ^ 2 = 2 := by
    norm_cast; exact Real.sq_sqrt (by norm_num)
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [UX, Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_two, Complex.conj_ofReal] <;>
    ring_nf <;> simp [hsq] <;> norm_num

private lemma energy_hamX_eq_hamZ {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (w : Sym2 (Fin n) → ℝ) (ψ : Config n → ℂ) :
    energy (hamX G w) ψ = energy (hamZ G w) (tensorOp (n := n) UX *ᵥ ψ) := by
  have hconj_ite : ∀ (A B : Op n) (_ : (tensorOp (n := n) UX)ᴴ * A * tensorOp (n := n) UX = B)
      (p : Prop) [Decidable p] (c : ℂ),
      (tensorOp (n := n) UX)ᴴ * (if p then c • A else 0) * tensorOp (n := n) UX =
        if p then c • B else 0 := by
    intro A B hAB p _ c
    split_ifs
    · simp only [Matrix.mul_smul, Matrix.smul_mul, hAB]
    · simp
  have hconj : (tensorOp (n := n) UX)ᴴ * hamZ G w * tensorOp (n := n) UX = hamX G w := by
    unfold hamZ hamX
    simp only [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    refine hconj_ite _ _ ?_ _ _
    have hu : tensorOp (n := n) UX * (tensorOp (n := n) UX)ᴴ = 1 := by
      rw [tensorOp_conjTranspose, tensorOp_mul, UX_mul_conjTranspose, tensorOp_one]
    calc (tensorOp UX)ᴴ * (onSite i pauliZ * onSite j pauliZ) * tensorOp UX
        = (tensorOp UX)ᴴ * (onSite i pauliZ * (tensorOp UX * (tensorOp UX)ᴴ) *
            onSite j pauliZ) * tensorOp UX := by rw [hu, Matrix.mul_one]
      _ = ((tensorOp UX)ᴴ * onSite i pauliZ * tensorOp UX) *
            ((tensorOp UX)ᴴ * onSite j pauliZ * tensorOp UX) := by simp only [Matrix.mul_assoc]
      _ = onSite i pauliX * onSite j pauliX := by
          rw [tensorOp_conj_onSite UX UX_unitary i pauliZ,
              tensorOp_conj_onSite UX UX_unitary j pauliZ, UX_conj_pauliZ]
  unfold energy
  rw [← hconj]
  congr 1
  rw [Matrix.star_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec]

private lemma UY_mul_conjTranspose : UY * UYᴴ = 1 := by
  have hsq : (Real.sqrt 2 : ℂ) ^ 2 = 2 := by
    norm_cast; exact Real.sq_sqrt (by norm_num)
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [UY, Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_two, Complex.conj_ofReal] <;>
    ring_nf <;> simp [hsq] <;> norm_num

private lemma energy_hamY_eq_hamZ {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (w : Sym2 (Fin n) → ℝ) (ψ : Config n → ℂ) :
    energy (hamY G w) ψ = energy (hamZ G w) (tensorOp (n := n) UYᴴ *ᵥ ψ) := by
  have hconj_ite : ∀ (A B : Op n) (_ : (tensorOp (n := n) UY)ᴴ * A * tensorOp (n := n) UY = B)
      (p : Prop) [Decidable p] (c : ℂ),
      (tensorOp (n := n) UY)ᴴ * (if p then c • A else 0) * tensorOp (n := n) UY =
        if p then c • B else 0 := by
    intro A B hAB p _ c
    split_ifs
    · simp only [Matrix.mul_smul, Matrix.smul_mul, hAB]
    · simp
  have hconj : (tensorOp (n := n) UY)ᴴ * hamY G w * tensorOp (n := n) UY = hamZ G w := by
    unfold hamY hamZ
    simp only [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    refine hconj_ite _ _ ?_ _ _
    have hu : tensorOp (n := n) UY * (tensorOp (n := n) UY)ᴴ = 1 := by
      rw [tensorOp_conjTranspose, tensorOp_mul, UY_mul_conjTranspose, tensorOp_one]
    calc (tensorOp UY)ᴴ * (onSite i pauliY * onSite j pauliY) * tensorOp UY
        = (tensorOp UY)ᴴ * (onSite i pauliY * (tensorOp UY * (tensorOp UY)ᴴ) *
            onSite j pauliY) * tensorOp UY := by rw [hu, Matrix.mul_one]
      _ = ((tensorOp UY)ᴴ * onSite i pauliY * tensorOp UY) *
            ((tensorOp UY)ᴴ * onSite j pauliY * tensorOp UY) := by simp only [Matrix.mul_assoc]
      _ = onSite i pauliZ * onSite j pauliZ := by
          rw [tensorOp_conj_onSite UY UY_unitary i pauliY,
              tensorOp_conj_onSite UY UY_unitary j pauliY, UY_conj_pauliY]
  have hconj2 : tensorOp (n := n) UY * hamZ G w * (tensorOp (n := n) UY)ᴴ = hamY G w := by
    have hu : tensorOp (n := n) UY * (tensorOp (n := n) UY)ᴴ = 1 := by
      rw [tensorOp_conjTranspose, tensorOp_mul, UY_mul_conjTranspose, tensorOp_one]
    calc tensorOp UY * hamZ G w * (tensorOp UY)ᴴ
        = tensorOp UY * ((tensorOp UY)ᴴ * hamY G w * tensorOp UY) * (tensorOp UY)ᴴ := by
          rw [hconj]
      _ = (tensorOp UY * (tensorOp UY)ᴴ) * hamY G w * (tensorOp UY * (tensorOp UY)ᴴ) := by
          simp only [Matrix.mul_assoc]
      _ = hamY G w := by rw [hu, Matrix.one_mul, Matrix.mul_one]
  unfold energy
  rw [← hconj2]
  congr 1
  have hL : star (tensorOp (n := n) UYᴴ *ᵥ ψ) = star ψ ᵥ* tensorOp (n := n) UY := by
    rw [Matrix.star_mulVec, tensorOp_conjTranspose, Matrix.conjTranspose_conjTranspose]
  rw [hL]
  rw [tensorOp_conjTranspose, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    Matrix.dotProduct_mulVec]

private lemma basisState_isUnitState {n : ℕ} (z : Config n) : IsUnitState (basisState z) := by
  unfold IsUnitState
  rw [Finset.sum_eq_single z]
  · simp [basisState]
  · intro x _ hx; simp [basisState, hx]
  · intro hz; exact absurd (Finset.mem_univ _) hz

private lemma off_diag_pair_basis_zero {n : ℕ} (σ : Matrix (Fin 2) (Fin 2) ℂ)
    (h0 : σ 0 0 = 0) (h1 : σ 1 1 = 0) (i j : Fin n) (hij : i ≠ j) (z : Config n) :
    (onSite i σ * onSite j σ) z z = 0 := by
  simp only [Matrix.mul_apply, onSite]
  refine Finset.sum_eq_zero fun y _ => ?_
  by_cases hyz : y = z
  · subst hyz
    have hdiag : σ (y i) (y i) = 0 := by
      have hyi : y i = 0 ∨ y i = 1 := by omega
      rcases hyi with h | h <;> simp [h, h0, h1]
    simp [hdiag]
  · have hex : ∃ k : Fin n, y k ≠ z k := by
      by_contra h; push_neg at h; exact hyz (funext h)
    rcases hex with ⟨k, hk⟩
    by_cases hki : k = i
    · have hkj : k ≠ j := hki ▸ hij
      have hother : ¬ ∀ l, l ≠ j → y l = z l := fun h => hk (h k hkj)
      simp [hother]
    · have hother : ¬ ∀ l, l ≠ i → z l = y l := fun h => hk (h k hki).symm
      simp [hother]

private theorem weighted_eq_18_19_aux {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (w : Sym2 (Fin n) → ℝ) (hw : ∀ e, 0 ≤ w e) :
    ∃ z : Config n,
      (∀ ψ : Config n → ℂ, IsUnitState ψ →
        energy (hamZ G w) ψ ≤ energy (hamZ G w) (basisState z)) ∧
      (∀ ψ : Config n → ℂ, IsUnitState ψ →
        energy (hamiltonian G w) ψ ≤ totalWeight G w / 2 + 3 * energy (hamZ G w) (basisState z)) ∧
      energy (hamiltonian G w) (basisState z) =
        totalWeight G w / 2 + energy (hamZ G w) (basisState z) := by
  obtain ⟨z, _, hz_max⟩ := Finset.exists_max_image Finset.univ (fun x : Config n => (hamZ G w x x).re)
    Finset.univ_nonempty
  refine ⟨z, ?_, ?_, ?_⟩
  · intro ψ hψ
    rw [energy_hamZ_eq, energy_hamZ_basisState]
    calc ∑ x : Config n, ‖ψ x‖ ^ 2 * (hamZ G w x x).re
        ≤ ∑ x : Config n, ‖ψ x‖ ^ 2 * (hamZ G w z z).re := by
          refine Finset.sum_le_sum fun x _ => ?_
          exact mul_le_mul_of_nonneg_left (hz_max x (Finset.mem_univ _)) (sq_nonneg _)
      _ = (hamZ G w z z).re := by
          rw [← Finset.sum_mul, show ∑ x : Config n, ‖ψ x‖ ^ 2 = 1 from hψ, one_mul]
  · intro ψ hψ
    have hdecomp : energy (hamiltonian G w) ψ =
        totalWeight G w / 2 + energy (hamX G w) ψ + energy (hamY G w) ψ + energy (hamZ G w) ψ := by
      unfold energy
      rw [hamiltonian_decomp]
      simp only [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_add,
        dotProduct_smul, Complex.add_re]
      have h1 : (star ψ ⬝ᵥ ψ).re = 1 := by
        have hnorm : (star ψ ⬝ᵥ ψ).re = ∑ x : Config n, ‖ψ x‖ ^ 2 := by
          simp only [dotProduct, Pi.star_apply, Complex.re_sum]
          refine Finset.sum_congr rfl fun x _ => ?_
          rw [Complex.star_def, mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.ofReal_re]
        rw [hnorm]; exact hψ
      rw [smul_eq_mul, Complex.re_ofReal_mul, h1, mul_one]
    rw [hdecomp, energy_hamX_eq_hamZ, energy_hamY_eq_hamZ]
    have hx : energy (hamZ G w) (tensorOp (n := n) UX *ᵥ ψ) ≤ energy (hamZ G w) (basisState z) := by
      have hux := isUnitState_mulVec UX UX_unitary ψ hψ
      rw [energy_hamZ_eq, energy_hamZ_basisState]
      calc ∑ x : Config n, ‖(tensorOp UX *ᵥ ψ) x‖ ^ 2 * (hamZ G w x x).re
          ≤ ∑ x : Config n, ‖(tensorOp UX *ᵥ ψ) x‖ ^ 2 * (hamZ G w z z).re :=
            Finset.sum_le_sum fun x _ => mul_le_mul_of_nonneg_left (hz_max x (Finset.mem_univ _)) (sq_nonneg _)
        _ = (hamZ G w z z).re := by
            rw [← Finset.sum_mul, show ∑ x : Config n, ‖(tensorOp UX *ᵥ ψ) x‖ ^ 2 = 1 from hux, one_mul]
    have hy : energy (hamZ G w) (tensorOp (n := n) UYᴴ *ᵥ ψ) ≤ energy (hamZ G w) (basisState z) := by
      have huy : UYᴴᴴ * UYᴴ = 1 := by rw [Matrix.conjTranspose_conjTranspose]; exact UY_mul_conjTranspose
      have huy_unit := isUnitState_mulVec UYᴴ huy ψ hψ
      rw [energy_hamZ_eq, energy_hamZ_basisState]
      calc ∑ x : Config n, ‖(tensorOp UYᴴ *ᵥ ψ) x‖ ^ 2 * (hamZ G w x x).re
          ≤ ∑ x : Config n, ‖(tensorOp UYᴴ *ᵥ ψ) x‖ ^ 2 * (hamZ G w z z).re :=
            Finset.sum_le_sum fun x _ => mul_le_mul_of_nonneg_left (hz_max x (Finset.mem_univ _)) (sq_nonneg _)
        _ = (hamZ G w z z).re := by
            rw [← Finset.sum_mul, show ∑ x : Config n, ‖(tensorOp UYᴴ *ᵥ ψ) x‖ ^ 2 = 1 from huy_unit, one_mul]
    have hz : energy (hamZ G w) ψ ≤ energy (hamZ G w) (basisState z) := by
      rw [energy_hamZ_eq, energy_hamZ_basisState]
      calc ∑ x : Config n, ‖ψ x‖ ^ 2 * (hamZ G w x x).re
          ≤ ∑ x : Config n, ‖ψ x‖ ^ 2 * (hamZ G w z z).re :=
            Finset.sum_le_sum fun x _ => mul_le_mul_of_nonneg_left (hz_max x (Finset.mem_univ _)) (sq_nonneg _)
        _ = (hamZ G w z z).re := by
            rw [← Finset.sum_mul, show ∑ x : Config n, ‖ψ x‖ ^ 2 = 1 from hψ, one_mul]
    linarith
  · have hdecomp : energy (hamiltonian G w) (basisState z) =
        totalWeight G w / 2 + energy (hamX G w) (basisState z) +
          energy (hamY G w) (basisState z) + energy (hamZ G w) (basisState z) := by
      unfold energy
      rw [hamiltonian_decomp]
      simp only [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_add,
        dotProduct_smul, Complex.add_re]
      have h1 : (star (basisState z) ⬝ᵥ basisState z).re = 1 := by
        have hnorm : (star (basisState z) ⬝ᵥ basisState z).re = ∑ x : Config n, ‖basisState z x‖ ^ 2 := by
          simp only [dotProduct, Pi.star_apply, Complex.re_sum]
          refine Finset.sum_congr rfl fun x _ => ?_
          rw [Complex.star_def, mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.ofReal_re]
        rw [hnorm]; exact basisState_isUnitState z
      rw [smul_eq_mul, Complex.re_ofReal_mul, h1, mul_one]
    have hx0 : energy (hamX G w) (basisState z) = 0 := by
      unfold energy hamX
      simp only [dotProduct, Matrix.mulVec, Pi.star_apply, Matrix.sum_apply, Matrix.smul_apply,
        Matrix.ite_apply, Matrix.zero_apply, smul_eq_mul]
      rw [Finset.sum_eq_single z]
      · simp only [basisState, ↓reduceIte, star_one, one_mul]
        have hz0 : ∑ y : Config n, (∑ i : Fin n, ∑ j : Fin n,
            if i < j ∧ G.Adj i j then ((-(1 / 2) * w s(i, j) : ℝ) : ℂ) *
              (onSite i pauliX * onSite j pauliX) z y else 0) *
            (if y = z then (1 : ℂ) else 0) = 0 := by
          rw [Finset.sum_eq_single z]
          · simp only [↓reduceIte, mul_one]
            refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_
            split_ifs with h
            · rw [off_diag_pair_basis_zero pauliX (by simp [pauliX]) (by simp [pauliX]) i j h.1.ne z,
                mul_zero]
            · rfl
          · intro y _ hy; simp [hy]
          · intro hz; exact absurd (Finset.mem_univ _) hz
        rw [hz0, Complex.zero_re]
      · intro x _ hx; simp [basisState, hx]
      · intro hz; exact absurd (Finset.mem_univ _) hz
    have hy0 : energy (hamY G w) (basisState z) = 0 := by
      unfold energy hamY
      simp only [dotProduct, Matrix.mulVec, Pi.star_apply, Matrix.sum_apply, Matrix.smul_apply,
        Matrix.ite_apply, Matrix.zero_apply, smul_eq_mul]
      rw [Finset.sum_eq_single z]
      · simp only [basisState, ↓reduceIte, star_one, one_mul]
        have hz0 : ∑ y : Config n, (∑ i : Fin n, ∑ j : Fin n,
            if i < j ∧ G.Adj i j then ((-(1 / 2) * w s(i, j) : ℝ) : ℂ) *
              (onSite i pauliY * onSite j pauliY) z y else 0) *
            (if y = z then (1 : ℂ) else 0) = 0 := by
          rw [Finset.sum_eq_single z]
          · simp only [↓reduceIte, mul_one]
            refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_
            split_ifs with h
            · rw [off_diag_pair_basis_zero pauliY (by simp [pauliY]) (by simp [pauliY]) i j h.1.ne z,
                mul_zero]
            · rfl
          · intro y _ hy; simp [hy]
          · intro hz; exact absurd (Finset.mem_univ _) hz
        rw [hz0, Complex.zero_re]
      · intro x _ hx; simp [basisState, hx]
      · intro hz; exact absurd (Finset.mem_univ _) hz
    rw [hdecomp, hx0, hy0, add_zero, add_zero]

end QMaxCutBeyond.TwoQubit

open QMaxCutBeyond.TwoQubit

theorem solution {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (w : Sym2 (Fin n) → ℝ) (hw : ∀ e, 0 ≤ w e) :
    ∃ z : Config n,
      (∀ ψ : Config n → ℂ, IsUnitState ψ →
        energy (hamZ G w) ψ ≤ energy (hamZ G w) (basisState z)) ∧
      (∀ ψ : Config n → ℂ, IsUnitState ψ →
        energy (hamiltonian G w) ψ ≤ totalWeight G w / 2 + 3 * energy (hamZ G w) (basisState z)) ∧
      energy (hamiltonian G w) (basisState z) =
        totalWeight G w / 2 + energy (hamZ G w) (basisState z) :=
  weighted_eq_18_19_aux G w hw
