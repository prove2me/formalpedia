-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Independent1.P04.maximally_coherent_preparation
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T21:38:51.108135+00:00
-- url     : https://prove2.me/submissions/ebd01cb6-ade2-4581-b875-b949cf0fc868

import Mathlib
import Definitions.Def_QAlgorithms_Defs_BasisCoherence
import Definitions.Def_QAlgorithms_Defs_ExtendedQuantumEntropy
import Definitions.Def_QAlgorithms_Defs_QuantumInformation
import Definitions.Def_QAlgorithms_Papers_Independent_Independent1_P04_Model
set_option autoImplicit false

/-! Quantifying Coherence, arXiv:1311.0275v3. Fixed bases and arbitrary finite dimensions.
Local predicates apply to density matrices only; invalid matrices carry no coherence guarantees. -/

noncomputable section

open scoped Matrix ComplexOrder

open QAlgorithms QAlgorithms.Papers QAlgorithms.Papers.Independent QAlgorithms.Papers.Independent.Independent1 QAlgorithms.Papers.Independent.Independent1.P04
attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

/-- PDF pp.5–6, (A.1)–(A.6): cyclic Kraus preparation, with erasure of mixed-state outcomes. -/
theorem gk_mod_unique {d : ℕ} (i j : Fin d) : ∀ a a' : Fin d,
    j.val = (i.val + a.val) % d → j.val = (i.val + a'.val) % d → a = a' := by
  intro a a' h1 h2
  have h : (i.val + a.val) % d = (i.val + a'.val) % d := h1.symm.trans h2
  have h' : a.val % d = a'.val % d := Nat.ModEq.add_left_cancel' i.val h
  rw [Nat.mod_eq_of_lt a.2, Nat.mod_eq_of_lt a'.2] at h'
  exact Fin.ext h'

theorem gk_mod_unique' {d : ℕ} (a i i' : Fin d)
    (h : (i.val + a.val) % d = (i'.val + a.val) % d) : i = i' := by
  have h' : i.val % d = i'.val % d := Nat.ModEq.add_right_cancel' a.val h
  rw [Nat.mod_eq_of_lt i.2, Nat.mod_eq_of_lt i'.2] at h'
  exact Fin.ext h'

theorem gk_mod_exists {d : ℕ} (i j : Fin d) :
    j.val = (i.val + ((j.val + d - i.val) % d)) % d := by
  rw [Nat.add_mod_mod]
  have : i.val + (j.val + d - i.val) = j.val + d := by have := i.2; omega
  rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt j.2]

theorem gk_sum_a {d : ℕ} (i j : Fin d) (x : ℂ) :
    ∑ a : Fin d, (if j.val = (i.val + a.val) % d then x else 0) = x := by
  have hd : 0 < d := Fin.pos i
  set a0 : Fin d := ⟨(j.val + d - i.val) % d, Nat.mod_lt _ hd⟩
  rw [Finset.sum_eq_single a0]
  · rw [if_pos (gk_mod_exists i j)]
  · intro b _ hb
    rw [if_neg]
    intro h
    exact hb (gk_mod_unique i j b a0 h (gk_mod_exists i j))
  · simp

theorem gk_conj_pure {d : ℕ} (A : CoherenceMatrix d) (u : EuclideanSpace ℂ (Fin d)) :
    A * pureDensity u * Aᴴ = Matrix.of fun i i' =>
      (A.mulVec (WithLp.ofLp u)) i * (starRingEnd ℂ) ((A.mulVec (WithLp.ofLp u)) i') := by
  ext i i'
  simp only [Matrix.mul_apply, pureDensity, Matrix.of_apply, Matrix.conjTranspose_apply,
    Matrix.mulVec, dotProduct, map_sum, map_mul, Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl; intro j _
  apply Finset.sum_congr rfl; intro k _
  simp [RCLike.star_def]; ring

theorem gk_kraus {d : ℕ} (c : EuclideanSpace ℂ (Fin d)) (hc : IsState c) :
    IsKrausFamily (cyclicPureKraus c) := by
  have hn : ∑ i, ‖c i‖^2 = 1 := by
    have := hc; unfold IsState at this
    rw [EuclideanSpace.norm_eq, Real.sqrt_eq_one] at this
    exact this
  unfold IsKrausFamily
  ext j j'
  simp only [Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, cyclicPureKraus,
    Matrix.of_apply]
  rw [Finset.sum_comm]
  by_cases hjj : j = j'
  · subst hjj
    simp only [Matrix.one_apply_eq]
    have : ∀ i : Fin d, ∑ a : Fin d, star (if j.val = (i.val + a.val) % d then c i else 0) *
        (if j.val = (i.val + a.val) % d then c i else 0) = ((‖c i‖^2 : ℝ) : ℂ) := by
      intro i
      rw [← gk_sum_a i j ((‖c i‖^2 : ℝ) : ℂ)]
      apply Finset.sum_congr rfl; intro a _
      split_ifs
      · rw [RCLike.star_def, mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
      · simp
    rw [Finset.sum_congr rfl (fun i _ => this i)]
    exact_mod_cast hn
  · rw [Matrix.one_apply_ne hjj]
    apply Finset.sum_eq_zero; intro i _
    apply Finset.sum_eq_zero; intro a _
    split_ifs with h1 h2
    · exact absurd (Fin.ext (h1.trans h2.symm)) hjj
    all_goals simp

theorem gk_smul_conj {d : ℕ} (s : ℂ) (K X : CoherenceMatrix d) :
    conjSuperop (s • K) X = (s * star s) • conjSuperop K X := by
  simp only [conjSuperop, Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, mul_comm (star s)]

theorem solution (d : ℕ) (hd : 0 < d) :
    IsState (uniformCoherentVector d) ∧
    (∀ c : EuclideanSpace ℂ (Fin d), IsState c →
      IsKrausFamily (cyclicPureKraus c) ∧
      (∀ i, PreservesDiagonalBranch (cyclicPureKraus c i)) ∧
      ∀ i, conjSuperop (cyclicPureKraus c i) (pureDensity (uniformCoherentVector d)) =
        ((d : ℂ)⁻¹) • pureDensity c) ∧
    ∀ rho : CoherenceMatrix d, IsDensityMatrix rho →
      ∃ (a : ℕ) (p : Fin a → ℝ) (c : Fin a → EuclideanSpace ℂ (Fin d)),
        Learning.IsDistribution p ∧ (∀ i, IsState (c i)) ∧
        rho = ensembleMixture p (fun i => pureDensity (c i)) ∧
        IsKrausFamily (cyclicMixedKraus p c) ∧
        (∀ i, PreservesDiagonalBranch (cyclicMixedKraus p c i)) ∧
        krausApply (cyclicMixedKraus p c) (pureDensity (uniformCoherentVector d)) = rho := by
  set u := uniformCoherentVector d with hudef
  have hsd : (0:ℝ) < Real.sqrt d := Real.sqrt_pos.2 (by exact_mod_cast hd)
  have hu : IsState u := by
    unfold IsState
    rw [EuclideanSpace.norm_eq, Real.sqrt_eq_one]
    simp only [hudef, uniformCoherentVector, norm_inv, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hsd, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, inv_pow,
      Real.sq_sqrt (Nat.cast_nonneg d)]
    have : (d:ℝ) ≠ 0 := by exact_mod_cast hd.ne'
    field_simp
  have hdiag : ∀ (c : EuclideanSpace ℂ (Fin d)) (a : Fin d),
      PreservesDiagonalBranch (cyclicPureKraus c a) := by
    intro c a X _ hX i i' hii'
    have hXd : X = Matrix.diagonal (fun i => X i i) := by
      ext p q
      by_cases h : p = q
      · subst h; simp
      · rw [hX p q h]; simp [Matrix.diagonal_apply_ne _ h]
    unfold conjSuperop
    rw [hXd, Matrix.mul_apply]
    apply Finset.sum_eq_zero; intro j _
    rw [Matrix.mul_diagonal]
    simp only [cyclicPureKraus, Matrix.of_apply, Matrix.conjTranspose_apply]
    split_ifs with h1 h2
    · exact absurd (gk_mod_unique' a i i' (h1.symm.trans h2)) hii'
    all_goals simp
  have hKu : ∀ (c : EuclideanSpace ℂ (Fin d)) (a : Fin d),
      (cyclicPureKraus c a).mulVec (WithLp.ofLp u) = fun i => c i * ((Real.sqrt d)⁻¹ : ℂ) := by
    intro c a
    ext i
    simp only [Matrix.mulVec, dotProduct, cyclicPureKraus, Matrix.of_apply, hudef,
      uniformCoherentVector]
    rw [Finset.sum_eq_single (⟨(i.val + a.val) % d, Nat.mod_lt _ hd⟩ : Fin d)]
    · simp
    · intro b _ hb
      rw [if_neg]; · simp
      intro h; exact hb (Fin.ext h)
    · simp
  have hconj : ∀ (c : EuclideanSpace ℂ (Fin d)) (a : Fin d),
      conjSuperop (cyclicPureKraus c a) (pureDensity u) = ((d : ℂ)⁻¹) • pureDensity c := by
    intro c a
    unfold conjSuperop
    rw [gk_conj_pure, hKu]
    ext i j
    simp only [Matrix.of_apply, Matrix.smul_apply, pureDensity, smul_eq_mul, map_mul]
    have h1 : (starRingEnd ℂ) ((Real.sqrt d)⁻¹ : ℂ) = ((Real.sqrt d)⁻¹ : ℂ) := by
      rw [← Complex.ofReal_inv, Complex.conj_ofReal]
    have h2 : ((Real.sqrt d)⁻¹ : ℂ) * ((Real.sqrt d)⁻¹ : ℂ) = (d : ℂ)⁻¹ := by
      rw [← mul_inv, ← Complex.ofReal_mul, Real.mul_self_sqrt (Nat.cast_nonneg d)]; simp
    rw [h1]
    linear_combination (c i * (starRingEnd ℂ) (c j)) * h2
  refine ⟨hu, fun c hc => ⟨gk_kraus c hc, hdiag c, hconj c⟩, ?_⟩
  intro rho hrho
  have hA := hrho.1.isHermitian
  set p : Fin d → ℝ := hA.eigenvalues with hp
  set c : Fin d → EuclideanSpace ℂ (Fin d) := fun k => hA.eigenvectorBasis k with hcdef
  have hp0 : ∀ k, 0 ≤ p k := fun k => hrho.1.eigenvalues_nonneg k
  have hp1 : ∑ k, p k = 1 := by
    have := hA.trace_eq_sum_eigenvalues
    rw [hrho.2] at this
    have := congrArg Complex.re this
    simpa using this.symm
  have hcs : ∀ k, IsState (c k) := fun k => hA.eigenvectorBasis.orthonormal.1 k
  have hdec : rho = ensembleMixture p (fun k => pureDensity (c k)) := by
    have hs := hA.spectral_theorem
    ext i j
    have := congrFun (congrFun hs i) j
    rw [this]
    simp only [Unitary.conjStarAlgAut_apply, Matrix.mul_apply, Matrix.diagonal_apply,
      ensembleMixture, Matrix.sum_apply, Matrix.smul_apply, pureDensity, Matrix.of_apply,
      hcdef, smul_eq_mul]
    simp [Matrix.star_apply, Finset.sum_ite_eq']
    apply Finset.sum_congr rfl; intro k _
    rw [hp]; ring
  refine ⟨d, p, c, ⟨hp0, hp1⟩, hcs, hdec, ?_, ?_, ?_⟩
  · unfold IsKrausFamily cyclicMixedKraus
    rw [Fintype.sum_prod_type]
    simp only [Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    have : ∀ k, ∑ a : Fin d, ((Real.sqrt (p k) : ℂ) * star (Real.sqrt (p k) : ℂ)) •
        ((cyclicPureKraus (c k) a)ᴴ * cyclicPureKraus (c k) a) = (p k : ℂ) • (1 : CoherenceMatrix d) := by
      intro k
      rw [← Finset.smul_sum, gk_kraus (c k) (hcs k)]
      congr 1
      rw [RCLike.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul,
        Real.mul_self_sqrt (hp0 k)]
    rw [Finset.sum_congr rfl (fun k _ => this k), ← Finset.sum_smul]
    rw [show (∑ k, (p k : ℂ)) = 1 by exact_mod_cast hp1, one_smul]
  · intro ⟨k, a⟩ X hX hXd i j hij
    simp only [cyclicMixedKraus]
    rw [gk_smul_conj, Matrix.smul_apply, hdiag (c k) a X hX hXd i j hij, smul_zero]
  · unfold krausApply cyclicMixedKraus
    rw [Fintype.sum_prod_type]
    have : ∀ k, ∑ a : Fin d, ((Real.sqrt (p k) : ℂ) • cyclicPureKraus (c k) a) * pureDensity u *
        ((Real.sqrt (p k) : ℂ) • cyclicPureKraus (c k) a)ᴴ = (p k : ℂ) • pureDensity (c k) := by
      intro k
      have e := fun a => gk_smul_conj (Real.sqrt (p k) : ℂ) (cyclicPureKraus (c k) a) (pureDensity u)
      simp only [conjSuperop] at e
      simp only [e]
      have e2 := fun a => hconj (c k) a
      simp only [conjSuperop] at e2
      simp only [e2, smul_smul, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
      rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul]
      congr 1
      rw [RCLike.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul,
        Real.mul_self_sqrt (hp0 k)]
      have : (d:ℂ) ≠ 0 := by exact_mod_cast hd.ne'
      field_simp
    rw [Finset.sum_congr rfl (fun k _ => this k)]
    exact hdec.symm

