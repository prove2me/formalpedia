-- Prove2me | solution 1 for TensorBTD.Gramian.theorem_4_5
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-10T20:54:46.104976+00:00
-- url     : https://prove2.me/submissions/0f35d6fa-c510-41c2-bd79-bbe6ebe7d9ea

import Mathlib
import Definitions.Def_TensorBTD_Gramian_Setting

namespace RRAux_TensorBTD_Gramian_theorem_4_5

open Matrix TensorBTD.Gramian

variable {P Q R : ℕ} {I : Fin P ⊕ Fin Q → ℕ} {L : Fin R → ℕ}

lemma cpdModel_apply (F : (n : Fin P ⊕ Fin Q) → Matrix (Fin (I n)) (Col L) ℂ)
    (ι : (n : Fin P ⊕ Fin Q) → Fin (I n)) :
    cpdModel F ι = ∑ c : Col L, ∏ n, F n (ι n) c := by
  simp [cpdModel, outer, Finset.sum_apply]

lemma deriv_cpd (A D : (n : Fin P ⊕ Fin Q) → Matrix (Fin (I n)) (Col L) ℂ) (T : Tensor I)
    (ι : (n : Fin P ⊕ Fin Q) → Fin (I n)) :
    deriv (fun t : ℂ => cpdModel (fun n => A n + t • D n) ι - T ι) 0 =
      ∑ c : Col L, ∑ n, (∏ m ∈ Finset.univ.erase n, A m (ι m) c) * D n (ι n) c := by
  have h : HasDerivAt (fun t : ℂ => cpdModel (fun n => A n + t • D n) ι - T ι)
      (∑ c : Col L, ∑ n, (∏ m ∈ Finset.univ.erase n, A m (ι m) c) * D n (ι n) c) 0 := by
    simp only [cpdModel_apply]
    apply HasDerivAt.sub_const
    have hc : ∀ c : Col L, HasDerivAt (fun t : ℂ => ∏ n, (A n + t • D n) (ι n) c)
        (∑ n, (∏ m ∈ Finset.univ.erase n, A m (ι m) c) * D n (ι n) c) 0 := by
      intro c
      have := HasDerivAt.fun_finsetProd (u := Finset.univ) (x := (0 : ℂ))
        (f := fun n (t : ℂ) => (A n + t • D n) (ι n) c) (f' := fun n => D n (ι n) c)
        (fun n _ => by
          simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
          simpa using ((hasDerivAt_id (0 : ℂ)).mul_const (D n (ι n) c)).const_add (A n (ι n) c))
      simpa using this
    simpa using HasDerivAt.fun_sum (u := Finset.univ) (fun c _ => hc c)
  exact h.deriv

lemma cpdFactor_add (x e : GIdx I L → ℂ) (t : ℂ) :
    cpdFactor (x + t • e) = fun n => cpdFactor x n + t • cpdFactor e n := by
  funext n; ext i c; simp [cpdFactor]

lemma factor_add (z e : Unk I L → ℂ) (t : ℂ) :
    factor (z + t • e) = fun n => factor z n + t • factor e n := by
  funext n
  rcases n with p | q
  · ext i c; simp [factor, aMat]
  · have : cMat (z + t • e) q = cMat z q + t • cMat e q := by ext i r; simp [cMat]
    simp only [factor, this, Matrix.add_mul, Matrix.smul_mul]

lemma cpdFactor_fullVec (z : Unk I L → ℂ) : cpdFactor (fullVec z) = factor z := by
  funext n; ext i c; rfl

lemma jac_cpd (T : Tensor I) (x : GIdx I L → ℂ) (ι : (n : Fin P ⊕ Fin Q) → Fin (I n))
    (g : GIdx I L) :
    jac (cpdResidual T) x ι g = ∑ c : Col L, ∑ n,
      (∏ m ∈ Finset.univ.erase n, cpdFactor x m (ι m) c) * cpdFactor (Pi.single g 1) n (ι n) c := by
  simp only [jac, of_apply, cpdResidual, cpdFactor_add, Pi.sub_apply]
  exact deriv_cpd _ _ T ι

lemma jac_res (T : Tensor I) (z : Unk I L → ℂ) (ι : (n : Fin P ⊕ Fin Q) → Fin (I n))
    (β : Unk I L) :
    jac (TensorBTD.Gramian.residual T) z ι β = ∑ c : Col L, ∑ n,
      (∏ m ∈ Finset.univ.erase n, factor z m (ι m) c) * factor (Pi.single β 1) n (ι n) c := by
  simp only [jac, of_apply, TensorBTD.Gramian.residual, factor_add, Pi.sub_apply]
  exact deriv_cpd _ _ T ι

lemma sig_eq_iff {n n0 : Fin P ⊕ Fin Q} {c c0 : Col L} {k : Fin (I n)} {i0 : Fin (I n0)} :
    (⟨n, (c, k)⟩ : GIdx I L) = ⟨n0, (c0, i0)⟩ ↔
      c = c0 ∧ (⟨n, k⟩ : Σ n, Fin (I n)) = ⟨n0, i0⟩ := by
  constructor
  · intro h; cases h; simp
  · rintro ⟨rfl, h⟩; cases h; rfl

/-- entry of the unstructured Jacobian as a product over modes. -/
lemma jac_cpd_prod (T : Tensor I) (x : GIdx I L → ℂ) (ι : (n : Fin P ⊕ Fin Q) → Fin (I n))
    (n0 : Fin P ⊕ Fin Q) (c0 : Col L) (i0 : Fin (I n0)) :
    jac (cpdResidual T) x ι ⟨n0, (c0, i0)⟩ = ∏ n, (if n = n0 then
      (if (⟨n, ι n⟩ : Σ n, Fin (I n)) = ⟨n0, i0⟩ then 1 else 0) else cpdFactor x n (ι n) c0) := by
  rw [jac_cpd]
  have hsingle : ∀ n c, cpdFactor (Pi.single (⟨n0, (c0, i0)⟩ : GIdx I L) (1 : ℂ)) n (ι n) c =
      if c = c0 ∧ (⟨n, ι n⟩ : Σ n, Fin (I n)) = ⟨n0, i0⟩ then 1 else 0 := by
    intro n c
    simp only [cpdFactor, of_apply, Pi.single_apply]
    exact if_congr sig_eq_iff rfl rfl
  simp only [hsingle]
  rw [Finset.sum_eq_single c0]
  · rw [Finset.sum_eq_single n0]
    · rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ n0)]
      simp only [if_pos rfl, true_and]
      rw [mul_comm]
      congr 1
      refine Finset.prod_congr rfl fun n hn => ?_
      rw [if_neg (Finset.ne_of_mem_erase hn)]
    · intro n _ hn
      have : ¬ ((⟨n, ι n⟩ : Σ n, Fin (I n)) = ⟨n0, i0⟩) := fun h => hn (congrArg Sigma.fst h)
      simp [this]
    · simp
  · intro c _ hc
    refine Finset.sum_eq_zero fun n _ => ?_
    simp [hc]
  · simp

def hfun (A : (n : Fin P ⊕ Fin Q) → Matrix (Fin (I n)) (Col L) ℂ)
    (n1 : Fin P ⊕ Fin Q) (c1 : Col L) (i1 : Fin (I n1))
    (n2 : Fin P ⊕ Fin Q) (c2 : Col L) (i2 : Fin (I n2))
    (n : Fin P ⊕ Fin Q) (k : Fin (I n)) : ℂ :=
  star (if n = n1 then
    (if (⟨n, k⟩ : Σ n, Fin (I n)) = ⟨n1, i1⟩ then (1 : ℂ) else 0) else A n k c1) *
  (if n = n2 then
    (if (⟨n, k⟩ : Σ n, Fin (I n)) = ⟨n2, i2⟩ then (1 : ℂ) else 0) else A n k c2)

lemma gram_cpd (T : Tensor I) (x : GIdx I L → ℂ) :
    (jac (cpdResidual T) x)ᴴ * jac (cpdResidual T) x = PiMat (cpdFactor x) := by
  ext ⟨n1, c1, i1⟩ ⟨n2, c2, i2⟩
  simp only [Matrix.mul_apply, conjTranspose_apply, jac_cpd_prod]
  have hprod : ∀ ι : (n : Fin P ⊕ Fin Q) → Fin (I n),
      star (∏ n, (if n = n1 then
        (if (⟨n, ι n⟩ : Σ n, Fin (I n)) = ⟨n1, i1⟩ then (1 : ℂ) else 0) else cpdFactor x n (ι n) c1)) *
      ∏ n, (if n = n2 then
        (if (⟨n, ι n⟩ : Σ n, Fin (I n)) = ⟨n2, i2⟩ then (1 : ℂ) else 0) else cpdFactor x n (ι n) c2) =
      ∏ n, hfun (cpdFactor x) n1 c1 i1 n2 c2 i2 n (ι n) := by
    intro ι
    simp only [hfun]
    rw [Finset.prod_mul_distrib]
    congr 1
    exact (map_prod (starRingEnd ℂ) _ _)
  rw [Finset.sum_congr rfl fun ι _ => hprod ι, ← Fintype.prod_sum]
  set S := fun n => ∑ k : Fin (I n), hfun (cpdFactor x) n1 c1 i1 n2 c2 i2 n k with hS
  have hgen : ∀ n, n ≠ n1 → n ≠ n2 → S n = ((cpdFactor x n)ᴴ * cpdFactor x n) c1 c2 := by
    intro n h1 h2
    simp [hS, hfun, h1, h2, Matrix.mul_apply]
  simp only [PiMat, of_apply]
  by_cases h12 : n1 = n2
  · subst h12
    rw [if_pos rfl]
    rw [← Finset.mul_prod_erase Finset.univ S (Finset.mem_univ n1), mul_comm]
    have hW : W {n1} (cpdFactor x) c1 c2 = ∏ n ∈ Finset.univ.erase n1, S n := by
      simp only [W, of_apply]
      have : Finset.univ.filter (· ∉ ({n1} : Finset (Fin P ⊕ Fin Q))) = Finset.univ.erase n1 := by
        ext n; simp
      rw [this]
      exact Finset.prod_congr rfl fun n hn => (hgen n (Finset.ne_of_mem_erase hn)
        (Finset.ne_of_mem_erase hn)).symm
    rw [hW]
    congr 1
    simp only [hS, hfun, if_pos rfl]
    simp only [Sigma.mk.inj_iff, heq_eq_eq, true_and]
    rw [Finset.sum_eq_single i1]
    · by_cases hi : i1 = i2 <;> simp [hi]
    · intro k _ hk; simp [hk]
    · simp
  · rw [if_neg h12]
    rw [← Finset.mul_prod_erase Finset.univ S (Finset.mem_univ n1),
      ← Finset.mul_prod_erase (Finset.univ.erase n1) S
        (Finset.mem_erase.mpr ⟨Ne.symm h12, Finset.mem_univ n2⟩)]
    have hW : W {n1, n2} (cpdFactor x) c1 c2 = ∏ n ∈ (Finset.univ.erase n1).erase n2, S n := by
      simp only [W, of_apply]
      have : Finset.univ.filter (· ∉ ({n1, n2} : Finset (Fin P ⊕ Fin Q))) =
          (Finset.univ.erase n1).erase n2 := by
        ext n; simp; tauto
      rw [this]
      refine Finset.prod_congr rfl fun n hn => ?_
      have h2 := Finset.ne_of_mem_erase hn
      have h1 := Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hn)
      exact (hgen n h1 h2).symm
    have hS1 : S n1 = cpdFactor x n1 i1 c2 := by
      simp only [hS, hfun, if_pos rfl, if_neg h12, Sigma.mk.inj_iff, heq_eq_eq, true_and]
      rw [Finset.sum_eq_single i1]
      · simp
      · intro k _ hk; simp [hk]
      · simp
    have hS2 : S n2 = starRingEnd ℂ (cpdFactor x n2 i2 c1) := by
      simp only [hS, hfun, if_pos rfl, if_neg (Ne.symm h12), Sigma.mk.inj_iff, heq_eq_eq, true_and]
      rw [Finset.sum_eq_single i2]
      · simp
      · intro k _ hk; simp [hk]
      · simp
    rw [hW, hS1, hS2]
    ring

lemma sigma_eq_factor (β : Unk I L) (g : GIdx I L) :
    TensorBTD.Gramian.Sigma I L β g = factor (Pi.single β 1) g.1 g.2.2 g.2.1 := by
  rcases β with ⟨nb, u, i⟩
  rcases g with ⟨ng, c, k⟩
  by_cases h : nb = ng
  · subst h
    rw [TensorBTD.Gramian.Sigma, blockDiagonal'_apply_eq]
    rcases nb with p | q
    · simp only [SigmaBlock, factor, aMat, of_apply, Pi.single_apply]
      show (1 : Matrix (Col L × Fin (I (Sum.inl p))) (Col L × Fin (I (Sum.inl p))) ℂ)
        ((u : Col L), i) (c, k) = _
      rw [Matrix.one_apply]
      refine if_congr ?_ rfl rfl
      constructor
      · intro h; cases h; rfl
      · intro h; cases h; rfl
    · simp only [SigmaBlock, F, factor, cMat, Matrix.mul_apply, of_apply, Pi.single_apply]
      show Matrix.kroneckerMap (fun x1 x2 => x1 * x2) (E L)
        (1 : Matrix (Fin (I (Sum.inr q))) (Fin (I (Sum.inr q))) ℂ) ((u : Fin R), i) (c, k) = _
      rw [Matrix.kroneckerMap_apply, Matrix.one_apply]
      change Fin R at u
      show ((if c.fst = u then (1 : ℂ) else 0) * if i = k then 1 else 0) = _
      rw [Finset.sum_eq_single u]
      · by_cases hk : k = i
        · subst hk; simp [E]
        · have : ¬ ((⟨Sum.inr q, (u, k)⟩ : Unk I L) = ⟨Sum.inr q, (u, i)⟩) := by
            intro h; cases h; exact hk rfl
          simp [hk, this, Ne.symm hk]
      · intro r _ hr
        have : ¬ ((⟨Sum.inr q, (r, k)⟩ : Unk I L) = ⟨Sum.inr q, (u, i)⟩) := by
          intro h; cases h; exact hr rfl
        simp [this]
      · simp
  · rw [TensorBTD.Gramian.Sigma, blockDiagonal'_apply_ne _ _ _ h]
    rcases ng with p | q
    · simp only [factor, aMat, of_apply, Pi.single_apply]
      rw [if_neg]
      intro h'; exact h (congrArg Sigma.fst h').symm
    · simp only [factor, cMat, Matrix.mul_apply, of_apply, Pi.single_apply]
      refine (Finset.sum_eq_zero fun r _ => ?_).symm
      rw [if_neg, zero_mul]
      intro h'; exact h (congrArg Sigma.fst h').symm

lemma sigma_star (β : Unk I L) (g : GIdx I L) : star (TensorBTD.Gramian.Sigma I L β g) = TensorBTD.Gramian.Sigma I L β g := by
  rw [sigma_eq_factor]
  rcases β with ⟨nb, u, i⟩
  rcases g with ⟨ng, c, k⟩
  rcases ng with p | q
  · simp only [factor, aMat, of_apply, Pi.single_apply]
    split_ifs <;> simp
  · simp only [factor, cMat, Matrix.mul_apply, of_apply, Pi.single_apply, E]
    rw [star_sum]
    refine Finset.sum_congr rfl fun r _ => ?_
    split_ifs <;> simp

lemma jac_res_eq (T : Tensor I) (z : Unk I L → ℂ) :
    jac (TensorBTD.Gramian.residual T) z = jac (cpdResidual T) (fullVec z) * (TensorBTD.Gramian.Sigma I L)ᵀ := by
  ext ι β
  rw [jac_res, Matrix.mul_apply]
  simp only [jac_cpd, cpdFactor_fullVec, transpose_apply]
  simp only [Finset.sum_mul, mul_assoc]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => ?_
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [← Finset.mul_sum]
  congr 1
  simp only [cpdFactor, of_apply, Pi.single_apply, ite_mul, one_mul, zero_mul]
  rw [Finset.sum_ite_eq]
  simp [sigma_eq_factor]

end RRAux_TensorBTD_Gramian_theorem_4_5

open RRAux_TensorBTD_Gramian_theorem_4_5 in
open TensorBTD.Gramian in
open Matrix in
theorem solution {P Q R : ℕ} {I : Fin P ⊕ Fin Q → ℕ} {L : Fin R → ℕ}
    (T : Tensor I) (z : Unk I L → ℂ) :
    (jac (cpdResidual T) (fullVec z))ᴴ * jac (cpdResidual T) (fullVec z) = PiMat (factor z) ∧
    (jac (residual T) z)ᴴ * jac (residual T) z =
      Sigma I L * PiMat (factor z) * (Sigma I L)ᵀ := by
  have h1 := gram_cpd T (fullVec z)
  rw [cpdFactor_fullVec] at h1
  refine ⟨h1, ?_⟩
  have hS : ((Sigma I L)ᵀ)ᴴ = Sigma I L := by
    ext a b
    simp [conjTranspose_apply, transpose_apply, sigma_star]
  rw [jac_res_eq, conjTranspose_mul, hS, Matrix.mul_assoc, ← Matrix.mul_assoc _ _ (Sigma I L)ᵀ, h1,
    Matrix.mul_assoc]

#print axioms solution
