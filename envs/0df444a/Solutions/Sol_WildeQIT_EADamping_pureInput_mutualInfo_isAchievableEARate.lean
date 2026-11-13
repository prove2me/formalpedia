-- Prove2me | solution 1 for WildeQIT.EADamping.pureInput_mutualInfo_isAchievableEARate
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-13T05:15:56.768861+00:00
-- url     : https://prove2.me/submissions/698a1957-e3cc-4b31-82e9-20239514cf9f

import Mathlib
import Definitions.Def_DattaDiscord_mutualInfo
import Definitions.Def_QAlgorithms_Defs_Ensemble
import Definitions.Def_WildeQIT_EADamping_EACode_errorProb
import Definitions.Def_WildeQIT_EADamping_IsAchievableEARate
import Definitions.Def_WildeQIT_EADamping_channelMutualInfo
import Definitions.Def_WildeQIT_EADamping_idTensorApply
import Definitions.Def_WildeQIT_QChannel

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false



/-! C4 step E3: tensor powers `kpow M k : Matrix (Fin k → ι) (Fin k → ι) ℂ`, multiplicativity,
trace, and `(M^{⊗k})^p = (M^p)^{⊗k}` for `M ≥ 0`. (SSALib block = copy of 7e1785ee_SSA1.lean helpers;
drop it in the assembly.) -/

namespace SSALib
open Matrix
open scoped ComplexOrder

lemma exists_poly (s : Finset ℝ) (f : ℝ → ℝ) : ∃ p : Polynomial ℝ, ∀ x ∈ s, p.eval x = f x := by
  refine ⟨Lagrange.interpolate s id f, fun x hx => ?_⟩
  have := Lagrange.eval_interpolate_at_node (s := s) (v := id) f (Set.injOn_id _) hx
  simpa using this

lemma cfc_eq_aeval {n : Type} [Fintype n] [DecidableEq n] (A : Matrix n n ℂ) (hA : A.IsHermitian)
    (p : Polynomial ℝ) (f : ℝ → ℝ) (hs : ∀ x ∈ spectrum ℝ A, p.eval x = f x) :
    cfc f A = Polynomial.aeval A p := by
  rw [← cfc_polynomial p A hA.isSelfAdjoint]
  exact cfc_congr (fun x hx => (hs x hx).symm)

/-- Functional calculus respects intertwiners: `A V = V B` implies `f(A) V = V f(B)`. -/
lemma cfc_intertwine {m n : Type} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (A : Matrix m m ℂ) (B : Matrix n n ℂ) (hA : A.IsHermitian) (hB : B.IsHermitian)
    (V : Matrix m n ℂ) (h : A * V = V * B) (f : ℝ → ℝ) :
    cfc f A * V = V * cfc f B := by
  have fA : (spectrum ℝ A).Finite := Matrix.finite_real_spectrum
  have fB : (spectrum ℝ B).Finite := Matrix.finite_real_spectrum
  obtain ⟨p, hp⟩ := exists_poly (fA.toFinset ∪ fB.toFinset) f
  rw [cfc_eq_aeval A hA p f (fun x hx => hp x (by simp [hx])),
    cfc_eq_aeval B hB p f (fun x hx => hp x (by simp [hx]))]
  have hpow : ∀ k : ℕ, A ^ k * V = V * B ^ k := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ, Matrix.mul_assoc, h, ← Matrix.mul_assoc, ih, Matrix.mul_assoc, ← pow_succ]
  rw [Polynomial.aeval_eq_sum_range, Polynomial.aeval_eq_sum_range, Matrix.sum_mul, Matrix.mul_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Matrix.smul_mul, Matrix.mul_smul, hpow]

lemma aeval_diag {n : Type} [Fintype n] [DecidableEq n] (d : n → ℝ) (p : Polynomial ℝ) :
    Polynomial.aeval (Matrix.diagonal (fun i => (d i : ℂ))) p =
      Matrix.diagonal (fun i => ((p.eval (d i) : ℝ) : ℂ)) := by
  ext i j
  rw [Polynomial.aeval_eq_sum_range, Matrix.sum_apply, Matrix.diagonal_apply]
  simp only [Polynomial.eval_eq_sum_range, Matrix.smul_apply, Matrix.diagonal_pow, Matrix.diagonal_apply,
    Pi.pow_apply]
  by_cases h : i = j
  · subst h
    simp only [if_true, Complex.ofReal_sum, Complex.ofReal_mul, Complex.ofReal_pow, Complex.real_smul]
  · simp [h]

lemma herm_diag {n : Type} [Fintype n] [DecidableEq n] (d : n → ℝ) :
    (Matrix.diagonal (fun i => (d i : ℂ))).IsHermitian := by
  rw [Matrix.IsHermitian, Matrix.diagonal_conjTranspose]
  congr 1; funext i; simp

lemma cfc_diag {n : Type} [Fintype n] [DecidableEq n] (d : n → ℝ) (f : ℝ → ℝ) :
    cfc f (Matrix.diagonal (fun i => (d i : ℂ))) = Matrix.diagonal (fun i => (f (d i) : ℂ)) := by
  have fD : (spectrum ℝ (Matrix.diagonal (fun i => (d i : ℂ)))).Finite := Matrix.finite_real_spectrum
  obtain ⟨p, hp⟩ := exists_poly (fD.toFinset ∪ Finset.univ.image d) f
  rw [cfc_eq_aeval _ (herm_diag d) p f (fun x hx => hp x (by simp [hx])), aeval_diag]
  congr 1; funext i; rw [hp (d i) (by simp)]

lemma eig_intertwine {n : Type} [Fintype n] [DecidableEq n] {σ : Matrix n n ℂ} (hσ : σ.IsHermitian) :
    σ * (hσ.eigenvectorUnitary : Matrix n n ℂ) =
      (hσ.eigenvectorUnitary : Matrix n n ℂ) * Matrix.diagonal (fun i => ((hσ.eigenvalues i : ℝ) : ℂ)) := by
  have hs := congrArg (· * (hσ.eigenvectorUnitary : Matrix n n ℂ)) hσ.spectral_theorem
  beta_reduce at hs
  rw [hs, Unitary.conjStarAlgAut_apply, Matrix.mul_assoc, Unitary.coe_star_mul_self, Matrix.mul_one]
  rfl

lemma unit_mul_star' {n : Type} [Fintype n] [DecidableEq n] {σ : Matrix n n ℂ} (hσ : σ.IsHermitian) :
    (hσ.eigenvectorUnitary : Matrix n n ℂ) * (hσ.eigenvectorUnitary : Matrix n n ℂ)ᴴ = 1 :=
  Unitary.coe_mul_star_self _

end SSALib

namespace KPLib
open Matrix SSALib
open scoped ComplexOrder

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- `k`-fold Kronecker power, indexed by `Fin k → ι`. -/
noncomputable def kpow (M : Matrix ι ι ℂ) (k : ℕ) : Matrix (Fin k → ι) (Fin k → ι) ℂ :=
  Matrix.of fun f g => ∏ i, M (f i) (g i)

lemma kpow_apply (M : Matrix ι ι ℂ) (k : ℕ) (f g : Fin k → ι) :
    kpow M k f g = ∏ i, M (f i) (g i) := rfl

lemma kpow_mul (M N : Matrix ι ι ℂ) (k : ℕ) : kpow M k * kpow N k = kpow (M * N) k := by
  ext f g
  simp only [Matrix.mul_apply, kpow_apply]
  rw [Finset.prod_univ_sum, Fintype.piFinset_univ]
  refine Finset.sum_congr rfl (fun h _ => ?_)
  rw [Finset.prod_mul_distrib]

lemma kpow_one (k : ℕ) : kpow (1 : Matrix ι ι ℂ) k = 1 := by
  ext f g
  simp [kpow_apply, Matrix.one_apply, Finset.prod_boole, funext_iff]

lemma kpow_diagonal (d : ι → ℂ) (k : ℕ) :
    kpow (Matrix.diagonal d) k = Matrix.diagonal (fun f : Fin k → ι => ∏ i, d (f i)) := by
  ext f g
  rw [kpow_apply, Matrix.diagonal_apply]
  by_cases h : f = g
  · subst h; simp [Matrix.diagonal_apply]
  · rw [if_neg h]
    obtain ⟨i, hi⟩ : ∃ i, f i ≠ g i := by
      by_contra hc; push_neg at hc; exact h (funext hc)
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [Matrix.diagonal_apply, hi])

lemma kpow_conjTranspose (M : Matrix ι ι ℂ) (k : ℕ) : (kpow M k)ᴴ = kpow Mᴴ k := by
  ext f g
  simp only [Matrix.conjTranspose_apply, kpow_apply]
  exact map_prod (starRingEnd ℂ) _ _

lemma trace_kpow (M : Matrix ι ι ℂ) (k : ℕ) : (kpow M k).trace = M.trace ^ k := by
  simp only [Matrix.trace, Matrix.diag, kpow_apply]
  rw [← Fin.prod_const, Finset.prod_univ_sum, Fintype.piFinset_univ]

lemma kpow_herm {M : Matrix ι ι ℂ} (hM : M.IsHermitian) (k : ℕ) : (kpow M k).IsHermitian := by
  rw [Matrix.IsHermitian, kpow_conjTranspose, hM.eq]

lemma kpow_unit {U : Matrix ι ι ℂ} (hU : U * Uᴴ = 1) (k : ℕ) : kpow U k * (kpow U k)ᴴ = 1 := by
  rw [kpow_conjTranspose, kpow_mul, hU, kpow_one]

/-- `f(M^{⊗k}) = f(M)^{⊗k}` when `f` is multiplicative on the eigenvalues of `M`. -/
lemma cfc_kpow {M : Matrix ι ι ℂ} (hM : M.IsHermitian) (k : ℕ) (f : ℝ → ℝ)
    (hf : ∀ x : Fin k → ι, f (∏ i, hM.eigenvalues (x i)) = ∏ i, f (hM.eigenvalues (x i))) :
    cfc f (kpow M k) = kpow (cfc f M) k := by
  set U : Matrix ι ι ℂ := (hM.eigenvectorUnitary : Matrix ι ι ℂ) with hUdef
  set D := Matrix.diagonal (fun i => ((hM.eigenvalues i : ℝ) : ℂ)) with hDdef
  have e : M * U = U * D := eig_intertwine hM
  have hD : kpow D k = Matrix.diagonal (fun x : Fin k → ι => ((∏ i, hM.eigenvalues (x i) : ℝ) : ℂ)) := by
    rw [hDdef, kpow_diagonal]; congr 1; funext x; push_cast; rfl
  have ek : kpow M k * kpow U k = kpow U k * kpow D k := by rw [kpow_mul, kpow_mul, e]
  have h1 := cfc_intertwine (kpow M k) (kpow D k) (kpow_herm hM k) (by rw [hD]; exact herm_diag _)
    (kpow U k) ek f
  rw [hD, cfc_diag] at h1
  have h2 := cfc_intertwine M D hM (herm_diag _) U e f
  rw [hDdef, cfc_diag] at h2
  have h3 : kpow U k * Matrix.diagonal (fun x : Fin k → ι => ((f (∏ i, hM.eigenvalues (x i)) : ℝ) : ℂ)) =
      kpow (cfc f M) k * kpow U k := by
    rw [kpow_mul, h2, ← kpow_mul, kpow_diagonal]
    congr 2; funext x; rw [hf x]; push_cast; rfl
  have hUU : kpow U k * (kpow U k)ᴴ = 1 := kpow_unit (unit_mul_star' hM) k
  calc cfc f (kpow M k) = cfc f (kpow M k) * (kpow U k * (kpow U k)ᴴ) := by rw [hUU, Matrix.mul_one]
    _ = kpow (cfc f M) k * kpow U k * (kpow U k)ᴴ := by rw [← Matrix.mul_assoc, h1, h3]
    _ = kpow (cfc f M) k := by rw [Matrix.mul_assoc, hUU, Matrix.mul_one]

open scoped Matrix.Norms.L2Operator MatrixOrder

lemma kpow_nonneg {A : Matrix ι ι ℂ} (hA : 0 ≤ A) (k : ℕ) : 0 ≤ kpow A k := by
  have hs : IsSelfAdjoint (CFC.sqrt A) := (CFC.sqrt_nonneg A).isSelfAdjoint
  have e : A = star (CFC.sqrt A) * CFC.sqrt A := by rw [hs.star_eq, CFC.sqrt_mul_sqrt_self A hA]
  have : kpow A k = star (kpow (CFC.sqrt A) k) * kpow (CFC.sqrt A) k := by
    rw [Matrix.star_eq_conjTranspose, kpow_conjTranspose, kpow_mul, ← Matrix.star_eq_conjTranspose, ← e]
  rw [this]; exact star_mul_self_nonneg _

lemma kpow_rpow {A : Matrix ι ι ℂ} (hA : 0 ≤ A) (k : ℕ) (r : ℝ) :
    cfc (fun x : ℝ => x ^ r) (kpow A k) = kpow (cfc (fun x : ℝ => x ^ r) A) k := by
  have hP := Matrix.nonneg_iff_posSemidef.mp hA
  refine cfc_kpow hP.isHermitian k _ (fun x => ?_)
  exact (Real.finset_prod_rpow _ _ (fun i _ => hP.eigenvalues_nonneg (x i)) r).symm

lemma kpow_nnrpow {A : Matrix ι ι ℂ} (hA : 0 ≤ A) (k : ℕ) {p : NNReal} (hp : 0 < p) :
    (kpow A k) ^ p = kpow (A ^ p) k := by
  rw [CFC.nnrpow_eq_rpow hp, CFC.nnrpow_eq_rpow hp, CFC.rpow_eq_cfc_real (kpow_nonneg hA k),
    CFC.rpow_eq_cfc_real hA, kpow_rpow hA]

/-- the Chernoff-type trace of tensor powers factorises. -/
lemma trace_kpow_pow {A B : Matrix ι ι ℂ} (hA : 0 ≤ A) (hB : 0 ≤ B) (k : ℕ) {p q : NNReal}
    (hp : 0 < p) (hq : 0 < q) :
    ((kpow A k) ^ p * (kpow B k) ^ q).trace = ((A ^ p * B ^ q).trace) ^ k := by
  rw [kpow_nnrpow hA k hp, kpow_nnrpow hB k hq, kpow_mul, trace_kpow]

end KPLib

namespace TayLib
open Matrix SSALib
open scoped ComplexOrder

variable {n : Type} [Fintype n] [DecidableEq n]

lemma cfc_conj {ρ : Matrix n n ℂ} (hρ : ρ.IsHermitian) (f : ℝ → ℝ) :
    cfc f ρ = (hρ.eigenvectorUnitary : Matrix n n ℂ) *
      Matrix.diagonal (fun i => ((f (hρ.eigenvalues i) : ℝ) : ℂ)) * (hρ.eigenvectorUnitary : Matrix n n ℂ)ᴴ := by
  have h := cfc_intertwine ρ _ hρ (herm_diag _) _ (eig_intertwine hρ) f
  rw [cfc_diag] at h
  rw [← h, Matrix.mul_assoc, unit_mul_star' hρ, Matrix.mul_one]

lemma tr_diag_conj (F G : n → ℝ) (V : Matrix n n ℂ) :
    (Matrix.diagonal (fun i => (F i : ℂ)) * V * Matrix.diagonal (fun j => (G j : ℂ)) * Vᴴ).trace =
      ((∑ i, ∑ j, F i * G j * Complex.normSq (V i j) : ℝ) : ℂ) := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply,
    Matrix.conjTranspose_apply]
  push_cast
  refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
  rw [← Complex.mul_conj]
  simp only [Matrix.diagonal_apply]
  simp
  ring

/-- Eigen-sum formula for `Tr f(ρ) g(σ)`. -/
theorem tr_cfc_cfc {ρ σ : Matrix n n ℂ} (hρ : ρ.IsHermitian) (hσ : σ.IsHermitian) (f g : ℝ → ℝ) :
    (cfc f ρ * cfc g σ).trace = ((∑ i, ∑ j, f (hρ.eigenvalues i) * g (hσ.eigenvalues j) *
      Complex.normSq (((hρ.eigenvectorUnitary : Matrix n n ℂ)ᴴ *
        (hσ.eigenvectorUnitary : Matrix n n ℂ)) i j) : ℝ) : ℂ) := by
  set U : Matrix n n ℂ := (hρ.eigenvectorUnitary : Matrix n n ℂ) with hU
  set W : Matrix n n ℂ := (hσ.eigenvectorUnitary : Matrix n n ℂ) with hW
  have hUU : U * Uᴴ = 1 := unit_mul_star' hρ
  have hUU' : Uᴴ * U = 1 := Unitary.coe_star_mul_self _
  rw [cfc_conj hρ f, cfc_conj hσ g, ← tr_diag_conj]
  set F := Matrix.diagonal (fun i => ((f (hρ.eigenvalues i) : ℝ) : ℂ))
  set G := Matrix.diagonal (fun j => ((g (hσ.eigenvalues j) : ℝ) : ℂ))
  have key : U * F * Uᴴ * (W * G * Wᴴ) = U * (F * (Uᴴ * W) * G * (Uᴴ * W)ᴴ) * Uᴴ := by
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc, hUU,
      Matrix.mul_one]
  rw [key, Matrix.trace_mul_comm, ← Matrix.mul_assoc, hUU', Matrix.one_mul]

lemma row_sum {V : Matrix n n ℂ} (hV : V * Vᴴ = 1) (i : n) : ∑ j, Complex.normSq (V i j) = 1 := by
  have h := congrFun (congrFun hV i) i
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply_eq] at h
  have h2 : ((∑ j, Complex.normSq (V i j) : ℝ) : ℂ) = 1 := by
    push_cast; rw [← h]; refine Finset.sum_congr rfl (fun j _ => ?_); rw [← Complex.mul_conj]; rfl
  exact_mod_cast h2

/-- scalar second-order bound. -/
lemma taylor_sum {ι κ : Type} [Fintype ι] [Fintype κ] (a : ι → ℝ) (b : κ → ℝ) (c : ι → κ → ℝ)
    (ha : ∀ i, 0 ≤ a i) (hb : ∀ j, 0 < b j) (hc : ∀ i j, 0 ≤ c i j) (hrow : ∀ i, ∑ j, c i j = 1)
    (u : ℝ) (hu0 : 0 < u) (hu1 : u < 1)
    (hsmall : ∀ i j, 0 < a i → u * |Real.log (a i) - Real.log (b j)| ≤ 1) :
    ∑ i, ∑ j, a i ^ (1 - u) * b j ^ u * c i j ≤
      ∑ i, a i - u * (∑ i, ∑ j, a i * c i j * (Real.log (a i) - Real.log (b j)))
        + u ^ 2 * ∑ i, ∑ j, a i * c i j * (Real.log (a i) - Real.log (b j)) ^ 2 := by
  have hterm : ∀ i j, a i ^ (1 - u) * b j ^ u * c i j ≤
      a i * c i j - u * (a i * c i j * (Real.log (a i) - Real.log (b j))) +
        u ^ 2 * (a i * c i j * (Real.log (a i) - Real.log (b j)) ^ 2) := by
    intro i j
    rcases (ha i).eq_or_lt with h0 | hpos
    · rw [← h0, Real.zero_rpow (by linarith)]; simp
    · set t := Real.log (a i) - Real.log (b j) with ht
      have hx : |-(u * t)| ≤ 1 := by rw [abs_neg, abs_mul, abs_of_pos hu0]; exact hsmall i j hpos
      have hE := Real.abs_exp_sub_one_sub_id_le hx
      have hE2 : Real.exp (-(u * t)) ≤ 1 + -(u * t) + (-(u * t)) ^ 2 := by
        have := (abs_le.mp hE).2; linarith
      have hprod : a i ^ (1 - u) * b j ^ u = a i * Real.exp (-(u * t)) := by
        rw [Real.rpow_def_of_pos hpos, Real.rpow_def_of_pos (hb j), ← Real.exp_add]
        conv_rhs => rw [← Real.exp_log hpos, ← Real.exp_add]
        congr 1; rw [ht]; ring
      rw [hprod]
      have hac : 0 ≤ a i * c i j := mul_nonneg (ha i) (hc i j)
      have h3 := mul_le_mul_of_nonneg_left hE2 hac
      calc a i * Real.exp (-(u * t)) * c i j = a i * c i j * Real.exp (-(u * t)) := by ring
        _ ≤ a i * c i j * (1 + -(u * t) + (-(u * t)) ^ 2) := h3
        _ = _ := by ring
  have e : ∀ i, ∑ j, a i * c i j = a i := fun i => by rw [← Finset.mul_sum, hrow, mul_one]
  calc _ ≤ ∑ i, ∑ j, (a i * c i j - u * (a i * c i j * (Real.log (a i) - Real.log (b j))) +
        u ^ 2 * (a i * c i j * (Real.log (a i) - Real.log (b j)) ^ 2)) :=
        Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => hterm i j))
    _ = _ := by
      simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, e]

open scoped Matrix.Norms.L2Operator MatrixOrder

/-- E4: `Tr ρ^{1-u} σ^u ≤ 1 - u D + u² K` for all small `u > 0`, `D` the eigen-sum relative entropy (nats). -/
theorem chernoff_taylor {ρ σ : Matrix n n ℂ} (hρ : 0 ≤ ρ) (htr : ρ.trace = 1) (hσ : σ.PosDef) :
    ∃ K : ℝ, ∃ u₀ : ℝ, 0 < u₀ ∧ ∀ u : ℝ, 0 < u → u ≤ u₀ →
      (cfc (fun x : ℝ => x ^ (1 - u)) ρ * cfc (fun x : ℝ => x ^ u) σ).trace.re ≤
        1 - u * ((cfc (id : ℝ → ℝ) ρ * cfc Real.log ρ).trace.re - (cfc (id : ℝ → ℝ) ρ * cfc Real.log σ).trace.re) + u ^ 2 * K := by
  have hP := Matrix.nonneg_iff_posSemidef.mp hρ
  set hρh := hP.isHermitian
  set hσh := hσ.isHermitian
  set a := hρh.eigenvalues
  set b := hσh.eigenvalues
  set c : n → n → ℝ := fun i j => Complex.normSq (((hρh.eigenvectorUnitary : Matrix n n ℂ)ᴴ *
        (hσh.eigenvectorUnitary : Matrix n n ℂ)) i j) with hcdef
  set t : n → n → ℝ := fun i j => Real.log (a i) - Real.log (b j)
  have ha : ∀ i, 0 ≤ a i := hP.eigenvalues_nonneg
  have hb : ∀ j, 0 < b j := hσ.eigenvalues_pos
  have hrow : ∀ i, ∑ j, c i j = 1 := by
    intro i
    refine row_sum ?_ i
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc,
      ← Matrix.mul_assoc _ _ (hρh.eigenvectorUnitary : Matrix n n ℂ), unit_mul_star' hσh, Matrix.one_mul]
    exact Unitary.coe_star_mul_self _
  have hsumA : ∑ i, a i = 1 := by
    have h1 := hρh.trace_eq_sum_eigenvalues
    rw [htr] at h1
    have h2 : ((∑ i, a i : ℝ) : ℂ) = 1 := by rw [Complex.ofReal_sum]; exact h1.symm
    exact_mod_cast h2
  set M : ℝ := ∑ i, ∑ j, |t i j| with hM
  have hM0 : 0 ≤ M := Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => abs_nonneg _))
  have hle : ∀ i j, |t i j| ≤ M := fun i j =>
    (Finset.single_le_sum (f := fun j => |t i j|) (fun j _ => abs_nonneg _) (Finset.mem_univ j)).trans
      (Finset.single_le_sum (f := fun i => ∑ j, |t i j|)
        (fun i _ => Finset.sum_nonneg (fun j _ => abs_nonneg _)) (Finset.mem_univ i))
  refine ⟨∑ i, ∑ j, a i * c i j * t i j ^ 2, 1 / (M + 2), by positivity, fun u hu0 hu => ?_⟩
  have hu1 : u < 1 := by
    have : 1 / (M + 2) < 1 := by rw [div_lt_one (by linarith)]; linarith
    linarith
  have hsmall : ∀ i j, 0 < a i → u * |t i j| ≤ 1 := by
    intro i j _
    calc u * |t i j| ≤ 1 / (M + 2) * M := mul_le_mul hu (hle i j) (abs_nonneg _) (by positivity)
      _ ≤ 1 := by rw [div_mul_eq_mul_div, one_mul, div_le_one (by linarith)]; linarith
  have hT := taylor_sum a b c ha hb (fun i j => Complex.normSq_nonneg _) hrow u hu0 hu1 hsmall
  have e1 := tr_cfc_cfc hρh hσh (fun x : ℝ => x ^ (1 - u)) (fun x : ℝ => x ^ u)
  have e2 := tr_cfc_cfc hρh hρh id Real.log
  have e3 := tr_cfc_cfc hρh hσh id Real.log
  rw [e1, e2, e3, Complex.ofReal_re, Complex.ofReal_re, Complex.ofReal_re]
  have hD2 : (∑ i, ∑ j, id (a i) * Real.log (a j) * Complex.normSq (((hρh.eigenvectorUnitary : Matrix n n ℂ)ᴴ *
        (hρh.eigenvectorUnitary : Matrix n n ℂ)) i j)) = ∑ i, a i * Real.log (a i) := by
    rw [show (hρh.eigenvectorUnitary : Matrix n n ℂ)ᴴ * (hρh.eigenvectorUnitary : Matrix n n ℂ) = 1 from
      Unitary.coe_star_mul_self _]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Finset.sum_eq_single i (fun j _ hj => by simp [Matrix.one_apply_ne' hj]) (by simp)]
    simp
  rw [hD2]
  have hD : ∑ i, ∑ j, a i * c i j * t i j = ∑ i, a i * Real.log (a i) -
      ∑ i, ∑ j, id (a i) * Real.log (b j) * c i j := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    have : a i * Real.log (a i) = ∑ j, a i * c i j * Real.log (a i) := by
      rw [← Finset.sum_mul, ← Finset.mul_sum, hrow, mul_one]
    rw [this, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    simp only [id, t]; ring
  rw [hsumA] at hT
  rw [← hD]
  exact hT

end TayLib

namespace OzLib
open Matrix
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder NNReal

variable {n : Type} [Fintype n] [DecidableEq n]

lemma tr_nonneg {P Q : Matrix n n ℂ} (hP : 0 ≤ P) (hQ : 0 ≤ Q) : 0 ≤ (P * Q).trace.re := by
  have hR : IsSelfAdjoint (CFC.sqrt P) := (CFC.sqrt_nonneg P).isSelfAdjoint
  have e : P * Q = CFC.sqrt P * (CFC.sqrt P * Q) := by
    rw [← Matrix.mul_assoc, CFC.sqrt_mul_sqrt_self P hP]
  rw [e, Matrix.trace_mul_comm, Matrix.mul_assoc]
  have h0 : 0 ≤ CFC.sqrt P * Q * CFC.sqrt P := by
    simpa [hR.star_eq] using star_left_conjugate_nonneg hQ (CFC.sqrt P)
  have h1 := (Matrix.nonneg_iff_posSemidef.mp h0).trace_nonneg
  rw [Matrix.mul_assoc] at h1
  exact (Complex.nonneg_iff.mp h1).1

lemma tr_mono {P Q₁ Q₂ : Matrix n n ℂ} (hP : 0 ≤ P) (h : Q₁ ≤ Q₂) :
    (P * Q₁).trace.re ≤ (P * Q₂).trace.re := by
  have := tr_nonneg hP (sub_nonneg.mpr h)
  rw [Matrix.mul_sub, Matrix.trace_sub, Complex.sub_re] at this
  linarith

lemma tr_mono' {P₁ P₂ Q : Matrix n n ℂ} (h : P₁ ≤ P₂) (hQ : 0 ≤ Q) :
    (P₁ * Q).trace.re ≤ (P₂ * Q).trace.re := by
  rw [Matrix.trace_mul_comm P₁, Matrix.trace_mul_comm P₂]
  have := tr_nonneg hQ (sub_nonneg.mpr h)
  rw [Matrix.mul_sub, Matrix.trace_sub, Complex.sub_re] at this
  linarith

/-- Ozawa's proof of the Audenaert inequality. -/
theorem oz {A B : Matrix n n ℂ} (hA : 0 ≤ A) (hB : 0 ≤ B) {p q : ℝ≥0} (hp : 0 < p) (hq : 0 < q)
    (hpq : p + q = 1) :
    A.trace.re - ((A - B)⁺).trace.re ≤ (A ^ p * B ^ q).trace.re := by
  set X := (A - B)⁺ with hXdef
  set C := B + X with hCdef
  have hX0 : 0 ≤ X := CFC.posPart_nonneg _
  have hsa : IsSelfAdjoint (A - B) := hA.isSelfAdjoint.sub hB.isSelfAdjoint
  have hAC : A ≤ C := by
    have e := CFC.posPart_sub_negPart (A - B) hsa
    have hn : 0 ≤ (A - B)⁻ := CFC.negPart_nonneg _
    have : A - B ≤ X := by rw [← e]; exact sub_le_self _ hn
    rw [hCdef]
    calc A = B + (A - B) := by abel
      _ ≤ B + X := add_le_add le_rfl this
  have hBC : B ≤ C := le_add_of_nonneg_right hX0
  have hC0 : 0 ≤ C := add_nonneg hB hX0
  have hp1 : p ∈ Set.Icc (0 : ℝ≥0) 1 := ⟨hp.le, by rw [← hpq]; exact le_add_of_nonneg_right hq.le⟩
  have hq1 : q ∈ Set.Icc (0 : ℝ≥0) 1 := ⟨hq.le, by rw [← hpq]; exact le_add_of_nonneg_left hp.le⟩
  have split : ∀ M : Matrix n n ℂ, 0 ≤ M → M = M ^ p * M ^ q := by
    intro M hM
    rw [← CFC.nnrpow_add hp hq, hpq, CFC.nnrpow_one M hM]
  have hApC : A ^ p ≤ C ^ p := CFC.nnrpow_le_nnrpow hp1 hAC
  have hAqC : A ^ q ≤ C ^ q := CFC.nnrpow_le_nnrpow hq1 hAC
  have hBpC : B ^ p ≤ C ^ p := CFC.nnrpow_le_nnrpow hp1 hBC
  have hBqC : B ^ q ≤ C ^ q := CFC.nnrpow_le_nnrpow hq1 hBC
  -- step 1
  have s1 : (A ^ p * (A ^ q - B ^ q)).trace.re ≤ (A ^ p * (C ^ q - B ^ q)).trace.re :=
    tr_mono CFC.nnrpow_nonneg (sub_le_sub_right hAqC _)
  -- step 2
  have s2 : (A ^ p * (C ^ q - B ^ q)).trace.re ≤ (C ^ p * (C ^ q - B ^ q)).trace.re :=
    tr_mono' hApC (sub_nonneg.mpr hBqC)
  -- step 3
  have s3 : (B ^ p * B ^ q).trace.re ≤ (C ^ p * B ^ q).trace.re :=
    tr_mono' hBpC CFC.nnrpow_nonneg
  have eA := split A hA
  have eB := split B hB
  have eC := split C hC0
  simp only [Matrix.mul_sub, Matrix.trace_sub, Complex.sub_re] at s1 s2
  rw [← eA] at s1
  rw [← eC] at s2
  rw [← eB] at s3
  have eCt : C.trace.re = B.trace.re + X.trace.re := by
    rw [hCdef, Matrix.trace_add, Complex.add_re]
  linarith

/-- every function is continuous on the (finite) real spectrum of a matrix. -/
lemma contOn (M : Matrix n n ℂ) (f : ℝ → ℝ) : ContinuousOn f (spectrum ℝ M) := by
  have : Finite (spectrum ℝ M) := (Matrix.finite_real_spectrum (A := M)).to_subtype
  exact continuousOn_iff_continuous_restrict.mpr continuous_of_discreteTopology

/-- The Neyman-Pearson-type test `1_{(0,∞)}(A - B)`. -/
noncomputable def npTest (A B : Matrix n n ℂ) : Matrix n n ℂ :=
  cfc (fun x : ℝ => if 0 < x then (1 : ℝ) else 0) (A - B)

lemma npTest_nonneg (A B : Matrix n n ℂ) : 0 ≤ npTest A B :=
  cfc_nonneg (fun x _ => by split_ifs <;> norm_num)

lemma npTest_le_one (A B : Matrix n n ℂ) : npTest A B ≤ 1 :=
  cfc_le_one _ _ (fun x _ => by split_ifs <;> norm_num)

lemma npTest_mul {A B : Matrix n n ℂ} (hA : 0 ≤ A) (hB : 0 ≤ B) :
    npTest A B * (A - B) = (A - B)⁺ := by
  have hsa : IsSelfAdjoint (A - B) := hA.isSelfAdjoint.sub hB.isSelfAdjoint
  rw [CFC.posPart_def, cfcₙ_eq_cfc, npTest]
  have e := (cfc_mul (fun x : ℝ => if 0 < x then (1 : ℝ) else 0) (fun x : ℝ => x) (A - B)
    (contOn _ _) (contOn _ _)).symm
  rw [cfc_id' ℝ (A - B)] at e
  rw [e]
  refine cfc_congr (fun x _ => ?_)
  by_cases hx : 0 < x
  · simp [hx, posPart_eq_self.mpr hx.le]
  · simp [hx, posPart_eq_zero.mpr (not_lt.mp hx)]

/-- E2: the test achieves the Chernoff bound. -/
theorem np_bound {A B : Matrix n n ℂ} (hA : 0 ≤ A) (hB : 0 ≤ B) {p q : ℝ≥0} (hp : 0 < p) (hq : 0 < q)
    (hpq : p + q = 1) :
    ((1 - npTest A B) * A).trace.re + (npTest A B * B).trace.re ≤ (A ^ p * B ^ q).trace.re := by
  have h := oz hA hB hp hq hpq
  rw [← npTest_mul hA hB] at h
  simp only [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_sub, Matrix.trace_sub, Complex.sub_re] at h ⊢
  linarith

end OzLib

/-! E6a: achievability half of quantum Stein via Audenaert + E4 (`D > 0` ⟹ type-I error → 0 with
`Tr T σ^{⊗k} ≤ 1`; rescale `σ` by `e^R` for rate `R`). -/
namespace SteinLib
open Matrix KPLib TayLib OzLib
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder NNReal

variable {n : Type} [Fintype n] [DecidableEq n]

lemma pow_eq_cfc {A : Matrix n n ℂ} (hA : 0 ≤ A) {u : ℝ} (hu0 : 0 < u) :
    A ^ (Real.toNNReal u) = cfc (fun x : ℝ => x ^ u) A := by
  rw [CFC.nnrpow_eq_rpow (Real.toNNReal_pos.mpr hu0), Real.coe_toNNReal _ hu0.le, CFC.rpow_eq_cfc_real hA]

theorem stein_ach {ρ σ : Matrix n n ℂ} (hρ : 0 ≤ ρ) (htr : ρ.trace = 1) (hσ : σ.PosDef)
    (hD : 0 < (cfc (id : ℝ → ℝ) ρ * cfc Real.log ρ).trace.re -
      (cfc (id : ℝ → ℝ) ρ * cfc Real.log σ).trace.re)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ k ≥ N₀, ∃ T : Matrix (Fin k → n) (Fin k → n) ℂ, 0 ≤ T ∧ T ≤ 1 ∧
      ((1 - T) * kpow ρ k).trace.re ≤ ε ∧ (T * kpow σ k).trace.re ≤ 1 := by
  set D := (cfc (id : ℝ → ℝ) ρ * cfc Real.log ρ).trace.re -
      (cfc (id : ℝ → ℝ) ρ * cfc Real.log σ).trace.re with hDdef
  have hσnn : 0 ≤ σ := Matrix.nonneg_iff_posSemidef.mpr hσ.posSemidef
  have hρh : ρ.IsHermitian := (Matrix.nonneg_iff_posSemidef.mp hρ).isHermitian
  obtain ⟨K, u₀, hu₀, hbound⟩ := chernoff_taylor hρ htr hσ
  set u : ℝ := min u₀ (min (1 / 2) (D / (2 * (|K| + 1)))) with hu
  have hK1 : 0 < |K| + 1 := by positivity
  have hu0 : 0 < u := lt_min hu₀ (lt_min (by norm_num) (by positivity))
  have hu_le : u ≤ u₀ := min_le_left _ _
  have hu_half : u ≤ 1 / 2 := (min_le_right _ _).trans (min_le_left _ _)
  have hu_D : u ≤ D / (2 * (|K| + 1)) := (min_le_right _ _).trans (min_le_right _ _)
  have h3 := (le_div_iff₀ (by positivity)).mp hu_D
  have huK : u * K ≤ D / 2 := by nlinarith [le_abs_self K, hu0]
  have h1u : 0 < 1 - u := by linarith
  set X := cfc (fun x : ℝ => x ^ (1 - u)) ρ * cfc (fun x : ℝ => x ^ u) σ with hX
  have hg : X.trace.re ≤ 1 - u * D + u ^ 2 * K := hbound u hu0 hu_le
  set p : ℝ≥0 := Real.toNNReal (1 - u) with hp
  set q : ℝ≥0 := Real.toNNReal u with hq
  have hpos : 0 < p := Real.toNNReal_pos.mpr h1u
  have hqos : 0 < q := Real.toNNReal_pos.mpr hu0
  have hpq : p + q = 1 := by rw [hp, hq, ← Real.toNNReal_add h1u.le hu0.le]; simp
  have hXpq : ρ ^ p * σ ^ q = X := by rw [hp, hq, pow_eq_cfc hρ h1u, pow_eq_cfc hσnn hu0]
  have hg0 : 0 ≤ X.trace.re := by rw [← hXpq]; exact tr_nonneg CFC.nnrpow_nonneg CFC.nnrpow_nonneg
  have him : X.trace.im = 0 := by rw [hX, tr_cfc_cfc hρh hσ.isHermitian]; exact Complex.ofReal_im _
  have hXre : X.trace = ((X.trace.re : ℝ) : ℂ) := Complex.ext (by simp) (by simp [him])
  set r := 1 - u * D / 2 with hr
  have hgr : X.trace.re ≤ r := by nlinarith [hg, huK, hu0]
  have hr1 : r < 1 := by have : 0 < u * D := mul_pos hu0 hD; linarith
  have hr0 : 0 ≤ r := hg0.trans hgr
  have ht : Filter.Tendsto (fun k : ℕ => r ^ k) Filter.atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr1
  obtain ⟨N₀, hN⟩ := Filter.eventually_atTop.mp (ht.eventually (gt_mem_nhds (lt_min hε one_pos)))
  refine ⟨N₀, fun k hk => ?_⟩
  have hA : 0 ≤ kpow ρ k := kpow_nonneg hρ k
  have hB : 0 ≤ kpow σ k := kpow_nonneg hσnn k
  refine ⟨npTest (kpow ρ k) (kpow σ k), npTest_nonneg _ _, npTest_le_one _ _, ?_⟩
  have hnp := np_bound hA hB hpos hqos hpq
  rw [trace_kpow_pow hρ hσnn k hpos hqos, hXpq, hXre, ← Complex.ofReal_pow, Complex.ofReal_re] at hnp
  have hpow : X.trace.re ^ k ≤ r ^ k := pow_le_pow_left₀ hg0 hgr k
  have hlt := hN k hk
  have t1 : 0 ≤ ((1 - npTest (kpow ρ k) (kpow σ k)) * kpow ρ k).trace.re :=
    tr_nonneg (sub_nonneg.mpr (npTest_le_one _ _)) hA
  have t2 : 0 ≤ (npTest (kpow ρ k) (kpow σ k) * kpow σ k).trace.re := tr_nonneg (npTest_nonneg _ _) hB
  have hm1 : min ε 1 ≤ ε := min_le_left _ _
  have hm2 : min ε 1 ≤ 1 := min_le_right _ _
  constructor <;> linarith

lemma kpow_smul (r : ℝ) (M : Matrix n n ℂ) (k : ℕ) : kpow (r • M) k = r ^ k • kpow M k := by
  ext f g
  simp [kpow_apply, Complex.real_smul, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ]

lemma log_smul {σ : Matrix n n ℂ} (hσ : σ.PosDef) (R : ℝ) :
    cfc Real.log (Real.exp R • σ) = algebraMap ℝ (Matrix n n ℂ) R + cfc Real.log σ := by
  have hsp : ∀ x ∈ spectrum ℝ σ, 0 < x := by
    intro x hx
    rw [Matrix.IsHermitian.spectrum_real_eq_range_eigenvalues hσ.isHermitian] at hx
    obtain ⟨i, rfl⟩ := hx
    exact hσ.eigenvalues_pos i
  have hfin : Finite ((fun x : ℝ => Real.exp R • x) '' spectrum ℝ σ) :=
    ((Matrix.finite_real_spectrum (A := σ)).image _).to_subtype
  rw [← cfc_comp_smul (Real.exp R) Real.log σ
      (continuousOn_iff_continuous_domRestrict.mpr continuous_of_discreteTopology) hσ.isHermitian.isSelfAdjoint,
    ← cfc_const_add R Real.log σ (contOn σ _) hσ.isHermitian.isSelfAdjoint]
  refine cfc_congr (fun x hx => ?_)
  simp only [smul_eq_mul]
  rw [Real.log_mul (Real.exp_pos R).ne' (hsp x hx).ne', Real.log_exp]

/-- E6b: quantum Stein achievability at any rate `R < D(ρ‖σ)` (nats). -/
theorem stein_rate {ρ σ : Matrix n n ℂ} (hρ : 0 ≤ ρ) (htr : ρ.trace = 1) (hσ : σ.PosDef) {R : ℝ}
    (hR : R < (cfc (id : ℝ → ℝ) ρ * cfc Real.log ρ).trace.re -
      (cfc (id : ℝ → ℝ) ρ * cfc Real.log σ).trace.re)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ k ≥ N₀, ∃ T : Matrix (Fin k → n) (Fin k → n) ℂ, 0 ≤ T ∧ T ≤ 1 ∧
      ((1 - T) * kpow ρ k).trace.re ≤ ε ∧ (T * kpow σ k).trace.re ≤ Real.exp (-(k * R)) := by
  have hρh : ρ.IsHermitian := (Matrix.nonneg_iff_posSemidef.mp hρ).isHermitian
  have hσ' : (Real.exp R • σ).PosDef := hσ.smul (Real.exp_pos R)
  have hid : cfc (id : ℝ → ℝ) ρ = ρ := cfc_id ℝ ρ hρh.isSelfAdjoint
  have hD' : 0 < (cfc (id : ℝ → ℝ) ρ * cfc Real.log ρ).trace.re -
      (cfc (id : ℝ → ℝ) ρ * cfc Real.log (Real.exp R • σ)).trace.re := by
    rw [log_smul hσ R, Matrix.mul_add, Matrix.trace_add, Complex.add_re, Algebra.algebraMap_eq_smul_one,
      Matrix.mul_smul, Matrix.mul_one, Matrix.trace_smul, Complex.smul_re, smul_eq_mul, hid, htr]
    rw [hid] at hR
    simp only [Complex.one_re, mul_one]
    linarith
  obtain ⟨N₀, hN⟩ := stein_ach hρ htr hσ' hD' hε
  refine ⟨N₀, fun k hk => ?_⟩
  obtain ⟨T, hT0, hT1, h1, h2⟩ := hN k hk
  refine ⟨T, hT0, hT1, h1, ?_⟩
  have e1 : (T * kpow (Real.exp R • σ) k).trace.re = Real.exp (k * R) * (T * kpow σ k).trace.re := by
    rw [kpow_smul, Matrix.mul_smul, Matrix.trace_smul, Complex.smul_re, smul_eq_mul, ← Real.exp_nat_mul]
  rw [e1] at h2
  calc (T * kpow σ k).trace.re = Real.exp (-(k * R)) * (Real.exp (k * R) * (T * kpow σ k).trace.re) := by
        rw [← mul_assoc, ← Real.exp_add]; simp
    _ ≤ Real.exp (-(k * R)) * 1 := mul_le_mul_of_nonneg_left h2 (Real.exp_pos _).le
    _ = _ := mul_one _

end SteinLib

namespace SSALib
open Matrix
open scoped ComplexOrder

open scoped Kronecker in
lemma log_kron_diag {m n : Type} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (d : m → ℝ) (e : n → ℝ) (hd : ∀ i, 0 < d i) (he : ∀ j, 0 < e j) :
    cfc Real.log (Matrix.diagonal (fun i => (d i : ℂ)) ⊗ₖ Matrix.diagonal (fun j => (e j : ℂ))) =
      cfc Real.log (Matrix.diagonal (fun i => (d i : ℂ))) ⊗ₖ (1 : Matrix n n ℂ) +
        (1 : Matrix m m ℂ) ⊗ₖ cfc Real.log (Matrix.diagonal (fun j => (e j : ℂ))) := by
  rw [Matrix.diagonal_kronecker_diagonal]
  have h : (fun mn : m × n => (d mn.1 : ℂ) * (e mn.2 : ℂ)) = fun mn => ((d mn.1 * e mn.2 : ℝ) : ℂ) := by
    funext mn; push_cast; ring
  rw [h, cfc_diag, cfc_diag, cfc_diag, ← Matrix.diagonal_one, Matrix.diagonal_kronecker_diagonal,
    ← Matrix.diagonal_one, Matrix.diagonal_kronecker_diagonal, Matrix.diagonal_add]
  congr 1; funext mn
  rw [Real.log_mul (hd mn.1).ne' (he mn.2).ne']
  push_cast; ring


open scoped Kronecker in
/-- `log(σ ⊗ τ) = log σ ⊗ 1 + 1 ⊗ log τ` for positive definite `σ, τ`. -/
theorem log_kron {m n : Type} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    {σ : Matrix m m ℂ} {τ : Matrix n n ℂ} (hσ : σ.PosDef) (hτ : τ.PosDef) :
    cfc Real.log (σ ⊗ₖ τ) = cfc Real.log σ ⊗ₖ (1 : Matrix n n ℂ) + (1 : Matrix m m ℂ) ⊗ₖ cfc Real.log τ := by
  set U : Matrix m m ℂ := (hσ.isHermitian.eigenvectorUnitary : Matrix m m ℂ) with hU
  set W : Matrix n n ℂ := (hτ.isHermitian.eigenvectorUnitary : Matrix n n ℂ) with hW
  set Dσ := Matrix.diagonal (fun i => ((hσ.isHermitian.eigenvalues i : ℝ) : ℂ))
  set Dτ := Matrix.diagonal (fun j => ((hτ.isHermitian.eigenvalues j : ℝ) : ℂ))
  have e1 : σ * U = U * Dσ := eig_intertwine hσ.isHermitian
  have e2 : τ * W = W * Dτ := eig_intertwine hτ.isHermitian
  have l1 := cfc_intertwine σ Dσ hσ.isHermitian (herm_diag _) U e1 Real.log
  have l2 := cfc_intertwine τ Dτ hτ.isHermitian (herm_diag _) W e2 Real.log
  have hX : (σ ⊗ₖ τ).IsHermitian := by
    rw [Matrix.IsHermitian, Matrix.conjTranspose_kronecker, hσ.isHermitian.eq, hτ.isHermitian.eq]
  have hDD : (Dσ ⊗ₖ Dτ).IsHermitian := by
    rw [Matrix.IsHermitian, Matrix.conjTranspose_kronecker, (herm_diag _).eq, (herm_diag _).eq]
  have eX : σ ⊗ₖ τ * (U ⊗ₖ W) = (U ⊗ₖ W) * (Dσ ⊗ₖ Dτ) := by
    rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul, e1, e2]
  have lX := cfc_intertwine _ _ hX hDD (U ⊗ₖ W) eX Real.log
  rw [log_kron_diag _ _ hσ.eigenvalues_pos hτ.eigenvalues_pos] at lX
  have hZ : (U ⊗ₖ W) * (U ⊗ₖ W)ᴴ = 1 := by
    rw [Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul, hU, hW, unit_mul_star',
      unit_mul_star', Matrix.one_kronecker_one]
  have hL : (cfc Real.log σ ⊗ₖ (1 : Matrix n n ℂ) + (1 : Matrix m m ℂ) ⊗ₖ cfc Real.log τ) * (U ⊗ₖ W) =
      (U ⊗ₖ W) * (cfc Real.log Dσ ⊗ₖ (1 : Matrix n n ℂ) + (1 : Matrix m m ℂ) ⊗ₖ cfc Real.log Dτ) := by
    rw [Matrix.add_mul, Matrix.mul_add, ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul,
      ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul, l1, l2]
    simp only [Matrix.one_mul, Matrix.mul_one]
  calc cfc Real.log (σ ⊗ₖ τ) = cfc Real.log (σ ⊗ₖ τ) * ((U ⊗ₖ W) * (U ⊗ₖ W)ᴴ) := by
        rw [hZ, Matrix.mul_one]
    _ = (cfc Real.log σ ⊗ₖ (1 : Matrix n n ℂ) + (1 : Matrix m m ℂ) ⊗ₖ cfc Real.log τ) *
          ((U ⊗ₖ W) * (U ⊗ₖ W)ᴴ) := by
        rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, lX, hL]
    _ = _ := by rw [hZ, Matrix.mul_one]


end SSALib

/-! C4 step E5: smoothing of the product of marginals and Stein's lemma at rate `log 2 * I(A;B)`
against the TRUE product of marginals `ρ_A ⊗ ρ_B` (possibly singular). -/

namespace SmoothLib
open Matrix KPLib TayLib OzLib SteinLib SSALib
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder Kronecker

section G
variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- mixed Kronecker product `M 0 ⊗ ... ⊗ M (k-1)`. -/
noncomputable def gpow {k : ℕ} (M : Fin k → Matrix ι ι ℂ) : Matrix (Fin k → ι) (Fin k → ι) ℂ :=
  Matrix.of fun f g => ∏ i, M i (f i) (g i)

lemma gpow_mul {k : ℕ} (M N : Fin k → Matrix ι ι ℂ) :
    gpow M * gpow N = gpow (fun i => M i * N i) := by
  ext f g
  simp only [gpow, Matrix.mul_apply, Matrix.of_apply]
  rw [Finset.prod_univ_sum, Fintype.piFinset_univ]
  refine Finset.sum_congr rfl (fun h _ => ?_)
  rw [Finset.prod_mul_distrib]

lemma gpow_conjTranspose {k : ℕ} (M : Fin k → Matrix ι ι ℂ) :
    (gpow M)ᴴ = gpow (fun i => (M i)ᴴ) := by
  ext f g
  simp only [gpow, Matrix.conjTranspose_apply, Matrix.of_apply]
  exact map_prod (starRingEnd ℂ) _ _

lemma gpow_nonneg {k : ℕ} {M : Fin k → Matrix ι ι ℂ} (hM : ∀ i, 0 ≤ M i) : 0 ≤ gpow M := by
  have e : gpow M = star (gpow (fun i => CFC.sqrt (M i))) * gpow (fun i => CFC.sqrt (M i)) := by
    rw [Matrix.star_eq_conjTranspose, gpow_conjTranspose, gpow_mul]
    congr 1; funext i
    rw [← Matrix.star_eq_conjTranspose, (CFC.sqrt_nonneg (M i)).isSelfAdjoint.star_eq,
      CFC.sqrt_mul_sqrt_self (M i) (hM i)]
  rw [e]; exact star_mul_self_nonneg _

lemma kpow_add (A C : Matrix ι ι ℂ) (k : ℕ) :
    kpow (A + C) k = ∑ t ∈ (Finset.univ : Finset (Fin k)).powerset,
      gpow (fun i => if i ∈ t then A else C) := by
  ext f g
  rw [Matrix.sum_apply, kpow_apply]
  simp only [Matrix.add_apply, gpow, Matrix.of_apply]
  rw [Finset.prod_add]
  refine Finset.sum_congr rfl (fun t _ => ?_)
  have h : ∀ i, (if i ∈ t then A else C) (f i) (g i) = if i ∈ t then A (f i) (g i) else C (f i) (g i) :=
    fun i => by split_ifs <;> rfl
  simp only [h]
  rw [Finset.prod_ite]
  congr 2
  · ext x; simp
  · ext x; simp

lemma kpow_mono {A B : Matrix ι ι ℂ} (hA : 0 ≤ A) (hAB : A ≤ B) (k : ℕ) : kpow A k ≤ kpow B k := by
  obtain ⟨C, hC, rfl⟩ : ∃ C, 0 ≤ C ∧ B = A + C := ⟨B - A, sub_nonneg.mpr hAB, by abel⟩
  rw [kpow_add, ← Finset.add_sum_erase _ _ (Finset.mem_powerset_self Finset.univ)]
  have h1 : gpow (fun i : Fin k => if i ∈ (Finset.univ : Finset (Fin k)) then A else C) = kpow A k := by
    ext f g; simp [kpow, gpow]
  rw [h1]
  refine le_add_of_nonneg_right (Finset.sum_nonneg (fun t _ => gpow_nonneg (fun i => ?_)))
  split_ifs
  · exact hA
  · exact hC

end G

/-- every function is continuous on a finite set of reals. -/
lemma fin_cont (s : Set ℝ) (hs : s.Finite) (f : ℝ → ℝ) : ContinuousOn f s := by
  have : Finite s := hs.to_subtype
  exact continuousOn_iff_continuous_restrict.mpr continuous_of_discreteTopology

section S
variable {α : Type} [Fintype α] [DecidableEq α]

lemma tr_cfc_mono {X : Matrix α α ℂ} (hX : X.IsHermitian) {f g : ℝ → ℝ}
    (hfg : ∀ x ∈ spectrum ℝ X, f x ≤ g x) : (cfc f X).trace.re ≤ (cfc g X).trace.re := by
  have h0 : 0 ≤ cfc g X - cfc f X := by
    rw [← cfc_sub g f X (contOn X g) (contOn X f)]
    exact cfc_nonneg (fun x hx => sub_nonneg.mpr (hfg x hx))
  have h1 := (Matrix.nonneg_iff_posSemidef.mp h0).trace_nonneg
  have h2 := (Complex.le_def.mp h1).1
  rw [Matrix.trace_sub, Complex.sub_re] at h2
  simp only [Complex.zero_re] at h2
  linarith

lemma mix_eq {X : Matrix α α ℂ} (hX : X.IsHermitian) (t c : ℝ) :
    cfc (fun x : ℝ => (1 - t) * x + c) X = (1 - t) • X + c • (1 : Matrix α α ℂ) := by
  have h := cfc_add (a := X) (fun x : ℝ => (1 - t) * x) (fun _ => c) (contOn X _) (contOn X _)
  rw [h, cfc_const_mul (1 - t) (fun x : ℝ => x) X (contOn X _), cfc_id' ℝ X, cfc_const c X hX.isSelfAdjoint,
    Algebra.algebraMap_eq_smul_one]

lemma mix_posDef {X : Matrix α α ℂ} (hX : 0 ≤ X) {t c : ℝ} (ht : t < 1) (hc : 0 < c) :
    (cfc (fun x : ℝ => (1 - t) * x + c) X).PosDef := by
  have hP := Matrix.nonneg_iff_posSemidef.mp hX
  rw [mix_eq hP.isHermitian]
  exact Matrix.PosDef.posSemidef_add (hP.smul (by linarith : (0 : ℝ) ≤ 1 - t)) (Matrix.PosDef.one.smul hc)

lemma mix_ge {X : Matrix α α ℂ} (hX : 0 ≤ X) {t c : ℝ} (ht : t < 1) (hc : 0 < c) :
    X ≤ (1 - t)⁻¹ • cfc (fun x : ℝ => (1 - t) * x + c) X := by
  have hP := Matrix.nonneg_iff_posSemidef.mp hX
  rw [mix_eq hP.isHermitian, smul_add, smul_smul, inv_mul_cancel₀ (by linarith : (1 - t) ≠ 0), one_smul,
    smul_smul]
  refine le_add_of_nonneg_right (smul_nonneg (by positivity) ?_)
  exact Matrix.nonneg_iff_posSemidef.mpr Matrix.PosSemidef.one

lemma pt_bound {x t c : ℝ} (hx : 0 ≤ x) (ht0 : 0 ≤ t) (ht1 : t < 1) (hc : 0 < c) :
    x * Real.log ((1 - t) * x + c) ≤ x * Real.log x + c := by
  rcases hx.eq_or_lt with h | h
  · subst h; simp; linarith
  · have hpos : 0 < ((1 - t) * x + c) / x := by
      have : 0 < (1 - t) * x + c := by nlinarith
      positivity
    have h1 := Real.log_le_sub_one_of_pos hpos
    rw [Real.log_div (by nlinarith) h.ne'] at h1
    have h2 : ((1 - t) * x + c) / x - 1 ≤ c / x := by
      rw [div_sub_one h.ne', div_le_div_iff_of_pos_right h]; nlinarith
    have h3 : Real.log ((1 - t) * x + c) ≤ Real.log x + c / x := by linarith
    calc x * Real.log ((1 - t) * x + c) ≤ x * (Real.log x + c / x) := mul_le_mul_of_nonneg_left h3 hx
      _ = x * Real.log x + c := by field_simp

/-- `Tr[X log X_t] ≤ Tr[X log X] + t` for the smoothed `X_t = (1-t) X + (t/d) 1`. -/
lemma tr_log_mix [Nonempty α] {X : Matrix α α ℂ} (hX : 0 ≤ X) {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    (X * cfc Real.log (cfc (fun x : ℝ => (1 - t) * x + t / Fintype.card α) X)).trace.re ≤
      (cfc (fun x : ℝ => x * Real.log x) X).trace.re + t := by
  have hP := Matrix.nonneg_iff_posSemidef.mp hX
  have hd : (0 : ℝ) < Fintype.card α := by exact_mod_cast Fintype.card_pos
  have hc : 0 < t / Fintype.card α := div_pos ht0 hd
  have hfin := (Matrix.finite_real_spectrum (A := X))
  have e1 := cfc_comp' Real.log (fun x : ℝ => (1 - t) * x + t / Fintype.card α) X
    (fin_cont _ (hfin.image _) _) (contOn X _) hP.isHermitian.isSelfAdjoint
  rw [← e1]
  have e2 := cfc_mul (fun x : ℝ => x) (fun x => Real.log ((1 - t) * x + t / Fintype.card α)) X
    (contOn X _) (contOn X _)
  rw [cfc_id' ℝ X] at e2
  rw [← e2]
  have e3 := cfc_add (a := X) (fun x : ℝ => x * Real.log x) (fun _ => t / Fintype.card α) (contOn X _) (contOn X _)
  have hle := tr_cfc_mono hP.isHermitian (f := fun x => x * Real.log ((1 - t) * x + t / Fintype.card α))
    (g := fun x => x * Real.log x + t / Fintype.card α)
    (fun x hx => pt_bound (spectrum_nonneg_of_nonneg hX hx) ht0.le ht1 hc)
  refine hle.trans (le_of_eq ?_)
  rw [e3, cfc_const _ X hP.isHermitian.isSelfAdjoint, Algebra.algebraMap_eq_smul_one, Matrix.trace_add,
    Complex.add_re, Matrix.trace_smul, Matrix.trace_one, Complex.smul_re]
  simp only [Complex.natCast_re, smul_eq_mul]
  field_simp

lemma vn_log (X : Matrix α α ℂ) (hX : X.IsHermitian) :
    Real.log 2 * QAlgorithms.vnEntropy X = -(cfc (fun x : ℝ => x * Real.log x) X).trace.re := by
  have h2 : Real.log 2 ≠ 0 := (Real.log_pos one_lt_two).ne'
  have e : (fun x : ℝ => x * Real.log x) = fun x => Real.log 2 * (x * Real.logb 2 x) := by
    funext x; rw [Real.logb]; field_simp
  rw [e, cfc_const_mul (Real.log 2) (fun x : ℝ => x * Real.logb 2 x) X (contOn X _),
    Matrix.trace_smul, Complex.smul_re, smul_eq_mul, QAlgorithms.vnEntropy]
  ring

end S

section P
variable {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]

lemma tr_kron_one (ρ : Matrix (α × β) (α × β) ℂ) (L : Matrix α α ℂ) :
    (ρ * (L ⊗ₖ (1 : Matrix β β ℂ))).trace = (QAlgorithms.traceRight ρ * L).trace := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.kroneckerMap_apply, Matrix.one_apply,
    QAlgorithms.traceRight, Matrix.of_apply, Fintype.sum_prod_type, Finset.sum_mul]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  refine Finset.sum_comm.trans ?_
  refine Finset.sum_congr rfl (fun a' _ => Finset.sum_congr rfl (fun b _ => ?_))
  simp [mul_ite]

lemma tr_one_kron (ρ : Matrix (α × β) (α × β) ℂ) (L : Matrix β β ℂ) :
    (ρ * ((1 : Matrix α α ℂ) ⊗ₖ L)).trace = (QAlgorithms.traceLeft ρ * L).trace := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.kroneckerMap_apply, Matrix.one_apply,
    QAlgorithms.traceLeft, Matrix.of_apply, Fintype.sum_prod_type, Finset.sum_mul]
  refine Finset.sum_comm.trans ?_
  refine Finset.sum_congr rfl (fun b _ => ?_)
  calc _ = ∑ a, ∑ b', ρ (a, b) (a, b') * L b' b := Finset.sum_congr rfl (fun a _ => by
          rw [Finset.sum_eq_single a (fun a' _ h => by simp [h]) (by simp)]; simp)
    _ = _ := Finset.sum_comm

lemma trR_nonneg {ρ : Matrix (α × β) (α × β) ℂ} (hρ : 0 ≤ ρ) : 0 ≤ QAlgorithms.traceRight ρ := by
  let V : β → Matrix α (α × β) ℂ := fun h => Matrix.of fun a p => if p = (a, h) then 1 else 0
  have e : QAlgorithms.traceRight ρ = ∑ h, V h * ρ * (V h)ᴴ := by
    ext a a'
    simp [V, QAlgorithms.traceRight, Matrix.mul_apply, Matrix.sum_apply, Fintype.sum_prod_type]
  rw [e]
  exact Finset.sum_nonneg (fun h _ => Matrix.nonneg_iff_posSemidef.mpr
    ((Matrix.nonneg_iff_posSemidef.mp hρ).mul_mul_conjTranspose_same _))

lemma trL_nonneg {ρ : Matrix (α × β) (α × β) ℂ} (hρ : 0 ≤ ρ) : 0 ≤ QAlgorithms.traceLeft ρ := by
  let V : α → Matrix β (α × β) ℂ := fun h => Matrix.of fun b p => if p = (h, b) then 1 else 0
  have e : QAlgorithms.traceLeft ρ = ∑ h, V h * ρ * (V h)ᴴ := by
    ext b b'
    simp [V, QAlgorithms.traceLeft, Matrix.mul_apply, Matrix.sum_apply, Fintype.sum_prod_type]
  rw [e]
  exact Finset.sum_nonneg (fun h _ => Matrix.nonneg_iff_posSemidef.mpr
    ((Matrix.nonneg_iff_posSemidef.mp hρ).mul_mul_conjTranspose_same _))

lemma kron_nonneg {X : Matrix α α ℂ} {Y : Matrix β β ℂ} (hX : 0 ≤ X) (hY : 0 ≤ Y) : 0 ≤ X ⊗ₖ Y :=
  Matrix.nonneg_iff_posSemidef.mpr ((Matrix.nonneg_iff_posSemidef.mp hX).kronecker
    (Matrix.nonneg_iff_posSemidef.mp hY))

lemma kron_mono {X X' : Matrix α α ℂ} {Y Y' : Matrix β β ℂ} (hX : 0 ≤ X) (hXX : X ≤ X')
    (hY : 0 ≤ Y) (hYY : Y ≤ Y') : X ⊗ₖ Y ≤ X' ⊗ₖ Y' := by
  have hY' : 0 ≤ Y' := hY.trans hYY
  have e1 : X ⊗ₖ Y' - X ⊗ₖ Y = X ⊗ₖ (Y' - Y) := by ext; simp [mul_sub]
  have e2 : X' ⊗ₖ Y' - X ⊗ₖ Y' = (X' - X) ⊗ₖ Y' := by ext; simp [sub_mul]
  have h1 : X ⊗ₖ Y ≤ X ⊗ₖ Y' := sub_nonneg.mp (by rw [e1]; exact kron_nonneg hX (sub_nonneg.mpr hYY))
  have h2 : X ⊗ₖ Y' ≤ X' ⊗ₖ Y' := sub_nonneg.mp (by rw [e2]; exact kron_nonneg (sub_nonneg.mpr hXX) hY')
  exact h1.trans h2

end P

end SmoothLib

namespace SmoothLib
open Matrix KPLib TayLib OzLib SteinLib SSALib
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder Kronecker

/-- Quantum Stein achievability against the true product of marginals at any rate below `log 2 * I(A;B)`. -/
theorem stein_mi {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    [Nonempty α] [Nonempty β]
    {ρ : Matrix (α × β) (α × β) ℂ} (hρ : 0 ≤ ρ) (htr : ρ.trace = 1) {R : ℝ}
    (hR : R < Real.log 2 * DattaDiscord.mutualInfo ρ) {ε : ℝ} (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ k ≥ N₀, ∃ T : Matrix (Fin k → α × β) (Fin k → α × β) ℂ, 0 ≤ T ∧ T ≤ 1 ∧
      ((1 - T) * kpow ρ k).trace.re ≤ ε ∧
      (T * kpow (QAlgorithms.traceRight ρ ⊗ₖ QAlgorithms.traceLeft ρ) k).trace.re ≤
        Real.exp (-(k * R)) := by
  have hA : 0 ≤ QAlgorithms.traceRight ρ := trR_nonneg hρ
  have hB : 0 ≤ QAlgorithms.traceLeft ρ := trL_nonneg hρ
  have hAh := (Matrix.nonneg_iff_posSemidef.mp hA).isHermitian
  have hBh := (Matrix.nonneg_iff_posSemidef.mp hB).isHermitian
  have hρh : ρ.IsHermitian := (Matrix.nonneg_iff_posSemidef.mp hρ).isHermitian
  obtain ⟨g, hg0, hg⟩ : ∃ g : ℝ, 0 < g ∧ R + g = Real.log 2 * DattaDiscord.mutualInfo ρ :=
    ⟨Real.log 2 * DattaDiscord.mutualInfo ρ - R, by linarith, by ring⟩
  obtain ⟨t, ht0, ht8, ht2⟩ : ∃ t : ℝ, 0 < t ∧ t ≤ g / 8 ∧ t ≤ 1 / 2 :=
    ⟨min (g / 8) (1 / 2), lt_min (by linarith) (by norm_num), min_le_left _ _, min_le_right _ _⟩
  have ht1 : t < 1 := by linarith
  have hdA : (0 : ℝ) < Fintype.card α := by exact_mod_cast Fintype.card_pos
  have hdB : (0 : ℝ) < Fintype.card β := by exact_mod_cast Fintype.card_pos
  have hcA : 0 < t / Fintype.card α := div_pos ht0 hdA
  have hcB : 0 < t / Fintype.card β := div_pos ht0 hdB
  have pA := mix_posDef hA ht1 hcA
  have pB := mix_posDef hB ht1 hcB
  have pσ := pA.kronecker pB
  obtain ⟨N₀, hN⟩ := stein_rate hρ htr pσ (R := R + g / 2) (by
    have hid : cfc (id : ℝ → ℝ) ρ = ρ := cfc_id ℝ ρ hρh.isSelfAdjoint
    rw [hid, log_kron pA pB, Matrix.mul_add, Matrix.trace_add, Complex.add_re, tr_kron_one, tr_one_kron]
    have e0 : ρ * cfc Real.log ρ = cfc (fun x : ℝ => x * Real.log x) ρ := by
      have := cfc_mul (a := ρ) (fun x : ℝ => x) Real.log (contOn ρ _) (contOn ρ _)
      rw [cfc_id' ℝ ρ] at this; exact this.symm
    rw [e0]
    have a1 := tr_log_mix hA ht0 ht1
    have a2 := tr_log_mix hB ht0 ht1
    have v0 := vn_log ρ hρh
    have v1 := vn_log _ hAh
    have v2 := vn_log _ hBh
    have hI : DattaDiscord.mutualInfo ρ = QAlgorithms.vnEntropy (QAlgorithms.traceRight ρ) +
        QAlgorithms.vnEntropy (QAlgorithms.traceLeft ρ) - QAlgorithms.vnEntropy ρ := rfl
    rw [hI, mul_sub, mul_add] at hg
    linarith) hε
  refine ⟨N₀, fun k hk => ?_⟩
  obtain ⟨T, hT0, hT1, h1, h2⟩ := hN k hk
  refine ⟨T, hT0, hT1, h1, ?_⟩
  have hσle := kron_mono hA (mix_ge hA ht1 hcA) hB (mix_ge hB ht1 hcB)
  rw [Matrix.smul_kronecker, Matrix.kronecker_smul, smul_smul] at hσle
  have hk2 := OzLib.tr_mono hT0 (kpow_mono (kron_nonneg hA hB) hσle k)
  rw [kpow_smul, Matrix.mul_smul, Matrix.trace_smul, Complex.smul_re, smul_eq_mul] at hk2
  have i1 : (1 - t)⁻¹ ≤ 1 + 2 * t := by
    rw [inv_eq_one_div, div_le_iff₀ (by linarith)]; nlinarith
  have i2 : 1 + 2 * t ≤ Real.exp (g / 4) := by
    have := Real.add_one_le_exp (2 * t)
    have := Real.exp_le_exp.mpr (show 2 * t ≤ g / 4 by linarith)
    linarith
  have h0 : 0 ≤ (1 - t)⁻¹ := inv_nonneg.mpr (by linarith)
  have i3 : (1 - t)⁻¹ * (1 - t)⁻¹ ≤ Real.exp (g / 2) := by
    calc _ ≤ Real.exp (g / 4) * Real.exp (g / 4) :=
          mul_le_mul (i1.trans i2) (i1.trans i2) h0 (Real.exp_pos _).le
      _ = Real.exp (g / 2) := by rw [← Real.exp_add]; congr 1; ring
  have hc : ((1 - t)⁻¹ * (1 - t)⁻¹) ^ k ≤ Real.exp (k * (g / 2)) := by
    calc _ ≤ Real.exp (g / 2) ^ k := pow_le_pow_left₀ (mul_nonneg h0 h0) i3 k
      _ = _ := (Real.exp_nat_mul _ _).symm
  have hX0 := OzLib.tr_nonneg hT0 (kpow_nonneg pσ.posSemidef.nonneg k)
  refine hk2.trans ((mul_le_mul hc h2 hX0 (Real.exp_pos _).le).trans (le_of_eq ?_))
  rw [← Real.exp_add]; congr 1; ring

end SmoothLib




/-! C4 step E1: Hayashi-Nagaoka operator inequality (IEEE TIT 49 (2003), Lemma 2), c = 1, invertible case.
`0 ≤ S ≤ 1`, `0 ≤ T`, `S + T` invertible, `X = (S+T)^{-1/2}`:  `1 - X S X ≤ 2 (1 - S) + 4 T`. -/

namespace HNLib

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- `G ^ (-1/2)` through the real functional calculus. -/
noncomputable def isq (G : A) : A := cfc (fun x : ℝ => (Real.sqrt x)⁻¹) G

lemma isq_sa (G : A) : IsSelfAdjoint (isq G) := cfc_predicate _ _

lemma spec_pos {G : A} (hG0 : 0 ≤ G) (hG : IsUnit G) : ∀ x ∈ spectrum ℝ G, 0 < x := by
  intro x hx
  have h1 : 0 ≤ x := spectrum_nonneg_of_nonneg hG0 hx
  rcases h1.lt_or_eq with h | h
  · exact h
  · subst h
    exact absurd hx ((spectrum.zero_notMem_iff ℝ).mpr hG)

lemma isq_cont {G : A} (hG0 : 0 ≤ G) (hG : IsUnit G) :
    ContinuousOn (fun x : ℝ => (Real.sqrt x)⁻¹) (spectrum ℝ G) :=
  ContinuousOn.inv₀ Real.continuous_sqrt.continuousOn
    (fun x hx => (Real.sqrt_pos.mpr (spec_pos hG0 hG x hx)).ne')

lemma sqrt_eq (G : A) (hG0 : 0 ≤ G) : CFC.sqrt G = cfc Real.sqrt G := by
  rw [CFC.sqrt_eq_real_sqrt G hG0, cfcₙ_eq_cfc]

lemma isq_mul {G : A} (hG0 : 0 ≤ G) (hG : IsUnit G) : isq G * G = CFC.sqrt G := by
  have hsa : IsSelfAdjoint G := IsSelfAdjoint.of_nonneg hG0
  rw [sqrt_eq G hG0, isq]
  have e := (cfc_mul (fun x : ℝ => (Real.sqrt x)⁻¹) (fun x : ℝ => x) G (isq_cont hG0 hG)).symm
  rw [cfc_id' ℝ G] at e
  rw [e]
  refine cfc_congr (fun x hx => ?_)
  have hx0 := spec_pos hG0 hG x hx
  have hs : Real.sqrt x ≠ 0 := (Real.sqrt_pos.mpr hx0).ne'
  rw [inv_mul_eq_div, div_eq_iff hs]
  exact (Real.mul_self_sqrt hx0.le).symm

lemma mul_isq {G : A} (hG0 : 0 ≤ G) (hG : IsUnit G) : G * isq G = CFC.sqrt G := by
  have hsa : IsSelfAdjoint G := IsSelfAdjoint.of_nonneg hG0
  rw [sqrt_eq G hG0, isq]
  have e := (cfc_mul (fun x : ℝ => x) (fun x : ℝ => (Real.sqrt x)⁻¹) G
    continuous_id.continuousOn (isq_cont hG0 hG)).symm
  rw [cfc_id' ℝ G] at e
  rw [e]
  refine cfc_congr (fun x hx => ?_)
  have hx0 := spec_pos hG0 hG x hx
  have hs : Real.sqrt x ≠ 0 := (Real.sqrt_pos.mpr hx0).ne'
  rw [← div_eq_mul_inv, div_eq_iff hs]
  exact (Real.mul_self_sqrt hx0.le).symm

lemma isq_mul_isq {G : A} (hG0 : 0 ≤ G) (hG : IsUnit G) : isq G * G * isq G = 1 := by
  have hsa : IsSelfAdjoint G := IsSelfAdjoint.of_nonneg hG0
  rw [isq_mul hG0 hG, sqrt_eq G hG0, isq, ← cfc_mul Real.sqrt (fun x : ℝ => (Real.sqrt x)⁻¹) G
    Real.continuous_sqrt.continuousOn (isq_cont hG0 hG), ← cfc_one ℝ G]
  refine cfc_congr (fun x hx => ?_)
  have hx0 := spec_pos hG0 hG x hx
  have hs : Real.sqrt x ≠ 0 := (Real.sqrt_pos.mpr hx0).ne'
  simp [hs]

lemma le_sqrt_of_le_one {S : A} (hS0 : 0 ≤ S) (hS1 : S ≤ 1) : S ≤ CFC.sqrt S := by
  have hsa : IsSelfAdjoint S := IsSelfAdjoint.of_nonneg hS0
  have hspec : ∀ x ∈ spectrum ℝ S, x ≤ 1 :=
    (le_algebraMap_iff_spectrum_le (r := (1 : ℝ)) (a := S)).mp (by simpa using hS1)
  rw [sqrt_eq S hS0]
  conv_lhs => rw [← cfc_id' ℝ S]
  refine cfc_mono (fun x hx => ?_)
  have h0 : 0 ≤ x := spectrum_nonneg_of_nonneg hS0 hx
  have h1 := hspec x hx
  rw [Real.le_sqrt h0 h0]
  nlinarith

/-- Hayashi-Nagaoka operator inequality (c = 1). -/
theorem hn {S T : A} (hS0 : 0 ≤ S) (hS1 : S ≤ 1) (hT : 0 ≤ T) (hG : IsUnit (S + T)) :
    1 - isq (S + T) * S * isq (S + T) ≤ 2 * (1 - S) + 4 * T := by
  have hG0 : 0 ≤ S + T := add_nonneg hS0 hT
  set X := isq (S + T) with hX
  set Q := CFC.sqrt (S + T) with hQ
  have hXsa : IsSelfAdjoint X := isq_sa _
  have h1 : X * (S + T) * X = 1 := isq_mul_isq hG0 hG
  have h2 : X * (S + T) = Q := isq_mul hG0 hG
  have h3 : (S + T) * X = Q := mul_isq hG0 hG
  have hQS : S ≤ Q :=
    (le_sqrt_of_le_one hS0 hS1).trans (CFC.sqrt_le_sqrt S (S + T) (le_add_of_nonneg_right hT))
  have hsub1 : IsSelfAdjoint (X - 1) := hXsa.sub (IsSelfAdjoint.one A)
  have hsub2 : IsSelfAdjoint (X - 2) := hXsa.sub (by simpa using (IsSelfAdjoint.one A).add (IsSelfAdjoint.one A))
  have p1 : 0 ≤ (X - 1) * S * (X - 1) := by
    simpa [hsub1.star_eq] using star_left_conjugate_nonneg hS0 (X - 1)
  have p2 : 0 ≤ (X - 2) * T * (X - 2) := by
    simpa [hsub2.star_eq] using star_left_conjugate_nonneg hT (X - 2)
  have p3 : 0 ≤ Q - S := sub_nonneg.mpr hQS
  have key : 2 * (1 - S) + 4 * T - (1 - X * S * X)
      = 4 * (Q - S) + 2 * ((X - 1) * S * (X - 1)) + (X - 2) * T * (X - 2) := by
    have e : 2 * (1 - S) + 4 * T - (1 - X * S * X)
        - (4 * (Q - S) + 2 * ((X - 1) * S * (X - 1)) + (X - 2) * T * (X - 2))
        = -(X * (S + T) * X - 1) + 2 * (X * (S + T) - Q) + 2 * ((S + T) * X - Q) := by
      noncomm_ring
    rw [h1, h2, h3] at e
    simpa [sub_eq_zero] using e
  rw [← sub_nonneg, key]
  have h4 : (0 : A) ≤ 4 * (Q - S) := by
    have : (4 : A) * (Q - S) = (Q - S) + (Q - S) + (Q - S) + (Q - S) := by noncomm_ring
    rw [this]; exact add_nonneg (add_nonneg (add_nonneg p3 p3) p3) p3
  have h5 : (0 : A) ≤ 2 * ((X - 1) * S * (X - 1)) := by
    rw [two_mul]; exact add_nonneg p1 p1
  exact add_nonneg (add_nonneg h4 h5) p2

end HNLib

/-! C4 step E7a: the one-shot position-based decoder (regularised square-root measurement). -/

namespace PBLib
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder

variable {H : Type} [Fintype H] [DecidableEq H]

lemma tr_nonneg {P Q : Matrix H H ℂ} (hP : 0 ≤ P) (hQ : 0 ≤ Q) : 0 ≤ (P * Q).trace.re := by
  have hR : IsSelfAdjoint (CFC.sqrt P) := (CFC.sqrt_nonneg P).isSelfAdjoint
  have e : P * Q = CFC.sqrt P * (CFC.sqrt P * Q) := by
    rw [← Matrix.mul_assoc, CFC.sqrt_mul_sqrt_self P hP]
  rw [e, Matrix.trace_mul_comm, Matrix.mul_assoc]
  have h0 : 0 ≤ CFC.sqrt P * Q * CFC.sqrt P := by
    simpa [hR.star_eq] using star_left_conjugate_nonneg hQ (CFC.sqrt P)
  have h1 := (Matrix.nonneg_iff_posSemidef.mp h0).trace_nonneg
  rw [Matrix.mul_assoc] at h1
  exact (Complex.nonneg_iff.mp h1).1

lemma tr_mono' {P₁ P₂ Q : Matrix H H ℂ} (h : P₁ ≤ P₂) (hQ : 0 ≤ Q) :
    (P₁ * Q).trace.re ≤ (P₂ * Q).trace.re := by
  rw [Matrix.trace_mul_comm P₁, Matrix.trace_mul_comm P₂]
  have := tr_nonneg hQ (sub_nonneg.mpr h)
  rw [Matrix.mul_sub, Matrix.trace_sub, Complex.sub_re] at this
  linarith

/-- One-shot position-based decoder: from tests `0 ≤ T j ≤ 1` build a POVM `Λ` whose error on any
state `ω ≥ 0` is at most `2 Tr[(1-T m) ω] + 4 Σ_{j ≠ m} Tr[T j ω] + 4 η Tr ω` (Hayashi-Nagaoka). -/
theorem pb_decoder {K : ℕ} (hK : 0 < K) (T : Fin K → Matrix H H ℂ) (hT0 : ∀ j, 0 ≤ T j)
    (hT1 : ∀ j, T j ≤ 1) {η : ℝ} (hη : 0 < η) :
    ∃ Λ : Fin K → Matrix H H ℂ, QAlgorithms.IsPOVM Λ ∧ ∀ (m : Fin K) (ω : Matrix H H ℂ), 0 ≤ ω →
      ((1 - Λ m) * ω).trace.re ≤ 2 * ((1 - T m) * ω).trace.re +
        4 * ∑ j ∈ Finset.univ.erase m, (T j * ω).trace.re + 4 * η * ω.trace.re := by
  set G : Matrix H H ℂ := ∑ j, T j + η • (1 : Matrix H H ℂ) with hGdef
  have hS0 : 0 ≤ ∑ j, T j := Finset.sum_nonneg (fun j _ => hT0 j)
  have hI0 : 0 ≤ η • (1 : Matrix H H ℂ) :=
    smul_nonneg hη.le (Matrix.nonneg_iff_posSemidef.mpr Matrix.PosSemidef.one)
  have hG0 : 0 ≤ G := add_nonneg hS0 hI0
  have hGpd : G.PosDef := Matrix.PosDef.posSemidef_add (Matrix.nonneg_iff_posSemidef.mp hS0)
    (Matrix.PosDef.one.smul hη)
  have hGu : IsUnit G := hGpd.isUnit
  set X := HNLib.isq G with hXdef
  have hXsa : IsSelfAdjoint X := HNLib.isq_sa G
  have hXGX : X * G * X = 1 := HNLib.isq_mul_isq hG0 hGu
  have hconj : ∀ M : Matrix H H ℂ, 0 ≤ M → 0 ≤ X * M * X := fun M hM => by
    simpa [hXsa.star_eq] using star_left_conjugate_nonneg hM X
  set Rem : Matrix H H ℂ := η • (X * X) with hRem
  have hRem0 : 0 ≤ Rem := by
    have := hconj 1 (Matrix.nonneg_iff_posSemidef.mpr Matrix.PosSemidef.one)
    rw [Matrix.mul_one] at this
    exact smul_nonneg hη.le this
  have hsumX : ∑ j, X * T j * X + Rem = 1 := by
    rw [← hXGX, hGdef, Matrix.mul_add, Matrix.add_mul, Matrix.mul_sum, Matrix.sum_mul, hRem,
      Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one]
  set j0 : Fin K := ⟨0, hK⟩
  refine ⟨fun j => X * T j * X + if j = j0 then Rem else 0, ⟨fun j => ?_, ?_⟩, fun m ω hω => ?_⟩
  · refine Matrix.nonneg_iff_posSemidef.mp (add_nonneg (hconj _ (hT0 j)) ?_)
    split_ifs
    · exact hRem0
    · exact le_rfl
  · rw [Finset.sum_add_distrib, Finset.sum_ite_eq' Finset.univ j0, if_pos (Finset.mem_univ _), hsumX]
  · have hE : 0 ≤ (if m = j0 then Rem else 0) := by
      split_ifs
      · exact hRem0
      · exact le_rfl
    have step1 : 1 - (X * T m * X + if m = j0 then Rem else 0) ≤ 1 - X * T m * X :=
      sub_le_sub_left (le_add_of_nonneg_right hE) _
    set Tt : Matrix H H ℂ := ∑ j ∈ Finset.univ.erase m, T j + η • (1 : Matrix H H ℂ) with hTt
    have hTt0 : 0 ≤ Tt := add_nonneg (Finset.sum_nonneg (fun j _ => hT0 j)) hI0
    have hGsplit : T m + Tt = G := by
      rw [hTt, hGdef, ← add_assoc, Finset.add_sum_erase _ _ (Finset.mem_univ m)]
    have hn := HNLib.hn (hT0 m) (hT1 m) hTt0 (by rw [hGsplit]; exact hGu)
    rw [hGsplit] at hn
    have e2 : (2 : Matrix H H ℂ) * (1 - T m) = (2 : ℝ) • (1 - T m) := by rw [two_mul, two_smul]
    have e4 : (4 : Matrix H H ℂ) * Tt = (4 : ℝ) • Tt := by
      rw [show (4 : Matrix H H ℂ) = 2 + 2 by norm_num, Matrix.add_mul, two_mul,
        show (4 : ℝ) = 2 + 2 by norm_num, add_smul, two_smul]
    rw [e2, e4] at hn
    have h1 := tr_mono' (step1.trans hn) hω
    refine h1.trans (le_of_eq ?_)
    rw [Matrix.add_mul, Matrix.trace_add, Complex.add_re, Matrix.smul_mul, Matrix.smul_mul,
      Matrix.trace_smul, Matrix.trace_smul, Complex.smul_re, Complex.smul_re, smul_eq_mul, smul_eq_mul,
      hTt, Matrix.add_mul, Matrix.trace_add, Complex.add_re, Finset.sum_mul, Matrix.trace_sum,
      Complex.re_sum, Matrix.smul_mul, Matrix.one_mul, Matrix.trace_smul, Complex.smul_re, smul_eq_mul]
    ring

end PBLib




/-! C4 step E8 (part 1): the position-based encoder "keep copy `m`, discard the others". -/

namespace CodeLib
open Matrix

variable {X : Type} [Fintype X] [DecidableEq X] {K : ℕ}

/-- Kraus operators of the encoder for message `m`, indexed by the discarded copies `z`. -/
noncomputable def selK (m : Fin K) (z : {c // c ≠ m} → X) : Matrix X (Fin K → X) ℂ :=
  Matrix.of fun out x => if (fun c : {c // c ≠ m} => x c.1) = z ∧ x m = out then 1 else 0

lemma selK_complete (m : Fin K) (x x' : Fin K → X) :
    ∑ z : {c // c ≠ m} → X, ∑ out : X, star (selK m z out x) * selK m z out x' =
      (1 : Matrix (Fin K → X) (Fin K → X) ℂ) x x' := by
  simp only [selK, Matrix.of_apply, Matrix.one_apply]
  by_cases hxx : x = x'
  · subst hxx
    rw [if_pos rfl, Fintype.sum_eq_single (fun c : {c // c ≠ m} => x c.1)]
    · rw [Fintype.sum_eq_single (x m)]
      · simp
      · intro out hout; simp [Ne.symm hout]
    · intro z hz; refine Finset.sum_eq_zero (fun out _ => ?_); simp [Ne.symm hz]
  · rw [if_neg hxx]
    refine Finset.sum_eq_zero (fun z _ => Finset.sum_eq_zero (fun out _ => ?_))
    by_cases h1 : (fun c : {c // c ≠ m} => x c.1) = z ∧ x m = out
    · by_cases h2 : (fun c : {c // c ≠ m} => x' c.1) = z ∧ x' m = out
      · exfalso; apply hxx; funext c
        by_cases hc : c = m
        · subst hc; rw [h1.2, h2.2]
        · have := congrFun (h1.1.trans h2.1.symm) ⟨c, hc⟩; exact this
      · simp [h2]
    · simp [h1]

/-- the encoder channel. -/
noncomputable def selCh (m : Fin K) : WildeQIT.QChannel (Fin K → X) X where
  ι := {c // c ≠ m} → X
  K := selK m
  complete := by
    ext x x'
    rw [← selK_complete m x x', Matrix.sum_apply]
    refine Finset.sum_congr rfl (fun z _ => ?_)
    rw [Matrix.mul_apply]
    rfl

end CodeLib

namespace CodeLib
open Matrix
open scoped Kronecker

/-- pure density of a plain vector. -/
noncomputable def pd {ι : Type} (v : ι → ℂ) : Matrix ι ι ℂ := Matrix.of fun p q => v p * (starRingEnd ℂ) (v q)

lemma pureDensity_eq {ι : Type} (ψ : EuclideanSpace ℂ ι) :
    QAlgorithms.pureDensity ψ = pd (fun p => ψ p) := rfl

lemma leftApply_pd {ι a b r : Type} [Fintype ι] [Fintype a] [Fintype r] [DecidableEq r]
    (K : ι → Matrix b a ℂ) (v : a × r → ℂ) :
    WildeQIT.EADamping.leftApply K (pd v) = ∑ i, pd (fun p => ∑ x, K i p.1 x * v (x, p.2)) := by
  have hs : ∀ (P : Prop) [Decidable P] (u : ℂ), star (if P then u else 0) = if P then star u else 0 := by
    intro P _ u; split_ifs <;> simp
  ext p q
  simp only [hs, WildeQIT.EADamping.leftApply, Matrix.sum_apply, pd, Matrix.mul_apply, Matrix.of_apply,
    Matrix.conjTranspose_apply, Matrix.kroneckerMap_apply, Matrix.one_apply, Fintype.sum_prod_type,
    mul_ite, ite_mul, mul_one, mul_zero, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true,
    star_one, star_zero, Finset.sum_ite_eq']
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun x2 _ => ?_)
  rw [Finset.sum_mul, Finset.sum_mul]
  refine Finset.sum_congr rfl (fun x1 _ => ?_)
  simp only [map_mul, Complex.star_def]
  ring

lemma leftApply_sum {ι a b r κ : Type} [Fintype ι] [Fintype a] [Fintype r] [DecidableEq r] [Fintype κ]
    (K : ι → Matrix b a ℂ) (X : κ → Matrix (a × r) (a × r) ℂ) :
    WildeQIT.EADamping.leftApply K (∑ z, X z) = ∑ z, WildeQIT.EADamping.leftApply K (X z) := by
  simp only [WildeQIT.EADamping.leftApply, Matrix.mul_sum, Matrix.sum_mul]
  exact Finset.sum_comm

variable {X : Type} [Fintype X] [DecidableEq X] {K : ℕ}

/-- the word with `x` at copy `m` and `z` elsewhere. -/
def glue (m : Fin K) (z : {c // c ≠ m} → X) (x : X) : Fin K → X :=
  fun c => if h : c = m then x else z ⟨c, h⟩

lemma selK_glue_sum {T : Type} [Fintype T] (e : (Fin K → X) ≃ T) (m : Fin K)
    (z : {c // c ≠ m} → X) (x : X) (F : (Fin K → X) → ℂ) :
    ∑ i, selK m z x (e.symm i) * F (e.symm i) = F (glue m z x) := by
  rw [Equiv.sum_comp e.symm (fun t => selK m z x t * F t)]
  rw [Fintype.sum_eq_single (glue m z x)]
  · have h1 : (fun c : {c // c ≠ m} => glue m z x c.1) = z := by
      funext c; simp [glue, c.2]
    have h2 : glue m z x m = x := by simp [glue]
    simp [selK, h1, h2]
  · intro t ht
    have : ¬ ((fun c : {c // c ≠ m} => t c.1) = z ∧ t m = x) := by
      rintro ⟨h1, h2⟩; apply ht; funext c
      by_cases hc : c = m
      · subst hc; simp [glue, h2]
      · simp only [glue, dif_neg hc]; exact congrFun h1 ⟨c, hc⟩
    simp [selK, this]

/-- the encoder for message `m` on Alice's share, reindexed by `e`. -/
noncomputable def encCh {T : Type} [Fintype T] [DecidableEq T] (e : (Fin K → X) ≃ T) (m : Fin K) :
    WildeQIT.QChannel T X where
  ι := {c // c ≠ m} → X
  K z := (selK m z).submatrix id e.symm
  complete := by
    ext i i'
    rw [Matrix.sum_apply]
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.submatrix_apply, id]
    rw [selK_complete m (e.symm i) (e.symm i')]
    simp [Matrix.one_apply, e.symm.injective.eq_iff]

end CodeLib

namespace CodeLib
open Matrix
open scoped Kronecker

lemma sum_prod_mul {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] (f g : ι → κ → ℂ) :
    ∑ x : ι → κ, (∏ l, f l (x l)) * ∏ l, g l (x l) = ∏ l, ∑ w, f l w * g l w := by
  simp_rw [← Finset.prod_mul_distrib]
  exact (Fintype.prod_sum (fun l w => f l w * g l w)).symm

lemma sum_prod_mul_conj {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] (f g : ι → κ → ℂ) :
    ∑ x : ι → κ, (∏ l, f l (x l)) * (starRingEnd ℂ) (∏ l, g l (x l)) =
      ∏ l, ∑ w, f l w * (starRingEnd ℂ) (g l w) := by
  simp_rw [map_prod]
  exact sum_prod_mul f (fun l w => (starRingEnd ℂ) (g l w))

section Code
variable {R A B : Type} [Fintype R] [DecidableEq R] [Fintype A] [DecidableEq A] [Fintype B]
  [DecidableEq B] (N : WildeQIT.QChannel A B) (ψ : R × A → ℂ) {n K dA dB : ℕ}
  (eA : (Fin K → Fin n → A) ≃ Fin dA) (eB : (Fin K → Fin n → R) ≃ Fin dB)

/-- the shared code state: `K` copies of `ψ^{⊗ n}`, Alice's halves in `T_A`, Bob's in `T_B`. -/
def Ψv : Fin dA × Fin dB → ℂ := fun p => ∏ c, ∏ l, ψ (eB.symm p.2 c l, eA.symm p.1 c l)

/-- `φ_i (s, y) = ((1 ⊗ K_i) ψ)(s, y)`. -/
def phiK (i : N.ι) (s : R) (y : B) : ℂ := ∑ w, N.K i y w * ψ (s, w)

/-- the reference marginal `σ = Tr_A |ψ⟩⟨ψ|`. -/
def sigR (s s' : R) : ℂ := ∑ w, ψ (s, w) * (starRingEnd ℂ) (ψ (s', w))

/-- entries of `ρ = (id ⊗ N)(|ψ⟩⟨ψ|)`. -/
def rhoE (p q : R × B) : ℂ := ∑ i, phiK N ψ i p.1 p.2 * (starRingEnd ℂ) (phiK N ψ i q.1 q.2)

lemma enc_vec (m : Fin K) (z : {c // c ≠ m} → Fin n → A) (x : Fin n → A) (j : Fin dB) :
    ∑ i', (encCh eA m).K z x i' * Ψv ψ eA eB (i', j) =
      (∏ l, ψ (eB.symm j m l, x l)) * ∏ c : {c // c ≠ m}, ∏ l, ψ (eB.symm j c l, z c l) := by
  have h := selK_glue_sum eA m z x (fun t => ∏ c, ∏ l, ψ (eB.symm j c l, t c l))
  refine h.trans ?_
  rw [Fintype.prod_eq_mul_prod_subtype_ne _ m]
  congr 1
  · simp [glue]
  · refine Finset.prod_congr rfl (fun c _ => ?_)
    simp only [glue, dif_neg c.2]

lemma w_eq (m : Fin K) (z : {c // c ≠ m} → Fin n → A) (i : Fin n → N.ι) (y : Fin n → B) (j : Fin dB) :
    ∑ x, WildeQIT.EADamping.powKraus N n i y x * ∑ i', (encCh eA m).K z x i' * Ψv ψ eA eB (i', j) =
      (∏ l, phiK N ψ (i l) (eB.symm j m l) (y l)) *
        ∏ c : {c // c ≠ m}, ∏ l, ψ (eB.symm j c l, z c l) := by
  simp_rw [enc_vec, ← mul_assoc]
  rw [← Finset.sum_mul]
  congr 1
  simp only [WildeQIT.EADamping.powKraus, Matrix.of_apply, phiK]
  exact sum_prod_mul (fun l w => N.K (i l) (y l) w) (fun l w => ψ (eB.symm j m l, w))

/-- the channel output for message `m`. -/
noncomputable def ωm (m : Fin K) : Matrix ((Fin n → B) × Fin dB) ((Fin n → B) × Fin dB) ℂ :=
  WildeQIT.EADamping.leftApply (WildeQIT.EADamping.powKraus N n)
    (WildeQIT.EADamping.leftApply (encCh eA m).K (pd (Ψv ψ eA eB)))

lemma ωm_eq (m : Fin K) : ωm N ψ eA eB m = ∑ z : {c // c ≠ m} → Fin n → A, ∑ i : Fin n → N.ι,
    pd (fun p : (Fin n → B) × Fin dB => (∏ l, phiK N ψ (i l) (eB.symm p.2 m l) (p.1 l)) *
        ∏ c : {c // c ≠ m}, ∏ l, ψ (eB.symm p.2 c l, z c l)) := by
  rw [ωm, leftApply_pd, leftApply_sum]
  refine Finset.sum_congr rfl (fun z _ => ?_)
  rw [leftApply_pd]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  congr 1
  funext p
  exact w_eq N ψ eA eB m z i p.1 p.2

lemma ωm_apply (m : Fin K) (y y' : Fin n → B) (j j' : Fin dB) :
    ωm N ψ eA eB m (y, j) (y', j') =
      (∏ l, rhoE N ψ (eB.symm j m l, y l) (eB.symm j' m l, y' l)) *
        ∏ c : {c // c ≠ m}, ∏ l, sigR ψ (eB.symm j c l) (eB.symm j' c l) := by
  rw [ωm_eq, Matrix.sum_apply]
  simp only [Matrix.sum_apply, pd, Matrix.of_apply, map_mul]
  have e1 : ∀ (z : {c // c ≠ m} → Fin n → A) (i : Fin n → N.ι),
      (∏ l, phiK N ψ (i l) (eB.symm j m l) (y l)) * (∏ c : {c // c ≠ m}, ∏ l, ψ (eB.symm j c l, z c l)) *
        ((starRingEnd ℂ) (∏ l, phiK N ψ (i l) (eB.symm j' m l) (y' l)) *
          (starRingEnd ℂ) (∏ c : {c // c ≠ m}, ∏ l, ψ (eB.symm j' c l, z c l))) =
      ((∏ l, phiK N ψ (i l) (eB.symm j m l) (y l)) *
          (starRingEnd ℂ) (∏ l, phiK N ψ (i l) (eB.symm j' m l) (y' l))) *
        ((∏ c : {c // c ≠ m}, ∏ l, ψ (eB.symm j c l, z c l)) *
          (starRingEnd ℂ) (∏ c : {c // c ≠ m}, ∏ l, ψ (eB.symm j' c l, z c l))) := by
    intro z i; ring
  simp_rw [e1, ← Finset.sum_mul, ← Finset.mul_sum]
  congr 1
  · exact sum_prod_mul_conj (fun l w => phiK N ψ w (eB.symm j m l) (y l))
      (fun l w => phiK N ψ w (eB.symm j' m l) (y' l))
  · refine (sum_prod_mul_conj (fun (c : {c // c ≠ m}) (w : Fin n → A) => ∏ l, ψ (eB.symm j c l, w l))
      (fun (c : {c // c ≠ m}) (w : Fin n → A) => ∏ l, ψ (eB.symm j' c l, w l))).trans ?_
    refine Finset.prod_congr rfl (fun c _ => ?_)
    exact sum_prod_mul_conj (fun l a => ψ (eB.symm j c l, a)) (fun l a => ψ (eB.symm j' c l, a))

end Code
end CodeLib

namespace CodeLib
open Matrix
open scoped Kronecker

section Rho
variable {R A B : Type} [Fintype R] [DecidableEq R] [Fintype A] [DecidableEq A] [Fintype B]
  [DecidableEq B] (N : WildeQIT.QChannel A B) (ψ : R × A → ℂ)

lemma idTensor_pd_apply (p q : R × B) :
    WildeQIT.EADamping.idTensorApply N (pd ψ) p q = rhoE N ψ p q := by
  have hs : ∀ (P : Prop) [Decidable P] (u : ℂ), star (if P then u else 0) = if P then star u else 0 := by
    intro P _ u; split_ifs <;> simp
  simp only [hs, WildeQIT.EADamping.idTensorApply, Matrix.sum_apply, pd, Matrix.mul_apply, Matrix.of_apply,
    Matrix.conjTranspose_apply, Matrix.kroneckerMap_apply, Matrix.one_apply, Fintype.sum_prod_type_right,
    ite_mul, one_mul, zero_mul, mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true,
    star_one, star_zero, rhoE, phiK]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun x2 _ => ?_)
  rw [Finset.sum_mul, Finset.sum_mul]
  refine Finset.sum_congr rfl (fun x1 _ => ?_)
  simp only [map_mul, Complex.star_def]
  ring

lemma traceRight_rho (s s' : R) :
    QAlgorithms.traceRight (WildeQIT.EADamping.idTensorApply N (pd ψ)) s s' = sigR ψ s s' := by
  have hc : ∀ w w' : A, ∑ i, ∑ y, (starRingEnd ℂ) (N.K i y w') * N.K i y w = if w' = w then 1 else 0 := by
    intro w w'
    have h := congrFun (congrFun N.complete w') w
    rw [Matrix.sum_apply] at h
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Complex.star_def] at h
    rw [h, Matrix.one_apply]
  simp only [QAlgorithms.traceRight, Matrix.of_apply, idTensor_pd_apply, rhoE, phiK, sigR]
  calc ∑ y, ∑ i, (∑ w, N.K i y w * ψ (s, w)) * (starRingEnd ℂ) (∑ w', N.K i y w' * ψ (s', w'))
      = ∑ y, ∑ i, ∑ w, ∑ w', N.K i y w * ψ (s, w) * ((starRingEnd ℂ) (N.K i y w') *
          (starRingEnd ℂ) (ψ (s', w'))) := by
        simp only [map_sum, map_mul, Finset.sum_mul, Finset.mul_sum]
        exact Finset.sum_congr rfl (fun y _ => Finset.sum_congr rfl (fun i _ => Finset.sum_comm))
    _ = ∑ i, ∑ w, ∑ w', ∑ y, N.K i y w * ψ (s, w) * ((starRingEnd ℂ) (N.K i y w') *
          (starRingEnd ℂ) (ψ (s', w'))) := by
        refine Finset.sum_comm.trans (Finset.sum_congr rfl (fun i _ => ?_))
        refine Finset.sum_comm.trans (Finset.sum_congr rfl (fun w _ => ?_))
        exact Finset.sum_comm
    _ = ∑ w, ∑ w', ∑ i, ∑ y, N.K i y w * ψ (s, w) * ((starRingEnd ℂ) (N.K i y w') *
          (starRingEnd ℂ) (ψ (s', w'))) := by
        refine Finset.sum_comm.trans (Finset.sum_congr rfl (fun w _ => ?_))
        exact Finset.sum_comm
    _ = ∑ w, ∑ w', ψ (s, w) * (starRingEnd ℂ) (ψ (s', w')) *
          ∑ i, ∑ y, (starRingEnd ℂ) (N.K i y w') * N.K i y w := by
        refine Finset.sum_congr rfl (fun w _ => Finset.sum_congr rfl (fun w' _ => ?_))
        simp only [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun y _ => ?_))
        ring
    _ = ∑ w, ψ (s, w) * (starRingEnd ℂ) (ψ (s', w)) := by
        simp only [hc, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]

lemma traceLeft_rho (y y' : B) :
    QAlgorithms.traceLeft (WildeQIT.EADamping.idTensorApply N (pd ψ)) y y' = ∑ s, rhoE N ψ (s, y) (s, y') := by
  simp only [QAlgorithms.traceLeft, Matrix.of_apply, idTensor_pd_apply]

end Rho
end CodeLib

namespace CodeLib
open Matrix

lemma sum2_prod {ι κ1 κ2 : Type} [Fintype ι] [DecidableEq ι] [Fintype κ1] [Fintype κ2]
    (f : ι → κ1 → κ2 → ℂ) :
    ∑ x : ι → κ1, ∑ r : ι → κ2, ∏ l, f l (x l) (r l) = ∏ l, ∑ u, ∑ v, f l u v := by
  calc ∑ x : ι → κ1, ∑ r : ι → κ2, ∏ l, f l (x l) (r l) = ∑ x : ι → κ1, ∏ l, ∑ v, f l (x l) v :=
        Finset.sum_congr rfl (fun x _ => (Fintype.prod_sum (fun l v => f l (x l) v)).symm)
    _ = _ := (Fintype.prod_sum (fun l u => ∑ v, f l u v)).symm

lemma sum_mul_conj_eq {ι : Type} [Fintype ι] (v : ι → ℂ) :
    ∑ p, v p * (starRingEnd ℂ) (v p) = ((∑ p, ‖v p‖ ^ 2 : ℝ) : ℂ) := by
  push_cast
  refine Finset.sum_congr rfl (fun p _ => ?_)
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  push_cast; ring

lemma euclid_sum_one {ι : Type} [Fintype ι] (ψ : EuclideanSpace ℂ ι) (h : ‖ψ‖ = 1) :
    ∑ p, ψ p * (starRingEnd ℂ) (ψ p) = 1 := by
  rw [sum_mul_conj_eq]
  rw [EuclideanSpace.norm_eq, Real.sqrt_eq_one] at h
  rw [h]; simp

lemma norm_toLp_one {ι : Type} [Fintype ι] (v : ι → ℂ) (h : ∑ p, v p * (starRingEnd ℂ) (v p) = 1) :
    ‖(WithLp.toLp 2 v : EuclideanSpace ℂ ι)‖ = 1 := by
  rw [EuclideanSpace.norm_eq, Real.sqrt_eq_one]
  rw [sum_mul_conj_eq] at h
  exact_mod_cast h

section Norm
variable {R A : Type} [Fintype R] [DecidableEq R] [Fintype A] [DecidableEq A] (ψ : R × A → ℂ) {n K dA dB : ℕ}
  (eA : (Fin K → Fin n → A) ≃ Fin dA) (eB : (Fin K → Fin n → R) ≃ Fin dB)

lemma Ψv_sum (h1 : ∑ q, ψ q * (starRingEnd ℂ) (ψ q) = 1) :
    ∑ p, Ψv ψ eA eB p * (starRingEnd ℂ) (Ψv ψ eA eB p) = 1 := by
  rw [Fintype.sum_prod_type, ← Equiv.sum_comp eA]
  simp_rw [← Equiv.sum_comp eB (fun j => Ψv ψ eA eB (eA _, j) * (starRingEnd ℂ) (Ψv ψ eA eB (eA _, j)))]
  simp only [Ψv, Equiv.symm_apply_apply, map_prod, ← Finset.prod_mul_distrib]
  rw [sum2_prod (fun c (u : Fin n → A) (v : Fin n → R) =>
    ∏ l, ψ (v l, u l) * (starRingEnd ℂ) (ψ (v l, u l)))]
  refine Finset.prod_eq_one (fun c _ => ?_)
  rw [sum2_prod (fun l (u : A) (v : R) => ψ (v, u) * (starRingEnd ℂ) (ψ (v, u)))]
  refine Finset.prod_eq_one (fun l _ => ?_)
  rw [Fintype.sum_prod_type] at h1
  rw [Finset.sum_comm]; exact h1

end Norm
end CodeLib

namespace CodeLib
open Matrix
open scoped ComplexOrder

lemma pd_psd {ι : Type} [Fintype ι] (v : ι → ℂ) : (pd v).PosSemidef := by
  have : pd v = Matrix.vecMulVec v (star v) := by
    ext p q; simp [pd, Matrix.vecMulVec_apply, Pi.star_apply, Complex.star_def]
  rw [this]; exact Matrix.posSemidef_vecMulVec_self_star v

lemma ωm_psd {R A B : Type} [Fintype R] [DecidableEq R] [Fintype A] [DecidableEq A] [Fintype B]
    [DecidableEq B] (N : WildeQIT.QChannel A B) (ψ : R × A → ℂ) {n K dA dB : ℕ}
    (eA : (Fin K → Fin n → A) ≃ Fin dA) (eB : (Fin K → Fin n → R) ≃ Fin dB) (m : Fin K) :
    (ωm N ψ eA eB m).PosSemidef := by
  rw [ωm_eq]
  exact Matrix.posSemidef_sum _ (fun z _ => Matrix.posSemidef_sum _ (fun i _ => pd_psd _))

end CodeLib

namespace CodeLib
open Matrix
open scoped Kronecker

noncomputable def kp {ι : Type} (M : Matrix ι ι ℂ) (k : ℕ) : Matrix (Fin k → ι) (Fin k → ι) ℂ :=
  Matrix.of fun f g => ∏ i, M (f i) (g i)

lemma trace_submatrix_eqv {ι κ : Type} [Fintype ι] [Fintype κ] (M : Matrix κ κ ℂ) (e : ι ≃ κ) :
    (M.submatrix e e).trace = M.trace := by
  simp only [Matrix.trace, Matrix.diag, Matrix.submatrix_apply]
  exact Equiv.sum_comp e (fun i => M i i)

lemma tr_kron_one_left {α β : Type} [Fintype α] [Fintype β] [DecidableEq β] (P : Matrix α α ℂ)
    (X : Matrix (α × β) (α × β) ℂ) :
    ((P ⊗ₖ (1 : Matrix β β ℂ)) * X).trace = (P * QAlgorithms.traceRight X).trace := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.kroneckerMap_apply, Matrix.one_apply,
    QAlgorithms.traceRight, Matrix.of_apply, Fintype.sum_prod_type, mul_ite, mul_one, mul_zero, ite_mul,
    zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true, Finset.mul_sum]
  exact Finset.sum_congr rfl (fun a _ => Finset.sum_comm)

section G
variable {R B : Type} [Fintype R] [DecidableEq R] [Fintype B] {n K dB : ℕ}
  (eB : (Fin K → Fin n → R) ≃ Fin dB)

def gl (j : Fin K) (w : Fin n → R) (z : {c // c ≠ j} → Fin n → R) : Fin K → Fin n → R :=
  fun c => if h : c = j then w else z ⟨c, h⟩

def gEq (j : Fin K) : (Fin n → B) × Fin dB ≃ (Fin n → R × B) × ({c // c ≠ j} → Fin n → R) where
  toFun p := (fun l => (eB.symm p.2 j l, p.1 l), fun c => eB.symm p.2 c.1)
  invFun q := (fun l => (q.1 l).2, eB (gl j (fun l => (q.1 l).1) q.2))
  left_inv p := by
    rcases p with ⟨y, i⟩
    simp only [Prod.mk.injEq, true_and]
    rw [Equiv.apply_eq_iff_eq_symm_apply]
    funext c
    by_cases h : c = j
    · subst h; simp [gl]
    · simp [gl, h]
  right_inv q := by
    rcases q with ⟨u, z⟩
    simp only [Equiv.symm_apply_apply, gl, Prod.mk.injEq]
    constructor
    · funext l; simp
    · funext c; simp [c.2]

lemma gEq_symm_apply (j : Fin K) (u : Fin n → R × B) (z : {c // c ≠ j} → Fin n → R) :
    (gEq (B := B) eB j).symm (u, z) = (fun l => (u l).2, eB (gl j (fun l => (u l).1) z)) := rfl

end G

section Tr
variable {R A B : Type} [Fintype R] [DecidableEq R] [Fintype A] [DecidableEq A] [Fintype B]
  [DecidableEq B] (N : WildeQIT.QChannel A B) (ψ : R × A → ℂ) {n K dA dB : ℕ}
  (eA : (Fin K → Fin n → A) ≃ Fin dA) (eB : (Fin K → Fin n → R) ≃ Fin dB)

def Gf (m : Fin K) (y y' : Fin n → B) (c : Fin K) (w w' : Fin n → R) : ℂ :=
  if c = m then ∏ l, rhoE N ψ (w l, y l) (w' l, y' l) else ∏ l, sigR ψ (w l) (w' l)

lemma ωm_G (m : Fin K) (y y' : Fin n → B) (r r' : Fin K → Fin n → R) :
    ωm N ψ eA eB m (y, eB r) (y', eB r') = ∏ c, Gf N ψ m y y' c (r c) (r' c) := by
  rw [ωm_apply, Equiv.symm_apply_apply, Equiv.symm_apply_apply,
    Fintype.prod_eq_mul_prod_subtype_ne _ m]
  simp only [Gf, if_true]
  congr 1
  exact Finset.prod_congr rfl (fun c _ => (if_neg c.2).symm)

lemma trR_coords (m j : Fin K) (u u' : Fin n → R × B) :
    QAlgorithms.traceRight ((ωm N ψ eA eB m).submatrix (gEq eB j).symm (gEq eB j).symm) u u' =
      Gf N ψ m (fun l => (u l).2) (fun l => (u' l).2) j (fun l => (u l).1) (fun l => (u' l).1) *
        ∏ c : {c // c ≠ j}, ∑ w, Gf N ψ m (fun l => (u l).2) (fun l => (u' l).2) c.1 w w := by
  simp only [QAlgorithms.traceRight, Matrix.of_apply, Matrix.submatrix_apply, gEq_symm_apply, ωm_G]
  have hz : ∀ z : {c // c ≠ j} → Fin n → R,
      ∏ c, Gf N ψ m (fun l => (u l).2) (fun l => (u' l).2) c (gl j (fun l => (u l).1) z c)
          (gl j (fun l => (u' l).1) z c) =
        Gf N ψ m (fun l => (u l).2) (fun l => (u' l).2) j (fun l => (u l).1) (fun l => (u' l).1) *
          ∏ c : {c // c ≠ j}, Gf N ψ m (fun l => (u l).2) (fun l => (u' l).2) c.1 (z c) (z c) := by
    intro z
    rw [Fintype.prod_eq_mul_prod_subtype_ne _ j]
    simp only [gl, dif_pos rfl]
    congr 1
    refine Finset.prod_congr rfl (fun c _ => ?_)
    simp only [dif_neg c.2]
  simp only [hz, ← Finset.mul_sum]
  congr 1
  exact (Fintype.prod_sum (fun (c : {c // c ≠ j}) w =>
    Gf N ψ m (fun l => (u l).2) (fun l => (u' l).2) c.1 w w)).symm

lemma sum_sigR (h1 : ∑ q, ψ q * (starRingEnd ℂ) (ψ q) = 1) : ∑ s, sigR ψ s s = 1 := by
  simp only [sigR]
  rw [← h1, Fintype.sum_prod_type]

lemma sum_Gf_ne (h1 : ∑ q, ψ q * (starRingEnd ℂ) (ψ q) = 1) (m c : Fin K) (hc : c ≠ m)
    (y y' : Fin n → B) : ∑ w, Gf N ψ m y y' c w w = 1 := by
  simp only [Gf, if_neg hc]
  rw [← Fintype.prod_sum (fun (_ : Fin n) s => sigR ψ s s), sum_sigR ψ h1]
  simp

lemma sum_Gf_eq (m : Fin K) (y y' : Fin n → B) :
    ∑ w, Gf N ψ m y y' m w w =
      ∏ l, QAlgorithms.traceLeft (WildeQIT.EADamping.idTensorApply N (pd ψ)) (y l) (y' l) := by
  simp only [Gf, if_true, traceLeft_rho]
  exact (Fintype.prod_sum (fun l s => rhoE N ψ (s, y l) (s, y' l))).symm

lemma sub_round {ι κ : Type} [Fintype ι] [Fintype κ] (P : Matrix κ κ ℂ) (X : Matrix ι ι ℂ) (g : ι ≃ κ) :
    (P.submatrix g g * X).trace = (P * X.submatrix g.symm g.symm).trace := by
  have : X = (X.submatrix g.symm g.symm).submatrix g g := by
    rw [Matrix.submatrix_submatrix]; simp
  conv_lhs => rw [this, Matrix.submatrix_mul_equiv, trace_submatrix_eqv]

lemma tr_own (h1 : ∑ q, ψ q * (starRingEnd ℂ) (ψ q) = 1) (m : Fin K)
    (P : Matrix (Fin n → R × B) (Fin n → R × B) ℂ) :
    ((P ⊗ₖ (1 : Matrix ({c // c ≠ m} → Fin n → R) ({c // c ≠ m} → Fin n → R) ℂ)).submatrix
        (gEq eB m) (gEq eB m) * ωm N ψ eA eB m).trace =
      (P * kp (WildeQIT.EADamping.idTensorApply N (pd ψ)) n).trace := by
  rw [sub_round, tr_kron_one_left]
  congr 2
  ext u u'
  rw [trR_coords, Finset.prod_eq_one (fun c _ => sum_Gf_ne N ψ h1 m c.1 c.2 _ _), mul_one]
  simp only [Gf, if_true, kp, Matrix.of_apply, idTensor_pd_apply]

lemma tr_other (h1 : ∑ q, ψ q * (starRingEnd ℂ) (ψ q) = 1) (m j : Fin K) (hjm : j ≠ m)
    (P : Matrix (Fin n → R × B) (Fin n → R × B) ℂ) :
    ((P ⊗ₖ (1 : Matrix ({c // c ≠ j} → Fin n → R) ({c // c ≠ j} → Fin n → R) ℂ)).submatrix
        (gEq eB j) (gEq eB j) * ωm N ψ eA eB m).trace =
      (P * kp (QAlgorithms.traceRight (WildeQIT.EADamping.idTensorApply N (pd ψ)) ⊗ₖ
        QAlgorithms.traceLeft (WildeQIT.EADamping.idTensorApply N (pd ψ))) n).trace := by
  rw [sub_round, tr_kron_one_left]
  congr 2
  ext u u'
  rw [trR_coords, Fintype.prod_eq_single (⟨m, hjm.symm⟩ : {c // c ≠ j})]
  · rw [sum_Gf_eq]
    simp only [Gf, if_neg hjm, kp, Matrix.of_apply, Matrix.kroneckerMap_apply, traceRight_rho]
    rw [← Finset.prod_mul_distrib]
  · intro c hc
    exact sum_Gf_ne N ψ h1 m c.1 (fun h => hc (Subtype.ext h)) _ _

end Tr
end CodeLib

namespace FinalLib
open Matrix CodeLib
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder Kronecker

theorem oneshot {R A B : Type} [Fintype R] [DecidableEq R] [Fintype A] [DecidableEq A] [Fintype B]
    [DecidableEq B] (N : WildeQIT.QChannel A B) (ψ : R × A → ℂ)
    (h1 : ∑ q, ψ q * (starRingEnd ℂ) (ψ q) = 1)
    (n K : ℕ) (hK : 0 < K) (P : Matrix (Fin n → R × B) (Fin n → R × B) ℂ) (hP0 : 0 ≤ P) (hP1 : P ≤ 1)
    {η : ℝ} (hη : 0 < η) :
    ∃ c : WildeQIT.EADamping.EACode A B n K, ∀ m, c.errorProb N m ≤
      2 * ((1 - P) * kp (WildeQIT.EADamping.idTensorApply N (pd ψ)) n).trace.re +
      4 * ((K : ℝ) - 1) * (P * kp (QAlgorithms.traceRight (WildeQIT.EADamping.idTensorApply N (pd ψ)) ⊗ₖ
        QAlgorithms.traceLeft (WildeQIT.EADamping.idTensorApply N (pd ψ))) n).trace.re +
      4 * η * (kp (WildeQIT.EADamping.idTensorApply N (pd ψ)) n).trace.re := by
  let eA := Fintype.equivFin (Fin K → Fin n → A)
  let eB := Fintype.equivFin (Fin K → Fin n → R)
  let T : Fin K → Matrix ((Fin n → B) × Fin (Fintype.card (Fin K → Fin n → R)))
      ((Fin n → B) × Fin (Fintype.card (Fin K → Fin n → R))) ℂ := fun j =>
    (P ⊗ₖ (1 : Matrix ({c // c ≠ j} → Fin n → R) ({c // c ≠ j} → Fin n → R) ℂ)).submatrix
      (gEq eB j) (gEq eB j)
  have hone : ∀ (j : Fin K) (Q : Matrix (Fin n → R × B) (Fin n → R × B) ℂ),
      1 - (Q ⊗ₖ (1 : Matrix ({c // c ≠ j} → Fin n → R) ({c // c ≠ j} → Fin n → R) ℂ)).submatrix
        (gEq eB j) (gEq eB j) = ((1 - Q) ⊗ₖ (1 : Matrix ({c // c ≠ j} → Fin n → R)
          ({c // c ≠ j} → Fin n → R) ℂ)).submatrix (gEq eB j) (gEq eB j) := by
    intro j Q
    have hk : (1 - Q) ⊗ₖ (1 : Matrix ({c // c ≠ j} → Fin n → R) ({c // c ≠ j} → Fin n → R) ℂ) =
        (1 : Matrix (Fin n → R × B) (Fin n → R × B) ℂ) ⊗ₖ
          (1 : Matrix ({c // c ≠ j} → Fin n → R) ({c // c ≠ j} → Fin n → R) ℂ) - Q ⊗ₖ 1 :=
      eq_sub_of_add_eq (by rw [← Matrix.add_kronecker, sub_add_cancel])
    rw [hk, Matrix.one_kronecker_one, ← Matrix.submatrix_one_equiv (gEq eB j)]
    rfl
  have hT0 : ∀ j, 0 ≤ T j := fun j => by
    rw [Matrix.nonneg_iff_posSemidef]
    exact (Matrix.posSemidef_submatrix_equiv (gEq eB j)).mpr
      ((Matrix.nonneg_iff_posSemidef.mp hP0).kronecker Matrix.PosSemidef.one)
  have hT1 : ∀ j, T j ≤ 1 := fun j => by
    rw [Matrix.le_iff, hone j P]
    exact (Matrix.posSemidef_submatrix_equiv (gEq eB j)).mpr
      ((Matrix.le_iff.mp hP1).kronecker Matrix.PosSemidef.one)
  obtain ⟨Λ, hΛ, hbound⟩ := PBLib.pb_decoder hK T hT0 hT1 hη
  refine ⟨WildeQIT.EADamping.EACode.mk _ _ (WithLp.toLp 2 (Ψv ψ eA eB))
    (norm_toLp_one _ (Ψv_sum ψ eA eB h1)) (encCh eA) Λ hΛ, fun m => ?_⟩
  show ((1 - Λ m) * ωm N ψ eA eB m).trace.re ≤ _
  have hω0 : 0 ≤ ωm N ψ eA eB m := Matrix.nonneg_iff_posSemidef.mpr (ωm_psd N ψ eA eB m)
  refine (hbound m _ hω0).trans (le_of_eq ?_)
  have e1 : ((1 - T m) * ωm N ψ eA eB m).trace =
      ((1 - P) * kp (WildeQIT.EADamping.idTensorApply N (pd ψ)) n).trace := by
    simp only [T]; rw [hone m P]; exact tr_own N ψ eA eB h1 m (1 - P)
  have e2 : ∀ j ∈ Finset.univ.erase m, (T j * ωm N ψ eA eB m).trace.re =
      (P * kp (QAlgorithms.traceRight (WildeQIT.EADamping.idTensorApply N (pd ψ)) ⊗ₖ
        QAlgorithms.traceLeft (WildeQIT.EADamping.idTensorApply N (pd ψ))) n).trace.re := by
    intro j hj
    rw [tr_other N ψ eA eB h1 m j (Finset.ne_of_mem_erase hj) P]
  have e3 : (ωm N ψ eA eB m).trace = (kp (WildeQIT.EADamping.idTensorApply N (pd ψ)) n).trace := by
    have h := tr_own N ψ eA eB h1 m 1
    rw [Matrix.one_kronecker_one, Matrix.submatrix_one_equiv, Matrix.one_mul, Matrix.one_mul] at h
    exact h
  rw [e1, Finset.sum_congr rfl e2, e3, Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ m),
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_sub (show 1 ≤ K by omega), Nat.cast_one]
  ring


lemma rho_psd {R A B : Type} [Fintype R] [DecidableEq R] [Fintype A] [DecidableEq A] [Fintype B]
    [DecidableEq B] (N : WildeQIT.QChannel A B) (ψ : R × A → ℂ) :
    0 ≤ WildeQIT.EADamping.idTensorApply N (pd ψ) := by
  have h : WildeQIT.EADamping.idTensorApply N (pd ψ) = ∑ i, pd (fun p : R × B => phiK N ψ i p.1 p.2) := by
    ext p q
    rw [idTensor_pd_apply, Matrix.sum_apply]
    simp only [rhoE, pd, Matrix.of_apply]
  rw [h]
  exact Finset.sum_nonneg (fun i _ => Matrix.nonneg_iff_posSemidef.mpr (pd_psd _))

lemma rho_trace {R A B : Type} [Fintype R] [DecidableEq R] [Fintype A] [DecidableEq A] [Fintype B]
    [DecidableEq B] (N : WildeQIT.QChannel A B) (ψ : R × A → ℂ)
    (h1 : ∑ q, ψ q * (starRingEnd ℂ) (ψ q) = 1) :
    (WildeQIT.EADamping.idTensorApply N (pd ψ)).trace = 1 := by
  have h := fun s => traceRight_rho N ψ s s
  simp only [QAlgorithms.traceRight, Matrix.of_apply] at h
  rw [Matrix.trace, Fintype.sum_prod_type]
  simp only [Matrix.diag, h]
  exact sum_sigR ψ h1

theorem direct {a b : Type} [Fintype a] [Fintype b] [DecidableEq a] [DecidableEq b]
    (N : WildeQIT.QChannel a b) (φ : WildeQIT.Degradable.PureInput a) :
    WildeQIT.EADamping.IsAchievableEARate N
      (DattaDiscord.mutualInfo (WildeQIT.EADamping.idTensorApply N (QAlgorithms.pureDensity φ.ψ))) := by
  intro ε hε hε1 δ hδ
  set ψ : Fin φ.m × a → ℂ := fun q => φ.ψ q with hψ
  have h1 : ∑ q, ψ q * (starRingEnd ℂ) (ψ q) = 1 := euclid_sum_one φ.ψ φ.norm_eq_one
  have hpd : QAlgorithms.pureDensity φ.ψ = pd ψ := rfl
  rw [hpd]
  set ρ := WildeQIT.EADamping.idTensorApply N (pd ψ) with hρdef
  obtain ⟨q0⟩ : Nonempty (Fin φ.m × a) := by
    by_contra h
    rw [not_nonempty_iff] at h
    simp at h1
  haveI : Nonempty (Fin φ.m) := ⟨q0.1⟩
  haveI : Nonempty b := by
    by_contra hb
    rw [not_nonempty_iff] at hb
    have h := congrFun (congrFun N.complete q0.2) q0.2
    simp [Matrix.sum_apply, Matrix.mul_apply] at h
  have hl2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  set I := DattaDiscord.mutualInfo ρ with hI
  have hR : Real.log 2 * (I - δ / 2) < Real.log 2 * I := by nlinarith
  obtain ⟨N₀, hN₀⟩ := SmoothLib.stein_mi (rho_psd N ψ) (rho_trace N ψ h1) hR (show 0 < ε / 4 by linarith)
  set c : ℝ := Real.log 2 * (δ / 2) with hcdef
  have hc : 0 < c := by positivity
  refine ⟨max N₀ (⌈16 / (ε * c)⌉₊), fun n hn => ?_⟩
  have hn0 : N₀ ≤ n := le_trans (le_max_left _ _) hn
  have hn1 : 16 / (ε * c) ≤ (n : ℝ) :=
    le_trans (Nat.le_ceil _) (by exact_mod_cast le_trans (le_max_right _ _) hn)
  obtain ⟨T, hT0, hT1, hTa, hTb⟩ := hN₀ n hn0
  have h2pos : 0 < (2:ℝ) ^ ((n:ℝ) * (I - δ)) := Real.rpow_pos_of_pos two_pos _
  have hK : 0 < ⌈(2:ℝ) ^ ((n:ℝ) * (I - δ))⌉₊ := Nat.ceil_pos.mpr h2pos
  refine ⟨⌈(2:ℝ) ^ ((n:ℝ) * (I - δ))⌉₊, Nat.le_ceil _, ?_⟩
  obtain ⟨code, hcode⟩ := oneshot N ψ h1 n _ hK T hT0 hT1 (show (0:ℝ) < ε / 16 by linarith)
  refine ⟨code, fun m => (hcode m).trans ?_⟩
  have hTa' : ((1 - T) * kp ρ n).trace.re ≤ ε / 4 := hTa
  have hTb' : (T * kp (QAlgorithms.traceRight ρ ⊗ₖ QAlgorithms.traceLeft ρ) n).trace.re ≤
      Real.exp (-(n * (Real.log 2 * (I - δ / 2)))) := hTb
  have htr1 : (kp ρ n).trace.re = 1 := by
    have e : kp ρ n = KPLib.kpow ρ n := rfl
    rw [e, KPLib.trace_kpow, rho_trace N ψ h1]
    simp
  have hK1 : ((⌈(2:ℝ) ^ ((n:ℝ) * (I - δ))⌉₊ : ℕ) : ℝ) - 1 ≤ (2:ℝ) ^ ((n:ℝ) * (I - δ)) := by
    have := Nat.ceil_lt_add_one h2pos.le
    linarith
  have hK0 : 0 ≤ ((⌈(2:ℝ) ^ ((n:ℝ) * (I - δ))⌉₊ : ℕ) : ℝ) - 1 := by
    have : (1:ℝ) ≤ ((⌈(2:ℝ) ^ ((n:ℝ) * (I - δ))⌉₊ : ℕ) : ℝ) := by exact_mod_cast hK
    linarith
  have hexp : (2:ℝ) ^ ((n:ℝ) * (I - δ)) * Real.exp (-(n * (Real.log 2 * (I - δ / 2)))) =
      Real.exp (-(n * c)) := by
    rw [Real.rpow_def_of_pos two_pos, ← Real.exp_add, hcdef]
    congr 1
    ring
  have hsmall : Real.exp (-(n * c)) ≤ ε / 16 := by
    have h16 : 16 ≤ (n:ℝ) * (ε * c) := by
      have := (div_le_iff₀ (mul_pos hε hc)).mp hn1
      linarith
    have hE := Real.add_one_le_exp ((n:ℝ) * c)
    have hEE : Real.exp (-(n * c)) * Real.exp (n * c) = 1 := by
      rw [← Real.exp_add]; simp
    have hεE : 16 ≤ ε * Real.exp (n * c) := by nlinarith
    have he0 := Real.exp_pos (-(n * c))
    nlinarith [mul_le_mul_of_nonneg_right hεE he0.le]
  have hprod : (((⌈(2:ℝ) ^ ((n:ℝ) * (I - δ))⌉₊ : ℕ) : ℝ) - 1) *
      (T * kp (QAlgorithms.traceRight ρ ⊗ₖ QAlgorithms.traceLeft ρ) n).trace.re ≤ ε / 16 :=
    calc _ ≤ (((⌈(2:ℝ) ^ ((n:ℝ) * (I - δ))⌉₊ : ℕ) : ℝ) - 1) *
          Real.exp (-(n * (Real.log 2 * (I - δ / 2)))) := mul_le_mul_of_nonneg_left hTb' hK0
      _ ≤ (2:ℝ) ^ ((n:ℝ) * (I - δ)) * Real.exp (-(n * (Real.log 2 * (I - δ / 2)))) :=
          mul_le_mul_of_nonneg_right hK1 (Real.exp_pos _).le
      _ = Real.exp (-(n * c)) := hexp
      _ ≤ ε / 16 := hsmall
  rw [htr1]
  linarith

end FinalLib

open WildeQIT WildeQIT.EADamping in
theorem solution {a b : Type} [Fintype a] [Fintype b] [DecidableEq a] [DecidableEq b]
    (N : QChannel a b) (φ : WildeQIT.Degradable.PureInput a) :
    IsAchievableEARate N
      (DattaDiscord.mutualInfo (idTensorApply N (QAlgorithms.pureDensity φ.ψ))) := by
  exact FinalLib.direct N φ
