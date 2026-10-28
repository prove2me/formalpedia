-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Claimed50.P08.sum_rate_redundancy
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T10:36:51.161873+00:00
-- url     : https://prove2.me/submissions/0c8206fa-41be-4939-acd6-17c8c8b06257

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P08
import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P33
import Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P20_strongSubadditivity
import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P41
import Definitions.Def_QAlgorithms_Defs_QuantumInformation
import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P42
import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P20
import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P24

-- ===== C1A =====

/-! Strong subadditivity for disjoint register sets (Claimed50.P33 conventions). -/

noncomputable section

namespace X4C1
open Matrix QAlgorithms
open QAlgorithms.Papers.Independent.Claimed50.P33
open QAlgorithms.Papers.Independent.Gap48.P20 (redistributionMarginal subsystemEntropy strongSubadditivity)
open scoped Matrix ComplexConjugate ComplexOrder

attribute [local instance] Classical.propDecidable Classical.decEq

noncomputable def selM {X K F : Type*} (k : X → K) (f : X → F) (φ : F) : Matrix K X ℂ :=
  Matrix.of fun a x => if k x = a ∧ f x = φ then (1:ℂ) else 0

lemma rmA {X K F : Type*} [Fintype X] [Fintype K] [Fintype F] (ρ : Matrix X X ℂ)
    (k : X → K) (f : X → F) :
    redistributionMarginal ρ k f = ∑ φ : F, selM k f φ * ρ * (selM k f φ)ᴴ := by
  ext a b
  simp only [redistributionMarginal, Matrix.sum_apply, Matrix.mul_apply, conjTranspose_apply, selM, of_apply,
    Finset.sum_mul]
  symm
  rw [Finset.sum_comm]
  simp_rw [Finset.sum_comm (s := (Finset.univ : Finset F)) (t := (Finset.univ : Finset X))]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
  rw [Finset.sum_eq_single (f x)]
  · by_cases hx : k x = a <;> by_cases hy : k y = b <;> by_cases hxy : f x = f y <;>
      simp [hx, hy, hxy, eq_comm]
  · intro φ _ hφ
    have : ¬ f x = φ := fun h => hφ h.symm
    simp [this]
  · simp

lemma rm_density {X K F : Type*} [Fintype X] [Fintype K] [Fintype F] (ρ : Matrix X X ℂ)
    (k : X → K) (f : X → F) (hinj : ∀ x y, k x = k y → f x = f y → x = y)
    (hρ : IsDensityMatrix ρ) : IsDensityMatrix (redistributionMarginal ρ k f) := by
  have hA := rmA ρ k f
  refine ⟨?_, ?_⟩
  · rw [hA]
    exact Matrix.posSemidef_sum _ fun φ _ => hρ.1.mul_mul_conjTranspose_same (selM k f φ)
  · rw [← hρ.2]
    simp only [Matrix.trace, Matrix.diag, redistributionMarginal]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.sum_comm, Finset.sum_eq_single x]
    · rw [Finset.sum_eq_single (k x)]
      · simp
      · intro b _ hb; rw [if_neg]; rintro ⟨h1, _⟩; exact hb h1.symm
      · simp
    · intro y _ hy
      refine Finset.sum_eq_zero fun a _ => ?_
      rw [if_neg]; rintro ⟨h1, h2, h3⟩; exact hy (hinj _ _ (h1.trans h2.symm) h3).symm
    · simp

variable {n : ℕ} {D : Fin n → Type} [∀ i, Fintype (D i)]

end X4C1

end

-- ===== C1B =====

/-! Conditional mutual information of disjoint register sets is nonnegative. -/

noncomputable section

namespace X4C1
open Matrix QAlgorithms
open QAlgorithms.Papers.Independent.Claimed50.P33
open QAlgorithms.Papers.Independent.Gap48.P20 (redistributionMarginal subsystemEntropy strongSubadditivity)
open scoped Matrix ComplexConjugate ComplexOrder

attribute [local instance] Classical.propDecidable Classical.decEq

variable {n : ℕ} {D : Fin n → Type} [∀ i, Fintype (D i)]

lemma vn_reindex {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (e : κ ≃ ι) {X : Matrix ι ι ℂ} (hX : IsSelfAdjoint X) :
    vnEntropy (X.submatrix e e) = vnEntropy X := by
  let φ : Matrix ι ι ℂ →⋆ₐ[ℂ] Matrix κ κ ℂ :=
    { (Matrix.reindexAlgEquiv ℂ ℂ e.symm).toAlgHom with
      map_star' := fun M => by
        ext a b; simp [Matrix.star_eq_conjTranspose, Matrix.reindexAlgEquiv] }
  have hφ : ∀ M, φ M = M.submatrix e e := fun M => by
    ext a b; simp [φ, Matrix.reindexAlgEquiv]
  have hc : Continuous φ := by
    have : (φ : Matrix ι ι ℂ → Matrix κ κ ℂ) = fun M => M.submatrix e e := funext hφ
    rw [this]; fun_prop
  have hXs : IsSelfAdjoint (φ X) := hX.map φ
  unfold vnEntropy
  rw [← hφ, ← StarAlgHom.map_cfc φ (fun x : ℝ => x * Real.logb 2 x) X (hf := Matrix.finite_real_spectrum.continuousOn _) (hφ := hc) (ha := hX) (hφa := hXs), hφ]
  simp only [Matrix.trace, Matrix.diag, Matrix.submatrix_apply]
  rw [e.sum_comp (fun i => cfc (fun x : ℝ => x * Real.logb 2 x) X i i)]

variable [∀ i, Nonempty (D i)]

end X4C1

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

end X4FN

end

-- ===== SFB =====

/-! Generic: `Σ_k |tr(ρ E_k)|² ≤ F(ρ, Σ_k E_k ρ E_kᴴ)²` for PSD `ρ`. -/

noncomputable section

namespace X4SF
open Matrix QAlgorithms
open scoped Matrix ComplexOrder ComplexConjugate

variable {ι K : Type*} [Fintype ι] [DecidableEq ι] [Fintype K]

end X4SF

end

-- ===== SUB =====

/-! Generic: subadditivity of von Neumann entropy, `S(AB) ≤ S(A) + S(B)`. -/

noncomputable section

namespace X4SU
open Matrix Real QAlgorithms
open scoped Matrix ComplexConjugate ComplexOrder Kronecker

variable {A B : Type*} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

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

end X4ER

end

-- ===== DPI =====

/-! Data processing for conditional entropy: a local channel on `A` (in Kraus form) does not
decrease `H(C | A Y)`, i.e. `S(AY) - S(AYC)` can only decrease. Proof: Stinespring isometry
from the Kraus family, isometric invariance of entropy, and strong subadditivity. -/

noncomputable section

namespace X4DPI
open Matrix QAlgorithms
open QAlgorithms.Papers.Independent.Gap48.P20 (redistributionMarginal subsystemEntropy strongSubadditivity)
open scoped Matrix ComplexConjugate ComplexOrder Kronecker

attribute [local instance] Classical.propDecidable Classical.decEq

lemma rm_e {X K F : Type*} [Fintype X] [Fintype K] [Fintype F] (M : Matrix X X ℂ) (e : X ≃ K × F)
    (k : X → K) (f : X → F) (hk : ∀ x, k x = (e x).1) (hf : ∀ x, f x = (e x).2) (a b : K) :
    redistributionMarginal M k f a b = ∑ φ, M (e.symm (a, φ)) (e.symm (b, φ)) := by
  simp only [redistributionMarginal, hk, hf]
  rw [← e.symm.sum_comp]
  simp_rw [← e.symm.sum_comp (fun y => if _ then _ else _)]
  simp only [Equiv.apply_symm_apply, Fintype.sum_prod_type]
  rw [Finset.sum_eq_single a, Finset.sum_comm, Finset.sum_eq_single b]
  · refine Finset.sum_congr rfl fun φ _ => ?_
    rw [Finset.sum_eq_single φ]
    · simp
    · intro ψ _ h; simp [Ne.symm h]
    · simp
  · intro c _ hc
    refine Finset.sum_eq_zero fun φ _ => Finset.sum_eq_zero fun ψ _ => ?_
    simp [hc]
  · simp
  · intro c _ hc
    refine Finset.sum_eq_zero fun φ _ => Finset.sum_eq_zero fun ψ _ => Finset.sum_eq_zero fun d _ => ?_
    simp [hc]
  · simp

lemma sum4 {α β γ δ : Type*} [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]
    (f : α → β → γ → δ → ℂ) :
    ∑ a, ∑ b, ∑ c, ∑ d, f a b c d = ∑ c, ∑ d, ∑ a, ∑ b, f a b c d := by
  calc ∑ a, ∑ b, ∑ c, ∑ d, f a b c d = ∑ a, ∑ c, ∑ d, ∑ b, f a b c d :=
        Finset.sum_congr rfl fun a _ => by
          rw [Finset.sum_comm]; exact Finset.sum_congr rfl fun c _ => Finset.sum_comm
    _ = ∑ c, ∑ a, ∑ d, ∑ b, f a b c d := Finset.sum_comm
    _ = ∑ c, ∑ d, ∑ a, ∑ b, f a b c d := Finset.sum_congr rfl fun c _ => Finset.sum_comm

variable {A A' Y C R : Type} [Fintype A] [Fintype A'] [Fintype Y] [Fintype C] [Fintype R]
  {N : ℕ} (E : Fin N → Matrix A' A ℂ)

/-- Local action of the Kraus family on the first factor. -/
def act (ρ : Matrix ((A × Y) × (C × R)) ((A × Y) × (C × R)) ℂ) :
    Matrix ((A' × Y) × (C × R)) ((A' × Y) × (C × R)) ℂ :=
  fun u v => ∑ k, ∑ a, ∑ b, E k u.1.1 a * ρ ((a, u.1.2), u.2) ((b, v.1.2), v.2) * conj (E k v.1.1 b)

/-- Trace out `R`. -/
def M1 {B : Type} (X : Matrix ((B × Y) × (C × R)) ((B × Y) × (C × R)) ℂ) :
    Matrix ((B × Y) × C) ((B × Y) × C) ℂ :=
  fun u v => ∑ r, X (u.1, (u.2, r)) (v.1, (v.2, r))

/-- Trace out `C × R`. -/
def M2 {B : Type} (X : Matrix ((B × Y) × (C × R)) ((B × Y) × (C × R)) ℂ) :
    Matrix (B × Y) (B × Y) ℂ :=
  fun u v => ∑ c, ∑ r, X (u, (c, r)) (v, (c, r))

lemma M1_rm {B : Type} [Fintype B] (X : Matrix ((B × Y) × (C × R)) ((B × Y) × (C × R)) ℂ) :
    M1 X = redistributionMarginal X (fun x => (x.1, x.2.1)) (fun x => x.2.2) := by
  funext u v
  rw [rm_e X (Equiv.prodAssoc _ _ _).symm (fun x => (x.1, x.2.1)) (fun x => x.2.2) (fun _ => rfl) (fun _ => rfl)]
  rfl

lemma M2_rm {B : Type} [Fintype B] (X : Matrix ((B × Y) × (C × R)) ((B × Y) × (C × R)) ℂ) :
    M2 X = redistributionMarginal X (fun x => x.1) (fun x => x.2) := by
  funext u v
  rw [rm_e X (Equiv.refl _) (fun x => x.1) (fun x => x.2) (fun _ => rfl) (fun _ => rfl)]
  simp only [M2, Fintype.sum_prod_type]
  rfl

/-- Kraus operators of the local action. -/
def L (Y C R : Type) (k : Fin N) : Matrix ((A' × Y) × (C × R)) ((A × Y) × (C × R)) ℂ :=
  Matrix.of fun u x => if u.1.2 = x.1.2 ∧ u.2 = x.2 then E k u.1.1 x.1.1 else 0

lemma L_mul (k : Fin N) (g : (A × Y) × (C × R) → ℂ) (u : (A' × Y) × (C × R)) :
    ∑ x, L E Y C R k u x * g x = ∑ a, E k u.1.1 a * g ((a, u.1.2), u.2) := by
  rw [Fintype.sum_prod_type, Finset.sum_comm, Finset.sum_eq_single u.2, Fintype.sum_prod_type,
    Finset.sum_comm, Finset.sum_eq_single u.1.2]
  · simp [L]
  · intro y _ hy; refine Finset.sum_eq_zero fun a _ => ?_; simp [L, Ne.symm hy]
  · simp
  · intro z _ hz; refine Finset.sum_eq_zero fun a _ => ?_; simp [L, Ne.symm hz]
  · simp

lemma L_mul' (k : Fin N) (g : (A × Y) × (C × R) → ℂ) (u : (A' × Y) × (C × R)) :
    ∑ x, star (L E Y C R k u x) * g x = ∑ a, star (E k u.1.1 a) * g ((a, u.1.2), u.2) := by
  rw [Fintype.sum_prod_type, Finset.sum_comm, Finset.sum_eq_single u.2, Fintype.sum_prod_type,
    Finset.sum_comm, Finset.sum_eq_single u.1.2]
  · simp [L]
  · intro y _ hy; refine Finset.sum_eq_zero fun a _ => ?_; simp [L, Ne.symm hy]
  · simp
  · intro z _ hz; refine Finset.sum_eq_zero fun a _ => ?_; simp [L, Ne.symm hz]
  · simp

lemma L_iso (hE : ∑ k, (E k)ᴴ * E k = 1) :
    ∑ k, (L E Y C R k)ᴴ * L E Y C R k = 1 := by
  ext u v
  have h := congrFun (congrFun hE u.1.1) v.1.1
  simp only [Matrix.sum_apply, Matrix.mul_apply, conjTranspose_apply] at h
  simp only [Matrix.sum_apply, Matrix.mul_apply, conjTranspose_apply]
  have key : ∀ k, ∑ x : (A' × Y) × (C × R), star (L E Y C R k x u) * L E Y C R k x v =
      if u.1.2 = v.1.2 ∧ u.2 = v.2 then ∑ a, star (E k a u.1.1) * E k a v.1.1 else 0 := by
    intro k
    rw [Fintype.sum_prod_type, Finset.sum_comm, Finset.sum_eq_single u.2, Fintype.sum_prod_type,
      Finset.sum_comm, Finset.sum_eq_single u.1.2]
    · by_cases h1 : u.1.2 = v.1.2 <;> by_cases h2 : u.2 = v.2 <;> simp [L, h1, h2]
    · intro y _ hy; refine Finset.sum_eq_zero fun a _ => ?_; simp [L, hy]
    · simp
    · intro z _ hz; refine Finset.sum_eq_zero fun a _ => ?_; simp [L, hz]
    · simp
  simp_rw [key]
  by_cases hc : u.1.2 = v.1.2 ∧ u.2 = v.2
  · simp only [hc, and_self, if_true, h, Matrix.one_apply]
    obtain ⟨⟨a, y⟩, z⟩ := u; obtain ⟨⟨b, y'⟩, z'⟩ := v
    obtain ⟨h1, h2⟩ := hc; simp only at h1 h2; subst h1 h2
    simp [Prod.ext_iff]
  · simp only [hc, if_false, Finset.sum_const_zero, Matrix.one_apply]
    rw [if_neg]; rintro rfl; exact hc ⟨rfl, rfl⟩

lemma act_eq (ρ : Matrix ((A × Y) × (C × R)) ((A × Y) × (C × R)) ℂ) :
    act E ρ = ∑ k, L E Y C R k * ρ * (L E Y C R k)ᴴ := by
  ext u v
  simp only [Matrix.sum_apply, Matrix.mul_apply, conjTranspose_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp_rw [L_mul E k (fun x => ρ x _), Finset.sum_mul]
  rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  have : ∀ i, ∑ x, E k u.1.1 i * ρ ((i, u.1.2), u.2) x * star (L E Y C R k v x) =
      ∑ b, star (E k v.1.1 b) * (E k u.1.1 i * ρ ((i, u.1.2), u.2) ((b, v.1.2), v.2)) := by
    intro i
    simp_rw [mul_comm _ (star (L E Y C R k v _))]
    exact L_mul' E k (fun x => E k u.1.1 i * ρ ((i, u.1.2), u.2) x) v
  simp_rw [this]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a _ => ?_
  simp only [RCLike.star_def]; ring

lemma act_density (hE : ∑ k, (E k)ᴴ * E k = 1)
    {ρ : Matrix ((A × Y) × (C × R)) ((A × Y) × (C × R)) ℂ} (hρ : IsDensityMatrix ρ) :
    IsDensityMatrix (act E ρ) := by
  rw [act_eq]
  refine ⟨Matrix.posSemidef_sum _ fun k _ => hρ.1.mul_mul_conjTranspose_same _, ?_⟩
  rw [Matrix.trace_sum]
  simp_rw [Matrix.trace_mul_cycle (L E Y C R _)]
  rw [← Matrix.trace_sum, ← Finset.sum_mul, L_iso E hE, one_mul, hρ.2]

/-- The SSA state: Stinespring dilation of the `R`-marginal, reordered as `K × (C × (A' × Y))`. -/
def om (ρ : Matrix ((A × Y) × (C × R)) ((A × Y) × (C × R)) ℂ) :
    Matrix (Fin N × (C × (A' × Y))) (Fin N × (C × (A' × Y))) ℂ :=
  fun u v => ∑ r, ∑ a, ∑ b, E u.1 u.2.2.1 a * ρ ((a, u.2.2.2), (u.2.1, r)) ((b, v.2.2.2), (v.2.1, r)) *
    conj (E v.1 v.2.2.1 b)

def W1 (Y C : Type) : Matrix (Fin N × (C × (A' × Y))) ((A × Y) × C) ℂ :=
  Matrix.of fun u x => if x.1.2 = u.2.2.2 ∧ x.2 = u.2.1 then E u.1 u.2.2.1 x.1.1 else 0

def W2 (Y : Type) : Matrix (Fin N × (A' × Y)) (A × Y) ℂ :=
  Matrix.of fun u x => if x.2 = u.2.2 then E u.1 u.2.1 x.1 else 0

lemma W1_mul (g : (A × Y) × C → ℂ) (u : Fin N × (C × (A' × Y))) :
    ∑ x, W1 E Y C u x * g x = ∑ a, E u.1 u.2.2.1 a * g ((a, u.2.2.2), u.2.1) := by
  rw [Fintype.sum_prod_type, Finset.sum_comm, Finset.sum_eq_single u.2.1, Fintype.sum_prod_type,
    Finset.sum_comm, Finset.sum_eq_single u.2.2.2]
  · simp [W1]
  · intro y _ hy; refine Finset.sum_eq_zero fun a _ => ?_; simp [W1, hy]
  · simp
  · intro z _ hz; refine Finset.sum_eq_zero fun a _ => ?_; simp [W1, hz]
  · simp

lemma W1_mul' (g : (A × Y) × C → ℂ) (u : Fin N × (C × (A' × Y))) :
    ∑ x, star (W1 E Y C u x) * g x = ∑ a, star (E u.1 u.2.2.1 a) * g ((a, u.2.2.2), u.2.1) := by
  rw [Fintype.sum_prod_type, Finset.sum_comm, Finset.sum_eq_single u.2.1, Fintype.sum_prod_type,
    Finset.sum_comm, Finset.sum_eq_single u.2.2.2]
  · simp [W1]
  · intro y _ hy; refine Finset.sum_eq_zero fun a _ => ?_; simp [W1, hy]
  · simp
  · intro z _ hz; refine Finset.sum_eq_zero fun a _ => ?_; simp [W1, hz]
  · simp

lemma W2_mul (g : A × Y → ℂ) (u : Fin N × (A' × Y)) :
    ∑ x, W2 E Y u x * g x = ∑ a, E u.1 u.2.1 a * g (a, u.2.2) := by
  rw [Fintype.sum_prod_type, Finset.sum_comm, Finset.sum_eq_single u.2.2]
  · simp [W2]
  · intro y _ hy; refine Finset.sum_eq_zero fun a _ => ?_; simp [W2, hy]
  · simp

lemma W2_mul' (g : A × Y → ℂ) (u : Fin N × (A' × Y)) :
    ∑ x, star (W2 E Y u x) * g x = ∑ a, star (E u.1 u.2.1 a) * g (a, u.2.2) := by
  rw [Fintype.sum_prod_type, Finset.sum_comm, Finset.sum_eq_single u.2.2]
  · simp [W2]
  · intro y _ hy; refine Finset.sum_eq_zero fun a _ => ?_; simp [W2, hy]
  · simp

lemma W1_iso (hE : ∑ k, (E k)ᴴ * E k = 1) : (W1 E Y C)ᴴ * W1 E Y C = 1 := by
  ext u v
  have h := congrFun (congrFun hE u.1.1) v.1.1
  simp only [Matrix.sum_apply, Matrix.mul_apply, conjTranspose_apply] at h
  simp only [Matrix.mul_apply, conjTranspose_apply]
  rw [Fintype.sum_prod_type]
  have key : ∀ k, ∑ y : C × (A' × Y), star (W1 E Y C (k, y) u) * W1 E Y C (k, y) v =
      if u.1.2 = v.1.2 ∧ u.2 = v.2 then ∑ a, star (E k a u.1.1) * E k a v.1.1 else 0 := by
    intro k
    rw [Fintype.sum_prod_type, Finset.sum_eq_single u.2]
    · rw [Fintype.sum_prod_type, Finset.sum_comm, Finset.sum_eq_single u.1.2]
      · by_cases h1 : u.1.2 = v.1.2 <;> by_cases h2 : u.2 = v.2 <;> simp [W1, h1, h2, eq_comm]
      · intro y _ hy; refine Finset.sum_eq_zero fun a _ => ?_; simp [W1, Ne.symm hy]
      · simp
    · intro z _ hz; refine Finset.sum_eq_zero fun y _ => ?_
      simp [W1, Ne.symm hz]
    · simp
  simp_rw [key]
  by_cases hc : u.1.2 = v.1.2 ∧ u.2 = v.2
  · simp only [hc, and_self, if_true, h, Matrix.one_apply]
    obtain ⟨⟨a, y⟩, z⟩ := u; obtain ⟨⟨b, y'⟩, z'⟩ := v
    obtain ⟨h1, h2⟩ := hc; simp only at h1 h2; subst h1 h2
    simp [Prod.ext_iff]
  · simp only [hc, if_false, Finset.sum_const_zero, Matrix.one_apply]
    rw [if_neg]; rintro rfl; exact hc ⟨rfl, rfl⟩

lemma W2_iso (hE : ∑ k, (E k)ᴴ * E k = 1) : (W2 E Y)ᴴ * W2 E Y = 1 := by
  ext u v
  have h := congrFun (congrFun hE u.1) v.1
  simp only [Matrix.sum_apply, Matrix.mul_apply, conjTranspose_apply] at h
  simp only [Matrix.mul_apply, conjTranspose_apply]
  rw [Fintype.sum_prod_type]
  have key : ∀ k, ∑ y : A' × Y, star (W2 E Y (k, y) u) * W2 E Y (k, y) v =
      if u.2 = v.2 then ∑ a, star (E k a u.1) * E k a v.1 else 0 := by
    intro k
    rw [Fintype.sum_prod_type, Finset.sum_comm, Finset.sum_eq_single u.2]
    · by_cases h1 : u.2 = v.2 <;> simp [W2, h1, eq_comm]
    · intro y _ hy; refine Finset.sum_eq_zero fun a _ => ?_; simp [W2, Ne.symm hy]
    · simp
  simp_rw [key]
  by_cases hc : u.2 = v.2
  · simp only [hc, if_true, h, Matrix.one_apply]
    obtain ⟨a, y⟩ := u; obtain ⟨b, y'⟩ := v
    simp only at hc; subst hc
    simp [Prod.ext_iff]
  · simp only [hc, if_false, Finset.sum_const_zero, Matrix.one_apply]
    rw [if_neg]; rintro rfl; exact hc rfl

lemma om_eq (ρ : Matrix ((A × Y) × (C × R)) ((A × Y) × (C × R)) ℂ) :
    om E ρ = W1 E Y C * M1 ρ * (W1 E Y C)ᴴ := by
  ext u v
  simp only [Matrix.mul_apply, conjTranspose_apply]
  simp_rw [W1_mul E (fun x => M1 ρ x _), Finset.sum_mul]
  rw [Finset.sum_comm]
  have : ∀ i, ∑ x, E u.1 u.2.2.1 i * M1 ρ ((i, u.2.2.2), u.2.1) x * star (W1 E Y C v x) =
      ∑ b, star (E v.1 v.2.2.1 b) * (E u.1 u.2.2.1 i * M1 ρ ((i, u.2.2.2), u.2.1) ((b, v.2.2.2), v.2.1)) := by
    intro i
    simp_rw [mul_comm _ (star (W1 E Y C v _))]
    exact W1_mul' E (fun x => E u.1 u.2.2.1 i * M1 ρ ((i, u.2.2.2), u.2.1) x) v
  simp_rw [this]
  simp only [om, M1, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun r _ => ?_
  simp only [RCLike.star_def]; ring

lemma rm_om1 (ρ : Matrix ((A × Y) × (C × R)) ((A × Y) × (C × R)) ℂ) :
    redistributionMarginal (om E ρ) (fun p => (p.1, p.2.2)) (fun p => p.2.1) =
      W2 E Y * M2 ρ * (W2 E Y)ᴴ := by
  funext u v
  rw [rm_e (om E ρ) (((Equiv.refl (Fin N)).prodCongr (Equiv.prodComm C (A' × Y))).trans
    (Equiv.prodAssoc _ _ _).symm) (fun p => (p.1, p.2.2)) (fun p => p.2.1) (fun _ => rfl) (fun _ => rfl)]
  simp only [Matrix.mul_apply, conjTranspose_apply]
  simp_rw [W2_mul E (fun x => M2 ρ x _), Finset.sum_mul]
  rw [Finset.sum_comm (s := (Finset.univ : Finset (A × Y)))]
  have : ∀ i, ∑ x, E u.1 u.2.1 i * M2 ρ (i, u.2.2) x * star (W2 E Y v x) =
      ∑ b, star (E v.1 v.2.1 b) * (E u.1 u.2.1 i * M2 ρ (i, u.2.2) (b, v.2.2)) := by
    intro i
    simp_rw [mul_comm _ (star (W2 E Y v _))]
    exact W2_mul' E (fun x => E u.1 u.2.1 i * M2 ρ (i, u.2.2) x) v
  simp_rw [this]
  simp only [om, M2, Finset.mul_sum, Equiv.trans_apply, Equiv.prodAssoc_symm_apply,
    Equiv.prodCongr_symm, Equiv.prodCongr_apply, Equiv.refl_symm, Equiv.refl_apply,
    Equiv.prodComm_symm, Equiv.prodComm_apply, Prod.map, Prod.swap, Equiv.symm_trans_apply,
    Equiv.symm_symm, Equiv.prodAssoc_apply]
  rw [sum4 (fun x x_1 x_2 i => star (E v.1 v.2.1 x_1) * (E u.1 u.2.1 x * ρ ((x, u.2.2), x_2, i) ((x_1, v.2.2), x_2, i)))]
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
    Finset.sum_congr rfl fun _ _ => ?_
  simp only [RCLike.star_def]; ring

lemma rm_om2 (ρ : Matrix ((A × Y) × (C × R)) ((A × Y) × (C × R)) ℂ) :
    redistributionMarginal (om E ρ) (fun p => p.2) (fun p => p.1) =
      (M1 (act E ρ)).submatrix (Equiv.prodComm C (A' × Y)) (Equiv.prodComm C (A' × Y)) := by
  funext u v
  rw [rm_e (om E ρ) (Equiv.prodComm (Fin N) (C × (A' × Y))) (fun p => p.2) (fun p => p.1)
    (fun _ => rfl) (fun _ => rfl)]
  simp only [om, M1, act, Matrix.submatrix_apply, Equiv.prodComm_symm, Equiv.prodComm_apply, Prod.swap]
  rw [Finset.sum_comm]

lemma rm_om3 (ρ : Matrix ((A × Y) × (C × R)) ((A × Y) × (C × R)) ℂ) :
    redistributionMarginal (om E ρ) (fun p => p.2.2) (fun p => (p.1, p.2.1)) = M2 (act E ρ) := by
  funext u v
  rw [rm_e (om E ρ) ((Equiv.prodAssoc _ _ _).symm.trans (Equiv.prodComm _ _)) (fun p => p.2.2)
    (fun p => (p.1, p.2.1)) (fun _ => rfl) (fun _ => rfl)]
  simp only [om, M2, act, Fintype.sum_prod_type, Equiv.symm_trans_apply, Equiv.prodComm_symm,
    Equiv.prodComm_apply, Prod.swap, Equiv.symm_symm, Equiv.prodAssoc_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Finset.sum_comm]

theorem dpi [Nonempty A] [Nonempty A'] [Nonempty Y] [Nonempty C] [Nonempty R]
    (hE : ∑ k, (E k)ᴴ * E k = 1) {ρ : Matrix ((A × Y) × (C × R)) ((A × Y) × (C × R)) ℂ}
    (hρ : IsDensityMatrix ρ) :
    vnEntropy (M2 (act E ρ)) - vnEntropy (M1 (act E ρ)) ≤ vnEntropy (M2 ρ) - vnEntropy (M1 ρ) := by
  have hN : Nonempty (Fin N) := by
    rcases N with _ | N
    · exfalso
      obtain ⟨a⟩ := ‹Nonempty A›
      have := congrFun (congrFun hE a) a
      simp at this
    · exact ⟨0⟩
  have hM1 : ∀ {B : Type} [Fintype B] {X : Matrix ((B × Y) × (C × R)) ((B × Y) × (C × R)) ℂ},
      IsDensityMatrix X → IsDensityMatrix (M1 X) := fun {B} _ {X} hX => by
    rw [M1_rm]
    exact X4C1.rm_density _ _ _ (fun x y h1 h2 => by
      obtain ⟨x1, x2, x3⟩ := x; obtain ⟨y1, y2, y3⟩ := y
      simp only [Prod.mk.injEq] at h1 h2 ⊢; exact ⟨h1.1, h1.2, h2⟩) hX
  have hM2 : IsDensityMatrix (M2 ρ) := by
    rw [M2_rm]
    exact X4C1.rm_density _ _ _ (fun x y h1 h2 => Prod.ext h1 h2) hρ
  have hσ := act_density E hE hρ
  have hω : IsDensityMatrix (om E ρ) := by
    rw [om_eq]
    refine ⟨(hM1 hρ).1.mul_mul_conjTranspose_same _, ?_⟩
    rw [Matrix.trace_mul_cycle, W1_iso E hE, Matrix.one_mul, (hM1 hρ).2]
  have h := strongSubadditivity (om E ρ) hω
  simp only [subsystemEntropy] at h
  rw [rm_om1, rm_om2, rm_om3, om_eq] at h
  have key : 0 ≤ vnEntropy (W2 E Y * M2 ρ * (W2 E Y)ᴴ) +
      vnEntropy ((M1 (act E ρ)).submatrix (Equiv.prodComm C (A' × Y)) (Equiv.prodComm C (A' × Y))) -
      vnEntropy (M2 (act E ρ)) - vnEntropy (W1 E Y C * M1 ρ * (W1 E Y C)ᴴ) := by
    convert h
  have e1 : vnEntropy (W1 E Y C * M1 ρ * (W1 E Y C)ᴴ) = vnEntropy (M1 ρ) :=
    X4ER.vn_conj_iso (hM1 hρ).1 _ (W1_iso E hE)
  have e2 : vnEntropy (W2 E Y * M2 ρ * (W2 E Y)ᴴ) = vnEntropy (M2 ρ) :=
    X4ER.vn_conj_iso hM2.1 _ (W2_iso E hE)
  have e3 : vnEntropy ((M1 (act E ρ)).submatrix (Equiv.prodComm C (A' × Y))
      (Equiv.prodComm C (A' × Y))) = vnEntropy (M1 (act E ρ)) :=
    X4C1.vn_reindex _ (hM1 hσ).1.isHermitian
  linarith

end X4DPI

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

end X4ES


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

end X4EP

end

-- ===== PEA =====

/-! Concavity of conditional entropy (both conditionings) from strong subadditivity. -/

noncomputable section

namespace X4PE
open Matrix Real QAlgorithms
open scoped Matrix ComplexConjugate ComplexOrder

section
variable {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

def KL (a : A) : Matrix B (A × B) ℂ := Matrix.of fun b p => if p = (a, b) then 1 else 0
def KR (b : B) : Matrix A (A × B) ℂ := Matrix.of fun a p => if p = (a, b) then 1 else 0

lemma tl_kraus (ω : Matrix (A × B) (A × B) ℂ) : traceLeft ω = ∑ a, (KL (B := B) a : Matrix B (A × B) ℂ) * ω * (KL (B := B) a : Matrix B (A × B) ℂ)ᴴ := by
  ext b b'
  simp [traceLeft, KL, Matrix.mul_apply, Matrix.sum_apply, conjTranspose_apply]

lemma tr_kraus (ω : Matrix (A × B) (A × B) ℂ) : traceRight ω = ∑ b, (KR (A := A) b : Matrix A (A × B) ℂ) * ω * (KR (A := A) b : Matrix A (A × B) ℂ)ᴴ := by
  ext a a'
  simp [traceRight, KR, Matrix.mul_apply, Matrix.sum_apply, conjTranspose_apply]

lemma tl_psd {ω : Matrix (A × B) (A × B) ℂ} (h : ω.PosSemidef) : (traceLeft ω).PosSemidef := by
  rw [tl_kraus]; exact Matrix.posSemidef_sum _ fun a _ => h.mul_mul_conjTranspose_same _

lemma tr_psd {ω : Matrix (A × B) (A × B) ℂ} (h : ω.PosSemidef) : (traceRight ω).PosSemidef := by
  rw [tr_kraus]; exact Matrix.posSemidef_sum _ fun a _ => h.mul_mul_conjTranspose_same _

lemma tr_trace (ω : Matrix (A × B) (A × B) ℂ) : (traceRight ω).trace = ω.trace := by
  simp only [Matrix.trace, traceRight, Matrix.diag, Matrix.of_apply]
  rw [← Fintype.sum_prod_type']

end

section
variable {M R B : Type} [Fintype M] [DecidableEq M] [Nonempty M] [Fintype R] [DecidableEq R]
  [Nonempty R] [Fintype B] [DecidableEq B] [Nonempty B]

end

end X4PE

end

-- ===== SRA =====

/-! Claimed50.P08 sum-rate redundancy: cq entropy bookkeeping plus data processing of
`H(W|·)` under the Hadamard degrading map (measure Bob's basis, prepare `psi_x`). -/

noncomputable section

namespace X4SR
open Matrix QAlgorithms
open QAlgorithms.Papers.Independent.Claimed50.P08
open QAlgorithms.Papers.Independent.Information100.P21 (Op)
open scoped Matrix ComplexConjugate ComplexOrder BigOperators

lemma unit_c {ι : Type} [Fintype ι] (ψ : EuclideanSpace ℂ ι) (h : ‖ψ‖ = 1) :
    ∑ k, ψ k * conj (ψ k) = 1 := by
  have h2 : ∑ i, ‖ψ i‖ ^ 2 = 1 := by rw [← EuclideanSpace.norm_sq_eq, h, one_pow]
  have : ∑ k, ψ k * conj (ψ k) = ((∑ k, ‖ψ k‖ ^ 2 : ℝ) : ℂ) := by
    push_cast
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]; push_cast; ring
  rw [this, h2]; simp

variable {a b c : ℕ} (H : HadamardData a b c)

lemma iso : (inputIsometry H)ᴴ * inputIsometry H = 1 := by
  have hp := H.povm
  ext i j
  have hij := congrFun (congrFun hp i) j
  simp only [Matrix.sum_apply, pureDensity, Matrix.of_apply] at hij
  rw [← hij]
  simp only [Matrix.mul_apply, conjTranspose_apply, inputIsometry, Fintype.sum_prod_type,
    star_mul', RCLike.star_def, Complex.conj_conj]
  refine Finset.sum_congr rfl fun x _ => ?_
  have hu := unit_c (H.psi x) (H.unit x)
  calc ∑ k, conj (H.psi x k) * H.phi x i * (H.psi x k * conj (H.phi x j))
      = (∑ k, H.psi x k * conj (H.psi x k)) * (H.phi x i * conj (H.phi x j)) := by
        rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun k _ => by ring
    _ = _ := by rw [hu, one_mul]

lemma bob_psd {ρ : Op (BroadcastRegister a)} (h : ρ.PosSemidef) : (bobChannel H ρ).PosSemidef := by
  simp only [bobChannel, Function.comp, hadamardChannel, conjSuperop]
  exact X4PE.tr_psd (h.mul_mul_conjTranspose_same _)

lemma bob_trace (ρ : Op (BroadcastRegister a)) : (bobChannel H ρ).trace = ρ.trace := by
  simp only [bobChannel, Function.comp, hadamardChannel, conjSuperop]
  rw [X4PE.tr_trace, Matrix.trace_mul_cycle, iso, Matrix.one_mul]

lemma bob_density {ρ : Op (BroadcastRegister a)} (h : IsDensityMatrix ρ) :
    IsDensityMatrix (bobChannel H ρ) := ⟨bob_psd H h.1, by rw [bob_trace, h.2]⟩

lemma had_apply (ρ : Op (BroadcastRegister a)) (x y : BroadcastRegister b) (k l : BroadcastRegister c) :
    hadamardChannel H ρ (x, k) (y, l) =
      H.psi x k * conj (H.psi y l) * inputCoefficient H ρ x y := by
  simp only [hadamardChannel, conjSuperop, inputIsometry, inputCoefficient, Matrix.mul_apply,
    conjTranspose_apply, star_mul', RCLike.star_def, Complex.conj_conj, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

lemma bob_diag (ρ : Op (BroadcastRegister a)) (x : BroadcastRegister b) :
    bobChannel H ρ x x = inputCoefficient H ρ x x := by
  simp only [bobChannel, Function.comp, traceRight, Matrix.of_apply, had_apply]
  rw [← Finset.sum_mul, unit_c _ (H.unit x), one_mul]

lemma charlie_eq (ρ : Op (BroadcastRegister a)) (k l : BroadcastRegister c) :
    charlieChannel H ρ k l = ∑ x, H.psi x k * bobChannel H ρ x x * conj (H.psi x l) := by
  simp only [charlieChannel, Function.comp, traceLeft, Matrix.of_apply, had_apply, bob_diag]
  exact Finset.sum_congr rfl fun x _ => by ring

/-- Kraus operators of the degrading map. -/
def E (x : Fin (b + 1)) : Matrix (Fin (c + 1)) (Fin (b + 1)) ℂ :=
  fun k u => if u = x then H.psi x k else 0

lemma E_kraus : ∑ x, (E H x)ᴴ * E H x = 1 := by
  ext u v
  simp only [Matrix.sum_apply, Matrix.mul_apply, conjTranspose_apply, E, RCLike.star_def]
  rw [Finset.sum_eq_single u]
  · by_cases huv : u = v
    · subst huv
      simp only [if_true, Matrix.one_apply_eq]
      rw [← unit_c _ (H.unit u)]
      exact Finset.sum_congr rfl fun k _ => by ring
    · simp [Ne.symm huv, huv]
  · intro x _ hx; simp [Ne.symm hx]
  · simp

end X4SR

end

-- ===== SRB =====

noncomputable section

namespace X4SR
open Matrix QAlgorithms
open QAlgorithms.Papers.Independent.Claimed50.P08
open QAlgorithms.Papers.Independent.Information100.P21 (Op)
open scoped Matrix ComplexConjugate ComplexOrder BigOperators

/-- single-block embedding. -/
def P {ι M : Type} [DecidableEq ι] [DecidableEq M] (m : M) : Matrix (M × ι) ι ℂ :=
  fun x j => if x.1 = m ∧ x.2 = j then 1 else 0

lemma cq_eq {ι M : Type} [Fintype ι] [DecidableEq ι] [Fintype M] [DecidableEq M]
    (σ : M → Matrix ι ι ℂ) : cqBlocks σ = ∑ m, P (ι := ι) m * σ m * (P (ι := ι) m)ᴴ := by
  ext x y
  rw [Matrix.sum_apply, Finset.sum_eq_single x.1]
  · simp only [Matrix.mul_apply, conjTranspose_apply, P, RCLike.star_def, cqBlocks]
    rw [Finset.sum_eq_single y.2]
    · rw [Finset.sum_eq_single x.2]
      · by_cases h : x.1 = y.1
        · simp [h]
        · simp only [h, if_false]; simp [h, Ne.symm h]
      · intro j _ hj; simp [Ne.symm hj]
      · simp
    · intro j _ hj; simp [Ne.symm hj]
    · simp
  · intro m _ hm
    simp [Matrix.mul_apply, P, Ne.symm hm]
  · simp

lemma cq_psd {ι M : Type} [Fintype ι] [DecidableEq ι] [Fintype M] [DecidableEq M]
    (σ : M → Matrix ι ι ℂ) (h : ∀ m, (σ m).PosSemidef) : (cqBlocks σ).PosSemidef := by
  rw [cq_eq]; exact Matrix.posSemidef_sum _ fun m _ => (h m).mul_mul_conjTranspose_same _

lemma cq_ent {ι M : Type} [Fintype ι] [DecidableEq ι] [Fintype M] [DecidableEq M]
    (q : M → ℝ) (hq : ∀ m, 0 ≤ q m) (τ : M → Matrix ι ι ℂ) (hτ : ∀ m, IsDensityMatrix (τ m)) :
    vnEntropy (cqBlocks fun m => (q m : ℂ) • τ m) =
      ∑ m, q m * vnEntropy (τ m) + classicalEntropy q := by
  have h1 : vnEntropy (cqBlocks fun m => (q m : ℂ) • τ m) =
      ∑ m, vnEntropy ((q m : ℂ) • τ m) :=
    X4LE.vn_blk _ fun m => (hτ m).1.smul (Complex.zero_le_real.mpr (hq m))
  rw [h1, classicalEntropy, X4LE.vn_diag, ← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [X4ER.vn_smul0 (hτ m).1.1 (hq m), (hτ m).2]
  simp only [Complex.one_re, mul_one]; ring

lemma sum2_single {ι : Type} [Fintype ι] [DecidableEq ι] (k : ι) (α β : ℂ) (F : ι → ι → ℂ) :
    ∑ a', ∑ b', (if a' = k then α else 0) * F a' b' * conj (if b' = k then β else 0) =
      α * F k k * conj β := by
  rw [Finset.sum_eq_single k (fun x _ hx => by simp [hx]) (by simp)]
  rw [Finset.sum_eq_single k (fun x _ hx => by simp [hx]) (by simp)]
  simp

variable {a b c w z : ℕ} (H : HadamardData a b c) (S : ClassicalEnsemble w z a)

/-- Bob's conditional (on `W`) output blocks. -/
def X (i : Fin (w + 1)) : Op (Fin (b + 1)) :=
  ∑ j, (S.probability.val (i, j) : ℂ) • bobChannel H (S.state j)

/-- Charlie's conditional output blocks. -/
def Y (i : Fin (w + 1)) : Op (Fin (c + 1)) :=
  ∑ j, (S.probability.val (i, j) : ℂ) • charlieChannel H (S.state j)

/-- cq state on `(B × Unit) × (W × Unit)`. -/
def rr : Matrix ((Fin (b + 1) × Unit) × (Fin (w + 1) × Unit))
    ((Fin (b + 1) × Unit) × (Fin (w + 1) × Unit)) ℂ :=
  fun u v => if u.2.1 = v.2.1 then X H S u.2.1 u.1.1 v.1.1 else 0

lemma X_psd (i : Fin (w + 1)) : (X H S i).PosSemidef :=
  Matrix.posSemidef_sum _ fun j _ =>
    (bob_psd H (S.density j).1).smul (Complex.zero_le_real.mpr (S.probability.2.1 _))

lemma rr_density : IsDensityMatrix (rr H S) := by
  constructor
  · have : rr H S = (cqBlocks (X H S)).submatrix (fun u => (u.2.1, u.1.1)) (fun u => (u.2.1, u.1.1)) := by
      ext u v; simp [rr, cqBlocks]
    rw [this]; exact (cq_psd _ (X_psd H S)).submatrix _
  · simp only [Matrix.trace, rr, Matrix.diag, if_true, Fintype.sum_prod_type, Finset.univ_unique,
      Finset.sum_singleton]
    rw [Finset.sum_comm]
    simp only [X, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
    have : ∀ i : Fin (w + 1), ∑ x, ∑ j, (S.probability.val (i, j) : ℂ) * bobChannel H (S.state j) x x =
        ∑ j, (S.probability.val (i, j) : ℂ) := fun i => by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [← Finset.mul_sum]
      have := bob_trace H (S.state j)
      rw [(S.density j).2] at this
      simp only [Matrix.trace, Matrix.diag] at this
      rw [this, mul_one]
    simp only [this]
    rw [← Fintype.sum_prod_type' (fun i j => (S.probability.val (i, j) : ℂ))]
    exact_mod_cast S.probability.2.2

lemma act_rr : X4DPI.act (E H) (rr H S) =
    fun u v => if u.2.1 = v.2.1 then Y H S u.2.1 u.1.1 v.1.1 else 0 := by
  ext u v
  simp only [X4DPI.act]
  have hk : ∀ k, ∑ a', ∑ b', E H k u.1.1 a' * rr H S ((a', u.1.2), u.2) ((b', v.1.2), v.2) *
      conj (E H k v.1.1 b') =
      H.psi k u.1.1 * rr H S ((k, u.1.2), u.2) ((k, v.1.2), v.2) * conj (H.psi k v.1.1) := fun k => by
    simp only [E]
    exact sum2_single k _ _ (fun a' b' => rr H S ((a', u.1.2), u.2) ((b', v.1.2), v.2))
  rw [Finset.sum_congr rfl fun k _ => hk k]
  simp only [rr]
  by_cases h : u.2.1 = v.2.1
  · simp only [h, if_true]
    simp only [Y, X, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, charlie_eq,
      Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun x _ => by ring
  · simp [h]

end X4SR

end

-- ===== SRSol =====

noncomputable section

namespace X4SR
open Matrix QAlgorithms
open QAlgorithms.Papers.Independent.Claimed50.P08
open QAlgorithms.Papers.Independent.Information100.P21 (Op)
open scoped Matrix ComplexConjugate ComplexOrder BigOperators

lemma charlie_psd {a b c : ℕ} (H : HadamardData a b c) {ρ : Op (BroadcastRegister a)}
    (h : ρ.PosSemidef) : (charlieChannel H ρ).PosSemidef := by
  simp only [charlieChannel, Function.comp, hadamardChannel, conjSuperop]
  exact X4PE.tl_psd (h.mul_mul_conjTranspose_same _)

/-- generic cq embedding on `(D × Unit) × (W × Unit)`. -/
def R {D W : Type} [DecidableEq W] (Z : W → Matrix D D ℂ) :
    Matrix ((D × Unit) × (W × Unit)) ((D × Unit) × (W × Unit)) ℂ :=
  fun u v => if u.2.1 = v.2.1 then Z u.2.1 u.1.1 v.1.1 else 0

lemma ent_M1 {D W : Type} [Fintype D] [DecidableEq D] [Fintype W] [DecidableEq W]
    (Z : W → Matrix D D ℂ) (hZ : ∀ i, (Z i).PosSemidef) (d : DecidableEq ((D × Unit) × W)) :
    @vnEntropy _ _ d (X4DPI.M1 (R Z)) = vnEntropy (cqBlocks Z) := by
  obtain rfl : d = instDecidableEqProd := Subsingleton.elim _ _
  let e : (D × Unit) × W ≃ W × D :=
    (Equiv.prodComm _ _).trans (Equiv.prodCongr (Equiv.refl _) (Equiv.prodPUnit _))
  have : X4DPI.M1 (R Z) = (cqBlocks Z).submatrix e e := by
    ext u v; simp [X4DPI.M1, R, cqBlocks, e]
  rw [this]
  exact X4C1.vn_reindex e (cq_psd Z hZ).1

lemma ent_M2 {D W : Type} [Fintype D] [DecidableEq D] [Fintype W] [DecidableEq W]
    (Z : W → Matrix D D ℂ) (hZ : ∀ i, (Z i).PosSemidef) (d : DecidableEq (D × Unit)) :
    @vnEntropy _ _ d (X4DPI.M2 (R Z)) = vnEntropy (∑ i, Z i) := by
  obtain rfl : d = instDecidableEqProd := Subsingleton.elim _ _
  let e : D × Unit ≃ D := Equiv.prodPUnit _
  have : X4DPI.M2 (R Z) = (∑ i, Z i).submatrix e e := by
    ext u v; simp [X4DPI.M2, R, e, Matrix.sum_apply, Fintype.sum_prod_type]
  rw [this]
  exact X4C1.vn_reindex e (Matrix.posSemidef_sum _ fun i _ => hZ i).1

lemma act_rr' {a b c w z : ℕ} (H : HadamardData a b c) (S : ClassicalEnsemble w z a) :
    X4DPI.act (E H) (rr H S) = R (Y H S) := act_rr H S

lemma rr_eq {a b c w z : ℕ} (H : HadamardData a b c) (S : ClassicalEnsemble w z a) :
    rr H S = R (X H S) := rfl

end X4SR

open QAlgorithms
open scoped ComplexOrder
open QAlgorithms.Papers.Independent.Claimed50.P08 in
theorem solution {a b c w z : ℕ} (H : HadamardData a b c)
    (S : ClassicalEnsemble w z a) (RB RC : ℝ) (hB : 0 ≤ RB) (hC : 0 ≤ RC)
    (bob_bound : RB ≤ classicalConditionalInfo S (bobChannel H))
    (charlie_bound : RC ≤ classicalLayerInfo S (charlieChannel H)) :
    RB + RC ≤ classicalTotalInfo S (bobChannel H) := by
  have hd := X4DPI.dpi (X4SR.E H) (by convert X4SR.E_kraus H) (X4SR.rr_density H S)
  have hY : ∀ i, (X4SR.Y H S i).PosSemidef := fun i =>
    Matrix.posSemidef_sum _ fun j _ =>
      (X4SR.charlie_psd H (S.density j).1).smul (Complex.zero_le_real.mpr (S.probability.2.1 _))
  rw [X4SR.act_rr', X4SR.rr_eq] at hd
  rw [X4SR.ent_M1 _ (X4SR.X_psd H S), X4SR.ent_M2 _ (X4SR.X_psd H S), X4SR.ent_M1 _ hY,
    X4SR.ent_M2 _ hY] at hd
  have eX : X4SR.X H S = fun i => ∑ j, (S.probability.val (i, j) : ℂ) • bobChannel H (S.state j) := rfl
  have eY : X4SR.Y H S = fun i => ∑ j, (S.probability.val (i, j) : ℂ) • charlieChannel H (S.state j) := rfl
  rw [eX, eY] at hd
  have hp0 : ∀ ij, 0 ≤ S.probability.val ij := S.probability.2.1
  have hτ : ∀ j, IsDensityMatrix (bobChannel H (S.state j)) := fun j => X4SR.bob_density H (S.density j)
  have hWZB := X4SR.cq_ent S.probability.val hp0 (fun ij => bobChannel H (S.state ij.2)) (fun ij => hτ ij.2)
  have hZB := X4SR.cq_ent (fun j => ∑ i, S.probability.val (i, j)) (fun j => Finset.sum_nonneg fun i _ => hp0 _)
    (fun j => bobChannel H (S.state j)) hτ
  have hsum : ∑ ij : Fin (w + 1) × Fin (z + 1), S.probability.val ij * vnEntropy (bobChannel H (S.state ij.2)) =
      ∑ j, (∑ i, S.probability.val (i, j)) * vnEntropy (bobChannel H (S.state j)) := by
    rw [Fintype.sum_prod_type, Finset.sum_comm]
    exact Finset.sum_congr rfl fun j _ => by rw [Finset.sum_mul]
  have havg : ∑ j, ((∑ i, S.probability.val (i, j) : ℝ) : ℂ) • bobChannel H (S.state j) =
      ∑ i, ∑ j, (S.probability.val (i, j) : ℂ) • bobChannel H (S.state j) := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun j _ => by push_cast; rw [Finset.sum_smul]
  have hv := congrArg vnEntropy havg
  simp only [classicalConditionalInfo, classicalLayerInfo, classicalTotalInfo] at bob_bound charlie_bound ⊢
  linarith

