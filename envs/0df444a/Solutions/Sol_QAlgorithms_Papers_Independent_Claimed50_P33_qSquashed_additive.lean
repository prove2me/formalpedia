-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Claimed50.P33.qSquashed_additive
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T09:24:06.584988+00:00
-- url     : https://prove2.me/submissions/24706119-089f-4a6a-8719-c5754ccc4f99

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P33
import Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P20_strongSubadditivity
import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P41
import Definitions.Def_QAlgorithms_Defs_QuantumInformation
import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P42
import Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P33_proposition1

-- ===== C1A =====

/-! Strong subadditivity for disjoint register sets (Claimed50.P33 conventions). -/

noncomputable section

namespace X4C1
open Matrix QAlgorithms
open QAlgorithms.Papers.Independent.Claimed50.P33
open QAlgorithms.Papers.Independent.Gap48.P20 (redistributionMarginal subsystemEntropy strongSubadditivity)
open scoped Matrix ComplexConjugate ComplexOrder

attribute [local instance] Classical.propDecidable Classical.decEq

lemma rm_comp {X K F K' F' : Type*} [Fintype X] [Fintype K] (ρ : Matrix X X ℂ)
    (k : X → K) (f : X → F) (k' : K → K') (f' : K → F') :
    redistributionMarginal (redistributionMarginal ρ k f) k' f' =
      redistributionMarginal ρ (k' ∘ k) (fun x => (f' (k x), f x)) := by
  ext a b
  simp only [redistributionMarginal]
  have h1 : ∀ u v : K, (if k' u = a ∧ k' v = b ∧ f' u = f' v then
      ∑ x : X, ∑ y : X, (if k x = u ∧ k y = v ∧ f x = f y then ρ x y else 0) else 0) =
      ∑ x : X, ∑ y : X, if k x = u then (if k y = v then
        (if k' (k x) = a ∧ k' (k y) = b ∧ (f' (k x), f x) = (f' (k y), f y) then ρ x y else 0)
        else 0) else 0 := by
    intro u v
    split_ifs with h
    · refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
      by_cases hx : k x = u <;> by_cases hy : k y = v <;> simp [hx, hy, h, Prod.ext_iff]
    · symm; refine Finset.sum_eq_zero fun x _ => Finset.sum_eq_zero fun y _ => ?_
      by_cases hx : k x = u <;> by_cases hy : k y = v <;> simp only [hx, hy, if_false, if_true]
      subst hx hy
      rw [if_neg]; intro h'; apply h
      exact ⟨h'.1, h'.2.1, (Prod.ext_iff.1 h'.2.2).1⟩
  simp_rw [h1]
  rw [Finset.sum_comm]
  simp_rw [Finset.sum_comm (s := (Finset.univ : Finset K)) (t := (Finset.univ : Finset X))]
  simp [Finset.sum_ite_eq', Function.comp]

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

/-- Restriction to a register set. -/
def restr (s : Finset (Fin n)) (x : RegisterBasis D) : SubBasis D s := fun i => x i.1

/-- Restriction to the complement of a register set. -/
def restrC (s : Finset (Fin n)) (x : RegisterBasis D) : (i : {i : Fin n // i ∉ s}) → D i.1 :=
  fun i => x i.1

lemma restr_eq {s : Finset (Fin n)} {x y : RegisterBasis D} :
    restr s x = restr s y ↔ ∀ i ∈ s, x i = y i := by
  simp [restr, funext_iff]

lemma restr_eq' {s : Finset (Fin n)} {x : RegisterBasis D} {c : SubBasis D s} :
    restr s x = c ↔ ∀ i (hi : i ∈ s), x i = c ⟨i, hi⟩ := by
  simp [restr, funext_iff]

lemma restrC_eq {s : Finset (Fin n)} {x y : RegisterBasis D} :
    restrC s x = restrC s y ↔ ∀ i, i ∉ s → x i = y i := by
  simp [restrC, funext_iff]

lemma reg_rm {E : Type} [Fintype E] (ρ : Matrix (RegisterBasis D × E) (RegisterBasis D × E) ℂ)
    (s : Finset (Fin n)) :
    registerMarginal ρ s = redistributionMarginal ρ (fun x => (restr s x.1, x.2))
      (fun x => restrC s x.1) := by
  ext a b
  simp only [registerMarginal, redistributionMarginal, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.sum_eq_single a.2]
  · refine Finset.sum_congr rfl fun y _ => ?_
    rw [Finset.sum_eq_single b.2]
    · congr 1
      apply propext
      simp only [Prod.ext_iff, restr_eq', restrC_eq, and_true]
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨fun i hi => (h1 i hi).1, fun i hi => (h1 i hi).2, h2⟩
      · rintro ⟨h1, h2, h3⟩
        exact ⟨fun i hi => ⟨h1 i hi, h2 i hi⟩, h3⟩
    · intro e _ he; rw [if_neg]; intro h; exact he (Prod.ext_iff.1 h.2.1).2
    · simp
  · intro e _ he; refine Finset.sum_eq_zero fun y _ => Finset.sum_eq_zero fun e' _ => ?_
    rw [if_neg]; intro h; exact he (Prod.ext_iff.1 h.1).2
  · simp

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

end X4ZE

end

-- ===== LEA =====

/-! Generic von Neumann entropy facts: scaling, orthogonal rank-one sums, `S(Σσ) ≤ ΣS(σ)`
for unnormalized PSD terms, and concavity `Σ (S(σ_m) + p_m log p_m) ≤ S(Σσ)`. -/

noncomputable section

namespace X4LE
open Matrix Real QAlgorithms
open scoped Matrix ComplexConjugate ComplexOrder

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

end X4LE

end

-- ===== ERA =====

/-! Generic entropy facts: scaling with `c ≥ 0`, additivity on orthogonal PSD summands,
invariance under isometric conjugation, pure states, and the qubit bound `S ≤ 1`. -/

noncomputable section

namespace X4ER
open Matrix Real QAlgorithms
open scoped Matrix ComplexConjugate ComplexOrder

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

end X4DPI

end

-- ===== RMC =====

/-! Entropy of a redistribution marginal depends only on the two partitions
(`keep` and `forget` level sets), not on the labels; conjugation by a partial isometry
that is isometric on the support preserves entropy. -/

noncomputable section

namespace X4RM
open Matrix QAlgorithms
open QAlgorithms.Papers.Independent.Gap48.P20 (redistributionMarginal subsystemEntropy strongSubadditivity)
open scoped Matrix ComplexConjugate ComplexOrder

attribute [local instance] Classical.propDecidable Classical.decEq

lemma vn_conj_piso {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    {X : Matrix ι ι ℂ} (hX : X.PosSemidef) (J : Matrix κ ι ℂ) (hJ : Jᴴ * J * X = X) :
    vnEntropy (J * X * Jᴴ) = vnEntropy X := by
  set V : Matrix ι ι ℂ := Matrix.of fun a k => X4LE.amp hX k a
  have hV : X = V * Vᴴ := by
    conv_lhs => rw [X4LE.amp_decomp hX]
    ext a b; simp [V, Matrix.mul_apply, Matrix.sum_apply, conjTranspose_apply]
  set P := Jᴴ * J with hPdef
  have hP : Pᴴ = P := by simp [hPdef, conjTranspose_mul]
  have hXP : X * P = X := by
    have := congrArg conjTranspose hJ
    rwa [conjTranspose_mul, hX.1.eq, hP] at this
  have hPV : P * V = V := by
    have hW : (P * V - V) * (P * V - V)ᴴ = 0 := by
      have e1 : P * V * (P * V)ᴴ = X := by
        rw [conjTranspose_mul, hP, Matrix.mul_assoc, ← Matrix.mul_assoc V, ← hV,
          ← Matrix.mul_assoc, hJ, hXP]
      have e2 : P * V * Vᴴ = X := by rw [Matrix.mul_assoc, ← hV, hJ]
      have e3 : V * (P * V)ᴴ = X := by
        rw [conjTranspose_mul, hP, ← Matrix.mul_assoc, ← hV, hXP]
      rw [conjTranspose_sub, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub, e1, e2, e3, ← hV]
      abel
    exact sub_eq_zero.1 (self_mul_conjTranspose_eq_zero.1 hW)
  have h1 : J * X * Jᴴ = (J * V) * (J * V)ᴴ := by
    rw [hV, conjTranspose_mul]; simp only [Matrix.mul_assoc]
  have h2 : (J * V)ᴴ * (J * V) = Vᴴ * V := by
    rw [conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc Jᴴ, ← hPdef, hPV]
  rw [h1, X4KF.x4_ent_swap, h2, ← X4KF.x4_ent_swap, ← hV]

lemma rm_psd {X K F : Type*} [Fintype X] [Fintype K] [Fintype F] {Z : Matrix X X ℂ}
    (hZ : Z.PosSemidef) (k : X → K) (f : X → F) : (redistributionMarginal Z k f).PosSemidef := by
  rw [X4C1.rmA]
  exact Matrix.posSemidef_sum _ fun φ _ => hZ.mul_mul_conjTranspose_same _

/-- Entropy of a redistribution marginal only depends on the level-set partitions. -/
theorem rm_ent_congr {X K1 F1 K2 F2 : Type} [Fintype X] [Fintype K1] [Fintype F1] [Fintype K2]
    {Z : Matrix X X ℂ} (hZ : Z.PosSemidef) (k1 : X → K1) (f1 : X → F1) (k2 : X → K2) (f2 : X → F2)
    (hk : ∀ x y, k1 x = k1 y ↔ k2 x = k2 y) (hf : ∀ x y, f1 x = f1 y ↔ f2 x = f2 y) :
    vnEntropy (redistributionMarginal Z k2 f2) = vnEntropy (redistributionMarginal Z k1 f1) := by
  set M := redistributionMarginal Z k1 f1
  let J : Matrix K2 K1 ℂ := Matrix.of fun b a => if ∃ x, k1 x = a ∧ k2 x = b then 1 else 0
  have hJk : ∀ b x, J b (k1 x) = if k2 x = b then 1 else 0 := by
    intro b x
    simp only [J, of_apply]
    congr 1
    apply propext
    constructor
    · rintro ⟨x', h1, h2⟩; rw [← h2]; exact ((hk x' x).1 h1).symm
    · intro h; exact ⟨x, rfl, h⟩
  have hM : ∀ a a', M a a' = ∑ x, ∑ y, if k1 x = a ∧ k1 y = a' ∧ f1 x = f1 y then Z x y else 0 := by
    intro a a'; rfl
  have c1 : redistributionMarginal Z k2 f2 = J * M * Jᴴ := by
    funext b b'
    simp only [Matrix.mul_apply, conjTranspose_apply, hM, Finset.mul_sum, Finset.sum_mul]
    rw [X4DPI.sum4]
    simp only [redistributionMarginal]
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
    rw [Finset.sum_eq_single (k1 y), Finset.sum_eq_single (k1 x)]
    rotate_left
    · intro a _ h; simp [Ne.symm h]
    · simp
    · intro a' _ h; refine Finset.sum_eq_zero fun a _ => ?_; simp [Ne.symm h]
    · simp
    simp only [true_and, hJk]
    by_cases h3 : f1 x = f1 y
    · have h4 := (hf x y).1 h3
      by_cases h1 : k2 x = b <;> by_cases h2 : k2 y = b' <;> simp [h1, h2, h3, h4]
    · have h4 : ¬ f2 x = f2 y := mt (hf x y).2 h3
      simp [h3, h4]
  have c2 : Jᴴ * J * M = M := by
    funext a a'
    simp only [Matrix.mul_apply, conjTranspose_apply, hM, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [Finset.sum_eq_single (k1 x)]
    · by_cases h : k1 y = a' ∧ f1 x = f1 y
      · simp only [h, and_true, true_and]
        have : ∑ b, star (J b a) * J b (k1 x) = if k1 x = a then 1 else 0 := by
          simp_rw [hJk]
          rw [Finset.sum_eq_single (k2 x)]
          · simp only [if_true, mul_one, J, of_apply]
            by_cases hxa : k1 x = a
            · rw [if_pos ⟨x, hxa, rfl⟩, if_pos hxa]; simp
            · rw [if_neg, if_neg hxa]; · simp
              rintro ⟨x', h1, h2⟩; exact hxa ((hk x' x).2 h2 ▸ h1)
          · intro b _ hb; simp [Ne.symm hb]
          · simp
        rw [this]
        by_cases hxa : k1 x = a <;> simp [hxa]
      · simp only [h, and_false, if_false, mul_zero]
    · intro a'' _ h; simp [Ne.symm h]
    · simp
  rw [c1, vn_conj_piso (rm_psd hZ k1 f1) J c2]

theorem rm_ent_congr' {X K1 F1 K2 F2 : Type} [Fintype X] [Fintype K1] [Fintype F1] [Fintype K2]
    {Z : Matrix X X ℂ} (hZ : Z.PosSemidef) (k1 : X → K1) (f1 : X → F1) (k2 : X → K2) (f2 : X → F2)
    (hk : ∀ x y, k1 x = k1 y ↔ k2 x = k2 y) (hf : ∀ x y, f1 x = f1 y ↔ f2 x = f2 y)
    (d1 : DecidableEq K1) (d2 : DecidableEq K2) :
    @vnEntropy K2 _ d2 (redistributionMarginal Z k2 f2) = @vnEntropy K1 _ d1 (redistributionMarginal Z k1 f1) := by
  have h := rm_ent_congr hZ k1 f1 k2 f2 hk hf
  convert h using 2

theorem ssa_rm {X KX KY KZ F : Type} [Fintype X] [Fintype KX] [Fintype KY] [Fintype KZ] [Fintype F]
    {Z : Matrix X X ℂ} (hZ : IsDensityMatrix Z) (kX : X → KX) (kY : X → KY) (kZ : X → KZ) (f : X → F)
    (hinj : ∀ x y, kX x = kX y → kY x = kY y → kZ x = kZ y → f x = f y → x = y) :
    vnEntropy (redistributionMarginal Z (fun x => (kX x, (kY x, kZ x))) f) +
      vnEntropy (redistributionMarginal Z kZ (fun x => ((kX x, kY x), f x))) ≤
    vnEntropy (redistributionMarginal Z (fun x => (kX x, kZ x)) (fun x => (kY x, f x))) +
      vnEntropy (redistributionMarginal Z (fun x => (kY x, kZ x)) (fun x => (kX x, f x))) := by
  have hX : Nonempty X := by
    by_contra h
    rw [not_nonempty_iff] at h
    have := hZ.2
    simp [Matrix.trace] at this
  obtain ⟨x0⟩ := hX
  have : Nonempty KX := ⟨kX x0⟩
  have : Nonempty KY := ⟨kY x0⟩
  have : Nonempty KZ := ⟨kZ x0⟩
  have hω := X4C1.rm_density Z (fun x => (kX x, (kY x, kZ x))) f (fun x y h1 h2 => by
    simp only [Prod.mk.injEq] at h1
    exact hinj x y h1.1 h1.2.1 h1.2.2 h2) hZ
  have h := strongSubadditivity _ hω
  simp only [subsystemEntropy, X4C1.rm_comp] at h
  have key : 0 ≤ vnEntropy (redistributionMarginal Z (fun x => (kX x, kZ x)) (fun x => (kY x, f x))) +
      vnEntropy (redistributionMarginal Z (fun x => (kY x, kZ x)) (fun x => (kX x, f x))) -
      vnEntropy (redistributionMarginal Z kZ (fun x => ((kX x, kY x), f x))) -
      vnEntropy (redistributionMarginal Z (fun x => (kX x, (kY x, kZ x))) f) := by
    convert h using 4 <;> congr
  linarith

end X4RM

end

-- ===== SQA =====

/-! Strong subadditivity for register sets with an environment register (Claimed50.P33
`entropyAt` conventions), and nonnegativity of both conditional multipartite informations. -/

noncomputable section

namespace X4SQ
open Matrix QAlgorithms
open QAlgorithms.Papers.Independent.Claimed50.P33
open QAlgorithms.Papers.Independent.Gap48.P20 (redistributionMarginal subsystemEntropy strongSubadditivity)
open scoped Matrix ComplexConjugate ComplexOrder

attribute [local instance] Classical.propDecidable Classical.decEq

variable {n : ℕ} {G : Fin n → Type} [∀ i, Fintype (G i)] {E : Type} [Fintype E]

lemma ent_rm (τ : Matrix (RegisterBasis G × E) (RegisterBasis G × E) ℂ) (hτ : τ.PosSemidef)
    (s : Finset (Fin n)) {K F : Type} [Fintype K] [Fintype F]
    (k : RegisterBasis G × E → K) (f : RegisterBasis G × E → F)
    (hk : ∀ x y, k x = k y ↔ (∀ i ∈ s, x.1 i = y.1 i) ∧ x.2 = y.2)
    (hf : ∀ x y, f x = f y ↔ ∀ i, i ∉ s → x.1 i = y.1 i) (d : DecidableEq K) :
    @vnEntropy K _ d (redistributionMarginal τ k f) = entropyAt τ s := by
  rw [entropyAt, X4C1.reg_rm]
  exact X4RM.rm_ent_congr' hτ (fun x => (X4C1.restr s x.1, x.2)) (fun x => X4C1.restrC s x.1) k f
    (fun x y => by rw [Prod.mk.injEq, X4C1.restr_eq, hk]) (fun x y => by rw [X4C1.restrC_eq, hf]) _ _

theorem ssa_reg (τ : Matrix (RegisterBasis G × E) (RegisterBasis G × E) ℂ) (hτ : IsDensityMatrix τ)
    (X Y Z : Finset (Fin n)) (hXY : Disjoint X Y) (hXZ : Disjoint X Z) (hYZ : Disjoint Y Z) :
    entropyAt τ (X ∪ Y ∪ Z) + entropyAt τ Z ≤ entropyAt τ (X ∪ Z) + entropyAt τ (Y ∪ Z) := by
  have h := X4RM.ssa_rm hτ (fun x => X4C1.restr X x.1) (fun x => X4C1.restr Y x.1)
    (fun x => (X4C1.restr Z x.1, x.2)) (fun x => X4C1.restrC (X ∪ Y ∪ Z) x.1) (by
      intro x y h1 h2 h3 h4
      simp only [Prod.mk.injEq, X4C1.restr_eq, X4C1.restrC_eq] at h1 h2 h3 h4
      refine Prod.ext (funext fun i => ?_) h3.2
      by_cases hx : i ∈ X; · exact h1 i hx
      by_cases hy : i ∈ Y; · exact h2 i hy
      by_cases hz : i ∈ Z; · exact h3.1 i hz
      exact h4 i (by simp [hx, hy, hz]))
  have dXY : ∀ i, i ∈ X → i ∉ Y := fun i h => Finset.disjoint_left.1 hXY h
  have dXZ : ∀ i, i ∈ X → i ∉ Z := fun i h => Finset.disjoint_left.1 hXZ h
  have dYZ : ∀ i, i ∈ Y → i ∉ Z := fun i h => Finset.disjoint_left.1 hYZ h
  rw [ent_rm τ hτ.1 (X ∪ Y ∪ Z) (fun x => (X4C1.restr X x.1, X4C1.restr Y x.1, X4C1.restr Z x.1, x.2))
      (fun x => X4C1.restrC (X ∪ Y ∪ Z) x.1) (fun x y => by
      simp only [Prod.mk.injEq, X4C1.restr_eq, Finset.mem_union]
      constructor
      · rintro ⟨h1, h2, h3, h4⟩; exact ⟨fun i hi => by rcases hi with (hi | hi) | hi <;> tauto, h4⟩
      · rintro ⟨h1, h2⟩; exact ⟨fun i hi => h1 i (by tauto), fun i hi => h1 i (by tauto),
          fun i hi => h1 i (by tauto), h2⟩)
      (fun x y => by rw [X4C1.restrC_eq]) _,
    ent_rm τ hτ.1 Z (fun x => (X4C1.restr Z x.1, x.2))
      (fun x => ((X4C1.restr X x.1, X4C1.restr Y x.1), X4C1.restrC (X ∪ Y ∪ Z) x.1)) (fun x y => by simp only [Prod.mk.injEq, X4C1.restr_eq])
      (fun x y => by
        simp only [Prod.mk.injEq, X4C1.restr_eq, X4C1.restrC_eq, Finset.mem_union, not_or]
        constructor
        · rintro ⟨⟨h1, h2⟩, h3⟩ i hi
          by_cases hx : i ∈ X; · exact h1 i hx
          by_cases hy : i ∈ Y; · exact h2 i hy
          exact h3 i ⟨⟨hx, hy⟩, hi⟩
        · intro h
          exact ⟨⟨fun i hi => h i (dXZ i hi), fun i hi => h i (dYZ i hi)⟩, fun i hi => h i hi.2⟩) _,
    ent_rm τ hτ.1 (X ∪ Z) (fun x => (X4C1.restr X x.1, X4C1.restr Z x.1, x.2))
      (fun x => (X4C1.restr Y x.1, X4C1.restrC (X ∪ Y ∪ Z) x.1)) (fun x y => by
        simp only [Prod.mk.injEq, X4C1.restr_eq, Finset.mem_union]
        constructor
        · rintro ⟨h1, h2, h3⟩; exact ⟨fun i hi => by rcases hi with hi | hi <;> tauto, h3⟩
        · rintro ⟨h1, h2⟩; exact ⟨fun i hi => h1 i (by tauto), fun i hi => h1 i (by tauto), h2⟩)
      (fun x y => by
        simp only [Prod.mk.injEq, X4C1.restr_eq, X4C1.restrC_eq, Finset.mem_union, not_or]
        constructor
        · rintro ⟨h1, h2⟩ i hi
          by_cases hy : i ∈ Y; · exact h1 i hy
          exact h2 i ⟨⟨hi.1, hy⟩, hi.2⟩
        · intro h
          exact ⟨fun i hi => h i ⟨fun h' => dXY i h' hi, dYZ i hi⟩, fun i hi => h i ⟨hi.1.1, hi.2⟩⟩) _,
    ent_rm τ hτ.1 (Y ∪ Z) (fun x => (X4C1.restr Y x.1, X4C1.restr Z x.1, x.2))
      (fun x => (X4C1.restr X x.1, X4C1.restrC (X ∪ Y ∪ Z) x.1)) (fun x y => by
        simp only [Prod.mk.injEq, X4C1.restr_eq, Finset.mem_union]
        constructor
        · rintro ⟨h1, h2, h3⟩; exact ⟨fun i hi => by rcases hi with hi | hi <;> tauto, h3⟩
        · rintro ⟨h1, h2⟩; exact ⟨fun i hi => h1 i (by tauto), fun i hi => h1 i (by tauto), h2⟩)
      (fun x y => by
        simp only [Prod.mk.injEq, X4C1.restr_eq, X4C1.restrC_eq, Finset.mem_union, not_or]
        constructor
        · rintro ⟨h1, h2⟩ i hi
          by_cases hx : i ∈ X; · exact h1 i hx
          exact h2 i ⟨⟨hx, hi.1⟩, hi.2⟩
        · intro h
          exact ⟨fun i hi => h i ⟨dXY i hi, dXZ i hi⟩, fun i hi => h i ⟨hi.1.2, hi.2⟩⟩) _] at h
  exact h

/-- Prefix register sets. -/
def P (n : ℕ) (j : ℕ) : Finset (Fin n) := Finset.univ.filter fun i => i.val < j

lemma tele (n : ℕ) (g : ℕ → ℝ) : ∑ i : Fin n, (g (i.val + 1) - g i.val) = g n - g 0 := by
  rw [Fin.sum_univ_eq_sum_range (fun j => g (j + 1) - g j), Finset.sum_range_sub]

lemma P_zero (n : ℕ) : P n 0 = ∅ := by ext i; simp [P]
lemma P_n (n : ℕ) : P n n = Finset.univ := by ext i; simp [P, i.2]
lemma P_succ (n : ℕ) (i : Fin n) : P n (i.val + 1) = {i} ∪ P n i.val := by
  ext j; simp only [P, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union,
    Finset.mem_singleton]; constructor
  · intro h; by_cases hj : j = i; · exact Or.inl hj
    · right; have : j.val ≠ i.val := fun h' => hj (Fin.ext h'); omega
  · rintro (h | h); · rw [h]; omega
    · omega

theorem cmi_nonneg (τ : Matrix (RegisterBasis G × E) (RegisterBasis G × E) ℂ) (hτ : IsDensityMatrix τ)
    (hn : 1 ≤ n) (kind : InformationKind) :
    0 ≤ conditionalMultipartiteInformation kind τ (singleParties n) ∅ := by
  have hall : allParties (singleParties n) = Finset.univ := by
    ext j; simp [allParties, singleParties]
  have hc : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by rw [Nat.cast_sub hn]; simp
  have hS := fun X Y Z hXY hXZ hYZ => ssa_reg τ hτ X Y Z hXY hXZ hYZ
  cases kind with
  | total =>
    simp only [conditionalMultipartiteInformation, hall, Finset.union_empty, singleParties]
    have ht := tele n (fun j => entropyAt τ (P n j))
    simp only [P_zero, P_n] at ht
    have key : ∀ i : Fin n, 0 ≤ entropyAt τ {i} + entropyAt τ (P n i.val) -
        entropyAt τ (P n (i.val + 1)) - entropyAt τ ∅ := by
      intro i
      have h := hS {i} (P n i.val) ∅ (by simp [P]) (Finset.disjoint_empty_right _)
        (Finset.disjoint_empty_right _)
      simp only [Finset.union_empty] at h
      rw [P_succ]; linarith
    have hsum := Finset.sum_nonneg fun i (_ : i ∈ Finset.univ) => key i
    simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul] at hsum
    rw [hc]
    have : ∑ i : Fin n, entropyAt τ (P n i.val) - ∑ i : Fin n, entropyAt τ (P n (i.val + 1)) =
        entropyAt τ ∅ - entropyAt τ Finset.univ := by
      rw [Finset.sum_sub_distrib] at ht; linarith
    linarith
  | dual =>
    have hb : ∀ i : Fin n, (Finset.univ.erase i).biUnion (singleParties n) = Finset.univ.erase i := by
      intro i; ext j; simp [singleParties]
    simp only [conditionalMultipartiteInformation, hall, Finset.union_empty, hb]
    have ht := tele n (fun j => entropyAt τ (P n j))
    simp only [P_zero, P_n] at ht
    have key : ∀ i : Fin n, 0 ≤ entropyAt τ (Finset.univ.erase i) - entropyAt τ Finset.univ +
        entropyAt τ (P n (i.val + 1)) - entropyAt τ (P n i.val) := by
      intro i
      set Y : Finset (Fin n) := Finset.univ.filter fun j => i.val < j.val
      have h := hS {i} Y (P n i.val) (by simp [Y]) (by simp [P]) (by
        rw [Finset.disjoint_left]; intro j hj hj'; simp [Y, P] at hj hj'; omega)
      have e1 : {i} ∪ Y ∪ P n i.val = Finset.univ := by
        ext j; simp only [Y, P, Finset.mem_union, Finset.mem_singleton, Finset.mem_filter,
          Finset.mem_univ, true_and, iff_true]
        by_cases hj : j = i; · tauto
        · have : j.val ≠ i.val := fun h' => hj (Fin.ext h'); omega
      have e2 : Y ∪ P n i.val = Finset.univ.erase i := by
        ext j; simp only [Y, P, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and,
          Finset.mem_erase, and_true]
        constructor
        · intro h h'; rw [h'] at h; omega
        · intro h; have : j.val ≠ i.val := fun h' => h (Fin.ext h'); omega
      rw [e1, e2, ← P_succ] at h
      linarith
    have hsum := Finset.sum_nonneg fun i (_ : i ∈ Finset.univ) => key i
    simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul] at hsum
    rw [hc]
    have : ∑ i : Fin n, entropyAt τ (P n (i.val + 1)) - ∑ i : Fin n, entropyAt τ (P n i.val) =
        entropyAt τ Finset.univ - entropyAt τ ∅ := by
      rw [Finset.sum_sub_distrib] at ht; linarith
    linarith

end X4SQ

end

-- ===== SQB =====

/-! Entropies of the unprimed / primed parts of a paired register state with environment,
and strong subadditivity for them. -/

noncomputable section

namespace X4SQ
open Matrix QAlgorithms
open QAlgorithms.Papers.Independent.Claimed50.P33
open QAlgorithms.Papers.Independent.Gap48.P20 (redistributionMarginal subsystemEntropy strongSubadditivity)
open scoped Matrix ComplexConjugate ComplexOrder

attribute [local instance] Classical.propDecidable Classical.decEq

variable {m : ℕ} {D F : Fin m → Type} [∀ i, Fintype (D i)] [∀ i, Fintype (F i)] {E : Type} [Fintype E]

def dS (S : Finset (Fin m)) (x : RegisterBasis (fun i => D i × F i) × E) : SubBasis D S :=
  fun i => (x.1 i.1).1
def pT (T : Finset (Fin m)) (x : RegisterBasis (fun i => D i × F i) × E) : SubBasis F T :=
  fun i => (x.1 i.1).2

/-- Keep the unprimed parts in `S`, the primed parts in `T`, and the environment. -/
def kST (S T : Finset (Fin m)) (x : RegisterBasis (fun i => D i × F i) × E) :
    SubBasis D S × (SubBasis F T × E) :=
  (dS S x, (pT T x, x.2))

def fST (S T : Finset (Fin m)) (x : RegisterBasis (fun i => D i × F i) × E) :
    ((i : {i : Fin m // i ∉ S}) → D i.1) × ((i : {i : Fin m // i ∉ T}) → F i.1) :=
  (fun i => (x.1 i.1).1, fun i => (x.1 i.1).2)

def Ent (σ : Matrix (RegisterBasis (fun i => D i × F i) × E) (RegisterBasis (fun i => D i × F i) × E) ℂ)
    (S T : Finset (Fin m)) : ℝ :=
  vnEntropy (redistributionMarginal σ (kST S T) (fST S T))

def RD (S : Finset (Fin m)) (x y : RegisterBasis (fun i => D i × F i) × E) : Prop :=
  ∀ i ∈ S, (x.1 i).1 = (y.1 i).1
def RF (T : Finset (Fin m)) (x y : RegisterBasis (fun i => D i × F i) × E) : Prop :=
  ∀ i ∈ T, (x.1 i).2 = (y.1 i).2
def CD (S : Finset (Fin m)) (x y : RegisterBasis (fun i => D i × F i) × E) : Prop :=
  ∀ i, i ∉ S → (x.1 i).1 = (y.1 i).1
def CF (T : Finset (Fin m)) (x y : RegisterBasis (fun i => D i × F i) × E) : Prop :=
  ∀ i, i ∉ T → (x.1 i).2 = (y.1 i).2

lemma dS_eq (S : Finset (Fin m)) (x y : RegisterBasis (fun i => D i × F i) × E) :
    dS S x = dS S y ↔ RD S x y := by
  simp [dS, RD, funext_iff]
lemma pT_eq (T : Finset (Fin m)) (x y : RegisterBasis (fun i => D i × F i) × E) :
    pT T x = pT T y ↔ RF T x y := by
  simp [pT, RF, funext_iff]

lemma kST_eq (S T : Finset (Fin m)) (x y : RegisterBasis (fun i => D i × F i) × E) :
    kST S T x = kST S T y ↔ RD S x y ∧ RF T x y ∧ x.2 = y.2 := by
  simp only [kST, Prod.mk.injEq, dS_eq, pT_eq]

lemma fST_eq (S T : Finset (Fin m)) (x y : RegisterBasis (fun i => D i × F i) × E) :
    fST S T x = fST S T y ↔ CD S x y ∧ CF T x y := by
  simp [fST, CD, CF, funext_iff]

lemma RD_union (S S' : Finset (Fin m)) (x y : RegisterBasis (fun i => D i × F i) × E) :
    RD (S ∪ S') x y ↔ RD S x y ∧ RD S' x y := by
  simp only [RD, Finset.mem_union]; constructor
  · intro h; exact ⟨fun i hi => h i (Or.inl hi), fun i hi => h i (Or.inr hi)⟩
  · rintro ⟨h1, h2⟩ i (hi | hi); exacts [h1 i hi, h2 i hi]
lemma RF_union (S S' : Finset (Fin m)) (x y : RegisterBasis (fun i => D i × F i) × E) :
    RF (S ∪ S') x y ↔ RF S x y ∧ RF S' x y := by
  simp only [RF, Finset.mem_union]; constructor
  · intro h; exact ⟨fun i hi => h i (Or.inl hi), fun i hi => h i (Or.inr hi)⟩
  · rintro ⟨h1, h2⟩ i (hi | hi); exacts [h1 i hi, h2 i hi]
/-- complement splitting: `S'` disjoint from `S`. -/
lemma CD_split (S S' : Finset (Fin m)) (h : Disjoint S S') (x y : RegisterBasis (fun i => D i × F i) × E) :
    CD S x y ↔ RD S' x y ∧ CD (S ∪ S') x y := by
  simp only [CD, RD, Finset.mem_union, not_or]; constructor
  · intro h1; exact ⟨fun i hi => h1 i (Finset.disjoint_right.1 h hi), fun i hi => h1 i hi.1⟩
  · rintro ⟨h1, h2⟩ i hi; by_cases h' : i ∈ S'; exacts [h1 i h', h2 i ⟨hi, h'⟩]
lemma CF_split (S S' : Finset (Fin m)) (h : Disjoint S S') (x y : RegisterBasis (fun i => D i × F i) × E) :
    CF S x y ↔ RF S' x y ∧ CF (S ∪ S') x y := by
  simp only [CF, RF, Finset.mem_union, not_or]; constructor
  · intro h1; exact ⟨fun i hi => h1 i (Finset.disjoint_right.1 h hi), fun i hi => h1 i hi.1⟩
  · rintro ⟨h1, h2⟩ i hi; by_cases h' : i ∈ S'; exacts [h1 i h', h2 i ⟨hi, h'⟩]

lemma ent_congr (σ : Matrix (RegisterBasis (fun i => D i × F i) × E) (RegisterBasis (fun i => D i × F i) × E) ℂ)
    (hσ : σ.PosSemidef) (S T : Finset (Fin m)) {K G : Type} [Fintype K] [Fintype G]
    (k : RegisterBasis (fun i => D i × F i) × E → K) (f : RegisterBasis (fun i => D i × F i) × E → G)
    (hk : ∀ x y, k x = k y ↔ RD S x y ∧ RF T x y ∧ x.2 = y.2)
    (hf : ∀ x y, f x = f y ↔ CD S x y ∧ CF T x y) (d : DecidableEq K) :
    @vnEntropy K _ d (redistributionMarginal σ k f) = Ent σ S T := by
  rw [Ent]
  exact X4RM.rm_ent_congr' hσ _ _ k f (fun x y => by rw [kST_eq, hk]) (fun x y => by rw [fST_eq, hf]) _ _

theorem ssa_ST (σ : Matrix (RegisterBasis (fun i => D i × F i) × E) (RegisterBasis (fun i => D i × F i) × E) ℂ)
    (hσ : IsDensityMatrix σ) (S1 S2 S3 T1 T2 T3 : Finset (Fin m))
    (h12 : Disjoint S1 S2) (h13 : Disjoint S1 S3) (h23 : Disjoint S2 S3)
    (g12 : Disjoint T1 T2) (g13 : Disjoint T1 T3) (g23 : Disjoint T2 T3) :
    Ent σ (S1 ∪ S2 ∪ S3) (T1 ∪ T2 ∪ T3) + Ent σ S3 T3 ≤
      Ent σ (S1 ∪ S3) (T1 ∪ T3) + Ent σ (S2 ∪ S3) (T2 ∪ T3) := by
  have hU1 : S1 ∪ S2 ∪ S3 = S1 ∪ S2 ∪ S3 := rfl
  have e1 : S3 ∪ (S1 ∪ S2) = S1 ∪ S2 ∪ S3 := Finset.union_comm _ _
  have e1' : T3 ∪ (T1 ∪ T2) = T1 ∪ T2 ∪ T3 := Finset.union_comm _ _
  have e2 : S1 ∪ S3 ∪ S2 = S1 ∪ S2 ∪ S3 := Finset.union_right_comm _ _ _
  have e2' : T1 ∪ T3 ∪ T2 = T1 ∪ T2 ∪ T3 := Finset.union_right_comm _ _ _
  have e3 : S2 ∪ S3 ∪ S1 = S1 ∪ S2 ∪ S3 := by ext; simp only [Finset.mem_union]; tauto
  have e3' : T2 ∪ T3 ∪ T1 = T1 ∪ T2 ∪ T3 := by ext; simp only [Finset.mem_union]; tauto
  have h := X4RM.ssa_rm hσ (fun x => (dS S1 x, pT T1 x)) (fun x => (dS S2 x, pT T2 x))
    (fun x => (dS S3 x, pT T3 x, x.2)) (fST (S1 ∪ S2 ∪ S3) (T1 ∪ T2 ∪ T3)) (by
      intro x y h1 h2 h3 h4
      simp only [Prod.mk.injEq, dS_eq, pT_eq, fST_eq] at h1 h2 h3 h4
      refine Prod.ext (funext fun i => Prod.ext ?_ ?_) h3.2.2
      · by_cases a1 : i ∈ S1; · exact h1.1 i a1
        by_cases a2 : i ∈ S2; · exact h2.1 i a2
        by_cases a3 : i ∈ S3; · exact h3.1 i a3
        exact h4.1 i (by simp [a1, a2, a3])
      · by_cases a1 : i ∈ T1; · exact h1.2 i a1
        by_cases a2 : i ∈ T2; · exact h2.2 i a2
        by_cases a3 : i ∈ T3; · exact h3.2.1 i a3
        exact h4.2 i (by simp [a1, a2, a3]))
  rw [ent_congr σ hσ.1 (S1 ∪ S2 ∪ S3) (T1 ∪ T2 ∪ T3)
      (fun x => ((dS S1 x, pT T1 x), ((dS S2 x, pT T2 x), (dS S3 x, pT T3 x, x.2))))
      (fST (S1 ∪ S2 ∪ S3) (T1 ∪ T2 ∪ T3))
      (fun x y => by simp only [Prod.mk.injEq, dS_eq, pT_eq, RD_union, RF_union]; tauto)
      (fun x y => fST_eq _ _ x y) _,
    ent_congr σ hσ.1 S3 T3 (fun x => (dS S3 x, pT T3 x, x.2))
      (fun x => (((dS S1 x, pT T1 x), (dS S2 x, pT T2 x)), fST (S1 ∪ S2 ∪ S3) (T1 ∪ T2 ∪ T3) x))
      (fun x y => by simp only [Prod.mk.injEq, dS_eq, pT_eq])
      (fun x y => by
        rw [CD_split S3 (S1 ∪ S2) (Finset.disjoint_union_right.2 ⟨h13.symm, h23.symm⟩),
          CF_split T3 (T1 ∪ T2) (Finset.disjoint_union_right.2 ⟨g13.symm, g23.symm⟩), e1, e1',
          RD_union, RF_union]
        simp only [Prod.mk.injEq, dS_eq, pT_eq, fST_eq]; tauto) _,
    ent_congr σ hσ.1 (S1 ∪ S3) (T1 ∪ T3) (fun x => ((dS S1 x, pT T1 x), (dS S3 x, pT T3 x, x.2)))
      (fun x => ((dS S2 x, pT T2 x), fST (S1 ∪ S2 ∪ S3) (T1 ∪ T2 ∪ T3) x))
      (fun x y => by simp only [Prod.mk.injEq, dS_eq, pT_eq, RD_union, RF_union]; tauto)
      (fun x y => by
        rw [CD_split (S1 ∪ S3) S2 (Finset.disjoint_union_left.2 ⟨h12, h23.symm⟩),
          CF_split (T1 ∪ T3) T2 (Finset.disjoint_union_left.2 ⟨g12, g23.symm⟩), e2, e2']
        simp only [Prod.mk.injEq, dS_eq, pT_eq, fST_eq]; tauto) _,
    ent_congr σ hσ.1 (S2 ∪ S3) (T2 ∪ T3) (fun x => ((dS S2 x, pT T2 x), (dS S3 x, pT T3 x, x.2)))
      (fun x => ((dS S1 x, pT T1 x), fST (S1 ∪ S2 ∪ S3) (T1 ∪ T2 ∪ T3) x))
      (fun x y => by simp only [Prod.mk.injEq, dS_eq, pT_eq, RD_union, RF_union]; tauto)
      (fun x y => by
        rw [CD_split (S2 ∪ S3) S1 (Finset.disjoint_union_left.2 ⟨h12.symm, h13.symm⟩),
          CF_split (T2 ∪ T3) T1 (Finset.disjoint_union_left.2 ⟨g12.symm, g13.symm⟩), e3, e3']
        simp only [Prod.mk.injEq, dS_eq, pT_eq, fST_eq]; tauto) _] at h
  exact h

end X4SQ

end

-- ===== SQC =====

/-! Superadditivity of the q-squashed multipartite informations (Claimed50.P33 (49)). -/

noncomputable section

namespace X4SQ
open Matrix QAlgorithms
open QAlgorithms.Papers.Independent.Claimed50.P33
open QAlgorithms.Papers.Independent.Gap48.P20 (redistributionMarginal subsystemEntropy strongSubadditivity)
open scoped Matrix ComplexConjugate ComplexOrder

attribute [local instance] Classical.propDecidable Classical.decEq

variable {m : ℕ} {D F : Fin m → Type} [∀ i, Fintype (D i)] [∀ i, Fintype (F i)]

def Qpair : RegisterBasis D × RegisterBasis F ≃ RegisterBasis (fun i => D i × F i) where
  toFun p i := (p.1 i, p.2 i)
  invFun x := (fun i => (x i).1, fun i => (x i).2)
  left_inv _ := rfl
  right_inv _ := rfl

variable (D F) in
abbrev eU (e : ℕ) : ℕ := Fintype.card (RegisterBasis F × Fin e)

variable (D F) in
def encE (e : ℕ) : RegisterBasis F × Fin e ≃ Fin (eU F e) := Fintype.equivFin _

variable (D F) in
def QU (e : ℕ) : RegisterBasis D × Fin (eU F e) ≃ RegisterBasis (fun i => D i × F i) × Fin e :=
  ((Equiv.refl _).prodCongr (encE F e).symm).trans
    ((Equiv.prodAssoc _ _ _).symm.trans (Qpair.prodCongr (Equiv.refl _)))

lemma QU_symm (e : ℕ) (x : RegisterBasis (fun i => D i × F i) × Fin e) :
    (QU D F e).symm x = (fun i => (x.1 i).1, encE F e (fun i => (x.1 i).2, x.2)) := rfl

lemma QU_enc (e : ℕ) (a : RegisterBasis D) (p : RegisterBasis F × Fin e) :
    QU D F e (a, encE F e p) = (fun i => (a i, p.1 i), p.2) := by
  simp [QU, Qpair]

def tauU {e : ℕ} (σ : Matrix (RegisterBasis (fun i => D i × F i) × Fin e)
    (RegisterBasis (fun i => D i × F i) × Fin e) ℂ) :
    Matrix (RegisterBasis D × Fin (eU F e)) (RegisterBasis D × Fin (eU F e)) ℂ :=
  σ.submatrix (QU D F e) (QU D F e)

def tauP {e : ℕ} (σ : Matrix (RegisterBasis (fun i => D i × F i) × Fin e)
    (RegisterBasis (fun i => D i × F i) × Fin e) ℂ) :
    Matrix (RegisterBasis F × Fin e) (RegisterBasis F × Fin e) ℂ :=
  redistributionMarginal σ (fun x => (fun i => (x.1 i).2, x.2)) (fun x => fun i => (x.1 i).1)

variable {e : ℕ} (σ : Matrix (RegisterBasis (fun i => D i × F i) × Fin e)
    (RegisterBasis (fun i => D i × F i) × Fin e) ℂ)

lemma fe_U : forgetEnvironment (tauU σ) = unprimedMarginal (forgetEnvironment σ) := by
  funext a b
  simp only [forgetEnvironment, tauU, submatrix_apply, unprimedMarginal]
  rw [← (encE F e).sum_comp]
  simp only [QU_enc, Fintype.sum_prod_type]

lemma fe_P : forgetEnvironment (tauP σ) = primedMarginal (forgetEnvironment σ) := by
  funext a b
  simp only [forgetEnvironment, tauP, primedMarginal]
  have : ∀ u v, redistributionMarginal σ (fun x => (fun i => (x.1 i).2, x.2)) (fun x => fun i => (x.1 i).1)
      u v = ∑ z : RegisterBasis D, σ ((fun i => (z i, u.1 i)), u.2) ((fun i => (z i, v.1 i)), v.2) := by
    intro u v
    rw [X4DPI.rm_e σ ((Qpair.symm.prodCongr (Equiv.refl _)).trans
      ((Equiv.prodAssoc _ _ _).trans (Equiv.prodComm _ _))) (fun x => (fun i => (x.1 i).2, x.2))
      (fun x i => (x.1 i).1) (fun _ => rfl) (fun _ => rfl)]
    rfl
  simp only [this]
  rw [Finset.sum_comm]

lemma dens_U (hσ : IsDensityMatrix σ) : IsDensityMatrix (tauU σ) := by
  refine ⟨hσ.1.submatrix _, ?_⟩
  rw [← hσ.2]
  simp only [Matrix.trace, Matrix.diag, tauU, submatrix_apply]
  exact (QU D F e).sum_comp (fun i => σ i i)

lemma dens_P (hσ : IsDensityMatrix σ) : IsDensityMatrix (tauP σ) :=
  X4C1.rm_density σ _ _ (fun x y h1 h2 => by
    simp only [Prod.mk.injEq, funext_iff] at h1 h2
    exact Prod.ext (funext fun i => Prod.ext (h2 i) (h1.1 i)) h1.2) hσ

lemma rm_subm {X T K G : Type*} [Fintype X] [Fintype T] (M : Matrix X X ℂ) (q : T ≃ X)
    (k : T → K) (f : T → G) :
    redistributionMarginal (M.submatrix q q) k f = redistributionMarginal M (k ∘ q.symm) (f ∘ q.symm) := by
  funext a b
  simp only [redistributionMarginal, submatrix_apply, Function.comp]
  rw [← q.symm.sum_comp]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [← q.symm.sum_comp]
  simp

lemma ent_S (hσ : σ.PosSemidef) (s : Finset (Fin m)) : entropyAt σ s = Ent σ s s := by
  rw [entropyAt, X4C1.reg_rm]
  exact ent_congr σ hσ s s _ _ (fun x y => by
      simp only [Prod.mk.injEq, X4C1.restr_eq, RD, RF, Prod.ext_iff]
      constructor
      · rintro ⟨h1, h2⟩; exact ⟨fun i hi => (h1 i hi).1, fun i hi => (h1 i hi).2, h2⟩
      · rintro ⟨h1, h2, h3⟩; exact ⟨fun i hi => ⟨h1 i hi, h2 i hi⟩, h3⟩)
    (fun x y => by
      simp only [X4C1.restrC_eq, CD, CF, Prod.ext_iff]
      constructor
      · intro h; exact ⟨fun i hi => (h i hi).1, fun i hi => (h i hi).2⟩
      · rintro ⟨h1, h2⟩ i hi; exact ⟨h1 i hi, h2 i hi⟩) _

lemma ent_U (hσ : σ.PosSemidef) (s : Finset (Fin m)) :
    entropyAt (tauU σ) s = Ent σ s Finset.univ := by
  rw [entropyAt, X4C1.reg_rm, tauU, rm_subm]
  exact ent_congr σ hσ s Finset.univ _ _ (fun x y => by
      simp only [Function.comp, QU_symm, Prod.mk.injEq, EmbeddingLike.apply_eq_iff_eq, X4C1.restr_eq]
      simp only [RD, RF, funext_iff, Finset.mem_univ, forall_const])
    (fun x y => by
      simp only [Function.comp, QU_symm, X4C1.restrC_eq, CD, CF, Finset.mem_univ, not_true_eq_false,
        IsEmpty.forall_iff, forall_const, and_true, implies_true]) _

lemma ent_P (hσ : σ.PosSemidef) (s : Finset (Fin m)) :
    entropyAt (tauP σ) s = Ent σ ∅ s := by
  rw [entropyAt, X4C1.reg_rm, tauP, X4C1.rm_comp]
  exact ent_congr σ hσ ∅ s _ _ (fun x y => by
      simp only [Function.comp, Prod.mk.injEq, X4C1.restr_eq, RD, RF, Finset.notMem_empty,
        IsEmpty.forall_iff, forall_const, true_and, implies_true])
    (fun x y => by
      simp only [Prod.mk.injEq, X4C1.restrC_eq]
      simp only [CD, CF, Finset.notMem_empty, not_false_eq_true, forall_const, funext_iff]
      tauto) _

end X4SQ

end

-- ===== SQD =====

noncomputable section

namespace X4SQ
open Matrix QAlgorithms
open QAlgorithms.Papers.Independent.Claimed50.P33

attribute [local instance] Classical.propDecidable Classical.decEq

variable {m : ℕ} {D F : Fin m → Type} [∀ i, Fintype (D i)] [∀ i, Fintype (F i)]

lemma erase_union (i : Fin m) : Finset.univ.erase i ∪ {i} = Finset.univ := by
  ext j; by_cases h : j = i <;> simp [h]

theorem main_ineq {e : ℕ} (σ : Matrix (RegisterBasis (fun i => D i × F i) × Fin e)
    (RegisterBasis (fun i => D i × F i) × Fin e) ℂ) (hσ : IsDensityMatrix σ) (hm : 1 ≤ m)
    (kind : InformationKind) :
    conditionalMultipartiteInformation kind (tauU σ) (singleParties m) ∅ +
      conditionalMultipartiteInformation kind (tauP σ) (singleParties m) ∅ ≤
      conditionalMultipartiteInformation kind σ (singleParties m) ∅ := by
  have hall : allParties (singleParties m) = Finset.univ := by
    ext j; simp [allParties, singleParties]
  have hc : ((m - 1 : ℕ) : ℝ) = (m : ℝ) - 1 := by rw [Nat.cast_sub hm]; simp
  have hS := ent_S σ hσ.1
  have hU := ent_U σ hσ.1
  have hP := ent_P σ hσ.1
  cases kind with
  | total =>
    simp only [conditionalMultipartiteInformation, hall, Finset.union_empty, singleParties, hS, hU, hP]
    have key : ∀ i : Fin m, Ent σ {i} Finset.univ + Ent σ ∅ {i} ≤ Ent σ {i} {i} + Ent σ ∅ Finset.univ := by
      intro i
      have h := ssa_ST σ hσ {i} ∅ ∅ ∅ (Finset.univ.erase i) {i} (by simp) (by simp) (by simp)
        (by simp) (by simp) (by simp)
      simp only [Finset.union_empty, Finset.empty_union, erase_union] at h
      exact h
    have hsum := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => key i
    simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul] at hsum
    rw [hc]
    linarith
  | dual =>
    have hb : ∀ i : Fin m, (Finset.univ.erase i).biUnion (singleParties m) = Finset.univ.erase i := by
      intro i; ext j; simp [singleParties]
    simp only [conditionalMultipartiteInformation, hall, Finset.union_empty, hb, hS, hU, hP]
    have key : ∀ i : Fin m, Ent σ (Finset.univ.erase i) Finset.univ + Ent σ ∅ (Finset.univ.erase i) ≤
        Ent σ (Finset.univ.erase i) (Finset.univ.erase i) + Ent σ ∅ Finset.univ := by
      intro i
      have h := ssa_ST σ hσ (Finset.univ.erase i) ∅ ∅ ∅ {i} (Finset.univ.erase i) (by simp) (by simp)
        (by simp) (by simp) (by simp) (by simp)
      simp only [Finset.union_empty, Finset.empty_union, Finset.union_comm {i}, erase_union] at h
      exact h
    have hsum := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => key i
    simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul] at hsum
    rw [hc]
    linarith

open scoped Matrix ComplexOrder

theorem superadd {m : ℕ} (hm : 2 ≤ m)
    {D F : Fin m → Type} [∀ i, Fintype (D i)] [∀ i, Fintype (F i)]
    [∀ i, Nonempty (D i)] [∀ i, Nonempty (F i)]
    (rho : Matrix (RegisterBasis (fun i => D i × F i)) (RegisterBasis (fun i => D i × F i)) ℂ)
    (hrho : IsDensityMatrix rho) : ∀ kind : InformationKind,
      multipartiteSquashed false kind (unprimedMarginal rho) +
        multipartiteSquashed false kind (primedMarginal rho) ≤ multipartiteSquashed false kind rho := by
  intro kind
  have hm1 : 1 ≤ m := by omega
  unfold multipartiteSquashed
  apply le_csInf
  · refine ⟨_, 1, one_pos, fun x y => rho x.1 y.1, ⟨?_, ?_⟩, ?_, fun h => absurd h (by decide), rfl⟩
    · exact hrho.1.submatrix Prod.fst
    · rw [← hrho.2]; simp [Matrix.trace, Matrix.diag, Fintype.sum_prod_type]
    · funext a b; simp [forgetEnvironment]
  · rintro v ⟨e, he, σ, hσ, hfe, -, rfl⟩
    have : Nonempty (Fin e) := ⟨⟨0, he⟩⟩
    have hA := csInf_le (s := {v : ℝ | ∃ e : ℕ, 0 < e ∧
        ∃ sigma : Matrix (RegisterBasis D × Fin e) (RegisterBasis D × Fin e) ℂ,
        IsDensityMatrix sigma ∧ forgetEnvironment sigma = unprimedMarginal rho ∧
        (false = true → IsClassicalExtension sigma) ∧
        v = conditionalMultipartiteInformation kind sigma (singleParties m) ∅})
      ⟨0, by rintro w ⟨e', -, τ, hτ, -, -, rfl⟩; exact cmi_nonneg τ hτ hm1 kind⟩
      ⟨eU F e, Fintype.card_pos, tauU σ, dens_U σ hσ, by rw [fe_U, hfe],
        fun h => absurd h (by decide), rfl⟩
    have hB := csInf_le (s := {v : ℝ | ∃ e : ℕ, 0 < e ∧
        ∃ sigma : Matrix (RegisterBasis F × Fin e) (RegisterBasis F × Fin e) ℂ,
        IsDensityMatrix sigma ∧ forgetEnvironment sigma = primedMarginal rho ∧
        (false = true → IsClassicalExtension sigma) ∧
        v = conditionalMultipartiteInformation kind sigma (singleParties m) ∅})
      ⟨0, by rintro w ⟨e', -, τ, hτ, -, -, rfl⟩; exact cmi_nonneg τ hτ hm1 kind⟩
      ⟨e, he, tauP σ, dens_P σ hσ, by rw [fe_P, hfe],
        fun h => absurd h (by decide), rfl⟩
    have := main_ineq σ hσ hm1 kind
    linarith

end X4SQ

end

-- ===== ADSol =====

/-! Additivity of the q-squashed quantities on party products (Claimed50.P33 Prop. 4). -/

noncomputable section

namespace X4SQ
open Matrix QAlgorithms
open QAlgorithms.Papers.Independent.Claimed50.P33
open QAlgorithms.Papers.Independent.Gap48.P20 (redistributionMarginal)
open scoped Matrix ComplexConjugate ComplexOrder Kronecker

attribute [local instance] Classical.propDecidable Classical.decEq

section
variable {n : ℕ} {G : Fin n → Type} [∀ i, Fintype (G i)] {E E' : Type} [Fintype E] [Fintype E']

lemma ent_relabel (τ : Matrix (RegisterBasis G × E) (RegisterBasis G × E) ℂ) (hτ : τ.PosSemidef)
    (g : E' ≃ E) (s : Finset (Fin n)) :
    entropyAt (τ.submatrix ((Equiv.refl _).prodCongr g) ((Equiv.refl _).prodCongr g)) s =
      entropyAt τ s := by
  rw [entropyAt, X4C1.reg_rm, rm_subm, entropyAt, X4C1.reg_rm]
  exact X4RM.rm_ent_congr' hτ _ _ _ _ (fun x y => by
      simp only [Function.comp, Equiv.prodCongr_symm, Equiv.prodCongr_apply, Prod.map, Equiv.refl_symm,
        Equiv.refl_apply, Prod.mk.injEq, EmbeddingLike.apply_eq_iff_eq])
    (fun x y => by simp only [Function.comp, Equiv.prodCongr_symm, Equiv.prodCongr_apply, Prod.map,
        Equiv.refl_symm, Equiv.refl_apply]) _ _

lemma cmi_relabel (τ : Matrix (RegisterBasis G × E) (RegisterBasis G × E) ℂ) (hτ : τ.PosSemidef)
    (g : E' ≃ E) {k : ℕ} (a : Fin k → Finset (Fin n)) (e : Finset (Fin n)) (kind : InformationKind) :
    conditionalMultipartiteInformation kind
      (τ.submatrix ((Equiv.refl _).prodCongr g) ((Equiv.refl _).prodCongr g)) a e =
    conditionalMultipartiteInformation kind τ a e := by
  cases kind <;> simp only [conditionalMultipartiteInformation, ent_relabel τ hτ g]

lemma fe_relabel (τ : Matrix (RegisterBasis G × E) (RegisterBasis G × E) ℂ) (g : E' ≃ E) :
    forgetEnvironment (τ.submatrix ((Equiv.refl _).prodCongr g) ((Equiv.refl _).prodCongr g)) =
      forgetEnvironment τ := by
  funext a b
  simp only [forgetEnvironment, submatrix_apply, Equiv.prodCongr_apply, Prod.map, Equiv.refl_apply]
  exact g.sum_comp (fun e => τ (a, e) (b, e))

lemma dens_relabel {τ : Matrix (RegisterBasis G × E) (RegisterBasis G × E) ℂ} (hτ : IsDensityMatrix τ)
    (g : E' ≃ E) :
    IsDensityMatrix (τ.submatrix ((Equiv.refl _).prodCongr g) ((Equiv.refl _).prodCongr g)) := by
  refine ⟨hτ.1.submatrix _, ?_⟩
  rw [← hτ.2]
  simp only [Matrix.trace, Matrix.diag, submatrix_apply]
  exact ((Equiv.refl _).prodCongr g).sum_comp (fun i => τ i i)
end

variable {m : ℕ} {D F : Fin m → Type} [∀ i, Fintype (D i)] [∀ i, Fintype (F i)]

def phi (E Z : Type) : RegisterBasis (fun i => D i × F i) × (E × Z) ≃
    (RegisterBasis D × E) × (RegisterBasis F × Z) :=
  (Qpair.symm.prodCongr (Equiv.refl _)).trans (Equiv.prodProdProdComm _ _ _ _)

lemma pp_eq {E Z : Type} (r : Matrix (RegisterBasis D × E) (RegisterBasis D × E) ℂ)
    (s : Matrix (RegisterBasis F × Z) (RegisterBasis F × Z) ℂ) :
    pairedProduct r s = (r ⊗ₖ s).submatrix (phi E Z) (phi E Z) := rfl

lemma dens_pp {E Z : Type} [Fintype E] [Fintype Z] {r : Matrix (RegisterBasis D × E) (RegisterBasis D × E) ℂ}
    {s : Matrix (RegisterBasis F × Z) (RegisterBasis F × Z) ℂ} (hr : IsDensityMatrix r)
    (hs : IsDensityMatrix s) : IsDensityMatrix (pairedProduct r s) := by
  rw [pp_eq]
  refine ⟨(hr.1.kronecker hs.1).submatrix _, ?_⟩
  have : ((r ⊗ₖ s).submatrix (phi E Z) (phi E Z)).trace = (r ⊗ₖ s).trace := by
    simp only [Matrix.trace, Matrix.diag, submatrix_apply]
    exact (phi E Z).sum_comp (fun i => (r ⊗ₖ s) i i)
  rw [this, Matrix.trace_kronecker, hr.2, hs.2, one_mul]

lemma fe_pp {E Z : Type} [Fintype E] [Fintype Z] (r : Matrix (RegisterBasis D × E) (RegisterBasis D × E) ℂ)
    (s : Matrix (RegisterBasis F × Z) (RegisterBasis F × Z) ℂ) :
    forgetEnvironment (pairedProduct r s) = partyProduct (forgetEnvironment r) (forgetEnvironment s) := by
  funext a b
  simp only [forgetEnvironment, pairedProduct, partyProduct, Fintype.sum_prod_type, Finset.sum_mul_sum]

lemma unp_pp (ρ : Matrix (RegisterBasis D) (RegisterBasis D) ℂ) {σ : Matrix (RegisterBasis F) (RegisterBasis F) ℂ}
    (hσ : σ.trace = 1) : unprimedMarginal (partyProduct ρ σ) = ρ := by
  funext a b
  simp only [unprimedMarginal, partyProduct, ← Finset.mul_sum]
  have : ∑ z : RegisterBasis F, σ z z = 1 := hσ
  rw [this, mul_one]

lemma pri_pp {ρ : Matrix (RegisterBasis D) (RegisterBasis D) ℂ} (σ : Matrix (RegisterBasis F) (RegisterBasis F) ℂ)
    (hρ : ρ.trace = 1) : primedMarginal (partyProduct ρ σ) = σ := by
  funext a b
  simp only [primedMarginal, partyProduct, ← Finset.sum_mul]
  have : ∑ z : RegisterBasis D, ρ z z = 1 := hρ
  rw [this, one_mul]

lemma dens_party {ρ : Matrix (RegisterBasis D) (RegisterBasis D) ℂ} {σ : Matrix (RegisterBasis F) (RegisterBasis F) ℂ}
    (hρ : IsDensityMatrix ρ) (hσ : IsDensityMatrix σ) : IsDensityMatrix (partyProduct ρ σ) := by
  have e : partyProduct ρ σ = (ρ ⊗ₖ σ).submatrix Qpair.symm Qpair.symm := rfl
  rw [e]
  refine ⟨(hρ.1.kronecker hσ.1).submatrix _, ?_⟩
  have : ((ρ ⊗ₖ σ).submatrix Qpair.symm Qpair.symm).trace = (ρ ⊗ₖ σ).trace := by
    simp only [Matrix.trace, Matrix.diag, submatrix_apply]
    exact (Qpair.symm).sum_comp (fun i => (ρ ⊗ₖ σ) i i)
  rw [this, Matrix.trace_kronecker, hρ.2, hσ.2, one_mul]

lemma inf_add {A B C : Set ℝ} (hA : A.Nonempty) (hB : B.Nonempty) (hC : BddBelow C)
    (key : ∀ a ∈ A, ∀ b ∈ B, a + b ∈ C) : sInf C ≤ sInf A + sInf B := by
  have h1 : ∀ b ∈ B, sInf C - b ≤ sInf A := fun b hb =>
    le_csInf hA fun a ha => by linarith [csInf_le hC (key a ha b hb)]
  have h2 : sInf C - sInf A ≤ sInf B := le_csInf hB fun b hb => by linarith [h1 b hb]
  linarith

lemma triv_mem {n : ℕ} {G : Fin n → Type} [∀ i, Fintype (G i)] {ρ : Matrix (RegisterBasis G) (RegisterBasis G) ℂ}
    (hρ : IsDensityMatrix ρ) (kind : InformationKind) :
    ∃ e : ℕ, 0 < e ∧ ∃ sigma : Matrix (RegisterBasis G × Fin e) (RegisterBasis G × Fin e) ℂ,
      IsDensityMatrix sigma ∧ forgetEnvironment sigma = ρ ∧ (false = true → IsClassicalExtension sigma) ∧
      conditionalMultipartiteInformation kind (fun x y : RegisterBasis G × Fin 1 => ρ x.1 y.1) (singleParties n) ∅ =
        conditionalMultipartiteInformation kind sigma (singleParties n) ∅ := by
  refine ⟨1, one_pos, fun x y => ρ x.1 y.1, ⟨?_, ?_⟩, ?_, fun h => absurd h (by decide), rfl⟩
  · exact hρ.1.submatrix Prod.fst
  · rw [← hρ.2]; simp [Matrix.trace, Matrix.diag, Fintype.sum_prod_type]
  · funext a b; simp [forgetEnvironment]

end X4SQ

open QAlgorithms QAlgorithms.Papers.Independent.Claimed50.P33
open scoped Matrix ComplexOrder

attribute [local instance] Classical.propDecidable Classical.decEq

theorem solution {m : ℕ} (hm : 2 ≤ m)
    {D F : Fin m → Type} [∀ i, Fintype (D i)] [∀ i, Fintype (F i)]
    [∀ i, Nonempty (D i)] [∀ i, Nonempty (F i)]
    (rho : Matrix (RegisterBasis D) (RegisterBasis D) ℂ) (sigma : Matrix (RegisterBasis F) (RegisterBasis F) ℂ)
    (hrho : IsDensityMatrix rho) (hsigma : IsDensityMatrix sigma) :
    ∀ kind : InformationKind,
      multipartiteSquashed false kind (partyProduct rho sigma) =
      multipartiteSquashed false kind rho + multipartiteSquashed false kind sigma := by
  intro kind
  have hm1 : 1 ≤ m := by omega
  have hpp : IsDensityMatrix (partyProduct rho sigma) := X4SQ.dens_party hrho hsigma
  obtain ⟨-, -, -, -, h5, -⟩ := proposition1 (k := 0) rho hrho (fun _ => ∅) ∅
    ⟨fun _ _ _ => Finset.disjoint_empty_left _, fun _ => Finset.disjoint_empty_left _⟩
  apply le_antisymm
  · unfold multipartiteSquashed
    refine X4SQ.inf_add ⟨_, X4SQ.triv_mem hrho kind⟩ ⟨_, X4SQ.triv_mem hsigma kind⟩
      ⟨0, by rintro w ⟨e', -, τ, hτ, -, -, rfl⟩; exact X4SQ.cmi_nonneg τ hτ hm1 kind⟩ ?_
    rintro v1 ⟨e1, he1, s1, hs1, hf1, -, rfl⟩ v2 ⟨e2, he2, s2, hs2, hf2, -, rfl⟩
    have : Nonempty (Fin e1) := ⟨⟨0, he1⟩⟩
    have : Nonempty (Fin e2) := ⟨⟨0, he2⟩⟩
    have hP := X4SQ.dens_pp hs1 hs2
    refine ⟨e1 * e2, Nat.mul_pos he1 he2, _, X4SQ.dens_relabel hP finProdFinEquiv.symm, ?_,
      fun h => absurd h (by decide), ?_⟩
    · rw [X4SQ.fe_relabel, X4SQ.fe_pp, hf1, hf2]
    · rw [X4SQ.cmi_relabel _ hP.1, h5 m D F (Fin e1) (Fin e2) s1 s2 hm hs1 hs2 kind]
  · have h := X4SQ.superadd hm (partyProduct rho sigma) hpp kind
    rwa [X4SQ.unp_pp rho hsigma.2, X4SQ.pri_pp sigma hrho.2] at h

