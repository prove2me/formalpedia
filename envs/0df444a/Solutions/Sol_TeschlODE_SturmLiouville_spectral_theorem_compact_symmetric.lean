-- Prove2me | solution 1 for TeschlODE.SturmLiouville.spectral_theorem_compact_symmetric
-- status  : ACCEPTED   (prove)
-- author  : @sometik179
-- created : 2026-10-10T01:23:12.475022+00:00
-- url     : https://prove2.me/submissions/d6454229-1fdc-4fae-a7e4-3f47ff4fc2ff

/-
SPDX-License-Identifier: Apache-2.0
Complete proof of the canonical compact symmetric spectral theorem.
All custom proof bodies are included; only canonical definitions and Mathlib
are imported. The compact eigenpair construction and orthogonal recursion are reconstructed.
-/
import Mathlib
import Definitions.Def_TeschlODE_SturmLiouville_IsCompactOp

/- Complete module: PrefixGeometry -/
section

open scoped ComplexConjugate BigOperators
namespace TeschlODE.SturmLiouville.Proof

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- The unused subspace after finitely many orthogonal eigenvectors. -/
noncomputable def prefixComplement {n : ℕ} (u : Fin n → E) : Submodule ℂ E :=
  (Submodule.span ℂ (Set.range u))ᗮ

theorem mem_prefixComplement {n : ℕ} (u : Fin n → E) (v : E) :
    v ∈ prefixComplement u ↔ ∀ i, inner ℂ (u i) v = 0 := by
  rw [prefixComplement, Submodule.mem_orthogonal]
  constructor
  · intro h i
    exact h _ (Submodule.subset_span (Set.mem_range_self i))
  · intro h w hw
    induction hw using Submodule.span_induction with
    | mem w hw => obtain ⟨i,rfl⟩ := hw; exact h i
    | zero => simp
    | add x y _ _ hx hy => simp [inner_add_left, hx, hy]
    | smul a x _ hx => simp [inner_smul_left, hx]

theorem prefixComplement_invariant {n : ℕ} (A : E →ₗ[ℂ] E)
    (hsym : A.IsSymmetric) (u : Fin n → E) (a : Fin n → ℝ)
    (hu : ∀ i, A (u i) = (a i : ℂ) • u i) :
    ∀ v ∈ prefixComplement u, A v ∈ prefixComplement u := by
  intro v hv
  rw [mem_prefixComplement] at hv ⊢
  intro i
  rw [← hsym, hu, inner_smul_left, hv, mul_zero]

theorem prefixComplement_nontrivial {n : ℕ} (u : Fin n → E)
    (hE : ¬ FiniteDimensional ℂ E) : Nontrivial (prefixComplement u) := by
  classical
  let K := Submodule.span ℂ (Set.range u)
  have : FiniteDimensional ℂ K := FiniteDimensional.span_of_finite ℂ (Set.finite_range u)
  apply Submodule.nontrivial_iff_ne_bot.mpr
  intro heq
  have htop : K = ⊤ := Submodule.orthogonal_eq_bot_iff.mp heq
  have : FiniteDimensional ℂ (⊤ : Submodule ℂ E) := htop ▸ inferInstance
  exact hE (FiniteDimensional.of_injective (Submodule.topEquiv : (⊤ : Submodule ℂ E) ≃ₗ[ℂ] E).symm.toLinearMap
    (Submodule.topEquiv.symm.injective))

theorem orthonormal_snoc {n : ℕ} (u : Fin n → E) (hu : Orthonormal ℂ u)
    (v : E) (hv : ‖v‖ = 1) (ho : v ∈ prefixComplement u) :
    Orthonormal ℂ (Fin.snoc u v) := by
  classical
  rw [orthonormal_iff_ite] at hu ⊢
  intro i j
  refine Fin.lastCases ?_ (fun i => ?_) i <;> refine Fin.lastCases ?_ (fun j => ?_) j
  · simp [inner_self_eq_norm_sq_to_K, hv]
  · simp only [Fin.snoc_last, Fin.snoc_castSucc, (Ne.symm (Fin.castSucc_ne_last j)), ite_false]
    exact inner_eq_zero_symm.mpr ((mem_prefixComplement u v).mp ho j)
  · simp only [Fin.snoc_last, Fin.snoc_castSucc, Fin.castSucc_ne_last, ite_false]
    exact (mem_prefixComplement u v).mp ho i
  · simpa only [Fin.snoc_castSucc, Fin.castSucc_inj] using hu i j

/-- Finite orthogonal expansion, defined without completing the ambient space. -/
noncomputable def prefixSum {n : ℕ} (u : Fin n → E) (x : E) : E :=
  ∑ i, inner ℂ (u i) x • u i

theorem prefixSum_remainder {n : ℕ} (u : Fin n → E) (hu : Orthonormal ℂ u) (x : E) :
    x - prefixSum u x ∈ prefixComplement u := by
  rw [mem_prefixComplement]
  intro i
  simp only [inner_sub_right, prefixSum, hu.inner_right_fintype, sub_self]

theorem prefixSum_remainder_norm {n : ℕ} (u : Fin n → E) (hu : Orthonormal ℂ u) (x : E) :
    ‖x-prefixSum u x‖ ≤ ‖x‖ := by
  have ho : inner ℂ (prefixSum u x) (x-prefixSum u x) = 0 := by
    change inner ℂ (∑ i, inner ℂ (u i) x • u i) (x-prefixSum u x) = 0
    rw [sum_inner]
    apply Finset.sum_eq_zero
    intro i _
    rw [inner_smul_left, (mem_prefixComplement u _).mp (prefixSum_remainder u hu x) i, mul_zero]
  have hp := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero
    (prefixSum u x) (x-prefixSum u x) ho
  rw [add_sub_cancel] at hp
  nlinarith [norm_nonneg (x-prefixSum u x), norm_nonneg x, sq_nonneg ‖prefixSum u x‖]

end TeschlODE.SturmLiouville.Proof

end

/- Complete module: EigenRecursion -/
section

noncomputable section
namespace TeschlODE.SturmLiouville.Proof
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- A finite orthonormal eigenvector prefix. -/
structure EigenPrefix (A : E →ₗ[ℂ] E) (n : ℕ) where
  u : Fin n → E
  a : Fin n → ℝ
  orth : Orthonormal ℂ u
  eigen : ∀ i, A (u i) = (a i : ℂ) • u i

/-- A maximal-modulus eigenvector on the unused complement. -/
structure EigenExtension {A : E →ₗ[ℂ] E} {n : ℕ} (p : EigenPrefix A n) where
  v : E
  b : ℝ
  unit : ‖v‖ = 1
  mem : v ∈ prefixComplement p.u
  eigen : A v = (b : ℂ) • v
  bound : ∀ w ∈ prefixComplement p.u, ‖A w‖ ≤ |b| * ‖w‖

def extendPrefix {A : E →ₗ[ℂ] E} {n : ℕ} {p : EigenPrefix A n}
    (e : EigenExtension p) : EigenPrefix A (n+1) where
  u := Fin.snoc p.u e.v
  a := Fin.snoc p.a e.b
  orth := orthonormal_snoc p.u p.orth e.v e.unit e.mem
  eigen i := by
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa using e.eigen
    · simpa using p.eigen j

def buildPrefix {A : E →ₗ[ℂ] E}
    (next : ∀ n, (p : EigenPrefix A n) → EigenExtension p) : (n : ℕ) → EigenPrefix A n
  | 0 => ⟨Fin.elim0, Fin.elim0, by simp, by intro i; exact i.elim0⟩
  | n+1 => extendPrefix (next n (buildPrefix next n))

def eigenSequence {A : E →ₗ[ℂ] E}
    (next : ∀ n, (p : EigenPrefix A n) → EigenExtension p) (n : ℕ) : E :=
  (next n (buildPrefix next n)).v

def valueSequence {A : E →ₗ[ℂ] E}
    (next : ∀ n, (p : EigenPrefix A n) → EigenExtension p) (n : ℕ) : ℝ :=
  (next n (buildPrefix next n)).b

theorem buildPrefix_u {A : E →ₗ[ℂ] E}
    (next : ∀ n, (p : EigenPrefix A n) → EigenExtension p) (n : ℕ) (i : Fin n) :
    (buildPrefix next n).u i = eigenSequence next i.val := by
  induction n with
  | zero => exact i.elim0
  | succ n ih =>
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp [buildPrefix,extendPrefix,eigenSequence]
    · simpa [buildPrefix,extendPrefix] using ih j

theorem buildPrefix_a {A : E →ₗ[ℂ] E}
    (next : ∀ n, (p : EigenPrefix A n) → EigenExtension p) (n : ℕ) (i : Fin n) :
    (buildPrefix next n).a i = valueSequence next i.val := by
  induction n with
  | zero => exact i.elim0
  | succ n ih =>
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp [buildPrefix,extendPrefix,valueSequence]
    · simpa [buildPrefix,extendPrefix] using ih j

theorem eigenSequence_orthonormal {A : E →ₗ[ℂ] E}
    (next : ∀ n, (p : EigenPrefix A n) → EigenExtension p) :
    Orthonormal ℂ (eigenSequence next) := by
  classical
  rw [orthonormal_iff_ite]
  intro i j
  let N := max i j + 1
  let ii : Fin N := ⟨i,by dsimp [N]; omega⟩
  let jj : Fin N := ⟨j,by dsimp [N]; omega⟩
  have h := (orthonormal_iff_ite.mp (buildPrefix next N).orth) ii jj
  simpa [buildPrefix_u, ii, jj] using h

theorem eigenSequence_eigen {A : E →ₗ[ℂ] E}
    (next : ∀ n, (p : EigenPrefix A n) → EigenExtension p) (n : ℕ) :
    A (eigenSequence next n) = (valueSequence next n : ℂ) • eigenSequence next n :=
  (next n (buildPrefix next n)).eigen

theorem eigenSequence_bound {A : E →ₗ[ℂ] E}
    (next : ∀ n, (p : EigenPrefix A n) → EigenExtension p) (n : ℕ) (w : E)
    (hw : ∀ j < n, inner ℂ (eigenSequence next j) w = 0) :
    ‖A w‖ ≤ |valueSequence next n| * ‖w‖ := by
  apply (next n (buildPrefix next n)).bound
  rw [mem_prefixComplement]
  intro j
  rw [buildPrefix_u]
  exact hw j.val j.isLt

theorem valueSequence_antitone {A : E →ₗ[ℂ] E}
    (next : ∀ n, (p : EigenPrefix A n) → EigenExtension p) :
    Antitone (fun n => |valueSequence next n|) := by
  apply antitone_nat_of_succ_le
  intro n
  have hu := eigenSequence_orthonormal next
  have h := eigenSequence_bound next n (eigenSequence next (n+1)) (by
    intro j hj
    exact hu.inner_eq_zero (by omega))
  simpa [eigenSequence_eigen, norm_smul, hu.norm_eq_one] using h

end TeschlODE.SturmLiouville.Proof

end
end

/- Complete module: CompactBounded -/
section

noncomputable section
open Filter Topology
namespace TeschlODE.SturmLiouville.Proof
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem bound_of_unit_bound (A : E →ₗ[ℂ] E) (C : ℝ)
    (_hC : 0 ≤ C) (h : ∀ x : E, ‖x‖ = 1 → ‖A x‖ ≤ C) :
    ∀ x, ‖A x‖ ≤ C * ‖x‖ := by
  intro x
  by_cases hx : x = 0
  · simp [hx]
  have hn : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hb := h ((‖x‖⁻¹ : ℂ) • x) (norm_smul_inv_norm hx)
  rw [map_smul, norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg hn.le] at hb
  have := (mul_le_mul_iff_left₀ hn).mpr hb
  field_simp at this
  nlinarith

theorem compact_unit_bound (A : E →ₗ[ℂ] E) (hA : IsCompactOp A) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : E, ‖x‖ = 1 → ‖A x‖ ≤ C := by
  classical
  by_contra h
  have he : ∀ n : ℕ, ∃ x : E, ‖x‖ = 1 ∧ (n : ℝ) < ‖A x‖ := by
    intro n
    by_contra hn
    push Not at hn
    exact h ⟨n, Nat.cast_nonneg n, hn⟩
  choose f hf hlt using he
  have hb : Bornology.IsBounded (Set.range f) :=
    isBounded_iff_forall_norm_le.mpr ⟨1, by rintro _ ⟨n, rfl⟩; exact (hf n).le⟩
  obtain ⟨φ, hφ, g, hg⟩ := hA f hb
  obtain ⟨C, hC⟩ := hg.cauchySeq.isBounded_range.exists_norm_le
  obtain ⟨n, hn⟩ := exists_nat_gt C
  have hle : (n : ℝ) ≤ (φ n : ℝ) := by exact_mod_cast hφ.id_le n
  have hu := hC (A (f (φ n))) ⟨n, rfl⟩
  have hl := hlt (φ n)
  linarith

theorem compact_bound (A : E →ₗ[ℂ] E) (hA : IsCompactOp A) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x, ‖A x‖ ≤ C * ‖x‖ := by
  obtain ⟨C, hC, hb⟩ := compact_unit_bound A hA
  exact ⟨C, hC, bound_of_unit_bound A C hC hb⟩

theorem compact_continuous (A : E →ₗ[ℂ] E) (hA : IsCompactOp A) : Continuous A := by
  obtain ⟨C, _, hC⟩ := compact_bound A hA
  exact (A.mkContinuous C hC).continuous

end TeschlODE.SturmLiouville.Proof

end
end

/- Complete module: SpectralApprox -/
section

noncomputable section
open Filter Topology
namespace TeschlODE.SturmLiouville.Proof
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem exists_unit_norm_approx [Nontrivial E] (A : E →L[ℂ] E) :
    ∃ f : ℕ → E, (∀ n, ‖f n‖ = 1) ∧
      Tendsto (fun n => ‖A (f n)‖) atTop (𝓝 ‖A‖) := by
  classical
  let S : Set ℝ := (fun x : E => ‖A x‖) '' Metric.sphere 0 1
  have hne : S.Nonempty := by
    obtain ⟨x, hx⟩ := NormedSpace.sphere_nonempty_rclike (𝕜 := ℂ) (E := E) zero_le_one
    exact ⟨_, x, hx, rfl⟩
  have hb : BddAbove S := ⟨‖A‖, by
    rintro _ ⟨x, hx, rfl⟩
    exact A.unit_le_opNorm x (mem_sphere_zero_iff_norm.mp hx).le⟩
  obtain ⟨v, _, hv, hmem⟩ := exists_seq_tendsto_sSup hne hb
  choose f hf heq using hmem
  refine ⟨f, fun n => mem_sphere_zero_iff_norm.mp (hf n), ?_⟩
  have hs : sSup S = ‖A‖ := A.sSup_sphere_eq_norm
  simpa only [heq, hs] using hv

theorem square_residual_bound (A : E →L[ℂ] E)
    (hsym : (A : E →ₗ[ℂ] E).IsSymmetric) (x : E) (hx : ‖x‖ = 1) :
    ‖A (A x) - ((‖A‖ ^ 2 : ℝ) : ℂ) • x‖ ^ 2 ≤
      2 * ‖A‖ ^ 2 * (‖A‖ ^ 2 - ‖A x‖ ^ 2) := by
  have hi : inner ℂ (A (A x)) x = inner ℂ (A x) (A x) := hsym (A x) x
  have hnorm : ‖A (A x)‖ ≤ ‖A‖ ^ 2 := by
    calc
      ‖A (A x)‖ ≤ ‖A‖ * ‖A x‖ := A.le_opNorm _
      _ ≤ ‖A‖ * ‖A‖ := mul_le_mul_of_nonneg_left (A.unit_le_opNorm x hx.le) (norm_nonneg _)
      _ = ‖A‖ ^ 2 := by ring
  have hsq : ‖A (A x)‖ ^ 2 ≤ (‖A‖ ^ 2) ^ 2 := sq_le_sq₀ (norm_nonneg _) (sq_nonneg _) |>.mpr hnorm
  rw [norm_sub_sq (𝕜 := ℂ), inner_smul_right, hi, inner_self_eq_norm_sq_to_K,
    norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), hx]
  change ‖A (A x)‖ ^ 2 - 2 * (Complex.re ((↑(‖A‖ ^ 2) : ℂ) * (↑‖A x‖ : ℂ) ^ 2)) + (‖A‖ ^ 2 * 1) ^ 2 ≤ _
  simp only [← Complex.ofReal_pow, ← Complex.ofReal_mul, Complex.ofReal_re, mul_one]
  nlinarith

theorem square_residual_tendsto (A : E →L[ℂ] E)
    (hsym : (A : E →ₗ[ℂ] E).IsSymmetric) (f : ℕ → E)
    (hf : ∀ n, ‖f n‖ = 1) (hlim : Tendsto (fun n => ‖A (f n)‖) atTop (𝓝 ‖A‖)) :
    Tendsto (fun n => A (A (f n)) - ((‖A‖ ^ 2 : ℝ) : ℂ) • f n) atTop (𝓝 0) := by
  have hh : Tendsto (fun n => ‖A (A (f n)) - ((‖A‖ ^ 2 : ℝ) : ℂ) • f n‖ ^ 2)
      atTop (𝓝 0) := by
    apply squeeze_zero (fun n => sq_nonneg _) (fun n => square_residual_bound A hsym _ (hf n))
    convert (tendsto_const_nhds.mul (tendsto_const_nhds.sub (hlim.pow 2))) using 1; simp
  have hn := (Real.continuous_sqrt.tendsto 0).comp hh
  change Tendsto (fun n => Real.sqrt (‖A (A (f n)) - ((‖A‖ ^ 2 : ℝ) : ℂ) • f n‖ ^ 2)) atTop (𝓝 (Real.sqrt 0)) at hn
  have hn' : Tendsto (fun n => ‖A (A (f n)) - ((‖A‖ ^ 2 : ℝ) : ℂ) • f n‖)
      atTop (𝓝 0) := by simpa only [Real.sqrt_sq_eq_abs, abs_norm, Real.sqrt_zero] using hn
  exact tendsto_zero_iff_norm_tendsto_zero.mpr hn'

end TeschlODE.SturmLiouville.Proof

end
end

/- Complete module: CompactSquareEigenvector -/
section

noncomputable section
open Filter Topology
namespace TeschlODE.SturmLiouville.Proof
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem compact_square_unit_eigenvector [Nontrivial E] (A : E →L[ℂ] E)
    (hA : IsCompactOp (A : E →ₗ[ℂ] E))
    (hsym : (A : E →ₗ[ℂ] E).IsSymmetric) (hc : 0 < ‖A‖) :
    ∃ u : E, ‖u‖ = 1 ∧ A (A u) = ((‖A‖ ^ 2 : ℝ) : ℂ) • u := by
  obtain ⟨f, hf, hlim⟩ := exists_unit_norm_approx A
  have hres := square_residual_tendsto A hsym f hf hlim
  have hb : Bornology.IsBounded (Set.range f) :=
    isBounded_iff_forall_norm_le.mpr ⟨1, by rintro _ ⟨n, rfl⟩; exact (hf n).le⟩
  obtain ⟨φ, hφ, g, hg⟩ := hA f hb
  let c : ℂ := ((‖A‖ ^ 2 : ℝ) : ℂ)
  have hc0 : c ≠ 0 := by dsimp [c]; exact_mod_cast (pow_ne_zero 2 hc.ne')
  let u : E := c⁻¹ • A g
  have hu : Tendsto (fun n => f (φ n)) atTop (𝓝 u) := by
    have ht := ((A.continuous.tendsto g).comp hg).sub (hres.comp hφ.tendsto_atTop)
    have ht' := ht.const_smul c⁻¹
    convert ht' using 1
    · ext n
      change f (φ n) = c⁻¹ • (A (A (f (φ n))) -
        (A (A (f (φ n))) - c • f (φ n)))
      rw [sub_sub_cancel, inv_smul_smul₀ hc0]
    · simp only [sub_zero]; rfl
  have hunorm : ‖u‖ = 1 := by
    have ht : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 ‖u‖) := by
      simpa only [hf] using hu.norm
    exact tendsto_nhds_unique ht tendsto_const_nhds
  have hgu : A u = g := tendsto_nhds_unique ((A.continuous.tendsto u).comp hu) hg
  refine ⟨u, hunorm, ?_⟩
  rw [hgu]
  exact (smul_inv_smul₀ hc0 (A g)).symm

end TeschlODE.SturmLiouville.Proof

end
end

/- Complete module: CompactRestriction -/
section

noncomputable section
open Filter Topology
namespace TeschlODE.SturmLiouville.Proof
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem compact_restrict (A : E →ₗ[ℂ] E) (hA : IsCompactOp A)
    (K : Submodule ℂ E) (hK : IsClosed (K : Set E))
    (hAK : ∀ x ∈ K, A x ∈ K) : IsCompactOp (A.restrict hAK) := by
  intro f hf
  obtain ⟨C, hC⟩ := hf.exists_norm_le
  have hb : Bornology.IsBounded (Set.range (fun n => (f n : E))) :=
    isBounded_iff_forall_norm_le.mpr ⟨C, by
      rintro _ ⟨n, rfl⟩
      exact hC (f n) ⟨n, rfl⟩⟩
  obtain ⟨φ, hφ, g, hg⟩ := hA (fun n => (f n : E)) hb
  have hgK : g ∈ K := hK.mem_of_tendsto hg (Filter.Eventually.of_forall
    (fun n => hAK (f (φ n)) (f (φ n)).property))
  exact ⟨φ, hφ, ⟨g, hgK⟩, tendsto_subtype_rng.mpr hg⟩

end TeschlODE.SturmLiouville.Proof

end
end

/- Complete module: CompactEigenpair -/
section

noncomputable section
open Filter Topology
namespace TeschlODE.SturmLiouville.Proof
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem normalize_eigenvector (A : E →ₗ[ℂ] E) (a : ℝ) (w : E)
    (hw : w ≠ 0) (he : A w = (a : ℂ) • w) :
    ∃ u : E, ‖u‖ = 1 ∧ A u = (a : ℂ) • u := by
  refine ⟨(‖w‖⁻¹ : ℂ) • w, norm_smul_inv_norm hw, ?_⟩
  rw [map_smul, he, smul_comm]

theorem clm_exists_unit_eigenpair_bound [Nontrivial E] (A : E →L[ℂ] E)
    (hA : IsCompactOp (A : E →ₗ[ℂ] E))
    (hsym : (A : E →ₗ[ℂ] E).IsSymmetric) :
    ∃ a : ℝ, ∃ u : E, ‖u‖ = 1 ∧ A u = (a : ℂ) • u ∧
      ∀ x, ‖A x‖ ≤ |a| * ‖x‖ := by
  by_cases hzero : ‖A‖ = 0
  · have hAz : A = 0 := norm_eq_zero.mp hzero
    obtain ⟨u, hu⟩ := NormedSpace.sphere_nonempty_rclike (𝕜 := ℂ) (E := E) zero_le_one
    refine ⟨0, u, mem_sphere_zero_iff_norm.mp hu, ?_, ?_⟩ <;> simp [hAz]
  have hc : 0 < ‖A‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hzero)
  obtain ⟨u, hu, heu⟩ := compact_square_unit_eigenvector A hA hsym hc
  let w : E := A u + (‖A‖ : ℂ) • u
  by_cases hw : w = 0
  · have he : A u = ((-‖A‖ : ℝ) : ℂ) • u := by
      have hh : A u + (‖A‖ : ℂ) • u = 0 := hw
      simpa using (eq_neg_of_add_eq_zero_left hh)
    refine ⟨-‖A‖, u, hu, he, ?_⟩
    intro x
    simpa only [abs_neg, abs_of_nonneg (norm_nonneg A)] using A.le_opNorm x
  · have he : A w = (‖A‖ : ℂ) • w := by
      simp only [w, map_add, map_smul, heu, Complex.ofReal_pow]
      module
    obtain ⟨v, hv, hev⟩ := normalize_eigenvector (A : E →ₗ[ℂ] E) ‖A‖ w hw he
    refine ⟨‖A‖, v, hv, hev, ?_⟩
    intro x
    simpa only [abs_of_nonneg (norm_nonneg A)] using A.le_opNorm x

theorem exists_unit_eigenpair_bound [Nontrivial E] (A : E →ₗ[ℂ] E)
    (hA : IsCompactOp A) (hsym : A.IsSymmetric) :
    ∃ a : ℝ, ∃ u : E, ‖u‖ = 1 ∧ A u = (a : ℂ) • u ∧
      ∀ x, ‖A x‖ ≤ |a| * ‖x‖ := by
  obtain ⟨C, _, hC⟩ := compact_bound A hA
  exact clm_exists_unit_eigenpair_bound (A.mkContinuous C hC) hA hsym

end TeschlODE.SturmLiouville.Proof

end
end

/- Complete module: SpectralDecay -/
section

open Filter Topology
namespace TeschlODE.SturmLiouville.Proof

/-- Compactness makes a decreasing sequence of orthogonal eigenvalues vanish. -/
theorem eigenvalues_tendsto_zero {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] (A : E →ₗ[ℂ] E) (hA : IsCompactOp A)
    (u : ℕ → E) (a : ℕ → ℝ) (hu : Orthonormal ℂ u)
    (he : ∀ n, A (u n) = (a n : ℂ) • u n)
    (ha : Antitone (fun n => |a n|)) : Tendsto a atTop (𝓝 0) := by
  have hb : Bornology.IsBounded (Set.range u) := by
    apply (Metric.isBounded_closedBall (x := (0 : E)) (r := 1)).subset
    rintro _ ⟨n,rfl⟩
    simp [Metric.mem_closedBall, dist_zero_right, hu.norm_eq_one]
  obtain ⟨φ,hφ,g,hg⟩ := hA u hb
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨N,hN⟩ := Metric.tendsto_atTop.mp hg (ε/2) (half_pos hε)
  have hdist : dist (A (u (φ N))) (A (u (φ (N+1)))) < ε := by
    have h1 := hN N le_rfl
    have h2 := hN (N+1) (Nat.le_succ N)
    have ht := dist_triangle (A (u (φ N))) g (A (u (φ (N+1))))
    rw [dist_comm g] at ht
    linarith
  have ho : inner ℂ (A (u (φ N))) (A (u (φ (N+1)))) = 0 := by
    rw [he,he,inner_smul_left,inner_smul_right,
      hu.inner_eq_zero (hφ.injective.ne (by omega)),mul_zero,mul_zero]
  have hs := @norm_sub_sq ℂ E _ _ _ (A (u (φ N))) (A (u (φ (N+1))))
  rw [ho] at hs
  simp only [map_zero, mul_zero, sub_zero] at hs
  have heN : ‖A (u (φ N))‖ = |a (φ N)| := by
    rw [he, norm_smul, hu.norm_eq_one, mul_one, Complex.norm_real, Real.norm_eq_abs]
  have hle : |a (φ N)| ≤ dist (A (u (φ N))) (A (u (φ (N+1)))) := by
    rw [dist_eq_norm, ← heN]
    nlinarith [norm_nonneg (A (u (φ N))), norm_nonneg (A (u (φ N))-A (u (φ (N+1)))),
      sq_nonneg ‖A (u (φ (N+1)))‖]
  refine ⟨φ N,fun n hn => ?_⟩
  simpa [Real.dist_eq] using (ha hn).trans_lt (hle.trans_lt hdist)

end TeschlODE.SturmLiouville.Proof

end

/- Complete module: CompactSequence -/
section

noncomputable section
open Filter Topology
namespace TeschlODE.SturmLiouville.Proof
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem exists_extension (A : E →ₗ[ℂ] E) (hA : IsCompactOp A)
    (hsym : A.IsSymmetric) (hE : ¬ FiniteDimensional ℂ E)
    (n : ℕ) (p : EigenPrefix A n) : Nonempty (EigenExtension p) := by
  let K := prefixComplement p.u
  have hK : IsClosed (K : Set E) := Submodule.isClosed_orthogonal _
  have hi : ∀ x ∈ K, A x ∈ K := prefixComplement_invariant A hsym p.u p.a p.eigen
  let : Nontrivial K := prefixComplement_nontrivial p.u hE
  obtain ⟨a,u,hu,he,hb⟩ := exists_unit_eigenpair_bound (A.restrict hi)
    (compact_restrict A hA K hK hi) (hsym.restrict_invariant hi)
  refine ⟨⟨u.val,a,hu,u.property,?_,?_⟩⟩
  · exact congrArg Subtype.val he
  · intro w hw
    exact hb ⟨w,hw⟩

/-- Countable maximal-modulus eigenvectors, constructed inside the original space. -/
theorem infinite_spectral_sequence (A : E →ₗ[ℂ] E) (hA : IsCompactOp A)
    (hsym : A.IsSymmetric) (hE : ¬ FiniteDimensional ℂ E) :
    ∃ (a : ℕ → ℝ) (u : ℕ → E), Orthonormal ℂ u ∧
      (∀ n, A (u n) = (a n : ℂ) • u n) ∧ Tendsto a atTop (𝓝 0) ∧
      (∀ n w, (∀ j < n, inner ℂ (u j) w = 0) → ‖A w‖ ≤ |a n| * ‖w‖) := by
  let next := fun n p => Classical.choice (exists_extension A hA hsym hE n p)
  refine ⟨valueSequence next,eigenSequence next,eigenSequence_orthonormal next,
    eigenSequence_eigen next,?_,eigenSequence_bound next⟩
  exact eigenvalues_tendsto_zero A hA _ _ (eigenSequence_orthonormal next)
    (eigenSequence_eigen next) (valueSequence_antitone next)

end TeschlODE.SturmLiouville.Proof

end
end

/- Complete module: SpectralExpansion -/
section

noncomputable section
open scoped BigOperators
open Filter Topology
namespace TeschlODE.SturmLiouville.Proof
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- Finite-rank orthogonal expansion operator for a sequence. -/
def partialProjection (u : ℕ → E) (n : ℕ) : E →ₗ[ℂ] E where
  toFun x := ∑ j ∈ Finset.range n, inner ℂ (u j) x • u j
  map_add' x y := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' c x := by simp [mul_smul, Finset.smul_sum]

theorem partialProjection_orthogonal (u : ℕ → E) (hu : Orthonormal ℂ u)
    (n : ℕ) (x : E) (j : ℕ) (hj : j < n) :
    inner ℂ (u j) (x-partialProjection u n x) = 0 := by
  change inner ℂ (u j) (x-∑ k ∈ Finset.range n, inner ℂ (u k) x • u k) = 0
  rw [inner_sub_right,hu.inner_right_sum _ (Finset.mem_range.mpr hj),sub_self]

theorem partialProjection_residual_bound (u : ℕ → E) (hu : Orthonormal ℂ u)
    (n : ℕ) (x : E) : ‖x-partialProjection u n x‖ ≤ ‖x‖ := by
  have ho : inner ℂ (partialProjection u n x) (x-partialProjection u n x) = 0 := by
    change inner ℂ (∑ j ∈ Finset.range n, inner ℂ (u j) x • u j) _ = 0
    rw [sum_inner]
    apply Finset.sum_eq_zero
    intro j hj
    rw [inner_smul_left,partialProjection_orthogonal u hu n x j (Finset.mem_range.mp hj),mul_zero]
  have hp := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero
    (partialProjection u n x) (x-partialProjection u n x) ho
  rw [add_sub_cancel] at hp
  nlinarith [norm_nonneg (x-partialProjection u n x), norm_nonneg x,
    sq_nonneg ‖partialProjection u n x‖]

theorem partialProjection_commute (A : E →ₗ[ℂ] E) (hsym : A.IsSymmetric)
    (u : ℕ → E) (a : ℕ → ℝ) (he : ∀ j, A (u j) = (a j : ℂ) • u j)
    (n : ℕ) (x : E) : partialProjection u n (A x) = A (partialProjection u n x) := by
  change (∑ j ∈ Finset.range n, inner ℂ (u j) (A x) • u j) =
    A (∑ j ∈ Finset.range n, inner ℂ (u j) x • u j)
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [← hsym,he,inner_smul_left,map_smul,he,smul_smul]
  simp [mul_comm]

theorem partialProjection_range_tendsto (A : E →ₗ[ℂ] E) (hsym : A.IsSymmetric)
    (u : ℕ → E) (a : ℕ → ℝ) (hu : Orthonormal ℂ u)
    (he : ∀ j, A (u j) = (a j : ℂ) • u j)
    (ha : Tendsto a atTop (𝓝 0))
    (hb : ∀ n x, (∀ j < n, inner ℂ (u j) x = 0) → ‖A x‖ ≤ |a n| *‖x‖)
    (g : E) : Tendsto (fun n => partialProjection u n (A g)) atTop (𝓝 (A g)) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero (g := fun n => |a n| * ‖g‖) (fun _ => norm_nonneg _)
  · intro n
    rw [norm_sub_rev,partialProjection_commute A hsym u a he,← map_sub]
    exact (hb n _ (partialProjection_orthogonal u hu n g)).trans
      (mul_le_mul_of_nonneg_left (partialProjection_residual_bound u hu n g) (abs_nonneg _))
  · simpa using ha.abs.mul_const ‖g‖

theorem partialProjection_dense_tendsto (A : E →ₗ[ℂ] E) (u : ℕ → E)
    (hu : Orthonormal ℂ u)
    (hlim : ∀ g, Tendsto (fun n => partialProjection u n (A g)) atTop (𝓝 (A g)))
    (hd : Dense (LinearMap.range A : Set E)) (x : E) :
    Tendsto (fun n => partialProjection u n x) atTop (𝓝 x) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨y,hy,hxy⟩ := Metric.mem_closure_iff.mp (hd x) (ε/2) (half_pos hε)
  obtain ⟨g,rfl⟩ := hy
  obtain ⟨N,hN⟩ := Metric.tendsto_atTop.mp (hlim g) (ε/2) (half_pos hε)
  refine ⟨N,fun n hn => ?_⟩
  have heq : x-partialProjection u n x =
      (x-A g)-partialProjection u n (x-A g) + (A g-partialProjection u n (A g)) := by
    rw [map_sub]
    abel
  have ht := norm_add_le ((x-A g)-partialProjection u n (x-A g))
    (A g-partialProjection u n (A g))
  rw [← heq] at ht
  have hb := partialProjection_residual_bound u hu n (x-A g)
  have hh := hN n hn
  rw [dist_eq_norm] at hxy hh ⊢
  rw [norm_sub_rev] at hh ⊢
  linarith

end TeschlODE.SturmLiouville.Proof

end
end

/- Complete module: FiniteSpectral -/
section

noncomputable section
open scoped BigOperators
open Filter Topology
namespace TeschlODE.SturmLiouville.Proof
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- Extend a finite orthonormal eigenbasis by arbitrary zero values outside its index set. -/
theorem finite_spectral_sequence [FiniteDimensional ℂ E]
    (A : E →ₗ[ℂ] E) (hsym : A.IsSymmetric) :
    ∃ (a : ℕ → ℝ) (u : ℕ → E),
      (∀ j : ℕ, j < Module.finrank ℂ E → A (u j) = (a j : ℂ) • u j) ∧
      Orthonormal ℂ (fun j : {j : ℕ // (j : ℕ∞) < (Module.finrank ℂ E : ℕ∞)} => u j) ∧
      (∀ x : E, Tendsto
        (fun n => ∑ j ∈ (Finset.range n).filter (fun j : ℕ => (j : ℕ∞) < (Module.finrank ℂ E : ℕ∞)),
          inner ℂ (u j) x • u j) atTop (𝓝 x)) := by
  classical
  let d := Module.finrank ℂ E
  let b := hsym.eigenvectorBasis (n := d) rfl
  let a : ℕ → ℝ := fun j => if h : j < d then hsym.eigenvalues rfl ⟨j,h⟩ else 0
  let u : ℕ → E := fun j => if h : j < d then b ⟨j,h⟩ else 0
  refine ⟨a,u,?_,?_,?_⟩
  · intro j hj
    change j < d at hj
    simp only [a,u,dif_pos hj]
    exact hsym.apply_eigenvectorBasis (n := d) rfl ⟨j,hj⟩
  · let e : {j : ℕ // (j : ℕ∞) < (d : ℕ∞)} → Fin d := fun j =>
      ⟨j.val,ENat.natCast_lt_natCast.mp j.property⟩
    have he : Function.Injective e := by
      intro i j hij
      exact Subtype.ext (congrArg Fin.val hij)
    have hh := b.orthonormal.comp e he
    convert hh using 1
    funext j
    have hj : j.val < d := ENat.natCast_lt_natCast.mp j.property
    simp only [u,dif_pos hj,Function.comp_apply,e]
  · intro x
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop d] with n hn
    have hfilter : (Finset.range n).filter (fun j : ℕ => (j : ℕ∞) < (d : ℕ∞)) =
        Finset.range d := by
      ext j
      simp only [Finset.mem_filter,Finset.mem_range,ENat.natCast_lt_natCast]
      omega
    rw [hfilter,← Fin.sum_univ_eq_sum_range]
    have hh := b.sum_repr' x
    simpa [u] using hh.symm

end TeschlODE.SturmLiouville.Proof

end
end

/- Complete module: SpectralRoot -/
section

namespace TeschlODE.SturmLiouville

/-- Teschl, Theorem 5.6 (spectral theorem for compact symmetric operators), p. 151: let `H₀` be
a complex inner product space and `A : H₀ → H₀` compact and symmetric. There are `N ∈ ℕ₀ ∪ {∞}`,
real eigenvalues `αⱼ` and normalized eigenvectors `uⱼ` (`j < N`) forming an orthonormal set,
with `N = ∞` when `H₀` is infinite dimensional (and `N = dim H₀` otherwise) and `αⱼ → 0` when
`N = ∞`, such that every `f ∈ Ran(A)` satisfies `f = Σ_{j<N} ⟨uⱼ, f⟩ uⱼ` (5.42), the partial sums
converging in `H₀`; if `Ran(A)` is dense, the `uⱼ` form an orthonormal basis, i.e. the same
expansion holds for every `f ∈ H₀` (5.34). -/
theorem spectral_theorem_compact_symmetric {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] (A : E →ₗ[ℂ] E) (hA : IsCompactOp A) (hsym : A.IsSymmetric) :
    ∃ (N : ℕ∞) (α : ℕ → ℝ) (u : ℕ → E),
      (FiniteDimensional ℂ E → N = (Module.finrank ℂ E : ℕ∞)) ∧
      (¬ FiniteDimensional ℂ E → N = ⊤) ∧
      (∀ j : ℕ, (j : ℕ∞) < N → A (u j) = (α j : ℂ) • u j) ∧
      Orthonormal ℂ (fun j : {j : ℕ // (j : ℕ∞) < N} => u j) ∧
      (N = ⊤ → Filter.Tendsto α Filter.atTop (nhds 0)) ∧
      (∀ f ∈ LinearMap.range A,
        Filter.Tendsto
          (fun n => ∑ j ∈ (Finset.range n).filter (fun j : ℕ => (j : ℕ∞) < N),
            inner ℂ (u j) f • u j) Filter.atTop (nhds f)) ∧
      (Dense (LinearMap.range A : Set E) → ∀ f : E,
        Filter.Tendsto
          (fun n => ∑ j ∈ (Finset.range n).filter (fun j : ℕ => (j : ℕ∞) < N),
            inner ℂ (u j) f • u j) Filter.atTop (nhds f)) := by
  classical
  by_cases hE : FiniteDimensional ℂ E
  · let : FiniteDimensional ℂ E := hE
    obtain ⟨a,u,he,hu,hl⟩ := Proof.finite_spectral_sequence A hsym
    refine ⟨(Module.finrank ℂ E : ℕ∞),a,u,fun _ => rfl,
      (fun h => (h hE).elim),?_,hu,?_,?_,?_⟩
    · intro j hj
      exact he j (ENat.natCast_lt_natCast.mp hj)
    · intro ht
      exact (ENat.natCast_ne_top _ ht).elim
    · intro f _
      exact hl f
    · intro _ f
      exact hl f
  · obtain ⟨a,u,hu,he,ha,hb⟩ := Proof.infinite_spectral_sequence A hA hsym hE
    refine ⟨⊤,a,u,(fun h => (hE h).elim),fun _ => rfl,
      (fun j _ => he j),?_,(fun _ => ha),?_,?_⟩
    · exact hu.comp Subtype.val Subtype.val_injective
    · rintro f ⟨g,rfl⟩
      simpa [Proof.partialProjection] using
        Proof.partialProjection_range_tendsto A hsym u a hu he ha hb g
    · intro hd f
      simpa [Proof.partialProjection] using
        Proof.partialProjection_dense_tendsto A u hu
          (Proof.partialProjection_range_tendsto A hsym u a hu he ha hb) hd f


end TeschlODE.SturmLiouville

theorem solution {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] (A : E →ₗ[ℂ] E) (hA : TeschlODE.SturmLiouville.IsCompactOp A) (hsym : A.IsSymmetric) :
    ∃ (N : ℕ∞) (α : ℕ → ℝ) (u : ℕ → E),
      (FiniteDimensional ℂ E → N = (Module.finrank ℂ E : ℕ∞)) ∧
      (¬ FiniteDimensional ℂ E → N = ⊤) ∧
      (∀ j : ℕ, (j : ℕ∞) < N → A (u j) = (α j : ℂ) • u j) ∧
      Orthonormal ℂ (fun j : {j : ℕ // (j : ℕ∞) < N} => u j) ∧
      (N = ⊤ → Filter.Tendsto α Filter.atTop (nhds 0)) ∧
      (∀ f ∈ LinearMap.range A,
        Filter.Tendsto
          (fun n => ∑ j ∈ (Finset.range n).filter (fun j : ℕ => (j : ℕ∞) < N),
            inner ℂ (u j) f • u j) Filter.atTop (nhds f)) ∧
      (Dense (LinearMap.range A : Set E) → ∀ f : E,
        Filter.Tendsto
          (fun n => ∑ j ∈ (Finset.range n).filter (fun j : ℕ => (j : ℕ∞) < N),
            inner ℂ (u j) f • u j) Filter.atTop (nhds f)) := by
  exact TeschlODE.SturmLiouville.spectral_theorem_compact_symmetric A hA hsym

end
