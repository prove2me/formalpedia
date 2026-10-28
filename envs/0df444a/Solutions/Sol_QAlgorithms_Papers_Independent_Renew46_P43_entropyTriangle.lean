-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Renew46.P43.entropyTriangle
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T22:21:29.840174+00:00
-- url     : https://prove2.me/submissions/c0fe27e8-79f1-4d80-a43f-8105d96b3bb5

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P43
import Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P20_strongSubadditivity

noncomputable section
open scoped Matrix ComplexConjugate ComplexOrder

set_option linter.unusedSectionVars false

section S193T_ent
open Matrix Polynomial

lemma S193T_spec_finite {ι : Type*} [Fintype ι] {inst : DecidableEq ι} (A : Matrix ι ι ℂ)
    (hA : A.IsHermitian) : (spectrum ℝ A).Finite := by
  rw [hA.spectrum_real_eq_range_eigenvalues]; exact Set.finite_range _

lemma S193T_vn_poly {ι : Type*} [Fintype ι] {inst : DecidableEq ι} (A : Matrix ι ι ℂ)
    (hA : A.IsHermitian) (p : ℝ[X])
    (hp : ∀ x ∈ spectrum ℝ A, p.eval x = x * Real.logb 2 x) :
    QAlgorithms.vnEntropy A = -(aeval A p).trace.re := by
  unfold QAlgorithms.vnEntropy
  rw [cfc_congr (g := fun x => p.eval x) (fun x hx => (hp x hx).symm),
    cfc_polynomial p A hA.isSelfAdjoint]

/-- interpolation polynomial of x log x on a finite set -/
def S193T_interp (s : Finset ℝ) : ℝ[X] :=
  Lagrange.interpolate s id (fun x => x * Real.logb 2 x)

lemma S193T_interp_eval (s : Finset ℝ) {x : ℝ} (hx : x ∈ s) :
    (S193T_interp s).eval x = x * Real.logb 2 x :=
  Lagrange.eval_interpolate_at_node (v := id) _ (Set.injOn_id _) hx

lemma S193T_vn_submatrix {ι κ : Type*} [Fintype ι] [Fintype κ] {inst : DecidableEq ι}
    {inst' : DecidableEq κ} (A : Matrix ι ι ℂ) (hA : A.IsHermitian) (e : κ ≃ ι) :
    QAlgorithms.vnEntropy (A.submatrix e e) = QAlgorithms.vnEntropy A := by
  set s := (S193T_spec_finite A hA).toFinset
  have hsub : A.submatrix e e = Matrix.reindexAlgEquiv ℝ ℂ e.symm A := by
    ext a b; simp [Matrix.coe_reindexAlgEquiv]
  have hspec : spectrum ℝ (A.submatrix e e) = spectrum ℝ A := by
    rw [hsub]; exact AlgEquiv.spectrum_eq _ _
  rw [S193T_vn_poly A hA (S193T_interp s) (fun x hx => S193T_interp_eval s (by simpa [s] using hx)),
    S193T_vn_poly _ (hA.submatrix e) (S193T_interp s)
      (fun x hx => S193T_interp_eval s (by rw [hspec] at hx; simpa [s] using hx))]
  rw [hsub, Polynomial.aeval_algEquiv, AlgHom.comp_apply]
  congr 2
  simp only [AlgEquiv.coe_toAlgHom, Matrix.coe_reindexAlgEquiv, Matrix.reindex_apply,
    Equiv.symm_symm, Matrix.trace, Matrix.diag, Matrix.submatrix_apply]
  exact e.sum_comp (fun i => (aeval A (S193T_interp s)) i i)

lemma S193T_vn_conj {ι : Type*} [Fintype ι] {inst : DecidableEq ι} (A : Matrix ι ι ℂ)
    (hA : A.IsHermitian) :
    QAlgorithms.vnEntropy (A.map (starRingEnd ℂ)) = QAlgorithms.vnEntropy A := by
  set s := (S193T_spec_finite A hA).toFinset
  set φ : Matrix ι ι ℂ ≃ₐ[ℝ] Matrix ι ι ℂ := AlgEquiv.mapMatrix Complex.conjAe
  have hφ : A.map (starRingEnd ℂ) = φ A := rfl
  have hspec : spectrum ℝ (A.map (starRingEnd ℂ)) = spectrum ℝ A := by
    rw [hφ]; exact AlgEquiv.spectrum_eq _ _
  have hH : (A.map (starRingEnd ℂ)).IsHermitian := by
    ext i j; have := congrFun (congrFun hA i) j
    simp only [conjTranspose_apply, map_apply] at this ⊢
    rw [← this]; simp
  rw [S193T_vn_poly A hA (S193T_interp s) (fun x hx => S193T_interp_eval s (by simpa [s] using hx)),
    S193T_vn_poly _ hH (S193T_interp s)
      (fun x hx => S193T_interp_eval s (by rw [hspec] at hx; simpa [s] using hx))]
  rw [hφ, Polynomial.aeval_algEquiv, AlgHom.comp_apply]
  have htr : ∀ X : Matrix ι ι ℂ, (φ X).trace = starRingEnd ℂ X.trace := by
    intro X
    simp only [φ, AlgEquiv.mapMatrix_apply, Matrix.trace, Matrix.diag, Matrix.map_apply, map_sum]
    rfl
  simp only [AlgEquiv.coe_toAlgHom]
  rw [htr, Complex.conj_re]

lemma S193T_pow_mul {κ ι : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (M : Matrix κ ι ℂ) (N : Matrix ι κ ℂ) (k : ℕ) :
    (M * N) ^ (k + 1) = M * (N * M) ^ k * N := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, ih, pow_succ]; simp only [Matrix.mul_assoc]

lemma S193T_tr_pow {κ ι : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (M : Matrix κ ι ℂ) (N : Matrix ι κ ℂ) (k : ℕ) :
    ((M * N) ^ (k + 1)).trace = ((N * M) ^ (k + 1)).trace := by
  rw [S193T_pow_mul, Matrix.mul_assoc, Matrix.trace_mul_comm, Matrix.mul_assoc, pow_succ]

lemma S193T_vn_mul_comm {κ ι : Type*} [Fintype ι] [Fintype κ] {inst : DecidableEq ι}
    {inst' : DecidableEq κ} (M : Matrix κ ι ℂ) :
    QAlgorithms.vnEntropy (M * Mᴴ) = QAlgorithms.vnEntropy (Mᴴ * M) := by
  have h1 : (M * Mᴴ).IsHermitian := isHermitian_mul_conjTranspose_self M
  have h2 : (Mᴴ * M).IsHermitian := isHermitian_conjTranspose_mul_self M
  set s : Finset ℝ := insert 0 ((S193T_spec_finite (inst := inst') _ h1).toFinset ∪
    (S193T_spec_finite (inst := inst) _ h2).toFinset)
  set p := S193T_interp s
  rw [S193T_vn_poly _ h1 p (fun x hx => S193T_interp_eval s (by simp [s, hx])),
    S193T_vn_poly _ h2 p (fun x hx => S193T_interp_eval s (by simp [s, hx]))]
  have h0 : p.coeff 0 = 0 := by
    rw [Polynomial.coeff_zero_eq_eval_zero, S193T_interp_eval s (by simp [s])]; simp
  congr 2
  rw [Polynomial.aeval_eq_sum_range, Polynomial.aeval_eq_sum_range, Matrix.trace_sum,
    Matrix.trace_sum, Finset.sum_range_succ', Finset.sum_range_succ']
  simp only [h0, zero_smul, Matrix.trace_zero, add_zero, Matrix.trace_smul]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [S193T_tr_pow]

end S193T_ent

section S193T_marg
open Matrix
open scoped Classical
open QAlgorithms.Papers.Independent.Gap48.P20 (redistributionMarginal)

def S193T_pure {Y : Type*} (Ψ : Y → ℂ) : Matrix Y Y ℂ := Matrix.of fun a b => Ψ a * conj (Ψ b)

def S193T_M {Y K F : Type*} [Fintype Y] (Ψ : Y → ℂ) (k : Y → K) (f : Y → F) : Matrix K F ℂ :=
  fun a z => ∑ y, if k y = a ∧ f y = z then Ψ y else 0

lemma S193T_pure_marg {Y K F : Type*} [Fintype Y] [Fintype F] (Ψ : Y → ℂ) (k : Y → K)
    (f : Y → F) : redistributionMarginal (S193T_pure Ψ) k f =
      S193T_M Ψ k f * (S193T_M Ψ k f)ᴴ := by
  ext a b
  simp only [redistributionMarginal, Matrix.mul_apply, Matrix.conjTranspose_apply, S193T_M,
    S193T_pure, Matrix.of_apply, star_sum, Finset.sum_mul_sum]
  symm
  rw [Finset.sum_comm]; refine Finset.sum_congr rfl (fun x _ => ?_)
  rw [Finset.sum_comm]; refine Finset.sum_congr rfl (fun y _ => ?_)
  rw [Finset.sum_eq_single (f x)]
  · by_cases h1 : k x = a <;> by_cases h2 : k y = b <;> by_cases h3 : f x = f y <;>
      simp [h1, h2, h3, eq_comm (a := f y)]
  · intro z _ hz; simp [Ne.symm hz]
  · simp

lemma S193T_ite_sum {α : Type*} (s : Finset α) (c : Prop) [Decidable c] (g : α → ℂ) :
    (if c then ∑ i ∈ s, g i else 0) = ∑ i ∈ s, if c then g i else 0 := by
  split_ifs <;> simp

lemma S193T_marg_comp {Y K F K2 F2 : Type*} [Fintype Y] [Fintype K] (ρ : Matrix Y Y ℂ)
    (k : Y → K) (f : Y → F) (k2 : K → K2) (f2 : K → F2) :
    redistributionMarginal (redistributionMarginal ρ k f) k2 f2 =
      redistributionMarginal ρ (k2 ∘ k) (fun y => (f2 (k y), f y)) := by
  ext a b
  simp only [redistributionMarginal, S193T_ite_sum, Function.comp]
  rw [Finset.sum_congr rfl (fun u _ => Finset.sum_comm)]
  rw [Finset.sum_congr rfl (fun u _ => Finset.sum_congr rfl (fun x _ => Finset.sum_comm))]
  rw [Finset.sum_comm]
  rw [Finset.sum_congr rfl (fun x _ => Finset.sum_comm)]
  refine Finset.sum_congr rfl (fun x _ => Finset.sum_congr rfl (fun y _ => ?_))
  rw [Finset.sum_eq_single (k x)]
  · rw [Finset.sum_eq_single (k y)]
    · by_cases h1 : k2 (k x) = a <;> by_cases h2 : k2 (k y) = b <;>
        by_cases h3 : f2 (k x) = f2 (k y) <;> by_cases h4 : f x = f y <;> simp [h1, h2, h3, h4]
    · intro v _ hv; simp [Ne.symm hv]
    · simp
  · intro u _ hu
    apply Finset.sum_eq_zero; intro v _; simp [Ne.symm hu]
  · simp


lemma S193T_marg_forget {Y K F F' : Type*} [Fintype Y] (ρ : Matrix Y Y ℂ) (k : Y → K)
    (f : Y → F) (f' : Y → F') (hf : ∀ x y, f x = f y ↔ f' x = f' y) :
    redistributionMarginal ρ k f = redistributionMarginal ρ k f' := by
  ext a b
  simp only [redistributionMarginal]
  refine Finset.sum_congr rfl (fun x _ => Finset.sum_congr rfl (fun y _ => ?_))
  simp only [hf x y]

lemma S193T_vn_keep {Y K K' F : Type*} [Fintype Y] [Fintype K] [Fintype K']
    {inst : DecidableEq K} {inst' : DecidableEq K'} (ρ : Matrix Y Y ℂ) (k : Y → K)
    (k' : Y → K') (f : Y → F) (hk : ∀ x y, k x = k y ↔ k' x = k' y)
    (hs : Function.Surjective k) (hs' : Function.Surjective k')
    (hH : (redistributionMarginal ρ k' f).IsHermitian) :
    QAlgorithms.vnEntropy (redistributionMarginal ρ k f) =
      QAlgorithms.vnEntropy (redistributionMarginal ρ k' f) := by
  set g : K → K' := fun a => k' (Function.surjInv hs a) with hg
  have hgk : ∀ x a, k' x = g a ↔ k x = a := by
    intro x a
    have := hk x (Function.surjInv hs a)
    rw [Function.surjInv_eq hs a] at this
    exact this.symm
  have hb : Function.Bijective g := by
    constructor
    · intro a b hab
      have h1 := (hgk (Function.surjInv hs a) b).1 hab
      rwa [Function.surjInv_eq hs a] at h1
    · intro c
      obtain ⟨y, rfl⟩ := hs' c
      exact ⟨k y, ((hgk y (k y)).2 rfl).symm⟩
  have hsub : (redistributionMarginal ρ k' f).submatrix (Equiv.ofBijective g hb)
      (Equiv.ofBijective g hb) = redistributionMarginal ρ k f := by
    ext a b
    simp only [Matrix.submatrix_apply, Equiv.ofBijective_apply, redistributionMarginal]
    refine Finset.sum_congr rfl (fun x _ => Finset.sum_congr rfl (fun y _ => ?_))
    by_cases h : k x = a ∧ k y = b ∧ f x = f y
    · rw [if_pos (by rwa [hgk, hgk]), if_pos h]
    · rw [if_neg (by rwa [hgk, hgk]), if_neg h]
  rw [← hsub, S193T_vn_submatrix _ hH]

lemma S193T_pure_herm {Y K F : Type*} [Fintype Y] [Fintype F] (Ψ : Y → ℂ) (k : Y → K)
    (f : Y → F) : (redistributionMarginal (S193T_pure Ψ) k f).IsHermitian := by
  rw [S193T_pure_marg]; exact isHermitian_mul_conjTranspose_self _

lemma S193T_vn_swap {Y K F : Type*} [Fintype Y] [Fintype K] [Fintype F]
    {inst : DecidableEq K} {inst' : DecidableEq F} (Ψ : Y → ℂ) (k : Y → K) (f : Y → F) :
    QAlgorithms.vnEntropy (redistributionMarginal (S193T_pure Ψ) k f) =
      QAlgorithms.vnEntropy (redistributionMarginal (S193T_pure Ψ) f k) := by
  rw [S193T_pure_marg, S193T_pure_marg]
  set M := S193T_M Ψ k f
  have hN : S193T_M Ψ f k * (S193T_M Ψ f k)ᴴ = (Mᴴ * M).map (starRingEnd ℂ) := by
    ext z w
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.map_apply, map_sum, map_mul,
      M, S193T_M]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    simp only [and_comm, RCLike.star_def, Complex.conj_conj, map_sum]
    congr 1
    · refine Finset.sum_congr rfl (fun y _ => ?_)
      by_cases h : k y = a ∧ f y = z
      · rw [if_pos h, if_pos h]
      · rw [if_neg h, if_neg h]
    · refine Finset.sum_congr rfl (fun y _ => ?_)
      by_cases h : k y = a ∧ f y = w
      · rw [if_pos h, if_pos h]
      · rw [if_neg h, if_neg h]
  rw [hN, S193T_vn_conj _ (isHermitian_conjTranspose_mul_self M), S193T_vn_mul_comm]

lemma S193T_marg_trace {Y K F : Type*} [Fintype Y] [Fintype K] (ρ : Matrix Y Y ℂ)
    (k : Y → K) (f : Y → F) (hinj : Function.Injective (fun y => (k y, f y))) :
    (redistributionMarginal ρ k f).trace = ρ.trace := by
  simp only [Matrix.trace, Matrix.diag, redistributionMarginal]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  rw [Finset.sum_comm, Finset.sum_eq_single x]
  · rw [Finset.sum_eq_single (k x)]
    · simp
    · intro b _ hb; simp [Ne.symm hb]
    · simp
  · intro y _ hy
    apply Finset.sum_eq_zero; intro a _
    rw [if_neg]; rintro ⟨h1, h2, h3⟩
    exact hy (hinj (Prod.ext (h2.trans h1.symm) h3.symm))
  · simp

lemma S193T_pure_density {Y K F : Type*} [Fintype Y] [Fintype K] [Fintype F] (Ψ : Y → ℂ)
    (hΨ : (S193T_pure Ψ).trace = 1) (k : Y → K) (f : Y → F)
    (hinj : Function.Injective (fun y => (k y, f y))) :
    QAlgorithms.IsDensityMatrix (redistributionMarginal (S193T_pure Ψ) k f) := by
  refine ⟨?_, ?_⟩
  · rw [S193T_pure_marg]; exact posSemidef_self_mul_conjTranspose _
  · rw [S193T_marg_trace _ _ _ hinj, hΨ]

lemma S193T_vn_unit {inst : DecidableEq Unit} (A : Matrix Unit Unit ℂ) (h : A.trace = 1) :
    QAlgorithms.vnEntropy A = 0 := by
  have : A = 1 := by
    ext a b; cases a; cases b; simpa [Matrix.trace] using h
  rw [this]; simp [QAlgorithms.vnEntropy]
end S193T_marg

section S193T_bridge
open Matrix
open QAlgorithms.Papers.Independent.Gap48.P20 (redistributionMarginal)

lemma S193T_purify {X : Type*} [Fintype X] [DecidableEq X] (ρ : Matrix X X ℂ)
    (hρ : ρ.PosSemidef) : ∃ Ψ : X × X → ℂ,
      redistributionMarginal (S193T_pure Ψ) Prod.fst Prod.snd = ρ := by
  set U : Matrix X X ℂ := (hρ.1.eigenvectorUnitary : Matrix X X ℂ)
  set lam := hρ.1.eigenvalues
  refine ⟨fun y => U y.1 y.2 * ((Real.sqrt (lam y.2) : ℝ) : ℂ), ?_⟩
  rw [S193T_pure_marg]
  have hM : S193T_M (fun y : X × X => U y.1 y.2 * ((Real.sqrt (lam y.2) : ℝ) : ℂ))
      Prod.fst Prod.snd = U * diagonal (fun j => ((Real.sqrt (lam j) : ℝ) : ℂ)) := by
    ext a j
    simp only [S193T_M, mul_diagonal]
    rw [Finset.sum_eq_single (a, j)]
    · simp
    · intro y _ hy; rw [if_neg]; rintro ⟨h1, h2⟩; exact hy (Prod.ext h1 h2)
    · simp
  rw [hM]
  have hsp := hρ.1.spectral_theorem
  rw [Unitary.conjStarAlgAut_apply] at hsp
  conv_rhs => rw [hsp]
  rw [conjTranspose_mul, diagonal_conjTranspose, Matrix.mul_assoc, ← Matrix.mul_assoc (diagonal _),
    diagonal_mul_diagonal, ← Matrix.mul_assoc]
  congr 2
  · congr 1; funext j
    simp only [Function.comp, Pi.star_apply, RCLike.star_def, Complex.conj_ofReal]
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (hρ.eigenvalues_nonneg j)]
    rfl

end S193T_bridge

section S193T_AL
open Matrix
open QAlgorithms.Papers.Independent.Gap48.P20 (redistributionMarginal subsystemEntropy)

lemma S193T_vn_eq {Y K K' F F' : Type*} [Fintype Y] [Fintype K] [Fintype K'] [Fintype F']
    {inst : DecidableEq K} {inst' : DecidableEq K'} (Ψ : Y → ℂ) (k : Y → K) (f : Y → F)
    (k' : Y → K') (f' : Y → F') (hk : ∀ x y, k x = k y ↔ k' x = k' y)
    (hs : Function.Surjective k) (hs' : Function.Surjective k')
    (hf : ∀ x y, f x = f y ↔ f' x = f' y) :
    QAlgorithms.vnEntropy (redistributionMarginal (S193T_pure Ψ) k f) =
      QAlgorithms.vnEntropy (redistributionMarginal (S193T_pure Ψ) k' f') := by
  rw [S193T_marg_forget _ k f f' hf]
  exact S193T_vn_keep _ k k' f' hk hs hs' (S193T_pure_herm _ _ _)


def S193T_S {ι : Type*} [Fintype ι] (A : Matrix ι ι ℂ) : ℝ :=
  @QAlgorithms.vnEntropy ι _ (Classical.decEq ι) A

lemma S193T_toS {ι : Type*} [Fintype ι] (i : DecidableEq ι) (A : Matrix ι ι ℂ) :
    @QAlgorithms.vnEntropy ι _ i A = S193T_S A := by
  unfold S193T_S; congr

lemma S193T_AL1 {α β : Type*} [Fintype α] [Fintype β] [Nonempty α] [Nonempty β]
    {ia : DecidableEq α} {ib : DecidableEq β} {iab : DecidableEq (α × β)}
    (ρ : Matrix (α × β) (α × β) ℂ) (hρ : QAlgorithms.IsDensityMatrix ρ) :
    QAlgorithms.vnEntropy (redistributionMarginal ρ Prod.fst Prod.snd) ≤
      QAlgorithms.vnEntropy (redistributionMarginal ρ Prod.snd Prod.fst) +
        QAlgorithms.vnEntropy ρ := by
  classical
  obtain ⟨Ψ, hΨ⟩ := S193T_purify ρ hρ.1
  have hinj0 : Function.Injective (fun y : (α × β) × (α × β) => (y.1, y.2)) := by
    intro y y' h; simpa using h
  have htr : (S193T_pure Ψ).trace = 1 := by
    rw [← S193T_marg_trace _ Prod.fst Prod.snd hinj0, hΨ, hρ.2]
  subst hΨ
  rw [S193T_marg_comp, S193T_marg_comp]
  set k : (α × β) × (α × β) → β × ((α × β) × Unit) := fun y => (y.1.2, (y.2, ())) with hk
  set f : (α × β) × (α × β) → α := fun y => y.1.1 with hf
  have hinj : Function.Injective (fun y => (k y, f y)) := by
    intro y y' h
    simp only [hk, hf, Prod.mk.injEq, and_true] at h
    obtain ⟨⟨h1, h2⟩, h3⟩ := h
    exact Prod.ext (Prod.ext h3 h1) h2
  have hssa := QAlgorithms.Papers.Independent.Gap48.P20.strongSubadditivity
    (redistributionMarginal (S193T_pure Ψ) k f) (S193T_pure_density Ψ htr k f hinj)
  unfold subsystemEntropy at hssa
  rw [S193T_marg_comp, S193T_marg_comp, S193T_marg_comp] at hssa
  obtain ⟨a0⟩ : Nonempty α := inferInstance
  obtain ⟨b0⟩ : Nonempty β := inferInstance
  have h1 : QAlgorithms.vnEntropy (redistributionMarginal (S193T_pure Ψ)
      ((fun p : β × ((α × β) × Unit) => (p.1, p.2.2)) ∘ k)
      (fun y => ((fun p : β × ((α × β) × Unit) => p.2.1) (k y), f y))) =
      QAlgorithms.vnEntropy (redistributionMarginal (S193T_pure Ψ) (Prod.snd ∘ Prod.fst)
        (fun y => (Prod.fst (Prod.fst y), Prod.snd y))) := by
    apply S193T_vn_eq
    · intro y y'; simp [hk]
    · rintro ⟨b, u⟩; exact ⟨((a0, b), (a0, b0)), rfl⟩
    · intro b; exact ⟨((a0, b), (a0, b0)), rfl⟩
    · intro y y'; simp [hk, hf]; tauto
  have h2 : QAlgorithms.vnEntropy (redistributionMarginal (S193T_pure Ψ)
      ((fun p : β × ((α × β) × Unit) => p.2) ∘ k)
      (fun y => ((fun p : β × ((α × β) × Unit) => p.1) (k y), f y))) =
      QAlgorithms.vnEntropy (redistributionMarginal (S193T_pure Ψ) Prod.fst Prod.snd) := by
    rw [S193T_vn_swap (inst' := iab) Ψ Prod.fst Prod.snd]
    apply S193T_vn_eq
    · intro y y'; simp [hk]
    · rintro ⟨e, u⟩; exact ⟨((a0, b0), e), rfl⟩
    · intro e; exact ⟨((a0, b0), e), rfl⟩
    · intro y y'; simp [hk, hf]
      constructor
      · rintro ⟨h1, h2⟩; exact Prod.ext h2 h1
      · intro h; rw [h]; exact ⟨rfl, rfl⟩
  have h3 : QAlgorithms.vnEntropy (redistributionMarginal (S193T_pure Ψ)
      ((fun p : β × ((α × β) × Unit) => p.2.2) ∘ k)
      (fun y => ((fun p : β × ((α × β) × Unit) => (p.1, p.2.1)) (k y), f y))) = 0 := by
    apply S193T_vn_unit
    rw [S193T_marg_trace, htr]
    intro y y' h
    simp only [hk, hf, Function.comp, Prod.mk.injEq, true_and] at h
    obtain ⟨⟨h1, h2⟩, h3⟩ := h
    exact Prod.ext (Prod.ext h3 h1) h2
  have h4 : QAlgorithms.vnEntropy (redistributionMarginal (S193T_pure Ψ) k f) =
      QAlgorithms.vnEntropy (redistributionMarginal (S193T_pure Ψ) (Prod.fst ∘ Prod.fst)
        (fun y => (Prod.snd (Prod.fst y), Prod.snd y))) := by
    rw [S193T_vn_swap (inst' := ia) Ψ k f]
    apply S193T_vn_eq
    · intro y y'; simp [hf]
    · intro a; exact ⟨((a, b0), (a0, b0)), rfl⟩
    · intro a; exact ⟨((a, b0), (a0, b0)), rfl⟩
    · intro y y'; simp [hk]
  beta_reduce at h1 h2 h3
  simp only [S193T_toS] at hssa h1 h2 h3 h4 ⊢
  rw [h1, h2, h3, h4] at hssa
  linarith

lemma S193T_AL2 {α β : Type*} [Fintype α] [Fintype β] [Nonempty α] [Nonempty β]
    {ia : DecidableEq α} {ib : DecidableEq β} {iab : DecidableEq (α × β)}
    (ρ : Matrix (α × β) (α × β) ℂ) (hρ : QAlgorithms.IsDensityMatrix ρ) :
    QAlgorithms.vnEntropy (redistributionMarginal ρ Prod.snd Prod.fst) ≤
      QAlgorithms.vnEntropy (redistributionMarginal ρ Prod.fst Prod.snd) +
        QAlgorithms.vnEntropy ρ := by
  classical
  set e : β × α ≃ α × β := Equiv.prodComm β α
  have hd : QAlgorithms.IsDensityMatrix (ρ.submatrix e e) := by
    refine ⟨hρ.1.submatrix _, ?_⟩
    rw [← hρ.2]; simp only [Matrix.trace, Matrix.diag, Matrix.submatrix_apply]
    exact e.sum_comp (fun i => ρ i i)
  have hm1 : redistributionMarginal (ρ.submatrix e e) Prod.fst Prod.snd =
      redistributionMarginal ρ Prod.snd Prod.fst := by
    ext a b
    simp only [redistributionMarginal, Matrix.submatrix_apply]
    rw [← e.sum_comp]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    rw [← e.sum_comp]
    rfl
  have hm2 : redistributionMarginal (ρ.submatrix e e) Prod.snd Prod.fst =
      redistributionMarginal ρ Prod.fst Prod.snd := by
    ext a b
    simp only [redistributionMarginal, Matrix.submatrix_apply]
    rw [← e.sum_comp]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    rw [← e.sum_comp]
    rfl
  have := S193T_AL1 (ia := ib) (ib := ia) (iab := inferInstance) (ρ.submatrix e e) hd
  rw [hm1, hm2, S193T_vn_submatrix ρ hρ.1.1 e] at this
  exact this

end S193T_AL

section S193T_joint
open Matrix
open QAlgorithms.Papers.Independent.Gap48.P20 (redistributionMarginal)
open QAlgorithms.Papers.Independent.Renew46.P43
open QAlgorithms.Papers.Independent.Claimed50.P40 (InBlocks)

lemma S193T_single_mem {d : ℕ} (blk : Fin d → ℕ) {i j : Fin d} (h : blk i = blk j) :
    InBlocks blk (Matrix.single i j (1 : ℂ)) := by
  intro a b hab
  rw [Matrix.single_apply, if_neg]
  rintro ⟨rfl, rfl⟩; exact hab h

def S193T_lead {d : ℕ} (blk : Fin d → ℕ) (i : Fin d) : Fin d :=
  @Classical.epsilon (Fin d) ⟨i⟩ (fun j => blk j = blk i)

lemma S193T_lead_blk {d : ℕ} (blk : Fin d → ℕ) (i : Fin d) : blk (S193T_lead blk i) = blk i :=
  @Classical.epsilon_spec (Fin d) (fun j => blk j = blk i) ⟨i, rfl⟩

lemma S193T_lead_iff {d : ℕ} (blk : Fin d → ℕ) (i j : Fin d) :
    S193T_lead blk i = S193T_lead blk j ↔ blk i = blk j := by
  constructor
  · intro h
    calc blk i = blk (S193T_lead blk i) := (S193T_lead_blk blk i).symm
      _ = blk (S193T_lead blk j) := by rw [h]
      _ = blk j := S193T_lead_blk blk j
  · intro h
    show @Classical.epsilon (Fin d) ⟨i⟩ (fun k => blk k = blk i) =
      @Classical.epsilon (Fin d) ⟨i⟩ (fun k => blk k = blk j)
    rw [h]

variable {X Y A : IntrinsicSystem}

lemma S193T_mfst {α β : Type*} [Fintype α] [Fintype β] (M : Matrix (α × β) (α × β) ℂ) (a b : α) :
    redistributionMarginal M Prod.fst Prod.snd a b = ∑ k, M (a, k) (b, k) := by
  simp only [redistributionMarginal, Fintype.sum_prod_type, ite_and]
  simp
  rw [Finset.sum_eq_single a (by intro c _ hc; simp [hc]) (by simp)]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [if_pos rfl, Finset.sum_eq_single b (by intro c _ hc; simp [hc]) (by simp)]
  simp

lemma S193T_msnd {α β : Type*} [Fintype α] [Fintype β] (M : Matrix (α × β) (α × β) ℂ) (a b : β) :
    redistributionMarginal M Prod.snd Prod.fst a b = ∑ k, M (k, a) (k, b) := by
  simp only [redistributionMarginal, Fintype.sum_prod_type, ite_and]
  rw [Finset.sum_comm]
  simp
  rw [Finset.sum_eq_single a (by intro c _ hc; simp [hc]) (by simp)]
  simp

variable {X Y A : IntrinsicSystem}

lemma S193T_margX (E : Embedding X A) (F : Embedding Y A)
    (rho : Matrix (Fin A.dim) (Fin A.dim) ℂ) :
    redistributionMarginal (jointState X Y E.map F.map rho) Prod.fst Prod.snd =
      intrinsicRestriction X E.map rho := by
  ext a b
  rw [S193T_mfst]
  simp only [jointState, intrinsicRestriction, and_true]
  split_ifs with hab
  · rw [← Matrix.trace_sum, ← Matrix.mul_sum, ← Matrix.mul_sum, ← map_sum, Matrix.sum_single_one,
      F.unit, Matrix.mul_one]
  · simp

lemma S193T_margY (E : Embedding X A) (F : Embedding Y A)
    (rho : Matrix (Fin A.dim) (Fin A.dim) ℂ) :
    redistributionMarginal (jointState X Y E.map F.map rho) Prod.snd Prod.fst =
      intrinsicRestriction Y F.map rho := by
  ext a b
  rw [S193T_msnd]
  simp only [jointState, intrinsicRestriction, true_and]
  split_ifs with hab
  · rw [← Matrix.trace_sum, ← Matrix.mul_sum, ← Matrix.sum_mul, ← map_sum, Matrix.sum_single_one,
      E.unit, Matrix.one_mul]
  · simp

lemma S193T_trace (E : Embedding X A) (F : Embedding Y A)
    (rho : Matrix (Fin A.dim) (Fin A.dim) ℂ) (hrho : rho.trace = 1) :
    (jointState X Y E.map F.map rho).trace = 1 := by
  have hi : ∀ i, ∑ k, (rho * (E.map (Matrix.single i i 1) * F.map (Matrix.single k k 1))).trace
      = (rho * E.map (Matrix.single i i 1)).trace := by
    intro i
    rw [← Matrix.trace_sum, ← Matrix.mul_sum, ← Matrix.mul_sum, ← map_sum, Matrix.sum_single_one,
      F.unit, Matrix.mul_one]
  rw [Matrix.trace]
  simp only [Matrix.diag, jointState, and_self, if_true, Fintype.sum_prod_type, hi]
  rw [← Matrix.trace_sum, ← Matrix.mul_sum, ← map_sum, Matrix.sum_single_one, E.unit,
    Matrix.mul_one, hrho]

lemma S193T_herm (E : Embedding X A) (F : Embedding Y A)
    (hcompat : CommutingImages E.map F.map)
    (rho : Matrix (Fin A.dim) (Fin A.dim) ℂ) (hrho : rho.IsHermitian) :
    (jointState X Y E.map F.map rho).IsHermitian := by
  ext p q
  simp only [Matrix.conjTranspose_apply, jointState]
  by_cases h : X.block p.1 = X.block q.1 ∧ Y.block p.2 = Y.block q.2
  · rw [if_pos ⟨h.1.symm, h.2.symm⟩, if_pos h, ← Matrix.trace_conjTranspose,
      Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hrho.eq,
      ← E.star _ (S193T_single_mem _ h.1), ← F.star _ (S193T_single_mem _ h.2),
      Matrix.conjTranspose_single, Matrix.conjTranspose_single, star_one,
      hcompat _ _ (S193T_single_mem _ h.1.symm) (S193T_single_mem _ h.2.symm),
      Matrix.trace_mul_comm rho]
  · rw [if_neg (fun h' => h ⟨h'.1.symm, h'.2.symm⟩), if_neg h, star_zero]

def S193T_Yf (E : Embedding X A) (F : Embedding Y A) (r p : Fin X.dim × Fin Y.dim) :
    Matrix (Fin A.dim) (Fin A.dim) ℂ :=
  if S193T_lead X.block p.1 = r.1 ∧ S193T_lead Y.block p.2 = r.2 then
    E.map (Matrix.single r.1 p.1 1) * F.map (Matrix.single r.2 p.2 1) else 0

lemma S193T_Yprod (E : Embedding X A) (F : Embedding Y A)
    (hcompat : CommutingImages E.map F.map) (r q p : Fin X.dim × Fin Y.dim) :
    (S193T_Yf E F r q)ᴴ * S193T_Yf E F r p =
      if (S193T_lead X.block q.1 = r.1 ∧ S193T_lead Y.block q.2 = r.2) ∧
        (S193T_lead X.block p.1 = r.1 ∧ S193T_lead Y.block p.2 = r.2) then
      E.map (Matrix.single q.1 p.1 1) * F.map (Matrix.single q.2 p.2 1) else 0 := by
  unfold S193T_Yf
  by_cases hq : S193T_lead X.block q.1 = r.1 ∧ S193T_lead Y.block q.2 = r.2
  · by_cases hp : S193T_lead X.block p.1 = r.1 ∧ S193T_lead Y.block p.2 = r.2
    · rw [if_pos hq, if_pos hp, if_pos ⟨hq, hp⟩]
      obtain ⟨r1, r2⟩ := r
      simp only at hq hp ⊢
      have a1 : X.block q.1 = X.block r1 := by rw [← hq.1]; exact (S193T_lead_blk _ _).symm
      have a2 : X.block r1 = X.block p.1 := by rw [← hp.1]; exact S193T_lead_blk _ _
      have b1 : Y.block q.2 = Y.block r2 := by rw [← hq.2]; exact (S193T_lead_blk _ _).symm
      have b2 : Y.block r2 = Y.block p.2 := by rw [← hp.2]; exact S193T_lead_blk _ _
      rw [Matrix.conjTranspose_mul, ← E.star _ (S193T_single_mem _ a1.symm),
        ← F.star _ (S193T_single_mem _ b1.symm), Matrix.conjTranspose_single,
        Matrix.conjTranspose_single, star_one, Matrix.mul_assoc, ← Matrix.mul_assoc (E.map _),
        ← E.mul _ _ (S193T_single_mem _ a1) (S193T_single_mem _ a2),
        Matrix.single_mul_single_same, mul_one, ← Matrix.mul_assoc,
        ← hcompat _ _ (S193T_single_mem _ (a1.trans a2)) (S193T_single_mem _ b1),
        Matrix.mul_assoc, ← F.mul _ _ (S193T_single_mem _ b1) (S193T_single_mem _ b2),
        Matrix.single_mul_single_same, mul_one]
    · simp only [hp, and_false, if_false, Matrix.mul_zero]
  · simp only [hq, false_and, if_false, Matrix.conjTranspose_zero, Matrix.zero_mul]

lemma S193T_sumr (E : Embedding X A) (F : Embedding Y A)
    (hcompat : CommutingImages E.map F.map) (rho : Matrix (Fin A.dim) (Fin A.dim) ℂ)
    (q p : Fin X.dim × Fin Y.dim) :
    ∑ r, (rho * ((S193T_Yf E F r q)ᴴ * S193T_Yf E F r p)).trace =
      jointState X Y E.map F.map rho p q := by
  simp only [S193T_Yprod E F hcompat, jointState]
  rw [Finset.sum_eq_single (S193T_lead X.block q.1, S193T_lead Y.block q.2)]
  · simp only [and_true, true_and, S193T_lead_iff]
    split_ifs <;> simp_all [eq_comm]
  · intro r _ hr
    rw [if_neg, Matrix.mul_zero, Matrix.trace_zero]
    rintro ⟨⟨h1, h2⟩, _⟩
    exact hr (Prod.ext h1.symm h2.symm)
  · simp

lemma S193T_psd (E : Embedding X A) (F : Embedding Y A)
    (hcompat : CommutingImages E.map F.map)
    (rho : Matrix (Fin A.dim) (Fin A.dim) ℂ) (hrho : rho.PosSemidef) :
    (jointState X Y E.map F.map rho).PosSemidef := by
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg (S193T_herm E F hcompat rho hrho.1)
    (fun x => ?_)
  set W : Fin X.dim × Fin Y.dim → Matrix (Fin A.dim) (Fin A.dim) ℂ :=
    fun r => ∑ p, star (x p) • S193T_Yf E F r p with hW
  have key : star x ⬝ᵥ (jointState X Y E.map F.map rho *ᵥ x) =
      ∑ r, (rho * ((W r)ᴴ * W r)).trace := by
    have e1 : ∀ r, (rho * ((W r)ᴴ * W r)).trace = ∑ q, ∑ p, (x q * star (x p)) *
        (rho * ((S193T_Yf E F r q)ᴴ * S193T_Yf E F r p)).trace := by
      intro r
      simp only [hW, Matrix.conjTranspose_sum, Matrix.conjTranspose_smul, star_star]
      rw [Matrix.sum_mul]
      simp only [Matrix.mul_sum, Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.trace_sum,
        Matrix.trace_smul, smul_eq_mul]
      exact Finset.sum_congr rfl (fun _ _ => Finset.sum_congr rfl (fun _ _ => by ring))
    simp only [e1]
    rw [Finset.sum_comm]
    simp only [dotProduct, mulVec, Pi.star_apply, Finset.mul_sum]
    conv_lhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun q _ => ?_)
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun p _ => ?_)
    rw [← Finset.mul_sum, S193T_sumr E F hcompat]
    ring
  rw [key]
  refine Finset.sum_nonneg (fun r _ => ?_)
  rw [← Matrix.mul_assoc, Matrix.trace_mul_cycle]
  exact (hrho.mul_mul_conjTranspose_same (W r)).trace_nonneg

end S193T_joint

section S193T_final
open QAlgorithms.Papers.Independent.Gap48.P20 (redistributionMarginal)
open QAlgorithms.Papers.Independent.Renew46.P43

lemma S193T_both {X Y A : IntrinsicSystem} (E : Embedding X A) (F : Embedding Y A)
    (hcompat : CommutingImages E.map F.map) (rho : Matrix (Fin A.dim) (Fin A.dim) ℂ)
    (hrho : A.IsState rho) :
    S193T_S (intrinsicRestriction X E.map rho) ≤
        S193T_S (intrinsicRestriction Y F.map rho) + S193T_S (jointState X Y E.map F.map rho) ∧
      S193T_S (intrinsicRestriction Y F.map rho) ≤
        S193T_S (intrinsicRestriction X E.map rho) + S193T_S (jointState X Y E.map F.map rho) := by
  classical
  have hJ : QAlgorithms.IsDensityMatrix (jointState X Y E.map F.map rho) :=
    ⟨S193T_psd E F hcompat rho hrho.1.1, S193T_trace E F rho hrho.1.2⟩
  have : Nonempty (Fin X.dim) := ⟨⟨0, X.positive⟩⟩
  have : Nonempty (Fin Y.dim) := ⟨⟨0, Y.positive⟩⟩
  have h1 := S193T_AL1 (ia := inferInstance) (ib := inferInstance) (iab := inferInstance) _ hJ
  have h2 := S193T_AL2 (ia := inferInstance) (ib := inferInstance) (iab := inferInstance) _ hJ
  rw [S193T_margX, S193T_margY] at h1 h2
  simp only [S193T_toS] at h1 h2
  exact ⟨h1, h2⟩

end S193T_final

open scoped BigOperators Matrix ComplexConjugate ComplexOrder ENNReal Matrix.Norms.L2Operator

open Filter MeasureTheory

attribute [local instance] Classical.propDecidable Classical.decEq

attribute [local instance] QAlgorithms.Papers.Independent.Renew46.P43.matrixMeasurableSpace

open QAlgorithms QAlgorithms.Papers.Independent.Renew46.P43 in
open QAlgorithms.Papers.Independent.Claimed50.P40 (InBlocks) in
/-- Theorem A.13, PDF pp.71-72: the intrinsic-algebra entropy triangle inequality. -/
theorem solution {X Y A : IntrinsicSystem} (E : Embedding X A) (F : Embedding Y A)
    (hcompat : CommutingImages E.map F.map) (rho : Matrix (Fin A.dim) (Fin A.dim) ℂ)
    (hrho : A.IsState rho) :
    |viewedEntropy X E.map rho - viewedEntropy Y F.map rho| ≤
      vnEntropy (jointState X Y E.map F.map rho) := by
  obtain ⟨h1, h2⟩ := S193T_both E F hcompat rho hrho
  unfold viewedEntropy
  simp only [S193T_toS]
  rw [abs_sub_le_iff]
  constructor <;> linarith
