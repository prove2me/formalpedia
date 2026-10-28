-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Support50.P43.alternative_nonnegative
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T19:25:11.204311+00:00
-- url     : https://prove2.me/submissions/3a2e71d9-8c3d-4d0d-882d-97000655c286

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P43
import Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P20_strongSubadditivity

noncomputable section
open scoped Matrix ComplexConjugate ComplexOrder

section S191B_ent
open Matrix Polynomial

lemma S191B_spec_finite {ι : Type*} [Fintype ι] {inst : DecidableEq ι} (A : Matrix ι ι ℂ)
    (hA : A.IsHermitian) : (spectrum ℝ A).Finite := by
  rw [hA.spectrum_real_eq_range_eigenvalues]; exact Set.finite_range _

lemma S191B_vn_poly {ι : Type*} [Fintype ι] {inst : DecidableEq ι} (A : Matrix ι ι ℂ)
    (hA : A.IsHermitian) (p : ℝ[X])
    (hp : ∀ x ∈ spectrum ℝ A, p.eval x = x * Real.logb 2 x) :
    QAlgorithms.vnEntropy A = -(aeval A p).trace.re := by
  unfold QAlgorithms.vnEntropy
  rw [cfc_congr (g := fun x => p.eval x) (fun x hx => (hp x hx).symm),
    cfc_polynomial p A hA.isSelfAdjoint]

/-- interpolation polynomial of x log x on a finite set -/
def S191B_interp (s : Finset ℝ) : ℝ[X] :=
  Lagrange.interpolate s id (fun x => x * Real.logb 2 x)

lemma S191B_interp_eval (s : Finset ℝ) {x : ℝ} (hx : x ∈ s) :
    (S191B_interp s).eval x = x * Real.logb 2 x :=
  Lagrange.eval_interpolate_at_node (v := id) _ (Set.injOn_id _) hx

lemma S191B_vn_submatrix {ι κ : Type*} [Fintype ι] [Fintype κ] {inst : DecidableEq ι}
    {inst' : DecidableEq κ} (A : Matrix ι ι ℂ) (hA : A.IsHermitian) (e : κ ≃ ι) :
    QAlgorithms.vnEntropy (A.submatrix e e) = QAlgorithms.vnEntropy A := by
  set s := (S191B_spec_finite A hA).toFinset
  have hsub : A.submatrix e e = Matrix.reindexAlgEquiv ℝ ℂ e.symm A := by
    ext a b; simp [Matrix.coe_reindexAlgEquiv]
  have hspec : spectrum ℝ (A.submatrix e e) = spectrum ℝ A := by
    rw [hsub]; exact AlgEquiv.spectrum_eq _ _
  rw [S191B_vn_poly A hA (S191B_interp s) (fun x hx => S191B_interp_eval s (by simpa [s] using hx)),
    S191B_vn_poly _ (hA.submatrix e) (S191B_interp s)
      (fun x hx => S191B_interp_eval s (by rw [hspec] at hx; simpa [s] using hx))]
  rw [hsub, Polynomial.aeval_algEquiv, AlgHom.comp_apply]
  congr 2
  simp only [AlgEquiv.coe_toAlgHom, Matrix.coe_reindexAlgEquiv, Matrix.reindex_apply,
    Equiv.symm_symm, Matrix.trace, Matrix.diag, Matrix.submatrix_apply]
  exact e.sum_comp (fun i => (aeval A (S191B_interp s)) i i)

lemma S191B_vn_conj {ι : Type*} [Fintype ι] {inst : DecidableEq ι} (A : Matrix ι ι ℂ)
    (hA : A.IsHermitian) :
    QAlgorithms.vnEntropy (A.map (starRingEnd ℂ)) = QAlgorithms.vnEntropy A := by
  set s := (S191B_spec_finite A hA).toFinset
  set φ : Matrix ι ι ℂ ≃ₐ[ℝ] Matrix ι ι ℂ := AlgEquiv.mapMatrix Complex.conjAe
  have hφ : A.map (starRingEnd ℂ) = φ A := rfl
  have hspec : spectrum ℝ (A.map (starRingEnd ℂ)) = spectrum ℝ A := by
    rw [hφ]; exact AlgEquiv.spectrum_eq _ _
  have hH : (A.map (starRingEnd ℂ)).IsHermitian := by
    ext i j; have := congrFun (congrFun hA i) j
    simp only [conjTranspose_apply, map_apply] at this ⊢
    rw [← this]; simp
  rw [S191B_vn_poly A hA (S191B_interp s) (fun x hx => S191B_interp_eval s (by simpa [s] using hx)),
    S191B_vn_poly _ hH (S191B_interp s)
      (fun x hx => S191B_interp_eval s (by rw [hspec] at hx; simpa [s] using hx))]
  rw [hφ, Polynomial.aeval_algEquiv, AlgHom.comp_apply]
  have htr : ∀ X : Matrix ι ι ℂ, (φ X).trace = starRingEnd ℂ X.trace := by
    intro X
    simp only [φ, AlgEquiv.mapMatrix_apply, Matrix.trace, Matrix.diag, Matrix.map_apply, map_sum]
    rfl
  simp only [AlgEquiv.coe_toAlgHom]
  rw [htr, Complex.conj_re]

lemma S191B_pow_mul {κ ι : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (M : Matrix κ ι ℂ) (N : Matrix ι κ ℂ) (k : ℕ) :
    (M * N) ^ (k + 1) = M * (N * M) ^ k * N := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, ih, pow_succ]; simp only [Matrix.mul_assoc]

lemma S191B_tr_pow {κ ι : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (M : Matrix κ ι ℂ) (N : Matrix ι κ ℂ) (k : ℕ) :
    ((M * N) ^ (k + 1)).trace = ((N * M) ^ (k + 1)).trace := by
  rw [S191B_pow_mul, Matrix.mul_assoc, Matrix.trace_mul_comm, Matrix.mul_assoc, pow_succ]

lemma S191B_vn_mul_comm {κ ι : Type*} [Fintype ι] [Fintype κ] {inst : DecidableEq ι}
    {inst' : DecidableEq κ} (M : Matrix κ ι ℂ) :
    QAlgorithms.vnEntropy (M * Mᴴ) = QAlgorithms.vnEntropy (Mᴴ * M) := by
  have h1 : (M * Mᴴ).IsHermitian := isHermitian_mul_conjTranspose_self M
  have h2 : (Mᴴ * M).IsHermitian := isHermitian_conjTranspose_mul_self M
  set s : Finset ℝ := insert 0 ((S191B_spec_finite (inst := inst') _ h1).toFinset ∪
    (S191B_spec_finite (inst := inst) _ h2).toFinset)
  set p := S191B_interp s
  rw [S191B_vn_poly _ h1 p (fun x hx => S191B_interp_eval s (by simp [s, hx])),
    S191B_vn_poly _ h2 p (fun x hx => S191B_interp_eval s (by simp [s, hx]))]
  have h0 : p.coeff 0 = 0 := by
    rw [Polynomial.coeff_zero_eq_eval_zero, S191B_interp_eval s (by simp [s])]; simp
  congr 2
  rw [Polynomial.aeval_eq_sum_range, Polynomial.aeval_eq_sum_range, Matrix.trace_sum,
    Matrix.trace_sum, Finset.sum_range_succ', Finset.sum_range_succ']
  simp only [h0, zero_smul, Matrix.trace_zero, add_zero, Matrix.trace_smul]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [S191B_tr_pow]

end S191B_ent

section S191B_marg
open Matrix
open scoped Classical
open QAlgorithms.Papers.Independent.Gap48.P20 (redistributionMarginal)

def S191B_pure {Y : Type*} (Ψ : Y → ℂ) : Matrix Y Y ℂ := Matrix.of fun a b => Ψ a * conj (Ψ b)

def S191B_M {Y K F : Type*} [Fintype Y] (Ψ : Y → ℂ) (k : Y → K) (f : Y → F) : Matrix K F ℂ :=
  fun a z => ∑ y, if k y = a ∧ f y = z then Ψ y else 0

lemma S191B_pure_marg {Y K F : Type*} [Fintype Y] [Fintype F] (Ψ : Y → ℂ) (k : Y → K)
    (f : Y → F) : redistributionMarginal (S191B_pure Ψ) k f =
      S191B_M Ψ k f * (S191B_M Ψ k f)ᴴ := by
  ext a b
  simp only [redistributionMarginal, Matrix.mul_apply, Matrix.conjTranspose_apply, S191B_M,
    S191B_pure, Matrix.of_apply, star_sum, Finset.sum_mul_sum]
  symm
  rw [Finset.sum_comm]; refine Finset.sum_congr rfl (fun x _ => ?_)
  rw [Finset.sum_comm]; refine Finset.sum_congr rfl (fun y _ => ?_)
  rw [Finset.sum_eq_single (f x)]
  · by_cases h1 : k x = a <;> by_cases h2 : k y = b <;> by_cases h3 : f x = f y <;>
      simp [h1, h2, h3, eq_comm (a := f y)]
  · intro z _ hz; simp [Ne.symm hz]
  · simp

lemma S191B_ite_sum {α : Type*} (s : Finset α) (c : Prop) [Decidable c] (g : α → ℂ) :
    (if c then ∑ i ∈ s, g i else 0) = ∑ i ∈ s, if c then g i else 0 := by
  split_ifs <;> simp

lemma S191B_marg_comp {Y K F K2 F2 : Type*} [Fintype Y] [Fintype K] (ρ : Matrix Y Y ℂ)
    (k : Y → K) (f : Y → F) (k2 : K → K2) (f2 : K → F2) :
    redistributionMarginal (redistributionMarginal ρ k f) k2 f2 =
      redistributionMarginal ρ (k2 ∘ k) (fun y => (f2 (k y), f y)) := by
  ext a b
  simp only [redistributionMarginal, S191B_ite_sum, Function.comp]
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


lemma S191B_marg_forget {Y K F F' : Type*} [Fintype Y] (ρ : Matrix Y Y ℂ) (k : Y → K)
    (f : Y → F) (f' : Y → F') (hf : ∀ x y, f x = f y ↔ f' x = f' y) :
    redistributionMarginal ρ k f = redistributionMarginal ρ k f' := by
  ext a b
  simp only [redistributionMarginal]
  refine Finset.sum_congr rfl (fun x _ => Finset.sum_congr rfl (fun y _ => ?_))
  simp only [hf x y]

lemma S191B_vn_keep {Y K K' F : Type*} [Fintype Y] [Fintype K] [Fintype K']
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
  rw [← hsub, S191B_vn_submatrix _ hH]

lemma S191B_pure_herm {Y K F : Type*} [Fintype Y] [Fintype F] (Ψ : Y → ℂ) (k : Y → K)
    (f : Y → F) : (redistributionMarginal (S191B_pure Ψ) k f).IsHermitian := by
  rw [S191B_pure_marg]; exact isHermitian_mul_conjTranspose_self _

lemma S191B_vn_swap {Y K F : Type*} [Fintype Y] [Fintype K] [Fintype F]
    {inst : DecidableEq K} {inst' : DecidableEq F} (Ψ : Y → ℂ) (k : Y → K) (f : Y → F) :
    QAlgorithms.vnEntropy (redistributionMarginal (S191B_pure Ψ) k f) =
      QAlgorithms.vnEntropy (redistributionMarginal (S191B_pure Ψ) f k) := by
  rw [S191B_pure_marg, S191B_pure_marg]
  set M := S191B_M Ψ k f
  have hN : S191B_M Ψ f k * (S191B_M Ψ f k)ᴴ = (Mᴴ * M).map (starRingEnd ℂ) := by
    ext z w
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.map_apply, map_sum, map_mul,
      M, S191B_M]
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
  rw [hN, S191B_vn_conj _ (isHermitian_conjTranspose_mul_self M), S191B_vn_mul_comm]

lemma S191B_marg_trace {Y K F : Type*} [Fintype Y] [Fintype K] (ρ : Matrix Y Y ℂ)
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

lemma S191B_pure_density {Y K F : Type*} [Fintype Y] [Fintype K] [Fintype F] (Ψ : Y → ℂ)
    (hΨ : (S191B_pure Ψ).trace = 1) (k : Y → K) (f : Y → F)
    (hinj : Function.Injective (fun y => (k y, f y))) :
    QAlgorithms.IsDensityMatrix (redistributionMarginal (S191B_pure Ψ) k f) := by
  refine ⟨?_, ?_⟩
  · rw [S191B_pure_marg]; exact posSemidef_self_mul_conjTranspose _
  · rw [S191B_marg_trace _ _ _ hinj, hΨ]

lemma S191B_vn_unit {inst : DecidableEq Unit} (A : Matrix Unit Unit ℂ) (h : A.trace = 1) :
    QAlgorithms.vnEntropy A = 0 := by
  have : A = 1 := by
    ext a b; cases a; cases b; simpa [Matrix.trace] using h
  rw [this]; simp [QAlgorithms.vnEntropy]
end S191B_marg

section S191B_bridge
open Matrix
open QAlgorithms.Papers.Independent.Gap48.P20 (redistributionMarginal)
open QAlgorithms.Papers.Independent.Claimed50.P33 (RegisterBasis SubBasis registerMarginal
  trivialExtension)
open QAlgorithms.Papers.Independent.Support50.P43
attribute [local instance] Classical.propDecidable Classical.decEq

lemma S191B_restrict_eq {n : ℕ} {D : Fin n → Type} (T : Finset (Fin n)) (x y : RegisterBasis D) :
    restrictLabel T x = restrictLabel T y ↔ ∀ i ∈ T, x i = y i := by
  constructor
  · intro h i hi; exact congrFun h ⟨i, hi⟩
  · intro h; funext i; exact h i.1 i.2

lemma S191B_C1 {n : ℕ} {D : Fin n → Type} [∀ i, Fintype (D i)]
    (ρ : Matrix (RegisterBasis D) (RegisterBasis D) ℂ) (T : Finset (Fin n)) :
    registerMarginal (trivialExtension ρ) T =
      redistributionMarginal ρ (fun x => (restrictLabel T x, ())) (fun x => restrictLabel Tᶜ x) := by
  ext a b
  simp only [registerMarginal, trivialExtension, redistributionMarginal]
  refine Finset.sum_congr rfl (fun x _ => Finset.sum_congr rfl (fun y _ => ?_))
  have hiff : ((∀ i (hi : i ∈ T), x i = a.1 ⟨i, hi⟩ ∧ y i = b.1 ⟨i, hi⟩) ∧
      (∀ i, i ∉ T → x i = y i)) ↔ ((restrictLabel T x, ()) = a ∧ (restrictLabel T y, ()) = b ∧
      restrictLabel Tᶜ x = restrictLabel Tᶜ y) := by
    rw [S191B_restrict_eq]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨Prod.ext (funext fun i => (h1 i.1 i.2).1) rfl,
        Prod.ext (funext fun i => (h1 i.1 i.2).2) rfl, fun i hi => h2 i (by simpa using hi)⟩
    · rintro ⟨h1, h2, h3⟩
      subst h1; subst h2
      exact ⟨fun i hi => ⟨rfl, rfl⟩, fun i hi => h3 i (by simpa using hi)⟩
  by_cases h : ((∀ i (hi : i ∈ T), x i = a.1 ⟨i, hi⟩ ∧ y i = b.1 ⟨i, hi⟩) ∧
      (∀ i, i ∉ T → x i = y i))
  · rw [if_pos h, if_pos (hiff.1 h)]
  · rw [if_neg h, if_neg (fun h' => h (hiff.2 h'))]

lemma S191B_purify {X : Type*} [Fintype X] [DecidableEq X] (ρ : Matrix X X ℂ)
    (hρ : ρ.PosSemidef) : ∃ Ψ : X × X → ℂ,
      redistributionMarginal (S191B_pure Ψ) Prod.fst Prod.snd = ρ := by
  set U : Matrix X X ℂ := (hρ.1.eigenvectorUnitary : Matrix X X ℂ)
  set lam := hρ.1.eigenvalues
  refine ⟨fun y => U y.1 y.2 * ((Real.sqrt (lam y.2) : ℝ) : ℂ), ?_⟩
  rw [S191B_pure_marg]
  have hM : S191B_M (fun y : X × X => U y.1 y.2 * ((Real.sqrt (lam y.2) : ℝ) : ℂ))
      Prod.fst Prod.snd = U * diagonal (fun j => ((Real.sqrt (lam j) : ℝ) : ℂ)) := by
    ext a j
    simp only [S191B_M, mul_diagonal]
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

end S191B_bridge

section S191B_main
open Matrix
open QAlgorithms.Papers.Independent.Gap48.P20 (redistributionMarginal subsystemEntropy)
open QAlgorithms.Papers.Independent.Claimed50.P33 (RegisterBasis SubBasis registerMarginal
  trivialExtension entropyAt)
open QAlgorithms.Papers.Independent.Support50.P43
attribute [local instance] Classical.propDecidable Classical.decEq

lemma S191B_vn_eq {Y K K' F F' : Type*} [Fintype Y] [Fintype K] [Fintype K'] [Fintype F']
    {inst : DecidableEq K} {inst' : DecidableEq K'} (Ψ : Y → ℂ) (k : Y → K) (f : Y → F)
    (k' : Y → K') (f' : Y → F') (hk : ∀ x y, k x = k y ↔ k' x = k' y)
    (hs : Function.Surjective k) (hs' : Function.Surjective k')
    (hf : ∀ x y, f x = f y ↔ f' x = f' y) :
    QAlgorithms.vnEntropy (redistributionMarginal (S191B_pure Ψ) k f) =
      QAlgorithms.vnEntropy (redistributionMarginal (S191B_pure Ψ) k' f') := by
  rw [S191B_marg_forget _ k f f' hf]
  exact S191B_vn_keep _ k k' f' hk hs hs' (S191B_pure_herm _ _ _)

def S191B_ext {n : ℕ} {D : Fin n → Type} (T : Finset (Fin n)) (a : SubBasis D T)
    (z : RegisterBasis D) : RegisterBasis D := fun k => if h : k ∈ T then a ⟨k, h⟩ else z k

lemma S191B_restrict_ext {n : ℕ} {D : Fin n → Type} (T : Finset (Fin n)) (a : SubBasis D T)
    (z : RegisterBasis D) : restrictLabel T (S191B_ext T a z) = a := by
  funext i; simp [restrictLabel, S191B_ext, i.2]

lemma S191B_ext_out {n : ℕ} {D : Fin n → Type} (T : Finset (Fin n)) (a : SubBasis D T)
    (z : RegisterBasis D) (k : Fin n) (hk : k ∉ T) : S191B_ext T a z k = z k := by
  simp [S191B_ext, hk]

variable {n : ℕ} {D : Fin n → Type} [∀ i, Fintype (D i)] [∀ i, Nonempty (D i)]

lemma S191B_S_eq (ρ : Matrix (RegisterBasis D) (RegisterBasis D) ℂ)
    (Ψ : RegisterBasis D × RegisterBasis D → ℂ)
    (hP : redistributionMarginal (S191B_pure Ψ) Prod.fst Prod.snd = ρ) (T : Finset (Fin n)) :
    marginalEntropyBits ρ T = QAlgorithms.vnEntropy (redistributionMarginal (S191B_pure Ψ)
      (fun y => (restrictLabel T y.1, ())) (fun y => (restrictLabel Tᶜ y.1, y.2))) := by
  unfold marginalEntropyBits entropyAt
  rw [S191B_C1, ← hP, S191B_marg_comp]
  congr 1

lemma S191B_restrict_update_ext (T : Finset (Fin n)) (a : SubBasis D T) (z : RegisterBasis D)
    (j : Fin n) (hj : j ∉ T) (c : D j) :
    restrictLabel T (Function.update (S191B_ext T a z) j c) = a := by
  funext k
  have hk : (k : Fin n) ≠ j := fun h => hj (h ▸ k.2)
  simp only [restrictLabel, Function.update_of_ne hk]
  exact congrFun (S191B_restrict_ext T a z) k

lemma S191B_restrict_ext_disj (T T' : Finset (Fin n)) (a : SubBasis D T) (z : RegisterBasis D)
    (h : ∀ k ∈ T', k ∉ T) : restrictLabel T' (S191B_ext T a z) = restrictLabel T' z := by
  funext k; simp [restrictLabel, S191B_ext, h k.1 k.2]

lemma S191B_empty (ρ : Matrix (RegisterBasis D) (RegisterBasis D) ℂ)
    (Ψ : RegisterBasis D × RegisterBasis D → ℂ)
    (hP : redistributionMarginal (S191B_pure Ψ) Prod.fst Prod.snd = ρ)
    (hΨ : (S191B_pure Ψ).trace = 1) : marginalEntropyBits ρ ∅ = 0 := by
  obtain ⟨z⟩ : Nonempty (RegisterBasis D) := inferInstance
  rw [S191B_S_eq ρ Ψ hP]
  rw [S191B_vn_eq (inst' := instDecidableEqPUnit) Ψ _ _ (fun _ => ()) (fun y => (restrictLabel (∅ : Finset (Fin n))ᶜ y.1, y.2))
    (fun y y' => by simp [S191B_restrict_eq])
    (fun ⟨a, u⟩ => ⟨(S191B_ext _ a z, z), by simp [S191B_restrict_ext]⟩)
    (fun u => ⟨(z, z), rfl⟩) (fun y y' => Iff.rfl)]
  apply S191B_vn_unit
  rw [S191B_marg_trace, hΨ]
  intro y y' h
  simp only [Prod.mk.injEq, S191B_restrict_eq, Finset.mem_compl, Finset.notMem_empty,
    not_false_eq_true, forall_const, true_and] at h
  exact Prod.ext (funext h.1) h.2

lemma S191B_han (ρ : Matrix (RegisterBasis D) (RegisterBasis D) ℂ)
    (Ψ : RegisterBasis D × RegisterBasis D → ℂ)
    (hP : redistributionMarginal (S191B_pure Ψ) Prod.fst Prod.snd = ρ)
    (hΨ : (S191B_pure Ψ).trace = 1) (i : Fin n) :
    marginalEntropyBits ρ Finset.univ +
      marginalEntropyBits ρ (Finset.univ.filter (fun j : Fin n => j.val < i.val)) ≤
    marginalEntropyBits ρ (Finset.univ.filter (fun j : Fin n => j.val < i.val + 1)) +
      marginalEntropyBits ρ (Finset.univ.erase i) := by
  set L : Finset (Fin n) := Finset.univ.filter (fun j : Fin n => j.val < i.val) with hL
  set A : Finset (Fin n) := Finset.univ.filter (fun j : Fin n => j.val < i.val + 1) with hA
  set U : Finset (Fin n) := Finset.univ.filter (fun j : Fin n => i.val < j.val) with hU
  have hLm : ∀ k, k ∈ L ↔ k.val < i.val := by intro k; simp [hL]
  have hAm : ∀ k, k ∈ A ↔ k.val < i.val + 1 := by intro k; simp [hA]
  have hUm : ∀ k, k ∈ U ↔ i.val < k.val := by intro k; simp [hU]
  have hiL : i ∉ L := by simp [hLm]
  have hiU : i ∉ U := by simp [hUm]
  have hUL : ∀ k ∈ L, k ∉ U := by intro k hk; rw [hLm] at hk; rw [hUm]; omega
  have hvi : ∀ k : Fin n, k ≠ i ↔ k.val ≠ i.val := fun k => Fin.val_ne_iff.symm
  obtain ⟨z⟩ : Nonempty (RegisterBasis D) := inferInstance
  rw [S191B_S_eq ρ Ψ hP, S191B_S_eq ρ Ψ hP, S191B_S_eq ρ Ψ hP, S191B_S_eq ρ Ψ hP]
  set kσ : RegisterBasis D × RegisterBasis D → D i × (SubBasis D U × SubBasis D L) :=
    fun y => (y.1 i, (restrictLabel U y.1, restrictLabel L y.1)) with hkσ
  set fσ : RegisterBasis D × RegisterBasis D → RegisterBasis D := fun y => y.2 with hfσ
  have hinj : Function.Injective (fun y => (kσ y, fσ y)) := by
    intro y y' h
    simp only [hkσ, hfσ, Prod.mk.injEq, S191B_restrict_eq, hUm, hLm] at h
    obtain ⟨⟨h1, h2, h3⟩, h4⟩ := h
    refine Prod.ext (funext fun k => ?_) h4
    rcases lt_trichotomy k.val i.val with hk | hk | hk
    · exact h3 k hk
    · rw [Fin.ext hk]; exact h1
    · exact h2 k hk
  have hssa := QAlgorithms.Papers.Independent.Gap48.P20.strongSubadditivity
    (redistributionMarginal (S191B_pure Ψ) kσ fσ) (S191B_pure_density Ψ hΨ kσ fσ hinj)
  unfold subsystemEntropy at hssa
  rw [S191B_marg_comp, S191B_marg_comp, S191B_marg_comp] at hssa
  have hssa' : 0 ≤
      QAlgorithms.vnEntropy (redistributionMarginal (S191B_pure Ψ)
        (fun y => (y.1 i, restrictLabel L y.1)) (fun y => (restrictLabel U y.1, y.2))) +
      QAlgorithms.vnEntropy (redistributionMarginal (S191B_pure Ψ)
        (fun y => (restrictLabel U y.1, restrictLabel L y.1)) (fun y => (y.1 i, y.2))) -
      QAlgorithms.vnEntropy (redistributionMarginal (S191B_pure Ψ) (fun y => restrictLabel L y.1)
        (fun y => ((y.1 i, restrictLabel U y.1), y.2))) -
      QAlgorithms.vnEntropy (redistributionMarginal (S191B_pure Ψ) kσ fσ) := by
    simp only [hkσ, hfσ, Function.comp_def] at hssa
    convert hssa
  have h1 : QAlgorithms.vnEntropy (redistributionMarginal (S191B_pure Ψ)
        (fun y => (y.1 i, restrictLabel L y.1)) (fun y => (restrictLabel U y.1, y.2))) =
      QAlgorithms.vnEntropy (redistributionMarginal (S191B_pure Ψ)
        (fun y => (restrictLabel A y.1, ())) (fun y => (restrictLabel Aᶜ y.1, y.2))) := by
    apply S191B_vn_eq
    · intro y y'
      simp only [Prod.mk.injEq, S191B_restrict_eq, hLm, hAm, and_true]
      constructor
      · rintro ⟨h1, h2⟩ k hk
        rcases Nat.lt_or_ge k.val i.val with hk' | hk'
        · exact h2 k hk'
        · rw [Fin.ext (by omega : k.val = i.val)]; exact h1
      · intro h; exact ⟨h i (by omega), fun k hk => h k (by omega)⟩
    · rintro ⟨c, a⟩
      exact ⟨(Function.update (S191B_ext L a z) i c, z), by
        simp [S191B_restrict_update_ext L a z i hiL c]⟩
    · rintro ⟨a, u⟩; exact ⟨(S191B_ext _ a z, z), by simp [S191B_restrict_ext]⟩
    · intro y y'
      simp only [Prod.mk.injEq, S191B_restrict_eq, hUm, hAm, Finset.mem_compl]
      constructor
      · rintro ⟨h1, h2⟩; exact ⟨fun k hk => h1 k (by omega), h2⟩
      · rintro ⟨h1, h2⟩; exact ⟨fun k hk => h1 k (by omega), h2⟩
  have h2 : QAlgorithms.vnEntropy (redistributionMarginal (S191B_pure Ψ)
        (fun y => (restrictLabel U y.1, restrictLabel L y.1)) (fun y => (y.1 i, y.2))) =
      QAlgorithms.vnEntropy (redistributionMarginal (S191B_pure Ψ)
        (fun y => (restrictLabel (Finset.univ.erase i) y.1, ()))
        (fun y => (restrictLabel (Finset.univ.erase i)ᶜ y.1, y.2))) := by
    apply S191B_vn_eq
    · intro y y'
      simp only [Prod.mk.injEq, S191B_restrict_eq, hLm, hUm, Finset.mem_erase,
        Finset.mem_univ, and_true, hvi]
      constructor
      · rintro ⟨h1, h2⟩ k hk
        rcases Nat.lt_or_ge k.val i.val with hk' | hk'
        · exact h2 k hk'
        · exact h1 k (by omega)
      · intro h; exact ⟨fun k hk => h k (by omega), fun k hk => h k (by omega)⟩
    · rintro ⟨aU, aL⟩
      exact ⟨(S191B_ext U aU (S191B_ext L aL z), z), by
        simp [S191B_restrict_ext, S191B_restrict_ext_disj U L aU _ (fun k hk => hUL k hk)]⟩
    · rintro ⟨a, u⟩; exact ⟨(S191B_ext _ a z, z), by simp [S191B_restrict_ext]⟩
    · intro y y'
      simp only [Prod.mk.injEq, S191B_restrict_eq, Finset.mem_compl, Finset.mem_erase,
        Finset.mem_univ, and_true, not_not, forall_eq]
  have h3 : QAlgorithms.vnEntropy (redistributionMarginal (S191B_pure Ψ)
        (fun y => restrictLabel L y.1) (fun y => ((y.1 i, restrictLabel U y.1), y.2))) =
      QAlgorithms.vnEntropy (redistributionMarginal (S191B_pure Ψ)
        (fun y => (restrictLabel L y.1, ())) (fun y => (restrictLabel Lᶜ y.1, y.2))) := by
    apply S191B_vn_eq
    · intro y y'; simp
    · intro a; exact ⟨(S191B_ext _ a z, z), by simp [S191B_restrict_ext]⟩
    · rintro ⟨a, u⟩; exact ⟨(S191B_ext _ a z, z), by simp [S191B_restrict_ext]⟩
    · intro y y'
      simp only [Prod.mk.injEq, S191B_restrict_eq, hUm, hLm, Finset.mem_compl]
      constructor
      · rintro ⟨⟨h1, h2⟩, h3⟩
        refine ⟨fun k hk => ?_, h3⟩
        rcases Nat.lt_or_ge i.val k.val with hk' | hk'
        · exact h2 k hk'
        · rw [Fin.ext (by omega : k.val = i.val)]; exact h1
      · rintro ⟨h1, h2⟩; exact ⟨⟨h1 i (by omega), fun k hk => h1 k (by omega)⟩, h2⟩
  have h4 : QAlgorithms.vnEntropy (redistributionMarginal (S191B_pure Ψ) kσ fσ) =
      QAlgorithms.vnEntropy (redistributionMarginal (S191B_pure Ψ)
        (fun y => (restrictLabel Finset.univ y.1, ()))
        (fun y => (restrictLabel Finset.univᶜ y.1, y.2))) := by
    apply S191B_vn_eq
    · intro y y'
      simp only [hkσ, Prod.mk.injEq, S191B_restrict_eq, hUm, hLm, Finset.mem_univ,
        forall_const, and_true]
      constructor
      · rintro ⟨h1, h2, h3⟩ k
        rcases lt_trichotomy k.val i.val with hk | hk | hk
        · exact h3 k hk
        · rw [Fin.ext hk]; exact h1
        · exact h2 k hk
      · intro h; exact ⟨h i, fun k _ => h k, fun k _ => h k⟩
    · rintro ⟨c, aU, aL⟩
      exact ⟨(Function.update (S191B_ext U aU (S191B_ext L aL z)) i c, z), by
        have e1 := S191B_restrict_update_ext U aU (S191B_ext L aL z) i hiU c
        have e2 : restrictLabel L (Function.update (S191B_ext U aU (S191B_ext L aL z)) i c) = aL := by
          funext k
          have hk : (k : Fin n) ≠ i := fun h => hiL (h ▸ k.2)
          simp only [restrictLabel, Function.update_of_ne hk]
          calc S191B_ext U aU (S191B_ext L aL z) k
              = restrictLabel L (S191B_ext U aU (S191B_ext L aL z)) k := rfl
            _ = restrictLabel L (S191B_ext L aL z) k :=
                congrFun (S191B_restrict_ext_disj U L aU _ (fun k hk => hUL k hk)) k
            _ = aL k := congrFun (S191B_restrict_ext L aL z) k
        simp [hkσ, e1, e2]⟩
    · rintro ⟨a, u⟩; exact ⟨(S191B_ext _ a z, z), by simp [S191B_restrict_ext]⟩
    · intro y y'; simp [hfσ, S191B_restrict_eq]
  linarith

end S191B_main


section S191B_final
open QAlgorithms.Papers.Independent.Gap48.P20 (redistributionMarginal)
open QAlgorithms.Papers.Independent.Claimed50.P33 (RegisterBasis SubBasis)
open QAlgorithms.Papers.Independent.Support50.P43
attribute [local instance] Classical.propDecidable Classical.decEq

theorem S191B_main {n : ℕ} (hn : 2 ≤ n) {D : Fin n → Type}
    [∀ i, Fintype (D i)] [∀ i, Nonempty (D i)]
    (rho : Matrix (RegisterBasis D) (RegisterBasis D) ℂ) (hrho : QAlgorithms.IsDensityMatrix rho) :
    0 ≤ alternativeOn rho Finset.univ := by
  obtain ⟨Ψ, hP⟩ := S191B_purify rho hrho.1
  have hΨ : (S191B_pure Ψ).trace = 1 := by
    rw [← S191B_marg_trace _ Prod.fst Prod.snd (fun y y' h => by simpa using h), hP, hrho.2]
  set F : ℕ → ℝ := fun k => marginalEntropyBits rho (Finset.univ.filter (fun j : Fin n => j.val < k))
    with hF
  have hsum := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin n))) =>
    S191B_han rho Ψ hP hΨ i)
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul] at hsum
  have htel : ∑ i : Fin n, (F (i.val + 1) - F i.val) = F n - F 0 := by
    rw [Fin.sum_univ_eq_sum_range (fun k => F (k + 1) - F k), Finset.sum_range_sub]
  have hFn : F n = marginalEntropyBits rho Finset.univ := by
    simp only [hF]; congr 1; ext j; simp
  have hF0 : F 0 = 0 := by
    simp only [hF]
    rw [show (Finset.univ.filter (fun j : Fin n => j.val < 0)) = ∅ by ext j; simp]
    exact S191B_empty rho Ψ hP hΨ
  rw [Finset.sum_sub_distrib] at htel
  unfold alternativeOn
  simp only [Finset.card_univ, Fintype.card_fin]
  rw [Nat.cast_sub (by omega : 1 ≤ n)]
  push_cast
  simp only [hF] at htel hFn hF0
  linarith
end S191B_final

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Claimed50.P33 (RegisterBasis SubBasis) in
open QAlgorithms.Papers.Independent.Information100.P21 (ghzKet) in
open QAlgorithms QAlgorithms.Papers.Independent.Support50.P43 in
theorem solution {n : ℕ} (hn : 2 ≤ n) {D : Fin n → Type}
    [∀ i, Fintype (D i)] [∀ i, Nonempty (D i)]
    (rho : Matrix (RegisterBasis D) (RegisterBasis D) ℂ) (hrho : IsDensityMatrix rho) :
    0 ≤ alternativeOn rho Finset.univ :=
  S191B_main hn rho hrho

#print axioms solution
