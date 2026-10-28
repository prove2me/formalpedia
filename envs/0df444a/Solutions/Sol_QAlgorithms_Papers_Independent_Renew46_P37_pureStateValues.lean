-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Renew46.P37.pureStateValues
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T16:28:19.974788+00:00
-- url     : https://prove2.me/submissions/df828032-d803-471c-85e9-7c3b3ee5c7dc

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P37
import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P20

noncomputable section
open scoped Matrix ComplexConjugate ComplexOrder

set_option linter.unusedSectionVars false

section psv204_ent
open Matrix Polynomial

lemma psv204_spec_finite {ι : Type*} [Fintype ι] {inst : DecidableEq ι} (A : Matrix ι ι ℂ)
    (hA : A.IsHermitian) : (spectrum ℝ A).Finite := by
  rw [hA.spectrum_real_eq_range_eigenvalues]; exact Set.finite_range _

lemma psv204_vn_poly {ι : Type*} [Fintype ι] {inst : DecidableEq ι} (A : Matrix ι ι ℂ)
    (hA : A.IsHermitian) (p : ℝ[X])
    (hp : ∀ x ∈ spectrum ℝ A, p.eval x = x * Real.logb 2 x) :
    QAlgorithms.vnEntropy A = -(aeval A p).trace.re := by
  unfold QAlgorithms.vnEntropy
  rw [cfc_congr (g := fun x => p.eval x) (fun x hx => (hp x hx).symm),
    cfc_polynomial p A hA.isSelfAdjoint]

/-- interpolation polynomial of x log x on a finite set -/
def psv204_interp (s : Finset ℝ) : ℝ[X] :=
  Lagrange.interpolate s id (fun x => x * Real.logb 2 x)

lemma psv204_interp_eval (s : Finset ℝ) {x : ℝ} (hx : x ∈ s) :
    (psv204_interp s).eval x = x * Real.logb 2 x :=
  Lagrange.eval_interpolate_at_node (v := id) _ (Set.injOn_id _) hx

lemma psv204_vn_submatrix {ι κ : Type*} [Fintype ι] [Fintype κ] {inst : DecidableEq ι}
    {inst' : DecidableEq κ} (A : Matrix ι ι ℂ) (hA : A.IsHermitian) (e : κ ≃ ι) :
    QAlgorithms.vnEntropy (A.submatrix e e) = QAlgorithms.vnEntropy A := by
  set s := (psv204_spec_finite A hA).toFinset
  have hsub : A.submatrix e e = Matrix.reindexAlgEquiv ℝ ℂ e.symm A := by
    ext a b; simp [Matrix.coe_reindexAlgEquiv]
  have hspec : spectrum ℝ (A.submatrix e e) = spectrum ℝ A := by
    rw [hsub]; exact AlgEquiv.spectrum_eq _ _
  rw [psv204_vn_poly A hA (psv204_interp s) (fun x hx => psv204_interp_eval s (by simpa [s] using hx)),
    psv204_vn_poly _ (hA.submatrix e) (psv204_interp s)
      (fun x hx => psv204_interp_eval s (by rw [hspec] at hx; simpa [s] using hx))]
  rw [hsub, Polynomial.aeval_algEquiv, AlgHom.comp_apply]
  congr 2
  simp only [AlgEquiv.coe_toAlgHom, Matrix.coe_reindexAlgEquiv, Matrix.reindex_apply,
    Equiv.symm_symm, Matrix.trace, Matrix.diag, Matrix.submatrix_apply]
  exact e.sum_comp (fun i => (aeval A (psv204_interp s)) i i)

lemma psv204_vn_conj {ι : Type*} [Fintype ι] {inst : DecidableEq ι} (A : Matrix ι ι ℂ)
    (hA : A.IsHermitian) :
    QAlgorithms.vnEntropy (A.map (starRingEnd ℂ)) = QAlgorithms.vnEntropy A := by
  set s := (psv204_spec_finite A hA).toFinset
  set φ : Matrix ι ι ℂ ≃ₐ[ℝ] Matrix ι ι ℂ := AlgEquiv.mapMatrix Complex.conjAe
  have hφ : A.map (starRingEnd ℂ) = φ A := rfl
  have hspec : spectrum ℝ (A.map (starRingEnd ℂ)) = spectrum ℝ A := by
    rw [hφ]; exact AlgEquiv.spectrum_eq _ _
  have hH : (A.map (starRingEnd ℂ)).IsHermitian := by
    ext i j; have := congrFun (congrFun hA i) j
    simp only [conjTranspose_apply, map_apply] at this ⊢
    rw [← this]; simp
  rw [psv204_vn_poly A hA (psv204_interp s) (fun x hx => psv204_interp_eval s (by simpa [s] using hx)),
    psv204_vn_poly _ hH (psv204_interp s)
      (fun x hx => psv204_interp_eval s (by rw [hspec] at hx; simpa [s] using hx))]
  rw [hφ, Polynomial.aeval_algEquiv, AlgHom.comp_apply]
  have htr : ∀ X : Matrix ι ι ℂ, (φ X).trace = starRingEnd ℂ X.trace := by
    intro X
    simp only [φ, AlgEquiv.mapMatrix_apply, Matrix.trace, Matrix.diag, Matrix.map_apply, map_sum]
    rfl
  simp only [AlgEquiv.coe_toAlgHom]
  rw [htr, Complex.conj_re]

lemma psv204_pow_mul {κ ι : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (M : Matrix κ ι ℂ) (N : Matrix ι κ ℂ) (k : ℕ) :
    (M * N) ^ (k + 1) = M * (N * M) ^ k * N := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, ih, pow_succ]; simp only [Matrix.mul_assoc]

lemma psv204_tr_pow {κ ι : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (M : Matrix κ ι ℂ) (N : Matrix ι κ ℂ) (k : ℕ) :
    ((M * N) ^ (k + 1)).trace = ((N * M) ^ (k + 1)).trace := by
  rw [psv204_pow_mul, Matrix.mul_assoc, Matrix.trace_mul_comm, Matrix.mul_assoc, pow_succ]

lemma psv204_vn_mul_comm {κ ι : Type*} [Fintype ι] [Fintype κ] {inst : DecidableEq ι}
    {inst' : DecidableEq κ} (M : Matrix κ ι ℂ) :
    QAlgorithms.vnEntropy (M * Mᴴ) = QAlgorithms.vnEntropy (Mᴴ * M) := by
  have h1 : (M * Mᴴ).IsHermitian := isHermitian_mul_conjTranspose_self M
  have h2 : (Mᴴ * M).IsHermitian := isHermitian_conjTranspose_mul_self M
  set s : Finset ℝ := insert 0 ((psv204_spec_finite (inst := inst') _ h1).toFinset ∪
    (psv204_spec_finite (inst := inst) _ h2).toFinset)
  set p := psv204_interp s
  rw [psv204_vn_poly _ h1 p (fun x hx => psv204_interp_eval s (by simp [s, hx])),
    psv204_vn_poly _ h2 p (fun x hx => psv204_interp_eval s (by simp [s, hx]))]
  have h0 : p.coeff 0 = 0 := by
    rw [Polynomial.coeff_zero_eq_eval_zero, psv204_interp_eval s (by simp [s])]; simp
  congr 2
  rw [Polynomial.aeval_eq_sum_range, Polynomial.aeval_eq_sum_range, Matrix.trace_sum,
    Matrix.trace_sum, Finset.sum_range_succ', Finset.sum_range_succ']
  simp only [h0, zero_smul, Matrix.trace_zero, add_zero, Matrix.trace_smul]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [psv204_tr_pow]

end psv204_ent

section psv204_marg
open Matrix
open scoped Classical
open QAlgorithms.Papers.Independent.Gap48.P20 (redistributionMarginal)

def psv204_pure {Y : Type*} (Ψ : Y → ℂ) : Matrix Y Y ℂ := Matrix.of fun a b => Ψ a * conj (Ψ b)

def psv204_M {Y K F : Type*} [Fintype Y] (Ψ : Y → ℂ) (k : Y → K) (f : Y → F) : Matrix K F ℂ :=
  fun a z => ∑ y, if k y = a ∧ f y = z then Ψ y else 0

lemma psv204_pure_marg {Y K F : Type*} [Fintype Y] [Fintype F] (Ψ : Y → ℂ) (k : Y → K)
    (f : Y → F) : redistributionMarginal (psv204_pure Ψ) k f =
      psv204_M Ψ k f * (psv204_M Ψ k f)ᴴ := by
  ext a b
  simp only [redistributionMarginal, Matrix.mul_apply, Matrix.conjTranspose_apply, psv204_M,
    psv204_pure, Matrix.of_apply, star_sum, Finset.sum_mul_sum]
  symm
  rw [Finset.sum_comm]; refine Finset.sum_congr rfl (fun x _ => ?_)
  rw [Finset.sum_comm]; refine Finset.sum_congr rfl (fun y _ => ?_)
  rw [Finset.sum_eq_single (f x)]
  · by_cases h1 : k x = a <;> by_cases h2 : k y = b <;> by_cases h3 : f x = f y <;>
      simp [h1, h2, h3, eq_comm (a := f y)]
  · intro z _ hz; simp [Ne.symm hz]
  · simp

lemma psv204_marg_forget {Y K F F' : Type*} [Fintype Y] (ρ : Matrix Y Y ℂ) (k : Y → K)
    (f : Y → F) (f' : Y → F') (hf : ∀ x y, f x = f y ↔ f' x = f' y) :
    redistributionMarginal ρ k f = redistributionMarginal ρ k f' := by
  ext a b
  simp only [redistributionMarginal]
  refine Finset.sum_congr rfl (fun x _ => Finset.sum_congr rfl (fun y _ => ?_))
  simp only [hf x y]

lemma psv204_vn_keep {Y K K' F : Type*} [Fintype Y] [Fintype K] [Fintype K']
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
  rw [← hsub, psv204_vn_submatrix _ hH]

lemma psv204_pure_herm {Y K F : Type*} [Fintype Y] [Fintype F] (Ψ : Y → ℂ) (k : Y → K)
    (f : Y → F) : (redistributionMarginal (psv204_pure Ψ) k f).IsHermitian := by
  rw [psv204_pure_marg]; exact isHermitian_mul_conjTranspose_self _

lemma psv204_vn_swap {Y K F : Type*} [Fintype Y] [Fintype K] [Fintype F]
    {inst : DecidableEq K} {inst' : DecidableEq F} (Ψ : Y → ℂ) (k : Y → K) (f : Y → F) :
    QAlgorithms.vnEntropy (redistributionMarginal (psv204_pure Ψ) k f) =
      QAlgorithms.vnEntropy (redistributionMarginal (psv204_pure Ψ) f k) := by
  rw [psv204_pure_marg, psv204_pure_marg]
  set M := psv204_M Ψ k f
  have hN : psv204_M Ψ f k * (psv204_M Ψ f k)ᴴ = (Mᴴ * M).map (starRingEnd ℂ) := by
    ext z w
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.map_apply, map_sum, map_mul,
      M, psv204_M]
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
  rw [hN, psv204_vn_conj _ (isHermitian_conjTranspose_mul_self M), psv204_vn_mul_comm]

lemma psv204_marg_trace {Y K F : Type*} [Fintype Y] [Fintype K] (ρ : Matrix Y Y ℂ)
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

lemma psv204_pure_density {Y K F : Type*} [Fintype Y] [Fintype K] [Fintype F] (Ψ : Y → ℂ)
    (hΨ : (psv204_pure Ψ).trace = 1) (k : Y → K) (f : Y → F)
    (hinj : Function.Injective (fun y => (k y, f y))) :
    QAlgorithms.IsDensityMatrix (redistributionMarginal (psv204_pure Ψ) k f) := by
  refine ⟨?_, ?_⟩
  · rw [psv204_pure_marg]; exact posSemidef_self_mul_conjTranspose _
  · rw [psv204_marg_trace _ _ _ hinj, hΨ]

lemma psv204_vn_unit {inst : DecidableEq Unit} (A : Matrix Unit Unit ℂ) (h : A.trace = 1) :
    QAlgorithms.vnEntropy A = 0 := by
  have : A = 1 := by
    ext a b; cases a; cases b; simpa [Matrix.trace] using h
  rw [this]; simp [QAlgorithms.vnEntropy]

lemma psv204_inst {ι : Type*} [Fintype ι] (i1 i2 : DecidableEq ι) (A : Matrix ι ι ℂ) :
    @QAlgorithms.vnEntropy ι _ i1 A = @QAlgorithms.vnEntropy ι _ i2 A := by
  congr


lemma psv204_vn_eq {Y K K' F F' : Type*} [Fintype Y] [Fintype K] [Fintype K'] [Fintype F']
    {inst : DecidableEq K} {inst' : DecidableEq K'} (Ψ : Y → ℂ) (k : Y → K) (f : Y → F)
    (k' : Y → K') (f' : Y → F') (hk : ∀ x y, k x = k y ↔ k' x = k' y)
    (hs : Function.Surjective k) (hs' : Function.Surjective k')
    (hf : ∀ x y, f x = f y ↔ f' x = f' y) :
    QAlgorithms.vnEntropy (redistributionMarginal (psv204_pure Ψ) k f) =
      QAlgorithms.vnEntropy (redistributionMarginal (psv204_pure Ψ) k' f') := by
  rw [psv204_marg_forget _ k f f' hf]
  exact psv204_vn_keep _ k k' f' hk hs hs' (psv204_pure_herm _ _ _)

lemma psv204_vn_uniq {ι : Type*} [Fintype ι] [Subsingleton ι] {inst : DecidableEq ι}
    (A : Matrix ι ι ℂ) (h : A.trace = 1) : QAlgorithms.vnEntropy A = 0 := by
  have hA : A = 1 := by
    ext a b
    rw [Subsingleton.elim b a, Matrix.one_apply_eq]
    rw [← h, Matrix.trace]
    have : (Finset.univ : Finset ι) = {a} := by
      ext c; simp [Subsingleton.elim c a]
    rw [this, Finset.sum_singleton]; rfl
  rw [hA]; unfold QAlgorithms.vnEntropy; rw [cfc_apply_one]; simp

end psv204_marg

section psv204_reg
open Matrix
open QAlgorithms.Papers.Independent.Claimed50.P33 (RegisterBasis SubBasis registerMarginal
  trivialExtension entropyAt)
open QAlgorithms.Papers.Independent.Gap48.P20 (redistributionMarginal)
attribute [local instance] Classical.propDecidable Classical.decEq

variable {n : ℕ} {D : Fin n → Type} [∀ i, Fintype (D i)]

def psv204_rl (s : Finset (Fin n)) (x : RegisterBasis D) : SubBasis D s := fun i => x i.val

def psv204_H (ρ : Matrix (RegisterBasis D) (RegisterBasis D) ℂ) (s : Finset (Fin n)) : ℝ :=
  entropyAt (trivialExtension ρ) s

lemma psv204_req (s : Finset (Fin n)) (x y : RegisterBasis D) :
    psv204_rl s x = psv204_rl s y ↔ ∀ i ∈ s, x i = y i := by
  constructor
  · intro h i hi; exact congrFun h ⟨i, hi⟩
  · intro h; funext i; exact h i.1 i.2
lemma psv204_C1 (ρ : Matrix (RegisterBasis D) (RegisterBasis D) ℂ) (T : Finset (Fin n)) :
    registerMarginal (trivialExtension ρ) T =
      redistributionMarginal ρ (fun x => (psv204_rl T x, ())) (fun x => psv204_rl Tᶜ x) := by
  ext a b
  simp only [registerMarginal, trivialExtension, redistributionMarginal]
  refine Finset.sum_congr rfl (fun x _ => Finset.sum_congr rfl (fun y _ => ?_))
  have hiff : ((∀ i (hi : i ∈ T), x i = a.1 ⟨i, hi⟩ ∧ y i = b.1 ⟨i, hi⟩) ∧
      (∀ i, i ∉ T → x i = y i)) ↔ ((psv204_rl T x, ()) = a ∧ (psv204_rl T y, ()) = b ∧
      psv204_rl Tᶜ x = psv204_rl Tᶜ y) := by
    rw [psv204_req]
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

lemma psv204_S_eq (ρ : Matrix (RegisterBasis D) (RegisterBasis D) ℂ) (T : Finset (Fin n)) :
    psv204_H ρ T = QAlgorithms.vnEntropy
      (redistributionMarginal ρ (fun x => (psv204_rl T x, ())) (fun x => psv204_rl Tᶜ x)) := by
  unfold psv204_H entropyAt
  rw [psv204_C1]
  exact psv204_inst _ _ _

lemma psv204_rl_surj [∀ i, Nonempty (D i)] (T : Finset (Fin n)) :
    Function.Surjective (psv204_rl (D := D) T) := by
  intro a
  obtain ⟨z⟩ : Nonempty (RegisterBasis D) := inferInstance
  refine ⟨fun k => if h : k ∈ T then a ⟨k, h⟩ else z k, ?_⟩
  funext i; simp [psv204_rl, i.2]

lemma psv204_rl_surj' [∀ i, Nonempty (D i)] (T : Finset (Fin n)) :
    Function.Surjective (fun x : RegisterBasis D => (psv204_rl T x, ())) := by
  rintro ⟨a, u⟩
  obtain ⟨x, hx⟩ := psv204_rl_surj T a
  exact ⟨x, by simp [hx]⟩

lemma psv204_H_empty [∀ i, Nonempty (D i)] (ρ : Matrix (RegisterBasis D) (RegisterBasis D) ℂ)
    (htr : ρ.trace = 1) : psv204_H ρ ∅ = 0 := by
  rw [psv204_S_eq]
  apply psv204_vn_uniq
  rw [psv204_marg_trace, htr]
  intro x y h
  simp only [Prod.mk.injEq, and_true] at h
  funext i
  exact congrFun h.2 ⟨i, by simp⟩

lemma psv204_univ (Ψ : RegisterBasis D → ℂ) (htr : (psv204_pure Ψ).trace = 1) :
    psv204_H (psv204_pure Ψ) Finset.univ = 0 := by
  rw [psv204_S_eq, psv204_vn_swap (inst' := Classical.decEq _)]
  have : Subsingleton (SubBasis D (Finset.univ : Finset (Fin n))ᶜ) :=
    ⟨fun a b => funext fun i => absurd i.2 (by simp)⟩
  apply psv204_vn_uniq
  rw [psv204_marg_trace, htr]
  intro x y h
  simp only [Prod.mk.injEq] at h
  funext i; exact congrFun h.2.1 ⟨i, Finset.mem_univ _⟩

lemma psv204_erase [∀ i, Nonempty (D i)] (Ψ : RegisterBasis D → ℂ) (i : Fin n) :
    psv204_H (psv204_pure Ψ) (Finset.univ.erase i) = psv204_H (psv204_pure Ψ) {i} := by
  rw [psv204_S_eq, psv204_S_eq, psv204_vn_swap (inst' := Classical.decEq _)]
  apply psv204_vn_eq
  · intro x y
    simp only [Prod.mk.injEq, psv204_req, and_true, Finset.mem_compl, Finset.mem_erase,
      Finset.mem_singleton, Finset.mem_univ, ne_eq, not_not]
  · exact psv204_rl_surj _
  · exact psv204_rl_surj' _
  · intro x y
    simp only [Prod.mk.injEq, psv204_req, and_true, Finset.mem_compl, Finset.mem_erase,
      Finset.mem_singleton, Finset.mem_univ, ne_eq, and_true]

lemma psv204_info [∀ i, Nonempty (D i)] (kind : QAlgorithms.Papers.Independent.Claimed50.P33.InformationKind)
    (Ψ : RegisterBasis D → ℂ) (htr : (psv204_pure Ψ).trace = 1) :
    QAlgorithms.Papers.Independent.Claimed50.P33.info kind (psv204_pure Ψ)
      (QAlgorithms.Papers.Independent.Claimed50.P33.singleParties n) ∅ =
      ∑ i, psv204_H (psv204_pure Ψ) {i} := by
  have hU : QAlgorithms.Papers.Independent.Claimed50.P33.allParties
      (QAlgorithms.Papers.Independent.Claimed50.P33.singleParties n) = Finset.univ := by
    ext k; simp [QAlgorithms.Papers.Independent.Claimed50.P33.allParties,
      QAlgorithms.Papers.Independent.Claimed50.P33.singleParties]
  have hE : ∀ i : Fin n, (Finset.univ.erase i).biUnion
      (QAlgorithms.Papers.Independent.Claimed50.P33.singleParties n) = Finset.univ.erase i := by
    intro i; ext k; simp [QAlgorithms.Papers.Independent.Claimed50.P33.singleParties]
  have key : ∀ T, entropyAt (trivialExtension (psv204_pure Ψ)) T = psv204_H (psv204_pure Ψ) T :=
    fun _ => rfl
  have h0 := psv204_H_empty _ htr
  have h1 := psv204_univ Ψ htr
  unfold QAlgorithms.Papers.Independent.Claimed50.P33.info
    QAlgorithms.Papers.Independent.Claimed50.P33.conditionalMultipartiteInformation
  cases kind
  · simp only [Finset.union_empty, hU, key, h0, h1, mul_zero, sub_zero,
      QAlgorithms.Papers.Independent.Claimed50.P33.singleParties]
  · simp only [Finset.union_empty, hU, hE, key, h0, h1, mul_zero, sub_zero, psv204_erase]

end psv204_reg

section psv204_ex
open Matrix
open QAlgorithms.Papers.Independent.Claimed50.P33 (RegisterBasis SubBasis registerMarginal
  trivialExtension entropyAt)
open QAlgorithms.Papers.Independent.Gap48.P20 (redistributionMarginal)
attribute [local instance] Classical.propDecidable Classical.decEq

lemma psv204_ite_sum {α : Type*} (s : Finset α) (c : Prop) [Decidable c] (g : α → ℂ) :
    (if c then ∑ i ∈ s, g i else 0) = ∑ i ∈ s, if c then g i else 0 := by
  split_ifs <;> simp

lemma psv204_two {Y K F : Type*} [Fintype Y] (e : Fin 2 → Y) (w : Fin 2 → ℂ) (he : e 0 ≠ e 1)
    (Ψ : Y → ℂ) (hΨ0 : Ψ (e 0) = w 0) (hΨ1 : Ψ (e 1) = w 1)
    (hΨz : ∀ y, y ≠ e 0 → y ≠ e 1 → Ψ y = 0)
    (k : Y → K) (f : Y → F) (a b : K) :
    redistributionMarginal (psv204_pure Ψ) k f a b = ∑ j, ∑ l,
      if k (e j) = a ∧ k (e l) = b ∧ f (e j) = f (e l) then w j * conj (w l) else 0 := by
  have pw : ∀ x y, (if k x = a ∧ k y = b ∧ f x = f y then psv204_pure Ψ x y else 0) =
      ∑ j, ∑ l, if x = e j then (if y = e l then
        (if k (e j) = a ∧ k (e l) = b ∧ f (e j) = f (e l) then w j * conj (w l) else 0)
        else 0) else 0 := by
    intro x y
    simp only [Fin.sum_univ_two, psv204_pure, Matrix.of_apply]
    by_cases hx0 : x = e 0
    · subst hx0
      by_cases hy0 : y = e 0
      · subst hy0; simp [he, hΨ0]
      · by_cases hy1 : y = e 1
        · subst hy1; simp [he, Ne.symm he, hΨ0, hΨ1]
        · simp [hy0, hy1, he, hΨz y hy0 hy1]
    · by_cases hx1 : x = e 1
      · subst hx1
        by_cases hy0 : y = e 0
        · subst hy0; simp [he, Ne.symm he, hΨ0, hΨ1]
        · by_cases hy1 : y = e 1
          · subst hy1; simp [Ne.symm he, hΨ1]
          · simp [hy0, hy1, Ne.symm he, hΨz y hy0 hy1]
      · simp [hx0, hx1, hΨz x hx0 hx1]
  unfold redistributionMarginal
  simp only [pw]
  simp only [Fin.sum_univ_two, Finset.sum_add_distrib]
  simp only [← psv204_ite_sum, Finset.sum_ite_eq', Finset.mem_univ, if_true]

lemma psv204_vn_half {inst : DecidableEq (Fin 2)} :
    @QAlgorithms.vnEntropy (Fin 2) _ inst (algebraMap ℝ (Matrix (Fin 2) (Fin 2) ℂ) (1/2)) = 1 := by
  unfold QAlgorithms.vnEntropy
  rw [cfc_algebraMap]
  have hl : Real.logb 2 (1/2) = -1 := by
    rw [one_div, Real.logb_inv, Real.logb_self_eq_one (by norm_num)]
  rw [hl]
  simp [Matrix.trace, Matrix.algebraMap_matrix_apply]

lemma psv204_trace {Y : Type*} [Fintype Y] (e : Fin 2 → Y) (w : Fin 2 → ℂ) (he : e 0 ≠ e 1)
    (Ψ : Y → ℂ) (hΨ0 : Ψ (e 0) = w 0) (hΨ1 : Ψ (e 1) = w 1)
    (hΨz : ∀ y, y ≠ e 0 → y ≠ e 1 → Ψ y = 0)
    (hw : ∀ j, w j * conj (w j) = 1/2) : (psv204_pure Ψ).trace = 1 := by
  rw [← psv204_marg_trace (psv204_pure Ψ) (fun _ => ()) id (fun x y h => by simpa using h)]
  simp only [Matrix.trace, Matrix.diag, Fintype.univ_punit, Finset.sum_singleton]
  rw [psv204_two e w he Ψ hΨ0 hΨ1 hΨz]
  simp [Fin.sum_univ_two, he, Ne.symm he, hw]
  norm_num

variable {m : ℕ}

lemma psv204_qubit (e : Fin 2 → (Fin m → Fin 2)) (w : Fin 2 → ℂ) (he : e 0 ≠ e 1)
    (Ψ : (Fin m → Fin 2) → ℂ) (hΨ0 : Ψ (e 0) = w 0) (hΨ1 : Ψ (e 1) = w 1)
    (hΨz : ∀ y, y ≠ e 0 → y ≠ e 1 → Ψ y = 0)
    (hw : ∀ j, w j * conj (w j) = 1/2)
    (hoff : ∀ i, psv204_rl (D := fun _ => Fin 2) ({i} : Finset (Fin m))ᶜ (e 0) ≠
      psv204_rl (D := fun _ => Fin 2) ({i} : Finset (Fin m))ᶜ (e 1))
    (hdiff : ∀ i, e 0 i ≠ e 1 i) (i : Fin m) :
    psv204_H (D := fun _ => Fin 2) (psv204_pure Ψ) {i} = 1 := by
  rw [psv204_S_eq, psv204_vn_eq Ψ _ _ (fun x => x i) (psv204_rl ({i} : Finset (Fin m))ᶜ)
    (fun x y => by simp [psv204_req]) (psv204_rl_surj' _) (fun a => ⟨fun _ => a, rfl⟩)
    (fun _ _ => Iff.rfl)]
  have hmat : redistributionMarginal (psv204_pure Ψ) (fun x => x i)
      (psv204_rl (D := fun _ => Fin 2) ({i} : Finset (Fin m))ᶜ) =
      algebraMap ℝ (Matrix (Fin 2) (Fin 2) ℂ) (1/2) := by
    ext a b
    rw [psv204_two e w he Ψ hΨ0 hΨ1 hΨz]
    simp only [Fin.sum_univ_two, hoff i, Ne.symm (hoff i), and_false, if_false, add_zero,
      zero_add, hw, Matrix.algebraMap_matrix_apply]
    have hd := hdiff i
    generalize e 0 i = p at hd ⊢
    generalize e 1 i = q at hd ⊢
    fin_cases p <;> fin_cases q <;> fin_cases a <;> fin_cases b <;> simp at hd ⊢
  rw [hmat]; exact psv204_vn_half

lemma psv204_val (e : Fin 2 → (Fin m → Fin 2)) (w : Fin 2 → ℂ) (he : e 0 ≠ e 1)
    (Ψ : (Fin m → Fin 2) → ℂ) (hΨ0 : Ψ (e 0) = w 0) (hΨ1 : Ψ (e 1) = w 1)
    (hΨz : ∀ y, y ≠ e 0 → y ≠ e 1 → Ψ y = 0)
    (hw : ∀ j, w j * conj (w j) = 1/2)
    (hoff : ∀ i, psv204_rl (D := fun _ => Fin 2) ({i} : Finset (Fin m))ᶜ (e 0) ≠
      psv204_rl (D := fun _ => Fin 2) ({i} : Finset (Fin m))ᶜ (e 1))
    (hdiff : ∀ i, e 0 i ≠ e 1 i)
    (kind : QAlgorithms.Papers.Independent.Claimed50.P33.InformationKind) :
    QAlgorithms.Papers.Independent.Claimed50.P33.info kind (D := fun _ => Fin 2) (psv204_pure Ψ)
      (QAlgorithms.Papers.Independent.Claimed50.P33.singleParties m) ∅ = m := by
  rw [psv204_info kind Ψ (psv204_trace e w he Ψ hΨ0 hΨ1 hΨz hw)]
  rw [Finset.sum_congr rfl (fun i _ => psv204_qubit e w he Ψ hΨ0 hΨ1 hΨz hw hoff hdiff i)]
  simp

lemma psv204_off (hm : 2 ≤ m) (i : Fin m) (u v : Fin m → Fin 2) (h : ∀ j, u j ≠ v j) :
    psv204_rl (D := fun _ => Fin 2) ({i} : Finset (Fin m))ᶜ u ≠
      psv204_rl (D := fun _ => Fin 2) ({i} : Finset (Fin m))ᶜ v := by
  intro hh
  obtain ⟨j, hj⟩ : ∃ j : Fin m, j ≠ i := by
    by_cases h0 : i.val = 0
    · exact ⟨⟨1, by omega⟩, fun h' => by have := congrArg Fin.val h'; simp at this; omega⟩
    · exact ⟨⟨0, by omega⟩, fun h' => by have := congrArg Fin.val h'; simp at this; omega⟩
  exact h j (congrFun hh ⟨j, by simp [hj]⟩)

lemma psv204_singlet (kind : QAlgorithms.Papers.Independent.Claimed50.P33.InformationKind) :
    QAlgorithms.Papers.Independent.Claimed50.P33.info kind
      (QAlgorithms.pureDensity QAlgorithms.Papers.Independent.Renew46.P37.labelledSingletVector)
      (QAlgorithms.Papers.Independent.Claimed50.P33.singleParties 2) ∅ = 2 := by
  have h2 : ((Real.sqrt 2 / 2 : ℝ) : ℂ) * ((Real.sqrt 2 / 2 : ℝ) : ℂ) = 1/2 := by
    rw [← Complex.ofReal_mul]
    have : Real.sqrt 2 / 2 * (Real.sqrt 2 / 2) = 1/2 := by
      rw [div_mul_div_comm, Real.mul_self_sqrt (by norm_num)]; norm_num
    rw [this]; push_cast; ring
  have hne : (![![0, 1], ![1, 0]] : Fin 2 → Fin 2 → Fin 2) 0 ≠ ![![0, 1], ![1, 0]] 1 := by
    decide
  have hd : ∀ i, (![![0, 1], ![1, 0]] : Fin 2 → Fin 2 → Fin 2) 0 i ≠ ![![0, 1], ![1, 0]] 1 i := by
    decide
  have h := psv204_val (m := 2) ![![0, 1], ![1, 0]]
    ![((Real.sqrt 2 / 2 : ℝ) : ℂ), -((Real.sqrt 2 / 2 : ℝ) : ℂ)] hne
    (fun x => QAlgorithms.Papers.Independent.Renew46.P37.labelledSingletVector x) ?_ ?_ ?_ ?_
    (fun i => psv204_off le_rfl i _ _ (hd)) hd kind
  · exact h.trans (by norm_num)
  · rfl
  · rfl
  · intro y hy0 hy1
    have hy : y = ![y 0, y 1] := by funext j; fin_cases j <;> rfl
    rw [hy] at hy0 hy1 ⊢
    show QAlgorithms.Papers.Independent.Dependency50.P42.singletVector (y 0, y 1) = 0
    simp only [QAlgorithms.Papers.Independent.Dependency50.P42.singletVector]
    generalize y 0 = p at hy0 hy1; generalize y 1 = q at hy0 hy1
    fin_cases p <;> fin_cases q <;> simp at hy0 hy1 ⊢
  · intro j; fin_cases j
    · show ((Real.sqrt 2 / 2 : ℝ) : ℂ) * conj ((Real.sqrt 2 / 2 : ℝ) : ℂ) = 1/2
      rw [Complex.conj_ofReal, h2]
    · show (-((Real.sqrt 2 / 2 : ℝ) : ℂ)) * conj (-((Real.sqrt 2 / 2 : ℝ) : ℂ)) = 1/2
      rw [map_neg, Complex.conj_ofReal, neg_mul_neg, h2]

lemma psv204_ghz (kind : QAlgorithms.Papers.Independent.Claimed50.P33.InformationKind) :
    QAlgorithms.Papers.Independent.Claimed50.P33.info kind
      (QAlgorithms.pureDensity (QAlgorithms.Papers.Independent.Renew46.P37.ghzVector 3))
      (QAlgorithms.Papers.Independent.Claimed50.P33.singleParties 3) ∅ = 3 := by
  have h2 : (Real.sqrt 2 : ℂ)⁻¹ * (Real.sqrt 2 : ℂ)⁻¹ = 1/2 := by
    rw [← mul_inv, ← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]; push_cast; ring
  have hne : (![fun _ => 0, fun _ => 1] : Fin 2 → Fin 3 → Fin 2) 0 ≠
      ![fun _ => 0, fun _ => 1] 1 := by
    intro h; have := congrFun h 0; simp at this
  have hd : ∀ i, (![fun _ => 0, fun _ => 1] : Fin 2 → Fin 3 → Fin 2) 0 i ≠
      ![fun _ => 0, fun _ => 1] 1 i := by
    intro i; simp
  have h := psv204_val (m := 3) ![fun _ => 0, fun _ => 1]
    ![(Real.sqrt 2 : ℂ)⁻¹, (Real.sqrt 2 : ℂ)⁻¹] hne
    (fun x => QAlgorithms.Papers.Independent.Renew46.P37.ghzVector 3 x) ?_ ?_ ?_ ?_
    (fun i => psv204_off (by norm_num) i _ _ hd) hd kind
  · exact h.trans (by norm_num)
  · simp [QAlgorithms.Papers.Independent.Renew46.P37.ghzVector]
  · simp [QAlgorithms.Papers.Independent.Renew46.P37.ghzVector]
  · intro y hy0 hy1
    have h0 : ¬ ∀ i, y i = 0 := fun h => hy0 (funext fun i => by simpa using h i)
    have h1 : ¬ ∀ i, y i = 1 := fun h => hy1 (funext fun i => by simpa using h i)
    simp [QAlgorithms.Papers.Independent.Renew46.P37.ghzVector, h0, h1]
  · intro j; fin_cases j <;> simp [Complex.conj_ofReal, h2]

end psv204_ex

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms in
open QAlgorithms.Papers.Independent.Renew46.P37 in
open QAlgorithms.Papers.Independent.Claimed50.P33
  (InformationKind RegisterBasis FiniteState singleParties allParties
   info entropyAt trivialExtension informationFunctional LocalInstrument
   IsContinuousFunctional partyProduct registerMarginal) in
theorem solution :
    (∀ (n : ℕ), 2 ≤ n → ∀ s : FiniteState n,
      QAlgorithms.Papers.Independent.Information100.P08.IsPure s.rho →
      qValue .dual s = localEntropySum s ∧ qValue .total s = localEntropySum s) ∧
    (∀ kind : InformationKind,
      info kind (pureDensity labelledSingletVector) (singleParties 2) ∅ = 2 ∧
      info kind (pureDensity (ghzVector 3)) (singleParties 3) ∅ = 3) := by
  refine ⟨fun n _ s hs => ?_, fun kind => ⟨psv204_singlet kind, psv204_ghz kind⟩⟩
  obtain ⟨v, -, hv⟩ := hs
  have : ∀ i, Nonempty (Fin (s.dims i)) := fun i => ⟨⟨0, s.positive i⟩⟩
  have htr : (psv204_pure (fun x => v x)).trace = 1 := by
    have := s.normalized.2; rw [hv] at this; exact this
  have hq : ∀ k : InformationKind, qValue k s = ∑ i, psv204_H (psv204_pure (fun x => v x)) {i} := by
    intro k
    rw [← psv204_info k _ htr]
    show info k s.rho (singleParties n) ∅ = _
    rw [hv]; rfl
  have hl : localEntropySum s = ∑ i, psv204_H (psv204_pure (fun x => v x)) {i} := by
    show ∑ i, entropyAt (trivialExtension s.rho) {i} = _
    rw [hv]; rfl
  exact ⟨(hq _).trans hl.symm, (hq _).trans hl.symm⟩

