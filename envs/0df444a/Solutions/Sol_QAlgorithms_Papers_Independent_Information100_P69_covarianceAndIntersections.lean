-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Information100.P69.covarianceAndIntersections
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T09:17:14.759719+00:00
-- url     : https://prove2.me/submissions/24e47fb5-37e1-42ed-9a2f-1d5f80d7d262

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P69

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

open QAlgorithms QAlgorithms.Papers.Independent.Information100.P69

namespace S201CAI

open scoped MatrixOrder in
lemma factor {ι : Type*} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℂ) (hM : M.PosSemidef) :
    ∃ B : Matrix ι ι ℂ, M = Bᴴ * B := by
  obtain ⟨B, hB⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hM.nonneg
  exact ⟨B, hB⟩

lemma ch_of {ι κ J : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [Fintype J]
    (M : Superop ι κ) (K : J → Matrix κ ι ℂ) (hK : ∑ j, (K j)ᴴ * K j = 1)
    (hM : ∀ X, M X = krausApply K X) : IsChannel M := by
  let e := Fintype.equivFin J
  refine ⟨Fintype.card J, fun i => K (e.symm i), ?_, fun X => ?_⟩
  · unfold IsKrausFamily; rw [← hK]; exact Equiv.sum_comp e.symm (fun j => (K j)ᴴ * K j)
  · rw [hM]; unfold krausApply; exact (Equiv.sum_comp e.symm (fun j => K j * X * (K j)ᴴ)).symm

lemma kraus_entry {ι κ J : Type*} [Fintype ι] [Fintype J] (M : J → Matrix κ ι ℂ)
    (X : Matrix ι ι ℂ) (b b' : κ) :
    ∑ j, ∑ a', ∑ a, M j b a * X a a' * star (M j b' a') =
      ∑ a', ∑ a, X a a' * ∑ j, M j b a * conj (M j b' a') := by
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a' _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [RCLike.star_def]; ring

lemma gram_kraus {ι κ J J' : Type*} [Fintype ι] [Fintype κ] [Fintype J] [Fintype J']
    (K : J → Matrix κ ι ℂ) (L : J' → Matrix κ ι ℂ)
    (h : ∀ b a b' a', ∑ j, K j b a * conj (K j b' a') = ∑ j, L j b a * conj (L j b' a')) :
    (∀ X, krausApply K X = krausApply L X) ∧
      (∑ j, (K j)ᴴ * K j = ∑ j, (L j)ᴴ * L j) := by
  constructor
  · intro X; ext b b'
    simp only [krausApply, Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Finset.sum_mul]
    rw [kraus_entry K, kraus_entry L]
    simp only [h]
  · ext a a'
    simp only [Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply]
    rw [Finset.sum_comm, Finset.sum_comm (f := fun j b => star (L j b a) * L j b a')]
    refine Finset.sum_congr rfl fun b _ => ?_
    have := congrArg (starRingEnd ℂ) (h b a b a')
    simp only [map_sum, map_mul, Complex.conj_conj] at this
    simp only [RCLike.star_def]
    rw [show (∑ j, (starRingEnd ℂ) (K j b a) * K j b a') = ∑ j, K j b a' * (starRingEnd ℂ) (K j b a)
      from Finset.sum_congr rfl fun _ _ => mul_comm _ _]
    rw [show (∑ j, (starRingEnd ℂ) (L j b a) * L j b a') = ∑ j, L j b a' * (starRingEnd ℂ) (L j b a)
      from Finset.sum_congr rfl fun _ _ => mul_comm _ _]
    have h2 := h b a' b a
    exact h2

/-- Kraus rank reduction: every channel has a Kraus family indexed by `κ × ι`. -/
lemma reduce {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    {m : ℕ} (E : Fin m → Matrix κ ι ℂ) :
    ∃ F : κ × ι → Matrix κ ι ℂ, (∀ X, krausApply E X = krausApply F X) ∧
      (∑ j, (E j)ᴴ * E j = ∑ j, (F j)ᴴ * F j) := by
  let G : Matrix (Fin m) (κ × ι) ℂ := Matrix.of fun j p => conj (E j p.1 p.2)
  obtain ⟨B, hB⟩ := factor (Gᴴ * G) (Matrix.posSemidef_conjTranspose_mul_self G)
  refine ⟨fun k => fun b a => conj (B k (b, a)), gram_kraus _ _ fun b a b' a' => ?_⟩
  have := congrArg (fun M => M (b, a) (b', a')) hB
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, G, Matrix.of_apply, RCLike.star_def,
    Complex.conj_conj] at this
  simp only [Complex.conj_conj]
  rw [this]


lemma ch_iff {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (M : Superop ι κ) : IsChannel M ↔
      ∃ F : κ × ι → Matrix κ ι ℂ, ∑ j, (F j)ᴴ * F j = 1 ∧ M = krausApply F := by
  constructor
  · rintro ⟨m, E, hE, hM⟩
    obtain ⟨F, h1, h2⟩ := reduce E
    exact ⟨F, by rw [← h2]; exact hE, funext fun X => by rw [hM, h1]⟩
  · rintro ⟨F, hF, rfl⟩
    exact ch_of _ F hF fun _ => rfl

lemma entry_le {ι κ J : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [Fintype J]
    (F : J → Matrix κ ι ℂ) (hF : ∑ j, (F j)ᴴ * F j = 1) (j : J) (b : κ) (a : ι) :
    ‖F j b a‖ ≤ 1 := by
  have h := congrArg (fun M => (M a a).re) hF
  simp only [Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply_eq,
    Complex.re_sum, Complex.one_re] at h
  have hterm : ∀ j b, (star (F j b a) * F j b a).re = ‖F j b a‖ ^ 2 := by
    intro j b
    rw [RCLike.star_def, ← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq]
    norm_cast
  simp only [hterm] at h
  have h1 : ‖F j b a‖ ^ 2 ≤ ∑ j, ∑ b, ‖F j b a‖ ^ 2 := by
    have := Finset.single_le_sum (f := fun b => ‖F j b a‖ ^ 2) (fun _ _ => by positivity)
      (Finset.mem_univ b)
    refine this.trans ?_
    exact Finset.single_le_sum (f := fun j => ∑ b, ‖F j b a‖ ^ 2)
      (fun _ _ => Finset.sum_nonneg fun _ _ => by positivity) (Finset.mem_univ j)
  rw [h] at h1
  nlinarith [norm_nonneg (F j b a)]

lemma ch_compact {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ] :
    IsCompact {M : Superop ι κ | IsChannel M} := by
  let S : Set (κ × ι → Matrix κ ι ℂ) := {F | ∑ j, (F j)ᴴ * F j = 1}
  have hS : IsCompact S := by
    have hP : IsCompact (Set.pi Set.univ fun _ : κ × ι =>
        (Set.pi Set.univ fun _ : κ => Set.pi Set.univ fun _ : ι => Metric.closedBall (0:ℂ) 1 :
          Set (Matrix κ ι ℂ))) :=
      isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_univ_pi fun _ =>
        isCompact_closedBall 0 1
    refine hP.of_isClosed_subset ?_ ?_
    · have hc : Continuous fun F : κ × ι → Matrix κ ι ℂ => ∑ j, (F j)ᴴ * F j := by
        fun_prop
      exact isClosed_singleton.preimage hc
    · intro F hF
      simp only [Set.mem_pi, Set.mem_univ, true_implies, Metric.mem_closedBall, dist_zero_right]
      intro j b a
      exact entry_le F hF j b a
  have heq : {M : Superop ι κ | IsChannel M} = (fun F => krausApply F) '' S := by
    ext M
    rw [Set.mem_setOf_eq, ch_iff]
    constructor
    · rintro ⟨F, hF, rfl⟩; exact ⟨F, hF, rfl⟩
    · rintro ⟨F, hF, rfl⟩; exact ⟨F, hF, rfl⟩
  rw [heq]
  refine hS.image ?_
  refine continuous_pi fun X => ?_
  unfold krausApply
  fun_prop


open scoped Kronecker

lemma conj_sub {α β γ δ : Type*} [Fintype α] [Fintype γ] (A : Matrix β α ℂ) (Y : Matrix α α ℂ)
    (e : δ ≃ β) (f : γ ≃ α) :
    (A * Y * Aᴴ).submatrix e e = A.submatrix e f * Y.submatrix f f * (A.submatrix e f)ᴴ := by
  rw [Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv]

lemma kraus_comp {α β γ J K : Type*} [Fintype α] [Fintype β] [Fintype J] [Fintype K]
    (Kk : J → Matrix γ β ℂ) (L : K → Matrix β α ℂ) (X : Matrix α α ℂ) :
    krausApply (fun p : J × K => Kk p.1 * L p.2) X = krausApply Kk (krausApply L X) := by
  unfold krausApply
  rw [Fintype.sum_prod_type]
  simp only [Matrix.mul_sum, Matrix.sum_mul, Matrix.conjTranspose_mul, Matrix.mul_assoc]

lemma kraus_comp_norm {α β γ J K : Type*} [Fintype α] [Fintype β] [Fintype γ] [Fintype J]
    [Fintype K] (Kk : J → Matrix γ β ℂ) (L : K → Matrix β α ℂ) :
    ∑ p : J × K, (Kk p.1 * L p.2)ᴴ * (Kk p.1 * L p.2) =
      ∑ k, (L k)ᴴ * (∑ j, (Kk j)ᴴ * Kk j) * L k := by
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  simp only [Matrix.mul_sum, Matrix.sum_mul, Matrix.conjTranspose_mul, Matrix.mul_assoc]

lemma kron_conj {α β γ δ : Type*} [Fintype α] [Fintype γ]
    (A : Matrix β α ℂ) (B : Matrix δ γ ℂ) (P : Matrix α α ℂ) (Q : Matrix γ γ ℂ) :
    (A ⊗ₖ B) * (P ⊗ₖ Q) * (A ⊗ₖ B)ᴴ = (A * P * Aᴴ) ⊗ₖ (B * Q * Bᴴ) := by
  rw [Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul]

def ptr {β γ : Type*} [Fintype γ] (Z : Matrix (β × γ) (β × γ) ℂ) : Matrix β β ℂ :=
  Matrix.of fun y z => ∑ b, Z (y, b) (z, b)

def ptrK {β γ : Type*} [DecidableEq β] [DecidableEq γ] (b : γ) : Matrix β (β × γ) ℂ :=
  Matrix.of fun y q => if q = (y, b) then 1 else 0

lemma ptr_kraus {β γ : Type*} [Fintype β] [Fintype γ] [DecidableEq β] [DecidableEq γ]
    (Z : Matrix (β × γ) (β × γ) ℂ) : ptr Z = krausApply (fun b : γ => ptrK (β := β) b) Z := by
  ext y z
  simp [ptr, ptrK, krausApply, Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply]

lemma ptrK_norm {β γ : Type*} [Fintype β] [Fintype γ] [DecidableEq β] [DecidableEq γ] :
    ∑ b : γ, (ptrK (β := β) b)ᴴ * ptrK (β := β) b = 1 := by
  refine Matrix.ext fun p q => ?_
  simp only [ptrK, Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply,
    Matrix.one_apply]
  obtain ⟨p1, p2⟩ := p
  obtain ⟨q1, q2⟩ := q
  by_cases h : (p1, p2) = (q1, q2)
  · rw [if_pos h]
    simp only [Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    rw [Finset.sum_eq_single p2]
    · simp
    · intro b _ hb; simp [Ne.symm hb]
    · simp
  · rw [if_neg h]
    refine Finset.sum_eq_zero fun b _ => ?_
    refine Finset.sum_eq_zero fun y _ => ?_
    by_cases h1 : (p1, p2) = (y, b)
    · by_cases h2 : (q1, q2) = (y, b)
      · exact absurd (h1.trans h2.symm) h
      · simp [h2]
    · simp [h1]

lemma ptr_conj {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ] [DecidableEq γ]
    (P : Matrix β α ℂ) (V : Matrix γ γ ℂ) (hV : Vᴴ * V = 1) (Z : Matrix (α × γ) (α × γ) ℂ) :
    ptr ((P ⊗ₖ V) * Z * (P ⊗ₖ V)ᴴ) = P * ptr Z * Pᴴ := by
  ext y z
  have hV' : ∀ c c', ∑ b, star (V b c') * V b c = if c' = c then 1 else 0 := by
    intro c c'
    have := congrArg (fun M => M c' c) hV
    simpa [Matrix.mul_apply, Matrix.one_apply] using this
  simp only [ptr, Matrix.of_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Matrix.kronecker_apply, Fintype.sum_prod_type, Finset.sum_mul, Finset.mul_sum]
  have e : ∀ (b : γ) (q1 : α) (y1 : γ) (x1 : α) (i : γ),
      P y x1 * V b i * Z (x1, i) (q1, y1) * star (P z q1 * V b y1) =
        (P y x1 * Z (x1, i) (q1, y1) * star (P z q1)) * (star (V b y1) * V b i) := by
    intros; rw [star_mul']; ring
  simp only [e]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun q1 _ => ?_
  rw [Finset.sum_comm]
  have e2 : ∀ y1 : γ, ∑ b, ∑ x1, ∑ i, (P y x1 * Z (x1, i) (q1, y1) * star (P z q1)) *
      (star (V b y1) * V b i) = ∑ x1, ∑ i, (P y x1 * Z (x1, i) (q1, y1) * star (P z q1)) *
        (if y1 = i then 1 else 0) := by
    intro y1
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun x1 _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.mul_sum, hV']
  simp only [e2]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x1 _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp

def S200T_Kr {α β γ δ : Type*} (P : Matrix β γ ℂ) (T : Matrix δ α ℂ) (j : γ × δ) :
    Matrix β α ℂ := Matrix.of fun y x => P y j.1 * T j.2 x

lemma S200T_Kr_apply {α β γ δ : Type*} [Fintype α] [Fintype γ] [Fintype δ]
    (P : Matrix β γ ℂ) (T : Matrix δ α ℂ) (X : Matrix α α ℂ) :
    krausApply (S200T_Kr P T) X = ((Tᴴ * T : Matrix α α ℂ) * X).trace • (P * Pᴴ : Matrix β β ℂ) := by
  ext y y'
  simp only [krausApply, S200T_Kr, Matrix.sum_apply, Matrix.mul_apply, Matrix.of_apply,
    Matrix.conjTranspose_apply, Matrix.smul_apply, Matrix.trace, Matrix.diag, smul_eq_mul,
    Fintype.sum_prod_type, star_mul']
  simp only [Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x' _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun b _ => ?_
  ring

lemma S200T_Kr_sum {α β γ δ : Type*} [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]
    (P : Matrix β γ ℂ) (T : Matrix δ α ℂ) :
    ∑ j, ((S200T_Kr P T j)ᴴ * S200T_Kr P T j : Matrix α α ℂ) =
      (P * Pᴴ : Matrix β β ℂ).trace • (Tᴴ * T : Matrix α α ℂ) := by
  ext x x'
  simp only [S200T_Kr, Matrix.sum_apply, Matrix.mul_apply, Matrix.of_apply,
    Matrix.conjTranspose_apply, Matrix.smul_apply, Matrix.trace, Matrix.diag, smul_eq_mul,
    Fintype.sum_prod_type, star_mul']
  simp only [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun c _ => ?_
  ring

lemma S200T_mp_mul {α β γ : Type*} [Fintype γ] (A : Matrix β γ ℂ) (B : Matrix γ α ℂ) (n : ℕ) :
    matrixPower (A * B : Matrix β α ℂ) n =
      (matrixPower A n * matrixPower B n : Matrix (Sites β n) (Sites α n) ℂ) := by
  ext x y
  simp only [matrixPower, Matrix.mul_apply]
  rw [Finset.prod_univ_sum]
  simp only [Fintype.piFinset_univ, Finset.prod_mul_distrib]

lemma S200T_mp_conj {α β : Type*} (A : Matrix β α ℂ) (n : ℕ) :
    matrixPower Aᴴ n = (matrixPower A n)ᴴ := by
  ext x y
  simp only [matrixPower, Matrix.conjTranspose_apply]
  exact (map_prod (starRingEnd ℂ) (fun i => A (y i) (x i)) Finset.univ).symm

lemma S200T_mp_trace {α : Type*} [Fintype α] (A : Matrix α α ℂ) (n : ℕ) :
    (matrixPower A n).trace = A.trace ^ n := by
  simp only [Matrix.trace, Matrix.diag, matrixPower]
  rw [← Fin.prod_const n (∑ a, A a a), Finset.prod_univ_sum, Fintype.piFinset_univ]

lemma S200T_tr_single {α : Type*} [Fintype α] [DecidableEq α] (a b : α) :
    (Matrix.single a b (1:ℂ)).trace = if a = b then 1 else 0 := by
  rw [Matrix.trace, Finset.sum_eq_single a]
  · by_cases h : a = b
    · subst h; simp
    · simp [Matrix.single_apply, h, Ne.symm h]
  · intro c _ hc; simp [Matrix.single_apply, Ne.symm hc]
  · simp

lemma S200T_prod_delta {α : Type*} [DecidableEq α] {n : ℕ} (x x' : Fin n → α) :
    (∏ i, (if x i = x' i then (1:ℂ) else 0)) = if x = x' then 1 else 0 := by
  rw [Finset.prod_boole]
  simp [funext_iff]

lemma S200T_pi_trace {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] {n : ℕ}
    (N : Superop α β) (hN : ∀ a b : α, (N (Matrix.single a b 1)).trace = if a = b then 1 else 0)
    (X : Matrix (Sites α n) (Sites α n) ℂ) : (power N n X).trace = X.trace := by
  simp only [power, piSuperop, Matrix.trace, Matrix.diag, Matrix.of_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.sum_comm]
  simp only [← Finset.mul_sum]
  have : ∀ x' : Sites α n, ∑ y : Sites β n, ∏ i, N (Matrix.single (x i) (x' i) 1) (y i) (y i) =
      if x = x' then 1 else 0 := by
    intro x'
    have h := Finset.prod_univ_sum (fun _ => (Finset.univ : Finset β))
      (fun i a => N (Matrix.single (x i) (x' i) 1) a a)
    simp only [Fintype.piFinset_univ] at h
    rw [← S200T_prod_delta, ← h]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [← hN]; rfl
  simp only [this, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]

lemma S200T_pow_repl {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] {n : ℕ}
    (omega : Matrix β β ℂ) (X : Matrix (Sites α n) (Sites α n) ℂ) :
    power (replacer (A := α) omega) n X = X.trace • matrixPower omega n := by
  ext y y'
  simp only [power, piSuperop, replacer, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul,
    matrixPower]
  simp only [Finset.prod_mul_distrib]
  have : ∀ x x' : Sites α n, (∏ i, (Matrix.single (x i) (x' i) (1:ℂ)).trace) =
      if x = x' then 1 else 0 := by
    intro x x'
    rw [← S200T_prod_delta]
    exact Finset.prod_congr rfl fun i _ => S200T_tr_single _ _
  simp only [this]
  simp only [ite_mul, one_mul, zero_mul, mul_ite, mul_zero, Finset.sum_ite_eq,
    Finset.mem_univ, if_true, Matrix.trace, Matrix.diag, Finset.sum_mul]

def snocE (α : Type*) (n : ℕ) : Sites α n × α ≃ Sites α (n+1) where
  toFun p := Fin.snoc (α := fun _ => α) p.1 p.2
  invFun u := (Fin.init u, u (Fin.last n))
  left_inv p := by simp
  right_inv u := by simp

def splitE (α : Type*) (n m : ℕ) : Sites α n × Sites α m ≃ Sites α (n+m) where
  toFun p := Fin.append p.1 p.2
  invFun y := (fun i => y (Fin.castAdd m i), fun i => y (Fin.natAdd n i))
  left_inv p := by simp
  right_inv y := by simp [Fin.append_castAdd_natAdd]

def permE (α : Type*) {n : ℕ} (π : Equiv.Perm (Fin n)) : Sites α n ≃ Sites α n where
  toFun x := x ∘ π
  invFun x := x ∘ π.symm
  left_inv x := by ext i; simp
  right_inv x := by ext i; simp

lemma mp_snoc {α β : Type*} (U : Matrix β α ℂ) (n : ℕ) :
    (matrixPower U (n+1)).submatrix (snocE β n) (snocE α n) = matrixPower U n ⊗ₖ U := by
  ext ⟨x, a⟩ ⟨y, b⟩
  simp [matrixPower, snocE, Fin.prod_univ_castSucc, Matrix.kronecker_apply]

lemma mp_split {α β : Type*} (U : Matrix β α ℂ) (n m : ℕ) :
    (matrixPower U (n+m)).submatrix (splitE β n m) (splitE α n m) =
      matrixPower U n ⊗ₖ matrixPower U m := by
  ext ⟨x, x'⟩ ⟨y, y'⟩
  simp [matrixPower, splitE, Fin.prod_univ_add, Matrix.kronecker_apply]

lemma mp_perm {α β : Type*} (U : Matrix β α ℂ) {n : ℕ} (π : Equiv.Perm (Fin n)) :
    (matrixPower U n).submatrix (permE β π) (permE α π) = matrixPower U n := by
  ext x y
  simp only [Matrix.submatrix_apply, matrixPower, permE, Equiv.coe_fn_mk, Function.comp_apply]
  exact Equiv.prod_comp π (fun i => U (x i) (y i))

lemma mp_one {α : Type*} [DecidableEq α] (n : ℕ) :
    matrixPower (1 : Matrix α α ℂ) n = 1 := by
  ext x y
  simp only [matrixPower, Matrix.one_apply]
  exact S200T_prod_delta x y

lemma mp_unitary {α β : Type*} [Fintype β] [DecidableEq α] (U : Matrix β α ℂ) (h : Uᴴ * U = 1)
    (n : ℕ) : (matrixPower U n)ᴴ * matrixPower U n = 1 := by
  rw [← S200T_mp_conj, ← S200T_mp_mul, h, mp_one]

lemma kraus_expand {ι κ J : Type*} [Fintype ι] [Fintype J] (K : J → Matrix κ ι ℂ)
    (X : Matrix ι ι ℂ) (b b' : κ) :
    krausApply K X b b' = ∑ a, ∑ a', X a a' * ∑ j, K j b a * conj (K j b' a') := by
  simp only [krausApply, Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Finset.sum_mul]
  rw [kraus_entry, Finset.sum_comm]

lemma kraus_single {ι κ J : Type*} [Fintype ι] [DecidableEq ι] [Fintype J]
    (K : J → Matrix κ ι ℂ) (a a' : ι) (b b' : κ) :
    krausApply K (Matrix.single a a' 1) b b' = ∑ j, K j b a * conj (K j b' a') := by
  rw [kraus_expand]
  rw [Finset.sum_eq_single a]
  · rw [Finset.sum_eq_single a']
    · simp
    · intro c _ hc; simp [Matrix.single_apply, Ne.symm hc]
    · simp
  · intro c _ hc
    refine Finset.sum_eq_zero fun c' _ => ?_
    simp [Matrix.single_apply, Ne.symm hc]
  · simp

lemma kraus_ext {ι κ J J' : Type*} [Fintype ι] [DecidableEq ι] [Fintype J] [Fintype J']
    (K : J → Matrix κ ι ℂ) (L : J' → Matrix κ ι ℂ)
    (h : ∀ a a', krausApply K (Matrix.single a a' 1) = krausApply L (Matrix.single a a' 1))
    (X : Matrix ι ι ℂ) : krausApply K X = krausApply L X := by
  ext b b'
  rw [kraus_expand, kraus_expand]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun a' _ => ?_
  have := congrArg (fun M => M b b') (h a a')
  simp only [kraus_single] at this
  rw [this]

lemma conj_kraus {ι κ : Type*} [Fintype ι] (A : Matrix κ ι ℂ) (X : Matrix ι ι ℂ) :
    conjSuperop A X = krausApply (fun _ : Unit => A) X := by
  simp [conjSuperop, krausApply]


lemma repl_ch {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (ρ : Matrix β β ℂ) (hρ : IsDensityMatrix ρ) :
    IsChannel (fun X : Matrix α α ℂ => X.trace • ρ) := by
  obtain ⟨B, hB⟩ := factor ρ hρ.1
  refine ch_of _ (S200T_Kr Bᴴ (1 : Matrix α α ℂ)) ?_ fun X => ?_
  · rw [S200T_Kr_sum, Matrix.conjTranspose_conjTranspose, ← hB, hρ.2]; simp
  · rw [S200T_Kr_apply, Matrix.conjTranspose_conjTranspose, ← hB]; simp

lemma mp_density {α : Type*} [Fintype α] [DecidableEq α] (ω : Matrix α α ℂ)
    (hω : IsDensityMatrix ω) (n : ℕ) : IsDensityMatrix (matrixPower ω n) := by
  obtain ⟨B, hB⟩ := factor ω hω.1
  refine ⟨?_, ?_⟩
  · rw [hB, S200T_mp_mul, S200T_mp_conj]
    exact Matrix.posSemidef_conjTranspose_mul_self _
  · rw [S200T_mp_trace, hω.2, one_pow]

lemma powrepl_ch {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (ω : Matrix β β ℂ) (hω : IsDensityMatrix ω) (n : ℕ) :
    IsChannel (power (replacer (A := α) ω) n) := by
  have : power (replacer (A := α) ω) n = fun X => X.trace • matrixPower ω n :=
    funext fun X => S200T_pow_repl ω X
  rw [this]
  exact repl_ch _ (mp_density ω hω n)

lemma sum_sub {ι κ ι' κ' J : Type*} [Fintype J] (M : J → Matrix ι κ ℂ) (e : ι' → ι) (f : κ' → κ) :
    ∑ p, (M p).submatrix e f = (∑ p, M p).submatrix e f := by
  ext; simp [Matrix.sum_apply]

lemma sum_kron {ι κ ι' κ' J K : Type*} [Fintype J] [Fintype K] (P : J → Matrix ι κ ℂ)
    (Q : K → Matrix ι' κ' ℂ) :
    ∑ p : J × K, P p.1 ⊗ₖ Q p.2 = (∑ j, P j) ⊗ₖ (∑ k, Q k) := by
  ext ⟨a, b⟩ ⟨c, d⟩
  simp [Matrix.sum_apply, Matrix.kronecker_apply, Fintype.sum_prod_type, Finset.sum_mul_sum]

def concK {α β J K : Type*} {n m : ℕ} (E : J → Matrix (Sites β n) (Sites α n) ℂ)
    (F : K → Matrix (Sites β m) (Sites α m) ℂ) (p : J × K) :
    Matrix (Sites β (n+m)) (Sites α (n+m)) ℂ :=
  (E p.1 ⊗ₖ F p.2).submatrix (splitE β n m).symm (splitE α n m).symm

variable {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]

lemma concat_kraus {J K : Type*} [Fintype J] [Fintype K] {n m : ℕ}
    {T : Superop (Sites A n) (Sites B n)} {M : Superop (Sites A m) (Sites B m)}
    (E : J → Matrix (Sites B n) (Sites A n) ℂ) (F : K → Matrix (Sites B m) (Sites A m) ℂ)
    (hT : ∀ X, T X = krausApply E X) (hM : ∀ X, M X = krausApply F X)
    (X : Matrix (Sites A (n+m)) (Sites A (n+m)) ℂ) :
    concatenate T M X = krausApply (concK E F) X := by
  ext y z
  rw [kraus_expand]
  simp only [concatenate, hT, hM, kraus_single]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun x' _ => ?_
  rw [mul_assoc]
  congr 1
  rw [Fintype.sum_prod_type, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
  simp only [concK, Matrix.submatrix_apply, Matrix.kronecker_apply, splitE, Equiv.coe_fn_symm_mk,
    map_mul, Function.comp_def]
  ring

lemma concK_norm {J K : Type*} [Fintype J] [Fintype K] {n m : ℕ}
    (E : J → Matrix (Sites B n) (Sites A n) ℂ) (F : K → Matrix (Sites B m) (Sites A m) ℂ) :
    ∑ p, (concK E F p)ᴴ * concK E F p =
      ((∑ j, (E j)ᴴ * E j) ⊗ₖ (∑ k, (F k)ᴴ * F k)).submatrix (splitE A n m).symm
        (splitE A n m).symm := by
  rw [← sum_kron, ← sum_sub]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [concK, Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv,
    Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul]

lemma concat_ch {n m : ℕ} {T : Superop (Sites A n) (Sites B n)}
    {M : Superop (Sites A m) (Sites B m)} (hT : IsChannel T) (hM : IsChannel M) :
    IsChannel (concatenate T M) := by
  obtain ⟨E, hE, rfl⟩ := (ch_iff T).1 hT
  obtain ⟨F, hF, rfl⟩ := (ch_iff M).1 hM
  refine ch_of _ (concK E F) ?_ (concat_kraus E F (fun _ => rfl) (fun _ => rfl))
  rw [concK_norm, hE, hF, Matrix.one_kronecker_one, Matrix.submatrix_one_equiv]

lemma concat_prod {J K : Type*} [Fintype J] [Fintype K] {n m : ℕ}
    {T : Superop (Sites A n) (Sites B n)} {M : Superop (Sites A m) (Sites B m)}
    (E : J → Matrix (Sites B n) (Sites A n) ℂ) (F : K → Matrix (Sites B m) (Sites A m) ℂ)
    (hT : ∀ X, T X = krausApply E X) (hM : ∀ X, M X = krausApply F X)
    (P : Matrix (Sites A n) (Sites A n) ℂ) (Q : Matrix (Sites A m) (Sites A m) ℂ) :
    concatenate T M ((P ⊗ₖ Q).submatrix (splitE A n m).symm (splitE A n m).symm) =
      (T P ⊗ₖ M Q).submatrix (splitE B n m).symm (splitE B n m).symm := by
  rw [concat_kraus E F hT hM, hT, hM]
  unfold krausApply
  rw [← sum_kron, ← sum_sub]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [concK, ← conj_sub, kron_conj]


lemma kraus_subs {α β α' β' J : Type*} [Fintype α] [Fintype α'] [Fintype J]
    (E : J → Matrix β α ℂ) (e : β' ≃ β) (f : α' ≃ α) (Y : Matrix α α ℂ) :
    (krausApply E Y).submatrix e e = krausApply (fun j => (E j).submatrix e f) (Y.submatrix f f) := by
  unfold krausApply
  rw [← sum_sub]
  exact Finset.sum_congr rfl fun j _ => conj_sub _ _ _ _

lemma kraus_subs_norm {α β α' β' J : Type*} [Fintype β] [Fintype β'] [Fintype J]
    (E : J → Matrix β α ℂ) (e : β' ≃ β) (f : α' ≃ α) :
    ∑ j, ((E j).submatrix e f)ᴴ * (E j).submatrix e f = (∑ j, (E j)ᴴ * E j).submatrix f f := by
  rw [← sum_sub]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv]

lemma perm_ch {n : ℕ} (π : Equiv.Perm (Fin n)) {M : Superop (Sites A n) (Sites B n)}
    (hM : IsChannel M) : IsChannel (permuteChannel π M) := by
  obtain ⟨E, hE, rfl⟩ := (ch_iff M).1 hM
  refine ch_of _ (fun j => (E j).submatrix (permE B π) (permE A π)) ?_ fun X => ?_
  · rw [kraus_subs_norm, hE, Matrix.submatrix_one_equiv]
  · show (krausApply E (X.submatrix (permE A π).symm (permE A π).symm)).submatrix
      (permE B π) (permE B π) = _
    rw [kraus_subs E (permE B π) (permE A π), Matrix.submatrix_submatrix]
    simp

lemma perm_conj {α β : Type*} [Fintype α] {n : ℕ} (σ : Equiv.Perm (Fin n)) (U : Matrix β α ℂ)
    (X : Matrix (Sites α n) (Sites α n) ℂ) :
    permute σ (conjSuperop (matrixPower U n) X) = conjSuperop (matrixPower U n) (permute σ X) := by
  show (matrixPower U n * X * (matrixPower U n)ᴴ).submatrix (permE β σ) (permE β σ) = _
  rw [conj_sub _ _ (permE β σ) (permE α σ), mp_perm]
  rfl

lemma marg_eq {n : ℕ} (τ : Matrix A A ℂ) (M : Superop (Sites A (n+1)) (Sites B (n+1)))
    (X : Matrix (Sites A n) (Sites A n) ℂ) :
    marginal τ M X = ptr ((M ((X ⊗ₖ τ).submatrix (snocE A n).symm (snocE A n).symm)).submatrix
      (snocE B n) (snocE B n)) := by
  ext y z
  simp [marginal, ptr, snocE, Matrix.kronecker_apply, Fin.init]
  rfl

def margR {n : ℕ} {K : Type*} (C : Matrix K A ℂ) (k : K) :
    Matrix (Sites A n × A) (Sites A n) ℂ :=
  Matrix.of fun p x => if p.1 = x then conj (C k p.2) else 0

lemma margR_apply {n : ℕ} {K : Type*} [Fintype K] (C : Matrix K A ℂ)
    (X : Matrix (Sites A n) (Sites A n) ℂ) :
    krausApply (margR (n := n) C) X = X ⊗ₖ (Cᴴ * C : Matrix A A ℂ) := by
  ext ⟨x, a⟩ ⟨x', a'⟩
  rw [kraus_expand]
  simp only [margR, Matrix.of_apply, Matrix.kronecker_apply, Matrix.mul_apply,
    Matrix.conjTranspose_apply, RCLike.star_def]
  rw [Finset.sum_eq_single x]
  · rw [Finset.sum_eq_single x']
    · simp only [if_true]
      simp
    · intro c _ hc; simp [Ne.symm hc]
    · simp
  · intro c _ hc
    refine Finset.sum_eq_zero fun c' _ => ?_
    simp [Ne.symm hc]
  · simp

lemma margR_norm {n : ℕ} {K : Type*} [Fintype K] (C : Matrix K A ℂ) (hC : (Cᴴ * C).trace = 1) :
    ∑ k, (margR (n := n) C k)ᴴ * margR (n := n) C k = 1 := by
  refine Matrix.ext fun x x' => ?_
  simp only [margR, Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply,
    Fintype.sum_prod_type, Matrix.one_apply]
  by_cases h : x = x'
  · subst h
    simp only [if_true]
    rw [Finset.sum_comm]
    have : ∀ y : Sites A n, ∑ k, ∑ a, star (if y = x then conj (C k a) else 0) *
        (if y = x then conj (C k a) else 0) = if y = x then (Cᴴ * C).trace else 0 := by
      intro y
      by_cases hy : y = x
      · simp only [hy, if_true, Matrix.trace, Matrix.diag, Matrix.mul_apply,
          Matrix.conjTranspose_apply]
        rw [Finset.sum_comm]
        simp [RCLike.star_def, mul_comm]
      · simp [hy]
    simp only [this, hC, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  · simp only [if_neg h]
    refine Finset.sum_eq_zero fun k _ => Finset.sum_eq_zero fun y _ => Finset.sum_eq_zero
      fun a _ => ?_
    by_cases hy : y = x
    · subst hy; simp [h]
    · simp [hy]

lemma marg_ch {n : ℕ} (τ : Matrix A A ℂ) (hτ : IsDensityMatrix τ)
    {M : Superop (Sites A (n+1)) (Sites B (n+1))} (hM : IsChannel M) :
    IsChannel (marginal τ M) := by
  obtain ⟨E, hE, rfl⟩ := (ch_iff M).1 hM
  obtain ⟨C, hC⟩ := factor τ hτ.1
  let E' := fun j => (E j).submatrix (snocE B n) (snocE A n)
  have hE' : ∑ j, (E' j)ᴴ * E' j = 1 := by
    rw [kraus_subs_norm, hE, Matrix.submatrix_one_equiv]
  have hR : ∑ k, (margR (n := n) C k)ᴴ * margR (n := n) C k = 1 :=
    margR_norm C (by rw [← hC]; exact hτ.2)
  refine ch_of _ (fun p : B × ((Sites B (n+1) × Sites A (n+1)) × A) =>
    ptrK (β := Sites B n) p.1 * (E' p.2.1 * margR (n := n) C p.2.2)) ?_ fun X => ?_
  · have h1 := kraus_comp_norm (fun b : B => ptrK (β := Sites B n) b)
      (fun q : (Sites B (n+1) × Sites A (n+1)) × A => E' q.1 * margR (n := n) C q.2)
    have h2 := kraus_comp_norm E' (fun k : A => margR (n := n) C k)
    rw [h1, ptrK_norm]
    simp only [Matrix.mul_one]
    rw [h2, hE']
    simp only [Matrix.mul_one]
    exact hR
  · have h1 := kraus_comp (fun b : B => ptrK (β := Sites B n) b)
      (fun q : (Sites B (n+1) × Sites A (n+1)) × A => E' q.1 * margR (n := n) C q.2) X
    have h2 := kraus_comp E' (fun k : A => margR (n := n) C k) X
    rw [h1, h2, marg_eq, ptr_kraus, margR_apply, ← hC, kraus_subs E (snocE B n) (snocE A n),
      Matrix.submatrix_submatrix]
    simp [E']


def Cov {n : ℕ} (UA : Matrix A A ℂ) (UB : Matrix B B ℂ) (M : Superop (Sites A n) (Sites B n)) :
    Prop :=
  ∀ X, M (conjSuperop (matrixPower UA n) X) = conjSuperop (matrixPower UB n) (M X)

lemma cov_perm {n : ℕ} (UA : Matrix A A ℂ) (UB : Matrix B B ℂ) (π : Equiv.Perm (Fin n))
    {M : Superop (Sites A n) (Sites B n)} (hM : Cov UA UB M) : Cov UA UB (permuteChannel π M) := by
  intro X
  simp only [permuteChannel]
  rw [perm_conj, hM, perm_conj]

lemma mp_snoc' {α β : Type*} (U : Matrix β α ℂ) (n : ℕ) :
    (matrixPower U n ⊗ₖ U).submatrix (snocE β n).symm (snocE α n).symm = matrixPower U (n+1) := by
  rw [← mp_snoc, Matrix.submatrix_submatrix]; simp

lemma mp_split' {α β : Type*} (U : Matrix β α ℂ) (n m : ℕ) :
    (matrixPower U n ⊗ₖ matrixPower U m).submatrix (splitE β n m).symm (splitE α n m).symm =
      matrixPower U (n+m) := by
  rw [← mp_split, Matrix.submatrix_submatrix]; simp

lemma cov_marg {n : ℕ} (UA : Matrix A A ℂ) (UB : Matrix B B ℂ) (τ : Matrix A A ℂ)
    (hU : conjSuperop UA τ = τ) (hV : UBᴴ * UB = 1)
    {M : Superop (Sites A (n+1)) (Sites B (n+1))} (hM : Cov UA UB M) :
    Cov UA UB (marginal τ M) := by
  intro X
  rw [marg_eq, marg_eq]
  have h1 : (conjSuperop (matrixPower UA n) X ⊗ₖ τ) =
      (matrixPower UA n ⊗ₖ UA) * (X ⊗ₖ τ) * (matrixPower UA n ⊗ₖ UA)ᴴ := by
    rw [kron_conj]; congr 1; exact hU.symm
  rw [h1, conj_sub _ _ (snocE A n).symm (snocE A n).symm, mp_snoc']
  have h2 := hM ((X ⊗ₖ τ).submatrix (snocE A n).symm (snocE A n).symm)
  unfold conjSuperop at h2
  rw [h2, conj_sub _ _ (snocE B n) (snocE B n), mp_snoc, ptr_conj _ _ hV]
  rfl

lemma single_split {α β γ : Type*} [DecidableEq α] [DecidableEq β] [DecidableEq γ]
    (e : α × β ≃ γ) (x x' : γ) :
    Matrix.single x x' (1:ℂ) = (Matrix.single (e.symm x).1 (e.symm x').1 (1:ℂ) ⊗ₖ
      Matrix.single (e.symm x).2 (e.symm x').2 (1:ℂ)).submatrix e.symm e.symm := by
  rw [Matrix.single_kronecker_single, Matrix.submatrix_single_equiv]; simp

lemma cov_concat {n m : ℕ} (UA : Matrix A A ℂ) (UB : Matrix B B ℂ)
    {T : Superop (Sites A n) (Sites B n)} {M : Superop (Sites A m) (Sites B m)}
    (hT : IsChannel T) (hM : IsChannel M) (cT : Cov UA UB T) (cM : Cov UA UB M) :
    Cov UA UB (concatenate T M) := by
  obtain ⟨E, -, hTE⟩ := (ch_iff T).1 hT
  obtain ⟨F, -, hMF⟩ := (ch_iff M).1 hM
  have hTE' : ∀ X, T X = krausApply E X := fun X => by rw [hTE]
  have hMF' : ∀ X, M X = krausApply F X := fun X => by rw [hMF]
  have key : ∀ P Q, concatenate T M (conjSuperop (matrixPower UA (n+m))
      ((P ⊗ₖ Q).submatrix (splitE A n m).symm (splitE A n m).symm)) =
      conjSuperop (matrixPower UB (n+m))
        (concatenate T M ((P ⊗ₖ Q).submatrix (splitE A n m).symm (splitE A n m).symm)) := by
    intro P Q
    unfold conjSuperop
    rw [← mp_split' UA, ← conj_sub, kron_conj, concat_prod E F hTE' hMF',
      concat_prod E F hTE' hMF']
    have h1 := cT P
    have h2 := cM Q
    unfold conjSuperop at h1 h2
    rw [h1, h2, ← kron_conj, conj_sub _ _ (splitE B n m).symm (splitE B n m).symm, mp_split']
  intro X
  have eL : ∀ X, concatenate T M (conjSuperop (matrixPower UA (n+m)) X) =
      krausApply (fun p : ((Sites B n × Sites A n) × (Sites B m × Sites A m)) × Unit => concK E F p.1 * matrixPower UA (n+m)) X := by
    intro X
    rw [kraus_comp (concK E F) (fun _ : Unit => matrixPower UA (n+m)), ← conj_kraus,
      concat_kraus E F hTE' hMF']
  have eR : ∀ X, conjSuperop (matrixPower UB (n+m)) (concatenate T M X) =
      krausApply (fun p : Unit × ((Sites B n × Sites A n) × (Sites B m × Sites A m)) => matrixPower UB (n+m) * concK E F p.2) X := by
    intro X
    rw [kraus_comp (fun _ : Unit => matrixPower UB (n+m)) (concK E F), ← conj_kraus,
      concat_kraus E F hTE' hMF']
  rw [eL, eR]
  refine kraus_ext _ _ (fun x x' => ?_) X
  rw [← eL, ← eR, single_split (splitE A n m)]
  exact key _ _


lemma ch_convex {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] :
    Convex ℝ {M : Superop α β | IsChannel M} := by
  intro M hM N hN a b ha hb hab
  obtain ⟨E, hE, rfl⟩ := (ch_iff M).1 hM
  obtain ⟨F, hF, rfl⟩ := (ch_iff N).1 hN
  have hsa : star ((Real.sqrt a : ℝ) : ℂ) * ((Real.sqrt a : ℝ) : ℂ) = (a : ℂ) := by
    rw [Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul, Real.mul_self_sqrt ha]
  have hsb : star ((Real.sqrt b : ℝ) : ℂ) * ((Real.sqrt b : ℝ) : ℂ) = (b : ℂ) := by
    rw [Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul, Real.mul_self_sqrt hb]
  have hsa' : ((Real.sqrt a : ℝ) : ℂ) * star ((Real.sqrt a : ℝ) : ℂ) = (a : ℂ) := by
    rw [mul_comm, hsa]
  have hsb' : ((Real.sqrt b : ℝ) : ℂ) * star ((Real.sqrt b : ℝ) : ℂ) = (b : ℂ) := by
    rw [mul_comm, hsb]
  refine ch_of _ (Sum.elim (fun j => ((Real.sqrt a : ℝ) : ℂ) • E j)
    (fun j => ((Real.sqrt b : ℝ) : ℂ) • F j)) ?_ fun X => ?_
  · rw [Fintype.sum_sum_type]
    simp only [Sum.elim_inl, Sum.elim_inr, Matrix.conjTranspose_smul, Matrix.smul_mul,
      Matrix.mul_smul, smul_smul, ← Finset.smul_sum, hE, hF, hsa', hsb']
    rw [← add_smul]
    have : (a : ℂ) + (b : ℂ) = 1 := by exact_mod_cast hab
    rw [this, one_smul]
  · simp only [Set.mem_setOf_eq, Pi.add_apply, Pi.smul_apply, krausApply, Fintype.sum_sum_type,
      Sum.elim_inl, Sum.elim_inr, Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul,
      smul_smul, ← Finset.smul_sum, hsa', hsb']
    rw [hsa, hsb]
    simp only [Complex.coe_smul]

lemma cov_closed {G : Type*} {n : ℕ} (UA : G → Matrix A A ℂ) (UB : G → Matrix B B ℂ) :
    IsClosed {M : Superop (Sites A n) (Sites B n) | ∀ g X,
      M (conjSuperop (matrixPower (UA g) n) X) = conjSuperop (matrixPower (UB g) n) (M X)} := by
  simp only [Set.setOf_forall]
  refine isClosed_iInter fun g => isClosed_iInter fun X => isClosed_eq (continuous_apply _) ?_
  unfold conjSuperop
  exact (continuous_const.matrix_mul (continuous_apply X)).matrix_mul continuous_const

lemma cov_convex {G : Type*} {n : ℕ} (UA : G → Matrix A A ℂ) (UB : G → Matrix B B ℂ) :
    Convex ℝ {M : Superop (Sites A n) (Sites B n) | ∀ g X,
      M (conjSuperop (matrixPower (UA g) n) X) = conjSuperop (matrixPower (UB g) n) (M X)} := by
  intro M hM N hN a b _ _ _ g X
  simp only [Pi.add_apply, Pi.smul_apply]
  rw [hM g X, hN g X]
  unfold conjSuperop
  simp [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul]

lemma powrepl_cov {n : ℕ} (UA : Matrix A A ℂ) (UB : Matrix B B ℂ) (ω : Matrix B B ℂ)
    (hU : UAᴴ * UA = 1) (hω : conjSuperop UB ω = ω) :
    Cov UA UB (power (replacer (A := A) ω) n) := by
  intro X
  rw [S200T_pow_repl, S200T_pow_repl]
  unfold conjSuperop at hω ⊢
  have ht : (matrixPower UA n * X * (matrixPower UA n)ᴴ).trace = X.trace := by
    rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, mp_unitary UA hU, Matrix.one_mul]
  rw [ht, Matrix.mul_smul, Matrix.smul_mul, ← S200T_mp_conj, ← S200T_mp_mul, ← S200T_mp_mul, hω]

lemma split_eq_iff {α : Type*} {n m : ℕ} (x x' : Sites α (n+m)) :
    (x ∘ Fin.castAdd m = x' ∘ Fin.castAdd m ∧ x ∘ Fin.natAdd n = x' ∘ Fin.natAdd n) ↔ x = x' := by
  constructor
  · rintro ⟨h1, h2⟩
    exact (splitE α n m).symm.injective (Prod.ext h1 h2)
  · rintro rfl; exact ⟨rfl, rfl⟩

lemma powrepl_concat (ω : Matrix B B ℂ) (n m : ℕ) :
    concatenate (power (replacer (A := A) ω) n) (power (replacer (A := A) ω) m) =
      power (replacer (A := A) ω) (n+m) := by
  funext X
  ext y z
  rw [S200T_pow_repl (n := n+m)]
  simp only [concatenate, S200T_pow_repl, Matrix.smul_apply, smul_eq_mul, S200T_tr_single]
  have hterm : ∀ x x' : Sites A (n+m),
      X x x' * ((if x ∘ Fin.castAdd m = x' ∘ Fin.castAdd m then (1:ℂ) else 0) *
        matrixPower ω n (y ∘ Fin.castAdd m) (z ∘ Fin.castAdd m)) *
      ((if x ∘ Fin.natAdd n = x' ∘ Fin.natAdd n then (1:ℂ) else 0) *
        matrixPower ω m (y ∘ Fin.natAdd n) (z ∘ Fin.natAdd n)) =
      if x = x' then X x x * matrixPower ω (n+m) y z else 0 := by
    intro x x'
    by_cases h : x = x'
    · subst h
      simp only [if_true, one_mul]
      rw [mul_assoc]
      congr 1
      simp only [matrixPower, Fin.prod_univ_add, Function.comp_apply]
    · rw [if_neg h]
      rw [← split_eq_iff] at h
      by_cases h1 : x ∘ Fin.castAdd m = x' ∘ Fin.castAdd m
      · have h2 : ¬ x ∘ Fin.natAdd n = x' ∘ Fin.natAdd n := fun h2 => h ⟨h1, h2⟩
        simp [h2]
      · simp [h1]
  simp only [hterm, Finset.sum_ite_eq, Finset.mem_univ, if_true, Matrix.trace, Matrix.diag,
    Finset.sum_mul]

end S201CAI

open scoped Matrix ComplexConjugate ENNReal ComplexOrder

open Filter

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms QAlgorithms.Papers.Independent.Information100.P69 in
theorem solution {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    [Nonempty A] [Nonempty B] :
    (∀ (G : Type*) [Group G] (UA : G → Matrix A A ℂ) (UB : G → Matrix B B ℂ),
      (∀ g, (UA g).conjTranspose*UA g = 1) → (∀ g, (UB g).conjTranspose*UB g = 1) →
      UA 1 = 1 → UB 1 = 1 → (∀ g h, UA (g*h) = UA g*UA h) → (∀ g h, UB (g*h) = UB g*UB h) →
      ∀ tau : Matrix A A ℂ, ∀ omega : Matrix B B ℂ, Faithful tau → Faithful omega →
      (∀ g, conjSuperop (UA g) tau = tau) → (∀ g, conjSuperop (UB g) omega = omega) →
        Admissible (covariantFamily UA UB) omega ∧ Additional (covariantFamily UA UB) tau) ∧
    (∀ (I : Type*) (F : I → BlockFamily A B) (tau : Matrix A A ℂ) (omega : Matrix B B ℂ),
      Faithful tau → Faithful omega → (∀ i, Admissible (F i) omega ∧ Additional (F i) tau) →
        Admissible (fun n => {M | IsChannel M ∧ ∀ i, M ∈ F i n}) omega ∧
        Additional (fun n => {M | IsChannel M ∧ ∀ i, M ∈ F i n}) tau) := by
  refine ⟨?_, ?_⟩
  · intro G _ UA UB hUA hUB _ _ _ _ tau omega htau homega hUAt hUBo
    refine ⟨⟨fun n hn => ?_, ?_, ?_⟩, ⟨htau, ?_, ?_⟩⟩
    · have hset : covariantFamily UA UB n = {M | IsChannel M} ∩ {M : Superop (Sites A n) (Sites B n) |
          ∀ g X, M (conjSuperop (matrixPower (UA g) n) X) =
            conjSuperop (matrixPower (UB g) n) (M X)} := rfl
      refine ⟨⟨power (replacer omega) n, S201CAI.powrepl_ch omega homega.1 n,
        fun g => S201CAI.powrepl_cov (UA g) (UB g) omega (hUA g) (hUBo g)⟩, ?_, ?_,
        fun M hM => hM.1⟩
      · rw [hset]; exact S201CAI.ch_compact.inter_right (S201CAI.cov_closed UA UB)
      · rw [hset]; exact S201CAI.ch_convex.inter (S201CAI.cov_convex UA UB)
    · intro n m hn hm T hT M hM
      exact ⟨S201CAI.concat_ch hT.1 hM.1,
        fun g => S201CAI.cov_concat (UA g) (UB g) hT.1 hM.1 (hT.2 g) (hM.2 g)⟩
    · exact ⟨homega, S201CAI.powrepl_ch omega homega.1 1,
        fun g => S201CAI.powrepl_cov (UA g) (UB g) omega (hUA g) (hUBo g)⟩
    · intro n hn π M hM
      exact ⟨S201CAI.perm_ch π hM.1, fun g => S201CAI.cov_perm (UA g) (UB g) π (hM.2 g)⟩
    · intro n hn M hM
      exact ⟨S201CAI.marg_ch tau htau.1 hM.1,
        fun g => S201CAI.cov_marg (UA g) (UB g) tau (hUAt g) (hUB g) (hM.2 g)⟩
  · intro I F tau omega htau homega hF
    have hS : ∀ n, {M | IsChannel M ∧ ∀ i, M ∈ F i n} = {M | IsChannel M} ∩ ⋂ i, F i n := by
      intro n; ext M; simp
    have hP : ∀ n, 1 ≤ n → ∀ i, power (replacer omega) n ∈ F i n := by
      intro n hn i
      induction n, hn using Nat.le_induction with
      | base => exact (hF i).1.2.2.2
      | succ k hk ih =>
        rw [← S201CAI.powrepl_concat]
        exact (hF i).1.2.1 k 1 hk le_rfl _ ih _ (hF i).1.2.2.2
    refine ⟨⟨fun n hn => ?_, ?_, ?_⟩, ⟨htau, ?_, ?_⟩⟩
    · refine ⟨⟨_, S201CAI.powrepl_ch omega homega.1 n, fun i => hP n hn i⟩, ?_, ?_,
        fun M hM => hM.1⟩
      · beta_reduce; rw [hS]
        exact S201CAI.ch_compact.inter_right
          (isClosed_iInter fun i => ((hF i).1.1 n hn).2.1.isClosed)
      · beta_reduce; rw [hS]
        exact S201CAI.ch_convex.inter (convex_iInter fun i => ((hF i).1.1 n hn).2.2.1)
    · intro n m hn hm T hT M hM
      exact ⟨S201CAI.concat_ch hT.1 hM.1, fun i => (hF i).1.2.1 n m hn hm T (hT.2 i) M (hM.2 i)⟩
    · exact ⟨homega, S201CAI.powrepl_ch omega homega.1 1, fun i => (hF i).1.2.2.2⟩
    · intro n hn π M hM
      exact ⟨S201CAI.perm_ch π hM.1, fun i => (hF i).2.2.1 n hn π M (hM.2 i)⟩
    · intro n hn M hM
      exact ⟨S201CAI.marg_ch tau htau.1 hM.1, fun i => (hF i).2.2.2 n hn M (hM.2 i)⟩
