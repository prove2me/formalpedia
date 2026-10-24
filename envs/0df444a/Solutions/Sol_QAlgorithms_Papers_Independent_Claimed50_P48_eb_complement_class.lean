-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Claimed50.P48.eb_complement_class
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-23T08:40:38.293987+00:00
-- url     : https://prove2.me/submissions/8ebed956-b6ea-48fa-8992-534feb208721

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P48

noncomputable section

namespace QAlgorithms.Papers.Independent.Claimed50.P48

open scoped BigOperators Matrix Kronecker ComplexConjugate ComplexOrder ENNReal

open QAlgorithms.Papers.Independent.Information100.P67 (receiverChannel complementaryChannel environmentSwap)

attribute [local instance] Classical.propDecidable Classical.decEq

variable {A B C D A2 B2 C2 K : Type*}

variable [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

variable [Fintype C] [DecidableEq C] [Fintype D] [DecidableEq D]

variable [Fintype K] [DecidableEq K]

open Matrix

set_option linter.unusedSectionVars false

theorem x8_spec {n : Type*} [Fintype n] [DecidableEq n] {M : Matrix n n ℂ} (h : M.IsHermitian)
    (x y : n) : M x y = ∑ k, (h.eigenvalues k : ℂ) * (h.eigenvectorBasis k) x *
      star ((h.eigenvectorBasis k) y) := by
  conv_lhs => rw [h.spectral_theorem]
  simp [Unitary.conjStarAlgAut_apply, mul_apply, diagonal_apply, IsHermitian.eigenvectorUnitary_apply,
    star_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  ring

theorem x8_kentry (F : K → Matrix B A ℂ) (rho : Matrix A A ℂ) (b b' : B) :
    krausApply F rho b b' = ∑ a, ∑ a', rho a a' * ∑ j, F j b a * star (F j b' a') := by
  have : ∀ j, (F j * rho * (F j)ᴴ) b b' = ∑ a, ∑ a', F j b a * rho a a' * star (F j b' a') := by
    intro j
    simp only [mul_apply, conjTranspose_apply, Finset.sum_mul]
    rw [Finset.sum_comm]
  simp only [krausApply, Matrix.sum_apply, this, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a' _ => Finset.sum_congr rfl fun j _ => ?_
  ring

section gen
variable {X : Type*} [Fintype X] [DecidableEq X]

/-- coefficient of a vector on an eigenvector. -/
def x8c {J : Matrix X X ℂ} (hH : J.IsHermitian) (k : X) (f : X → ℂ) : ℂ :=
  ∑ x, star ((hH.eigenvectorBasis k) x) * f x

theorem x8_orth {J : Matrix X X ℂ} (hH : J.IsHermitian) (k k' : X) :
    ∑ x, star ((hH.eigenvectorBasis k) x) * (hH.eigenvectorBasis k') x =
      if k = k' then 1 else 0 := by
  have := (hH.eigenvectorBasis).orthonormal
  rw [orthonormal_iff_ite] at this
  have h := this k k'
  rw [PiLp.inner_apply] at h
  rw [← h]
  refine Finset.sum_congr rfl fun x _ => ?_
  simp [mul_comm]

theorem x8_compl {J : Matrix X X ℂ} (hH : J.IsHermitian) (x y : X) :
    ∑ k, (hH.eigenvectorBasis k) x * star ((hH.eigenvectorBasis k) y) =
      if x = y then 1 else 0 := by
  have hU := hH.eigenvectorUnitary.2
  rw [Matrix.mem_unitaryGroup_iff] at hU
  have := congrFun (congrFun hU x) y
  simp only [mul_apply, star_apply, IsHermitian.eigenvectorUnitary_apply, one_apply] at this
  exact this

theorem x8_expand {J : Matrix X X ℂ} (hH : J.IsHermitian) (f : X → ℂ) (x : X) :
    ∑ k, x8c hH k f * (hH.eigenvectorBasis k) x = f x := by
  simp only [x8c, Finset.sum_mul]
  rw [Finset.sum_comm]
  have : ∀ y, ∑ k, star ((hH.eigenvectorBasis k) y) * f y * (hH.eigenvectorBasis k) x =
      f y * if x = y then 1 else 0 := by
    intro y; rw [← x8_compl hH x y, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_; ring
  simp only [this]
  simp

theorem x8_eig {J : Matrix X X ℂ} (hH : J.IsHermitian) (k : X) (x : X) :
    ∑ y, J x y * (hH.eigenvectorBasis k) y = (hH.eigenvalues k : ℂ) * (hH.eigenvectorBasis k) x := by
  simp only [x8_spec hH, Finset.sum_mul]
  rw [Finset.sum_comm]
  have : ∀ k', ∑ y, (hH.eigenvalues k' : ℂ) * (hH.eigenvectorBasis k') x *
      star ((hH.eigenvectorBasis k') y) * (hH.eigenvectorBasis k) y =
      (hH.eigenvalues k' : ℂ) * (hH.eigenvectorBasis k') x * (if k' = k then 1 else 0) := by
    intro k'; rw [← x8_orth hH k' k, Finset.mul_sum]
    refine Finset.sum_congr rfl fun y _ => ?_; ring
  simp only [this]
  simp

variable {J : Matrix X X ℂ} (hH : J.IsHermitian) {c : ℝ} {K' : Type*} [Fintype K']

theorem x8_K1 (f : K' → X → ℂ) (hf : ∀ x y, ∑ j, f j x * star (f j y) = c * J x y)
    (k x : X) : ∑ j, f j x * star (x8c hH k (f j)) =
      c * (hH.eigenvalues k : ℂ) * (hH.eigenvectorBasis k) x := by
  simp only [x8c, star_sum, star_mul', star_star, Finset.mul_sum]
  rw [Finset.sum_comm]
  have : ∀ y, ∑ j, f j x * ((hH.eigenvectorBasis k) y * star (f j y)) =
      (c : ℂ) * (J x y * (hH.eigenvectorBasis k) y) := by
    intro y
    rw [← mul_assoc, ← hf, Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => ?_; ring
  simp only [this, ← Finset.mul_sum, x8_eig]
  ring

theorem x8_K2 (f : K' → X → ℂ) (hf : ∀ x y, ∑ j, f j x * star (f j y) = c * J x y)
    (k k' : X) : ∑ j, star (x8c hH k (f j)) * x8c hH k' (f j) =
      if k' = k then c * (hH.eigenvalues k : ℂ) else 0 := by
  have : ∀ j, star (x8c hH k (f j)) * x8c hH k' (f j) =
      ∑ x, star ((hH.eigenvectorBasis k') x) * (f j x * star (x8c hH k (f j))) := by
    intro j
    rw [show x8c hH k' (f j) = ∑ x, star ((hH.eigenvectorBasis k') x) * f j x from rfl,
      Finset.mul_sum]; refine Finset.sum_congr rfl fun x _ => ?_; ring
  simp only [this]
  rw [Finset.sum_comm]
  simp only [← Finset.mul_sum, x8_K1 hH f hf]
  have h2 : ∀ x, star ((hH.eigenvectorBasis k') x) *
      (c * (hH.eigenvalues k : ℂ) * (hH.eigenvectorBasis k) x) =
      c * (hH.eigenvalues k : ℂ) * (star ((hH.eigenvectorBasis k') x) * (hH.eigenvectorBasis k) x) :=
    fun x => by ring
  simp only [h2, ← Finset.mul_sum, x8_orth]
  split_ifs <;> simp

theorem x8_K3 (f : K' → X → ℂ) (hf : ∀ x y, ∑ j, f j x * star (f j y) = c * J x y)
    (k : X) (hk : hH.eigenvalues k = 0) (j : K') : x8c hH k (f j) = 0 := by
  have h := x8_K2 hH f hf k k
  simp only [if_true, hk, Complex.ofReal_zero, mul_zero] at h
  have h' : ∑ j, Complex.normSq (x8c hH k (f j)) = 0 := by
    have : ((∑ j, Complex.normSq (x8c hH k (f j)) : ℝ) : ℂ) = 0 := by
      rw [← h, Complex.ofReal_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Complex.normSq_eq_conj_mul_self]; rfl
    exact_mod_cast this
  rw [Finset.sum_eq_zero_iff_of_nonneg (fun j _ => Complex.normSq_nonneg _)] at h'
  exact Complex.normSq_eq_zero.mp (h' j (Finset.mem_univ _))

def x8s (c : ℝ) (k : X) : ℂ := (Real.sqrt (c * hH.eigenvalues k) : ℂ)

def x8α (c : ℝ) (f : K' → X → ℂ) : Matrix K' {k // hH.eigenvalues k ≠ 0} ℂ :=
  Matrix.of fun j k => x8c hH k.1 (f j) / x8s hH c k.1

variable (hc : 0 < c) (hnn : ∀ k, 0 ≤ hH.eigenvalues k)
include hc hnn

theorem x8_ss (k : X) (hk : hH.eigenvalues k ≠ 0) :
    x8s hH c k * x8s hH c k = c * (hH.eigenvalues k : ℂ) ∧ x8s hH c k ≠ 0 ∧
      star (x8s hH c k) = x8s hH c k := by
  have hpos : 0 < c * hH.eigenvalues k := mul_pos hc (lt_of_le_of_ne (hnn k) (Ne.symm hk))
  refine ⟨?_, ?_, ?_⟩
  · rw [x8s, ← Complex.ofReal_mul, Real.mul_self_sqrt hpos.le]; simp
  · rw [x8s]; exact Complex.ofReal_ne_zero.mpr (Real.sqrt_ne_zero'.mpr hpos)
  · rw [x8s, Complex.star_def, Complex.conj_ofReal]

theorem x8_αgram (f : K' → X → ℂ) (hf : ∀ x y, ∑ j, f j x * star (f j y) = c * J x y) :
    (x8α hH c f)ᴴ * x8α hH c f = 1 := by
  ext k k'
  obtain ⟨h1, h2, h3⟩ := x8_ss hH hc hnn k.1 k.2
  obtain ⟨h1', h2', h3'⟩ := x8_ss hH hc hnn k'.1 k'.2
  simp only [mul_apply, conjTranspose_apply, x8α, of_apply, star_div₀, h3]
  have : ∀ j, star (x8c hH k.1 (f j)) / x8s hH c k.1 * (x8c hH k'.1 (f j) / x8s hH c k'.1) =
      (star (x8c hH k.1 (f j)) * x8c hH k'.1 (f j)) / (x8s hH c k.1 * x8s hH c k'.1) := by
    intro j; field_simp
  simp only [this, ← Finset.sum_div, x8_K2 hH f hf, one_apply]
  by_cases hkk : k = k'
  · subst hkk; simp only [if_true, h1]; exact div_self (h1 ▸ mul_ne_zero h2 h2)
  · have : ¬ k'.1 = k.1 := fun h => hkk (Subtype.ext h).symm
    simp [hkk, this]

theorem x8_K4 (f : K' → X → ℂ) (hf : ∀ x y, ∑ j, f j x * star (f j y) = c * J x y)
    (k : {k // hH.eigenvalues k ≠ 0}) (x : X) :
    ∑ j, star (x8α hH c f j k) * f j x = x8s hH c k.1 * (hH.eigenvectorBasis k.1) x := by
  obtain ⟨h1, h2, h3⟩ := x8_ss hH hc hnn k.1 k.2
  simp only [x8α, of_apply, star_div₀, h3]
  have : ∀ j, star (x8c hH k.1 (f j)) / x8s hH c k.1 * f j x =
      (f j x * star (x8c hH k.1 (f j))) / x8s hH c k.1 := fun j => by ring
  simp only [this, ← Finset.sum_div, x8_K1 hH f hf, ← h1]
  field_simp

theorem x8_K5 (f : K' → X → ℂ) (hf : ∀ x y, ∑ j, f j x * star (f j y) = c * J x y)
    (j : K') (x : X) :
    ∑ k : {k // hH.eigenvalues k ≠ 0}, x8α hH c f j k * (x8s hH c k.1 * (hH.eigenvectorBasis k.1) x)
      = f j x := by
  have : ∀ k : {k // hH.eigenvalues k ≠ 0}, x8α hH c f j k * (x8s hH c k.1 * (hH.eigenvectorBasis k.1) x)
      = x8c hH k.1 (f j) * (hH.eigenvectorBasis k.1) x := by
    intro k
    obtain ⟨h1, h2, h3⟩ := x8_ss hH hc hnn k.1 k.2
    simp only [x8α, of_apply]; field_simp
  simp only [this]
  rw [← x8_expand hH (f j) x, ← Fintype.sum_subtype_add_sum_subtype (fun k => hH.eigenvalues k ≠ 0)]
  have h0 : ∑ k : {k // ¬ hH.eigenvalues k ≠ 0}, x8c hH k.1 (f j) * (hH.eigenvectorBasis k.1) x = 0 :=
    Finset.sum_eq_zero fun k _ => by
      rw [x8_K3 hH f hf k.1 (not_not.mp k.2) j, zero_mul]
  rw [h0, add_zero]

theorem x8_W {L' : Type*} [Fintype L'] (f : K' → X → ℂ) (g : L' → X → ℂ)
    (hf : ∀ x y, ∑ j, f j x * star (f j y) = c * J x y)
    (hg : ∀ x y, ∑ l, g l x * star (g l y) = c * J x y) :
    let W := x8α hH c f * (x8α hH c g)ᴴ
    (∀ j x, ∑ l, W j l * g l x = f j x) ∧ (∀ l x, ∑ j, star (W j l) * f j x = g l x) ∧
    W * Wᴴ * W = W ∧ W.rank = Fintype.card {k // hH.eigenvalues k ≠ 0} := by
  intro W
  have hαf := x8_αgram hH hc hnn f hf
  have hαg := x8_αgram hH hc hnn g hg
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro j x
    simp only [W, mul_apply, conjTranspose_apply, Finset.sum_mul]
    rw [Finset.sum_comm]
    simp only [mul_assoc, ← Finset.mul_sum, x8_K4 hH hc hnn g hg]
    exact x8_K5 hH hc hnn f hf j x
  · intro l x
    simp only [W, mul_apply, conjTranspose_apply, star_sum, star_mul', star_star, Finset.sum_mul]
    rw [Finset.sum_comm]
    have : ∀ k : {k // hH.eigenvalues k ≠ 0}, ∑ j, star (x8α hH c f j k) * x8α hH c g l k * f j x =
        x8α hH c g l k * (x8s hH c k.1 * (hH.eigenvectorBasis k.1) x) := by
      intro k; rw [← x8_K4 hH hc hnn f hf, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_; ring
    simp only [this]
    exact x8_K5 hH hc hnn g hg l x
  · simp only [W, conjTranspose_mul, conjTranspose_conjTranspose, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (x8α hH c g)ᴴ, hαg, Matrix.one_mul, ← Matrix.mul_assoc (x8α hH c f)ᴴ, hαf,
      Matrix.one_mul]
  · apply le_antisymm
    · calc W.rank ≤ (x8α hH c f).rank := rank_mul_le_left _ _
        _ = ((x8α hH c f)ᴴ * x8α hH c f).rank := (rank_conjTranspose_mul_self _).symm
        _ = _ := by rw [hαf, rank_one]
    · have : x8α hH c f = W * x8α hH c g := by
        simp only [W, Matrix.mul_assoc, hαg, Matrix.mul_one]
      calc Fintype.card {k // hH.eigenvalues k ≠ 0} = (1 : Matrix {k // hH.eigenvalues k ≠ 0}
            {k // hH.eigenvalues k ≠ 0} ℂ).rank := (rank_one).symm
        _ = ((x8α hH c f)ᴴ * x8α hH c f).rank := by rw [hαf]
        _ = (x8α hH c f).rank := rank_conjTranspose_mul_self _
        _ ≤ W.rank := by rw [this]; exact rank_mul_le_left _ _

end gen
theorem x8_recv (V : Matrix (B × C) A ℂ) (rho : Matrix A A ℂ) (b b' : B) :
    receiverChannel V rho b b' = ∑ a, ∑ a', rho a a' * ∑ c, V (b, c) a * star (V (b', c) a') := by
  simp only [receiverChannel, QAlgorithms.traceRight, of_apply, mul_apply, conjTranspose_apply,
    Finset.sum_mul, Finset.mul_sum]
  conv_lhs => rw [Finset.sum_comm]; arg 2; ext y; rw [Finset.sum_comm]
  conv_lhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun a' _ =>
    Finset.sum_congr rfl fun c _ => ?_
  ring

theorem x8_comp (V : Matrix (B × C) A ℂ) (rho : Matrix A A ℂ) (c c' : C) :
    complementaryChannel V rho c c' = ∑ a, ∑ a', rho a a' * ∑ b, V (b, c) a * star (V (b, c') a') := by
  simp only [complementaryChannel, traceLeft, of_apply, mul_apply, conjTranspose_apply,
    Finset.sum_mul, Finset.mul_sum]
  conv_lhs => rw [Finset.sum_comm]; arg 2; ext y; rw [Finset.sum_comm]
  conv_lhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun a' _ =>
    Finset.sum_congr rfl fun b _ => ?_
  ring

theorem x8_recvK (V : Matrix (B × C) A ℂ) :
    receiverChannel V = krausApply (fun c => Matrix.of fun b a => V (b, c) a) := by
  funext rho; ext b b'
  rw [x8_recv, x8_kentry]; simp

theorem x8_compK (V : Matrix (B × C) A ℂ) :
    complementaryChannel V = krausApply (fun b => Matrix.of fun c a => V (b, c) a) := by
  funext rho; ext c c'
  rw [x8_comp, x8_kentry]; simp


end QAlgorithms.Papers.Independent.Claimed50.P48


noncomputable section

namespace QAlgorithms.Papers.Independent.Claimed50.P48

open scoped BigOperators Matrix Kronecker ComplexConjugate ComplexOrder ENNReal

open QAlgorithms.Papers.Independent.Information100.P67 (receiverChannel complementaryChannel environmentSwap)

attribute [local instance] Classical.propDecidable Classical.decEq

variable {A B C D K : Type*}

variable [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

variable [Fintype C] [DecidableEq C] [Fintype D] [DecidableEq D]

open Matrix

set_option linter.unusedSectionVars false

section gram
variable {X : Type*} [Fintype X] [DecidableEq X]

/-- Gram ("Choi") matrix of a family of vectors. -/
def x8G {K' : Type*} [Fintype K'] (f : K' → X → ℂ) : Matrix X X ℂ :=
  Matrix.of fun x y => ∑ j, f j x * star (f j y)

theorem x8G_psd {K' : Type*} [Fintype K'] (f : K' → X → ℂ) : (x8G f).PosSemidef := by
  have : x8G f = (Matrix.of fun j x => star (f j x))ᴴ * Matrix.of fun j x => star (f j x) := by
    ext x y; simp [x8G, mul_apply, conjTranspose_apply]
  rw [this]; exact posSemidef_conjTranspose_mul_self _

/-- spectral family of a PSD matrix. -/
def x8h {J : Matrix X X ℂ} (hH : J.IsHermitian) : {k // hH.eigenvalues k ≠ 0} → X → ℂ :=
  fun k x => x8s hH 1 k.1 * (hH.eigenvectorBasis k.1) x

theorem x8h_G {J : Matrix X X ℂ} (hP : J.PosSemidef) : x8G (x8h hP.isHermitian) = J := by
  have hnn : ∀ k, 0 ≤ hP.isHermitian.eigenvalues k := fun k => hP.eigenvalues_nonneg k
  ext x y
  rw [x8_spec hP.isHermitian x y]
  simp only [x8G, of_apply, x8h]
  rw [← Fintype.sum_subtype_add_sum_subtype (fun k => hP.isHermitian.eigenvalues k ≠ 0)]
  have h0 : ∑ k : {k // ¬ hP.isHermitian.eigenvalues k ≠ 0},
      (hP.isHermitian.eigenvalues k.1 : ℂ) * (hP.isHermitian.eigenvectorBasis k.1) x *
        star ((hP.isHermitian.eigenvectorBasis k.1) y) = 0 :=
    Finset.sum_eq_zero fun k _ => by have := k.2; rw [not_not] at this; simp [this]
  rw [h0, add_zero]
  refine Finset.sum_congr rfl fun k _ => ?_
  obtain ⟨h1, -, h3⟩ := x8_ss hP.isHermitian one_pos hnn k.1 k.2
  rw [star_mul', h3]
  have : (hP.isHermitian.eigenvalues k.1 : ℂ) = x8s hP.isHermitian 1 k.1 * x8s hP.isHermitian 1 k.1 := by
    rw [h1]; simp
  rw [this]; ring

theorem x8_hf {J : Matrix X X ℂ} {K' : Type*} [Fintype K'] (f : K' → X → ℂ) (hf : x8G f = J) :
    ∀ x y, ∑ j, f j x * star (f j y) = ((1 : ℝ) : ℂ) * J x y := by
  intro x y; rw [← hf]; simp [x8G]

theorem x8_card_le {J : Matrix X X ℂ} (hP : J.PosSemidef) {K' : Type*} [Fintype K']
    (f : K' → X → ℂ) (hf : x8G f = J) :
    Fintype.card {k // hP.isHermitian.eigenvalues k ≠ 0} ≤ Fintype.card K' := by
  have hnn : ∀ k, 0 ≤ hP.isHermitian.eigenvalues k := fun k => hP.eigenvalues_nonneg k
  have h := x8_αgram hP.isHermitian one_pos hnn f (x8_hf f hf)
  calc Fintype.card {k // hP.isHermitian.eigenvalues k ≠ 0}
      = (1 : Matrix {k // hP.isHermitian.eigenvalues k ≠ 0} {k // hP.isHermitian.eigenvalues k ≠ 0} ℂ).rank :=
        rank_one.symm
    _ = _ := by rw [← h, rank_conjTranspose_mul_self]
    _ ≤ Fintype.card K' := rank_le_card_height _

theorem x8_uniq {K' L' : Type*} [Fintype K'] [Fintype L'] [DecidableEq K'] [DecidableEq L'] (f : K' → X → ℂ) (g : L' → X → ℂ)
    (hfg : x8G f = x8G g) :
    ∃ W : Matrix K' L' ℂ, PartialIsometry W ∧ (∀ j x, ∑ l, W j l * g l x = f j x) ∧
      (∀ l x, ∑ j, star (W j l) * f j x = g l x) ∧
      (Fintype.card K' ≤ Fintype.card {k // (x8G_psd g).isHermitian.eigenvalues k ≠ 0} →
        Fintype.card L' ≤ Fintype.card {k // (x8G_psd g).isHermitian.eigenvalues k ≠ 0} →
        Wᴴ * W = 1 ∧ W * Wᴴ = 1) := by
  set hP := x8G_psd g
  have hnn : ∀ k, 0 ≤ hP.isHermitian.eigenvalues k := fun k => hP.eigenvalues_nonneg k
  have hf := x8_hf f hfg
  have hg := x8_hf g rfl
  obtain ⟨W1, W2, W3, -⟩ := x8_W hP.isHermitian one_pos hnn f g hf hg
  refine ⟨_, W3, W1, W2, fun hK hL => ?_⟩
  have hαf := x8_αgram hP.isHermitian one_pos hnn f hf
  have hαg := x8_αgram hP.isHermitian one_pos hnn g hg
  have cK := x8_card_le hP f hfg
  have cL := x8_card_le hP g rfl
  have eK : K' ≃ {k // hP.isHermitian.eigenvalues k ≠ 0} :=
    Fintype.equivOfCardEq (le_antisymm hK cK)
  have eL : L' ≃ {k // hP.isHermitian.eigenvalues k ≠ 0} :=
    Fintype.equivOfCardEq (le_antisymm hL cL)
  have hαf' := (mul_eq_one_comm_of_equiv eK.symm).1 hαf
  have hαg' := (mul_eq_one_comm_of_equiv eL.symm).1 hαg
  constructor
  · simp only [conjTranspose_mul, conjTranspose_conjTranspose, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (x8α hP.isHermitian 1 f)ᴴ, hαf, Matrix.one_mul, hαg']
  · simp only [conjTranspose_mul, conjTranspose_conjTranspose, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (x8α hP.isHermitian 1 g)ᴴ, hαg, Matrix.one_mul, hαf']

end gram

/-- dilation family: column c of the dilation, as a vector on A × B. -/
def x8f (V : Matrix (B × C) A ℂ) : C → A × B → ℂ := fun c x => V (x.2, c) x.1

/-- dilation from a family. -/
def x8V {K' : Type*} (h : K' → A × B → ℂ) : Matrix (B × K') A ℂ := fun bk a => h bk.2 (a, bk.1)

theorem x8_recv_G (V : Matrix (B × C) A ℂ) (rho : Matrix A A ℂ) (b b' : B) :
    receiverChannel V rho b b' = ∑ a, ∑ a', rho a a' * x8G (x8f V) (a, b) (a', b') := by
  rw [x8_recv]; rfl

theorem x8_kraus_G {K' : Type*} [Fintype K'] (E : K' → Matrix B A ℂ) (rho : Matrix A A ℂ) (b b' : B) :
    krausApply E rho b b' = ∑ a, ∑ a', rho a a' * x8G (fun j (x : A × B) => E j x.2 x.1) (a, b) (a', b') := by
  rw [x8_kentry]; rfl

theorem x8_G_ext {K' L' : Type*} [Fintype K'] [Fintype L'] (f : K' → A × B → ℂ) (g : L' → A × B → ℂ)
    (h : ∀ rho : Matrix A A ℂ, ∀ b b', ∑ a, ∑ a', rho a a' * x8G f (a, b) (a', b') =
      ∑ a, ∑ a', rho a a' * x8G g (a, b) (a', b')) : x8G f = x8G g := by
  ext ⟨a, b⟩ ⟨a', b'⟩
  have := h (Matrix.single a a' 1) b b'
  simpa [Matrix.single_apply, ite_and, Finset.sum_ite_eq, Finset.sum_ite_eq'] using this

theorem x8_kron {C' D' : Type*} [Fintype C'] (J : Matrix D' C' ℂ) (V : Matrix (B × C') A ℂ) :
    ((1 : Matrix B B ℂ) ⊗ₖ J) * V = fun bd a => ∑ c, J bd.2 c * V (bd.1, c) a := by
  ext ⟨b, d⟩ a
  simp [mul_apply, kroneckerMap_apply, one_apply, Fintype.sum_prod_type, ite_mul, Finset.sum_ite_eq]

/-- general uniqueness of complements. -/
theorem x8_equiv (V : Matrix (B × C) A ℂ) (W : Matrix (B × D) A ℂ)
    (h : receiverChannel V = receiverChannel W) :
    Equivalent (complementaryChannel V) (complementaryChannel W) := by
  have hG : x8G (x8f W) = x8G (x8f V) := x8_G_ext _ _ fun rho b b' => by
    rw [← x8_recv_G, ← x8_recv_G, h]
  obtain ⟨Wm, hPI, h1, h2, -⟩ := x8_uniq (x8f W) (x8f V) hG
  have hR : ∀ b, (Matrix.of fun d a => W (b, d) a) = Wm * Matrix.of fun c a => V (b, c) a := by
    intro b; ext d a; rw [mul_apply]; exact (h1 d (a, b)).symm
  have hR' : ∀ b, (Matrix.of fun c a => V (b, c) a) = Wmᴴ * Matrix.of fun d a => W (b, d) a := by
    intro b; ext c a; rw [mul_apply]; exact (h2 c (a, b)).symm
  refine ⟨Wm, hPI, ?_, ?_⟩
  · intro rho
    rw [x8_compK, x8_compK]
    simp only [krausApply, Matrix.mul_sum, Matrix.sum_mul]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [hR b]; simp only [conjTranspose_mul, Matrix.mul_assoc]
  · intro rho
    rw [x8_compK, x8_compK]
    simp only [krausApply, Matrix.mul_sum, Matrix.sum_mul]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [hR' b]; simp only [conjTranspose_mul, conjTranspose_conjTranspose, Matrix.mul_assoc]

end QAlgorithms.Papers.Independent.Claimed50.P48


noncomputable section

namespace QAlgorithms.Papers.Independent.Claimed50.P48

open scoped BigOperators Matrix Kronecker ComplexConjugate ComplexOrder ENNReal

open QAlgorithms.Papers.Independent.Information100.P67 (receiverChannel complementaryChannel environmentSwap)

attribute [local instance] Classical.propDecidable Classical.decEq

variable {A B C D K : Type*}

variable [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

variable [Fintype C] [DecidableEq C] [Fintype D] [DecidableEq D]

open Matrix

set_option linter.unusedSectionVars false

theorem x8_fV {K' : Type*} (h : K' → A × B → ℂ) : x8f (x8V h) = h := rfl

/-- spectral dilation of a dilation, indexed by Fin. -/
theorem x8_spec_dil (V : Matrix (B × C) A ℂ) :
    ∃ (r : ℕ) (U : Matrix (B × Fin r) A ℂ),
      r = Fintype.card {k // (x8G_psd (x8f V)).isHermitian.eigenvalues k ≠ 0} ∧
      x8G (x8f U) = x8G (x8f V) := by
  set hP := x8G_psd (x8f V)
  let e := Fintype.equivFin {k // hP.isHermitian.eigenvalues k ≠ 0}
  refine ⟨_, x8V (fun i => x8h hP.isHermitian (e.symm i)), rfl, ?_⟩
  rw [x8_fV]
  refine Eq.trans ?_ (x8h_G hP)
  ext x y
  simp only [x8G, of_apply]
  exact Equiv.sum_comp e.symm (fun k => x8h hP.isHermitian k x * star (x8h hP.isHermitian k y))

theorem x8_recv_eq (V : Matrix (B × C) A ℂ) (W : Matrix (B × D) A ℂ)
    (h : x8G (x8f V) = x8G (x8f W)) : receiverChannel V = receiverChannel W := by
  funext rho; ext b b'; rw [x8_recv_G, x8_recv_G, h]

theorem x8_G_of_recv (V : Matrix (B × C) A ℂ) (W : Matrix (B × D) A ℂ)
    (h : receiverChannel V = receiverChannel W) : x8G (x8f V) = x8G (x8f W) :=
  x8_G_ext _ _ fun rho b b' => by rw [← x8_recv_G, ← x8_recv_G, h]

theorem x8_stine [Nonempty A] (Phi : Superop A B) (hPhi : FiniteKrausCP Phi) :
    ∃ (r : ℕ) (V : Matrix (B × Fin r) A ℂ),
      r ≤ Fintype.card A * Fintype.card B ∧ receiverChannel V = Phi ∧ (IsChannel Phi → Vᴴ * V = 1) ∧
      ∀ (s : ℕ) (W : Matrix (B × Fin s) A ℂ), receiverChannel W = Phi →
        ∃ J : Matrix (Fin s) (Fin r) ℂ, PartialIsometry J ∧
          W = ((1 : Matrix B B ℂ) ⊗ₖ J) * V ∧ V = ((1 : Matrix B B ℂ) ⊗ₖ Jᴴ) * W := by
  obtain ⟨r0, E, rfl⟩ := hPhi
  set V0 : Matrix (B × Fin r0) A ℂ := x8V (fun j (x : A × B) => E j x.2 x.1)
  have hV0 : receiverChannel V0 = krausApply E := by
    funext rho; ext b b'; rw [x8_recv_G, x8_kraus_G]; rfl
  obtain ⟨r, V, hr, hG⟩ := x8_spec_dil V0
  have hV : receiverChannel V = krausApply E := by rw [x8_recv_eq V V0 hG, hV0]
  refine ⟨r, V, ?_, hV, ?_, ?_⟩
  · rw [hr, ← Fintype.card_prod]; exact Fintype.card_subtype_le _
  · rintro ⟨m, E', hE', hPE'⟩
    have hEE : receiverChannel V = receiverChannel (x8V (fun j (x : A × B) => E' j x.2 x.1)) := by
      rw [hV]; funext rho; ext b b'; rw [hPE', x8_recv_G, x8_kraus_G]; rfl
    have hG' := x8_G_of_recv _ _ hEE
    rw [← hE']
    ext a a'
    have := fun b => congrFun (congrFun hG' (a', b)) (a, b)
    simp only [x8G, x8f, x8V, of_apply] at this
    simp only [mul_apply, conjTranspose_apply, Fintype.sum_prod_type, Matrix.sum_apply]
    rw [Finset.sum_comm (s := Finset.univ (α := Fin m))]
    refine Finset.sum_congr rfl fun b _ => ?_
    have h2 := this b
    calc ∑ i, star (V (b, i) a) * V (b, i) a' = ∑ i, V (b, i) a' * star (V (b, i) a) :=
          Finset.sum_congr rfl fun _ _ => mul_comm _ _
      _ = ∑ j, E' j b a' * star (E' j b a) := h2
      _ = _ := Finset.sum_congr rfl fun _ _ => mul_comm _ _
  · intro s W hW
    have hG2 : x8G (x8f W) = x8G (x8f V) := x8_G_of_recv _ _ (hW.trans hV.symm)
    obtain ⟨J, hPI, h1, h2, -⟩ := x8_uniq (x8f W) (x8f V) hG2
    refine ⟨J, hPI, ?_, ?_⟩
    · rw [x8_kron]; ext ⟨b, j⟩ a; exact (h1 j (a, b)).symm
    · rw [x8_kron]; ext ⟨b, l⟩ a; exact (h2 l (a, b)).symm

/-- swap the output and environment factors. -/
def x8sw (V : Matrix (B × C) A ℂ) : Matrix (C × B) A ℂ := fun cb a => V (cb.2, cb.1) a

theorem x8_sw_recv (V : Matrix (B × C) A ℂ) : receiverChannel (x8sw V) = complementaryChannel V := by
  funext rho; ext c c'; rw [x8_recv, x8_comp]; rfl

theorem x8_sw_comp (V : Matrix (B × C) A ℂ) : complementaryChannel (x8sw V) = receiverChannel V := by
  funext rho; ext b b'; rw [x8_recv, x8_comp]; rfl

theorem x8_ce [Nonempty A]
    (Phi : Superop A B) (Psi : Superop A C) (Psi2 : Superop A D)
    (h : CPComplementary Phi Psi) (h2 : CPComplementary Phi Psi2) :
    Equivalent Psi Psi2 ∧
    (∀ (V : Matrix (B × C) A ℂ) (W : Matrix (B × D) A ℂ),
      MinimalDilation Phi V → MinimalDilation Phi W →
      ∃ J : Matrix D C ℂ, Jᴴ * J = 1 ∧ J * Jᴴ = 1 ∧
        W = ((1 : Matrix B B ℂ) ⊗ₖ J) * V ∧ V = ((1 : Matrix B B ℂ) ⊗ₖ Jᴴ) * W) ∧
    (∀ Phi2 : Superop A D, CPComplementary Psi Phi2 → Equivalent Phi Phi2) := by
  obtain ⟨V1, hV1, hV1'⟩ := h
  obtain ⟨V2, hV2, hV2'⟩ := h2
  refine ⟨?_, ?_, ?_⟩
  · rw [← hV1', ← hV2']; exact x8_equiv V1 V2 (hV1.trans hV2.symm)
  · rintro V W ⟨hV, hVm⟩ ⟨hW, hWm⟩
    have hG2 : x8G (x8f W) = x8G (x8f V) := x8_G_of_recv _ _ (hW.trans hV.symm)
    obtain ⟨J, -, h1, h2, h3⟩ := x8_uniq (x8f W) (x8f V) hG2
    obtain ⟨r, U, hr, hU⟩ := x8_spec_dil V
    have hUr : receiverChannel U = Phi := by rw [x8_recv_eq U V hU, hV]
    obtain ⟨hJ1, hJ2⟩ := h3 (hr ▸ hWm r U hUr) (hr ▸ hVm r U hUr)
    refine ⟨J, hJ1, hJ2, ?_, ?_⟩
    · rw [x8_kron]; ext ⟨b, j⟩ a; exact (h1 j (a, b)).symm
    · rw [x8_kron]; ext ⟨b, l⟩ a; exact (h2 l (a, b)).symm
  · rintro Phi2 ⟨U, hU, hU'⟩
    rw [← hU', ← hV1, ← x8_sw_comp V1]
    refine x8_equiv (x8sw V1) U ?_
    rw [x8_sw_recv, hV1', hU]

end QAlgorithms.Papers.Independent.Claimed50.P48


noncomputable section

namespace QAlgorithms.Papers.Independent.Claimed50.P48

open scoped BigOperators Matrix Kronecker ComplexConjugate ComplexOrder ENNReal

open QAlgorithms.Papers.Independent.Information100.P67 (receiverChannel complementaryChannel environmentSwap)

attribute [local instance] Classical.propDecidable Classical.decEq

variable {A B C D K : Type*}

variable [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

variable [Fintype C] [DecidableEq C] [Fintype D] [DecidableEq D]

variable [Fintype K] [DecidableEq K]

open Matrix

set_option linter.unusedSectionVars false

theorem x8_gram_apply (phi : K → EuclideanSpace ℂ B) (a b : K) :
    gram phi a b = ∑ i, star (phi b i) * phi a i := by
  simp [gram, PiLp.inner_apply, mul_comm]

theorem x8_gram_psd (phi : K → EuclideanSpace ℂ B) : (gram phi).PosSemidef := by
  have : gram phi = (Matrix.of fun i a => star (phi a i))ᴴ * Matrix.of fun i a => star (phi a i) := by
    ext a b; rw [x8_gram_apply, mul_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [mul_comm]
  rw [this]; exact posSemidef_conjTranspose_mul_self _

/-- rank-one dilation. -/
def x8D (psi : K → EuclideanSpace ℂ A) (phi : K → EuclideanSpace ℂ B) : Matrix (B × K) A ℂ :=
  fun bk a => phi bk.2 bk.1 * conj (psi bk.2 a)

theorem x8D_recv (psi : K → EuclideanSpace ℂ A) (phi : K → EuclideanSpace ℂ B) :
    receiverChannel (x8D psi phi) = krausApply (rankOneKraus psi phi) := by
  rw [x8_recvK]; rfl

theorem x8D_comp (psi : K → EuclideanSpace ℂ A) (phi : K → EuclideanSpace ℂ B) :
    complementaryChannel (x8D psi phi) = arbitraryVectorComplement (gram phi) psi := by
  funext rho; ext k k'
  rw [x8_compK, x8_kentry]
  simp only [arbitraryVectorComplement, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun a' _ => ?_
  rw [x8_gram_apply]
  simp only [Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun b _ => ?_
  simp only [x8D, of_apply, star_mul', Complex.star_def, Complex.conj_conj]
  ring

theorem x8_comp_gram (psi : K → EuclideanSpace ℂ A) (phi : K → EuclideanSpace ℂ B) :
    CPComplementary (krausApply (rankOneKraus psi phi)) (arbitraryVectorComplement (gram phi) psi) :=
  ⟨x8D psi phi, x8D_recv psi phi, x8D_comp psi phi⟩

theorem x8_sqrt_gram (c : Matrix K K ℂ) (hc : c.PosSemidef) :
    ∃ phi2 : K → EuclideanSpace ℂ K, gram phi2 = c := by
  have hH := hc.isHermitian
  refine ⟨fun a => WithLp.toLp 2 (fun k => (Real.sqrt (hH.eigenvalues k) : ℂ) *
    (hH.eigenvectorBasis k) a), ?_⟩
  ext a b
  rw [x8_gram_apply, x8_spec hH a b]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [star_mul', Complex.star_def, Complex.conj_ofReal]
  have h : (Real.sqrt (hH.eigenvalues k) : ℂ) * (Real.sqrt (hH.eigenvalues k) : ℂ) =
      (hH.eigenvalues k : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (hc.eigenvalues_nonneg k)]
  linear_combination ((hH.eigenvectorBasis k) a * (starRingEnd ℂ) ((hH.eigenvectorBasis k) b)) * h

theorem x8_avc_kraus (v : Matrix K B ℂ) (psi : K → EuclideanSpace ℂ A) :
    arbitraryVectorComplement (v * vᴴ) psi = krausApply (gramKraus v psi) := by
  funext rho; ext k k'
  rw [x8_kentry]
  simp only [arbitraryVectorComplement, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun a' _ => ?_
  rw [mul_apply]
  simp only [Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [gramKraus, conjTranspose_apply, star_mul', Complex.star_def, Complex.conj_conj]
  ring

/-- complements transfer along equivalence. -/
theorem x8_transfer {E' : Type*} [Fintype E'] [DecidableEq E'] (Phi : Superop A B) (Psi : Superop A C)
    (Phi' : Superop A E') (h : CPComplementary Phi Psi) (he : Equivalent Psi Phi') :
    CPComplementary Phi Phi' := by
  obtain ⟨V, hV1, hV2⟩ := h
  obtain ⟨W, hPI, hW1, hW2⟩ := he
  set R : B → Matrix C A ℂ := fun b => Matrix.of fun c a => V (b, c) a
  obtain ⟨P, hPdef⟩ : ∃ P, P = Wᴴ * W := ⟨_, rfl⟩
  have hPP : P * P = P := by
    rw [hPdef]
    calc Wᴴ * W * (Wᴴ * W) = Wᴴ * (W * Wᴴ * W) := by simp only [Matrix.mul_assoc]
      _ = Wᴴ * W := by rw [hPI]
  have hPH : Pᴴ = P := by simp [hPdef]
  have hPsi : ∀ rho, Psi rho = ∑ b, R b * rho * (R b)ᴴ := by
    intro rho; rw [← hV2, x8_compK]; simp only [krausApply, R]
  have hM : ∑ b, R b * (R b)ᴴ = P * (∑ b, R b * (R b)ᴴ) * P := by
    have := hW2 1
    rw [hW1, hPsi] at this
    simp only [Matrix.mul_one] at this
    refine this.trans ?_; simp only [hPdef, Matrix.mul_assoc]
  have h1 : (1 - P) * P = 0 := by rw [Matrix.sub_mul, Matrix.one_mul, hPP, sub_self]
  have h2 : P * (1 - P) = 0 := by rw [Matrix.mul_sub, Matrix.mul_one, hPP, sub_self]
  -- (1 - P) R b = 0
  have hQ : ∀ b, (1 - P) * R b = 0 := by
    have h0 : ∑ b, ((1 - P) * R b) * ((1 - P) * R b)ᴴ = 0 := by
      have : ∑ b, ((1 - P) * R b) * ((1 - P) * R b)ᴴ = (1 - P) * (∑ b, R b * (R b)ᴴ) * (1 - P) := by
        simp only [conjTranspose_mul, Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_assoc]
        refine Finset.sum_congr rfl fun b _ => ?_
        rw [conjTranspose_sub, conjTranspose_one, hPH]
      rw [this]
      generalize (∑ b, R b * (R b)ᴴ) = M at hM ⊢
      rw [hM, show (1 - P) * (P * M * P) * (1 - P) = ((1 - P) * P) * M * (P * (1 - P)) by
        simp only [Matrix.mul_assoc], h1]
      simp
    have htr := congrArg Matrix.trace h0
    rw [trace_sum, trace_zero] at htr
    intro b
    have hnn : ∀ b, 0 ≤ (((1 - P) * R b) * ((1 - P) * R b)ᴴ).trace := fun b =>
      (posSemidef_self_mul_conjTranspose _).trace_nonneg
    have := (Finset.sum_eq_zero_iff_of_nonneg (fun b _ => hnn b)).mp htr b (Finset.mem_univ _)
    exact trace_mul_conjTranspose_self_eq_zero_iff.mp this
  have hPR : ∀ b, P * R b = R b := by
    intro b; have := hQ b
    rw [Matrix.sub_mul, Matrix.one_mul, sub_eq_zero] at this; exact this.symm
  set V' : Matrix (B × E') A ℂ := fun be a => (W * R be.1) be.2 a
  refine ⟨V', ?_, ?_⟩
  · rw [← hV1, x8_recvK, x8_recvK]
    funext rho; ext b b'
    rw [x8_kentry, x8_kentry]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun a' _ => ?_
    congr 1
    have key : (W * R b')ᴴ * (W * R b) = (R b')ᴴ * R b := by
      rw [conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc Wᴴ, ← hPdef, hPR]
    have := congrFun (congrFun key a') a
    simp only [mul_apply, conjTranspose_apply] at this
    have e1 : ∀ e, (Matrix.of fun b a => V' (b, e) a) b a = (W * R b) e a := fun e => rfl
    have e2 : ∀ e, (Matrix.of fun b a => V' (b, e) a) b' a' = (W * R b') e a' := fun e => rfl
    have e3 : ∀ c, (Matrix.of fun b a => V (b, c) a) b a = R b c a := fun c => rfl
    have e4 : ∀ c, (Matrix.of fun b a => V (b, c) a) b' a' = R b' c a' := fun c => rfl
    simp only [e1, e2, e3, e4]
    calc _ = ∑ e, star ((W * R b') e a') * (W * R b) e a := Finset.sum_congr rfl fun _ _ => mul_comm _ _
      _ = _ := this
      _ = _ := Finset.sum_congr rfl fun _ _ => mul_comm _ _
  · funext rho
    rw [x8_compK, hW1, hPsi]
    simp only [krausApply, Matrix.mul_sum, Matrix.sum_mul]
    refine Finset.sum_congr rfl fun b _ => ?_
    have : (Matrix.of fun e a => V' (b, e) a) = W * R b := by ext e a; rfl
    rw [this]; simp only [conjTranspose_mul, Matrix.mul_assoc]

theorem x8_ebc [Nonempty A]
    (psi : K → EuclideanSpace ℂ A) (phi : K → EuclideanSpace ℂ B) :
    (gram phi).PosSemidef ∧
    CPComplementary (krausApply (rankOneKraus psi phi)) (arbitraryVectorComplement (gram phi) psi) ∧
    (∀ c : Matrix K K ℂ, c.PosSemidef → ∃ phi2 : K → EuclideanSpace ℂ K, gram phi2 = c ∧
      CPComplementary (krausApply (rankOneKraus psi phi2)) (arbitraryVectorComplement c psi)) ∧
    (∀ v : Matrix K B ℂ, arbitraryVectorComplement (v * vᴴ) psi = krausApply (gramKraus v psi)) ∧
    (∀ Phi : Superop A C, EBComplement Phi ↔
      ∃ (r : ℕ) (c : Matrix (Fin r) (Fin r) ℂ) (psi2 : Fin r → EuclideanSpace ℂ A),
        c.PosSemidef ∧ Equivalent (arbitraryVectorComplement c psi2) Phi) := by
  refine ⟨x8_gram_psd phi, x8_comp_gram psi phi, ?_, fun v => x8_avc_kraus v psi, ?_⟩
  · intro c hc
    obtain ⟨phi2, h2⟩ := x8_sqrt_gram c hc
    exact ⟨phi2, h2, h2 ▸ x8_comp_gram psi phi2⟩
  · intro Phi
    constructor
    · rintro ⟨n, E, ⟨r, psi2, phi2, rfl⟩, ⟨V, hV1, hV2⟩⟩
      refine ⟨r, gram phi2, psi2, x8_gram_psd phi2, ?_⟩
      rw [← x8D_comp, ← hV2]
      exact x8_equiv _ _ ((x8D_recv psi2 phi2).trans hV1.symm)
    · rintro ⟨r, c, psi2, hc, he⟩
      obtain ⟨phi2, h2⟩ := x8_sqrt_gram c hc
      refine ⟨r, krausApply (rankOneKraus psi2 phi2), ⟨r, psi2, phi2, rfl⟩, ?_⟩
      exact x8_transfer _ _ _ (h2 ▸ x8_comp_gram psi2 phi2) he

end QAlgorithms.Papers.Independent.Claimed50.P48



open scoped BigOperators Matrix Kronecker ComplexConjugate ComplexOrder ENNReal

open QAlgorithms.Papers.Independent.Information100.P67 (receiverChannel complementaryChannel environmentSwap)

open QAlgorithms.Papers.Independent.Information100.P03 (PureEnsemble convexRoof)

open QAlgorithms.Papers.Independent.Information100.P50 (schattenNorm)

open QAlgorithms.Papers.Independent.Information100.P60 (wernerHolevo)

open QAlgorithms.Papers.Independent.Information100.P56 (entropy)

attribute [local instance] Classical.propDecidable Classical.decEq

variable {A B C D A2 B2 C2 K : Type*}

variable [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

variable [Fintype C] [DecidableEq C] [Fintype D] [DecidableEq D]

variable [Fintype A2] [DecidableEq A2] [Fintype B2] [DecidableEq B2]

variable [Fintype C2] [DecidableEq C2] [Fintype K] [DecidableEq K]

open QAlgorithms QAlgorithms.Papers.Independent.Claimed50.P48 in
/-- Equations (13)–(15), PDF pp.4–5: arbitrary vectors, the converse Gram
construction, Kraus formula, and ALL complements up to (2). -/
theorem solution [Nonempty A]
    (psi : K → EuclideanSpace ℂ A) (phi : K → EuclideanSpace ℂ B) :
    (gram phi).PosSemidef ∧
    CPComplementary (krausApply (rankOneKraus psi phi)) (arbitraryVectorComplement (gram phi) psi) ∧
    (∀ c : Matrix K K ℂ, c.PosSemidef → ∃ phi2 : K → EuclideanSpace ℂ K, gram phi2 = c ∧
      CPComplementary (krausApply (rankOneKraus psi phi2)) (arbitraryVectorComplement c psi)) ∧
    (∀ v : Matrix K B ℂ, arbitraryVectorComplement (v * vᴴ) psi = krausApply (gramKraus v psi)) ∧
    (∀ Phi : Superop A C, EBComplement Phi ↔
      ∃ (r : ℕ) (c : Matrix (Fin r) (Fin r) ℂ) (psi2 : Fin r → EuclideanSpace ℂ A),
        c.PosSemidef ∧ Equivalent (arbitraryVectorComplement c psi2) Phi) :=
  x8_ebc psi phi



