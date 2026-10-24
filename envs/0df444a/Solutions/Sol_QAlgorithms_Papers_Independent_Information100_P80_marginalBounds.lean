-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Information100.P80.marginalBounds
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-23T06:12:28.4829+00:00
-- url     : https://prove2.me/submissions/51d06a7f-cc36-442b-9f96-2114b4297e0e

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P80

noncomputable section
open scoped Matrix ComplexConjugate ComplexOrder

namespace X7B14MB

open QAlgorithms

lemma X7_opq {n : Type*} [Fintype n] [DecidableEq n] (A : Matrix n n ℂ) (z : n → ℂ) :
    (star z ⬝ᵥ (A *ᵥ z)).re ≤ specNorm A * ∑ i, ‖z i‖ ^ 2 := by
  open scoped Matrix.Norms.L2Operator in
  have h1 := Matrix.l2_opNorm_mulVec A (WithLp.toLp 2 z)
  set x : EuclideanSpace ℂ n := WithLp.toLp 2 z
  set y : EuclideanSpace ℂ n := WithLp.toLp 2 (A *ᵥ z)
  have hin : star z ⬝ᵥ (A *ᵥ z) = inner ℂ x y := by
    rw [EuclideanSpace.inner_toLp_toLp, dotProduct_comm]
  have hx : ‖x‖ ^ 2 = ∑ i, ‖z i‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
  have hy : ‖y‖ ≤ specNorm A * ‖x‖ := h1
  rw [hin, ← hx]
  calc (inner ℂ x y).re ≤ ‖inner ℂ x y‖ := Complex.re_le_norm _
    _ ≤ ‖x‖ * ‖y‖ := norm_inner_le_norm x y
    _ ≤ ‖x‖ * (specNorm A * ‖x‖) := by gcongr
    _ = specNorm A * ‖x‖ ^ 2 := by ring


lemma X7_rot3 {α β γ M : Type*} [Fintype α] [Fintype β] [Fintype γ] [AddCommMonoid M]
    (f : α → β → γ → M) : ∑ a, ∑ b, ∑ c, f a b c = ∑ c, ∑ a, ∑ b, f a b c := by
  calc ∑ a, ∑ b, ∑ c, f a b c = ∑ a, ∑ c, ∑ b, f a b c :=
        Finset.sum_congr rfl (fun a _ => Finset.sum_comm)
    _ = ∑ c, ∑ a, ∑ b, f a b c := Finset.sum_comm

lemma X7_key {B R : Type*} [Fintype B] [Fintype R] [DecidableEq B] [DecidableEq R]
    (G : Matrix (B × R) (B × R) ℂ) (hG : G.IsHermitian) (ω : B → R → R → ℂ) :
    ∑ b, ‖∑ r, ∑ b', ∑ t, G (b, r) (b', t) * ω b' t r‖ ^ 2 ≤
      specNorm (traceRight (G * G)) * ∑ b', ∑ t, ∑ r, ‖ω b' t r‖ ^ 2 := by
  classical
  set c := specNorm (traceRight (G * G)) with hc
  set z : B → ℂ := fun b => ∑ r, ∑ b', ∑ t, G (b, r) (b', t) * ω b' t r with hzdef
  let a : B → EuclideanSpace ℂ (B × R × R) :=
    fun b => WithLp.toLp 2 (fun i => conj (G (b, i.2.2) (i.1, i.2.1)))
  let W : EuclideanSpace ℂ (B × R × R) := WithLp.toLp 2 (fun i => ω i.1 i.2.1 i.2.2)
  have hz : ∀ b, inner ℂ (a b) W = z b := by
    intro b
    rw [EuclideanSpace.inner_toLp_toLp]
    simp only [dotProduct, Fintype.sum_prod_type, Pi.star_apply, RCLike.star_def,
      Complex.conj_conj, hzdef]
    rw [X7_rot3]
    refine Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun b' _ =>
      Finset.sum_congr rfl fun t _ => ?_
    ring
  have hgram : ∀ b b', inner ℂ (a b) (a b') = traceRight (G * G) b b' := by
    intro b b'
    rw [EuclideanSpace.inner_toLp_toLp]
    simp only [dotProduct, Fintype.sum_prod_type, Pi.star_apply, RCLike.star_def,
      Complex.conj_conj, traceRight, Matrix.of_apply, Matrix.mul_apply]
    rw [X7_rot3]
    refine Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun b'' _ =>
      Finset.sum_congr rfl fun t _ => ?_
    have := congrFun (congrFun hG (b'', t)) (b', r)
    simp only [Matrix.conjTranspose_apply, RCLike.star_def] at this
    rw [← this]
    ring
  set u : EuclideanSpace ℂ (B × R × R) := ∑ b, z b • a b with hu
  set S : ℝ := ∑ b, ‖z b‖ ^ 2 with hS
  have huW : inner ℂ u W = (S : ℂ) := by
    rw [hu, sum_inner]
    simp only [inner_smul_left, hz, hS]
    push_cast
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [Complex.conj_mul']
  have huu : ‖u‖ ^ 2 ≤ c * S := by
    have h1 : inner ℂ u u = star z ⬝ᵥ (traceRight (G * G) *ᵥ z) := by
      rw [hu, sum_inner]
      simp only [inner_sum, inner_smul_left, inner_smul_right, hgram, dotProduct,
        Matrix.mulVec, Pi.star_apply, RCLike.star_def, Finset.mul_sum]
      refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun b' _ => ?_
      ring
    have h2 := X7_opq (traceRight (G * G)) z
    rw [← h1] at h2
    rw [norm_sq_eq_re_inner (𝕜 := ℂ)]
    exact h2
  have hW : ‖W‖ ^ 2 = ∑ b', ∑ t, ∑ r, ‖ω b' t r‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    simp only [Fintype.sum_prod_type]
    rfl
  have hc0 : 0 ≤ c := by
    rw [hc]; unfold specNorm
    open scoped Matrix.Norms.L2Operator in exact norm_nonneg _
  have hcross : RCLike.re (inner ℂ ((c : ℂ) • W) u) = c * S := by
    rw [inner_smul_left, ← inner_conj_symm, huW]
    simp
  have h0 := norm_sub_sq (𝕜 := ℂ) ((c : ℂ) • W) u
  rw [hcross, norm_smul] at h0
  have hcn : ‖(c : ℂ)‖ = c := by simp [abs_of_nonneg hc0]
  rw [hcn] at h0
  have hnn : 0 ≤ ‖(c : ℂ) • W - u‖ ^ 2 := by positivity
  change S ≤ c * ∑ b', ∑ t, ∑ r, ‖ω b' t r‖ ^ 2
  rw [← hW]
  rcases hc0.lt_or_eq with hpos | hzero
  · have : 0 ≤ c * (c * ‖W‖ ^ 2 - S) := by nlinarith
    have := (mul_nonneg_iff_of_pos_left hpos).mp this
    linarith
  · rw [← hzero] at huu
    have hu0 : u = 0 := by
      have : ‖u‖ ^ 2 ≤ 0 := by simpa using huu
      have : ‖u‖ = 0 := by nlinarith [norm_nonneg u]
      exact norm_eq_zero.mp this
    rw [hu0, inner_zero_left] at huW
    have : S = 0 := by exact_mod_cast huW.symm
    rw [this, ← hzero]; simp


open QAlgorithms.Papers.Independent.Information100.P80

lemma X7_sqrt_mul_sqrt {n : Type*} [Fintype n] [DecidableEq n] {Q : Matrix n n ℂ}
    (hQ : Q.PosSemidef) : cfc Real.sqrt Q * cfc Real.sqrt Q = Q := by
  open scoped MatrixOrder in
  have hnn : (0 : Matrix n n ℂ) ≤ Q := Matrix.nonneg_iff_posSemidef.mpr hQ
  rw [← cfc_mul Real.sqrt Real.sqrt Q]
  conv_rhs => rw [← cfc_id ℝ Q]
  apply cfc_congr
  intro t ht
  exact Real.mul_self_sqrt (spectrum_nonneg_of_nonneg hnn ht)

lemma X7_qf {n : Type*} [Fintype n] (x v : n → ℂ) :
    star v ⬝ᵥ (Matrix.vecMulVec x (star x) *ᵥ v) = ((‖star v ⬝ᵥ x‖ ^ 2 : ℝ) : ℂ) := by
  push_cast
  rw [← Complex.conj_mul']
  simp only [dotProduct, Matrix.mulVec, Matrix.vecMulVec_apply, Pi.star_apply, RCLike.star_def,
    map_sum, map_mul, Complex.conj_conj, Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

lemma X7_liftBR_mul {B E R : Type*} [Fintype B] [Fintype E] [Fintype R] [DecidableEq E]
    (G G' : Matrix (B × R) (B × R) ℂ) :
    liftBR (E := E) (G * G') = liftBR (E := E) G * liftBR (E := E) G' := by
  ext ⟨b, e, r⟩ ⟨b', e', r'⟩
  simp only [liftBR, Matrix.mul_apply, Fintype.sum_prod_type]
  by_cases h : e = e'
  · subst h
    simp only [if_true, mul_one]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [Finset.sum_eq_single e]
    · simp
    · intro f _ hf; simp [Ne.symm hf]
    · simp
  · simp only [h, if_false, mul_zero]
    symm
    apply Finset.sum_eq_zero; intro c _
    apply Finset.sum_eq_zero; intro f _
    apply Finset.sum_eq_zero; intro t _
    by_cases h1 : e = f
    · subst h1; simp [h]
    · simp [h1]

lemma X7_liftBR_herm {B E R : Type*} [DecidableEq E]
    (G : Matrix (B × R) (B × R) ℂ) (hG : G.IsHermitian) :
    (liftBR (E := E) G).IsHermitian := by
  ext ⟨b, e, r⟩ ⟨b', e', r'⟩
  have := congrFun (congrFun hG (b, r)) (b', r')
  simp only [Matrix.conjTranspose_apply, RCLike.star_def] at this
  simp only [liftBR, Matrix.conjTranspose_apply, RCLike.star_def, map_mul, this]
  by_cases h : e = e' <;> simp [h, eq_comm]

lemma X7_conj_rank1 {n : Type*} [Fintype n] (H : Matrix n n ℂ) (hH : H.IsHermitian) (y : n → ℂ) :
    H * Matrix.vecMulVec y (star y) * H = Matrix.vecMulVec (H *ᵥ y) (star (H *ᵥ y)) := by
  rw [Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, Matrix.star_mulVec, hH.eq]

lemma X7_tl_add {α β : Type*} [Fintype α] (A A' : Matrix (α × β) (α × β) ℂ) :
    traceLeft (A + A') = traceLeft A + traceLeft A' := by
  ext; simp [traceLeft, Finset.sum_add_distrib]

lemma X7_tr_add {α β : Type*} [Fintype β] (A A' : Matrix (α × β) (α × β) ℂ) :
    traceRight (A + A') = traceRight A + traceRight A' := by
  ext; simp [traceRight, Finset.sum_add_distrib]

/-- rank-one case of clause 2 -/
lemma X7_c2_rank1 {B E R : Type*} [Fintype B] [Fintype E] [Fintype R]
    [DecidableEq B] [DecidableEq E] [DecidableEq R]
    (G : Matrix (B × R) (B × R) ℂ) (hG : G.IsHermitian) (y : B × (E × R) → ℂ) :
    (specNorm (traceRight (G * G)) •
        Matrix.kronecker (traceBR (Matrix.vecMulVec y (star y))) (1 : Matrix R R ℂ) -
      traceLeft (liftBR (E := E) G * Matrix.vecMulVec y (star y) * liftBR (E := E) G)).PosSemidef := by
  set c := specNorm (traceRight (G * G)) with hc
  set H := liftBR (E := E) G with hHdef
  have hH : H.IsHermitian := X7_liftBR_herm G hG
  set g : B × (E × R) → ℂ := H *ᵥ y with hg
  let gb : B → (E × R) → ℂ := fun b i => g (b, i)
  let u : B → R → R → (E × R) → ℂ := fun b t r0 i => if i.2 = r0 then y (b, (i.1, t)) else 0
  have hL : traceLeft (H * Matrix.vecMulVec y (star y) * H) =
      ∑ b, Matrix.vecMulVec (gb b) (star (gb b)) := by
    rw [X7_conj_rank1 H hH y]
    ext i j
    simp [traceLeft, Matrix.sum_apply, Matrix.vecMulVec_apply, gb, g]
  have hR : Matrix.kronecker (traceBR (Matrix.vecMulVec y (star y))) (1 : Matrix R R ℂ) =
      ∑ b, ∑ t, ∑ r0, Matrix.vecMulVec (u b t r0) (star (u b t r0)) := by
    ext ⟨e, r⟩ ⟨f, s⟩
    simp only [Matrix.kronecker, Matrix.kroneckerMap_apply, traceBR, traceRight, traceLeft,
      Matrix.of_apply, Matrix.vecMulVec_apply, Matrix.sum_apply, Matrix.one_apply, Pi.star_apply, u]
    by_cases hrs : r = s
    · subst hrs
      simp only [if_true, mul_one]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun t _ => ?_
      rw [Finset.sum_eq_single r]
      · simp
      · intro r0 _ h0; simp [Ne.symm h0]
      · simp
    · simp only [hrs, if_false, mul_zero]
      symm
      apply Finset.sum_eq_zero; intro b _
      apply Finset.sum_eq_zero; intro t _
      apply Finset.sum_eq_zero; intro r0 _
      by_cases h1 : r = r0
      · subst h1; simp [Ne.symm hrs]
      · simp [h1]
  rw [hL, hR]
  have hc0 : 0 ≤ c := by
    rw [hc]; unfold specNorm
    open scoped Matrix.Norms.L2Operator in exact norm_nonneg _
  have hP1 : (c • ∑ b, ∑ t, ∑ r0, Matrix.vecMulVec (u b t r0) (star (u b t r0))).PosSemidef :=
    Matrix.PosSemidef.smul (Matrix.posSemidef_sum _ fun b _ => Matrix.posSemidef_sum _ fun t _ =>
      Matrix.posSemidef_sum _ fun r0 _ => Matrix.posSemidef_vecMulVec_self_star _) hc0
  have hP2 : (∑ b, Matrix.vecMulVec (gb b) (star (gb b))).PosSemidef :=
    Matrix.posSemidef_sum _ fun b _ => Matrix.posSemidef_vecMulVec_self_star _
  rw [Matrix.posSemidef_iff_dotProduct_mulVec]
  refine ⟨hP1.1.sub hP2.1, fun v => ?_⟩
  rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.sum_mulVec, Matrix.sum_mulVec, dotProduct_sub,
    dotProduct_smul, dotProduct_sum, dotProduct_sum]
  simp only [Matrix.sum_mulVec, dotProduct_sum, X7_qf]
  -- key inequality
  let ω : B → R → R → ℂ := fun b t r => ∑ e, star (v (e, r)) * y (b, (e, t))
  have hω : ∀ b t r, star v ⬝ᵥ u b t r = ω b t r := by
    intro b t r
    simp only [dotProduct, Fintype.sum_prod_type, Pi.star_apply, u, ω]
    rw [Finset.sum_comm]
    rw [Finset.sum_eq_single r]
    · simp
    · intro r0 _ h0; simp [h0]
    · simp
  have hgent : ∀ b e r, g (b, (e, r)) = ∑ b', ∑ t, G (b, r) (b', t) * y (b', (e, t)) := by
    intro b e r
    simp only [hg, hHdef, Matrix.mulVec, dotProduct, Fintype.sum_prod_type, liftBR]
    refine Finset.sum_congr rfl fun b' _ => ?_
    rw [Finset.sum_eq_single e]
    · simp
    · intro f _ hf; simp [Ne.symm hf]
    · simp
  have hgb : ∀ b, star v ⬝ᵥ gb b = ∑ r, ∑ b', ∑ t, G (b, r) (b', t) * ω b' t r := by
    intro b
    simp only [dotProduct, Fintype.sum_prod_type, Pi.star_apply, gb, hgent, ω, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [X7_rot3, X7_rot3]
    refine Finset.sum_congr rfl fun b' _ => Finset.sum_congr rfl fun t _ =>
      Finset.sum_congr rfl fun e _ => ?_
    ring
  have key := X7_key G hG ω
  simp only [hω, hgb]
  have : (0 : ℝ) ≤ c * ∑ b, ∑ t, ∑ r, ‖ω b t r‖ ^ 2 - ∑ b, ‖∑ r, ∑ b', ∑ t, G (b, r) (b', t) * ω b' t r‖ ^ 2 := by
    rw [hc]; linarith
  have h2 : (c • ∑ b, ∑ t, ∑ r, (((‖ω b t r‖ ^ 2 : ℝ)) : ℂ)) -
      ∑ b, (((‖∑ r, ∑ b', ∑ t, G (b, r) (b', t) * ω b' t r‖ ^ 2 : ℝ)) : ℂ) =
      (((c * ∑ b, ∑ t, ∑ r, ‖ω b t r‖ ^ 2 - ∑ b, ‖∑ r, ∑ b', ∑ t, G (b, r) (b', t) * ω b' t r‖ ^ 2 : ℝ)) : ℂ) := by
    push_cast
    rw [Complex.real_smul]
  rw [h2]
  exact_mod_cast this


lemma X7_c2 {B E R : Type*} [Fintype B] [Fintype E] [Fintype R]
    [DecidableEq B] [DecidableEq E] [DecidableEq R]
    (Q : Matrix (B × R) (B × R) ℂ) (rho : Matrix (B × (E × R)) (B × (E × R)) ℂ)
    (hQ : Q.PosSemidef) (hrho : rho.PosSemidef) :
    OperatorLE (traceLeft (liftBR (E := E) Q * rho * liftBR (E := E) Q))
      (specNorm (traceRight Q) • Matrix.kronecker
        (traceBR (liftBR (E := E) (cfc Real.sqrt Q) * rho * liftBR (E := E) (cfc Real.sqrt Q)))
        (1 : Matrix R R ℂ)) := by
  have hGG : cfc Real.sqrt Q * cfc Real.sqrt Q = Q := X7_sqrt_mul_sqrt hQ
  have hG : (cfc Real.sqrt Q).IsHermitian := cfc_predicate Real.sqrt Q
  set G := cfc Real.sqrt Q with hGdef
  set H := liftBR (E := E) G with hHdef
  have hH : H.IsHermitian := X7_liftBR_herm G hG
  have hL : liftBR (E := E) Q = H * H := by rw [← hGG, X7_liftBR_mul]
  obtain ⟨m, w, hw⟩ := Matrix.posSemidef_iff_eq_sum_vecMulVec.mp hrho
  have hX : H * rho * H = ∑ k, Matrix.vecMulVec (H *ᵥ w k) (star (H *ᵥ w k)) := by
    rw [hw, Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun k _ => X7_conj_rank1 H hH (w k)
  have hLL : liftBR (E := E) Q * rho * liftBR (E := E) Q = H * (H * rho * H) * H := by
    rw [hL]; simp only [mul_assoc]
  unfold OperatorLE
  rw [hLL, hX]
  rw [show traceRight Q = traceRight (G * G) by rw [hGG]]
  set c := specNorm (traceRight (G * G))
  let Φ : Matrix (B × (E × R)) (B × (E × R)) ℂ →+ Matrix (E × R) (E × R) ℂ :=
    AddMonoidHom.mk' (fun X => c • Matrix.kronecker (traceBR X) (1 : Matrix R R ℂ) -
      traceLeft (H * X * H)) (by
        intro X Y
        simp only [traceBR, X7_tl_add, X7_tr_add, Matrix.kronecker, Matrix.add_kronecker, mul_add, add_mul, smul_add]
        abel)
  have hΦ : c • Matrix.kronecker (traceBR (∑ k, Matrix.vecMulVec (H *ᵥ w k) (star (H *ᵥ w k))))
      (1 : Matrix R R ℂ) - traceLeft (H * (∑ k, Matrix.vecMulVec (H *ᵥ w k) (star (H *ᵥ w k))) * H)
      = ∑ k, Φ (Matrix.vecMulVec (H *ᵥ w k) (star (H *ᵥ w k))) := by
    rw [← map_sum]; rfl
  rw [hΦ]
  exact Matrix.posSemidef_sum _ fun k _ => X7_c2_rank1 G hG (H *ᵥ w k)

lemma X7_trL_psd {A B : Type*} [Fintype A] [Fintype B] (M : Matrix (A × B) (A × B) ℂ)
    (hM : M.PosSemidef) : (QAlgorithms.traceLeft M).PosSemidef := by
  have : QAlgorithms.traceLeft M = ∑ a, M.submatrix (fun b => (a, b)) (fun b => (a, b)) := by
    ext b b'; simp [QAlgorithms.traceLeft, Matrix.sum_apply]
  rw [this]
  exact Matrix.posSemidef_sum _ fun a _ => hM.submatrix _

/-- clause 1 helper -/
def X7_F {B E : Type*} [Fintype B] (S : Matrix (B × E) (B × E) ℂ) (M : Matrix B B ℂ) :
    Matrix E E ℂ := Matrix.of fun e f => ∑ b, ∑ c, M c b * S (b, e) (c, f)

lemma X7_F_eq {B Bp E : Type*} [Fintype B] [Fintype Bp] [Fintype E] [DecidableEq E]
    (S : Matrix (B × E) (B × E) ℂ) (K : Matrix Bp B ℂ) :
    traceLeft (Matrix.kronecker K (1 : Matrix E E ℂ) * S * (Matrix.kronecker K (1 : Matrix E E ℂ))ᴴ)
      = X7_F S (Kᴴ * K) := by
  simp only [Matrix.kronecker]
  rw [Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one]
  ext e f
  simp only [traceLeft, X7_F, Matrix.of_apply, Matrix.mul_apply, Matrix.kronecker,
    Matrix.kroneckerMap_apply, Matrix.one_apply, Fintype.sum_prod_type, mul_ite, mul_one, mul_zero,
    ite_mul, zero_mul, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true,
    Finset.sum_mul, Finset.mul_sum, Matrix.conjTranspose_apply]
  rw [X7_rot3]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun b' _ => ?_
  ring

lemma X7_c1 {B Bp E : Type*} [Fintype B] [Fintype Bp] [Fintype E]
    [DecidableEq B] [DecidableEq Bp] [DecidableEq E]
    (S : Matrix (B × E) (B × E) ℂ) (K : Matrix Bp B ℂ) (hS : S.PosSemidef)
    (hK : OperatorLE (Kᴴ * K) 1) :
    OperatorLE (traceLeft (Matrix.kronecker K (1 : Matrix E E ℂ) * S *
      (Matrix.kronecker K (1 : Matrix E E ℂ))ᴴ)) (traceLeft S) := by
  unfold OperatorLE at *
  obtain ⟨m, u, hu⟩ := Matrix.posSemidef_iff_eq_sum_vecMulVec.mp hK
  have hF1 : X7_F S 1 = traceLeft S := by
    ext e f
    simp [X7_F, traceLeft, Matrix.one_apply]
  have hFsub : ∀ M1 M2 : Matrix B B ℂ, X7_F S M1 - X7_F S M2 = X7_F S (M1 - M2) := by
    intro M1 M2; ext e f
    simp [X7_F, sub_mul, Finset.sum_sub_distrib]
  have hFsum : ∀ M : Fin m → Matrix B B ℂ, X7_F S (∑ i, M i) = ∑ i, X7_F S (M i) := by
    intro M; ext e f
    simp only [X7_F, Matrix.of_apply, Matrix.sum_apply, Finset.sum_mul]
    rw [X7_rot3]
  let Rm : Fin m → Matrix Unit B ℂ := fun i => Matrix.of fun _ b => star (u i b)
  have hR : ∀ i, Matrix.vecMulVec (u i) (star (u i)) = (Rm i)ᴴ * Rm i := by
    intro i; ext c b
    simp [Rm, Matrix.mul_apply, Matrix.vecMulVec_apply]
  rw [← hF1, X7_F_eq, hFsub, hu, hFsum]
  refine Matrix.posSemidef_sum _ fun i _ => ?_
  rw [hR, ← X7_F_eq]
  exact X7_trL_psd _ (hS.mul_mul_conjTranspose_same _)

lemma X7_c3 {V : Type*} [Fintype V] (m : ℕ) (v : Fin m → EuclideanSpace ℂ V) (p : Fin m → ℝ)
    (hp : ∀ j, 0 ≤ p j) (h1 : ∑ j, p j = 1) :
    OperatorLE (pureDensity (∑ j, (p j : ℂ) • v j)) (∑ j, p j • pureDensity (v j)) := by
  unfold OperatorLE
  set w := ∑ j, (p j : ℂ) • v j with hw
  have hwa : ∀ a, w a = ∑ j, (p j : ℂ) * v j a := by
    intro a; simp [hw]
  have key : (∑ j, p j • pureDensity (v j)) - pureDensity w =
      ∑ j, p j • Matrix.vecMulVec (fun a => v j a - w a) (star (fun a => v j a - w a)) := by
    ext a b
    simp only [Matrix.sub_apply, Matrix.sum_apply, Matrix.smul_apply, pureDensity, Matrix.of_apply,
      Matrix.vecMulVec_apply, Pi.star_apply, RCLike.star_def, Complex.real_smul, map_sub]
    have hP : (∑ j, (p j : ℂ)) = 1 := by exact_mod_cast h1
    have hwb : (starRingEnd ℂ) (w b) = ∑ j, (p j : ℂ) * (starRingEnd ℂ) (v j b) := by
      rw [hwa, map_sum]; simp [Complex.conj_ofReal]
    have e1 : ∑ j, (p j : ℂ) * ((v j a - w a) * ((starRingEnd ℂ) (v j b) - (starRingEnd ℂ) (w b))) =
        ∑ j, (p j : ℂ) * (v j a * (starRingEnd ℂ) (v j b)) -
          (∑ j, (p j : ℂ) * v j a) * (starRingEnd ℂ) (w b) -
          w a * (∑ j, (p j : ℂ) * (starRingEnd ℂ) (v j b)) +
          (∑ j, (p j : ℂ)) * (w a * (starRingEnd ℂ) (w b)) := by
      simp only [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      ring
    rw [e1, ← hwa, ← hwb, hP]
    ring
  rw [key]
  exact Matrix.posSemidef_sum _ fun j _ =>
    Matrix.PosSemidef.smul (Matrix.posSemidef_vecMulVec_self_star _) (hp j)

end X7B14MB

open scoped Matrix ComplexConjugate ComplexOrder

open QAlgorithms QAlgorithms.Papers.Independent.Information100.P80 X7B14MB in
theorem solution
    {B Bprime E R V : Type*} [Fintype B] [Fintype Bprime] [Fintype E]
    [Fintype R] [Fintype V] [DecidableEq B] [DecidableEq Bprime]
    [DecidableEq E] [DecidableEq R]
    [Nonempty B] [Nonempty Bprime] [Nonempty E] [Nonempty R] [Nonempty V] :
    (∀ (S : Matrix (B × E) (B × E) ℂ) (K : Matrix Bprime B ℂ),
      S.PosSemidef → OperatorLE (Kᴴ * K) 1 →
      OperatorLE
        (traceLeft (Matrix.kronecker K (1 : Matrix E E ℂ) * S *
          (Matrix.kronecker K (1 : Matrix E E ℂ))ᴴ)) (traceLeft S)) ∧
    (∀ (Q : Matrix (B × R) (B × R) ℂ)
      (rho : Matrix (B × (E × R)) (B × (E × R)) ℂ),
      Q.PosSemidef → rho.PosSemidef →
      let L := liftBR (E := E) Q
      let H := liftBR (E := E) (cfc Real.sqrt Q)
      let tau := traceBR (H * rho * H)
      let c := specNorm (traceRight Q)
      OperatorLE (traceLeft (L * rho * L))
        (c • Matrix.kronecker tau (1 : Matrix R R ℂ))) ∧
    (∀ (m : ℕ) (v : Fin m → EuclideanSpace ℂ V) (p : Fin m → ℝ),
      (∀ j, 0 ≤ p j) → (∑ j, p j) = 1 →
      OperatorLE (pureDensity (∑ j, (p j : ℂ) • v j))
        (∑ j, p j • pureDensity (v j))) :=
  ⟨fun S K hS hK => X7_c1 S K hS hK, fun Q rho hQ hrho => X7_c2 Q rho hQ hrho,
    fun m v p hp h1 => X7_c3 m v p hp h1⟩
