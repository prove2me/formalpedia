-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Gap20.P19.fullRankPureOutput
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T19:28:10.911172+00:00
-- url     : https://prove2.me/submissions/abd37ca0-0473-4e6f-8468-6c3caa73226a

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Gap20_P19

open scoped BigOperators Matrix ComplexConjugate ComplexOrder

open Matrix

/-- Range containment for a Hermitian `Y`: if `ker Y ⊆ ker M` and `M` is Hermitian,
then every `M x` lies in the range of `Y` (via the spectral theorem). -/
lemma x8_range {I : Type} [Fintype I] [DecidableEq I] (Y M : Matrix I I ℂ) (hY : Y.IsHermitian)
    (hM : Mᴴ = M) (h : ∀ u, Y *ᵥ u = 0 → M *ᵥ u = 0) (x : I → ℂ) :
    ∃ z, Y *ᵥ z = M *ᵥ x := by
  set W : Matrix I I ℂ := (hY.eigenvectorUnitary : Matrix I I ℂ) with hWdef
  set d : I → ℂ := RCLike.ofReal ∘ hY.eigenvalues with hd
  have hs : Y = W * diagonal d * star W := by
    conv_lhs => rw [hY.spectral_theorem]
    rfl
  have hWW : star W * W = 1 := Unitary.coe_star_mul_self _
  have hWW' : W * star W = 1 := Unitary.coe_mul_star_self _
  set v := star W *ᵥ (M *ᵥ x) with hvdef
  have hv : ∀ k, d k = 0 → v k = 0 := by
    intro k hk
    have hk' : hY.eigenvalues k = 0 := by simpa [hd] using hk
    have he : Y *ᵥ ⇑(hY.eigenvectorBasis k) = 0 := by
      rw [hY.mulVec_eigenvectorBasis, hk', zero_smul]
    have hMe := h _ he
    have : v k = star ⇑(hY.eigenvectorBasis k) ⬝ᵥ (M *ᵥ x) := by
      simp only [hvdef, mulVec, dotProduct, hWdef, star_apply, Matrix.star_apply,
        IsHermitian.eigenvectorUnitary_apply, Pi.star_apply]
    rw [this, dotProduct_mulVec, ← conjTranspose_conjTranspose M, ← star_mulVec, hM, hMe,
      star_zero, zero_dotProduct]
  refine ⟨(W * diagonal (fun k => (d k)⁻¹) * star W) *ᵥ (M *ᵥ x), ?_⟩
  have hprod : (W * diagonal d * star W) * (W * diagonal (fun k => (d k)⁻¹) * star W) =
      W * diagonal (fun k => d k * (d k)⁻¹) * star W := by
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (star W) W, hWW, Matrix.one_mul, ← Matrix.mul_assoc (diagonal d),
      diagonal_mul_diagonal]
  have hdv : diagonal (fun k => d k * (d k)⁻¹) *ᵥ v = v := by
    funext k
    rw [mulVec_diagonal]
    by_cases hk : d k = 0
    · rw [hv k hk, mul_zero]
    · rw [mul_inv_cancel₀ hk, one_mul]
  rw [hs, mulVec_mulVec, hprod, ← mulVec_mulVec, ← mulVec_mulVec, ← hvdef, hdv, hvdef,
    mulVec_mulVec, hWW', one_mulVec]

/-- Kernel transfer through a Kraus map: if `Σ K P Kᴴ` kills `u` and `P ⪰ 0`, then so does
`Σ K φφᴴ Kᴴ` for every `φ = P x` in the range of `P`. -/
lemma x8_ker {B E : Type} [Fintype B] [Fintype E] {m : ℕ} (K : Fin m → Matrix E B ℂ)
    (P : Matrix B B ℂ) (hP : P.PosSemidef) (x : B → ℂ) (u : E → ℂ)
    (hu : (∑ j, K j * P * (K j)ᴴ) *ᵥ u = 0) :
    (∑ j, K j * vecMulVec (P *ᵥ x) (star (P *ᵥ x)) * (K j)ᴴ) *ᵥ u = 0 := by
  have hterm : ∀ j, star u ⬝ᵥ (K j * P * (K j)ᴴ) *ᵥ u =
      star ((K j)ᴴ *ᵥ u) ⬝ᵥ P *ᵥ ((K j)ᴴ *ᵥ u) := by
    intro j
    rw [← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec, star_mulVec,
      conjTranspose_conjTranspose]
  have h0 : ∑ j, star ((K j)ᴴ *ᵥ u) ⬝ᵥ P *ᵥ ((K j)ᴴ *ᵥ u) = 0 := by
    have := congrArg (fun w => star u ⬝ᵥ w) hu
    simp only [sum_mulVec, dotProduct_sum, dotProduct_zero, hterm] at this
    exact this
  have hz : ∀ j, P *ᵥ ((K j)ᴴ *ᵥ u) = 0 := by
    intro j
    rw [← hP.dotProduct_mulVec_zero_iff]
    exact (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => hP.dotProduct_mulVec_nonneg _)).1 h0 j
      (Finset.mem_univ _)
  rw [sum_mulVec]
  refine Finset.sum_eq_zero fun j _ => ?_
  rw [← mulVec_mulVec, ← mulVec_mulVec, vecMulVec_mulVec]
  have : star (P *ᵥ x) ⬝ᵥ ((K j)ᴴ *ᵥ u) = 0 := by
    rw [star_mulVec, ← dotProduct_mulVec, hP.1.eq, hz j, dotProduct_zero]
  rw [this]
  simp

lemma x8_pd {I : Type} (ψ : EuclideanSpace ℂ I) :
    QAlgorithms.pureDensity ψ = vecMulVec (fun i => ψ i) (star (fun i => ψ i)) := by
  ext i j
  simp [QAlgorithms.pureDensity, vecMulVec_apply]

lemma x8_tr_psd {B E : Type} [Fintype B] [Fintype E] (v : B × E → ℂ) :
    (QAlgorithms.traceRight (vecMulVec v (star v))).PosSemidef := by
  have : QAlgorithms.traceRight (vecMulVec v (star v)) =
      ∑ e, vecMulVec (fun b => v (b, e)) (star (fun b => v (b, e))) := by
    ext b b'
    simp [QAlgorithms.traceRight, vecMulVec_apply, Matrix.sum_apply]
  rw [this]
  exact posSemidef_sum _ fun e _ => posSemidef_vecMulVec_self_star _

namespace QAlgorithms.Papers.Independent.Gap20.P19

open QAlgorithms.Papers.Independent.Information100.P67
  (IsIsometry receiverChannel complementaryChannel IsDegradable IsAntidegradable)

open QAlgorithms.Papers.Independent.Information100.P50 (matrixRange)

attribute [local instance] Classical.propDecidable Classical.decEq

theorem x8_main {A B E : Type} [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B] [Fintype E] [DecidableEq E] [Nonempty E]
    (U : Matrix (B × E) A ℂ) (hU : IsIsometry U)
    (D : Superop B E) (hD : IsChannel D)
    (hdegrade : ∀ rho, D (receiverChannel U rho) = complementaryChannel U rho)
    (psi : EuclideanSpace ℂ A) (hpsi : IsState psi)
    (phi : EuclideanSpace ℂ B)
    (hphi : (fun b => phi b) ∈ matrixRange (receiverChannel U (pureDensity psi))) :
    matrixRange (D (pureDensity phi)) ≤ matrixRange (complementaryChannel U (pureDensity psi)) := by
  obtain ⟨m, K, -, hDK⟩ := hD
  set P := receiverChannel U (pureDensity psi) with hPdef
  have hP : P.PosSemidef := by
    rw [hPdef, receiverChannel, x8_pd, mul_vecMulVec, vecMulVec_mul]
    have : star (fun i => psi i) ᵥ* Uᴴ = star (U *ᵥ fun i => psi i) := by
      rw [star_mulVec]
    rw [this]
    exact x8_tr_psd _
  obtain ⟨x, hx⟩ := hphi
  rw [Matrix.toLin'_apply] at hx
  have hY : complementaryChannel U (pureDensity psi) = ∑ j, K j * P * (K j)ᴴ := by
    rw [← hdegrade, hDK]; rfl
  have hM : D (pureDensity phi) =
      ∑ j, K j * vecMulVec (P *ᵥ x) (star (P *ᵥ x)) * (K j)ᴴ := by
    rw [hDK, x8_pd, hx]; rfl
  have hYh : (∑ j, K j * P * (K j)ᴴ).IsHermitian :=
    (posSemidef_sum _ fun j _ => hP.mul_mul_conjTranspose_same (K j)).1
  have hMh : (∑ j, K j * vecMulVec (P *ᵥ x) (star (P *ᵥ x)) * (K j)ᴴ).IsHermitian :=
    (posSemidef_sum _ fun j _ =>
      (posSemidef_vecMulVec_self_star (P *ᵥ x)).mul_mul_conjTranspose_same (K j)).1
  rw [hY, hM]
  rintro w ⟨y, rfl⟩
  obtain ⟨z, hz⟩ := x8_range _ _ hYh hMh.eq (fun u hu => x8_ker K P hP x u hu) y
  exact ⟨z, by rw [Matrix.toLin'_apply, Matrix.toLin'_apply, hz]⟩

end QAlgorithms.Papers.Independent.Gap20.P19


open scoped BigOperators Matrix ComplexConjugate ComplexOrder

open Matrix

namespace QAlgorithms.Papers.Independent.Gap20.P19

open QAlgorithms.Papers.Independent.Information100.P67
  (IsIsometry receiverChannel complementaryChannel IsDegradable IsAntidegradable)

open QAlgorithms.Papers.Independent.Information100.P50 (matrixRange)

open QAlgorithms.Papers.Independent.Claimed50.P48 (MinimalDilation)

attribute [local instance] Classical.propDecidable Classical.decEq

lemma x8_swap {A R : Type} [Fintype A] [Fintype R] (w w' : R → A → ℂ) (rho : Matrix A A ℂ) :
    ∑ r, ∑ j, ∑ i, w r i * rho i j * star (w' r j) =
      ∑ i, ∑ j, rho i j * ∑ r, w r i * star (w' r j) := by
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  rw [Finset.sum_congr rfl fun j _ => Finset.sum_comm]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
    Finset.sum_congr rfl fun r _ => by ring

/-- If an environment direction `u` is orthogonal to every column slice of `U`, the environment
can be compressed by one dimension without changing the receiver channel. -/
lemma x8_compress {A B E : Type} [Fintype A] [Fintype B] [Fintype E] [Nonempty E]
    (U : Matrix (B × E) A ℂ) (u : EuclideanSpace ℂ E) (hu : u ≠ 0)
    (horth : ∀ b a, ∑ e, conj (u e) * U (b, e) a = 0) :
    ∃ W : Matrix (B × Fin (Fintype.card E - 1)) A ℂ, receiverChannel W = receiverChannel U := by
  have hcard : Module.finrank ℂ (EuclideanSpace ℂ E) = (Fintype.card E - 1) + 1 := by
    rw [finrank_euclideanSpace]; have := Fintype.card_pos (α := E); omega
  have : Fact (Module.finrank ℂ (EuclideanSpace ℂ E) = (Fintype.card E - 1) + 1) := ⟨hcard⟩
  set f := OrthonormalBasis.fromOrthogonalSpanSingleton (𝕜 := ℂ) (Fintype.card E - 1) hu
  let x : B → A → EuclideanSpace ℂ E := fun b a => WithLp.toLp 2 (fun e => U (b, e) a)
  have hx : ∀ b a, x b a ∈ (ℂ ∙ u)ᗮ := by
    intro b a
    rw [Submodule.mem_orthogonal_singleton_iff_inner_right, PiLp.inner_apply]
    simpa [x, RCLike.inner_apply, mul_comm] using horth b a
  refine ⟨Matrix.of fun p a => inner ℂ ((f p.2 : (ℂ ∙ u)ᗮ) : EuclideanSpace ℂ E) (x p.1 a), ?_⟩
  funext rho
  ext b b'
  have key : ∀ a a', ∑ r, inner ℂ ((f r : (ℂ ∙ u)ᗮ) : EuclideanSpace ℂ E) (x b a) *
      conj (inner ℂ ((f r : (ℂ ∙ u)ᗮ) : EuclideanSpace ℂ E) (x b' a')) =
      ∑ e, U (b, e) a * conj (U (b', e) a') := by
    intro a a'
    have h1 := f.sum_inner_mul_inner (⟨x b' a', hx b' a'⟩ : (ℂ ∙ u)ᗮ) ⟨x b a, hx b a⟩
    simp only [Submodule.coe_inner] at h1
    have h2 : ∀ r, inner ℂ ((f r : (ℂ ∙ u)ᗮ) : EuclideanSpace ℂ E) (x b a) *
        conj (inner ℂ ((f r : (ℂ ∙ u)ᗮ) : EuclideanSpace ℂ E) (x b' a')) =
        inner ℂ (x b' a') ((f r : (ℂ ∙ u)ᗮ) : EuclideanSpace ℂ E) *
        inner ℂ ((f r : (ℂ ∙ u)ᗮ) : EuclideanSpace ℂ E) (x b a) := by
      intro r; rw [inner_conj_symm, mul_comm]
    rw [Finset.sum_congr rfl fun r _ => h2 r, h1]
    simp only [PiLp.inner_apply, RCLike.inner_apply, x]
  simp only [receiverChannel, QAlgorithms.traceRight, of_apply, mul_apply, conjTranspose_apply,
    Finset.sum_mul]
  refine (x8_swap (fun r i => inner ℂ ((f r : (ℂ ∙ u)ᗮ) : EuclideanSpace ℂ E) (x b i))
    (fun r i => inner ℂ ((f r : (ℂ ∙ u)ᗮ) : EuclideanSpace ℂ E) (x b' i)) rho).trans
    (Eq.trans ?_ (x8_swap (fun e i => U (b, e) i) (fun e i => U (b', e) i) rho).symm)
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by
    exact congrArg (rho i j * ·) (key i j)

lemma x8_kill_vecs {E J : Type} [Fintype E] [Fintype J] (y : J → E → ℂ) (u : E → ℂ)
    (hu : (∑ k, vecMulVec (y k) (star (y k))) *ᵥ u = 0) : ∀ k, star (y k) ⬝ᵥ u = 0 := by
  have h0 : ∑ k, star u ⬝ᵥ vecMulVec (y k) (star (y k)) *ᵥ u = 0 := by
    have := congrArg (fun w => star u ⬝ᵥ w) hu
    simpa only [sum_mulVec, dotProduct_sum, dotProduct_zero] using this
  intro k
  have hk := (Finset.sum_eq_zero_iff_of_nonneg (fun k _ =>
    (posSemidef_vecMulVec_self_star (y k)).dotProduct_mulVec_nonneg u)).1 h0 k (Finset.mem_univ _)
  rw [vecMulVec_mulVec, dotProduct_smul] at hk
  simp only [MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op, smul_eq_mul] at hk
  have hc : star u ⬝ᵥ y k = star (star (y k) ⬝ᵥ u) := by
    simp only [dotProduct, star_sum, star_mul', Pi.star_apply, star_star, mul_comm]
  rw [hc] at hk
  rcases mul_eq_zero.mp hk with h | h
  · exact star_eq_zero.mp h
  · exact h

lemma x8_nc_one {A B E : Type} [Fintype A] [Fintype B] [Fintype E] [DecidableEq A]
    (U : Matrix (B × E) A ℂ) :
    complementaryChannel U 1 = ∑ p : B × A, vecMulVec (fun e => U (p.1, e) p.2)
      (star (fun e => U (p.1, e) p.2)) := by
  ext e e'
  simp [complementaryChannel, QAlgorithms.traceLeft, mul_apply, vecMulVec_apply,
    Matrix.sum_apply, Fintype.sum_prod_type]

lemma x8_full {A B E : Type} [Fintype A] [DecidableEq A] [Fintype B] [Fintype E] [Nonempty E]
    (U : Matrix (B × E) A ℂ) (hmin : MinimalDilation (receiverChannel U) U) (u : E → ℂ)
    (hu : complementaryChannel U 1 *ᵥ u = 0) : u = 0 := by
  by_contra hne
  rw [x8_nc_one] at hu
  have hk := x8_kill_vecs _ u hu
  have horth : ∀ b a, ∑ e, conj ((WithLp.toLp 2 u : EuclideanSpace ℂ E) e) * U (b, e) a = 0 := by
    intro b a
    have := congrArg conj (hk (b, a))
    simp only [dotProduct, Pi.star_apply, map_sum, map_mul, RCLike.star_def, Complex.conj_conj,
      map_zero] at this
    simpa [mul_comm] using this
  have hu0 : (WithLp.toLp 2 u : EuclideanSpace ℂ E) ≠ 0 := by
    intro h; apply hne; simpa using congrArg (WithLp.ofLp) h
  obtain ⟨W, hW⟩ := x8_compress U _ hu0 horth
  have := hmin.2 _ W hW
  have := Fintype.card_pos (α := E)
  omega

lemma x8_kill {B E J : Type} [Fintype B] [Fintype E] [Fintype J] {m : ℕ}
    (K : Fin m → Matrix E B ℂ) (P : J → Matrix B B ℂ) (hP : ∀ j, (P j).PosSemidef)
    (hspan : ∀ a : B → ℂ, (∀ j, P j *ᵥ a = 0) → a = 0) (u : E → ℂ)
    (hu : (∑ j, ∑ k, K k * P j * (K k)ᴴ) *ᵥ u = 0) : ∀ k, (K k)ᴴ *ᵥ u = 0 := by
  have hterm : ∀ j k, star u ⬝ᵥ (K k * P j * (K k)ᴴ) *ᵥ u =
      star ((K k)ᴴ *ᵥ u) ⬝ᵥ P j *ᵥ ((K k)ᴴ *ᵥ u) := by
    intro j k
    rw [← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec, star_mulVec,
      conjTranspose_conjTranspose]
  have h0 : ∑ j, ∑ k, star ((K k)ᴴ *ᵥ u) ⬝ᵥ P j *ᵥ ((K k)ᴴ *ᵥ u) = 0 := by
    have := congrArg (fun w => star u ⬝ᵥ w) hu
    simp only [sum_mulVec, dotProduct_sum, dotProduct_zero, hterm] at this
    exact this
  intro k
  apply hspan
  intro j
  have hj := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => Finset.sum_nonneg fun k _ =>
    (hP j).dotProduct_mulVec_nonneg ((K k)ᴴ *ᵥ u))).1 h0 j (Finset.mem_univ _)
  have hjk := (Finset.sum_eq_zero_iff_of_nonneg (fun k _ =>
    (hP j).dotProduct_mulVec_nonneg ((K k)ᴴ *ᵥ u))).1 hj k (Finset.mem_univ _)
  exact ((hP j).dotProduct_mulVec_zero_iff _).1 hjk

lemma x8_killed {B E : Type} [Fintype B] [Fintype E] {m : ℕ}
    (K : Fin m → Matrix E B ℂ) (u : E → ℂ) (h : ∀ k, (K k)ᴴ *ᵥ u = 0) (X : Matrix B B ℂ) :
    (∑ k, K k * X * (K k)ᴴ) *ᵥ u = 0 := by
  rw [sum_mulVec]
  exact Finset.sum_eq_zero fun k _ => by rw [← mulVec_mulVec, h k, mulVec_zero]

lemma x8_span {B J : Type} [Fintype B] [DecidableEq B] (P : J → Matrix B B ℂ)
    (hP : ∀ j, (P j).IsHermitian) (htop : (⨆ j, matrixRange (P j)) = ⊤) (a : B → ℂ)
    (ha : ∀ j, P j *ᵥ a = 0) : a = 0 := by
  have hmem : a ∈ (⨆ j, matrixRange (P j)) := htop ▸ Submodule.mem_top
  have key : ∀ w ∈ (⨆ j, matrixRange (P j)), star a ⬝ᵥ w = 0 := by
    intro w hw
    refine Submodule.iSup_induction (fun j => matrixRange (P j))
      (motive := fun w => star a ⬝ᵥ w = 0) hw ?_ (dotProduct_zero _) ?_
    · intro j w hw
      obtain ⟨x, rfl⟩ := hw
      rw [Matrix.toLin'_apply, dotProduct_mulVec, ← conjTranspose_conjTranspose (P j),
        ← star_mulVec, (hP j).eq, ha j, star_zero, zero_dotProduct]
    · intro x y hx hy
      rw [dotProduct_add, hx, hy, add_zero]
  exact dotProduct_star_self_eq_zero.mp (key a hmem)

lemma x8_sum_range {B J : Type} [Fintype B] [DecidableEq B] [Fintype J] (P : J → Matrix B B ℂ) :
    matrixRange (∑ j, P j) ≤ ⨆ j, matrixRange (P j) := by
  rintro w ⟨x, rfl⟩
  rw [Matrix.toLin'_apply, sum_mulVec]
  exact Submodule.sum_mem _ fun j _ =>
    Submodule.mem_iSup_of_mem j ⟨x, by rw [Matrix.toLin'_apply]⟩

lemma x8_rangeS {I : Type} [Fintype I] [DecidableEq I] (Y M : Matrix I I ℂ) (hY : Y.IsHermitian)
    (hM : M.IsHermitian) (h : ∀ u, Y *ᵥ u = 0 → M *ᵥ u = 0) :
    matrixRange M ≤ matrixRange Y := by
  rintro w ⟨x, rfl⟩
  obtain ⟨z, hz⟩ := x8_range Y M hY hM.eq h x
  exact ⟨z, by rw [Matrix.toLin'_apply, Matrix.toLin'_apply, hz]⟩

lemma x8_rank_eq {B E : Type} [Fintype B] [Fintype E] (v : B × E → ℂ) :
    (QAlgorithms.traceRight (vecMulVec v (star v))).rank =
      (QAlgorithms.traceLeft (vecMulVec v (star v))).rank := by
  set V : Matrix B E ℂ := Matrix.of fun b e => v (b, e)
  have h1 : QAlgorithms.traceRight (vecMulVec v (star v)) = V * Vᴴ := by
    ext b b'; simp [V, QAlgorithms.traceRight, mul_apply, vecMulVec_apply]
  have h2 : QAlgorithms.traceLeft (vecMulVec v (star v)) = Vᵀ * Vᵀᴴ := by
    ext e e'; simp [V, QAlgorithms.traceLeft, mul_apply, vecMulVec_apply]
  rw [h1, h2, rank_self_mul_conjTranspose, rank_self_mul_conjTranspose, rank_transpose]

lemma x8_kraus_psd {B E : Type} [Fintype B] [Fintype E] {m : ℕ} (K : Fin m → Matrix E B ℂ)
    (X : Matrix B B ℂ) (hX : X.PosSemidef) : (∑ k, K k * X * (K k)ᴴ).PosSemidef :=
  posSemidef_sum _ fun k _ => hX.mul_mul_conjTranspose_same (K k)

theorem x8_main2 {A B E : Type} [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B] [Fintype E] [DecidableEq E] [Nonempty E]
    (U : Matrix (B × E) A ℂ) (hU : IsDegradable U)
    (hmin : MinimalDilation (receiverChannel U) U) :
    ∀ m : ℕ, ∀ psi : Fin m → EuclideanSpace ℂ A,
      (∀ j, IsState (psi j)) →
      (∀ j, (receiverChannel U (pureDensity (psi j))).rank =
        (complementaryChannel U (pureDensity (psi j))).rank) ∧
      ((⨆ j, matrixRange (receiverChannel U (pureDensity (psi j)))) = ⊤ →
        (⨆ j, matrixRange (complementaryChannel U (pureDensity (psi j)))) = ⊤) := by
  intro n psi _
  have hform : ∀ X : Matrix A A ℂ, receiverChannel U X = QAlgorithms.traceRight (U * X * Uᴴ) ∧
      complementaryChannel U X = QAlgorithms.traceLeft (U * X * Uᴴ) := fun X => ⟨rfl, rfl⟩
  have hvv : ∀ j, U * pureDensity (psi j) * Uᴴ =
      vecMulVec (U *ᵥ fun i => psi j i) (star (U *ᵥ fun i => psi j i)) := by
    intro j
    rw [x8_pd, mul_vecMulVec, vecMulVec_mul, star_mulVec]
  have hPpsd : ∀ j, (receiverChannel U (pureDensity (psi j))).PosSemidef := by
    intro j; rw [(hform _).1, hvv]; exact x8_tr_psd _
  refine ⟨fun j => by rw [(hform _).1, (hform _).2, hvv]; exact x8_rank_eq _, fun htop => ?_⟩
  obtain ⟨-, D, ⟨m, K, -, hDK⟩, hdeg⟩ := hU
  have hDsum : ∀ X, D X = ∑ k, K k * X * (K k)ᴴ := fun X => hDK X
  have hNc : ∀ X, complementaryChannel U X = ∑ k, K k * receiverChannel U X * (K k)ᴴ := by
    intro X; rw [hdeg, hDsum]
  -- Nc(1) has full range
  have hN1psd : (receiverChannel U 1).PosSemidef := by
    rw [(hform _).1, Matrix.mul_one]
    have : U * Uᴴ = ∑ a, vecMulVec (fun p => U p a) (star fun p => U p a) := by
      ext p q; simp [mul_apply, vecMulVec_apply, Matrix.sum_apply]
    rw [this]
    have hlin : QAlgorithms.traceRight (∑ a, vecMulVec (fun p => U p a) (star fun p => U p a)) =
        ∑ a, QAlgorithms.traceRight (vecMulVec (fun p => U p a) (star fun p => U p a)) := by
      ext b b'; simp [QAlgorithms.traceRight, Matrix.sum_apply, Finset.sum_comm (γ := A)]
    rw [hlin]
    exact posSemidef_sum _ fun a _ => x8_tr_psd _
  have hD1 : ∀ u, (∑ k, K k * (1 : Matrix B B ℂ) * (K k)ᴴ) *ᵥ u = 0 → ∀ k, (K k)ᴴ *ᵥ u = 0 := by
    intro u hu
    refine x8_kill K (fun _ : Unit => (1 : Matrix B B ℂ)) (fun _ => PosSemidef.one)
      (fun a ha => by simpa using ha ()) u ?_
    simpa using hu
  have step1 : (⊤ : Submodule ℂ (E → ℂ)) ≤ matrixRange (complementaryChannel U 1) := by
    have := x8_rangeS (complementaryChannel U 1) 1
      (by rw [x8_nc_one]; exact (posSemidef_sum _ fun p _ =>
        posSemidef_vecMulVec_self_star _).1) isHermitian_one
      (fun u hu => by rw [x8_full U hmin u hu, mulVec_zero])
    simpa [matrixRange, Matrix.toLin'_one] using this
  have step2 : matrixRange (complementaryChannel U 1) ≤
      matrixRange (∑ k, K k * (1 : Matrix B B ℂ) * (K k)ᴴ) := by
    apply x8_rangeS
    · exact (x8_kraus_psd K 1 PosSemidef.one).1
    · rw [hNc]; exact (x8_kraus_psd K _ hN1psd).1
    · intro u hu; rw [hNc]; exact x8_killed K u (hD1 u hu) _
  have step3 : matrixRange (∑ k, K k * (1 : Matrix B B ℂ) * (K k)ᴴ) ≤
      matrixRange (∑ j, complementaryChannel U (pureDensity (psi j))) := by
    apply x8_rangeS
    · exact (posSemidef_sum _ fun j _ => by rw [hNc]; exact x8_kraus_psd K _ (hPpsd j)).1
    · exact (x8_kraus_psd K 1 PosSemidef.one).1
    · intro u hu
      simp only [hNc] at hu
      exact x8_killed K u (x8_kill K _ hPpsd
        (x8_span _ (fun j => (hPpsd j).1) htop) u hu) _
  exact top_le_iff.mp (step1.trans (step2.trans (step3.trans (x8_sum_range _))))

end QAlgorithms.Papers.Independent.Gap20.P19


open scoped BigOperators Matrix ComplexConjugate ComplexOrder

open Matrix

namespace QAlgorithms.Papers.Independent.Gap20.P19

open QAlgorithms.Papers.Independent.Information100.P67
  (IsIsometry receiverChannel complementaryChannel IsDegradable IsAntidegradable)

open QAlgorithms.Papers.Independent.Information100.P50 (matrixRange)

open QAlgorithms.Papers.Independent.Claimed50.P48 (MinimalDilation)

attribute [local instance] Classical.propDecidable Classical.decEq

lemma x8_rank_top {I : Type} [Fintype I] [DecidableEq I] (M : Matrix I I ℂ) :
    M.rank = Fintype.card I ↔ matrixRange M = ⊤ := by
  have hr : M.rank = Module.finrank ℂ (matrixRange M) := rfl
  constructor
  · intro h
    apply Submodule.eq_top_of_finrank_eq
    rw [← hr, h, Module.finrank_fintype_fun_eq_card]
  · intro h
    rw [hr, h, finrank_top, Module.finrank_fintype_fun_eq_card]

theorem x8_main3 {A B E : Type} [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B] [Fintype E] [DecidableEq E] [Nonempty E]
    (U : Matrix (B × E) A ℂ) (hU : IsDegradable U)
    (hmin : MinimalDilation (receiverChannel U) U)
    (hfull : ∃ psi : EuclideanSpace ℂ A, IsState psi ∧
      (receiverChannel U (pureDensity psi)).rank = Fintype.card B) :
    Fintype.card E = Fintype.card B := by
  obtain ⟨psi, hpsi, hrank⟩ := hfull
  obtain ⟨h1, h2⟩ := x8_main2 U hU hmin 1 (fun _ => psi) (fun _ => hpsi)
  have htop : matrixRange (receiverChannel U (pureDensity psi)) = ⊤ := (x8_rank_top _).1 hrank
  have hc := h2 (by simpa using htop)
  have hEtop : matrixRange (complementaryChannel U (pureDensity psi)) = ⊤ := by simpa using hc
  rw [← (x8_rank_top _).2 hEtop, ← h1 0, hrank]

end QAlgorithms.Papers.Independent.Gap20.P19



open scoped BigOperators Matrix ComplexConjugate ComplexOrder Kronecker

open Filter Topology

open QAlgorithms.Papers.Independent.Information100.P67
  (IsIsometry receiverChannel complementaryChannel IsDegradable IsAntidegradable
   maximumCoherentInformation dilationPower)

open QAlgorithms.Papers.Independent.Claimed50.P48
  (MinimalDilation indexedKrausDilation arbitraryVectorComplement superopTensor tensorDilation)

open QAlgorithms.Papers.Independent.Claimed50.P24 (ChannelEB)

open QAlgorithms.Papers.Independent.Information100.P60 (wernerHolevo)

open QAlgorithms.Papers.Independent.Gap48.P36 (finWeyl WeylLabel)

open QAlgorithms.Papers.Independent.Information100.P69 (choi)

open QAlgorithms.Papers.Independent.Information100.P50 (matrixRange)

open QAlgorithms.Papers.Independent.Information100.P08 (IsPure)

attribute [local instance] Classical.propDecidable Classical.decEq

variable {A B C E F R K A2 B2 E2 : Type}

variable [Fintype A] [DecidableEq A] [Nonempty A]

variable [Fintype B] [DecidableEq B] [Nonempty B]

variable [Fintype C] [DecidableEq C] [Nonempty C]

variable [Fintype E] [DecidableEq E] [Nonempty E]

variable [Fintype F] [DecidableEq F] [Nonempty F]

variable [Fintype R] [DecidableEq R] [Nonempty R]

variable [Fintype K] [DecidableEq K]

variable [Fintype A2] [DecidableEq A2] [Nonempty A2]

variable [Fintype B2] [DecidableEq B2] [Nonempty B2]

variable [Fintype E2] [DecidableEq E2] [Nonempty E2]

open QAlgorithms QAlgorithms.Papers.Independent.Gap20.P19 in
/-- Theorem 3, PDF p.9. Printed rank Phi(rho)=d_B is corrected to rank rho=d_B,
as required by rho=Phi(|psi><psi|) and the m=1 proof using Lemma 2. -/
theorem solution [Nonempty A] [Nonempty B] [Nonempty E]
    (U : Matrix (B × E) A ℂ) (hU : IsDegradable U)
    (hmin : MinimalDilation (receiverChannel U) U)
    (hfull : ∃ psi : EuclideanSpace ℂ A, IsState psi ∧
      (receiverChannel U (pureDensity psi)).rank = Fintype.card B) :
    Fintype.card E = Fintype.card B :=
  x8_main3 U hU hmin hfull



