-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Information100.P44.directionalLadderAlignment
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T07:30:18.147497+00:00
-- url     : https://prove2.me/submissions/1d113906-6477-411f-8e14-69099ec9a8ed

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P44

namespace QAlgorithms.Papers.Independent.Information100.P44

noncomputable section

open scoped ComplexConjugate ComplexOrder Matrix

attribute [local instance] Classical.propDecidable

lemma X7_perp_span {g : ℕ} (u w : Fin g → ℂ) (hu : u ≠ 0)
    (h : ∀ x : Fin g → ℂ, star u ⬝ᵥ x = 0 → star w ⬝ᵥ x = 0) : ∃ α : ℂ, w = α • u := by
  have huu : star u ⬝ᵥ u ≠ 0 := by
    intro h0; exact hu (dotProduct_star_self_eq_zero.mp h0)
  set α := (star u ⬝ᵥ w) / (star u ⬝ᵥ u)
  set x := w - α • u with hx
  have h1 : star u ⬝ᵥ x = 0 := by
    rw [hx, dotProduct_sub, dotProduct_smul, smul_eq_mul]
    simp only [α]; field_simp; ring
  have h2 := h x h1
  have h3 : star x ⬝ᵥ x = 0 := by
    have : star x ⬝ᵥ x = star w ⬝ᵥ x - star α * (star u ⬝ᵥ x) := by
      rw [hx, star_sub, sub_dotProduct, star_smul, smul_dotProduct, smul_eq_mul]
    rw [this, h1, h2]; ring
  refine ⟨α, ?_⟩
  have := dotProduct_star_self_eq_zero.mp h3
  rw [hx, sub_eq_zero] at this
  exact this

lemma X7_psd_kernel {ι : Type*} [Fintype ι] {M : Matrix ι ι ℂ} (hM : M.PosSemidef) (w : ι → ℂ)
    (h : star w ⬝ᵥ M *ᵥ w = 0) : M *ᵥ w = 0 :=
  (hM.dotProduct_mulVec_zero_iff w).mp h

section
variable {g : ℕ} (A B F : Mat g) (D E : Fin g → ℂ) (c : ℂ)

lemma X7_w1 (x : Fin g → ℂ) :
    (∀ i, (ladderGram A B F D E c *ᵥ Sum.elim x 0) (Sum.inl i) = (A *ᵥ x) i) ∧
    (∀ j, (ladderGram A B F D E c *ᵥ Sum.elim x 0) (Sum.inr (Sum.inl j)) = star (fun k => F k j) ⬝ᵥ x) ∧
    ((ladderGram A B F D E c *ᵥ Sum.elim x 0) (Sum.inr (Sum.inr 0)) = star D ⬝ᵥ x) := by
  refine ⟨fun i => ?_, fun j => ?_, ?_⟩ <;>
    simp [ladderGram, Matrix.mulVec, dotProduct, Fintype.sum_sum_type, augment, Matrix.fromBlocks,
      Matrix.conjTranspose_apply]

lemma X7_w2 (y : Fin g → ℂ) :
    (∀ i, (ladderGram A B F D E c *ᵥ Sum.elim 0 (Sum.elim y 0)) (Sum.inl i) =
        star (fun k => conj (F i k)) ⬝ᵥ y) ∧
    (∀ j, (ladderGram A B F D E c *ᵥ Sum.elim 0 (Sum.elim y 0)) (Sum.inr (Sum.inl j)) = (B *ᵥ y) j) ∧
    ((ladderGram A B F D E c *ᵥ Sum.elim 0 (Sum.elim y 0)) (Sum.inr (Sum.inr 0)) = star E ⬝ᵥ y) := by
  refine ⟨fun i => ?_, fun j => ?_, ?_⟩ <;>
    simp [ladderGram, Matrix.mulVec, dotProduct, Fintype.sum_sum_type, augment, Matrix.fromBlocks,
      Matrix.conjTranspose_apply] <;> rfl

end

lemma X7_ladder_main {g : ℕ} (A B F : Mat g)
    (D E u v : Fin g → ℂ) (c : ℂ) (hu : u ≠ 0) (hv : v ≠ 0)
    (hA : A = pureDensity (WithLp.toLp 2 u))
    (hB : B = pureDensity (WithLp.toLp 2 v))
    (hpos : (ladderGram A B F D E c).PosSemidef) :
    (∃ alpha beta lambda : ℂ, D = alpha • u ∧ E = beta • v ∧
      F = lambda • Matrix.vecMulVec u (fun i => conj (v i))) ∧
    (∃ alpha : ℂ, D = alpha • u) ∧ (∃ beta : ℂ, E = beta • v) ∧
    Set.range F.mulVec ⊆ {x | ∃ alpha : ℂ, x = alpha • u} ∧
    Set.range (Fᴴ).mulVec ⊆ {x | ∃ beta : ℂ, x = beta • v} := by
  have hAx : ∀ x, star u ⬝ᵥ x = 0 → A *ᵥ x = 0 := by
    intro x hx
    ext i
    have hx' : ∑ j, conj (u j) * x j = 0 := by simpa [dotProduct] using hx
    rw [hA]
    simp only [Matrix.mulVec, dotProduct, pureDensity, Matrix.of_apply, PiLp.toLp_apply,
      Pi.zero_apply]
    simp_rw [mul_assoc, ← Finset.mul_sum, hx', mul_zero]
  have hBy : ∀ y, star v ⬝ᵥ y = 0 → B *ᵥ y = 0 := by
    intro y hy
    ext i
    have hy' : ∑ j, conj (v j) * y j = 0 := by simpa [dotProduct] using hy
    rw [hB]
    simp only [Matrix.mulVec, dotProduct, pureDensity, Matrix.of_apply, PiLp.toLp_apply,
      Pi.zero_apply]
    simp_rw [mul_assoc, ← Finset.mul_sum, hy', mul_zero]
  have qA : ∀ x, star u ⬝ᵥ x = 0 → ladderGram A B F D E c *ᵥ Sum.elim x 0 = 0 := by
    intro x hx
    apply X7_psd_kernel hpos
    have h1 := (X7_w1 A B F D E c x).1
    rw [dotProduct, Fintype.sum_sum_type]
    simp only [Pi.star_apply, Sum.elim_inl, Sum.elim_inr, Pi.zero_apply, star_zero, zero_mul,
      Finset.sum_const_zero, add_zero, h1, hAx x hx, mul_zero, Finset.sum_const_zero]
  have qB : ∀ y, star v ⬝ᵥ y = 0 → ladderGram A B F D E c *ᵥ Sum.elim 0 (Sum.elim y 0) = 0 := by
    intro y hy
    apply X7_psd_kernel hpos
    have h1 := (X7_w2 A B F D E c y).2.1
    rw [dotProduct, Fintype.sum_sum_type, Fintype.sum_sum_type]
    simp only [Pi.star_apply, Sum.elim_inl, Sum.elim_inr, Pi.zero_apply, star_zero, zero_mul,
      Finset.sum_const_zero, add_zero, zero_add, h1, hBy y hy, mul_zero]
  obtain ⟨alpha, hD⟩ := X7_perp_span u D hu fun x hx => by
    have := congrFun (qA x hx) (Sum.inr (Sum.inr 0))
    rwa [(X7_w1 A B F D E c x).2.2] at this
  obtain ⟨beta, hE⟩ := X7_perp_span v E hv fun y hy => by
    have := congrFun (qB y hy) (Sum.inr (Sum.inr 0))
    rwa [(X7_w2 A B F D E c y).2.2] at this
  have hcol : ∀ j, ∃ γ : ℂ, (fun k => F k j) = γ • u := fun j =>
    X7_perp_span u _ hu fun x hx => by
      have := congrFun (qA x hx) (Sum.inr (Sum.inl j))
      rwa [(X7_w1 A B F D E c x).2.1] at this
  have hrow : ∀ i, ∃ δ : ℂ, (fun k => conj (F i k)) = δ • v := fun i =>
    X7_perp_span v _ hv fun y hy => by
      have := congrFun (qB y hy) (Sum.inl i)
      rwa [(X7_w2 A B F D E c y).1] at this
  choose γ hγ using hcol
  choose δ hδ using hrow
  have hFc : ∀ i k, F i k = γ k * u i := fun i k => by
    have := congrFun (hγ k) i; simpa using this
  have hFr : ∀ i k, F i k = conj (δ i) * conj (v k) := fun i k => by
    have := congrArg conj (congrFun (hδ i) k); simpa using this
  obtain ⟨i0, hi0⟩ : ∃ i0, u i0 ≠ 0 := by
    by_contra h; push_neg at h; exact hu (funext h)
  set lam := conj (δ i0) / u i0 with hlam
  have hF : F = lam • Matrix.vecMulVec u (fun i => conj (v i)) := by
    ext i k
    have h1 := hFc i k
    have h2 := hFc i0 k
    rw [hFr i0 k] at h2
    simp only [Matrix.smul_apply, Matrix.vecMulVec_apply, smul_eq_mul, hlam]
    rw [h1]
    have : γ k = conj (δ i0) * conj (v k) / u i0 := by
      field_simp; rw [← h2]
    rw [this]; field_simp
  refine ⟨⟨alpha, beta, lam, hD, hE, hF⟩, ⟨alpha, hD⟩, ⟨beta, hE⟩, ?_, ?_⟩
  · rintro x ⟨y, rfl⟩
    refine ⟨lam * ∑ k, conj (v k) * y k, ?_⟩
    ext i
    rw [hF]
    simp only [Matrix.mulVec, dotProduct, Matrix.smul_apply, Matrix.vecMulVec_apply, smul_eq_mul,
      Pi.smul_apply, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  · rintro x ⟨y, rfl⟩
    refine ⟨conj lam * ∑ k, conj (u k) * y k, ?_⟩
    ext i
    rw [hF]
    simp only [Matrix.mulVec, dotProduct, Matrix.conjTranspose_apply, Matrix.smul_apply,
      Matrix.vecMulVec_apply, smul_eq_mul, Pi.smul_apply, Finset.mul_sum, Finset.sum_mul,
      star_mul', RCLike.star_def, Complex.conj_conj]
    refine Finset.sum_congr rfl fun k _ => ?_
    ring

end

end QAlgorithms.Papers.Independent.Information100.P44

noncomputable section

open scoped ComplexConjugate ComplexOrder Matrix

attribute [local instance] Classical.propDecidable

open QAlgorithms QAlgorithms.Papers.Independent.Information100.P44 in
theorem solution {g : ℕ} (hg : 2 ≤ g) (A B F : Mat g)
    (D E u v : Fin g → ℂ) (c : ℝ) (hc : 0 ≤ c) (hu : u ≠ 0) (hv : v ≠ 0)
    (hA : A = pureDensity (WithLp.toLp 2 u))
    (hB : B = pureDensity (WithLp.toLp 2 v))
    (hpos : (ladderGram A B F D E (c : ℂ)).PosSemidef) :
    (∃ alpha beta lambda : ℂ, D = alpha • u ∧ E = beta • v ∧
      F = lambda • Matrix.vecMulVec u (fun i => conj (v i))) ∧
    (∃ alpha : ℂ, D = alpha • u) ∧ (∃ beta : ℂ, E = beta • v) ∧
    Set.range F.mulVec ⊆ {x | ∃ alpha : ℂ, x = alpha • u} ∧
    Set.range (Fᴴ).mulVec ⊆ {x | ∃ beta : ℂ, x = beta • v} :=
  X7_ladder_main A B F D E u v (c : ℂ) hu hv hA hB hpos

end
