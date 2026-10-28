-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Support50.P22.qkdSymmetrization
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-24T09:40:59.078282+00:00
-- url     : https://prove2.me/submissions/e1431d53-d6b1-4ad3-91d1-41e728cc6c2d

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P22
open Matrix
attribute [-instance] CStarMatrix.instHMulOfFintypeOfMulOfAddCommMonoid

namespace X5QS
open QAlgorithms

/-- permutation matrix of an equivalence -/
def pm {α : Type*} [DecidableEq α] (σ : α ≃ α) : Matrix α α ℂ :=
  Matrix.of fun x y => if y = σ x then (1 : ℂ) else 0

lemma pm_conj {α : Type*} [Fintype α] [DecidableEq α] (σ : α ≃ α) (X : Matrix α α ℂ) (x y : α) :
    (pm σ * X * (pm σ)ᴴ) x y = X (σ x) (σ y) := by
  simp only [pm, mul_apply, conjTranspose_apply, of_apply]
  simp [apply_ite, ite_mul, Finset.sum_ite_eq']

lemma pm_unitary {α : Type*} [Fintype α] [DecidableEq α] (σ : α ≃ α) :
    (pm σ)ᴴ * pm σ = 1 := by
  ext c c'
  simp only [pm, mul_apply, conjTranspose_apply, of_apply, one_apply]
  rw [Finset.sum_eq_single (σ.symm c)]
  · simp only [Equiv.apply_symm_apply, if_true, star_one, one_mul]
    by_cases h : c = c' <;> simp [h, eq_comm]
  · intro b _ hb
    have : c ≠ σ b := fun h => hb (by rw [h, Equiv.symm_apply_apply])
    simp [this]
  · simp

lemma isChannel_of_kraus {ι κ K : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [Fintype K]
    (Φ : Superop ι κ) (F : K → Matrix κ ι ℂ) (hF : ∑ k, (F k)ᴴ * F k = 1)
    (hΦ : ∀ ρ, Φ ρ = ∑ k, F k * ρ * (F k)ᴴ) : IsChannel Φ := by
  refine ⟨Fintype.card K, fun i => F ((Fintype.equivFin K).symm i), ?_, fun ρ => ?_⟩
  · unfold IsKrausFamily
    rw [← hF]
    exact (Fintype.equivFin K).symm.sum_comp (fun k => (F k)ᴴ * F k)
  · rw [hΦ ρ]; unfold krausApply
    exact ((Fintype.equivFin K).symm.sum_comp (fun k => F k * ρ * (F k)ᴴ)).symm

/-- block embedding at label p -/
def emb {R B : Type*} [DecidableEq R] [DecidableEq B] (p : R) : Matrix (R × B) B ℂ :=
  Matrix.of fun x b => if x = (p, b) then (1 : ℂ) else 0

lemma emb_conj {R B : Type*} [Fintype B] [DecidableEq R] [DecidableEq B] (p : R) (M : Matrix B B ℂ)
    (x y : R × B) :
    (emb (B := B) p * M * (emb (B := B) p)ᴴ) x y = if x.1 = p ∧ y.1 = p then M x.2 y.2 else 0 := by
  obtain ⟨x1, x2⟩ := x; obtain ⟨y1, y2⟩ := y
  simp only [emb, mul_apply, conjTranspose_apply, of_apply, Prod.mk.injEq]
  by_cases hx : x1 = p <;> by_cases hy : y1 = p <;> simp [hx, hy, apply_ite, ite_mul, Finset.sum_ite_eq']

lemma emb_iso {R B : Type*} [Fintype R] [Fintype B] [DecidableEq R] [DecidableEq B] (p : R) :
    (emb (B := B) p)ᴴ * emb (B := B) p = (1 : Matrix B B ℂ) := by
  ext b b'
  simp only [emb, mul_apply, conjTranspose_apply, of_apply, one_apply]
  rw [Finset.sum_eq_single (p, b)]
  · by_cases h : b = b' <;> simp [h, eq_comm]
  · intro x _ hx
    simp [hx]
  · simp

lemma sum_sandwich {ι α β : Type*} [Fintype ι] [Fintype α] [Fintype β] (L : Matrix α β ℂ)
    (M : ι → Matrix β β ℂ) (R : Matrix β α ℂ) :
    ∑ j, L * M j * R = L * (∑ j, M j) * R := by
  rw [Matrix.mul_sum, Matrix.sum_mul]

end X5QS

open Matrix

namespace X5QS
open QAlgorithms QAlgorithms.Papers.Independent.Support50.P22

/-- precomposition with a permutation of the copies -/
def cpe {n d : ℕ} (π : Equiv.Perm (Fin n)) : (Fin n → Fin d) ≃ (Fin n → Fin d) where
  toFun a := a ∘ π
  invFun a := a ∘ π.symm
  left_inv a := by ext; simp
  right_inv a := by ext; simp

lemma permIn_eq {n d : ℕ} [DecidableEq (Fin n → Fin d)] (π : Equiv.Perm (Fin n))
    (X : Matrix (Fin n → Fin d) (Fin n → Fin d) ℂ) :
    permuteInput π X = pm (cpe π) * X * (pm (cpe π))ᴴ := by
  ext a b; rw [pm_conj]; rfl

lemma sum_ite_and {R : Type*} [Fintype R] [DecidableEq R] (u v : R) (f : R → ℂ) :
    (∑ p, if u = p ∧ v = p then f p else 0) = if u = v then f u else 0 := by
  by_cases h : u = v
  · subst h; simp
  · rw [if_neg h]; refine Finset.sum_eq_zero fun p _ => ?_
    rw [if_neg]; rintro ⟨rfl, rfl⟩; exact h rfl

lemma emb_sandwich {α β R B : Type*} [Fintype R] [Fintype B] [DecidableEq R] [DecidableEq B]
    (p : R) (L : Matrix α B ℂ) (M : Matrix B β ℂ) :
    L * (emb (B := B) p)ᴴ * (emb (B := B) p * M) = L * M := by
  rw [Matrix.mul_assoc, ← Matrix.mul_assoc (emb (B := B) p)ᴴ, emb_iso, Matrix.one_mul]

lemma conj_emb {γ R B : Type*} [Fintype γ] [Fintype R] [Fintype B] [DecidableEq R] [DecidableEq B]
    (p : R) (M : Matrix B γ ℂ) (ρ : Matrix γ γ ℂ) :
    emb (B := B) p * M * ρ * (emb (B := B) p * M)ᴴ = emb (B := B) p * (M * ρ * Mᴴ) * (emb (B := B) p)ᴴ := by
  simp only [conjTranspose_mul, Matrix.mul_assoc]

theorem pubSym_channel {n d : ℕ} {B : Type*} [Fintype B] [DecidableEq B]
    [DecidableEq (Fin n → Fin d)] [DecidableEq (Equiv.Perm (Fin n))]
    (E : Superop (Fin n → Fin d) B) (hE : IsChannel E) : IsChannel (publicSymmetrize E) := by
  obtain ⟨m, K, hK, hEK⟩ := hE
  set c : ℂ := (((Real.sqrt (n.factorial : ℝ))⁻¹ : ℝ) : ℂ) with hc
  have hcc : star c * c = ((n.factorial : ℂ))⁻¹ := by
    rw [hc, Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul, ← mul_inv,
      Real.mul_self_sqrt (Nat.cast_nonneg _)]; push_cast; rfl
  have hcc' : c * star c = ((n.factorial : ℂ))⁻¹ := by rw [mul_comm]; exact hcc
  let G : Equiv.Perm (Fin n) × Fin m → Matrix (Equiv.Perm (Fin n) × B) (Fin n → Fin d) ℂ :=
    fun q => emb (B := B) q.1 * (c • ((K q.2 * pm (cpe q.1) : Matrix B (Fin n → Fin d) ℂ)))
  apply isChannel_of_kraus _ G
  · rw [Fintype.sum_prod_type]
    have h1 : ∀ p : Equiv.Perm (Fin n), ∑ j, (G (p, j))ᴴ * G (p, j) = ((n.factorial : ℂ))⁻¹ • 1 := by
      intro p
      have : ∀ j, (G (p, j))ᴴ * G (p, j) =
          ((n.factorial : ℂ))⁻¹ • ((pm (cpe p))ᴴ * ((K j)ᴴ * K j) * pm (cpe p)) := by
        intro j
        simp only [G]
        rw [conjTranspose_mul, emb_sandwich, conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
          hcc]
        erw [conjTranspose_mul]
        simp only [Matrix.mul_assoc]
        try rfl
      simp only [this, ← Finset.smul_sum, ← Finset.mul_sum, ← Finset.sum_mul]
      unfold IsKrausFamily at hK
      rw [hK, Matrix.mul_one, pm_unitary]
    simp only [h1, Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin]
    rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul, mul_inv_cancel₀ (by exact_mod_cast (Nat.factorial_ne_zero n)),
      one_smul]
  · intro ρ
    have h2 : ∀ p : Equiv.Perm (Fin n), ∑ j, G (p, j) * ρ * (G (p, j))ᴴ =
        emb (B := B) p * (((n.factorial : ℂ))⁻¹ • E (permuteInput p ρ)) * (emb (B := B) p)ᴴ := by
      intro p
      have : ∀ j, G (p, j) * ρ * (G (p, j))ᴴ =
          emb (B := B) p * (((n.factorial : ℂ))⁻¹ • (K j * (pm (cpe p) * ρ * (pm (cpe p))ᴴ) * (K j)ᴴ)) *
            (emb (B := B) p)ᴴ := by
        intro j
        simp only [G]
        rw [conj_emb, conjTranspose_smul]
        simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, hcc', hcc]
        erw [conjTranspose_mul]
        simp only [Matrix.mul_assoc]
        first | rfl | (congr 2; exact Matrix.mul_assoc _ _ _)
      simp only [this]
      erw [sum_sandwich]
      rw [← Finset.smul_sum, hEK, permIn_eq]; rfl
    rw [Fintype.sum_prod_type]
    simp only [h2]
    ext x y
    rw [Matrix.sum_apply]
    simp only [emb_conj]
    rw [sum_ite_and]
    unfold publicSymmetrize
    by_cases h : x.1 = y.1 <;> simp [h]

/-- the relabeling equivalence -/
def rle {n : ℕ} {B : Type*} (π : Equiv.Perm (Fin n)) : (Equiv.Perm (Fin n) × B) ≃ (Equiv.Perm (Fin n) × B) :=
  Equiv.prodCongr (Equiv.mulRight π.symm) (Equiv.refl B)

theorem relabel_channel {n : ℕ} {B : Type*} [Fintype B] [DecidableEq (Equiv.Perm (Fin n) × B)]
    (π : Equiv.Perm (Fin n)) : IsChannel (relabelPublic (B := B) π) := by
  apply isChannel_of_kraus _ (fun _ : Unit => pm (rle (B := B) π))
  · simp [pm_unitary]
  · intro ρ; ext x y
    simp only [Finset.univ_unique, Finset.sum_singleton]
    rw [pm_conj]; rfl

theorem cov1 {n d : ℕ} {B : Type*} (E : Superop (Fin n → Fin d) B) (π : Equiv.Perm (Fin n))
    (X : Matrix (Fin n → Fin d) (Fin n → Fin d) ℂ) :
    relabelPublic π (publicSymmetrize E (permuteInput π X)) = publicSymmetrize E X := by
  ext a b
  unfold relabelPublic publicSymmetrize
  have hiff : a.1 * π.symm = b.1 * π.symm ↔ a.1 = b.1 := mul_left_inj _
  have hX : permuteInput (a.1 * π.symm) (permuteInput π X) = permuteInput a.1 X := by
    ext u v
    simp only [permuteInput]
    congr 1 <;> (ext i; simp)
  by_cases h : a.1 = b.1
  · rw [if_pos (hiff.2 h), if_pos h, hX]
  · rw [if_neg (fun h' => h (hiff.1 h')), if_neg h]

theorem relabel_idT {n : ℕ} {B C : Type*} (S : Superop B C) (π : Equiv.Perm (Fin n))
    (Y : Matrix (Equiv.Perm (Fin n) × B) (Equiv.Perm (Fin n) × B) ℂ) :
    relabelPublic π (idTensorSuperop (R := Equiv.Perm (Fin n)) S Y) =
      idTensorSuperop (R := Equiv.Perm (Fin n)) S (relabelPublic π Y) := by
  ext a b; rfl

end X5QS

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder Matrix.Norms.L2Operator

open MeasureTheory

open QAlgorithms QAlgorithms.Papers.Independent.Support50.P22

attribute [local instance] Classical.decEq Classical.propDecidable

open QAlgorithms.Papers.Independent.Gap48.P20 (Copies)

open QAlgorithms.Papers.Independent.Information100.P69 (diamond)

open QAlgorithms.Papers.Independent.Dependency50.P18 (ClassicalOutput)

attribute [local instance] QAlgorithms.Papers.Independent.Support50.P22.postselectionMatrixMeasurableSpace

attribute [local instance] QAlgorithms.Papers.Independent.Support50.P22.postselectionMatrixBorelSpace

theorem solution (n d : ℕ) (hd : 0 < d)
    {L C : Type} [Fintype L] [DecidableEq L] [Nonempty L]
    [Fintype C] [DecidableEq C] [Nonempty C]
    (len : L → ℕ)
    (E : Matrix (Copies (Fin d) n) (Copies (Fin d) n) ℂ →ₗ[ℂ]
      Matrix (KeyOut L C len) (KeyOut L C len) ℂ)
    (hE : IsChannel E) (hclass : ClassicalOutput E) :
    IsChannel (publicSymmetrize E) ∧
    ∀ pi : Equiv.Perm (Fin n), IsChannel (relabelPublic (B := KeyOut L C len) pi) ∧
      (∀ X, relabelPublic pi (publicSymmetrize E (permuteInput pi X)) = publicSymmetrize E X) ∧
      (∀ X, relabelPublic pi
        (idTensorSuperop (R := Equiv.Perm (Fin n)) (keyReplacement len)
          (publicSymmetrize E (permuteInput pi X))) =
        idTensorSuperop (R := Equiv.Perm (Fin n)) (keyReplacement len)
          (publicSymmetrize E X)) := by
  refine ⟨X5QS.pubSym_channel _ hE, fun pi => ⟨X5QS.relabel_channel pi, fun X => X5QS.cov1 _ pi X, fun X => ?_⟩⟩
  rw [X5QS.relabel_idT, X5QS.cov1]

end
