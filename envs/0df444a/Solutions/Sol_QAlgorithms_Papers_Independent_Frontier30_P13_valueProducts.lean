-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Frontier30.P13.valueProducts
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T13:09:48.081816+00:00
-- url     : https://prove2.me/submissions/8d5a7f99-0344-4902-8b70-18fb4cc2909b

import Definitions.Def_QAlgorithms_Papers_Independent_Frontier30_P13

noncomputable section

open Filter

open QAlgorithms.Papers.Independent.Dependency50.P10 (complexify physicalCovariance)

open scoped ComplexOrder

attribute [local instance] Classical.decEq

attribute [local instance] Classical.propDecidable

namespace QAlgorithms.Papers.Independent.Frontier30.P13

open Matrix

theorem x8_fb_psd {α β 𝕜 : Type*} [RCLike 𝕜] [Fintype α] [Fintype β] {A : Matrix α α 𝕜}
    {B : Matrix β β 𝕜} (hA : A.PosSemidef) (hB : B.PosSemidef) : (fromBlocks A 0 0 B).PosSemidef := by
  rw [posSemidef_iff_dotProduct_mulVec] at hA hB ⊢
  refine ⟨?_, fun x => ?_⟩
  · rw [IsHermitian, fromBlocks_conjTranspose, hA.1.eq, hB.1.eq]; simp
  · rw [fromBlocks_mulVec]
    have h1 := hA.2 (x ∘ Sum.inl)
    have h2 := hB.2 (x ∘ Sum.inr)
    simp only [zero_mulVec, add_zero, zero_add] at *
    simp only [dotProduct, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, Pi.star_apply] at *
    exact add_nonneg h1 h2

theorem x8_bd_psd {ι 𝕜 : Type*} [RCLike 𝕜] [Fintype ι] {n : ι → Type*} [∀ i, Fintype (n i)]
    (M : ∀ i, Matrix (n i) (n i) 𝕜) (h : ∀ i, (M i).PosSemidef) :
    (blockDiagonal' M).PosSemidef := by
  rw [posSemidef_iff_dotProduct_mulVec]
  refine ⟨?_, fun x => ?_⟩
  · rw [IsHermitian, blockDiagonal'_conjTranspose]
    congr 1; funext i; exact (h i).1.eq
  · have hmv : ∀ k i, (blockDiagonal' M *ᵥ x) ⟨k, i⟩ = (M k *ᵥ fun j => x ⟨k, j⟩) i := by
      intro k i
      simp only [mulVec, dotProduct, Fintype.sum_sigma]
      rw [Finset.sum_eq_single k]
      · simp [blockDiagonal'_apply_eq]
      · intro k' _ hk
        simp [blockDiagonal'_apply_ne _ _ _ (Ne.symm hk)]
      · simp
    have : star x ⬝ᵥ (blockDiagonal' M *ᵥ x) =
        ∑ k, star (fun j => x ⟨k, j⟩) ⬝ᵥ (M k *ᵥ fun j => x ⟨k, j⟩) := by
      simp only [dotProduct, Fintype.sum_sigma, hmv, Pi.star_apply]
    rw [this]
    exact Finset.sum_nonneg fun k _ => (h k).dotProduct_mulVec_nonneg _

theorem x8_phys_psd {n : Type*} [Fintype n] {G J : Matrix n n ℝ} (h : physicalCovariance G J) :
    G.PosSemidef := by
  obtain ⟨hT, hP⟩ := h
  rw [posSemidef_iff_dotProduct_mulVec]
  refine ⟨?_, fun x => ?_⟩
  · rw [IsHermitian, conjTranspose_eq_transpose_of_trivial, hT]
  · have := hP.dotProduct_mulVec_nonneg (fun i => (x i : ℂ))
    have hre := (Complex.nonneg_iff.1 this).1
    refine le_of_le_of_eq hre ?_
    simp [dotProduct, mulVec, complexify, Complex.re_sum, Finset.mul_sum, sub_mul, mul_sub]

theorem x8_psd_of_eq {n R : Type*} [Ring R] [PartialOrder R] [StarRing R] {M N : Matrix n n R}
    (h : M.PosSemidef) (e : M = N) : N.PosSemidef := e ▸ h

theorem x8_V_nonneg {A B : Type*} [Fintype A] [Fintype B]
    (G : Matrix (BipPhase A B) (BipPhase A B) ℝ) : 0 ≤ valueV G :=
  Real.sSup_nonneg fun _ hp => hp.1

theorem x8_bdd {A B : Type*} [Fintype A] [Fintype B]
    (G : Matrix (BipPhase A B) (BipPhase A B) ℝ) : BddAbove {p | feasibleScale G p} :=
  ⟨1, fun _ hp => hp.2.1⟩

theorem x8_down {A B : Type*} [Fintype A] [Fintype B]
    {G : Matrix (BipPhase A B) (BipPhase A B) ℝ} {p q : ℝ} (hp : feasibleScale G p)
    (hq : 0 ≤ q) (hqp : q ≤ p) : feasibleScale G q := by
  obtain ⟨-, hp1, GA, GB, hA, hB, hD⟩ := hp
  refine ⟨hq, hqp.trans hp1, GA, GB, hA, hB, ?_⟩
  have hF := x8_fb_psd (x8_phys_psd hA) (x8_phys_psd hB)
  have := hD.add (hF.smul (sub_nonneg.2 hqp))
  convert this using 1
  rw [sub_smul]; abel

theorem x8_of_lt {A B : Type*} [Fintype A] [Fintype B]
    {G : Matrix (BipPhase A B) (BipPhase A B) ℝ} {q : ℝ} (hq : 0 ≤ q) (hlt : q < valueV G) :
    feasibleScale G q := by
  have hne : {p | feasibleScale G p}.Nonempty := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty] at h
    unfold valueV at hlt; rw [h, Real.sSup_empty] at hlt; linarith
  obtain ⟨p, hp, hqp⟩ := exists_lt_of_lt_csSup hne hlt
  exact x8_down hp hq hqp.le

section fam
variable {K : Type*} [Fintype K] (a b : K → ℕ)

/-- restriction of a feasible witness of the family to block `l` -/
theorem x8_restrict
    (G : ∀ k, Matrix (BipPhase (Fin (a k)) (Fin (b k))) (BipPhase (Fin (a k)) (Fin (b k))) ℝ)
    (l : K) {p : ℝ} (hp : feasibleScale (familyCM a b G) p) : feasibleScale (G l) p := by
  obtain ⟨hp0, hp1, GA, GB, hA, hB, hD⟩ := hp
  let fA : ModeQuadrature (Fin (a l)) → ModeQuadrature (Σ k, Fin (a k)) := fun u => (⟨l, u.1⟩, u.2)
  let fB : ModeQuadrature (Fin (b l)) → ModeQuadrature (Σ k, Fin (b k)) := fun u => (⟨l, u.1⟩, u.2)
  have hJ : ∀ (c : K → ℕ) (f : ModeQuadrature (Fin (c l)) → ModeQuadrature (Σ k, Fin (c k))),
      f = (fun u => (⟨l, u.1⟩, u.2)) →
      (phaseJ (Σ k, Fin (c k))).submatrix f f = phaseJ (Fin (c l)) := by
    intro c f hf; subst hf
    ext u v
    simp [phaseJ, Sigma.mk.injEq]
  have hphys : ∀ (c : K → ℕ) (f : ModeQuadrature (Fin (c l)) → ModeQuadrature (Σ k, Fin (c k)))
      (H : Matrix (ModeQuadrature (Σ k, Fin (c k))) (ModeQuadrature (Σ k, Fin (c k))) ℝ),
      f = (fun u => (⟨l, u.1⟩, u.2)) → physicalCovariance H (phaseJ _) →
      physicalCovariance (H.submatrix f f) (phaseJ _) := by
    intro c f H hf hH
    refine ⟨by rw [transpose_submatrix, hH.1], ?_⟩
    rw [← hJ c f hf]
    have := hH.2.submatrix f
    convert this using 1
    ext u v; simp [complexify]
  refine ⟨hp0, hp1, GA.submatrix fA fA, GB.submatrix fB fB, hphys a fA GA rfl hA,
    hphys b fB GB rfl hB, ?_⟩
  have := hD.submatrix (Sum.map fA fB)
  convert this using 1
  ext i j
  rcases i with ⟨i1, i2⟩ | ⟨i1, i2⟩ <;> rcases j with ⟨j1, j2⟩ | ⟨j1, j2⟩ <;>
    simp [familyCM, familyIndex, fA, fB]

/-- gluing block witnesses -/
theorem x8_glue
    (G : ∀ k, Matrix (BipPhase (Fin (a k)) (Fin (b k))) (BipPhase (Fin (a k)) (Fin (b k))) ℝ)
    {q : ℝ} (hq0 : 0 ≤ q ∧ q ≤ 1) (hq : ∀ k, feasibleScale (G k) q) :
    feasibleScale (familyCM a b G) q := by
  choose GAk GBk hAk hBk hDk using fun k => (hq k).2.2
  have hglue : ∀ (c : K → ℕ)
      (H : ∀ k, Matrix (ModeQuadrature (Fin (c k))) (ModeQuadrature (Fin (c k))) ℝ),
      (∀ k, physicalCovariance (H k) (phaseJ _)) →
      physicalCovariance ((blockDiagonal' H).submatrix
        (fun u : ModeQuadrature (Σ k, Fin (c k)) =>
          (⟨u.1.1, (u.1.2, u.2)⟩ : Σ k, ModeQuadrature (Fin (c k))))
        (fun u => ⟨u.1.1, (u.1.2, u.2)⟩)) (phaseJ (Σ k, Fin (c k))) := by
    intro c H hH
    refine ⟨?_, ?_⟩
    · rw [transpose_submatrix, blockDiagonal'_transpose]
      have : (fun k => (H k)ᵀ) = H := funext fun k => (hH k).1
      rw [this]
    · refine x8_psd_of_eq ((x8_bd_psd _ fun k => (hH k).2).submatrix
        (fun u : ModeQuadrature (Σ k, Fin (c k)) =>
          (⟨u.1.1, (u.1.2, u.2)⟩ : Σ k, ModeQuadrature (Fin (c k))))) ?_
      ext ⟨⟨k, j⟩, q⟩ ⟨⟨k', j'⟩, q'⟩
      by_cases h : k = k'
      · subst h; simp [blockDiagonal'_apply_eq, phaseJ, complexify]
      · simp [blockDiagonal'_apply_ne _ _ _ h, phaseJ, complexify, h]
  refine ⟨hq0.1, hq0.2, _, _, hglue a GAk hAk, hglue b GBk hBk, ?_⟩
  refine x8_psd_of_eq ((x8_bd_psd _ hDk).submatrix (familyIndex a b)) ?_
  ext i j
  rcases i with ⟨⟨k, i1⟩, i2⟩ | ⟨⟨k, i1⟩, i2⟩ <;> rcases j with ⟨⟨k', j1⟩, j2⟩ | ⟨⟨k', j1⟩, j2⟩
  all_goals
    by_cases h : k = k'
    · subst h; simp [familyCM, familyIndex, blockDiagonal'_apply_eq]
    · simp [familyCM, familyIndex, blockDiagonal'_apply_ne _ _ _ h, h]
end fam

theorem x8_main {K : Type*} [Fintype K] [Nonempty K]
    (a b : K → ℕ)
    (G : ∀ k, Matrix (BipPhase (Fin (a k)) (Fin (b k)))
      (BipPhase (Fin (a k)) (Fin (b k))) ℝ) :
    ∃ k : K, valueV (familyCM a b G) = valueV (G k) ∧
      ∀ l : K, valueV (G k) ≤ valueV (G l) := by
  obtain ⟨k0, hk0⟩ := Finite.exists_min (fun k => valueV (G k))
  refine ⟨k0, le_antisymm ?_ ?_, hk0⟩
  · by_cases hne : {p | feasibleScale (familyCM a b G) p}.Nonempty
    · exact csSup_le_csSup (x8_bdd _) hne fun p hp => x8_restrict a b G k0 hp
    · rw [Set.not_nonempty_iff_eq_empty] at hne
      unfold valueV; rw [hne, Real.sSup_empty]
      exact x8_V_nonneg _
  · by_contra hlt'
    have hlt := not_le.1 hlt'
    have h0 := x8_V_nonneg (familyCM a b G)
    set q := (valueV (familyCM a b G) + valueV (G k0)) / 2 with hqd
    have hq : feasibleScale (familyCM a b G) q := by
      refine x8_glue a b G ⟨by linarith, ?_⟩ fun k => x8_of_lt (by linarith) ?_
      · have := x8_of_lt (G := G k0) (q := q) (by linarith) (by linarith)
        exact this.2.1
      · linarith [hk0 k]
    have := le_csSup (x8_bdd _) hq
    change q ≤ valueV (familyCM a b G) at this
    linarith

end QAlgorithms.Papers.Independent.Frontier30.P13

open QAlgorithms.Papers.Independent.Frontier30.P13 in
theorem solution {K : Type*} [Fintype K] [Nonempty K]
    (a b : K → ℕ) (ha : ∀ k, 0 < a k) (hb : ∀ k, 0 < b k)
    (G : ∀ k, Matrix (BipPhase (Fin (a k)) (Fin (b k)))
      (BipPhase (Fin (a k)) (Fin (b k))) ℝ)
    (hG : ∀ k, physicalCovariance (G k) (bipJ (Fin (a k)) (Fin (b k)))) :
    ∃ k : K, valueV (familyCM a b G) = valueV (G k) ∧
      ∀ l : K, valueV (G k) ≤ valueV (G l) :=
  x8_main a b G
