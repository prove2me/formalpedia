-- Prove2me | solution 1 for QuantumLTF.Membership.Supplement.theorem_4_5
-- status  : ACCEPTED   (prove)
-- author  : @Robin Kothari
-- created : 2026-11-24T01:49:18.253525+00:00
-- url     : https://prove2.me/submissions/a2971c0b-13d6-4fb9-b8d6-ceedb5173377

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Query
import Definitions.Def_QuantumLTF_Membership_Supplement_queryComplexity
import Definitions.Def_QuantumLTF_Majority_AdversaryModel
import Theorems.Thm_QuantumLTF_Majority_lemma_4_5

namespace Aux_w_maj_alg

open QAlgorithms QuantumLTF.Membership.Supplement QuantumLTF.Majority

section GramUnitary

open Module

private lemma norm_sq_linear_comb_eq {α ι : Type*} [Fintype ι] [Fintype α]
    (v u : ι → EuclideanSpace ℂ α)
    (hgram : ∀ A B, inner ℂ (v A) (v B) = inner ℂ (u A) (u B))
    (c : ι → ℂ) :
    ‖∑ A, c A • u A‖ ^ 2 = ‖∑ A, c A • v A‖ ^ 2 := by
  have h : inner ℂ (∑ A, c A • u A) (∑ A, c A • u A) =
      inner ℂ (∑ A, c A • v A) (∑ A, c A • v A) := by
    simp only [sum_inner, inner_sum, inner_smul_left, inner_smul_right, hgram]
  rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at h
  exact_mod_cast h

private theorem exists_unitary_of_inner_eq {α ι : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
    [Fintype ι] (v u : ι → EuclideanSpace ℂ α)
    (hgram : ∀ A B, inner ℂ (v A) (v B) = inner ℂ (u A) (u B)) :
    ∃ U : Matrix α α ℂ, U ∈ Matrix.unitaryGroup α ℂ ∧ ∀ A, act U (v A) = u A := by
  classical
  let S₁ : Submodule ℂ (EuclideanSpace ℂ α) := Submodule.span ℂ (Set.range v)
  let S₂ : Submodule ℂ (EuclideanSpace ℂ α) := Submodule.span ℂ (Set.range u)
  let b₁ := stdOrthonormalBasis ℂ S₁
  let d₁ := Module.finrank ℂ S₁
  have hb₁_mem : ∀ k : Fin d₁, (b₁ k : EuclideanSpace ℂ α) ∈ S₁ := fun k => (b₁ k).2
  have hc : ∀ k : Fin d₁, ∃ c : ι → ℂ, (b₁ k : EuclideanSpace ℂ α) = ∑ A, c A • v A := by
    intro k
    have hk := hb₁_mem k
    dsimp only [S₁] at hk
    rw [Submodule.mem_span_range_iff_exists_fun] at hk
    obtain ⟨c, hc⟩ := hk
    exact ⟨c, hc.symm⟩
  choose c hc_eq using hc
  let w₀ : Fin d₁ → EuclideanSpace ℂ α := fun k => ∑ A, c k A • u A
  have hw₀_inner : ∀ k l : Fin d₁,
      inner ℂ (w₀ k) (w₀ l) = inner ℂ (b₁ k : EuclideanSpace ℂ α) (b₁ l : EuclideanSpace ℂ α) := by
    intro k l
    have h1 : inner ℂ (w₀ k) (w₀ l) =
        ∑ A, ∑ B, starRingEnd ℂ (c k A) * c l B * inner ℂ (u A) (u B) := by
      dsimp only [w₀]
      simp only [sum_inner, inner_sum, inner_smul_left, inner_smul_right, Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun A _ => Finset.sum_congr rfl fun B _ => ?_
      ring
    have h2 : inner ℂ (b₁ k : EuclideanSpace ℂ α) (b₁ l : EuclideanSpace ℂ α) =
        ∑ A, ∑ B, starRingEnd ℂ (c k A) * c l B * inner ℂ (v A) (v B) := by
      rw [hc_eq k, hc_eq l]
      simp only [sum_inner, inner_sum, inner_smul_left, inner_smul_right, Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun A _ => Finset.sum_congr rfl fun B _ => ?_
      ring
    rw [h1, h2]
    simp only [hgram]
  have hw₀_orth : Orthonormal ℂ w₀ := by
    rw [orthonormal_iff_ite]
    intro k l
    rw [hw₀_inner k l]
    exact (orthonormal_iff_ite.mp b₁.orthonormal) k l
  have hu_eq : ∀ A : ι, u A = ∑ k : Fin d₁, inner ℂ (b₁ k : EuclideanSpace ℂ α) (v A) • w₀ k := by
    intro A
    have hv_mem : v A ∈ S₁ := Submodule.subset_span ⟨A, rfl⟩
    have hv_repr : (⟨v A, hv_mem⟩ : S₁) = ∑ k : Fin d₁, inner ℂ (b₁ k) ⟨v A, hv_mem⟩ • b₁ k :=
      (b₁.sum_repr' ⟨v A, hv_mem⟩).symm
    have hv_eq : v A = ∑ k : Fin d₁,
        inner ℂ (b₁ k : EuclideanSpace ℂ α) (v A) • (b₁ k : EuclideanSpace ℂ α) := by
      have hcoe := congrArg Subtype.val hv_repr
      simpa [Submodule.coe_sum, Submodule.coe_smul, Submodule.coe_inner] using hcoe
    let coeff : ι → ℂ := fun B =>
      (if B = A then (1 : ℂ) else 0) -
        ∑ k : Fin d₁, inner ℂ (b₁ k : EuclideanSpace ℂ α) (v A) * c k B
    have hv_diff : ∑ B, coeff B • v B = 0 := by
      have h1 : ∑ B, (if B = A then (1 : ℂ) else 0) • v B = v A := by simp
      have h2 : ∑ B, (∑ k : Fin d₁, inner ℂ (b₁ k : EuclideanSpace ℂ α) (v A) * c k B) • v B =
          ∑ k : Fin d₁, inner ℂ (b₁ k : EuclideanSpace ℂ α) (v A) • (b₁ k : EuclideanSpace ℂ α) := by
        simp_rw [Finset.sum_smul, mul_smul]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [← Finset.smul_sum, hc_eq k]
      simp only [coeff, sub_smul, Finset.sum_sub_distrib, h1, h2]
      rw [← hv_eq, sub_self]
    have hu_diff : ∑ B, coeff B • u B =
        u A - ∑ k : Fin d₁, inner ℂ (b₁ k : EuclideanSpace ℂ α) (v A) • w₀ k := by
      have h1 : ∑ B, (if B = A then (1 : ℂ) else 0) • u B = u A := by simp
      have h2 : ∑ B, (∑ k : Fin d₁, inner ℂ (b₁ k : EuclideanSpace ℂ α) (v A) * c k B) • u B =
          ∑ k : Fin d₁, inner ℂ (b₁ k : EuclideanSpace ℂ α) (v A) • w₀ k := by
        simp_rw [Finset.sum_smul, mul_smul]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [← Finset.smul_sum]
      simp only [coeff, sub_smul, Finset.sum_sub_distrib, h1, h2]
    have hnorm : ‖u A - ∑ k : Fin d₁, inner ℂ (b₁ k : EuclideanSpace ℂ α) (v A) • w₀ k‖ ^ 2 = 0 := by
      rw [← hu_diff, norm_sq_linear_comb_eq v u hgram coeff, hv_diff, norm_zero, sq, mul_zero]
    rw [sq_eq_zero_iff, norm_eq_zero, sub_eq_zero] at hnorm
    exact hnorm
  have hw₀_mem : ∀ k : Fin d₁, w₀ k ∈ S₂ := fun k =>
    Submodule.sum_mem _ fun A _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨A, rfl⟩)
  have hS₂_eq : S₂ = Submodule.span ℂ (Set.range w₀) := by
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨A, rfl⟩
      rw [hu_eq A]
      exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
    · rw [Submodule.span_le]
      rintro _ ⟨k, rfl⟩
      exact hw₀_mem k
  have hfin₂ : Module.finrank ℂ S₂ = d₁ := by
    rw [hS₂_eq, finrank_span_eq_card hw₀_orth.linearIndependent, Fintype.card_fin]
  let p₁ := stdOrthonormalBasis ℂ S₁ᗮ
  let p₂ := stdOrthonormalBasis ℂ S₂ᗮ
  have hcard₁ : d₁ + Module.finrank ℂ S₁ᗮ = Module.finrank ℂ (EuclideanSpace ℂ α) :=
    Submodule.finrank_add_finrank_orthogonal S₁
  have hcard₂ : Module.finrank ℂ S₂ + Module.finrank ℂ S₂ᗮ = Module.finrank ℂ (EuclideanSpace ℂ α) :=
    Submodule.finrank_add_finrank_orthogonal S₂
  have horth_dim : Module.finrank ℂ S₁ᗮ = Module.finrank ℂ S₂ᗮ := by omega
  let e_orth : Fin (Module.finrank ℂ S₁ᗮ) ≃ Fin (Module.finrank ℂ S₂ᗮ) := finCongr horth_dim
  let f₁ : Fin d₁ ⊕ Fin (Module.finrank ℂ S₁ᗮ) → EuclideanSpace ℂ α :=
    Sum.elim (fun k => (b₁ k : EuclideanSpace ℂ α)) (fun j => (p₁ j : EuclideanSpace ℂ α))
  let f₂ : Fin d₁ ⊕ Fin (Module.finrank ℂ S₁ᗮ) → EuclideanSpace ℂ α :=
    Sum.elim w₀ (fun j => (p₂ (e_orth j) : EuclideanSpace ℂ α))
  have hf₁_orth : Orthonormal ℂ f₁ := by
    rw [orthonormal_iff_ite]
    rintro (k₁ | j₁) (k₂ | j₂)
    · simpa [f₁, Submodule.coe_inner] using (orthonormal_iff_ite.mp b₁.orthonormal) k₁ k₂
    · have hmem : (p₁ j₂ : EuclideanSpace ℂ α) ∈ S₁ᗮ := (p₁ j₂).2
      simp [f₁, Submodule.inner_right_of_mem_orthogonal (hb₁_mem k₁) hmem]
    · have hmem : (p₁ j₁ : EuclideanSpace ℂ α) ∈ S₁ᗮ := (p₁ j₁).2
      simp [f₁, Submodule.inner_left_of_mem_orthogonal (hb₁_mem k₂) hmem]
    · simpa [f₁, Submodule.coe_inner] using (orthonormal_iff_ite.mp p₁.orthonormal) j₁ j₂
  have hf₂_orth : Orthonormal ℂ f₂ := by
    rw [orthonormal_iff_ite]
    rintro (k₁ | j₁) (k₂ | j₂)
    · simpa [f₂] using (orthonormal_iff_ite.mp hw₀_orth) k₁ k₂
    · have hmem : (p₂ (e_orth j₂) : EuclideanSpace ℂ α) ∈ S₂ᗮ := (p₂ _).2
      simp [f₂, Submodule.inner_right_of_mem_orthogonal (hw₀_mem k₁) hmem]
    · have hmem : (p₂ (e_orth j₁) : EuclideanSpace ℂ α) ∈ S₂ᗮ := (p₂ _).2
      simp [f₂, Submodule.inner_left_of_mem_orthogonal (hw₀_mem k₂) hmem]
    · simpa [f₂, Submodule.coe_inner, e_orth.injective.eq_iff] using
        (orthonormal_iff_ite.mp p₂.orthonormal) (e_orth j₁) (e_orth j₂)
  have hcard_sum :
      Fintype.card (Fin d₁ ⊕ Fin (Module.finrank ℂ S₁ᗮ)) = Module.finrank ℂ (EuclideanSpace ℂ α) := by
    simpa [Fintype.card_sum] using hcard₁
  have hne_sum : Nonempty (Fin d₁ ⊕ Fin (Module.finrank ℂ S₁ᗮ)) := by
    have hpos : 0 < Module.finrank ℂ (EuclideanSpace ℂ α) := by
      rw [finrank_euclideanSpace]
      exact Fintype.card_pos
    rw [← hcard_sum, Fintype.card_sum, Fintype.card_fin, Fintype.card_fin] at hpos
    by_cases h1 : d₁ = 0
    · have h2 : 0 < Module.finrank ℂ S₁ᗮ := by omega
      exact ⟨Sum.inr ⟨0, h2⟩⟩
    · exact ⟨Sum.inl ⟨0, Nat.pos_of_ne_zero h1⟩⟩
  let B₁ : Basis (Fin d₁ ⊕ Fin (Module.finrank ℂ S₁ᗮ)) ℂ (EuclideanSpace ℂ α) :=
    basisOfOrthonormalOfCardEqFinrank hf₁_orth hcard_sum
  let B₂ : Basis (Fin d₁ ⊕ Fin (Module.finrank ℂ S₁ᗮ)) ℂ (EuclideanSpace ℂ α) :=
    basisOfOrthonormalOfCardEqFinrank hf₂_orth hcard_sum
  have hB₁_orth : Orthonormal ℂ B₁ := by simpa [B₁] using hf₁_orth
  have hB₂_orth : Orthonormal ℂ B₂ := by simpa [B₂] using hf₂_orth
  let T : EuclideanSpace ℂ α ≃ₗᵢ[ℂ] EuclideanSpace ℂ α :=
    hB₁_orth.equiv hB₂_orth (Equiv.refl _)
  let stdB := EuclideanSpace.basisFun α ℂ
  let stdT := stdB.map T
  let U : Matrix α α ℂ := stdB.toBasis.toMatrix ⇑stdT
  refine ⟨U, stdB.toMatrix_orthonormalBasis_mem_unitary stdT, ?_⟩
  intro A
  have hact : ∀ x : EuclideanSpace ℂ α, act U x = T x := by
    intro x
    ext i
    have hx_eq : x = ∑ j, x j • stdB j := by
      simpa [stdB, EuclideanSpace.basisFun_apply, EuclideanSpace.inner_single_left] using
        (stdB.sum_repr' x).symm
    have hT_eq : T x = ∑ j, x j • stdT j := by
      conv_lhs => rw [hx_eq, map_sum]
      refine Finset.sum_congr rfl fun j _ => by simp [stdT]
    have hU_entry : ∀ j, U i j = (stdT j) i := by
      intro j
      simp [U, stdB, Basis.toMatrix_apply]
    simp only [act, WithLp.ofLp_toLp, Matrix.mulVec, dotProduct, hU_entry, hT_eq,
      WithLp.ofLp_sum, WithLp.ofLp_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, mul_comm]
  rw [hact (v A)]
  have hv_mem : v A ∈ S₁ := Submodule.subset_span ⟨A, rfl⟩
  have hv_eq : v A = ∑ k : Fin d₁,
      inner ℂ (b₁ k : EuclideanSpace ℂ α) (v A) • (b₁ k : EuclideanSpace ℂ α) := by
    have hcoe := congrArg Subtype.val (b₁.sum_repr' ⟨v A, hv_mem⟩).symm
    simpa [Submodule.coe_sum, Submodule.coe_smul, Submodule.coe_inner] using hcoe
  conv_lhs => rw [hv_eq, map_sum]
  rw [hu_eq A]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_smul]
  congr 1
  have hTk : T (B₁ (Sum.inl k)) = B₂ (Sum.inl k) := hB₁_orth.equiv_apply hB₂_orth (Equiv.refl _) _
  simpa [B₁, B₂, f₁, f₂] using hTk

private theorem gram_vectors_of_posSemidef {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι ℝ) (hM : M.PosSemidef) :
    ∃ w : ι → EuclideanSpace ℂ ι, ∀ A B, inner ℂ (w A) (w B) = (M A B : ℂ) := by
  let U : Matrix ι ι ℝ := (hM.isHermitian.eigenvectorUnitary : Matrix ι ι ℝ)
  let d : ι → ℝ := fun i => Real.sqrt (hM.isHermitian.eigenvalues i)
  let B : Matrix ι ι ℝ := Matrix.diagonal d * star U
  let w : ι → EuclideanSpace ℂ ι := fun A => WithLp.toLp 2 (fun k => (B k A : ℂ))
  refine ⟨w, fun A B' => ?_⟩
  have hspec : U * Matrix.diagonal hM.isHermitian.eigenvalues * star U = M := by
    simpa [U, Unitary.conjStarAlgAut_apply] using hM.isHermitian.spectral_theorem.symm
  have hdiag : Matrix.diagonal d * Matrix.diagonal d = Matrix.diagonal hM.isHermitian.eigenvalues := by
    ext i j
    by_cases hij : i = j
    · subst hij
      simp [d, Real.mul_self_sqrt (hM.eigenvalues_nonneg i)]
    · simp [hij]
  have hBB : star B * B = M := by
    have hBstar : star B = U * Matrix.diagonal d := by
      have hdiag_star : star (Matrix.diagonal d) = Matrix.diagonal d := by
        ext i j
        by_cases hij : i = j
        · subst hij; simp [Matrix.star_apply]
        · simp [Matrix.star_apply, hij, ne_comm.mp hij]
      simp [B, star_mul, hdiag_star]
    calc star B * B
        = (U * Matrix.diagonal d) * (Matrix.diagonal d * star U) := by rw [hBstar]
      _ = U * ((Matrix.diagonal d * Matrix.diagonal d) * star U) := by simp only [Matrix.mul_assoc]
      _ = U * (Matrix.diagonal hM.isHermitian.eigenvalues * star U) := by rw [hdiag]
      _ = M := by rw [← Matrix.mul_assoc, hspec]
  have hinner : inner ℂ (w A) (w B') = ((∑ k : ι, B k A * B k B' : ℝ) : ℂ) := by
    rw [EuclideanSpace.inner_eq_star_dotProduct]
    simp [w, dotProduct, mul_comm]
  rw [hinner]
  congr 1
  have hent := congrArg (fun N : Matrix ι ι ℝ => N A B') hBB
  simpa [Matrix.mul_apply, Matrix.star_apply] using hent

end GramUnitary

section LiftHelpers

private lemma act_add {ι : Type*} [Fintype ι] (U : Matrix ι ι ℂ) (ψ φ : EuclideanSpace ℂ ι) :
    act U (ψ + φ) = act U ψ + act U φ := by
  ext y
  simp [act, Matrix.mulVec_add]

private lemma act_sub {ι : Type*} [Fintype ι] (U : Matrix ι ι ℂ) (ψ φ : EuclideanSpace ℂ ι) :
    act U (ψ - φ) = act U ψ - act U φ := by
  ext y
  simp [act, Matrix.mulVec_sub]

private lemma act_smul {ι : Type*} [Fintype ι] (U : Matrix ι ι ℂ) (c : ℂ) (ψ : EuclideanSpace ℂ ι) :
    act U (c • ψ) = c • act U ψ := by
  ext y
  simp [act, Matrix.mulVec_smul]

private lemma act_sum {ι κ : Type*} [Fintype ι] (U : Matrix ι ι ℂ) (s : Finset κ)
    (f : κ → EuclideanSpace ℂ ι) :
    act U (∑ x ∈ s, f x) = ∑ x ∈ s, act U (f x) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      ext y
      simp [act]
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, act_add, ih, Finset.sum_insert ha]

private lemma act_mul {ι : Type*} [Fintype ι] (A B : Matrix ι ι ℂ) (ψ : EuclideanSpace ℂ ι) :
    act (A * B) ψ = act A (act B ψ) := by
  ext y
  simp [act, Matrix.mulVec_mulVec]

private noncomputable def liftVec {α β : Type*} [Fintype α] [DecidableEq β] (e : α ↪ β)
    (ψ : EuclideanSpace ℂ α) : EuclideanSpace ℂ β :=
  ∑ a : α, ψ a • ket (e a)

private lemma liftVec_apply_embed {α β : Type*} [Fintype α] [DecidableEq β] (e : α ↪ β)
    (ψ : EuclideanSpace ℂ α) (a : α) : liftVec e ψ (e a) = ψ a := by
  classical
  simp only [liftVec, WithLp.ofLp_sum, WithLp.ofLp_smul, Finset.sum_apply, Pi.smul_apply,
    smul_eq_mul, ket, PiLp.single_apply]
  rw [Finset.sum_eq_single a]
  · simp
  · intro b _ hb
    simp [hb.symm]
  · intro ha; exact absurd (Finset.mem_univ _) ha

private lemma liftVec_apply_not_mem {α β : Type*} [Fintype α] [DecidableEq β] (e : α ↪ β)
    (ψ : EuclideanSpace ℂ α) {b : β} (hb : b ∉ Set.range e) : liftVec e ψ b = 0 := by
  simp only [liftVec, WithLp.ofLp_sum, WithLp.ofLp_smul, Finset.sum_apply, Pi.smul_apply,
    smul_eq_mul, ket, PiLp.single_apply]
  refine Finset.sum_eq_zero fun a _ => ?_
  have hne : b ≠ e a := fun h => hb ⟨a, h.symm⟩
  simp [hne]

private lemma liftVec_ket {α β : Type*} [Fintype α] [DecidableEq α] [DecidableEq β]
    (e : α ↪ β) (a : α) : liftVec e (ket a) = ket (e a) := by
  ext b
  by_cases hb : b ∈ Set.range e
  · obtain ⟨a', rfl⟩ := hb
    rw [liftVec_apply_embed]
    simp [ket, PiLp.single_apply, e.injective.eq_iff]
  · rw [liftVec_apply_not_mem e (ket a) hb]
    have hne : b ≠ e a := fun h => hb ⟨a, h.symm⟩
    simp [ket, hne]

private lemma liftVec_add {α β : Type*} [Fintype α] [DecidableEq β] (e : α ↪ β)
    (ψ φ : EuclideanSpace ℂ α) : liftVec e (ψ + φ) = liftVec e ψ + liftVec e φ := by
  simp [liftVec, add_smul, Finset.sum_add_distrib]

private lemma liftVec_sub {α β : Type*} [Fintype α] [DecidableEq β] (e : α ↪ β)
    (ψ φ : EuclideanSpace ℂ α) : liftVec e (ψ - φ) = liftVec e ψ - liftVec e φ := by
  simp [liftVec, sub_smul, Finset.sum_sub_distrib]

private lemma liftVec_smul {α β : Type*} [Fintype α] [DecidableEq β] (e : α ↪ β)
    (c : ℂ) (ψ : EuclideanSpace ℂ α) : liftVec e (c • ψ) = c • liftVec e ψ := by
  simp only [liftVec, Finset.smul_sum, smul_smul, PiLp.smul_apply, smul_eq_mul]

private lemma liftVec_inner {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β] (e : α ↪ β)
    (ψ φ : EuclideanSpace ℂ α) : inner ℂ (liftVec e ψ) (liftVec e φ) = inner ℂ ψ φ := by
  classical
  simp only [liftVec, sum_inner, inner_sum, inner_smul_left, inner_smul_right, ket,
    EuclideanSpace.inner_single_left, PiLp.single_apply, map_one, one_mul]
  rw [EuclideanSpace.inner_eq_star_dotProduct, dotProduct]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_eq_single a]
  · simp [RCLike.star_def, mul_comm]
  · intro b _ hb
    simp [hb]
  · intro ha; exact absurd (Finset.mem_univ _) ha

private lemma liftVec_norm {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β] (e : α ↪ β)
    (ψ : EuclideanSpace ℂ α) : ‖liftVec e ψ‖ = ‖ψ‖ := by
  rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)]
  have h : inner ℂ (liftVec e ψ) (liftVec e ψ) = inner ℂ ψ ψ := liftVec_inner e ψ ψ
  rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at h
  exact_mod_cast h

private lemma liftVec_comp {α β γ : Type*} [Fintype α] [Fintype β] [DecidableEq β] [DecidableEq γ]
    (e₁ : α ↪ β) (e₂ : β ↪ γ) (ψ : EuclideanSpace ℂ α) :
    liftVec e₂ (liftVec e₁ ψ) = liftVec (e₁.trans e₂) ψ := by
  classical
  ext c
  by_cases hc : c ∈ Set.range e₂
  · obtain ⟨b, rfl⟩ := hc
    rw [liftVec_apply_embed]
    by_cases hb : b ∈ Set.range e₁
    · obtain ⟨a, rfl⟩ := hb
      rw [liftVec_apply_embed]
      exact (liftVec_apply_embed (e₁.trans e₂) ψ a).symm
    · rw [liftVec_apply_not_mem e₁ ψ hb]
      symm
      apply liftVec_apply_not_mem
      rintro ⟨a, ha⟩
      apply hb
      exact ⟨a, e₂.injective ha⟩
  · rw [liftVec_apply_not_mem e₂ _ hc]
    symm
    apply liftVec_apply_not_mem
    rintro ⟨a, ha⟩
    apply hc
    exact ⟨e₁ a, ha⟩

private noncomputable def liftMat {α β : Type*} [DecidableEq β]
    (e : α ↪ β) (U : Matrix α α ℂ) : Matrix β β ℂ :=
  open Classical in
  Matrix.of fun x y =>
    if hx : ∃ a, e a = x then
      if hy : ∃ a', e a' = y then U (Classical.choose hx) (Classical.choose hy) else 0
    else if x = y then 1 else 0

private lemma liftMat_apply_embed {α β : Type*} [DecidableEq β]
    (e : α ↪ β) (U : Matrix α α ℂ) (a a' : α) :
    liftMat e U (e a) (e a') = U a a' := by
  dsimp only [liftMat]
  rw [Matrix.of_apply]
  split_ifs with hx hy
  · congr 1
    · exact e.injective (Classical.choose_spec hx)
    · exact e.injective (Classical.choose_spec hy)
  · exact absurd ⟨a', rfl⟩ hy
  · exact absurd ⟨a, rfl⟩ hx
  · exact absurd ⟨a, rfl⟩ hx

private lemma liftMat_apply_mem_not {α β : Type*} [DecidableEq β]
    (e : α ↪ β) (U : Matrix α α ℂ) (a : α) {y : β} (hy : y ∉ Set.range e) :
    liftMat e U (e a) y = 0 := by
  dsimp only [liftMat]
  rw [Matrix.of_apply]
  split_ifs with hx hy'
  · exact absurd hy' hy
  · rfl
  · exact absurd ⟨a, rfl⟩ hx
  · exact absurd ⟨a, rfl⟩ hx

private lemma liftMat_apply_not_mem {α β : Type*} [DecidableEq β]
    (e : α ↪ β) (U : Matrix α α ℂ) {x : β} (hx : x ∉ Set.range e) (a' : α) :
    liftMat e U x (e a') = 0 := by
  dsimp only [liftMat]
  rw [Matrix.of_apply]
  split_ifs with hx' _ hxy
  · exact absurd hx' hx
  · exact absurd hx' hx
  · exact absurd ⟨a', hxy.symm⟩ hx
  · rfl

private lemma liftMat_apply_not_not {α β : Type*} [DecidableEq β]
    (e : α ↪ β) (U : Matrix α α ℂ) {x y : β} (hx : x ∉ Set.range e) (_hy : y ∉ Set.range e) :
    liftMat e U x y = if x = y then 1 else 0 := by
  dsimp only [liftMat]
  rw [Matrix.of_apply]
  split_ifs with hx' hy' <;> first | exact absurd hx' hx | rfl

private lemma liftMat_star {α β : Type*} [DecidableEq β]
    (e : α ↪ β) (U : Matrix α α ℂ) : star (liftMat e U) = liftMat e (star U) := by
  ext x y
  simp only [Matrix.star_apply]
  by_cases hx : x ∈ Set.range e <;> by_cases hy : y ∈ Set.range e
  · obtain ⟨a, rfl⟩ := hx; obtain ⟨b, rfl⟩ := hy
    rw [liftMat_apply_embed, liftMat_apply_embed, Matrix.star_apply]
  · obtain ⟨a, rfl⟩ := hx
    rw [liftMat_apply_not_mem e U hy a, liftMat_apply_mem_not e (star U) a hy, star_zero]
  · obtain ⟨b, rfl⟩ := hy
    rw [liftMat_apply_mem_not e U b hx, liftMat_apply_not_mem e (star U) hx b, star_zero]
  · rw [liftMat_apply_not_not e U hy hx, liftMat_apply_not_not e (star U) hx hy]
    by_cases hxy : x = y
    · subst hxy; simp
    · simp [hxy, ne_comm.mp hxy]

private lemma liftMat_one {α β : Type*} [DecidableEq α] [DecidableEq β] (e : α ↪ β) :
    liftMat e 1 = 1 := by
  ext x y
  by_cases hx : x ∈ Set.range e <;> by_cases hy : y ∈ Set.range e
  · obtain ⟨a, rfl⟩ := hx; obtain ⟨b, rfl⟩ := hy
    rw [liftMat_apply_embed]
    by_cases hab : a = b
    · subst hab; simp
    · have hne : e a ≠ e b := fun h => hab (e.injective h)
      simp [hab, hne]
  · obtain ⟨a, rfl⟩ := hx
    rw [liftMat_apply_mem_not e 1 a hy]
    have hne : e a ≠ y := fun h => hy ⟨a, h⟩
    simp [hne]
  · obtain ⟨b, rfl⟩ := hy
    rw [liftMat_apply_not_mem e 1 hx b]
    have hne : x ≠ e b := fun h => hx ⟨b, h.symm⟩
    simp [hne]
  · rw [liftMat_apply_not_not e 1 hx hy, Matrix.one_apply]

private lemma liftMat_mul {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β]
    (e : α ↪ β) (U V : Matrix α α ℂ) : liftMat e (U * V) = liftMat e U * liftMat e V := by
  classical
  ext x y
  simp only [Matrix.mul_apply]
  by_cases hx : x ∈ Set.range e <;> by_cases hy : y ∈ Set.range e
  · obtain ⟨a, rfl⟩ := hx; obtain ⟨b, rfl⟩ := hy
    rw [liftMat_apply_embed, Matrix.mul_apply]
    have hsplit : (∑ z : β, liftMat e U (e a) z * liftMat e V z (e b)) =
        ∑ z ∈ Finset.univ.image e, liftMat e U (e a) z * liftMat e V z (e b) := by
      rw [← Finset.sum_subset (Finset.subset_univ _)]
      intro z _ hz
      have hz' : z ∉ Set.range e := by simpa using hz
      rw [liftMat_apply_mem_not e U a hz', zero_mul]
    rw [hsplit, Finset.sum_image (fun c _ d _ h => e.injective h)]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [liftMat_apply_embed, liftMat_apply_embed]
  · obtain ⟨a, rfl⟩ := hx
    rw [liftMat_apply_mem_not e (U * V) a hy]
    symm
    refine Finset.sum_eq_zero fun z _ => ?_
    by_cases hz : z ∈ Set.range e
    · obtain ⟨c, rfl⟩ := hz
      rw [liftMat_apply_mem_not e V c hy, mul_zero]
    · rw [liftMat_apply_mem_not e U a hz, zero_mul]
  · obtain ⟨b, rfl⟩ := hy
    rw [liftMat_apply_not_mem e (U * V) hx b]
    symm
    refine Finset.sum_eq_zero fun z _ => ?_
    by_cases hz : z ∈ Set.range e
    · obtain ⟨c, rfl⟩ := hz
      rw [liftMat_apply_not_mem e U hx c, zero_mul]
    · rw [liftMat_apply_not_mem e V hz b, mul_zero]
  · rw [liftMat_apply_not_not e (U * V) hx hy]
    symm
    rw [Finset.sum_eq_single x]
    · rw [liftMat_apply_not_not e U hx hx, if_pos rfl, one_mul,
        liftMat_apply_not_not e V hx hy]
    · intro z _ hz
      by_cases hzr : z ∈ Set.range e
      · obtain ⟨c, rfl⟩ := hzr
        rw [liftMat_apply_not_mem e U hx c, zero_mul]
      · rw [liftMat_apply_not_not e U hx hzr, if_neg hz.symm, zero_mul]
    · intro hmem; exact absurd (Finset.mem_univ _) hmem

private lemma liftMat_mem_unitaryGroup {α β : Type*} [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β] (e : α ↪ β) {U : Matrix α α ℂ} (hU : U ∈ Matrix.unitaryGroup α ℂ) :
    liftMat e U ∈ Matrix.unitaryGroup β ℂ := by
  rw [Matrix.mem_unitaryGroup_iff, liftMat_star, ← liftMat_mul,
    Matrix.mem_unitaryGroup_iff.mp hU, liftMat_one]

private lemma act_liftMat_liftVec {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β]
    (e : α ↪ β) (U : Matrix α α ℂ) (ψ : EuclideanSpace ℂ α) :
    act (liftMat e U) (liftVec e ψ) = liftVec e (act U ψ) := by
  classical
  ext y
  simp only [act, WithLp.ofLp_toLp, Matrix.mulVec, dotProduct]
  by_cases hy : y ∈ Set.range e
  · obtain ⟨a, rfl⟩ := hy
    rw [liftVec_apply_embed]
    have hsplit : (∑ z : β, liftMat e U (e a) z * liftVec e ψ z) =
        ∑ z ∈ Finset.univ.image e, liftMat e U (e a) z * liftVec e ψ z := by
      rw [← Finset.sum_subset (Finset.subset_univ _)]
      intro z _ hz
      have hz' : z ∉ Set.range e := by simpa using hz
      rw [liftVec_apply_not_mem e ψ hz', mul_zero]
    rw [hsplit, Finset.sum_image (fun c _ d _ h => e.injective h)]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [liftMat_apply_embed, liftVec_apply_embed]
  · rw [liftVec_apply_not_mem e _ hy]
    refine Finset.sum_eq_zero fun z _ => ?_
    by_cases hz : z ∈ Set.range e
    · obtain ⟨c, rfl⟩ := hz
      rw [liftMat_apply_not_mem e U hy c, zero_mul]
    · rw [liftVec_apply_not_mem e ψ hz, mul_zero]

private lemma act_liftMat_ket_not_mem {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β]
    (e : α ↪ β) (U : Matrix α α ℂ) {b : β} (hb : b ∉ Set.range e) :
    act (liftMat e U) (ket b) = ket b := by
  ext y
  simp only [act, WithLp.ofLp_toLp, Matrix.mulVec, dotProduct, ket, PiLp.single_apply]
  rw [Finset.sum_eq_single b]
  · simp only [↓reduceIte, mul_one]
    by_cases hy : y ∈ Set.range e
    · obtain ⟨a, rfl⟩ := hy
      rw [liftMat_apply_mem_not e U a hb]
      have hne : e a ≠ b := fun h => hb ⟨a, h⟩
      simp [hne]
    · exact liftMat_apply_not_not e U hy hb
  · intro z _ hz
    simp [hz]
  · intro hmem; exact absurd (Finset.mem_univ _) hmem

private lemma act_diagonal {ι : Type*} [Fintype ι] [DecidableEq ι] (d : ι → ℂ)
    (ψ : EuclideanSpace ℂ ι) (y : ι) : act (Matrix.diagonal d) ψ y = d y * ψ y := by
  simp only [act, WithLp.ofLp_toLp, Matrix.mulVec, dotProduct, Matrix.diagonal_apply]
  rw [Finset.sum_eq_single y]
  · simp
  · intro z _ hz; simp [hz.symm]
  · simp

private lemma act_diagonal_liftVec {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β] (e : α ↪ β) (d : β → ℂ) (d₀ : α → ℂ)
    (hd : ∀ a, d (e a) = d₀ a) (φ : EuclideanSpace ℂ α) :
    act (Matrix.diagonal d) (liftVec e φ) = liftVec e (act (Matrix.diagonal d₀) φ) := by
  classical
  ext y
  rw [act_diagonal]
  by_cases hy : y ∈ Set.range e
  · obtain ⟨a, rfl⟩ := hy
    rw [liftVec_apply_embed, liftVec_apply_embed, hd a, act_diagonal]
  · rw [liftVec_apply_not_mem e _ hy, liftVec_apply_not_mem e _ hy, mul_zero]

private def packQubits {n cBits : ℕ} (ctrl : Bool) (q : Qubits n) (c : Qubits cBits)
    (w : Qubits n) : Qubits (1 + n + cBits + n) :=
  fun a =>
    if h0 : a.1 = 0 then ctrl
    else if h1 : a.1 < 1 + n then q ⟨a.1 - 1, by omega⟩
    else if h2 : a.1 < 1 + n + cBits then c ⟨a.1 - (1 + n), by omega⟩
    else w ⟨a.1 - (1 + n + cBits), by omega⟩

private lemma packQubits_ctrl {n cBits : ℕ} (ctrl : Bool) (q : Qubits n) (c : Qubits cBits)
    (w : Qubits n) : packQubits ctrl q c w ⟨0, by omega⟩ = ctrl := by
  simp [packQubits]

private lemma packQubits_regQ {n cBits : ℕ} (ctrl : Bool) (q : Qubits n) (c : Qubits cBits)
    (w : Qubits n) (i : Fin n) : packQubits ctrl q c w ⟨1 + i.1, by omega⟩ = q i := by
  have hi := i.isLt
  simp [packQubits, hi]

private lemma packQubits_regC {n cBits : ℕ} (ctrl : Bool) (q : Qubits n) (c : Qubits cBits)
    (w : Qubits n) (i : Fin cBits) : packQubits ctrl q c w ⟨1 + n + i.1, by omega⟩ = c i := by
  have hi := i.isLt
  have h2 : ¬ (1 + n + i.1 < 1 + n) := by omega
  have h3 : 1 + n + i.1 < 1 + n + cBits := by omega
  simp [packQubits, h2, h3]

private lemma packQubits_regW {n cBits : ℕ} (ctrl : Bool) (q : Qubits n) (c : Qubits cBits)
    (w : Qubits n) (i : Fin n) :
    packQubits ctrl q c w ⟨1 + n + cBits + i.1, by omega⟩ = w i := by
  have hi := i.isLt
  have h2 : ¬ (1 + n + cBits + i.1 < 1 + n) := by omega
  have h3 : ¬ (1 + n + cBits + i.1 < 1 + n + cBits) := by omega
  simp [packQubits, h2, h3]

private lemma packQubits_inj {n cBits : ℕ} {ctrl₁ ctrl₂ : Bool} {q₁ q₂ : Qubits n}
    {c₁ c₂ : Qubits cBits} {w₁ w₂ : Qubits n}
    (h : packQubits ctrl₁ q₁ c₁ w₁ = packQubits ctrl₂ q₂ c₂ w₂) :
    ctrl₁ = ctrl₂ ∧ q₁ = q₂ ∧ c₁ = c₂ ∧ w₁ = w₂ := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · have hc := congrFun h ⟨0, by omega⟩
    rwa [packQubits_ctrl, packQubits_ctrl] at hc
  · funext i
    have hq := congrFun h ⟨1 + i.1, by omega⟩
    rwa [packQubits_regQ, packQubits_regQ] at hq
  · funext i
    have hci := congrFun h ⟨1 + n + i.1, by omega⟩
    rwa [packQubits_regC, packQubits_regC] at hci
  · funext i
    have hw := congrFun h ⟨1 + n + cBits + i.1, by omega⟩
    rwa [packQubits_regW, packQubits_regW] at hw

private lemma packQubits_false (n cBits : ℕ) :
    packQubits false (fun _ : Fin n => false) (fun _ : Fin cBits => false)
        (fun _ : Fin n => false) = fun _ => false := by
  funext a
  simp only [packQubits]
  split_ifs <;> rfl

private lemma natToBits_zero (n : ℕ) : natToBits n 0 = fun _ => false := by
  simp only [natToBits, Nat.zero_mod]
  apply (bitsEquivFin n).injective
  rw [Equiv.apply_symm_apply]
  ext
  rw [bitsEquivFin_apply]
  simp [bitsToNat]

private lemma natToBits_inj_of_lt {n a b : ℕ} (ha : a < 2 ^ n) (hb : b < 2 ^ n)
    (h : natToBits n a = natToBits n b) : a = b := by
  simp only [natToBits, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at h
  have h' := (bitsEquivFin n).symm.injective h
  exact congrArg Fin.val h'

end LiftHelpers

section CircuitHelpers

private noncomputable def minusAmp (b : Bool) : ℂ :=
  if b then -((Real.sqrt 2)⁻¹ : ℂ) else ((Real.sqrt 2)⁻¹ : ℂ)

private lemma minusAmp_neg (b : Bool) : minusAmp (!b) = -minusAmp b := by
  cases b <;> simp [minusAmp]

private lemma sum_norm_sq_minusAmp : ∑ b : Bool, ‖minusAmp b‖ ^ 2 = 1 := by
  simp only [Fintype.sum_bool, minusAmp, ↓reduceIte, Bool.false_eq_true, norm_neg,
    norm_inv, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg 2)]
  rw [← two_mul, inv_pow, Real.sq_sqrt (by norm_num)]
  norm_num

private noncomputable def withMinus {M : ℕ} (φ : EuclideanSpace ℂ (Qubits M)) :
    EuclideanSpace ℂ (Qubits (M + 1)) :=
  WithLp.toLp 2 fun z => φ (Fin.init z) * minusAmp (z (Fin.last M))

private def qubitsSnocEquiv (M : ℕ) : Qubits (M + 1) ≃ Qubits M × Bool where
  toFun z := (Fin.init z, z (Fin.last M))
  invFun p := Fin.snoc (α := fun _ => Bool) p.1 p.2
  left_inv z := Fin.snoc_init_self z
  right_inv p := by ext <;> simp

private lemma withMinus_norm {M : ℕ} (φ : EuclideanSpace ℂ (Qubits M)) : ‖withMinus φ‖ = ‖φ‖ := by
  rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _), EuclideanSpace.norm_sq_eq,
    EuclideanSpace.norm_sq_eq]
  rw [Fintype.sum_equiv (qubitsSnocEquiv M) _ (fun p => ‖φ p.1‖ ^ 2 * ‖minusAmp p.2‖ ^ 2)
    (fun z => by simp [withMinus, qubitsSnocEquiv, mul_pow])]
  rw [Fintype.sum_prod_type]
  simp_rw [← Finset.mul_sum, sum_norm_sq_minusAmp, mul_one]

private lemma probEvent_congr {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ψ : EuclideanSpace ℂ ι) (P Q : ι → Prop) [DecidablePred P] [DecidablePred Q]
    (hPQ : ∀ z, P z ↔ Q z) : probEvent ψ P = probEvent ψ Q := by
  simp only [probEvent]
  congr 1
  ext z
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, hPQ]

private lemma probEvent_withMinus {M : ℕ} (φ : EuclideanSpace ℂ (Qubits M))
    (P : Qubits M → Prop) [DecidablePred P] :
    open Classical in
    probEvent (withMinus φ) (fun z => P (Fin.init z)) = probEvent φ P := by
  classical
  simp only [probEvent, prob, ket, EuclideanSpace.inner_single_left, Finset.sum_filter,
    map_one, one_mul]
  rw [Fintype.sum_equiv (qubitsSnocEquiv M) _
    (fun p : Qubits M × Bool => if P p.1 then ‖φ p.1‖ ^ 2 * ‖minusAmp p.2‖ ^ 2 else 0)
    (fun z => by
      by_cases hz : P (Fin.init z)
      · simp [qubitsSnocEquiv, withMinus, hz, mul_pow]
      · simp [qubitsSnocEquiv, hz])]
  rw [Fintype.sum_prod_type]
  have hrow : ∀ x : Qubits M,
      ∑ b : Bool, (if P x then ‖φ x‖ ^ 2 * ‖minusAmp b‖ ^ 2 else 0) =
        if P x then ‖φ x‖ ^ 2 else 0 := by
    intro x
    by_cases hx : P x
    · simp only [hx, ↓reduceIte]
      rw [← Finset.mul_sum, sum_norm_sq_minusAmp, mul_one]
    · simp [hx]
  simp_rw [hrow]

private lemma act_embedOp_castSucc_withMinus {M : ℕ} (G : Matrix (Qubits M) (Qubits M) ℂ)
    (φ : EuclideanSpace ℂ (Qubits M)) :
    act (embedOp G (Fin.castAddEmb 1)) (withMinus φ) = withMinus (act G φ) := by
  ext y
  simp only [act, WithLp.ofLp_toLp, Matrix.mulVec, dotProduct, withMinus, embedOp, Matrix.of_apply]
  have hcast : ∀ j : Fin M, Fin.castAddEmb 1 j = j.castSucc := fun _ => rfl
  have hrange : ∀ a : Fin (M + 1), a ∉ Set.range (Fin.castAddEmb 1) ↔ a = Fin.last M := by
    intro a
    refine Fin.lastCases ?_ ?_ a
    · constructor
      · intro _; rfl
      · rintro _ ⟨i, hi⟩
        have hi' := congrArg Fin.val hi
        simp [Fin.castAddEmb] at hi'
        omega
    · intro i
      constructor
      · intro h; exact absurd ⟨i, rfl⟩ h
      · intro h
        have h' := congrArg Fin.val h
        simp at h'
        omega
  have hprod : (∑ z : Qubits (M + 1),
      (if ∀ a : Fin (M + 1), a ∉ Set.range (Fin.castAddEmb 1) → y a = z a
        then G (y ∘ Fin.castAddEmb 1) (z ∘ Fin.castAddEmb 1) else 0) *
      (φ (Fin.init z) * minusAmp (z (Fin.last M)))) =
      ∑ p : Qubits M × Bool,
      (if ∀ a : Fin (M + 1), a ∉ Set.range (Fin.castAddEmb 1) →
          y a = Fin.snoc (α := fun _ => Bool) p.1 p.2 a
        then G (y ∘ Fin.castAddEmb 1) (Fin.snoc (α := fun _ => Bool) p.1 p.2 ∘ Fin.castAddEmb 1)
        else 0) *
      (φ p.1 * minusAmp p.2) := by
    refine Fintype.sum_equiv (qubitsSnocEquiv M) _ _ fun z => ?_
    dsimp only [qubitsSnocEquiv]
    change (if ∀ a : Fin (M + 1), a ∉ Set.range (Fin.castAddEmb 1) → y a = z a
        then G (y ∘ Fin.castAddEmb 1) (z ∘ Fin.castAddEmb 1) else 0) *
        (φ (Fin.init z) * minusAmp (z (Fin.last M))) =
      (if ∀ a : Fin (M + 1), a ∉ Set.range (Fin.castAddEmb 1) →
          y a = Fin.snoc (α := fun _ => Bool) (Fin.init z) (z (Fin.last M)) a
        then G (y ∘ Fin.castAddEmb 1)
          (Fin.snoc (α := fun _ => Bool) (Fin.init z) (z (Fin.last M)) ∘ Fin.castAddEmb 1)
        else 0) *
        (φ (Fin.init z) * minusAmp (z (Fin.last M)))
    simp_rw [Fin.snoc_init_self]
  rw [hprod, Fintype.sum_prod_type, Finset.sum_comm]
  have hcomp : ∀ x : Qubits M,
      (Fin.snoc (α := fun _ => Bool) x (y (Fin.last M)) ∘ Fin.castAddEmb 1) = x := by
    intro x; funext j; rw [Function.comp_apply, hcast j, Fin.snoc_castSucc]
  have hy_comp : (y ∘ Fin.castAddEmb 1) = Fin.init y := by
    funext j; rfl
  rw [Finset.sum_eq_single (y (Fin.last M))]
  · have hpos_cond : ∀ x : Qubits M,
        ∀ a : Fin (M + 1), a ∉ Set.range (Fin.castAddEmb 1) →
          y a = Fin.snoc (α := fun _ => Bool) x (y (Fin.last M)) a := by
      intro x a ha
      rw [(hrange a).mp ha, Fin.snoc_last]
    have hsum_term : ∀ x : Qubits M,
        (if ∀ a : Fin (M + 1), a ∉ Set.range (Fin.castAddEmb 1) →
            y a = Fin.snoc (α := fun _ => Bool) x (y (Fin.last M)) a
          then G (y ∘ Fin.castAddEmb 1) (Fin.snoc (α := fun _ => Bool) x (y (Fin.last M)) ∘ Fin.castAddEmb 1)
          else 0) * (φ x * minusAmp (y (Fin.last M))) =
        (G (Fin.init y) x * φ x) * minusAmp (y (Fin.last M)) := by
      intro x
      rw [if_pos (hpos_cond x), hy_comp, hcomp x]
      ring
    simp_rw [hsum_term, ← Finset.sum_mul]
  · intro b _ hb
    refine Finset.sum_eq_zero fun x _ => ?_
    have hnot : ¬ (∀ a : Fin (M + 1), a ∉ Set.range (Fin.castAddEmb 1) →
        y a = Fin.snoc (α := fun _ => Bool) x b a) := by
      intro h
      have hlast := h (Fin.last M) ((hrange (Fin.last M)).mpr rfl)
      simp only [Fin.snoc_last] at hlast
      exact hb hlast.symm
    rw [if_neg hnot, zero_mul]
  · intro hmem; exact absurd (Finset.mem_univ _) hmem

private lemma majJunta_eq_neg_one_iff {n : ℕ} (A : Finset (Fin n)) (x : Qubits n) :
    decide (majJunta A (Finset.univ.filter fun i => x i = true) = -1) = majorityBit A x := by
  have hset : A ∩ (Finset.univ.filter fun i => x i = true) = A.filter fun i => x i := by
    ext i; simp
  rw [majJunta, majorityBit, hset]
  split_ifs with h1 <;> simp_all

private lemma act_majOracle_withMinus {n : ℕ} (A : Finset (Fin n)) (φ : EuclideanSpace ℂ (Qubits n)) :
    act (majOracle A) (withMinus φ) = withMinus (act (phaseOracle (majorityBit A)) φ) := by
  ext y
  simp only [act, WithLp.ofLp_toLp, Matrix.mulVec, dotProduct, majOracle, Matrix.of_apply,
    withMinus, phaseOracle, Matrix.diagonal_apply]
  have hprod : (∑ z : Qubits (n + 1),
      (if y = Fin.snoc (α := fun _ => Bool) (Fin.init z)
          (xor (z (Fin.last n))
            (decide (majJunta A (Finset.univ.filter fun i => Fin.init z i = true) = -1)))
        then (1 : ℂ) else 0) *
      (φ (Fin.init z) * minusAmp (z (Fin.last n)))) =
      ∑ p : Qubits n × Bool,
      (if y = Fin.snoc (α := fun _ => Bool) p.1 (xor p.2 (majorityBit A p.1)) then (1 : ℂ) else 0) *
      (φ p.1 * minusAmp p.2) := by
    refine Fintype.sum_equiv (qubitsSnocEquiv n) _ _ fun z => ?_
    dsimp only [qubitsSnocEquiv]
    change (if y = Fin.snoc (α := fun _ => Bool) (Fin.init z)
        (xor (z (Fin.last n))
          (decide (majJunta A (Finset.univ.filter fun i => Fin.init z i = true) = -1)))
        then (1 : ℂ) else 0) *
        (φ (Fin.init z) * minusAmp (z (Fin.last n))) =
      (if y = Fin.snoc (α := fun _ => Bool) (Fin.init z)
        (xor (z (Fin.last n)) (majorityBit A (Fin.init z))) then (1 : ℂ) else 0) *
        (φ (Fin.init z) * minusAmp (z (Fin.last n)))
    rw [majJunta_eq_neg_one_iff]
  rw [hprod, Fintype.sum_prod_type]
  rw [Finset.sum_eq_single (Fin.init y)]
  · rw [Finset.sum_eq_single (xor (y (Fin.last n)) (majorityBit A (Fin.init y)))]
    · have heq : y = Fin.snoc (α := fun _ => Bool) (Fin.init y)
          (xor (xor (y (Fin.last n)) (majorityBit A (Fin.init y))) (majorityBit A (Fin.init y))) := by
        rw [Bool.xor_assoc, Bool.xor_self, Bool.xor_false, Fin.snoc_init_self]
      rw [if_pos heq, one_mul]
      rw [Finset.sum_eq_single (Fin.init y)]
      · cases majorityBit A (Fin.init y)
        · simp
        · simp [minusAmp_neg]
      · intro x _ hx; simp [hx.symm]
      · simp
    · intro b _ hb
      have hne : y ≠ Fin.snoc (α := fun _ => Bool) (Fin.init y)
          (xor b (majorityBit A (Fin.init y))) := by
        intro h
        have hl := congrFun h (Fin.last n)
        simp only [Fin.snoc_last] at hl
        exact hb (by rw [hl, Bool.xor_assoc, Bool.xor_self, Bool.xor_false])
      simp [hne]
    · simp
  · intro x _ hx
    refine Finset.sum_eq_zero fun b _ => ?_
    have hne : y ≠ Fin.snoc (α := fun _ => Bool) x (xor b (majorityBit A x)) := by
      intro h
      apply hx
      have hi := congrArg Fin.init h
      simpa using hi.symm
    simp [hne]
  · simp

private noncomputable def phaseCtrlOracle {M n : ℕ} (A : Finset (Fin n)) (ctrl : Fin M)
    (regQ : Fin n ↪ Fin M) : Matrix (Qubits M) (Qubits M) ℂ :=
  Matrix.diagonal fun x => if x ctrl && majorityBit A (x ∘ regQ) then (-1 : ℂ) else 1

private lemma oracleStep_ctrl_query_apply_eq {M n : ℕ} (A : Finset (Fin n)) (ctrl : Fin M)
    (regQ : Fin n ↪ Fin M)
    (wires : Fin (n + 1) ↪ Fin (M + 1))
    (hw_init : ∀ i : Fin n, wires i.castSucc = (regQ i).castSucc)
    (hw_last : wires (Fin.last n) = Fin.last M)
    (hc : ∀ c, some ctrl.castSucc = some c → c ∉ Set.range wires)
    (y z : Qubits (M + 1)) :
    OracleStep.mat (S := {g : Gate | g.IsUnitary}) (r := 1) (a := fun _ => n + 1)
      (fun _ => majOracle A) (.query 0 false (some ctrl.castSucc) wires hc) y z =
    if z = Fin.snoc (α := fun _ => Bool) (Fin.init y)
      (xor (y (Fin.last M)) (Fin.init y ctrl && majorityBit A (Fin.init y ∘ regQ)))
    then 1 else 0 := by
  let w' : Fin (n + 2) ↪ Fin (M + 1) :=
    ⟨Fin.cons ctrl.castSucc wires, Fin.cons_injective_iff.2 ⟨hc ctrl.castSucc rfl, wires.injective⟩⟩
  change embedOp (controlledQubits (majOracle A)) w' y z = _
  simp only [embedOp, Matrix.of_apply, controlledQubits, Matrix.submatrix_apply, controlled]
  have hw'0 : ∀ u : Qubits (M + 1), (u ∘ w') 0 = u ctrl.castSucc := fun _ => rfl
  have hw'_tail : ∀ u : Qubits (M + 1), Fin.tail (u ∘ w') = u ∘ wires := fun u => by
    funext i; rfl
  have hw_init_comp : ∀ u : Qubits (M + 1), Fin.init (u ∘ wires) = Fin.init u ∘ regQ := fun u => by
    funext i; simp [Fin.init, hw_init i]
  have hw_last_comp : ∀ u : Qubits (M + 1), (u ∘ wires) (Fin.last n) = u (Fin.last M) := fun u => by
    simp [hw_last]
  by_cases hz_eq : z = Fin.snoc (α := fun _ => Bool) (Fin.init y)
      (xor (y (Fin.last M)) (Fin.init y ctrl && majorityBit A (Fin.init y ∘ regQ)))
  · rw [if_pos hz_eq]
    have hoff : ∀ a : Fin (M + 1), a ∉ Set.range w' → y a = z a := by
      intro a ha
      rw [hz_eq]
      refine Fin.lastCases ?_ ?_ a ha
      · intro hl
        exfalso
        apply hl
        refine ⟨(Fin.last n).succ, ?_⟩
        simp [w', hw_last]
      · intro i _
        simp [Fin.snoc_castSucc, Fin.init]
    rw [if_pos hoff]
    have hctrl_yz : y ctrl.castSucc = z ctrl.castSucc := by
      rw [hz_eq, Fin.snoc_castSucc]
      rfl
    simp only [hw'0, hw'_tail, if_pos hctrl_yz]
    cases hcval : y ctrl.castSucc
    · simp only [Bool.false_eq_true, ↓reduceIte, Matrix.one_apply, hw'_tail]
      have hyw : y ∘ wires = z ∘ wires := by
        funext j
        refine Fin.lastCases ?_ ?_ j
        · simp [hw_last, hz_eq, hcval, Fin.init]
        · intro i
          simp [hw_init i, hz_eq, Fin.init]
      rw [if_pos hyw]
    · simp only [↓reduceIte, majOracle, Matrix.of_apply, majJunta_eq_neg_one_iff]
      have hmaj : y ∘ wires = Fin.snoc (α := fun _ => Bool) (Fin.init (z ∘ wires))
          (xor ((z ∘ wires) (Fin.last n)) (majorityBit A (Fin.init (z ∘ wires)))) := by
        funext j
        refine Fin.lastCases ?_ ?_ j
        · simp only [hw_last_comp, hw_init_comp, hz_eq, Fin.snoc_last, Fin.init_snoc]
          simp [Fin.init, hcval]
        · intro i
          simp only [Function.comp_apply, hw_init i, Fin.snoc_castSucc, hw_init_comp, hz_eq,
            Fin.init_def]
      rw [if_pos hmaj]
  · rw [if_neg hz_eq]
    by_cases hoff : ∀ a : Fin (M + 1), a ∉ Set.range w' → y a = z a
    · rw [if_pos hoff]
      simp only [hw'0, hw'_tail]
      by_cases hctrl_yz : y ctrl.castSucc = z ctrl.castSucc
      · rw [if_pos hctrl_yz]
        have not_mem_w' : ∀ i : Fin M, i ≠ ctrl → (∀ q, regQ q ≠ i) → i.castSucc ∉ Set.range w' := by
          intro i hi hq ⟨x, hx⟩
          refine Fin.cases ?_ ?_ x hx
          · intro h0
            exact hi (Fin.ext (by
              have h0' := congrArg Fin.val h0
              simpa [w'] using h0'.symm))
          · intro j hj
            refine Fin.lastCases ?_ ?_ j hj
            · intro hl
              have hl' := congrArg Fin.val hl
              simp [w', hw_last] at hl'
              omega
            · intro q hq'
              apply hq q
              exact Fin.ext (by
                have hq'' := congrArg Fin.val hq'
                simpa [w', hw_init q] using hq'')
        cases hcval : y ctrl.castSucc
        · simp only [Bool.false_eq_true, ↓reduceIte, Matrix.one_apply]
          rw [if_neg]
          intro hyw
          apply hz_eq
          funext a
          refine Fin.lastCases ?_ ?_ a
          · have hl := congrFun hyw (Fin.last n)
            change (y ∘ wires) (Fin.last n) = (z ∘ wires) (Fin.last n) at hl
            rw [hw_last_comp y, hw_last_comp z] at hl
            have hcval' : Fin.init y ctrl = false := by simpa [Fin.init] using hcval
            simp [Fin.snoc_last, hcval', hl]
          · intro i
            by_cases hi : i = ctrl
            · subst hi; simpa [Fin.snoc_castSucc, Fin.init] using hctrl_yz.symm
            · by_cases hq : ∃ q, regQ q = i
              · obtain ⟨q, rfl⟩ := hq
                have hqi := congrFun hyw q.castSucc
                change y (wires q.castSucc) = z (wires q.castSucc) at hqi
                rw [hw_init q] at hqi
                simpa [Fin.snoc_castSucc, Fin.init] using hqi.symm
              · have hq' : ∀ q, regQ q ≠ i := fun q h => hq ⟨q, h⟩
                simpa [Fin.snoc_castSucc, Fin.init] using (hoff i.castSucc (not_mem_w' i hi hq')).symm
        · simp only [↓reduceIte, majOracle, Matrix.of_apply, majJunta_eq_neg_one_iff]
          rw [if_neg]
          intro hmaj
          apply hz_eq
          funext a
          refine Fin.lastCases ?_ ?_ a
          · have hl := congrFun hmaj (Fin.last n)
            simp only [hw_last_comp, Fin.snoc_last, hw_init_comp] at hl
            have hinit_q : Fin.init z ∘ regQ = Fin.init y ∘ regQ := by
              funext q
              have hq := congrFun hmaj q.castSucc
              simp only [Function.comp_apply, hw_init q, Fin.snoc_castSucc, hw_init_comp] at hq
              exact hq.symm
            rw [hl, hinit_q]
            have hcval' : Fin.init y ctrl = true := by simpa [Fin.init] using hcval
            simp only [Fin.snoc_last, hcval', Bool.true_and,
              Bool.xor_assoc, Bool.xor_self, Bool.xor_false]
          · intro i
            by_cases hi : i = ctrl
            · subst hi; simpa [Fin.snoc_castSucc, Fin.init] using hctrl_yz.symm
            · by_cases hq : ∃ q, regQ q = i
              · obtain ⟨q, rfl⟩ := hq
                have hqi := congrFun hmaj q.castSucc
                simp only [Function.comp_apply, hw_init q, Fin.snoc_castSucc, hw_init_comp] at hqi
                simpa [Fin.snoc_castSucc, Fin.init] using hqi.symm
              · have hq' : ∀ q, regQ q ≠ i := fun q h => hq ⟨q, h⟩
                simpa [Fin.snoc_castSucc, Fin.init] using (hoff i.castSucc (not_mem_w' i hi hq')).symm
      · rw [if_neg hctrl_yz]
    · rw [if_neg hoff]

private lemma act_ctrl_majOracle_withMinus {M n : ℕ} (A : Finset (Fin n)) (ctrl : Fin M)
    (regQ : Fin n ↪ Fin M) (wires : Fin (n + 1) ↪ Fin (M + 1))
    (hw_init : ∀ i : Fin n, wires i.castSucc = (regQ i).castSucc)
    (hw_last : wires (Fin.last n) = Fin.last M)
    (hc : ∀ c, some ctrl.castSucc = some c → c ∉ Set.range wires)
    (φ : EuclideanSpace ℂ (Qubits M)) :
    act (OracleStep.mat (S := {g : Gate | g.IsUnitary}) (r := 1) (a := fun _ => n + 1)
      (fun _ => majOracle A) (.query 0 false (some ctrl.castSucc) wires hc)) (withMinus φ) =
    withMinus (act (phaseCtrlOracle A ctrl regQ) φ) := by
  ext y
  simp only [act, WithLp.ofLp_toLp, Matrix.mulVec, dotProduct, withMinus, phaseCtrlOracle,
    Matrix.diagonal_apply]
  simp_rw [oracleStep_ctrl_query_apply_eq A ctrl regQ wires hw_init hw_last hc]
  let bit := Fin.init y ctrl && majorityBit A (Fin.init y ∘ regQ)
  rw [Finset.sum_eq_single (Fin.snoc (α := fun _ => Bool) (Fin.init y) (xor (y (Fin.last M)) bit))]
  · rw [if_pos rfl, one_mul, Fin.init_snoc, Fin.snoc_last]
    rw [Finset.sum_eq_single (Fin.init y)]
    · by_cases hbit : bit = true
      · have h1 : Fin.init y ctrl = true := (Bool.and_eq_true _ _).mp hbit |>.1
        have h2 : majorityBit A (Fin.init y ∘ regQ) = true := (Bool.and_eq_true _ _).mp hbit |>.2
        rw [hbit, Bool.xor_true, minusAmp_neg]
        simp only [h1, h2, Bool.true_and, ↓reduceIte]
        ring
      · have hbitf : bit = false := Bool.eq_false_iff.mpr hbit
        rw [hbitf, Bool.xor_false]
        have hbitf' : (Fin.init y ctrl && majorityBit A (Fin.init y ∘ regQ)) = false := hbitf
        simp only [hbitf', Bool.false_eq_true, ↓reduceIte]
        ring
    · intro x _ hx; simp [hx.symm]
    · simp
  · intro z _ hz
    have hz' : z ≠ Fin.snoc (α := fun _ => Bool) (Fin.init y)
        (xor (y (Fin.last M)) (Fin.init y ctrl && majorityBit A (Fin.init y ∘ regQ))) := hz
    rw [if_neg hz', zero_mul]
  · simp

private lemma hadamardN_mul_self (n : ℕ) : hadamardN n * hadamardN n = 1 := by
  ext y z
  have h2 : (((Real.sqrt 2 : ℝ)⁻¹ ^ n : ℝ) : ℂ) * (((Real.sqrt 2 : ℝ)⁻¹ ^ n : ℝ) : ℂ) =
      ((2 : ℂ)⁻¹) ^ n := by
    rw [← Complex.ofReal_mul, ← sq, ← pow_mul, mul_comm n 2, pow_mul, inv_pow,
      Real.sq_sqrt (by norm_num)]
    push_cast
    rfl
  have hdot : ∀ i : Qubits n, xor (dotBits i y) (dotBits i z) = dotBits i (y + z) := by
    intro i
    simp only [dotBits]
    change (∑ k, (i k && y k)) + (∑ k, (i k && z k)) = ∑ k, (i k && (y + z) k)
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [Pi.add_apply]
    cases i k <;> cases y k <;> cases z k <;> rfl
  have hsum : ∑ i : Qubits n, (if dotBits i (y + z) then (-1 : ℂ) else 1) =
      if y = z then (2 ^ n : ℂ) else 0 := by
    by_cases hyz : y = z
    · subst hyz
      have h0 : ∀ k, (y + y) k = false := fun k => by simp only [Pi.add_apply]; cases y k <;> rfl
      have hdot0 : ∀ i : Qubits n, dotBits i (y + y) = false := fun i => by
        simp only [dotBits, h0, Bool.and_false]
        exact (Finset.sum_const_zero (s := Finset.univ) : (∑ _ : Fin n, (0 : Bool)) = 0)
      simp [hdot0]
    · rw [if_neg hyz]
      have hne : ∃ r : Fin n, (y + z) r = true := by
        by_contra hc
        push Not at hc
        apply hyz
        funext r
        have hr := hc r
        cases hy : y r <;> cases hz : z r <;> simp_all [Pi.add_apply]
      obtain ⟨r, hr⟩ := hne
      let flip : Qubits n ≃ Qubits n :=
        { toFun := fun i => Function.update i r (!(i r))
          invFun := fun i => Function.update i r (!(i r))
          left_inv := fun i => by
            funext k
            by_cases hk : k = r <;> simp [Function.update, hk]
          right_inv := fun i => by
            funext k
            by_cases hk : k = r <;> simp [Function.update, hk] }
      have hflip : ∀ i : Qubits n, dotBits (flip i) (y + z) = !(dotBits i (y + z)) := by
        intro i
        simp only [dotBits]
        rw [← Finset.add_sum_erase _ _ (Finset.mem_univ r),
          ← Finset.add_sum_erase (Finset.univ) (fun k => i k && (y + z) k) (Finset.mem_univ r)]
        have hrest : ∑ k ∈ Finset.univ.erase r, (flip i k && (y + z) k) =
            ∑ k ∈ Finset.univ.erase r, (i k && (y + z) k) := by
          refine Finset.sum_congr rfl fun k hk => ?_
          have hkr : k ≠ r := (Finset.mem_erase.mp hk).1
          simp [flip, Function.update_of_ne hkr]
        rw [hrest]
        have hhead : (flip i r && (y + z) r) = !(i r && (y + z) r) := by
          simp [flip, hr]
        rw [hhead]
        cases (i r && (y + z) r) <;> cases (∑ k ∈ Finset.univ.erase r, (i k && (y + z) k)) <;> decide
      have hpair : ∑ i : Qubits n, (if dotBits (flip i) (y + z) then (-1 : ℂ) else 1) =
          ∑ i : Qubits n, (if dotBits i (y + z) then (-1 : ℂ) else 1) :=
        Fintype.sum_equiv flip _ _ fun _ => rfl
      have hneg : ∑ i : Qubits n, (if dotBits (flip i) (y + z) then (-1 : ℂ) else 1) =
          - ∑ i : Qubits n, (if dotBits i (y + z) then (-1 : ℂ) else 1) := by
        rw [← Finset.sum_neg_distrib]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [hflip i]
        cases dotBits i (y + z) <;> simp
      have h2s : (2 : ℂ) * ∑ i : Qubits n, (if dotBits i (y + z) then (-1 : ℂ) else 1) = 0 := by
        calc (2 : ℂ) * ∑ i : Qubits n, _
            = ∑ i : Qubits n, _ + ∑ i : Qubits n, _ := two_mul _
          _ = ∑ i : Qubits n, (if dotBits i (y + z) then (-1 : ℂ) else 1) +
              ∑ i : Qubits n, (if dotBits (flip i) (y + z) then (-1 : ℂ) else 1) := by rw [hpair]
          _ = 0 := by rw [hneg, add_neg_cancel]
      exact (mul_eq_zero.mp h2s).resolve_left (by norm_num)
  simp only [Matrix.mul_apply, hadamardN, Matrix.of_apply, Matrix.one_apply]
  have hterm : ∀ i : Qubits n,
      (if dotBits i y then -(((Real.sqrt 2 : ℝ)⁻¹ ^ n : ℝ) : ℂ) else (((Real.sqrt 2 : ℝ)⁻¹ ^ n : ℝ) : ℂ)) *
      (if dotBits z i then -(((Real.sqrt 2 : ℝ)⁻¹ ^ n : ℝ) : ℂ) else (((Real.sqrt 2 : ℝ)⁻¹ ^ n : ℝ) : ℂ)) =
      ((2 : ℂ)⁻¹) ^ n * (if dotBits i (y + z) then (-1 : ℂ) else 1) := by
    intro i
    have hdz : dotBits z i = dotBits i z := by simp only [dotBits, Bool.and_comm]
    rw [hdz, ← hdot i]
    cases dotBits i y <;> cases dotBits i z <;> simp [← h2]
  simp_rw [hterm, ← Finset.mul_sum, hsum]
  by_cases hyz : y = z
  · simp [hyz, inv_pow, pow_ne_zero n (by norm_num : (2 : ℂ) ≠ 0)]
  · simp [hyz]

private lemma hadamardN_mem_unitaryGroup (n : ℕ) :
    hadamardN n ∈ Matrix.unitaryGroup (Qubits n) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff, hadamardN_star, hadamardN_mul_self]

private lemma gate_ofMatrix1_isUnitary {M : Matrix Bool Bool ℂ}
    (hM : M ∈ Matrix.unitaryGroup Bool ℂ) : (Gate.ofMatrix1 M).IsUnitary := by
  dsimp only [Gate.IsUnitary, Gate.ofMatrix1]
  rw [Matrix.mem_unitaryGroup_iff]
  let e : Qubits 1 ≃ Bool :=
    { toFun := fun b => b 0
      invFun := fun x _ => x
      left_inv := fun b => funext fun i => by fin_cases i; rfl
      right_inv := fun _ => rfl }
  have hstar : star (M.submatrix (fun b : Qubits 1 => b 0) (fun b : Qubits 1 => b 0)) =
      (star M).submatrix e e := by
    ext i j; simp [e, Matrix.star_apply]
  have hmul : (M.submatrix (fun b : Qubits 1 => b 0) (fun b : Qubits 1 => b 0)) *
      (star M).submatrix e e = (M * star M).submatrix e e := by
    ext i j
    simp only [Matrix.mul_apply, Matrix.submatrix_apply, e]
    exact Fintype.sum_equiv e _ _ (fun _ => rfl)
  rw [hstar, hmul, Matrix.mem_unitaryGroup_iff.mp hM]
  ext i j
  by_cases hij : i = j
  · subst hij; simp [e]
  · have he : e i ≠ e j := fun h => hij (e.injective h)
    simp [Matrix.submatrix_apply, hij, he]

private lemma hadamard_mul_pauliX_mem_unitaryGroup :
    hadamard * pauliX ∈ Matrix.unitaryGroup Bool ℂ := by
  have hH : hadamard ∈ Matrix.unitaryGroup Bool ℂ := by
    rw [Matrix.mem_unitaryGroup_iff]
    have hHs : star hadamard = hadamard := by
      ext a b
      cases a <;> cases b <;> simp [hadamard, Matrix.star_apply, Complex.conj_ofReal]
    rw [hHs, hadamard_mul_self]
  have hX : pauliX ∈ Matrix.unitaryGroup Bool ℂ := by
    rw [Matrix.mem_unitaryGroup_iff]
    have hXs : star pauliX = pauliX := by
      ext a b; cases a <;> cases b <;> simp [pauliX, Matrix.star_apply]
    have hXX : pauliX * pauliX = 1 := by
      ext a b; cases a <;> cases b <;> simp [pauliX, Matrix.mul_apply]
    rw [hXs, hXX]
  exact Submonoid.mul_mem _ hH hX

private def prepareMinusWires (M : ℕ) : Fin 1 ↪ Fin (M + 1) :=
  ⟨fun _ => Fin.last M,
    fun u v _ => Fin.ext (Nat.lt_one_iff.mp u.2 |>.trans (Nat.lt_one_iff.mp v.2).symm)⟩

private noncomputable def prepareMinusStep {r : ℕ} {a : Fin r → ℕ} (M : ℕ) :
    OracleStep {g : Gate | g.IsUnitary} a (M + 1) :=
  OracleStep.gate
    ⟨Gate.ofMatrix1 (hadamard * pauliX), gate_ofMatrix1_isUnitary hadamard_mul_pauliX_mem_unitaryGroup,
      prepareMinusWires M⟩

private lemma act_prepareMinusStep {r : ℕ} {a : Fin r → ℕ} (M : ℕ)
    (orc : (k : Fin r) → Matrix (Qubits (a k)) (Qubits (a k)) ℂ) :
    act (OracleStep.mat orc (prepareMinusStep M)) (zeroKet (M + 1)) = withMinus (zeroKet M) := by
  change act (embedOp ((hadamard * pauliX).submatrix (fun b => b 0) (fun b => b 0))
    (prepareMinusWires M)) (zeroKet (M + 1)) = withMinus (zeroKet M)
  ext y
  simp only [act, WithLp.ofLp_toLp, Matrix.mulVec, dotProduct, embedOp, Matrix.of_apply,
    Matrix.submatrix_apply, zeroKet, ket, withMinus]
  rw [Finset.sum_eq_single (fun _ : Fin (M + 1) => false)]
  · simp only [PiLp.single_apply, ↓reduceIte, mul_one]
    by_cases hinit : Fin.init y = fun _ : Fin M => false
    · have hcond : ∀ b : Fin (M + 1), b ∉ Set.range (prepareMinusWires M) → y b = false := by
        intro b hb
        have hne : b ≠ Fin.last M := by
          intro heq
          apply hb
          exact ⟨0, heq.symm⟩
        rcases Fin.exists_castSucc_eq.mpr hne with ⟨i, rfl⟩
        exact congrFun hinit i
      rw [if_pos hcond, if_pos hinit, one_mul]
      change (hadamard * pauliX) (y (Fin.last M)) false = minusAmp (y (Fin.last M))
      cases y (Fin.last M) <;>
        simp [hadamard, pauliX, Matrix.mul_apply, minusAmp]
    · have hcond : ¬ ∀ b : Fin (M + 1), b ∉ Set.range (prepareMinusWires M) → y b = false := by
        intro h
        apply hinit
        funext i
        apply h i.castSucc
        rintro ⟨_, h0⟩
        exact Fin.castSucc_ne_last i h0.symm
      rw [if_neg hcond, if_neg hinit, zero_mul]
  · intro z _ hz
    simp only [PiLp.single_apply, if_neg hz, mul_zero]
  · intro hmem; exact absurd (Finset.mem_univ _) hmem

private lemma oracleCircuit_unitary_append {S : Set Gate} {r : ℕ} {a : Fin r → ℕ} {m : ℕ}
    (c₁ c₂ : OracleCircuit S a m)
    (orc : (k : Fin r) → Matrix (Qubits (a k)) (Qubits (a k)) ℂ) :
    (c₁ ++ c₂).unitary orc = c₂.unitary orc * c₁.unitary orc := by
  simp [OracleCircuit.unitary, List.map_append, List.reverse_append, List.prod_append]

private lemma oracleCircuit_queryCount_append {S : Set Gate} {r : ℕ} {a : Fin r → ℕ} {m : ℕ}
    (c₁ c₂ : OracleCircuit S a m) (k : Fin r) :
    (c₁ ++ c₂).queryCount k = c₁.queryCount k + c₂.queryCount k := by
  simp [OracleCircuit.queryCount, List.countP_append]

private theorem k_eq_one_case (n : ℕ) (_hn : 1 ≤ n) :
    queryComplexity n (fun A => A.card = 1) ≤ 1 := by
  let g_had : GateApp {g : Gate | g.IsUnitary} (n + 1) :=
    ⟨⟨n, hadamardN n⟩, hadamardN_mem_unitaryGroup n, Fin.castAddEmb 1⟩
  let s_tgt : OracleStep {g : Gate | g.IsUnitary} (fun _ : Fin 1 => n + 1) (n + 1) :=
    prepareMinusStep n
  let s_had : OracleStep {g : Gate | g.IsUnitary} (fun _ : Fin 1 => n + 1) (n + 1) :=
    OracleStep.gate g_had
  let s_qry : OracleStep {g : Gate | g.IsUnitary} (fun _ : Fin 1 => n + 1) (n + 1) :=
    .query 0 false none (Function.Embedding.refl _) (by simp)
  let c : OracleCircuit {g : Gate | g.IsUnitary} (fun _ : Fin 1 => n + 1) (n + 1) :=
    [s_tgt, s_had, s_qry, s_had]
  refine Nat.sInf_le ⟨n + 1, c, Fin.castAddEmb 1, ?_, ?_⟩
  · simp [c, OracleCircuit.queryCount, OracleStep.IsQueryTo, s_tgt, prepareMinusStep, s_had, s_qry]
  · intro A hA
    obtain ⟨i₀, rfl⟩ := Finset.card_eq_one.mp hA
    have hstep1 : act (OracleStep.mat (fun _ => majOracle {i₀}) s_tgt)
        (zeroKet (n + 1)) = withMinus (zeroKet n) :=
      act_prepareMinusStep n (fun _ => majOracle {i₀})
    have hstep2 : act (OracleStep.mat (fun _ => majOracle {i₀}) s_had)
        (withMinus (zeroKet n)) = withMinus (act (hadamardN n) (zeroKet n)) := by
      simpa [OracleStep.mat, s_had, g_had] using act_embedOp_castSucc_withMinus (hadamardN n) (zeroKet n)
    have hstep3 : act (OracleStep.mat (fun _ => majOracle {i₀}) s_qry)
        (withMinus (act (hadamardN n) (zeroKet n))) =
        withMinus (act (phaseOracle (majorityBit {i₀})) (act (hadamardN n) (zeroKet n))) := by
      have hem : embedOp (majOracle {i₀}) (Function.Embedding.refl _) = majOracle {i₀} := by
        ext y z
        simp [embedOp]
        rfl
      simpa [OracleStep.mat, s_qry, hem] using
        act_majOracle_withMinus {i₀} (act (hadamardN n) (zeroKet n))
    have hstep4 : act (OracleStep.mat (fun _ => majOracle {i₀}) s_had)
        (withMinus (act (phaseOracle (majorityBit {i₀})) (act (hadamardN n) (zeroKet n)))) =
        withMinus (act (hadamardN n) (act (phaseOracle (majorityBit {i₀})) (act (hadamardN n) (zeroKet n)))) := by
      simpa [OracleStep.mat, s_had, g_had] using
        act_embedOp_castSucc_withMinus (hadamardN n)
          (act (phaseOracle (majorityBit {i₀})) (act (hadamardN n) (zeroKet n)))
    let e : Qubits n := fun i => decide (i = i₀)
    have hphase_eq : act (phaseOracle (majorityBit {i₀})) (act (hadamardN n) (zeroKet n)) =
        -(act (hadamardN n) (ket e)) := by
      ext x
      have hmaj : majorityBit {i₀} x = !(x i₀) := by
        simp only [majorityBit, Finset.card_singleton]
        by_cases hx : x i₀ = true <;> simp [hx]
      have hdot_e : dotBits e x = x i₀ := by
        simp only [dotBits, e]
        rw [Finset.sum_eq_single i₀]
        · simp
        · intro k _ hk; simp [hk]; rfl
        · simp
      have hdot_0 : dotBits (fun _ : Fin n => false) x = false := by
        simp only [dotBits, Bool.false_and]
        exact (Finset.sum_const_zero (s := Finset.univ) : (∑ _ : Fin n, (0 : Bool)) = 0)
      simp only [act, PiLp.neg_apply, WithLp.ofLp_toLp, Matrix.mulVec, dotProduct, phaseOracle,
        Matrix.diagonal_apply, zeroKet, ket, PiLp.single_apply]
      rw [Finset.sum_eq_single x]
      · rw [Finset.sum_eq_single (fun _ : Fin n => false), Finset.sum_eq_single e]
        · simp only [hadamardN, Matrix.of_apply, hdot_0, hdot_e, hmaj]
          cases x i₀ <;> simp
        · intro k _ hk; simp [hk]
        · simp
        · intro k _ hk; simp [hk]
        · simp
      · intro k _ hk; simp [hk.symm]
      · simp
    have hact_had_neg : act (hadamardN n) (-(act (hadamardN n) (ket e))) = -(ket e) := by
      have hlin : act (hadamardN n) (-(act (hadamardN n) (ket e))) =
          -(act (hadamardN n * hadamardN n) (ket e)) := by
        ext y
        simp [act, Matrix.mulVec_neg, Matrix.mulVec_mulVec]
      rw [hlin, hadamardN_mul_self]
      simp [act]
    have hfinal : act (c.unitary fun _ => majOracle {i₀}) (zeroKet (n + 1)) =
        withMinus (-(ket e)) := by
      have hunit : c.unitary (fun _ => majOracle {i₀}) =
          OracleStep.mat (fun _ => majOracle {i₀}) s_had *
          (OracleStep.mat (fun _ => majOracle {i₀}) s_qry *
          (OracleStep.mat (fun _ => majOracle {i₀}) s_had *
          OracleStep.mat (fun _ => majOracle {i₀}) s_tgt)) := by
        dsimp only [c, OracleCircuit.unitary]
        simp only [List.map_cons, List.map_nil, List.reverse_cons, List.reverse_nil,
          List.nil_append, List.cons_append, List.prod_cons, List.prod_nil, mul_one]
      rw [hunit, act_mul, act_mul, act_mul, hstep1, hstep2, hstep3, hstep4, hphase_eq, hact_had_neg]
    rw [hfinal]
    have hprob_eq : open Classical in
        probEvent (withMinus (-ket e))
          (fun z => ∀ i : Fin n, z (Fin.castAddEmb 1 i) = decide (i ∈ ({i₀} : Finset (Fin n)))) =
        probEvent (withMinus (-ket e)) (fun z => Fin.init z = e) := by
      apply probEvent_congr
      intro z
      constructor
      · intro h; funext i
        have hi := h i
        simp only [Finset.mem_singleton] at hi
        exact hi
      · intro h i
        have hi := congrFun h i
        simp only [Finset.mem_singleton]
        exact hi
    change open Classical in
      probEvent (withMinus (-ket e))
        (fun z => ∀ i : Fin n, z (Fin.castAddEmb 1 i) = decide (i ∈ ({i₀} : Finset (Fin n)))) ≥ 2 / 3
    rw [hprob_eq]
    classical
    rw [probEvent_withMinus (-(ket e)) (fun x => x = e)]
    simp only [probEvent, prob, ket, EuclideanSpace.inner_single_left]
    rw [Finset.sum_eq_single e]
    · simp; norm_num
    · intro x hx hne
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
      exact absurd hx hne
    · intro he_mem
      exfalso; apply he_mem; simp

end CircuitHelpers

section TransducerToCircuit

private lemma diag_pm1_mem_unitaryGroup {α : Type*} [Fintype α] [DecidableEq α] (d : α → ℂ)
    (hd : ∀ x, d x = 1 ∨ d x = -1) : Matrix.diagonal d ∈ Matrix.unitaryGroup α ℂ := by
  rw [Matrix.mem_unitaryGroup_iff]
  ext x y
  simp only [Matrix.mul_apply, Matrix.star_apply, Matrix.diagonal_apply, Matrix.one_apply]
  rw [Finset.sum_eq_single x]
  · by_cases hxy : x = y
    · subst hxy
      rcases hd x with hx | hx <;> simp [hx]
    · simp [hxy, ne_comm.mp hxy]
  · intro z _ hz
    simp [hz.symm]
  · simp

private lemma norm_sum_ket {α κ : Type*} [Fintype α] [DecidableEq α] [Fintype κ]
    (f : κ ↪ α) : ‖∑ j : κ, ket (f j)‖ ^ 2 = (Fintype.card κ : ℝ) := by
  have h : inner ℂ (∑ j : κ, ket (f j)) (∑ j : κ, ket (f j)) = (Fintype.card κ : ℂ) := by
    simp only [sum_inner, inner_sum, ket, EuclideanSpace.inner_single_left, PiLp.single_apply,
      map_one, one_mul]
    trans ∑ _ : κ, (1 : ℂ)
    · refine Finset.sum_congr rfl fun j _ => ?_
      rw [Finset.sum_eq_single j]
      · simp
      · intro j' _ hj'
        simp [hj']
      · simp
    · simp
  rw [inner_self_eq_norm_sq_to_K] at h
  apply Complex.ofReal_injective
  simpa [Complex.ofReal_pow] using h

private lemma probEvent_ge_of_norm_sub_sq {α : Type*} [Fintype α] [DecidableEq α]
    (finalVec idealVec : EuclideanSpace ℂ α) (P : α → Prop) [DecidablePred P]
    (hnorm : ‖finalVec‖ = 1)
    (hsupp : ∀ x, ¬ P x → idealVec x = 0)
    (hdist : ‖finalVec - idealVec‖ ^ 2 ≤ (1 / 3 : ℝ)) :
    probEvent finalVec P ≥ 2 / 3 := by
  have h1 : ‖finalVec‖ ^ 2 = probEvent finalVec P +
      ∑ x ∈ Finset.univ.filter (fun x => ¬ P x), ‖finalVec x‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    have hsplit := (Finset.sum_filter_add_sum_filter_not Finset.univ P (fun x => ‖finalVec x‖ ^ 2)).symm
    rw [hsplit]
    congr 1
    simp only [probEvent, prob, ket, EuclideanSpace.inner_single_left, map_one, one_mul]
  have h2 : ∑ x ∈ Finset.univ.filter (fun x => ¬ P x), ‖finalVec x‖ ^ 2 ≤
      ‖finalVec - idealVec‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    have hrewrite : ∑ x ∈ Finset.univ.filter (fun x => ¬ P x), ‖finalVec x‖ ^ 2 =
        ∑ x ∈ Finset.univ.filter (fun x => ¬ P x), ‖(finalVec - idealVec) x‖ ^ 2 := by
      refine Finset.sum_congr rfl fun x hx => ?_
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
      simp [hsupp x hx]
    rw [hrewrite]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun _ _ _ => sq_nonneg _
  rw [hnorm, one_pow] at h1
  linarith

private theorem dual_adversary_to_circuit {n k : ℕ} (hk : 2 ≤ k) (hkn : k ≤ n)
    {T : ℝ} (X : Qubits n → Matrix (BoundedSupports n k) (BoundedSupports n k) ℝ)
    (hfeas : DualFeasible (fun A : BoundedSupports n k => A.1) X)
    (hcost : DualCostAtMost X T) :
    ∃ (m : ℕ) (c : OracleCircuit {g : Gate | g.IsUnitary} (fun _ : Fin 1 => n + 1) m)
      (out : Fin n ↪ Fin m),
      c.queryCount 0 ≤ Nat.ceil (6 * T) + 1 ∧
      ∀ A : Finset (Fin n), (1 ≤ A.card ∧ A.card ≤ k) →
        open Classical in
        probEvent (act (c.unitary fun _ => majOracle A) (zeroKet m))
          (fun z => ∀ i : Fin n, z (out i) = decide (i ∈ A)) ≥ 2 / 3 := by
  classical
  let ι := BoundedSupports n k
  have hne_ι : Nonempty ι := ⟨⟨{⟨0, by omega⟩}, Finset.singleton_nonempty _, by simp; omega⟩⟩
  let K : ℕ := Nat.ceil (6 * T) + 1
  have hK_pos : 0 < K := Nat.succ_pos _
  have hK_real_pos : (0 : ℝ) < (K : ℝ) := by exact_mod_cast hK_pos
  have h6T_le_K : 6 * T ≤ (K : ℝ) := by
    have hceil : 6 * T ≤ (Nat.ceil (6 * T) : ℝ) := Nat.le_ceil (6 * T)
    have hK_cast : (K : ℝ) = (Nat.ceil (6 * T) : ℝ) + 1 := by push_cast [K]; rfl
    linarith
  have hgramS : ∀ S : Qubits n, ∃ w : ι → EuclideanSpace ℂ ι,
      ∀ A B : ι, inner ℂ (w A) (w B) = (X S A B : ℂ) :=
    fun S => gram_vectors_of_posSemidef (X S) (hfeas.1 S)
  choose wVec hwVec using hgramS
  let wCat : ι → EuclideanSpace ℂ (Qubits n × ι) := fun A =>
    WithLp.toLp 2 fun p : Qubits n × ι => (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) * wVec p.1 A p.2
  have hwCat_inner : ∀ A B : ι,
      inner ℂ (wCat A) (wCat B) = ∑ S : Qubits n, ((1 / 2 : ℝ) : ℂ) * (X S A B : ℂ) := by
    intro A B
    rw [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun S _ => ?_
    have hinv2 : (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) * (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) = ((1 / 2 : ℝ) : ℂ) := by
      rw [← Complex.ofReal_mul, ← sq, inv_pow, Real.sq_sqrt (by norm_num)]
      norm_num
    have hS : ∑ j : ι, wCat B (S, j) * starRingEnd ℂ (wCat A (S, j)) =
        ((1 / 2 : ℝ) : ℂ) * inner ℂ (wVec S A) (wVec S B) := by
      rw [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp only [wCat, map_mul, Complex.conj_ofReal]
      calc (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) * wVec S B j *
            ((((Real.sqrt 2)⁻¹ : ℝ) : ℂ) * starRingEnd ℂ (wVec S A j))
          = ((((Real.sqrt 2)⁻¹ : ℝ) : ℂ) * (((Real.sqrt 2)⁻¹ : ℝ) : ℂ)) *
              (wVec S B j * starRingEnd ℂ (wVec S A j)) := by ring
        _ = ((1 / 2 : ℝ) : ℂ) * (wVec S B j * starRingEnd ℂ (wVec S A j)) := by rw [hinv2]
        _ = ((1 / 2 : ℝ) : ℂ) * (wVec S B j * star (wVec S A j)) := rfl
    simpa [hwVec S A B] using hS
  have hwCat_norm_sq : ∀ A : ι, ‖wCat A‖ ^ 2 ≤ T / 2 := by
    intro A
    have h : inner ℂ (wCat A) (wCat A) = ∑ S : Qubits n, ((1 / 2 : ℝ) : ℂ) * (X S A A : ℂ) :=
      hwCat_inner A A
    rw [inner_self_eq_norm_sq_to_K] at h
    have hreal_c : ((‖wCat A‖ ^ 2 : ℝ) : ℂ) = (((1 / 2 : ℝ) * ∑ S : Qubits n, X S A A : ℝ) : ℂ) := by
      push_cast at h ⊢
      rw [Finset.mul_sum]
      exact h
    have hreal : ‖wCat A‖ ^ 2 = (1 / 2 : ℝ) * ∑ S : Qubits n, X S A A :=
      Complex.ofReal_injective hreal_c
    rw [hreal]
    linarith [hcost A]
  let trIdx := Option ι ⊕ (Qubits n × ι)
  let inrTr : (Qubits n × ι) ↪ trIdx := ⟨Sum.inr, Sum.inr_injective⟩
  let trPhaseOracle : ι → Matrix trIdx trIdx ℂ := fun A =>
    Matrix.diagonal fun x =>
      match x with
      | Sum.inl _ => 1
      | Sum.inr (S, _) => if majorityBit A.1 S then (-1 : ℂ) else 1
  let vPre : ι → EuclideanSpace ℂ trIdx := fun A =>
    ket (Sum.inl (none : Option ι)) + liftVec inrTr (wCat A)
  let vTr : ι → EuclideanSpace ℂ trIdx := fun A => act (trPhaseOracle A) (vPre A)
  let uTr : ι → EuclideanSpace ℂ trIdx := fun A =>
    ket (Sum.inl (some A)) + liftVec inrTr (wCat A)
  have hvTr_eval_inl : ∀ (A : ι) (opt : Option ι),
      vTr A (Sum.inl opt) = if opt = none then (1 : ℂ) else 0 := by
    intro A opt
    dsimp only [vTr, trPhaseOracle]
    rw [act_diagonal]
    have h0 : liftVec inrTr (wCat A) (Sum.inl opt) = 0 :=
      liftVec_apply_not_mem inrTr (wCat A) (by rintro ⟨w, hw⟩; exact Sum.inr_ne_inl (by exact hw))
    simp [vPre, ket, h0]
  have hvTr_eval_inr : ∀ (A : ι) (S : Qubits n) (j : ι),
      vTr A (Sum.inr (S, j)) = (if majorityBit A.1 S then (-1 : ℂ) else 1) * wCat A (S, j) := by
    intro A S j
    dsimp only [vTr, trPhaseOracle]
    rw [act_diagonal]
    change _ * (ket (Sum.inl (none : Option ι)) (Sum.inr (S, j)) + liftVec inrTr (wCat A) (inrTr (S, j))) = _
    rw [liftVec_apply_embed]
    simp [ket]
  have huTr_eval_inl : ∀ (A : ι) (opt : Option ι),
      uTr A (Sum.inl opt) = if opt = some A then (1 : ℂ) else 0 := by
    intro A opt
    have h0 : liftVec inrTr (wCat A) (Sum.inl opt) = 0 :=
      liftVec_apply_not_mem inrTr (wCat A) (by rintro ⟨w, hw⟩; exact Sum.inr_ne_inl (by exact hw))
    simp [uTr, ket, h0]
  have huTr_eval_inr : ∀ (A : ι) (S : Qubits n) (j : ι),
      uTr A (Sum.inr (S, j)) = wCat A (S, j) := by
    intro A S j
    change ket (Sum.inl (some A)) (Sum.inr (S, j)) + liftVec inrTr (wCat A) (inrTr (S, j)) = _
    rw [liftVec_apply_embed]
    simp [ket]
  have hgramTr : ∀ A B : ι, inner ℂ (vTr A) (vTr B) = inner ℂ (uTr A) (uTr B) := by
    intro A B
    have hv_sum : inner ℂ (vTr A) (vTr B) =
        1 + ∑ S : Qubits n, (if majorityBit A.1 S ≠ majorityBit B.1 S then (-1 : ℂ) else 1) *
          (((1 / 2 : ℝ) : ℂ) * (X S A B : ℂ)) := by
      rw [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Fintype.sum_sum_type]
      simp only [Pi.star_apply]
      have h1 : ∑ opt : Option ι, vTr B (Sum.inl opt) * star (vTr A (Sum.inl opt)) = 1 := by
        simp only [hvTr_eval_inl]
        rw [Finset.sum_eq_single none]
        · simp
        · intro opt _ hopt; simp [hopt]
        · simp
      have h2 : ∑ p : Qubits n × ι, vTr B (Sum.inr p) * star (vTr A (Sum.inr p)) =
          ∑ S : Qubits n, (if majorityBit A.1 S ≠ majorityBit B.1 S then (-1 : ℂ) else 1) *
            (((1 / 2 : ℝ) : ℂ) * (X S A B : ℂ)) := by
        rw [Fintype.sum_prod_type]
        refine Finset.sum_congr rfl fun S _ => ?_
        have hs : (∑ j : ι, vTr B (Sum.inr (S, j)) * star (vTr A (Sum.inr (S, j)))) =
            (if majorityBit A.1 S ≠ majorityBit B.1 S then (-1 : ℂ) else 1) *
              ∑ j : ι, wCat B (S, j) * star (wCat A (S, j)) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [hvTr_eval_inr, hvTr_eval_inr]
          have hsign : (if majorityBit B.1 S then (-1 : ℂ) else 1) *
              star (if majorityBit A.1 S then (-1 : ℂ) else 1) =
              if majorityBit A.1 S ≠ majorityBit B.1 S then (-1 : ℂ) else 1 := by
            cases majorityBit A.1 S <;> cases majorityBit B.1 S <;> simp
          calc ((if majorityBit B.1 S then (-1 : ℂ) else 1) * wCat B (S, j)) *
                star ((if majorityBit A.1 S then (-1 : ℂ) else 1) * wCat A (S, j))
              = ((if majorityBit B.1 S then (-1 : ℂ) else 1) *
                  star (if majorityBit A.1 S then (-1 : ℂ) else 1)) *
                  (wCat B (S, j) * star (wCat A (S, j))) := by rw [star_mul]; ring
            _ = (if majorityBit A.1 S ≠ majorityBit B.1 S then (-1 : ℂ) else 1) *
                  (wCat B (S, j) * star (wCat A (S, j))) := by rw [hsign]
        have hinv2 : (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) * (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) = ((1 / 2 : ℝ) : ℂ) := by
          rw [← Complex.ofReal_mul, ← sq, inv_pow, Real.sq_sqrt (by norm_num)]
          norm_num
        have hw_slice : ∑ j : ι, wCat B (S, j) * star (wCat A (S, j)) =
            ((1 / 2 : ℝ) : ℂ) * (X S A B : ℂ) := by
          rw [← hwVec S A B, EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Finset.mul_sum]
          refine Finset.sum_congr rfl fun j _ => ?_
          simp only [wCat, star_mul, Complex.star_def, Complex.conj_ofReal]
          calc (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) * wVec S B j *
                (star (wVec S A j) * (((Real.sqrt 2)⁻¹ : ℝ) : ℂ))
              = ((((Real.sqrt 2)⁻¹ : ℝ) : ℂ) * (((Real.sqrt 2)⁻¹ : ℝ) : ℂ)) *
                  (wVec S B j * star (wVec S A j)) := by ring
            _ = ((1 / 2 : ℝ) : ℂ) * (wVec S B j * star (wVec S A j)) := by rw [hinv2]
        rw [hs, hw_slice]
      rw [h1, h2]
    have hu_sum : inner ℂ (uTr A) (uTr B) =
        (if A = B then (1 : ℂ) else 0) + ∑ S : Qubits n, ((1 / 2 : ℝ) : ℂ) * (X S A B : ℂ) := by
      rw [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Fintype.sum_sum_type]
      simp only [Pi.star_apply]
      have h1 : ∑ opt : Option ι, uTr B (Sum.inl opt) * star (uTr A (Sum.inl opt)) =
          if A = B then (1 : ℂ) else 0 := by
        simp only [huTr_eval_inl]
        rw [Finset.sum_eq_single (some B)]
        · by_cases hAB : A = B <;> simp [hAB, eq_comm]
        · intro opt _ hopt; simp [hopt]
        · simp
      have h2 : ∑ p : Qubits n × ι, uTr B (Sum.inr p) * star (uTr A (Sum.inr p)) =
          ∑ S : Qubits n, ((1 / 2 : ℝ) : ℂ) * (X S A B : ℂ) := by
        have hinr : (∑ p : Qubits n × ι, uTr B (Sum.inr p) * star (uTr A (Sum.inr p))) =
            inner ℂ (wCat A) (wCat B) := by
          rw [EuclideanSpace.inner_eq_star_dotProduct, dotProduct]
          simp only [Pi.star_apply]
          refine Finset.sum_congr rfl fun p _ => ?_
          rcases p with ⟨S, j⟩
          rw [huTr_eval_inr, huTr_eval_inr]
        rw [hinr, hwCat_inner A B]
      rw [h1, h2]
    rw [hv_sum, hu_sum]
    by_cases hAB : A = B
    · subst hAB
      simp
    · rw [if_neg hAB, zero_add]
      have hdiff : (∑ S : Qubits n, ((1 / 2 : ℝ) : ℂ) * (X S A B : ℂ)) -
          (∑ S : Qubits n, (if majorityBit A.1 S ≠ majorityBit B.1 S then (-1 : ℂ) else 1) *
            (((1 / 2 : ℝ) : ℂ) * (X S A B : ℂ))) = 1 := by
        rw [← Finset.sum_sub_distrib]
        have hterm : ∀ S : Qubits n,
            ((1 / 2 : ℝ) : ℂ) * (X S A B : ℂ) -
              (if majorityBit A.1 S ≠ majorityBit B.1 S then (-1 : ℂ) else 1) *
                (((1 / 2 : ℝ) : ℂ) * (X S A B : ℂ)) =
              ((if majorityBit A.1 S ≠ majorityBit B.1 S then X S A B else 0 : ℝ) : ℂ) := by
          intro S
          by_cases hd : majorityBit A.1 S ≠ majorityBit B.1 S
          · rw [if_pos hd, if_pos hd]; push_cast; ring
          · rw [if_neg hd, if_neg hd]; simp
        simp_rw [hterm, ← Complex.ofReal_sum]
        have hf := hfeas.2 A B hAB
        exact_mod_cast hf
      have heq := eq_add_of_sub_eq hdiff
      exact heq.symm
  obtain ⟨U_tr, hU_tr, hU_tr_act⟩ := exists_unitary_of_inner_eq vTr uTr hgramTr
  let clkIdx := (Fin K × Option ι) ⊕ (Qubits n × ι)
  let inrClk : (Qubits n × ι) ↪ clkIdx := ⟨Sum.inr, Sum.inr_injective⟩
  let slotEmbed : Fin K → (trIdx ↪ clkIdx) := fun j =>
    { toFun := fun x => match x with | Sum.inl opt => Sum.inl (j, opt) | Sum.inr sw => Sum.inr sw
      inj' := by rintro (o₁ | s₁) (o₂ | s₂) h <;> cases h <;> rfl }
  let U_step : Fin K → Matrix clkIdx clkIdx ℂ := fun j => liftMat (slotEmbed j) U_tr
  have hU_step_unitary : ∀ j : Fin K, U_step j ∈ Matrix.unitaryGroup clkIdx ℂ :=
    fun j => liftMat_mem_unitaryGroup (slotEmbed j) hU_tr
  let O_clk : ι → Matrix clkIdx clkIdx ℂ := fun A =>
    Matrix.diagonal fun x =>
      match x with
      | Sum.inl _ => 1
      | Sum.inr (S, _) => if majorityBit A.1 S then (-1 : ℂ) else 1
  have hO_clk_unitary : ∀ A : ι, O_clk A ∈ Matrix.unitaryGroup clkIdx ℂ := by
    intro A
    refine diag_pm1_mem_unitaryGroup _ ?_
    rintro (_ | ⟨S, _⟩)
    · left; rfl
    · by_cases h : majorityBit A.1 S <;> simp [h]
  let S_step : ι → Fin K → EuclideanSpace ℂ clkIdx → EuclideanSpace ℂ clkIdx :=
    fun A j ψ => act (U_step j) (act (O_clk A) ψ)
  let clkRun : (A : ι) → (t : ℕ) → t ≤ K → EuclideanSpace ℂ clkIdx → EuclideanSpace ℂ clkIdx :=
    fun A t => Nat.rec (motive := fun t => t ≤ K → EuclideanSpace ℂ clkIdx → EuclideanSpace ℂ clkIdx)
      (fun _ ψ => ψ)
      (fun t ih ht ψ => S_step A ⟨t, ht⟩ (ih (Nat.le_of_lt ht) ψ)) t
  have hclkRun_sub : ∀ (A : ι) (t : ℕ) (ht : t ≤ K) (ψ φ : EuclideanSpace ℂ clkIdx),
      clkRun A t ht (ψ - φ) = clkRun A t ht ψ - clkRun A t ht φ := by
    intro A t
    induction t with
    | zero => intro _ _ _; rfl
    | succ t ih =>
        intro ht ψ φ
        change S_step A ⟨t, ht⟩ (clkRun A t (Nat.le_of_lt ht) (ψ - φ)) =
          S_step A ⟨t, ht⟩ (clkRun A t (Nat.le_of_lt ht) ψ) -
          S_step A ⟨t, ht⟩ (clkRun A t (Nat.le_of_lt ht) φ)
        rw [ih (Nat.le_of_lt ht) ψ φ]
        dsimp only [S_step]
        rw [act_sub, act_sub]
  have hclkRun_norm : ∀ (A : ι) (t : ℕ) (ht : t ≤ K) (ψ : EuclideanSpace ℂ clkIdx),
      ‖clkRun A t ht ψ‖ = ‖ψ‖ := by
    intro A t
    induction t with
    | zero => intro _ _; rfl
    | succ t ih =>
        intro ht ψ
        change ‖S_step A ⟨t, ht⟩ (clkRun A t (Nat.le_of_lt ht) ψ)‖ = ‖ψ‖
        dsimp only [S_step]
        rw [act_norm_of_mem_unitaryGroup (hU_step_unitary ⟨t, ht⟩),
          act_norm_of_mem_unitaryGroup (hO_clk_unitary A), ih (Nat.le_of_lt ht) ψ]
  let scaleK : ℂ := (((Real.sqrt K)⁻¹ : ℝ) : ℂ)
  let ψ₀ : EuclideanSpace ℂ clkIdx :=
    scaleK • ∑ j : Fin K, ket (Sum.inl (j, (none : Option ι)))
  let sCat : ι → EuclideanSpace ℂ clkIdx := fun A => scaleK • liftVec inrClk (wCat A)
  let idealTarget : ι → EuclideanSpace ℂ clkIdx :=
    fun A => scaleK • ∑ j : Fin K, ket (Sum.inl (j, some A))
  let idealWithCat : ι → ℕ → EuclideanSpace ℂ clkIdx := fun A t =>
    scaleK • ((∑ j : Fin K, ket (Sum.inl (j, if j.1 < t then some A else none))) +
      liftVec inrClk (wCat A))
  have hideal_step : ∀ (A : ι) (t : ℕ) (ht : t < K),
      S_step A ⟨t, ht⟩ (idealWithCat A t) = idealWithCat A (t + 1) := by
    intro A t ht
    let j₀ : Fin K := ⟨t, ht⟩
    have hsum_split : (∑ j : Fin K, ket (Sum.inl (j, if j.1 < t then some A else none))) =
        ket (Sum.inl (j₀, (none : Option ι)) : clkIdx) +
          ∑ j ∈ Finset.univ.erase j₀, ket (Sum.inl (j, if j.1 < t then some A else none)) := by
      rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ j₀)]
      simp [j₀]
    have hvPre_lift : liftVec (slotEmbed j₀) (vPre A) =
        ket (Sum.inl (j₀, none)) + liftVec inrClk (wCat A) := by
      rw [liftVec_add, liftVec_ket, liftVec_comp]
      congr 1
    have hsum_step : (∑ j : Fin K, ket (Sum.inl (j, if j.1 < t then some A else none))) +
        liftVec inrClk (wCat A) =
        liftVec (slotEmbed j₀) (vPre A) +
          ∑ j ∈ Finset.univ.erase j₀, ket (Sum.inl (j, if j.1 < t then some A else none)) := by
      rw [hsum_split, hvPre_lift]
      abel
    have hO_ket : ∀ (j : Fin K) (opt : Option ι),
        act (O_clk A) (ket (Sum.inl (j, opt))) = ket (Sum.inl (j, opt)) := by
      intro j opt
      ext y
      dsimp only [O_clk]
      rw [act_diagonal]
      by_cases hy : y = Sum.inl (j, opt)
      · subst hy; simp [ket]
      · simp [ket, hy]
    have hO_pre : act (O_clk A) (liftVec (slotEmbed j₀) (vPre A)) =
        liftVec (slotEmbed j₀) (vTr A) := by
      have hd : ∀ x : trIdx,
          (match slotEmbed j₀ x with
            | Sum.inl _ => (1 : ℂ)
            | Sum.inr (S, _) => if majorityBit A.1 S then (-1 : ℂ) else 1) =
          (match x with
            | Sum.inl _ => (1 : ℂ)
            | Sum.inr (S, _) => if majorityBit A.1 S then (-1 : ℂ) else 1) := by
        rintro (opt | ⟨S, c⟩) <;> rfl
      simpa [O_clk, vTr, trPhaseOracle] using act_diagonal_liftVec (slotEmbed j₀) _ _ hd (vPre A)
    have hU_not_mem : ∀ j ∈ Finset.univ.erase j₀, ∀ opt : Option ι,
        Sum.inl (j, opt) ∉ Set.range (slotEmbed j₀) := by
      intro j hj opt ⟨x, hx⟩
      have hj_ne : j ≠ j₀ := (Finset.mem_erase.mp hj).1
      rcases x with opt' | sw
      · change Sum.inl (j₀, opt') = Sum.inl (j, opt) at hx
        cases hx
        exact hj_ne rfl
      · exact Sum.inr_ne_inl hx
    have huTr_lift : liftVec (slotEmbed j₀) (uTr A) =
        ket (Sum.inl (j₀, some A)) + liftVec inrClk (wCat A) := by
      rw [liftVec_add, liftVec_ket, liftVec_comp]
      congr 1
    have hsum_succ : (∑ j : Fin K, ket (Sum.inl (j, if j.1 < t + 1 then some A else none))) +
        liftVec inrClk (wCat A) =
        (ket (Sum.inl (j₀, some A)) + liftVec inrClk (wCat A)) +
          ∑ j ∈ Finset.univ.erase j₀, ket (Sum.inl (j, if j.1 < t then some A else none)) := by
      rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ j₀)]
      have hj₀_lt : j₀.1 < t + 1 := Nat.lt_succ_self t
      have hrest : ∑ j ∈ Finset.univ.erase j₀,
            ket (Sum.inl (j, if j.1 < t + 1 then some A else none) : clkIdx) =
          ∑ j ∈ Finset.univ.erase j₀,
            ket (Sum.inl (j, if j.1 < t then some A else none) : clkIdx) := by
        refine Finset.sum_congr rfl fun j hj => ?_
        have hj_ne : j ≠ j₀ := (Finset.mem_erase.mp hj).1
        have hval_ne : j.1 ≠ t := fun h => hj_ne (Fin.ext h)
        have hlt_iff : j.1 < t + 1 ↔ j.1 < t := by omega
        simp [hlt_iff]
      rw [if_pos hj₀_lt, hrest]
      abel
    dsimp only [S_step, idealWithCat]
    rw [hsum_step, act_smul, act_add, act_sum, hO_pre]
    have hO_sum : ∑ j ∈ Finset.univ.erase j₀,
        act (O_clk A) (ket (Sum.inl (j, if j.1 < t then some A else none))) =
        ∑ j ∈ Finset.univ.erase j₀, ket (Sum.inl (j, if j.1 < t then some A else none)) := by
      refine Finset.sum_congr rfl fun j _ => hO_ket j _
    rw [hO_sum, act_smul, act_add, act_sum]
    have hU_first : act (U_step j₀) (liftVec (slotEmbed j₀) (vTr A)) =
        ket (Sum.inl (j₀, some A)) + liftVec inrClk (wCat A) := by
      rw [act_liftMat_liftVec, hU_tr_act A, huTr_lift]
    have hU_rest : ∑ j ∈ Finset.univ.erase j₀,
        act (U_step j₀) (ket (Sum.inl (j, if j.1 < t then some A else none))) =
        ∑ j ∈ Finset.univ.erase j₀, ket (Sum.inl (j, if j.1 < t then some A else none)) := by
      refine Finset.sum_congr rfl fun j hj => act_liftMat_ket_not_mem (slotEmbed j₀) U_tr (hU_not_mem j hj _)
    rw [hU_first, hU_rest, ← hsum_succ]
  have hideal_run : ∀ (A : ι) (t : ℕ) (ht : t ≤ K),
      clkRun A t ht (idealWithCat A 0) = idealWithCat A t := by
    intro A t
    induction t with
    | zero => intro _; rfl
    | succ t ih =>
        intro ht
        change S_step A ⟨t, ht⟩ (clkRun A t (Nat.le_of_lt ht) (idealWithCat A 0)) = idealWithCat A (t + 1)
        rw [ih (Nat.le_of_lt ht)]
        exact hideal_step A t ht
  have hideal0_eq : ∀ A : ι, idealWithCat A 0 = ψ₀ + sCat A := by
    intro A
    simp only [idealWithCat, Nat.not_lt_zero, ↓reduceIte, ψ₀, sCat, smul_add]
  have hidealK_eq : ∀ A : ι, idealWithCat A K = idealTarget A + sCat A := by
    intro A
    have hsumK : ∑ j : Fin K, ket (Sum.inl (j, if j.1 < K then some A else none) : clkIdx) =
        ∑ j : Fin K, ket (Sum.inl (j, some A) : clkIdx) := by
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [if_pos j.isLt]
    simp only [idealWithCat, hsumK, idealTarget, sCat, smul_add]
  have hψ₀_norm : ‖ψ₀‖ = 1 := by
    let emb0 : Fin K ↪ clkIdx := ⟨fun j => Sum.inl (j, (none : Option ι)),
      fun j₁ j₂ h => by cases h; rfl⟩
    have hsum_norm : ‖∑ j : Fin K, ket (emb0 j)‖ = Real.sqrt K := by
      have hsq_r : ‖∑ j : Fin K, ket (emb0 j)‖ ^ 2 = (K : ℝ) := by
        simpa [Fintype.card_fin] using norm_sum_ket emb0
      rw [← Real.sqrt_sq (norm_nonneg _), hsq_r]
    change ‖scaleK • ∑ j : Fin K, ket (emb0 j)‖ = 1
    rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg K)),
      hsum_norm, inv_mul_cancel₀ (Real.sqrt_ne_zero'.mpr hK_real_pos)]
  have hclk_dist : ∀ A : ι, ‖clkRun A K le_rfl ψ₀ - idealTarget A‖ ^ 2 ≤ (1 / 3 : ℝ) := by
    intro A
    have hsub : clkRun A K le_rfl ψ₀ - idealTarget A = sCat A - clkRun A K le_rfl (sCat A) := by
      have hrun := hideal_run A K le_rfl
      rw [hideal0_eq A, hidealK_eq A] at hrun
      have hsub_add : clkRun A K le_rfl ψ₀ = clkRun A K le_rfl (ψ₀ + sCat A) - clkRun A K le_rfl (sCat A) := by
        rw [← hclkRun_sub A K le_rfl, add_sub_cancel_right]
      rw [hsub_add, hrun]
      abel
    have htri : ‖clkRun A K le_rfl ψ₀ - idealTarget A‖ ≤ 2 * ‖sCat A‖ := by
      rw [hsub]
      calc ‖sCat A - clkRun A K le_rfl (sCat A)‖
          ≤ ‖sCat A‖ + ‖clkRun A K le_rfl (sCat A)‖ := norm_sub_le _ _
        _ = ‖sCat A‖ + ‖sCat A‖ := by rw [hclkRun_norm A K le_rfl (sCat A)]
        _ = 2 * ‖sCat A‖ := (two_mul _).symm
    have hsCat_norm : ‖sCat A‖ = (Real.sqrt K)⁻¹ * ‖wCat A‖ := by
      dsimp only [sCat, scaleK]
      rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg K)),
        liftVec_norm]
    have hsq1 : ‖clkRun A K le_rfl ψ₀ - idealTarget A‖ ^ 2 ≤ (2 * ‖sCat A‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) htri 2
    have hsq2 : (2 * ‖sCat A‖) ^ 2 = 4 * (K : ℝ)⁻¹ * ‖wCat A‖ ^ 2 := by
      rw [hsCat_norm]
      have hsqrt_sq : (Real.sqrt K)⁻¹ ^ 2 = (K : ℝ)⁻¹ := by
        rw [inv_pow, Real.sq_sqrt (le_of_lt hK_real_pos)]
      calc (2 * ((Real.sqrt K)⁻¹ * ‖wCat A‖)) ^ 2
          = 4 * ((Real.sqrt K)⁻¹ ^ 2) * ‖wCat A‖ ^ 2 := by ring
        _ = 4 * (K : ℝ)⁻¹ * ‖wCat A‖ ^ 2 := by rw [hsqrt_sq]
    have hsq3 : 4 * (K : ℝ)⁻¹ * ‖wCat A‖ ^ 2 ≤ 4 * (K : ℝ)⁻¹ * (T / 2) :=
      mul_le_mul_of_nonneg_left (hwCat_norm_sq A) (by positivity)
    have hsq4 : 4 * (K : ℝ)⁻¹ * (T / 2) ≤ (1 / 3 : ℝ) := by
      rw [div_eq_mul_inv]
      have h_le : 4 * (K : ℝ)⁻¹ * (T * 2⁻¹) = (2 * T) / (K : ℝ) := by ring
      rw [h_le, div_le_iff₀ hK_real_pos]
      linarith
    exact le_trans hsq1 (le_trans (le_of_eq hsq2) (le_trans hsq3 hsq4))
  let cBits : ℕ := Nat.clog 2 K + 1
  have hK_lt_pow : K < 2 ^ cBits := by
    have hle : K ≤ 2 ^ Nat.clog 2 K := Nat.le_pow_clog (by norm_num) K
    have hpos : 0 < 2 ^ Nat.clog 2 K := Nat.two_pow_pos _
    calc K ≤ 2 ^ Nat.clog 2 K := hle
      _ < 2 * 2 ^ Nat.clog 2 K := by omega
      _ = 2 ^ cBits := by simp [cBits, pow_succ, mul_comm]
  let M : ℕ := 1 + n + cBits + n
  let embedFun : clkIdx → Qubits M := fun x =>
    match x with
    | Sum.inl (j, none) =>
        packQubits false (fun _ => false) (natToBits cBits j.1) (fun _ => false)
    | Sum.inl (j, some A) =>
        packQubits false (fun i => decide (i ∈ A.1)) (natToBits cBits j.1) (fun _ => false)
    | Sum.inr (S, C) =>
        packQubits true S (fun _ => false) (fun i => decide (i ∈ C.1))
  have hembed_inj : Function.Injective embedFun := by
    rintro (⟨j₁, o₁⟩ | ⟨S₁, C₁⟩) (⟨j₂, o₂⟩ | ⟨S₂, C₂⟩) h
    · rcases o₁ with _ | A₁ <;> rcases o₂ with _ | A₂
      · obtain ⟨_, _, hc, _⟩ := packQubits_inj h
        have hj : j₁.1 = j₂.1 := natToBits_inj_of_lt (lt_trans j₁.isLt hK_lt_pow)
          (lt_trans j₂.isLt hK_lt_pow) hc
        rw [Fin.ext hj]
      · obtain ⟨_, hq, _, _⟩ := packQubits_inj h
        obtain ⟨i, hi⟩ := A₂.2.1
        have hi_eq := congrFun hq i
        simp [hi] at hi_eq
      · obtain ⟨_, hq, _, _⟩ := packQubits_inj h
        obtain ⟨i, hi⟩ := A₁.2.1
        have hi_eq := congrFun hq i
        simp [hi] at hi_eq
      · obtain ⟨_, hq, hc, _⟩ := packQubits_inj h
        have hj : j₁.1 = j₂.1 := natToBits_inj_of_lt (lt_trans j₁.isLt hK_lt_pow)
          (lt_trans j₂.isLt hK_lt_pow) hc
        have hA : A₁ = A₂ := by
          apply Subtype.ext
          ext i
          have hi_eq := congrFun hq i
          simpa using hi_eq
        rw [Fin.ext hj, hA]
    · rcases o₁ with _ | A₁ <;>
        · obtain ⟨hctrl, _, _, _⟩ := packQubits_inj h
          cases hctrl
    · rcases o₂ with _ | A₂ <;>
        · obtain ⟨hctrl, _, _, _⟩ := packQubits_inj h
          cases hctrl
    · obtain ⟨_, hS, _, hC⟩ := packQubits_inj h
      have hC_eq : C₁ = C₂ := by
        apply Subtype.ext
        ext i
        have hi_eq := congrFun hC i
        simpa using hi_eq
      rw [hS, hC_eq]
  let embed : clkIdx ↪ Qubits M := ⟨embedFun, hembed_inj⟩
  have hembed_zero : embed (Sum.inl (⟨0, hK_pos⟩, none)) = fun _ => false := by
    change packQubits false (fun _ : Fin n => false) (natToBits cBits 0) (fun _ : Fin n => false) = _
    rw [natToBits_zero, packQubits_false]
  let ctrl : Fin M := ⟨0, by omega⟩
  let regQ : Fin n ↪ Fin M :=
    ⟨fun i => ⟨1 + i.1, by omega⟩, fun i j h => Fin.ext (by
      have hv := congrArg Fin.val h; dsimp at hv; omega)⟩
  let wiresFun : Fin (n + 1) → Fin (M + 1) := fun a =>
    if h : a.1 < n then ⟨1 + a.1, by omega⟩ else ⟨M, by omega⟩
  have hwires_inj : Function.Injective wiresFun := by
    intro a b hab
    have hv := congrArg Fin.val hab
    dsimp only [wiresFun] at hv
    by_cases ha : a.1 < n <;> by_cases hb : b.1 < n
    · simp only [ha, hb, ↓reduceDIte] at hv; exact Fin.ext (by omega)
    · simp only [ha, hb, ↓reduceDIte] at hv; exact Fin.ext (by omega)
    · simp only [ha, hb, ↓reduceDIte] at hv; exact Fin.ext (by omega)
    · simp only [ha, hb, ↓reduceDIte] at hv; exact Fin.ext (by omega)
  let wires : Fin (n + 1) ↪ Fin (M + 1) := ⟨wiresFun, hwires_inj⟩
  have hw_init : ∀ i : Fin n, wires i.castSucc = (regQ i).castSucc := by
    intro i
    apply Fin.ext
    simp only [wires, wiresFun, regQ, Function.Embedding.coeFn_mk, Fin.val_castSucc, i.isLt,
      ↓reduceDIte]
    rfl
  have hw_last : wires (Fin.last n) = Fin.last M := by
    apply Fin.ext
    simp only [wires, wiresFun, Function.Embedding.coeFn_mk, Fin.val_last, lt_self_iff_false,
      ↓reduceDIte]
  have hc_not_mem : ∀ c, some ctrl.castSucc = some c → c ∉ Set.range wires := by
    intro c hc ⟨a, ha⟩
    have hc_eq : c = ctrl.castSucc := (Option.some.inj hc).symm
    subst hc_eq
    have hv := congrArg Fin.val ha
    simp only [wires, wiresFun, Function.Embedding.coeFn_mk, ctrl, Fin.val_castSucc] at hv
    by_cases ha' : a.1 < n
    · simp only [ha', ↓reduceDIte] at hv; omega
    · simp only [ha', ↓reduceDIte] at hv; omega
  have hO_lift : ∀ (A : ι) (φ : EuclideanSpace ℂ clkIdx),
      act (phaseCtrlOracle A.1 ctrl regQ) (liftVec embed φ) =
      liftVec embed (act (O_clk A) φ) := by
    intro A φ
    refine act_diagonal_liftVec embed _ _ (fun x => ?_) φ
    rcases x with ⟨j, _ | B⟩ | ⟨S, C⟩
    · have hctrl_f : embed (Sum.inl (j, (none : Option ι))) ctrl = false := by
        change packQubits false (fun _ : Fin n => false) (natToBits cBits j.1)
          (fun _ : Fin n => false) ⟨0, by omega⟩ = false
        exact packQubits_ctrl false _ _ _
      dsimp only [O_clk]
      simp [hctrl_f]
    · have hctrl_f : embed (Sum.inl (j, some B)) ctrl = false := by
        change packQubits false (fun i => decide (i ∈ B.1)) (natToBits cBits j.1)
          (fun _ : Fin n => false) ⟨0, by omega⟩ = false
        exact packQubits_ctrl false _ _ _
      dsimp only [O_clk]
      simp [hctrl_f]
    · have hctrl_t : embed (Sum.inr (S, C)) ctrl = true := by
        change packQubits true S (fun _ : Fin cBits => false) (fun i => decide (i ∈ C.1))
          ⟨0, by omega⟩ = true
        exact packQubits_ctrl true S _ _
      have hreg_S : (embed (Sum.inr (S, C)) ∘ regQ) = S := by
        funext i
        change packQubits true S (fun _ : Fin cBits => false) (fun i => decide (i ∈ C.1))
          ⟨1 + i.1, by omega⟩ = S i
        exact packQubits_regQ true S _ _ i
      dsimp only [O_clk]
      simp [hctrl_t, hreg_S]
  let vInit : Unit → EuclideanSpace ℂ clkIdx := fun _ => ket (Sum.inl (⟨0, hK_pos⟩, none))
  let uInit : Unit → EuclideanSpace ℂ clkIdx := fun _ => ψ₀
  have hgram_init : ∀ x y : Unit, inner ℂ (vInit x) (vInit y) = inner ℂ (uInit x) (uInit y) := by
    intro _ _
    have h1 : inner ℂ (vInit ()) (vInit ()) = 1 := by
      simp [vInit, ket, EuclideanSpace.inner_single_left]
    have h2 : inner ℂ (uInit ()) (uInit ()) = 1 := by
      rw [inner_self_eq_norm_sq_to_K, hψ₀_norm]
      simp
    rw [h1, h2]
  obtain ⟨U_init, hU_init, hU_init_act⟩ := exists_unitary_of_inner_eq vInit uInit hgram_init
  let makeGateStep : (U : Matrix clkIdx clkIdx ℂ) → U ∈ Matrix.unitaryGroup clkIdx ℂ →
      OracleStep {g : Gate | g.IsUnitary} (fun _ : Fin 1 => n + 1) (M + 1) :=
    fun U hU => OracleStep.gate ⟨⟨M, liftMat embed U⟩, liftMat_mem_unitaryGroup embed hU, Fin.castAddEmb 1⟩
  let s_tgt : OracleStep {g : Gate | g.IsUnitary} (fun _ : Fin 1 => n + 1) (M + 1) :=
    prepareMinusStep M
  let s_init : OracleStep {g : Gate | g.IsUnitary} (fun _ : Fin 1 => n + 1) (M + 1) :=
    makeGateStep U_init hU_init
  let s_qry : OracleStep {g : Gate | g.IsUnitary} (fun _ : Fin 1 => n + 1) (M + 1) :=
    .query 0 false (some ctrl.castSucc) wires hc_not_mem
  let s_step : Fin K → OracleStep {g : Gate | g.IsUnitary} (fun _ : Fin 1 => n + 1) (M + 1) :=
    fun j => makeGateStep (U_step j) (hU_step_unitary j)
  let loopCirc : (t : ℕ) → t ≤ K →
      OracleCircuit {g : Gate | g.IsUnitary} (fun _ : Fin 1 => n + 1) (M + 1) :=
    fun t => Nat.rec (motive := fun t => t ≤ K →
        OracleCircuit {g : Gate | g.IsUnitary} (fun _ : Fin 1 => n + 1) (M + 1))
      (fun _ => [])
      (fun t ih ht => ih (Nat.le_of_lt ht) ++ [s_qry, s_step ⟨t, ht⟩]) t
  let c : OracleCircuit {g : Gate | g.IsUnitary} (fun _ : Fin 1 => n + 1) (M + 1) :=
    [s_tgt, s_init] ++ loopCirc K le_rfl
  let out : Fin n ↪ Fin (M + 1) := regQ.trans (Fin.castAddEmb 1)
  have hq_loop : ∀ (t : ℕ) (ht : t ≤ K), (loopCirc t ht).queryCount 0 = t := by
    intro t
    induction t with
    | zero => intro _; simp [loopCirc, OracleCircuit.queryCount]
    | succ t ih =>
        intro ht
        change (loopCirc t (Nat.le_of_lt ht) ++ [s_qry, s_step ⟨t, ht⟩]).queryCount 0 = t + 1
        rw [oracleCircuit_queryCount_append, ih (Nat.le_of_lt ht)]
        simp [OracleCircuit.queryCount, OracleStep.IsQueryTo, s_qry, s_step, makeGateStep]
  have hq_c : c.queryCount 0 ≤ K := by
    rw [oracleCircuit_queryCount_append, hq_loop K le_rfl]
    simp [OracleCircuit.queryCount, OracleStep.IsQueryTo, s_tgt, prepareMinusStep, s_init, makeGateStep]
  have hloop_act : ∀ (A : ι) (t : ℕ) (ht : t ≤ K) (φ : EuclideanSpace ℂ clkIdx),
      act ((loopCirc t ht).unitary fun _ => majOracle A.1) (withMinus (liftVec embed φ)) =
      withMinus (liftVec embed (clkRun A t ht φ)) := by
    intro A t
    induction t with
    | zero =>
        intro _ φ
        simp [loopCirc, clkRun, OracleCircuit.unitary, act]
    | succ t ih =>
        intro ht φ
        change act ((loopCirc t (Nat.le_of_lt ht) ++ [s_qry, s_step ⟨t, ht⟩]).unitary
            fun _ => majOracle A.1) (withMinus (liftVec embed φ)) =
          withMinus (liftVec embed (S_step A ⟨t, ht⟩ (clkRun A t (Nat.le_of_lt ht) φ)))
        rw [oracleCircuit_unitary_append, act_mul, ih (Nat.le_of_lt ht) φ]
        have hunit2 : OracleCircuit.unitary ([s_qry, s_step ⟨t, ht⟩] : OracleCircuit {g : Gate | g.IsUnitary}
            (fun _ : Fin 1 => n + 1) (M + 1)) (fun _ => majOracle A.1) =
            OracleStep.mat (fun _ => majOracle A.1) (s_step ⟨t, ht⟩) *
            OracleStep.mat (fun _ => majOracle A.1) s_qry := by
          dsimp only [OracleCircuit.unitary]
          simp only [List.map_cons, List.map_nil, List.reverse_cons, List.reverse_nil,
            List.nil_append, List.cons_append, List.prod_cons, List.prod_nil, mul_one]
        rw [hunit2, act_mul]
        have hq : act (OracleStep.mat (fun _ => majOracle A.1) s_qry)
            (withMinus (liftVec embed (clkRun A t (Nat.le_of_lt ht) φ))) =
            withMinus (liftVec embed (act (O_clk A) (clkRun A t (Nat.le_of_lt ht) φ))) := by
          rw [act_ctrl_majOracle_withMinus A.1 ctrl regQ wires hw_init hw_last hc_not_mem, hO_lift]
        rw [hq]
        change act (embedOp (liftMat embed (U_step ⟨t, ht⟩)) (Fin.castAddEmb 1))
            (withMinus (liftVec embed (act (O_clk A) (clkRun A t (Nat.le_of_lt ht) φ)))) = _
        rw [act_embedOp_castSucc_withMinus, act_liftMat_liftVec]
  refine ⟨M + 1, c, out, hq_c, ?_⟩
  intro A_raw hA_raw
  let A : ι := ⟨A_raw, ⟨Finset.card_pos.mp (by omega), hA_raw.2⟩⟩
  have hstart : act (OracleCircuit.unitary ([s_tgt, s_init] : OracleCircuit {g : Gate | g.IsUnitary}
      (fun _ : Fin 1 => n + 1) (M + 1)) fun _ => majOracle A_raw) (zeroKet (M + 1)) =
      withMinus (liftVec embed ψ₀) := by
    have hunit0 : OracleCircuit.unitary ([s_tgt, s_init] : OracleCircuit {g : Gate | g.IsUnitary}
        (fun _ : Fin 1 => n + 1) (M + 1)) (fun _ => majOracle A_raw) =
        OracleStep.mat (fun _ => majOracle A_raw) s_init *
        OracleStep.mat (fun _ => majOracle A_raw) s_tgt := by
      dsimp only [OracleCircuit.unitary]
      simp only [List.map_cons, List.map_nil, List.reverse_cons, List.reverse_nil,
        List.nil_append, List.cons_append, List.prod_cons, List.prod_nil, mul_one]
    rw [hunit0, act_mul]
    have hs1 : act (OracleStep.mat (fun _ => majOracle A_raw) s_tgt) (zeroKet (M + 1)) =
        withMinus (zeroKet M) := act_prepareMinusStep M _
    rw [hs1]
    have hzero : zeroKet M = liftVec embed (vInit ()) := by
      dsimp only [vInit]
      rw [liftVec_ket, hembed_zero]
      rfl
    rw [hzero]
    change act (embedOp (liftMat embed U_init) (Fin.castAddEmb 1))
        (withMinus (liftVec embed (vInit ()))) = _
    rw [act_embedOp_castSucc_withMinus, act_liftMat_liftVec, hU_init_act ()]
  have hfinal_vec : act (c.unitary fun _ => majOracle A_raw) (zeroKet (M + 1)) =
      withMinus (liftVec embed (clkRun A K le_rfl ψ₀)) := by
    dsimp only [c]
    rw [oracleCircuit_unitary_append, act_mul, hstart]
    exact hloop_act A K le_rfl ψ₀
  rw [hfinal_vec]
  let P_good : Qubits M → Prop := fun x => ∀ i : Fin n, x (regQ i) = decide (i ∈ A_raw)
  have hprob_eq : open Classical in
      probEvent (withMinus (liftVec embed (clkRun A K le_rfl ψ₀)))
        (fun z => ∀ i : Fin n, z (out i) = decide (i ∈ A_raw)) =
      probEvent (liftVec embed (clkRun A K le_rfl ψ₀)) P_good := by
    have hcongr : open Classical in
        probEvent (withMinus (liftVec embed (clkRun A K le_rfl ψ₀)))
          (fun z => ∀ i : Fin n, z (out i) = decide (i ∈ A_raw)) =
        probEvent (withMinus (liftVec embed (clkRun A K le_rfl ψ₀)))
          (fun z => P_good (Fin.init z)) := by
      apply probEvent_congr
      intro z
      rfl
    rw [hcongr]
    exact probEvent_withMinus _ P_good
  change open Classical in
    probEvent (withMinus (liftVec embed (clkRun A K le_rfl ψ₀)))
      (fun z => ∀ i : Fin n, z (out i) = decide (i ∈ A_raw)) ≥ 2 / 3
  rw [hprob_eq]
  classical
  have hnorm_final : ‖liftVec embed (clkRun A K le_rfl ψ₀)‖ = 1 := by
    rw [liftVec_norm, hclkRun_norm A K le_rfl ψ₀, hψ₀_norm]
  have hsupp : ∀ x : Qubits M, ¬ P_good x → liftVec embed (idealTarget A) x = 0 := by
    intro x hx
    by_cases hmem : x ∈ Set.range embed
    · obtain ⟨y, rfl⟩ := hmem
      rw [liftVec_apply_embed]
      rcases y with ⟨j, o⟩ | ⟨S, C⟩
      · rcases o with _ | B
        · simp [idealTarget, ket]
        · by_cases hAB : B = A
          · subst hAB
            exfalso
            apply hx
            intro i
            change packQubits false (fun i => decide (i ∈ A.1)) (natToBits cBits j.1)
              (fun _ : Fin n => false) ⟨1 + i.1, by omega⟩ = decide (i ∈ A_raw)
            exact packQubits_regQ false (fun i => decide (i ∈ A.1)) (natToBits cBits j.1) _ i
          · simp [idealTarget, ket, hAB]
      · simp [idealTarget, ket]
    · exact liftVec_apply_not_mem embed _ hmem
  have hdist_lift : ‖liftVec embed (clkRun A K le_rfl ψ₀) - liftVec embed (idealTarget A)‖ ^ 2 ≤
      (1 / 3 : ℝ) := by
    rw [← liftVec_sub, liftVec_norm]
    exact hclk_dist A
  exact probEvent_ge_of_norm_sub_sq _ _ P_good hnorm_final hsupp hdist_lift

end TransducerToCircuit

end Aux_w_maj_alg

open QuantumLTF.Membership.Supplement

theorem solution :
    (∃ C : ℝ, 0 < C ∧ ∀ k n : ℕ, 2 ≤ k → k ≤ n →
      (queryComplexity n (fun A => 1 ≤ A.card ∧ A.card ≤ k) : ℝ) ≤ C * Real.log k ∧
      (queryComplexity n (fun A => A.card = k) : ℝ) ≤ C * Real.log k) ∧
    (∃ C₁ : ℕ, ∀ n : ℕ, 1 ≤ n → queryComplexity n (fun A => A.card = 1) ≤ C₁) := by
  refine ⟨?_, ⟨1, Aux_w_maj_alg.k_eq_one_case⟩⟩
  obtain ⟨C₀, hC₀_pos, h45⟩ := QuantumLTF.Majority.lemma_4_5
  refine ⟨6 * C₀ + 2 / Real.log 2, ?_, ?_⟩
  · have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
    positivity
  · intro k n hk hkn
    obtain ⟨X, hfeas, hcost⟩ := h45 n k hk hkn
    obtain ⟨m, c, out, hq, hprob⟩ := Aux_w_maj_alg.dual_adversary_to_circuit hk hkn X hfeas hcost
    have hle_bounded : queryComplexity n (fun A => 1 ≤ A.card ∧ A.card ≤ k) ≤
        Nat.ceil (6 * (C₀ * Real.log k)) + 1 :=
      Nat.sInf_le ⟨m, c, out, hq, hprob⟩
    have hle_exact : queryComplexity n (fun A => A.card = k) ≤
        Nat.ceil (6 * (C₀ * Real.log k)) + 1 :=
      Nat.sInf_le ⟨m, c, out, hq, fun A hA => hprob A ⟨by omega, le_of_eq hA⟩⟩
    have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hlog2_le : Real.log 2 ≤ Real.log (k : ℝ) := by
      apply Real.log_le_log (by norm_num)
      exact_mod_cast hk
    have hlogk_pos : 0 < Real.log (k : ℝ) := lt_of_lt_of_le hlog2_pos hlog2_le
    have h6T_nonneg : 0 ≤ 6 * (C₀ * Real.log (k : ℝ)) := by positivity
    have hceil_lt : (Nat.ceil (6 * (C₀ * Real.log (k : ℝ))) : ℝ) <
        6 * (C₀ * Real.log (k : ℝ)) + 1 := Nat.ceil_lt_add_one h6T_nonneg
    have h2_le : (2 : ℝ) ≤ (2 / Real.log 2) * Real.log (k : ℝ) := by
      calc (2 : ℝ) = (2 / Real.log 2) * Real.log 2 := by
            rw [div_mul_cancel₀ _ (ne_of_gt hlog2_pos)]
        _ ≤ (2 / Real.log 2) * Real.log (k : ℝ) :=
            mul_le_mul_of_nonneg_left hlog2_le (by positivity)
    have hK_le : ((Nat.ceil (6 * (C₀ * Real.log (k : ℝ))) + 1 : ℕ) : ℝ) ≤
        (6 * C₀ + 2 / Real.log 2) * Real.log (k : ℝ) := by
      push_cast
      linarith
    have hq1 : (queryComplexity n (fun A => 1 ≤ A.card ∧ A.card ≤ k) : ℝ) ≤
        ((Nat.ceil (6 * (C₀ * Real.log (k : ℝ))) + 1 : ℕ) : ℝ) := by
      exact_mod_cast hle_bounded
    have hq2 : (queryComplexity n (fun A => A.card = k) : ℝ) ≤
        ((Nat.ceil (6 * (C₀ * Real.log (k : ℝ))) + 1 : ℕ) : ℝ) := by
      exact_mod_cast hle_exact
    exact ⟨le_trans hq1 hK_le, le_trans hq2 hK_le⟩
