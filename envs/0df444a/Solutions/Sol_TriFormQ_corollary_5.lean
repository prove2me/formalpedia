-- Prove2me | solution 1 for TriFormQ.corollary_5
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-27T00:46:11.265555+00:00
-- url     : https://prove2.me/submissions/d8087f6a-71c3-4953-8ac4-7ca14559b9d1

import Definitions.Def_QAlgorithms_Defs_Query

open QAlgorithms Matrix

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 1000

namespace TriFormQ.BVW

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

lemma exists_psi : ∃ ψ : AddChar F ℂ, ψ 1 ≠ 1 :=
  (AddChar.exists_apply_ne_zero (a := (1 : F))).2 one_ne_zero

lemma psi_conj (ψ : AddChar F ℂ) (t : F) : (starRingEnd ℂ) (ψ t) = ψ (-t) := by
  have h := AddChar.starComp_apply (R := F)
    (Nat.pos_of_ne_zero (CharP.ringChar_ne_zero_of_finite F)) (φ := ψ) t
  rw [h, AddChar.inv_apply', AddChar.map_neg_eq_inv]

/-- The character `z ↦ ψ (c ⬝ᵥ z)` sums to `q^n` or `0`. -/
lemma sum_psi_dot {n : ℕ} (ψ : AddChar F ℂ) (hψ : ψ 1 ≠ 1) (c : Fin n → F) :
    ∑ z : Fin n → F, ψ (c ⬝ᵥ z) = if c = 0 then (Fintype.card (Fin n → F) : ℂ) else 0 := by
  split_ifs with hc
  · subst hc; simp
  · let f : (Fin n → F) →+ F :=
      { toFun := fun z => c ⬝ᵥ z, map_zero' := dotProduct_zero c,
        map_add' := fun x y => dotProduct_add c x y }
    let χ : AddChar (Fin n → F) ℂ := ψ.compAddMonoidHom f
    have hχ : χ ≠ 1 := by
      obtain ⟨i, hi⟩ : ∃ i, c i ≠ 0 := by
        by_contra h; push Not at h; exact hc (funext h)
      intro h1
      have : χ (Pi.single i (c i)⁻¹) = 1 := by rw [h1]; rfl
      simp only [χ, AddChar.compAddMonoidHom_apply, f, AddMonoidHom.coe_mk, ZeroHom.coe_mk,
        dotProduct_single, mul_inv_cancel₀ hi] at this
      exact hψ this
    have := AddChar.sum_eq_zero_of_ne_one hχ
    simpa [χ, f] using this

/-- Sum over `ι` of a product of two extensions by zero along an injection. -/
lemma sum_extend_mul {ι Z : Type} [Fintype ι] [Fintype Z] [DecidableEq ι] (emb : Z → ι)
    (hemb : Function.Injective emb) (f g : Z → ℂ) :
    ∑ i, (starRingEnd ℂ) (Function.extend emb f 0 i) * Function.extend emb g 0 i =
      ∑ z, (starRingEnd ℂ) (f z) * g z := by
  classical
  rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.image emb))]
  · rw [Finset.sum_image (fun x _ y _ h => hemb h)]
    refine Finset.sum_congr rfl fun z _ => ?_
    rw [hemb.extend_apply, hemb.extend_apply]
  · intro i _ hi
    have : ¬ ∃ z, emb z = i := by
      rintro ⟨z, rfl⟩; exact hi (Finset.mem_image_of_mem _ (Finset.mem_univ z))
    rw [Function.extend_apply' _ _ _ this]; simp

/-- Action of the standard oracle tensored with the identity on the workspace. -/
lemma act_xor_apply {ι W : Type} [Fintype ι] [DecidableEq ι] [Fintype W] [DecidableEq W]
    (g : ι → F) (s : EuclideanSpace ℂ ((ι × F) × W)) (i : ι) (b : F) (w : W) :
    act (Matrix.kronecker (xorOracle g) (1 : Matrix W W ℂ)) s ((i, b), w) =
      s ((i, b - g i), w) := by
  simp only [act, Matrix.mulVec, dotProduct, Matrix.kronecker, Matrix.kroneckerMap_apply,
    xorOracle, Matrix.of_apply, Matrix.one_apply]
  rw [Finset.sum_eq_single ((i, b - g i), w)]
  · simp
  · rintro ⟨⟨i', b'⟩, w'⟩ _ hne
    by_cases h1 : i = i'
    · subst h1
      by_cases h2 : b = b' + g i
      · by_cases h3 : w = w'
        · subst h3; exfalso; apply hne; simp [h2]
        · simp [h3]
      · simp [h2]
    · simp [h1]
  · simp

/-- Generic one-query Bernstein–Vazirani over a finite field: if the oracle restricted to an
injectively embedded copy of `𝔽ⁿ` is the linear function `z ↦ a ⬝ᵥ z`, one query yields `a`
exactly (the final state is a basis vector decoding to `a`). -/
theorem bv_generic {ι : Type} [Fintype ι] [DecidableEq ι] {n : ℕ} (emb : (Fin n → F) → ι)
    (hemb : Function.Injective emb) :
    ∃ (A : QueryAlg ι F (Fin 1) 1) (dec : (ι × F) × Fin 1 → (Fin n → F)),
      ∀ (g : ι → F) (a : Fin n → F), (∀ z, g (emb z) = a ⬝ᵥ z) →
        ∃ z0, A.finalState (xorOracle g) = ket z0 ∧ dec z0 = a := by
  classical
  obtain ⟨ψ, hψ⟩ := exists_psi (F := F)
  set N : ℕ := Fintype.card (Fin n → F) * Fintype.card F with hN
  have hNpos : (0 : ℝ) < N := by
    have h1 : 0 < Fintype.card (Fin n → F) := Fintype.card_pos
    have h2 : 0 < Fintype.card F := Fintype.card_pos
    exact_mod_cast Nat.mul_pos h1 h2
  set c0 : ℂ := (((Real.sqrt N)⁻¹ : ℝ) : ℂ) with hc0
  have hc0sq : (starRingEnd ℂ) c0 * c0 = ((N : ℝ)⁻¹ : ℝ) := by
    rw [hc0, Complex.conj_ofReal, ← Complex.ofReal_mul, ← mul_inv, Real.mul_self_sqrt hNpos.le]
  let ι' := (ι × F) × Fin 1
  let φ : (Fin n → F) → EuclideanSpace ℂ ι' := fun a => WithLp.toLp 2 fun p =>
    Function.extend emb (fun z => c0 * ψ (a ⬝ᵥ z - p.1.2)) 0 p.1.1
  have hφ : Orthonormal ℂ φ := by
    rw [orthonormal_iff_ite]
    intro a a'
    rw [PiLp.inner_apply]
    simp only [RCLike.inner_apply, φ]
    rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
    simp only [Fintype.sum_unique]
    rw [Finset.sum_comm]
    have key : ∀ b : F, ∑ i : ι, (starRingEnd ℂ) (Function.extend emb
        (fun z => c0 * ψ (a ⬝ᵥ z - b)) 0 i) * Function.extend emb
        (fun z => c0 * ψ (a' ⬝ᵥ z - b)) 0 i = ((N : ℝ)⁻¹ : ℝ) * ∑ z, ψ ((a' - a) ⬝ᵥ z) := by
      intro b
      -- note: inner is conj(first) * second; here written as second * conj(first)
      rw [sum_extend_mul emb hemb, Finset.mul_sum]
      refine Finset.sum_congr rfl fun z _ => ?_
      rw [map_mul, psi_conj, mul_mul_mul_comm, hc0sq, ← AddChar.map_add_eq_mul]
      congr 2; simp [sub_dotProduct]
    have key' : ∀ b : F, ∑ i : ι, Function.extend emb
        (fun z => c0 * ψ (a' ⬝ᵥ z - b)) 0 i * (starRingEnd ℂ) (Function.extend emb
        (fun z => c0 * ψ (a ⬝ᵥ z - b)) 0 i) = ((N : ℝ)⁻¹ : ℝ) * ∑ z, ψ ((a' - a) ⬝ᵥ z) := by
      intro b; rw [← key b]; exact Finset.sum_congr rfl fun i _ => mul_comm _ _
    simp_rw [key']
    rw [Finset.sum_const, Finset.card_univ, sum_psi_dot ψ hψ]
    by_cases h : a = a'
    · subst h
      simp only [sub_self, if_true]
      rw [nsmul_eq_mul]
      have : (N : ℂ) = (Fintype.card F : ℂ) * (Fintype.card (Fin n → F) : ℂ) := by
        rw [hN]; push_cast; ring
      have hN0 : (N : ℂ) ≠ 0 := by exact_mod_cast hNpos.ne'
      rw [Complex.ofReal_inv, Complex.ofReal_natCast]
      field_simp
      rw [this]
    · have : a' - a ≠ 0 := sub_ne_zero.2 (Ne.symm h)
      simp [h, this]
  -- the embedding of `𝔽ⁿ` into the basis of the register
  let τ : (Fin n → F) → ι' := fun a => ((emb a, 0), 0)
  have hτ : Function.Injective τ := fun a a' h => hemb (by simpa [τ] using congrArg (·.1.1) h)
  let v : ι' → EuclideanSpace ℂ ι' := Function.extend τ φ 0
  have hcard : Module.finrank ℂ (EuclideanSpace ℂ ι') = Fintype.card ι' := finrank_euclideanSpace
  have hv : Orthonormal ℂ ((Set.range τ).domRestrict v) := by
    let e := Equiv.ofInjective τ hτ
    have : (Set.range τ).domRestrict v = φ ∘ e.symm := by
      funext x
      simp only [Set.domRestrict, Function.comp_apply, v]
      have hx : (x : ι') = τ (e.symm x) := (Equiv.apply_ofInjective_symm hτ x).symm
      rw [hx, hτ.extend_apply]
    rw [this]
    exact hφ.comp _ e.symm.injective
  obtain ⟨b, hb⟩ := Orthonormal.exists_orthonormalBasis_extension_of_card_eq hcard hv
  have hbτ : ∀ a, b (τ a) = φ a := by
    intro a
    rw [hb (τ a) ⟨a, rfl⟩]
    simp only [v, hτ.extend_apply]
  let U1 : Matrix ι' ι' ℂ := b.toBasis.toMatrix (EuclideanSpace.basisFun ι' ℂ).toBasis
  have hU1 : U1 ∈ Matrix.unitaryGroup ι' ℂ :=
    b.toMatrix_orthonormalBasis_mem_unitary (EuclideanSpace.basisFun ι' ℂ)
  have hU1act : ∀ x : EuclideanSpace ℂ ι', act U1 x = b.repr x := by
    intro x
    have h := Module.Basis.toMatrix_mulVec_repr (b' := b.toBasis) (b := (EuclideanSpace.basisFun ι' ℂ).toBasis) x
    simp only [act, U1]
    have e1 : (⇑((EuclideanSpace.basisFun ι' ℂ).toBasis.repr x) : ι' → ℂ) = WithLp.ofLp x := by
      funext i; simp
    rw [e1] at h
    rw [h]
    ext i
    simp
  let A : QueryAlg ι F (Fin 1) 1 :=
    { start := φ 0
      start_unit := hφ.1 0
      U := fun k => if k = 0 then 1 else ⟨U1, hU1⟩ }
  let dec : ι' → (Fin n → F) := fun p => Function.invFun emb p.1.1
  refine ⟨A, dec, fun g a hga => ⟨τ a, ?_, ?_⟩⟩
  · have hfin : A.finalState (xorOracle g) = act (A.U 1 : Matrix _ _ ℂ)
        (act (Matrix.kronecker (xorOracle g) (1 : Matrix (Fin 1) (Fin 1) ℂ))
          (act (A.U 0 : Matrix _ _ ℂ) A.start)) := rfl
    rw [hfin]
    have hU0 : (A.U 0 : Matrix ι' ι' ℂ) = 1 := by simp [A]
    have hU1' : (A.U 1 : Matrix ι' ι' ℂ) = U1 := by simp [A]
    rw [hU0, hU1']
    have hstep : act (Matrix.kronecker (xorOracle g) (1 : Matrix (Fin 1) (Fin 1) ℂ))
        (act 1 A.start) = φ a := by
      ext ⟨⟨i, b'⟩, w⟩
      rw [act_xor_apply]
      simp only [act, Matrix.one_mulVec, A, φ]
      by_cases hi : ∃ z, emb z = i
      · obtain ⟨z, rfl⟩ := hi
        rw [hemb.extend_apply, hemb.extend_apply, hga z]
        congr 2; simp
      · rw [Function.extend_apply' _ _ _ hi, Function.extend_apply' _ _ _ hi]
    rw [hstep, hU1act, ← hbτ, OrthonormalBasis.repr_self]
    rfl
  · simp only [dec, τ]
    exact Function.leftInverse_invFun hemb a

end TriFormQ.BVW

section
open QAlgorithms

lemma TriFormQ.BVW.outputProb_of_ket {ι W : Type} [Fintype ι] [Fintype W] [DecidableEq ι]
    [DecidableEq W] {κ : Type} [Fintype κ] [DecidableEq κ] {T : ℕ} {β : Type} [DecidableEq β]
    (A : QueryAlg ι κ W T) (O : Matrix (ι × κ) (ι × κ) ℂ) (out : (ι × κ) × W → β) (b : β)
    (z0 : (ι × κ) × W) (hz : A.finalState O = ket z0) (hb : out z0 = b) :
    A.outputProb O out b = 1 := by
  unfold QueryAlg.outputProb probEvent
  rw [hz, Finset.sum_eq_single z0]
  · simp [prob, ket, EuclideanSpace.inner_single_left]
  · intro z _ hz0
    simp [prob, ket, EuclideanSpace.inner_single_left, Pi.single_apply, hz0]
  · intro h; exact absurd (Finset.mem_filter.2 ⟨Finset.mem_univ z0, hb⟩) h
end

open Matrix in
theorem solution {F : Type} [Field F] [Fintype F] [DecidableEq F] (n m p : ℕ) :
    (∀ (x₀ : Fin n → F) (y₀ : Fin m → F),
      ∃ (w : ℕ) (A : QAlgorithms.QueryAlg ((Fin n → F) × (Fin m → F) × (Fin p → F)) F (Fin w) 1)
        (out : (((Fin n → F) × (Fin m → F) × (Fin p → F)) × F) × Fin w → (Fin p → F)),
        ∀ θ : Fin n → Fin m → Fin p → F,
          A.outputProb (QAlgorithms.xorOracle fun t : (Fin n → F) × (Fin m → F) × (Fin p → F) =>
              ∑ i, ∑ j, ∑ k, θ i j k * t.1 i * t.2.1 j * t.2.2 k) out
            (fun k => ∑ i, ∑ j, θ i j k * x₀ i * y₀ j) = 1) ∧
    (∀ (x₀ : Fin n → F) (z₀ : Fin p → F),
      ∃ (w : ℕ) (A : QAlgorithms.QueryAlg ((Fin n → F) × (Fin m → F) × (Fin p → F)) F (Fin w) 1)
        (out : (((Fin n → F) × (Fin m → F) × (Fin p → F)) × F) × Fin w → (Fin m → F)),
        ∀ θ : Fin n → Fin m → Fin p → F,
          A.outputProb (QAlgorithms.xorOracle fun t : (Fin n → F) × (Fin m → F) × (Fin p → F) =>
              ∑ i, ∑ j, ∑ k, θ i j k * t.1 i * t.2.1 j * t.2.2 k) out
            (fun j => ∑ i, ∑ k, θ i j k * x₀ i * z₀ k) = 1) ∧
    (∀ (y₀ : Fin m → F) (z₀ : Fin p → F),
      ∃ (w : ℕ) (A : QAlgorithms.QueryAlg ((Fin n → F) × (Fin m → F) × (Fin p → F)) F (Fin w) 1)
        (out : (((Fin n → F) × (Fin m → F) × (Fin p → F)) × F) × Fin w → (Fin n → F)),
        ∀ θ : Fin n → Fin m → Fin p → F,
          A.outputProb (QAlgorithms.xorOracle fun t : (Fin n → F) × (Fin m → F) × (Fin p → F) =>
              ∑ i, ∑ j, ∑ k, θ i j k * t.1 i * t.2.1 j * t.2.2 k) out
            (fun i => ∑ j, ∑ k, θ i j k * y₀ j * z₀ k) = 1) := by
  refine ⟨fun x₀ y₀ => ?_, fun x₀ z₀ => ?_, fun y₀ z₀ => ?_⟩
  · obtain ⟨A, dec, h⟩ := TriFormQ.BVW.bv_generic (F := F) (n := p)
      (fun z : Fin p → F => (x₀, y₀, z)) (fun a b hab => by simpa using hab)
    refine ⟨1, A, dec, fun θ => ?_⟩
    obtain ⟨z0, hz, hd⟩ := h (fun t : (Fin n → F) × (Fin m → F) × (Fin p → F) => ∑ i, ∑ j, ∑ k, θ i j k * t.1 i * t.2.1 j * t.2.2 k) (fun k => ∑ i, ∑ j, θ i j k * x₀ i * y₀ j) (fun z => by
      show ∑ i, ∑ j, ∑ k, θ i j k * x₀ i * y₀ j * z k = _
      simp only [dotProduct, Finset.sum_mul]
      rw [show (∑ i, ∑ j, ∑ k, θ i j k * x₀ i * y₀ j * z k) =
          ∑ i, ∑ k, ∑ j, θ i j k * x₀ i * y₀ j * z k from
        Finset.sum_congr rfl fun i _ => Finset.sum_comm]
      exact Finset.sum_comm)
    exact TriFormQ.BVW.outputProb_of_ket A _ dec _ z0 hz hd
  · obtain ⟨A, dec, h⟩ := TriFormQ.BVW.bv_generic (F := F) (n := m)
      (fun y : Fin m → F => (x₀, y, z₀)) (fun a b hab => by simpa using hab)
    refine ⟨1, A, dec, fun θ => ?_⟩
    obtain ⟨z0, hz, hd⟩ := h (fun t : (Fin n → F) × (Fin m → F) × (Fin p → F) => ∑ i, ∑ j, ∑ k, θ i j k * t.1 i * t.2.1 j * t.2.2 k) (fun j => ∑ i, ∑ k, θ i j k * x₀ i * z₀ k) (fun y => by
      show ∑ i, ∑ j, ∑ k, θ i j k * x₀ i * y j * z₀ k = _
      simp only [dotProduct, Finset.sum_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      refine Finset.sum_congr rfl fun k _ => ?_
      ring)
    exact TriFormQ.BVW.outputProb_of_ket A _ dec _ z0 hz hd
  · obtain ⟨A, dec, h⟩ := TriFormQ.BVW.bv_generic (F := F) (n := n)
      (fun x : Fin n → F => (x, y₀, z₀)) (fun a b hab => by simpa using hab)
    refine ⟨1, A, dec, fun θ => ?_⟩
    obtain ⟨z0, hz, hd⟩ := h (fun t : (Fin n → F) × (Fin m → F) × (Fin p → F) => ∑ i, ∑ j, ∑ k, θ i j k * t.1 i * t.2.1 j * t.2.2 k) (fun i => ∑ j, ∑ k, θ i j k * y₀ j * z₀ k) (fun x => by
      show ∑ i, ∑ j, ∑ k, θ i j k * x i * y₀ j * z₀ k = _
      simp only [dotProduct, Finset.sum_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      refine Finset.sum_congr rfl fun k _ => ?_
      ring)
    exact TriFormQ.BVW.outputProb_of_ket A _ dec _ z0 hz hd
