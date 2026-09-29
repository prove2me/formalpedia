-- Prove2me | solution 1 for PDivisibleGroup.associated_jacobianDet_pow_of_hasDimension_of_ringOfIntegers
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/c511c032-11c3-5490-b500-33d137085ed6

import Mathlib
import Definitions.Def_PDivisibleGroup_Basic
import Definitions.Def_PDivisibleGroup_Points
import Definitions.Def_PDivisibleGroup_Dimension
import Definitions.Def_PadicAlgCl_RingOfIntegers

import Theorems.Thm_Module_span_det_submatrix_eq_of_ker_eq_span_range
import Theorems.Thm_KaehlerDifferential_exists_linearMap_pi_surjective_ker_eq_span_pderiv_of_surjective
import Theorems.Thm_HopfAlgebra_nonempty_kaehlerDifferential_linearEquiv_tensorProduct_cotangent
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_PDivisibleGroup_associated_jacobianDet_pow_of_hasDimension_of_ringOfIntegers

set_option autoImplicit false

namespace DLA

open scoped TensorProduct

theorem span_range_det_submatrix_square {A : Type*} [CommRing A] {k : ℕ} (X : Matrix (Fin k) (Fin k) A) :
    Ideal.span (Set.range fun c : Fin k → Fin k => (X.submatrix id c).det) = Ideal.span {X.det} := by
  classical
  apply le_antisymm
  · rw [Ideal.span_le]
    rintro _ ⟨c, rfl⟩
    rw [SetLike.mem_coe, Ideal.mem_span_singleton]
    show X.det ∣ (X.submatrix id c).det
    by_cases hc : Function.Injective c
    · have hbij : Function.Bijective c := Finite.injective_iff_bijective.mp hc
      rw [show (X.submatrix id c).det = ↑↑(Equiv.Perm.sign (Equiv.ofBijective c hbij)) * X.det from
        Matrix.det_permute' (Equiv.ofBijective c hbij) X]
      exact Dvd.intro_left _ rfl
    · obtain ⟨i, j, hij, hne⟩ : ∃ i j, c i = c j ∧ i ≠ j := by
        simpa [Function.Injective, not_forall] using hc
      have h0 : (X.submatrix id c).det = 0 :=
        Matrix.det_zero_of_column_eq (M := X.submatrix id c) hne (fun r => by
          rw [Matrix.submatrix_apply, Matrix.submatrix_apply, hij])
      rw [h0]
      exact dvd_zero _
  · rw [Ideal.span_singleton_le_iff_mem]
    apply Ideal.subset_span
    exact ⟨id, by simp⟩

theorem associated_of_span_singleton_eq_of_mem_nonZeroDivisors {A : Type*} [CommRing A] {x y : A}
    (h : Ideal.span {x} = Ideal.span {y}) (hy : y ∈ nonZeroDivisors A) : Associated x y := by
  have hxy : y ∣ x := Ideal.mem_span_singleton.mp (h ▸ Ideal.mem_span_singleton_self x)
  have hyx : x ∣ y := Ideal.mem_span_singleton.mp (h.symm ▸ Ideal.mem_span_singleton_self y)
  obtain ⟨a, ha⟩ := hxy
  obtain ⟨b, hb⟩ := hyx
  have h1 : y * (a * b) = y * 1 := by rw [mul_one, ← mul_assoc, ← ha, ← hb]
  have hab : a * b = 1 := (mul_cancel_left_mem_nonZeroDivisors hy).mp h1
  exact ⟨⟨b, a, by rw [mul_comm, hab], hab⟩, hb.symm⟩

theorem exists_presentation_pi_quotient (A : Type*) [CommRing A] (n : ℕ) (α : A) :
    ∃ π : (Fin n → A) →ₗ[A] (Fin n → A ⧸ Ideal.span {α}), Function.Surjective π ∧
      LinearMap.ker π = Submodule.span A (Set.range fun j : Fin n => fun i => (α • (1 : Matrix (Fin n) (Fin n) A)) i j) := by
  classical
  let π : (Fin n → A) →ₗ[A] (Fin n → A ⧸ Ideal.span {α}) :=
    LinearMap.pi fun i => (Submodule.mkQ ((Ideal.span {α}).restrictScalars A)) ∘ₗ LinearMap.proj i
  have hπ : ∀ v i, π v i = Ideal.Quotient.mk (Ideal.span {α}) (v i) := fun v i => rfl
  refine ⟨π, fun w => ?_, ?_⟩
  · choose v hv using fun i => Ideal.Quotient.mk_surjective (w i)
    exact ⟨v, funext fun i => by rw [hπ, hv]⟩
  · have hcol : ∀ j : Fin n, (fun i => (α • (1 : Matrix (Fin n) (Fin n) A)) i j) = Pi.single j α := fun j => by
      ext i; by_cases h : i = j
      · subst h; rw [Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one, Pi.single_eq_same]
      · rw [Matrix.smul_apply, Matrix.one_apply_ne h, smul_zero, Pi.single_apply, if_neg h]
    rw [show (fun j : Fin n => fun i => (α • (1 : Matrix (Fin n) (Fin n) A)) i j) = fun j => (Pi.single j α : Fin n → A)
      from funext hcol]
    apply le_antisymm
    · intro v hv
      rw [LinearMap.mem_ker] at hv
      have hvi : ∀ i, ∃ b : A, b * α = v i := fun i => by
        have : π v i = 0 := by rw [hv]; rfl
        rw [hπ, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton'] at this
        exact this
      choose b hb using hvi
      have : v = ∑ i, b i • (Pi.single i α : Fin n → A) := by
        ext k; simp [Finset.sum_apply, Pi.single_apply, hb]
      rw [this]
      exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self i))
    · rw [Submodule.span_le]
      rintro _ ⟨j, rfl⟩
      rw [SetLike.mem_coe, LinearMap.mem_ker]
      ext i
      rw [hπ, Pi.zero_apply, Ideal.Quotient.eq_zero_iff_mem]
      by_cases h : i = j
      · subst h; simp [Ideal.mem_span_singleton_self]
      · simp [Pi.single_apply, h]

end DLA

open scoped TensorProduct

set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 6400000 in
theorem solution
    (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] K]
    {h : ℕ} (G : PDivisibleGroup (PadicAlgCl.ringOfIntegers p K) p h) {n : ℕ} (hn : G.HasDimension n) (v : ℕ)
    {m : ℕ} (f : Fin m → MvPolynomial (Fin m) (PadicAlgCl.ringOfIntegers p K))
    (e : (MvPolynomial (Fin m) (PadicAlgCl.ringOfIntegers p K) ⧸ Ideal.span (Set.range f)) ≃ₐ[PadicAlgCl.ringOfIntegers p K]
      G.level v) :
    Associated (e (Ideal.Quotient.mk _ (Matrix.det (Matrix.of fun i j => MvPolynomial.pderiv j (f i)))))
      (((p : ℕ) : G.level v) ^ (n * v)) := by
  classical

  let φ : MvPolynomial (Fin m) (PadicAlgCl.ringOfIntegers p K) →ₐ[(PadicAlgCl.ringOfIntegers p K)] (G.level v) := e.toAlgHom.comp (Ideal.Quotient.mkₐ (PadicAlgCl.ringOfIntegers p K) (Ideal.span (Set.range f)))
  have hφ : Function.Surjective φ := e.surjective.comp (Ideal.Quotient.mkₐ_surjective (PadicAlgCl.ringOfIntegers p K) (Ideal.span (Set.range f)))
  have hkerφ : RingHom.ker φ = (Ideal.span (Set.range f)) := by
    ext x
    rw [RingHom.mem_ker, show φ x = e (Ideal.Quotient.mk (Ideal.span (Set.range f)) x) from rfl, map_eq_zero_iff e e.injective,
      Ideal.Quotient.eq_zero_iff_mem]

  obtain ⟨Φ₁, hΦ₁s, -, hker₁⟩ :=
    KaehlerDifferential.exists_linearMap_pi_surjective_ker_eq_span_pderiv_of_surjective (PadicAlgCl.ringOfIntegers p K) (G.level v) f φ hφ hkerφ
  let X₁ : Matrix (Fin m) (Fin m) (G.level v) := Matrix.of fun a b => φ (MvPolynomial.pderiv a (f b))
  have hX₁ : LinearMap.ker Φ₁ = Submodule.span (G.level v) (Set.range fun j : Fin m => fun i => X₁ i j) :=
    hker₁

  obtain ⟨ω⟩ := HopfAlgebra.nonempty_kaehlerDifferential_linearEquiv_tensorProduct_cotangent (PadicAlgCl.ringOfIntegers p K) (G.level v)
  obtain ⟨δ⟩ := hn v
  have hmap : (Ideal.span {((p : ℕ) : (PadicAlgCl.ringOfIntegers p K)) ^ v}).map (algebraMap (PadicAlgCl.ringOfIntegers p K) (G.level v)) = Ideal.span {((p : ℕ) : (G.level v)) ^ v} := by
    rw [Ideal.map_span, Set.image_singleton, map_pow, map_natCast]
  let E : Ω[(G.level v)⁄(PadicAlgCl.ringOfIntegers p K)] ≃ₗ[(G.level v)] (Fin n → (G.level v) ⧸ Ideal.span {((p : ℕ) : (G.level v)) ^ v}) :=
    ω ≪≫ₗ (LinearEquiv.baseChange (PadicAlgCl.ringOfIntegers p K) (G.level v) _ _ (δ : (RingHom.ker (Bialgebra.counitAlgHom (PadicAlgCl.ringOfIntegers p K) (G.level v))).Cotangent ≃ₗ[(PadicAlgCl.ringOfIntegers p K)]
        (Fin n → (PadicAlgCl.ringOfIntegers p K) ⧸ Ideal.span {((p : ℕ) : (PadicAlgCl.ringOfIntegers p K)) ^ v}))) ≪≫ₗ
      TensorProduct.piRight (PadicAlgCl.ringOfIntegers p K) (G.level v) (G.level v) (fun _ : Fin n => (PadicAlgCl.ringOfIntegers p K) ⧸ Ideal.span {((p : ℕ) : (PadicAlgCl.ringOfIntegers p K)) ^ v}) ≪≫ₗ
      LinearEquiv.piCongrRight (fun _ : Fin n =>
        ((Algebra.TensorProduct.quotIdealMapEquivTensorQuot (G.level v) (Ideal.span {((p : ℕ) : (PadicAlgCl.ringOfIntegers p K)) ^ v})).symm.toLinearEquiv ≪≫ₗ
          Submodule.quotEquivOfEq _ _ hmap))
  obtain ⟨π₂, hπ₂s, hker₂⟩ := DLA.exists_presentation_pi_quotient (G.level v) n (((p : ℕ) : (G.level v)) ^ v)
  let Φ₂ : (Fin n → (G.level v)) →ₗ[(G.level v)] Ω[(G.level v)⁄(PadicAlgCl.ringOfIntegers p K)] := E.symm.toLinearMap ∘ₗ π₂
  have hΦ₂s : Function.Surjective Φ₂ := E.symm.surjective.comp hπ₂s
  let X₂ : Matrix (Fin n) (Fin n) (G.level v) := ((p : ℕ) : (G.level v)) ^ v • (1 : Matrix (Fin n) (Fin n) (G.level v))
  have hX₂ : LinearMap.ker Φ₂ = Submodule.span (G.level v) (Set.range fun j : Fin n => fun i => X₂ i j) := by
    rw [← hker₂, LinearMap.ker_comp, LinearEquiv.ker, Submodule.comap_bot]

  have hF := Module.span_det_submatrix_eq_of_ker_eq_span_range Φ₁ hΦ₁s X₁ hX₁ Φ₂ hΦ₂s X₂ hX₂
  rw [DLA.span_range_det_submatrix_square, DLA.span_range_det_submatrix_square] at hF
  have hdet₁ : X₁.det = e (Ideal.Quotient.mk _ (Matrix.det (Matrix.of fun i j => MvPolynomial.pderiv j (f i)))) := by
    have hX : X₁ = φ.toRingHom.mapMatrix (Matrix.of fun i j => MvPolynomial.pderiv j (f i)).transpose := by
      ext a b; rfl
    rw [hX, ← RingHom.map_det, Matrix.det_transpose]
    rfl
  have hdet₂ : X₂.det = ((p : ℕ) : (G.level v)) ^ (n * v) := by
    rw [Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin, ← pow_mul, mul_comm]
  rw [hdet₁, hdet₂] at hF

  have hp0 : ((p : ℕ) : (PadicAlgCl.ringOfIntegers p K)) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have hp1 : ((p : ℕ) : (G.level v)) ∈ nonZeroDivisors (G.level v) := by
    refine Submonoid.mem_carrier.mp ?_
    show ((p : ℕ) : (G.level v)) ∈ (nonZeroDivisors (G.level v) : Set (G.level v))
    rw [SetLike.mem_coe, mem_nonZeroDivisors_iff_right]
    intro a ha
    have : ((p : ℕ) : (PadicAlgCl.ringOfIntegers p K)) • a = 0 := by
      rw [Algebra.smul_def, map_natCast, mul_comm]; exact ha
    exact (smul_eq_zero.mp this).resolve_left hp0
  have hnzd : ((p : ℕ) : (G.level v)) ^ (n * v) ∈ nonZeroDivisors (G.level v) := pow_mem hp1 _
  exact DLA.associated_of_span_singleton_eq_of_mem_nonZeroDivisors hF hnzd

end S_PDivisibleGroup_associated_jacobianDet_pow_of_hasDimension_of_ringOfIntegers
end P2MW
export P2MW.S_PDivisibleGroup_associated_jacobianDet_pow_of_hasDimension_of_ringOfIntegers (solution)
