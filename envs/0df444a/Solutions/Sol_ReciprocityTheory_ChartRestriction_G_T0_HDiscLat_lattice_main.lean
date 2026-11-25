-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.HDiscLat.lattice_main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T15:51:17.48163+00:00
-- url     : https://prove2.me/submissions/85f9ae7d-3da6-4eb5-b48c-5e781c14b8d7

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HDiscAA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HDiscAB
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_HDiscLat_trace_term
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_HDiscLat_sum_three_comm
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_T0_HDiscLat_det_blockDiagonal__2f448d0cb1ca
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_HDiscLat_gram_mul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_HDiscLat_length_quot
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_Closed_dedekindRank


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0
open ReciprocityTheory.ChartRestriction.G.T0.HDiscLat
open Module
variable {R F : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field F]
  [Algebra R F] [IsFractionRing R F]
  {ι : Type} [Fintype ι] [DecidableEq ι] {L : ι → Type} [∀ c, Field (L c)] [∀ c, Algebra F (L c)]
  [∀ c, FiniteDimensional F (L c)] [∀ c, Algebra.IsSeparable F (L c)] [∀ c, Algebra R (L c)]
  [∀ c, IsScalarTower R F (L c)]
namespace ReciprocityTheory.ChartRestriction.G.T0.HDiscLat
theorem _root_.solution {ϖ : R} (hϖ : Irreducible ϖ) (g : ∀ c, L c) (hg : ∀ c, g c ≠ 0)
    {m : ℕ} (hm : m = ∑ c, finrank F (L c)) (b : Fin m → ∀ c, L c)
    (hb : ∀ k c, g c * b k c ∈ integralClosure R (L c)) (hli : LinearIndependent F b) :
    ∃ n t : ℕ, ∃ u : Rˣ,
      Module.length R
        (↥(Submodule.span R {y : ∀ c, L c | ∀ c, g c * y c ∈ integralClosure R (L c)}) ⧸
          (Submodule.span R (Set.range b)).comap
            (Submodule.span R {y : ∀ c, L c | ∀ c, g c * y c ∈ integralClosure R (L c)}).subtype) = n ∧
      (Matrix.of fun k l : Fin m => ∑ c, Algebra.trace F (L c) (b k c * b l c)).det *
          (∏ c, Algebra.norm F (g c)) ^ 2 = algebraMap R F (↑u * ϖ ^ (2 * n + t)) := by
  classical
  have hB : ∀ c, Module.Finite R (integralClosure R (L c)) ∧
      Module.Free R (integralClosure R (L c)) ∧
      finrank R (integralClosure R (L c)) = finrank F (L c) := fun c => by
    obtain ⟨_, h1, h2, h3, _⟩ := ReciprocityTheory.MultiplicativeHeights.Closed.dedekindRank R F (L c)
    exact ⟨h1, h2, h3⟩
  haveI : ∀ c, Module.Finite R (integralClosure R (L c)) := fun c => (hB c).1
  haveI : ∀ c, Module.Free R (integralClosure R (L c)) := fun c => (hB c).2.1
  let a := fun c => Module.Free.chooseBasis R (integralClosure R (L c))
  let α := Pi.basis a
  have hcard : Fintype.card (Σ c, Module.Free.ChooseBasisIndex R (integralClosure R (L c))) = m := by
    rw [hm, Fintype.card_sigma]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [← Module.finrank_eq_card_chooseBasisIndex, (hB c).2.2]
  let σ := Fintype.equivFinOfCardEq hcard
  let φ : (∀ c, integralClosure R (L c)) →ₗ[R] (∀ c, L c) :=
    LinearMap.pi fun c => (LinearMap.mulLeft R (g c)⁻¹) ∘ₗ
      (integralClosure R (L c)).val.toLinearMap ∘ₗ LinearMap.proj c
  have hφ : ∀ x c, φ x c = (g c)⁻¹ * (x c : L c) := fun x c => rfl
  have hφinj : Function.Injective φ := by
    intro x y hxy
    funext c
    apply Subtype.ext
    have := congrFun hxy c
    rw [hφ, hφ] at this
    exact mul_left_cancel₀ (inv_ne_zero (hg c)) this
  have hSA : Submodule.span R {y : ∀ c, L c | ∀ c, g c * y c ∈ integralClosure R (L c)} =
      LinearMap.range φ := by
    apply le_antisymm
    · rw [Submodule.span_le]
      intro y hy
      refine ⟨fun c => ⟨g c * y c, hy c⟩, ?_⟩
      funext c
      rw [hφ]
      simp [← mul_assoc, inv_mul_cancel₀ (hg c)]
    · rintro _ ⟨x, rfl⟩
      apply Submodule.subset_span
      intro c
      rw [hφ, ← mul_assoc, mul_inv_cancel₀ (hg c), one_mul]
      exact (x c).2
  let b' : Fin m → ∀ c, integralClosure R (L c) := fun k c => ⟨g c * b k c, hb k c⟩
  have hb' : φ ∘ b' = b := by
    funext k c
    simp only [Function.comp_apply]
    rw [hφ]
    simp [b', ← mul_assoc, inv_mul_cancel₀ (hg c)]
  have hliR : LinearIndependent R b :=
    hli.restrict_scalars (by
      intro x y hxy
      simp only [Algebra.smul_def, mul_one] at hxy
      exact IsFractionRing.injective R F hxy)
  have hli' : LinearIndependent R b' := LinearIndependent.of_comp φ (by rw [hb']; exact hliR)
  obtain ⟨n, u, hlen, hdet⟩ := length_quot hϖ α φ hφinj _ hSA b' hli' σ
  rw [hb'] at hlen
  set T := α.toMatrix (b' ∘ σ) with hT
  have hdetT : T.det = ↑u * ϖ ^ n := by rw [hT, ← Basis.det_apply]; exact hdet
  have hexp : ∀ q c, ((b' (σ q) c : integralClosure R (L c)) : L c) =
      ∑ p, algebraMap R (L c) (T p q) * ((α p c : integralClosure R (L c)) : L c) := by
    intro q c
    have h1 := congrArg (fun x : (∀ c, integralClosure R (L c)) =>
      ((x c : integralClosure R (L c)) : L c)) (α.sum_repr (b' (σ q)))
    simp only [Finset.sum_apply, Pi.smul_apply] at h1
    rw [← h1]
    simp only [AddSubmonoidClass.coe_finsetSum, SetLike.val_smul, hT,
      Basis.toMatrix_apply, Function.comp_apply]
    simp only [Algebra.smul_def]
  have hbexp : ∀ q c, b (σ q) c = ∑ p, algebraMap R (L c) (T p q) *
      ((g c)⁻¹ * ((α p c : integralClosure R (L c)) : L c)) := by
    intro q c
    have : b (σ q) c = (g c)⁻¹ * ((b' (σ q) c : integralClosure R (L c)) : L c) := by
      rw [← hb']; rfl
    rw [this, hexp, Finset.mul_sum]
    exact Finset.sum_congr rfl fun p _ => by ring
  let H : Matrix (Σ c, Module.Free.ChooseBasisIndex R (integralClosure R (L c)))
      (Σ c, Module.Free.ChooseBasisIndex R (integralClosure R (L c))) F :=
    Matrix.of fun p q => ∑ c, Algebra.trace F (L c) ((g c)⁻¹ * (g c)⁻¹ *
      ((α p c : integralClosure R (L c)) : L c) * ((α q c : integralClosure R (L c)) : L c))
  have hG : (Matrix.of fun k l : Fin m => ∑ c, Algebra.trace F (L c) (b k c * b l c)).submatrix σ σ =
      (T.map (algebraMap R F)).transpose * H * T.map (algebraMap R F) := by
    ext p' q'
    simp only [Matrix.submatrix_apply, Matrix.of_apply, Matrix.mul_apply, Matrix.transpose_apply,
      Matrix.map_apply, H, hbexp]
    simp only [Finset.sum_mul, Finset.mul_sum, map_sum, trace_term]
    rw [sum_three_comm, Finset.sum_comm]
  have hH : H = Matrix.blockDiagonal' fun c => Matrix.of fun i j => Algebra.trace F (L c)
      ((g c)⁻¹ * (g c)⁻¹ * ((a c i : integralClosure R (L c)) : L c) *
        ((a c j : integralClosure R (L c)) : L c)) := by
    ext ⟨c, i⟩ ⟨c', j⟩
    simp only [H, Matrix.of_apply, α, Pi.basis_apply]
    rw [Finset.sum_eq_single c]
    · by_cases hc : c = c'
      · subst hc
        simp [Matrix.blockDiagonal'_apply_eq]
      · rw [Matrix.blockDiagonal'_apply_ne _ _ _ hc, Pi.single_eq_of_ne hc]
        simp
    · intro c'' _ hc''
      rw [Pi.single_eq_of_ne hc'']
      simp
    · simp
  haveI : ∀ c, IsLocalization (Algebra.algebraMapSubmonoid (integralClosure R (L c))
      (nonZeroDivisors R)) (L c) := fun c =>
    IsIntegralClosure.isLocalization R F (L c) (integralClosure R (L c))
  let a' := fun c => (a c).localizationLocalization F (nonZeroDivisors R) (L c)
  have hblock : ∀ c, (Matrix.of fun i j => Algebra.trace F (L c)
      ((g c)⁻¹ * (g c)⁻¹ * ((a c i : integralClosure R (L c)) : L c) *
        ((a c j : integralClosure R (L c)) : L c))).det =
      Algebra.norm F ((g c)⁻¹ * (g c)⁻¹) * algebraMap R F (Algebra.discr R (a c)) := by
    intro c
    rw [← Algebra.discr_localizationLocalization R (nonZeroDivisors R) (L c) (a c), ← gram_mul]
    congr 1
    ext i j
    simp only [Matrix.of_apply, a', Module.Basis.localizationLocalization_apply]
    rfl
  have hd0 : ∀ c, Algebra.discr R (a c) ≠ 0 := by
    intro c h
    have := Algebra.discr_not_zero_of_basis F (a' c)
    rw [Algebra.discr_localizationLocalization R (nonZeroDivisors R) (L c) (a c), h, map_zero] at this
    exact this rfl
  have hN : ∀ c, Algebra.norm F ((g c)⁻¹ * (g c)⁻¹) * Algebra.norm F (g c) ^ 2 = 1 := by
    intro c
    have h1 : Algebra.norm F (g c)⁻¹ * Algebra.norm F (g c) = 1 := by
      rw [← map_mul, inv_mul_cancel₀ (hg c), map_one]
    rw [map_mul, sq]
    calc Algebra.norm F (g c)⁻¹ * Algebra.norm F (g c)⁻¹ * (Algebra.norm F (g c) * Algebra.norm F (g c))
        = (Algebra.norm F (g c)⁻¹ * Algebra.norm F (g c)) *
          (Algebra.norm F (g c)⁻¹ * Algebra.norm F (g c)) := by ring
      _ = 1 := by rw [h1, one_mul]
  have hprod : (∏ c, Algebra.discr R (a c)) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun c _ => hd0 c
  obtain ⟨t, v, hv⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hprod hϖ
  refine ⟨n, t, u * u * v, hlen, ?_⟩
  rw [← Matrix.det_submatrix_equiv_self σ, hG, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose,
    hH, det_blockDiagonal', Finset.prod_congr rfl fun c _ => hblock c]
  have hmap : (T.map (algebraMap R F)).det = algebraMap R F T.det := by
    rw [RingHom.map_det]; rfl
  rw [hmap, hdetT, Finset.prod_mul_distrib, ← map_prod, hv]
  have hNN : (∏ c, Algebra.norm F ((g c)⁻¹ * (g c)⁻¹)) * (∏ c, Algebra.norm F (g c)) ^ 2 = 1 := by
    rw [← Finset.prod_pow, ← Finset.prod_mul_distrib]
    exact Finset.prod_eq_one fun c _ => hN c
  calc algebraMap R F (↑u * ϖ ^ n) * ((∏ c, Algebra.norm F ((g c)⁻¹ * (g c)⁻¹)) *
          algebraMap R F (↑v * ϖ ^ t)) * algebraMap R F (↑u * ϖ ^ n) * (∏ c, Algebra.norm F (g c)) ^ 2
      = algebraMap R F (↑u * ϖ ^ n) * algebraMap R F (↑v * ϖ ^ t) * algebraMap R F (↑u * ϖ ^ n) *
          ((∏ c, Algebra.norm F ((g c)⁻¹ * (g c)⁻¹)) * (∏ c, Algebra.norm F (g c)) ^ 2) := by ring
    _ = algebraMap R F (↑(u * u * v) * ϖ ^ (2 * n + t)) := by
      rw [hNN, mul_one, ← map_mul, ← map_mul]
      congr 1
      rw [Units.val_mul, Units.val_mul, pow_add, pow_mul]
      ring
end ReciprocityTheory.ChartRestriction.G.T0.HDiscLat
