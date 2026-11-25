-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.Data.basis_block0
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T15:08:59.7348+00:00
-- url     : https://prove2.me/submissions/581a2024-af65-4195-a7a4-5417ce520173

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_DecompBlock0
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_BasisBlock0
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_Data_decomp_block0
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_VariableBasisExtension_basis_extend


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0
open NumberField
variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]
  {𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)}
open ReciprocityTheory.ChartRestriction.G.T0.Data
variable (d : Data K ι Ω WT A)
namespace ReciprocityTheory.ChartRestriction.G.T0.Data
theorem _root_.solution (hd : d.AxH 𝒜) (h : d.S1) (c : ι) :
    letI : Algebra (KTf K d.D d.N) (OmS (Ω c) d.D d.N) := (d.KTtoS h c).toAlgebra;
    ∃ (n : ℕ) (b : Module.Basis (Fin n) (KTf K d.D d.N) (OmS (Ω c) d.D d.N)) (Q0 : KTp K d.D d.N)
      (M : Fin (d.N + 1) → Matrix (Fin n) (Fin n) (KTp K d.D d.N)),
      Q0 ≠ 0 ∧ (∀ x, d.sub0 x Q0 = Q0) ∧ (∀ j a a' x, d.sub0 x (M j a a') = M j a a') ∧
      ∀ j, Algebra.leftMulMatrix b (algebraMap (Ω c) (OmS (Ω c) d.D d.N)
          (ratio (Ω := Ω c) (d.w j c) (d.w (d.jc c) c))) =
        (M j).map fun q => algebraMap (KTp K d.D d.N) (KTf K d.D d.N) q /
          algebraMap (KTp K d.D d.N) (KTf K d.D d.N) Q0 := by
  letI _inst : Algebra (KTf K d.D d.N) (OmS (Ω c) d.D d.N) := (d.KTtoS h c).toAlgebra
  obtain ⟨L, E, _, _, _, _, eL, eE, hcomp, hconst, hLc⟩ := d.decomp_block0 hd h c
  letI iLY : Algebra (FractionRing (MvPolynomial (Fin (d.N + 1)) L))
      (FractionRing (MvPolynomial (Fin (d.N + 1)) E)) :=
    (VariableBasisExtension.liftY (L := L) (E := E) (σ := Fin (d.N + 1))).toAlgebra
  obtain ⟨b', _, hb'2⟩ := VariableBasisExtension.basis_extend (σ := Fin (d.N + 1)) (Module.finBasis L E)
  letI iFO : Algebra (FractionRing (MvPolynomial (Fin (d.N + 1)) L)) (OmS (Ω c) d.D d.N) :=
    ((d.KTtoS h c).comp eL.symm.toRingHom).toAlgebra
  have hback : ∀ q : FractionRing (MvPolynomial (Fin (d.N + 1)) L),
      eE.symm (VariableBasisExtension.liftY q) = d.KTtoS h c (eL.symm q) := by
    intro q
    have h1 := hcomp (eL.symm q)
    rw [RingEquiv.apply_symm_apply] at h1
    rw [← h1, RingEquiv.symm_apply_apply]
  let eEl : FractionRing (MvPolynomial (Fin (d.N + 1)) E) ≃ₗ[FractionRing (MvPolynomial (Fin (d.N + 1)) L)]
      OmS (Ω c) d.D d.N :=
    AddEquiv.toLinearEquiv eE.symm.toAddEquiv (by
      intro q x
      show eE.symm (q • x) = q • eE.symm x
      rw [Algebra.smul_def, Algebra.smul_def, map_mul]
      congr 1
      exact hback q)
  let B0 := b'.map eEl
  let B : Module.Basis (Fin (Module.finrank L E)) (KTf K d.D d.N) (OmS (Ω c) d.D d.N) :=
    B0.mapCoeffs eL.symm (fun q x => rfl)
  have htr : ∀ (y : OmS (Ω c) d.D d.N) a a', Algebra.leftMulMatrix B y a a' =
      eL.symm (Algebra.leftMulMatrix b' (eE y) a a') := by
    intro y a a'
    rw [Algebra.leftMulMatrix_eq_repr_mul, Algebra.leftMulMatrix_eq_repr_mul]
    have hy : eEl.symm (y * eEl (b' a')) = eE y * b' a' := by
      show eE (y * eE.symm (b' a')) = eE y * b' a'
      rw [map_mul, RingEquiv.apply_symm_apply]
    simp only [B]
    erw [Module.Basis.mapCoeffs_apply, Module.Basis.mapCoeffs_repr]
    simp only [LinearEquiv.trans_apply, LinearEquiv.restrictScalars_apply, Finsupp.mapRange.linearEquiv_apply,
      Finsupp.mapRange_apply, B0, Module.Basis.map_apply, Module.Basis.map_repr]
    rw [hy]
    exact rfl
  choose e he using hconst
  choose P Q hQ hPinv hQinv hPQ using hLc
  let mm : Fin (d.N + 1) × Fin (Module.finrank L E) × Fin (Module.finrank L E) → L := fun t =>
    Algebra.leftMulMatrix (Module.finBasis L E)
      (e (ratio (Ω := Ω c) (d.w t.1 c) (d.w (d.jc c) c))) t.2.1 t.2.2
  have hinj := IsFractionRing.injective (KTp K d.D d.N) (KTf K d.D d.N)
  have hne : ∀ t, algebraMap (KTp K d.D d.N) (KTf K d.D d.N)
      (∏ s ∈ Finset.univ.erase t, Q (mm s)) ≠ 0 := by
    intro t
    rw [map_ne_zero_iff _ hinj]
    exact Finset.prod_ne_zero_iff.mpr fun s _ => hQ _
  have hfrac : ∀ t, algebraMap (KTp K d.D d.N) (KTf K d.D d.N) (P (mm t)) /
        algebraMap (KTp K d.D d.N) (KTf K d.D d.N) (Q (mm t)) =
      algebraMap (KTp K d.D d.N) (KTf K d.D d.N) (P (mm t) * ∏ s ∈ Finset.univ.erase t, Q (mm s)) /
        algebraMap (KTp K d.D d.N) (KTf K d.D d.N) (∏ s, Q (mm s)) := by
    intro t
    rw [← Finset.mul_prod_erase Finset.univ (fun s => Q (mm s)) (Finset.mem_univ t), map_mul, map_mul,
      mul_div_mul_right _ _ (hne t)]
  have hLtoC : ∀ l : L, algebraMap L (FractionRing (MvPolynomial (Fin (d.N + 1)) L)) l =
      algebraMap (MvPolynomial (Fin (d.N + 1)) L) (FractionRing (MvPolynomial (Fin (d.N + 1)) L))
        (MvPolynomial.C l) := by
    intro l
    rw [IsScalarTower.algebraMap_apply L (MvPolynomial (Fin (d.N + 1)) L)
      (FractionRing (MvPolynomial (Fin (d.N + 1)) L)), MvPolynomial.algebraMap_eq]
  refine ⟨Module.finrank L E, B, ∏ s, Q (mm s),
    fun j => Matrix.of fun a a' => P (mm (j, a, a')) * ∏ s ∈ Finset.univ.erase (j, a, a'), Q (mm s),
    ?_, ?_, ?_, ?_⟩
  · exact Finset.prod_ne_zero_iff.mpr fun s _ => hQ _
  · intro x
    rw [map_prod]
    exact Finset.prod_congr rfl fun s _ => hQinv _ x
  · intro j a a' x
    simp only [Matrix.of_apply]
    rw [map_mul, map_prod, hPinv]
    congr 1
    exact Finset.prod_congr rfl fun s _ => hQinv _ x
  · intro j
    ext a a'
    simp only [Matrix.map_apply, Matrix.of_apply]
    rw [htr, he, hb'2, Matrix.map_apply, hLtoC, hPQ]
    exact hfrac (j, a, a')
end ReciprocityTheory.ChartRestriction.G.T0.Data
