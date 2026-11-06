-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.GlobalPlace.globalAdeleSandwichRank_eq_defect_sub
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T19:12:43.407757+00:00
-- url     : https://prove2.me/submissions/7d6fb042-33b7-4c82-b491-8f4f2bade158

import Mathlib.Algebra.Order.GroupWithZero.Canonical
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.Isomorphisms
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Adeles_AdeleEffectiveIncrement
import Definitions.Def_QEC_Coding_AlgebraicGeometry_RiemannRoch_Genus
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Adeles_AdeleSandwich
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Divisor_degree_nonnegative
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Divisor_degree_sub
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Divisor_degree_zero
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_coe_constantsToValuationRing
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_globalAdeleFilterDiffDimension_of_le
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_globalAdeleFilterDiffQuotient_finite_of_le
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_globalAdeleFilter_inf_diagonal
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_globalAdeleFilter_mono
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_polarDivisor_zero
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_repackageEquiv_order
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_repackageEquiv_valuation
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_repackage_valuation
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_riemannRochSubmodule_mono
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_InverseAffinePlace_infinityFibre_nonempty
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_IsFullConstantField_mem_range
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_RatFuncDerivation_rationalDerivationEquiv_apply
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_RatFuncDerivation_rationalDerivationEquiv_symm_apply
attribute [local simp] QEC.Coding.AlgebraicGeometry.Divisor.degree_zero
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.coe_constantsToValuationRing
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.polarDivisor_zero
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.repackageEquiv_order
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.repackageEquiv_valuation
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.repackage_valuation
attribute [local simp] QEC.Coding.AlgebraicGeometry.RatFuncDerivation.rationalDerivationEquiv_apply
attribute [local simp] QEC.Coding.AlgebraicGeometry.RatFuncDerivation.rationalDerivationEquiv_symm_apply


section
namespace QEC.Coding.AlgebraicGeometry
open Filter
open scoped Polynomial RatFunc WithZero
noncomputable section
variable (k F : Type*) [Field k] [Finite k] [Field F]
variable [π : Algebra (Polynomial k) F] [ρ : Algebra (RatFunc k) F]
variable [τ : IsScalarTower (Polynomial k) (RatFunc k) F]
variable [φ : _root_.FunctionField k F]
variable [s : Algebra.IsSeparable (RatFunc k) F]
attribute [local instance] globalAdeleSandwichAlgebra
attribute [local instance] globalAdeleSandwichScalarTower
namespace GlobalPlace
variable [IsFullConstantField k F]
attribute [local instance] globalAdeleSandwichRiemannRochFiniteDimensional
attribute [local instance] globalAdeleSandwichFilterAddCommGroup
attribute [local instance] globalAdeleSandwichFilterModule
private theorem riemannRochFilterDiffDimension_add
    {D E : Divisor (GlobalPlace k F)} (hDE : D ≤ E) :
    riemannRochFilterDiffDimension (k := k) (F := F) D E +
        riemannRochDimension D =
      riemannRochDimension E := by
  let p := riemannRochSubmodule E
  let q := Submodule.comap p.subtype (riemannRochSubmodule D)
  have hq : Module.finrank k q = riemannRochDimension D := by
    let e := Submodule.comapSubtypeEquivOfLe
      (riemannRochSubmodule_mono (k := k) (F := F) hDE)
    simpa only [p, q, riemannRochDimension] using e.finrank_eq
  have hadd := Submodule.finrank_quotient_add_finrank q
  simpa only [riemannRochFilterDiffDimension, riemannRochDimension, p, q, hq]
    using hadd
private theorem globalPlace_nonempty : Nonempty (GlobalPlace k F) := by
  obtain ⟨D⟩ := InverseAffinePlace.infinityFibre_nonempty
    (oldRationalAlgebra := ρ) k F
  exact ⟨InverseAffinePlace.infinityFibreGlobalPlace
    (π := π) (ρ := ρ) (τ := τ) (φ := φ) (σ := s) D⟩
private theorem diagonalAdele_injective :
    Function.Injective (diagonalAdele (k := k) (F := F)) := by
  intro x y hxy
  let P := Classical.choice (globalPlace_nonempty
    (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F)
  have hvalue := congrArg
    (fun a : GlobalAdele (k := k) (F := F) => a.val P) hxy
  exact hvalue
private theorem finrank_map_comap_mkQ_eq_quotient
    {E : Divisor (GlobalPlace k F)}
    {s t : Submodule k (GlobalAdele (k := k) (F := F))}
    (_hs : s ≤ globalAdeleFilter (k := k) (F := F) E)
    (ht : t ≤ globalAdeleFilter (k := k) (F := F) E) (_hst : s ≤ t) :
    Module.finrank k
        (Submodule.map
          (Submodule.comap
            (globalAdeleFilter (k := k) (F := F) E).subtype s).mkQ
          (Submodule.comap
            (globalAdeleFilter (k := k) (F := F) E).subtype t)) =
      Module.finrank k
        (↥(Submodule.comap
            (globalAdeleFilter (k := k) (F := F) E).subtype t) ⧸
          Submodule.comap
            (Submodule.comap
              (globalAdeleFilter (k := k) (F := F) E).subtype t).subtype
            (Submodule.comap
              (globalAdeleFilter (k := k) (F := F) E).subtype s)) := by
  classical
  let p := globalAdeleFilter (k := k) (F := F) E
  let qp := Submodule.comap p.subtype s
  let qt := Submodule.comap p.subtype t
  let st := Submodule.comap t.subtype s
  let qpInQt := Submodule.comap qt.subtype qp
  letI : AddCommGroup t := Submodule.addCommGroup _
  letI : Module k t := Submodule.module _
  letI : AddCommGroup qt := Submodule.addCommGroup _
  letI : Module k qt := Submodule.module _
  let eT := Submodule.comapSubtypeEquivOfLe ht
  have hmap : st.map (eT.symm : t →ₗ[k] qt) = qpInQt := by
    ext x
    simp [Submodule.mem_comap, st, qpInQt, qp, qt, eT]
  have hker : (qp.mkQ.comp (qt.subtype : qt →ₗ[k] p)).ker = qpInQt := by
    rw [LinearMap.ker_comp, Submodule.ker_mkQ]
  have hrange : (qp.mkQ.comp (qt.subtype : qt →ₗ[k] p)).range =
      Submodule.map qp.mkQ qt := by
    rw [LinearMap.range_comp, Submodule.range_subtype]
  have eQuot : (qt ⧸ qpInQt) ≃ₗ[k] Submodule.map qp.mkQ qt := by
    rw [← hker, ← hrange]
    exact LinearMap.quotKerEquivRange (qp.mkQ.comp (qt.subtype : qt →ₗ[k] p))
  have eTS : (t ⧸ st) ≃ₗ[k] (qt ⧸ qpInQt) :=
    Submodule.Quotient.equiv st qpInQt eT.symm hmap
  rw [← eQuot.finrank_eq, ← eTS.finrank_eq]
end GlobalPlace
end
end QEC.Coding.AlgebraicGeometry
end

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
open Filter
open scoped Polynomial RatFunc WithZero
noncomputable section
variable (k F : Type*) [Field k] [Finite k] [Field F]
variable [π : Algebra (Polynomial k) F] [ρ : Algebra (RatFunc k) F]
variable [τ : IsScalarTower (Polynomial k) (RatFunc k) F]
variable [φ : _root_.FunctionField k F]
variable [s : Algebra.IsSeparable (RatFunc k) F]
attribute [local instance] QEC.Coding.AlgebraicGeometry.globalAdeleSandwichAlgebra
attribute [local instance] globalAdeleSandwichAlgebra
attribute [local instance] QEC.Coding.AlgebraicGeometry.globalAdeleSandwichScalarTower
attribute [local instance] globalAdeleSandwichScalarTower
open QEC.Coding.AlgebraicGeometry.GlobalPlace
variable [IsFullConstantField k F]
attribute [local instance] QEC.Coding.AlgebraicGeometry.GlobalPlace.globalAdeleSandwichRiemannRochFiniteDimensional
attribute [local instance] globalAdeleSandwichRiemannRochFiniteDimensional
attribute [local instance] QEC.Coding.AlgebraicGeometry.GlobalPlace.globalAdeleSandwichFilterAddCommGroup
attribute [local instance] globalAdeleSandwichFilterAddCommGroup
attribute [local instance] QEC.Coding.AlgebraicGeometry.GlobalPlace.globalAdeleSandwichFilterModule
attribute [local instance] globalAdeleSandwichFilterModule
namespace QEC.Coding.AlgebraicGeometry.GlobalPlace
theorem _root_.solution
    {D E : Divisor (GlobalPlace k F)} (hDE : D ≤ E) :
    globalAdeleSandwichRank (k := k) (F := F) D E hDE =
      riemannRochDefect (k := k) (F := F) E -
        riemannRochDefect (k := k) (F := F) D := by
  let p := globalAdeleFilter (k := k) (F := F) E
  let sA := globalAdeleFilter (k := k) (F := F) D
  let r := diagonalAdeleSubmodule (k := k) (F := F)
  let l := Submodule.map (diagonalAdele (k := k) (F := F))
    (riemannRochSubmodule E)
  let t := l ⊔ sA
  have hs_le_p : sA ≤ p := globalAdeleFilter_mono hDE
  have hst : sA ≤ t := le_sup_right
  have htp : t ≤ p := by
    rintro x hx
    rcases Submodule.mem_sup.mp hx with ⟨y, hy, z, hz, rfl⟩
    rcases hy with ⟨f, hf, rfl⟩
    exact Submodule.add_mem p
      (by exact hf)
      (hs_le_p hz)
  have hmod : p ⊓ (sA + r) = sA + p ⊓ r := by
    apply le_antisymm
    · rintro x ⟨hxp, hxsr⟩
      rcases Submodule.mem_sup.mp hxsr with ⟨a, has, y, hy, rfl⟩
      obtain ⟨f, rfl⟩ := LinearMap.mem_range.mp hy
      refine Submodule.mem_sup.mpr ⟨a, has, diagonalAdele (k := k) (F := F) f,
        ?_, rfl⟩
      exact Submodule.mem_inf.mpr
        ⟨(by simpa only [add_sub_cancel_left] using
            Submodule.sub_mem p hxp (hs_le_p has)), hy⟩
    · rintro x hx
      rcases Submodule.mem_sup.mp hx with ⟨a, has, y, hy, rfl⟩
      rcases Submodule.mem_inf.mp hy with ⟨hyp, hyr⟩
      exact ⟨Submodule.add_mem p (hs_le_p has) hyp,
        Submodule.add_mem (sA + r) (Submodule.mem_sup_left has)
          (Submodule.mem_sup_right hyr)⟩
  have hinter : p ⊓ (sA + r) = t := by
    have hpr : p ⊓ r = l := globalAdeleFilter_inf_diagonal E
    calc
      p ⊓ (sA + r) = sA + (p ⊓ r) := hmod
      _ = sA + l := by rw [hpr]
      _ = t := by simp only [t, Submodule.add_eq_sup, sup_comm]
  letI : AddCommGroup p := Submodule.addCommGroup _
  letI : Module k p := Submodule.module _
  letI : AddCommGroup (p + r) := Submodule.addCommGroup _
  letI : Module k (p + r) := Submodule.module _
  let qp := Submodule.comap p.subtype sA
  let qt := Submodule.comap p.subtype t
  have hqp : qp ≤ qt := Submodule.comap_mono hst
  have hpsum : p ⊔ (sA + r) = p + r := by
    rw [← Submodule.add_eq_sup]
    apply le_antisymm
    · exact sup_le le_sup_left (add_le_add hs_le_p le_rfl)
    · intro x hx
      rcases Submodule.mem_sup.mp hx with ⟨a, ha, b, hb, rfl⟩
      have hb' : b ∈ sA + r := Submodule.mem_sup_right hb
      exact Submodule.add_mem _ (Submodule.mem_sup_left ha)
        (Submodule.mem_sup_right hb')
  letI : AddCommGroup ↥(p ⊔ (sA + r)) := Submodule.addCommGroup _
  letI : Module k ↥(p ⊔ (sA + r)) := Submodule.module _
  have e1 := LinearMap.quotientInfEquivSupQuotient p (sA + r)
  have hsand :
      Module.finrank k
          ((p + r) ⧸ Submodule.comap (p + r).subtype (sA + r)) =
        Module.finrank k (p ⧸ qt) := by
    have hinfl :
        Submodule.comap p.subtype p ⊓ Submodule.comap p.subtype (sA + r) = qt := by
      rw [← Submodule.comap_inf, hinter]
    have hfin := e1.symm.finrank_eq
    rw [← hpsum.symm, hinfl] at hfin
    exact hfin
  haveI : Module.Finite k (p ⧸ qp) :=
    globalAdeleFilterDiffQuotient_finite_of_le hDE
  have e2 := Submodule.quotientQuotientEquivQuotient qp qt hqp
  have hsecond :
      Module.finrank k (Submodule.map qp.mkQ qt) =
        riemannRochFilterDiffDimension (k := k) (F := F) D E := by
    have hfin_map := finrank_map_comap_mkQ_eq_quotient
      (k := k) (F := F) hs_le_p htp hst
    let st := Submodule.comap t.subtype sA
    let qpInQt := Submodule.comap qt.subtype qp
    letI : AddCommGroup t := Submodule.addCommGroup _
    letI : Module k t := Submodule.module _
    let eT := Submodule.comapSubtypeEquivOfLe htp
    have hmap : st.map (eT.symm : t →ₗ[k] qt) = qpInQt := by
      ext x
      simp [Submodule.mem_comap, st, qpInQt, qp, qt, eT]
    have eTS : (t ⧸ st) ≃ₗ[k] (qt ⧸ qpInQt) :=
      Submodule.Quotient.equiv st qpInQt eT.symm hmap
    have e3 := LinearMap.quotientInfEquivSupQuotient l sA
    letI : AddCommGroup ↥(l ⊔ sA) := Submodule.addCommGroup _
    letI : Module k ↥(l ⊔ sA) := Submodule.module _
    letI : AddCommGroup l := Submodule.addCommGroup _
    letI : Module k l := Submodule.module _
    calc
      Module.finrank k (Submodule.map qp.mkQ qt) =
          Module.finrank k (qt ⧸ Submodule.comap qt.subtype qp) := hfin_map
      _ = Module.finrank k (t ⧸ st) := eTS.finrank_eq.symm
      _ = Module.finrank k
          (↥(l ⊔ sA) ⧸ Submodule.comap (l ⊔ sA).subtype sA) := rfl
      _ = Module.finrank k
          (l ⧸ (Submodule.comap l.subtype l ⊓
            Submodule.comap l.subtype sA)) := e3.symm.finrank_eq
      _ = riemannRochFilterDiffDimension (k := k) (F := F) D E := by
        let pR := riemannRochSubmodule E
        let qR := Submodule.comap pR.subtype (riemannRochSubmodule D)
        let qInL : Submodule k l := Submodule.comap l.subtype
          (Submodule.map (diagonalAdele (k := k) (F := F))
            (riemannRochSubmodule D))
        let f' := (diagonalAdele (k := k) (F := F)).comp pR.subtype
        have hf' : ∀ g, f' g ∈ l := fun g =>
          Submodule.mem_map.mpr ⟨g, g.property, rfl⟩
        let f : pR →ₗ[k] l := f'.codRestrict l hf'
        have hf_inj : Function.Injective f := by
          intro g₁ g₂ hfg
          apply Subtype.ext
          apply diagonalAdele_injective (k := k) (F := F)
          exact congrArg Subtype.val hfg
        have hf_surj : Function.Surjective f := by
          rintro ⟨a, g, hg, rfl⟩
          exact ⟨⟨g, hg⟩, rfl⟩
        let eL : pR ≃ₗ[k] l := LinearEquiv.ofBijective f ⟨hf_inj, hf_surj⟩
        have hld : l ⊓ sA =
            Submodule.map (diagonalAdele (k := k) (F := F))
              (riemannRochSubmodule D) := by
          rw [show l = p ⊓ r from (globalAdeleFilter_inf_diagonal E).symm]
          rw [inf_right_comm, inf_eq_right.mpr hs_le_p,
            globalAdeleFilter_inf_diagonal D]
        have hmapR : qR.map f = qInL := by
          ext x
          simp only [Submodule.mem_map, Submodule.mem_comap, qR, qInL, l]
          constructor
          · rintro ⟨g, hg, heq⟩
            refine ⟨g.val, ?_, ?_⟩
            · exact hg
            · rw [← heq]
              rfl
          · rintro ⟨y, hy, hxy⟩
            refine ⟨⟨y, riemannRochSubmodule_mono (k := k) (F := F) hDE hy⟩,
              hy, ?_⟩
            apply Subtype.ext
            exact hxy
        have eQuot : (pR ⧸ qR) ≃ₗ[k] (l ⧸ qInL) :=
          Submodule.Quotient.equiv qR qInL eL hmapR
        dsimp only [riemannRochFilterDiffDimension]
        rw [← Submodule.comap_inf, hld, eQuot.finrank_eq]
  have hsplit :
      Module.finrank k (p ⧸ qt) =
        globalAdeleFilterDiffDimension (k := k) (F := F) D E -
          riemannRochFilterDiffDimension (k := k) (F := F) D E := by
    have hle : Module.finrank k (Submodule.map qp.mkQ qt) ≤
        Module.finrank k (p ⧸ qp) := Submodule.finrank_le _
    have hadd := Submodule.finrank_quotient_add_finrank (Submodule.map qp.mkQ qt)
    rw [e2.finrank_eq, hsecond] at hadd
    dsimp only [globalAdeleFilterDiffDimension]
    exact (Nat.sub_eq_of_eq_add hadd.symm).symm
  have hfilter := globalAdeleFilterDiffDimension_of_le
    (k := k) (F := F) hDE
  have hdegreeNonnegative : 0 ≤
      Divisor.degree (residueDegree (k := k) (F := F)) (E - D) := by
    apply Divisor.degree_nonnegative
    intro P
    exact sub_nonneg.mpr (hDE P)
  have hrr := riemannRochFilterDiffDimension_add
    (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F hDE
  have hle : riemannRochFilterDiffDimension (k := k) (F := F) D E ≤
      globalAdeleFilterDiffDimension (k := k) (F := F) D E := by
    dsimp only [globalAdeleFilterDiffDimension]
    rw [← hsecond]
    exact Submodule.finrank_le _
  have hmain :
      globalAdeleSandwichRank (k := k) (F := F) D E hDE =
        (globalAdeleFilterDiffDimension (k := k) (F := F) D E : ℤ) -
          riemannRochFilterDiffDimension (k := k) (F := F) D E := by
    dsimp only [globalAdeleSandwichRank]
    rw [hsand, hsplit]
    simp only [Int.ofNat_eq_natCast, Nat.cast_sub hle]
  have hfilterZ :
      (globalAdeleFilterDiffDimension (k := k) (F := F) D E : ℤ) =
        Divisor.degree (residueDegree (k := k) (F := F)) (E - D) := by
    rw [hfilter, Int.toNat_of_nonneg hdegreeNonnegative]
  have hrrZ :
      (riemannRochFilterDiffDimension (k := k) (F := F) D E : ℤ) =
        (riemannRochDimension E : ℤ) - riemannRochDimension D := by
    have hrrInt :
        (riemannRochFilterDiffDimension (k := k) (F := F) D E : ℤ) +
            (riemannRochDimension D : ℤ) =
          (riemannRochDimension E : ℤ) := by
      exact_mod_cast hrr
    omega
  rw [hmain, hfilterZ, hrrZ, Divisor.degree_sub]
  simp only [riemannRochDefect]
  ring
end QEC.Coding.AlgebraicGeometry.GlobalPlace
