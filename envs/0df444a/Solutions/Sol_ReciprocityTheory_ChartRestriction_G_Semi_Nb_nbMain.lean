-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Semi.Nb.nbMain
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T14:27:55.473054+00:00
-- url     : https://prove2.me/submissions/deda7ad1-3189-4e4b-bd29-05296d412435

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_GenericFiberGluing_SemistableCompleteSplit
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.DiscreteValuationRing.TFAE
import Mathlib.RingTheory.AdicCompletion.Noetherian
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.FieldTheory.Minpoly.Field
import Mathlib.FieldTheory.Tower
import Mathlib.Algebra.Polynomial.Eval.Irreducible
import Mathlib.RingTheory.Polynomial.UniqueFactorization
import Mathlib.Algebra.Polynomial.Lifts
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_IsPrecompleteOfBasis
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Semi_Nb_exists_monic_lift
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Semi_Nb_isDomain
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Semi_Nb_finite
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Semi_Nb_inj
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Semi_Nb_isLocal
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Semi_Nb_dvr
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Semi_Nb_complete
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Semi_Nb_resEquiv_comp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open IsLocalRing Polynomial
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi
open ReciprocityTheory.ChartRestriction.G.Semi.Nb
namespace ReciprocityTheory.ChartRestriction.G.Semi.Nb
theorem _root_.solution (n : ℕ) : ∀ (V' : Type) [CommRing V'] [IsDomain V'] [IsDiscreteValuationRing V']
    [IsAdicComplete (maximalIdeal V') V']
    (k'' : Type) [Field k''] [Algebra (ResidueField V') k'']
    [FiniteDimensional (ResidueField V') k''], Module.finrank (ResidueField V') k'' = n →
    ∃ (V'' : Type) (_ : CommRing V'') (_ : IsDomain V'') (_ : IsDiscreteValuationRing V'')
      (_ : IsAdicComplete (maximalIdeal V'') V'') (_ : Algebra V' V''),
      Module.Finite V' V'' ∧ Function.Injective (algebraMap V' V'') ∧
      ∃ (_ : IsLocalHom (algebraMap V' V'')) (e : k'' ≃+* ResidueField V''),
        e.toRingHom.comp (algebraMap (ResidueField V') k'') =
          ResidueField.map (algebraMap V' V'') := by
  refine Nat.strong_induction_on n fun n ih => ?_
  intro V' _ _ _ _ k'' _ _ _ hn
  by_cases hs : Function.Surjective (algebraMap (ResidueField V') k'')
  · let e0 : ResidueField V' ≃+* k'' := RingEquiv.ofBijective (algebraMap (ResidueField V') k'')
      ⟨(algebraMap (ResidueField V') k'').injective, hs⟩
    refine ⟨V', inferInstance, inferInstance, inferInstance, inferInstance, Algebra.id V',
      Module.Finite.self V', fun x y h => h, ⟨fun x hx => hx⟩, e0.symm, ?_⟩
    refine RingHom.ext fun x => ?_
    obtain ⟨y, rfl⟩ := residue_surjective x
    rw [RingHom.comp_apply, ResidueField.map_residue]
    exact e0.symm_apply_apply (residue V' y)
  · obtain ⟨a, ha⟩ : ∃ a : k'', a ∉ (algebraMap (ResidueField V') k'').range := by
      by_contra h
      push_neg at h
      exact hs fun x => RingHom.mem_range.mp (h x)
    have hint : IsIntegral (ResidueField V') a := Algebra.IsIntegral.isIntegral a
    obtain ⟨f, hfg, -, hf⟩ := exists_monic_lift (minpoly (ResidueField V') a) (minpoly.monic hint)
    have hg : Irreducible (f.map (residue V')) := by
      rw [hfg]
      exact minpoly.irreducible hint
    haveI := isLocal f hf hg
    haveI := isDomain f hf hg
    haveI := locHom f hf hg
    haveI := dvr f hf hg
    haveI := complete f hf hg
    haveI := finite f hf
    have hroot : (f.map (residue V')).eval₂ (algebraMap (ResidueField V') k'') a = 0 := by
      rw [hfg, ← aeval_def]
      exact minpoly.aeval _ a
    letI : Algebra (ResidueField (AdjoinRoot f)) k'' := RingHom.toAlgebra
      ((AdjoinRoot.lift (f := f.map (residue V')) (algebraMap (ResidueField V') k'') a hroot).comp
        (resEquiv f hf hg).toRingHom)
    have htow_eq : algebraMap (ResidueField V') k'' =
        (algebraMap (ResidueField (AdjoinRoot f)) k'').comp
          (algebraMap (ResidueField V') (ResidueField (AdjoinRoot f))) := by
      refine RingHom.ext fun x => ?_
      have hc : (resEquiv f hf hg) (ResidueField.map (algebraMap V' (AdjoinRoot f)) x) =
          AdjoinRoot.of (f.map (residue V')) x := RingHom.congr_fun (resEquiv_comp f hf hg) x
      change _ = AdjoinRoot.lift (f := f.map (residue V')) (algebraMap (ResidueField V') k'') a hroot
        ((resEquiv f hf hg) (ResidueField.map (algebraMap V' (AdjoinRoot f)) x))
      rw [hc, AdjoinRoot.lift_of]
    haveI : IsScalarTower (ResidueField V') (ResidueField (AdjoinRoot f)) k'' :=
      IsScalarTower.of_algebraMap_eq' htow_eq
    haveI : FiniteDimensional (ResidueField (AdjoinRoot f)) k'' :=
      Module.Finite.of_restrictScalars_finite (ResidueField V') (ResidueField (AdjoinRoot f)) k''
    have hdim : 2 ≤ Module.finrank (ResidueField V') (ResidueField (AdjoinRoot f)) := by
      let E : ResidueField (AdjoinRoot f) ≃ₐ[ResidueField V'] AdjoinRoot (f.map (residue V')) :=
        AlgEquiv.ofRingEquiv (f := resEquiv f hf hg) fun x => RingHom.congr_fun (resEquiv_comp f hf hg) x
      rw [E.toLinearEquiv.finrank_eq, (AdjoinRoot.powerBasis hg.ne_zero).finrank,
        AdjoinRoot.powerBasis_dim, hfg]
      have h1 : (minpoly (ResidueField V') a).natDegree ≠ 1 := fun h =>
        ha (minpoly.natDegree_eq_one_iff.mp h)
      have h2 := minpoly.natDegree_pos hint
      omega
    have hlt : Module.finrank (ResidueField (AdjoinRoot f)) k'' < n := by
      have h1 := Module.finrank_mul_finrank (ResidueField V') (ResidueField (AdjoinRoot f)) k''
      have h2 : 0 < Module.finrank (ResidueField (AdjoinRoot f)) k'' := Module.finrank_pos
      rw [hn] at h1
      nlinarith
    obtain ⟨V2, i1, i2, i3, i4, i5, hfin, hinj, hloc, e, he⟩ := ih _ hlt (AdjoinRoot f) k'' rfl
    letI : Algebra V' V2 :=
      ((algebraMap (AdjoinRoot f) V2).comp (algebraMap V' (AdjoinRoot f))).toAlgebra
    haveI : IsScalarTower V' (AdjoinRoot f) V2 := IsScalarTower.of_algebraMap_eq' rfl
    haveI hl2 : IsLocalHom (algebraMap V' V2) := by
      show IsLocalHom ((algebraMap (AdjoinRoot f) V2).comp (algebraMap V' (AdjoinRoot f)))
      infer_instance
    refine ⟨V2, i1, i2, i3, i4, inferInstance, Module.Finite.trans (AdjoinRoot f) V2,
      hinj.comp (inj f hf hg), hl2, e, ?_⟩
    rw [htow_eq, ← RingHom.comp_assoc, he]
    first
    | exact (ResidueField.map_comp (algebraMap V' (AdjoinRoot f)) (algebraMap (AdjoinRoot f) V2)).symm
    | exact (ResidueField.map_comp (algebraMap (AdjoinRoot f) V2) (algebraMap V' (AdjoinRoot f))).symm
end ReciprocityTheory.ChartRestriction.G.Semi.Nb
