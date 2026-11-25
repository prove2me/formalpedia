-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.EigD.snd_lin
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T14:38:33.176117+00:00
-- url     : https://prove2.me/submissions/26da3dd9-8238-4455-a856-dd201d626f24

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_SingleMemDegLE
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_SubstTanSnd
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_Pf_EigD_fst_jetTan
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_Pf_EigD_jetTan_mk
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_Pf_EigD_jetAug_mk
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_Pf_EigD_aeval_tan

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
set_option autoImplicit false
noncomputable section
namespace ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.EigD
open MvPolynomial CategoryTheory Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G
attribute [local instance] Over.cartesianMonoidalCategory
variable {V : Type} [CommRing V] {d : ℕ}
private lemma snd_tan_lemma (c x : V) : (algebraMap V (DualNumber V) c + x • DualNumber.eps).snd = x := by
  rw [TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_smul, DualNumber.snd_eps, smul_eq_mul, mul_one]
  have h0 : (algebraMap V (DualNumber V) c).snd = 0 := by
    first | rfl | simp [TrivSqZeroExt.algebraMap_eq_inl] | exact TrivSqZeroExt.snd_inl _ _
  rw [h0, zero_add]
end ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.EigD
end
end

set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.PullbackSections ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.EigD
open MvPolynomial CategoryTheory Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G
attribute [local instance] Over.cartesianMonoidalCategory
variable {V : Type} [CommRing V] {d : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.EigD
theorem _root_.solution (φ : Jet V (Fin 1 × Fin d) 1 →ₐ[V] DualNumber V) (hφ : ∀ w, (φ w).fst = jetAug w)
    (w : Jet V (Fin 1 × Fin d) 1) :
    (φ w).snd = ∑ k, (φ (zk k)).snd * (jetTan (R := V) (m := 0) ((0 : Fin 1), k) w).snd := by
  obtain ⟨q, rfl⟩ := Ideal.Quotient.mk_surjective w
  induction q using MvPolynomial.induction_on
  next a =>
    have h1 : (Ideal.Quotient.mk _ (C a) : Jet V (Fin 1 × Fin d) 1) = algebraMap V _ a := rfl
    have h2 : (φ (Ideal.Quotient.mk _ (C a))).snd = 0 := by
      rw [h1, AlgHom.commutes]
      first | rfl | simp [TrivSqZeroExt.algebraMap_eq_inl] | exact TrivSqZeroExt.snd_inl _ _
    rw [h2]
    have hne : ∀ c : Fin d, (0 : Fin 1 × Fin d →₀ ℕ) ≠ Finsupp.single ((0 : Fin 1), c) 1 :=
      fun c => (Finsupp.single_ne_zero.2 one_ne_zero).symm
    symm
    refine Finset.sum_eq_zero fun c _ => ?_
    rw [jetTan_mk, aeval_tan, snd_tan_lemma, MvPolynomial.coeff_C, if_neg (hne c), mul_zero]
  next p q hp hq =>
    simp only [map_add, TrivSqZeroExt.snd_add, hp, hq, mul_add, Finset.sum_add_distrib]
  next p n _ =>
    obtain ⟨a, b⟩ := n
    obtain rfl : a = 0 := Subsingleton.elim _ _
    have hz : ∀ c : Fin d, (φ (zk c)).fst = 0 := fun c => by
      rw [hφ, zk, jetAug_mk, MvPolynomial.constantCoeff_X]
    have hp : (φ (Ideal.Quotient.mk _ p)).fst = constantCoeff p := by rw [hφ, jetAug_mk]
    have hT : ∀ c : Fin d, (jetTan (R := V) (m := 0) ((0 : Fin 1), c)
        (Ideal.Quotient.mk _ (p * X ((0 : Fin 1), b)))).snd = if b = c then constantCoeff p else 0 := by
      intro c
      have hf : (jetTan (R := V) (m := 0) ((0 : Fin 1), c) (Ideal.Quotient.mk _ p)).fst = constantCoeff p := by
        rw [fst_jetTan, jetAug_mk]
      rw [map_mul, map_mul, TrivSqZeroExt.snd_mul, hf, jetTan_mk (ℓ := ((0 : Fin 1), c)) (X _), aeval_X]
      by_cases h : b = c
      · subst h; simp
      · have h' : ((0 : Fin 1), b) ≠ ((0 : Fin 1), c) := fun e => h (congrArg Prod.snd e)
        simp [h, h']
    have hm : (Ideal.Quotient.mk _ (p * X ((0 : Fin 1), b)) : Jet V (Fin 1 × Fin d) 1) =
        Ideal.Quotient.mk _ p * zk b := map_mul _ _ _
    rw [hm, map_mul, TrivSqZeroExt.snd_mul, hp, hz, ← hm]
    simp only [hT, mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    simp [smul_eq_mul, mul_comm]
end ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.EigD
