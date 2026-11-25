-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.ERam.eqv_D
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T13:34:19.579035+00:00
-- url     : https://prove2.me/submissions/e0d9228e-9025-47a3-b487-585ebb279ded

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_EigRamCore
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_IdemDataBasis
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_EigRamData
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_Pf_ERam_dual_mul_expand

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open NumberField
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.PullbackSections ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.ERam
variable {E : Type} [Field E] [NumberField E]
namespace ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.ERam
theorem _root_.solution {k : Type} [Field k] (ψ : E →+* k) (δ : 𝓞 E) (hδ : ∀ i, IsIntegral ℤ ((δ : E) * omDF (E := E) i)) :
    IsEqv (ψ.comp (algebraMap (𝓞 E) E)) (bD δ hδ) (cD ψ δ) := by
  intro a
  refine ⟨fun i j => (RingOfIntegers.basis E).repr
      (a * RingOfIntegers.basis E ((Fintype.equivFin (Module.Free.ChooseBasisIndex ℤ (𝓞 E))).symm j))
      ((Fintype.equivFin (Module.Free.ChooseBasisIndex ℤ (𝓞 E))).symm i), fun i => ?_, fun j => ?_⟩
  · apply RingOfIntegers.ext
    have h1 := dual_mul_expand (E := E) a ((Fintype.equivFin (Module.Free.ChooseBasisIndex ℤ (𝓞 E))).symm i)
    rw [← Equiv.sum_comp (Fintype.equivFin (Module.Free.ChooseBasisIndex ℤ (𝓞 E))).symm] at h1
    show algebraMap (𝓞 E) E (a * bD δ hδ i) = algebraMap (𝓞 E) E (∑ j, _ • bD δ hδ j)
    rw [map_mul, map_sum]
    show (a : E) * ((δ : E) * TB.trDual (integralBasis E) ((Fintype.equivFin (Module.Free.ChooseBasisIndex ℤ (𝓞 E))).symm i)) = _
    rw [show (a : E) * ((δ : E) * TB.trDual (integralBasis E) ((Fintype.equivFin (Module.Free.ChooseBasisIndex ℤ (𝓞 E))).symm i)) =
        (δ : E) * ((a : E) * TB.trDual (integralBasis E) ((Fintype.equivFin (Module.Free.ChooseBasisIndex ℤ (𝓞 E))).symm i)) by ring, h1, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_zsmul]
    show (δ : E) * (_ • TB.trDual (integralBasis E) ((Fintype.equivFin (Module.Free.ChooseBasisIndex ℤ (𝓞 E))).symm j)) =
      _ • ((δ : E) * TB.trDual (integralBasis E) ((Fintype.equivFin (Module.Free.ChooseBasisIndex ℤ (𝓞 E))).symm j))
    simp only [zsmul_eq_mul, Rat.smul_def, Rat.cast_intCast]
    ring
  · simp only [cD, RingHom.comp_apply]
    have h2 : ((a * RingOfIntegers.basis E ((Fintype.equivFin (Module.Free.ChooseBasisIndex ℤ (𝓞 E))).symm j) :
        𝓞 E) : E) = ∑ i : Fin (nI E), (((RingOfIntegers.basis E).repr (a * RingOfIntegers.basis E
          ((Fintype.equivFin (Module.Free.ChooseBasisIndex ℤ (𝓞 E))).symm j))
          ((Fintype.equivFin (Module.Free.ChooseBasisIndex ℤ (𝓞 E))).symm i) : ℤ) : E) * (omF i : E) := by
      conv_lhs => rw [← (RingOfIntegers.basis E).sum_repr (a * RingOfIntegers.basis E
        ((Fintype.equivFin (Module.Free.ChooseBasisIndex ℤ (𝓞 E))).symm j))]
      rw [← Equiv.sum_comp (Fintype.equivFin (Module.Free.ChooseBasisIndex ℤ (𝓞 E))).symm]
      push_cast
      simp [omF, zsmul_eq_mul]
    have h3 : ψ (a : E) * ψ (omF j : E) = ∑ i : Fin (nI E), (((RingOfIntegers.basis E).repr
        (a * RingOfIntegers.basis E ((Fintype.equivFin (Module.Free.ChooseBasisIndex ℤ (𝓞 E))).symm j))
        ((Fintype.equivFin (Module.Free.ChooseBasisIndex ℤ (𝓞 E))).symm i) : ℤ) : k) * ψ (omF i : E) := by
      rw [← map_mul, show (a : E) * (omF j : E) = ((a * RingOfIntegers.basis E
        ((Fintype.equivFin (Module.Free.ChooseBasisIndex ℤ (𝓞 E))).symm j) : 𝓞 E) : E) by simp [omF], h2, map_sum]
      simp [map_mul, map_intCast]
    rw [mul_div_assoc', h3, Finset.sum_div]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
end ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.ERam
