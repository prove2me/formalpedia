-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.NPA.op_isFractionRing
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T14:54:41.428078+00:00
-- url     : https://prove2.me/submissions/730498d2-8b83-418d-a6c5-2c1d261a8139

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HtDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HNormDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_OpIsDVR
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_KTFiniteDimensional
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_ValNorm
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HNormPtsA
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_NPA_opToKT_alg
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_NPA_opToKT_injective

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0
open NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G.T0.NPA
attribute [local instance] MvPolynomial.algebraMvPolynomial
variable {K : Type} [Field K] [NumberField K] (D N : ℕ)
  (la : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
namespace ReciprocityTheory.ChartRestriction.G.T0.NPA
theorem _root_.solution :
    letI := (OpToKT D N la).toAlgebra
    IsFractionRing (Op D N la) (KTf K D N) := by
  letI := (OpToKT D N la).toAlgebra
  have hinj : Function.Injective (algebraMap (Op D N la) (KTf K D N)) := opToKT_injective D N la
  have hC : ∀ s : 𝓞 K, OTtoKT K D N (MvPolynomial.C s) = MvPolynomial.C (algebraMap (𝓞 K) K s) :=
    fun s => MvPolynomial.map_C _ _
  have hX : ∀ i, OTtoKT K D N (MvPolynomial.X i) = MvPolynomial.X i :=
    fun i => MvPolynomial.map_X _ _
  have hcl : ∀ p : KTp K D N, ∃ s : 𝓞 K, s ≠ 0 ∧ ∃ p' : OT K D N,
      OTtoKT K D N p' = MvPolynomial.C (algebraMap (𝓞 K) K s) * p := by
    intro p
    induction p using MvPolynomial.induction_on
    next a =>
      obtain ⟨x, y, hy, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 K) a
      have hy' : algebraMap (𝓞 K) K y ≠ 0 :=
        IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hy
      refine ⟨y, nonZeroDivisors.ne_zero hy, MvPolynomial.C x, ?_⟩
      rw [hC, ← MvPolynomial.C_mul]
      congr 1
      first
        | (field_simp; done)
        | (rw [mul_div_assoc', mul_div_cancel_left₀ _ hy'])
        | (field_simp; ring)
    next p q hp hq =>
      obtain ⟨s1, hs1, p1, hp1⟩ := hp
      obtain ⟨s2, hs2, q1, hq1⟩ := hq
      refine ⟨s1 * s2, mul_ne_zero hs1 hs2, MvPolynomial.C s2 * p1 + MvPolynomial.C s1 * q1, ?_⟩
      rw [map_add, map_mul, map_mul, hp1, hq1, hC, hC, map_mul (algebraMap (𝓞 K) K),
        MvPolynomial.C_mul]
      ring
    next p i hp =>
      obtain ⟨s, hs, p1, hp1⟩ := hp
      exact ⟨s, hs, p1 * MvPolynomial.X i, by rw [map_mul, hp1, hX, mul_assoc]⟩
  have hCne : ∀ s : 𝓞 K, s ≠ 0 → algebraMap (KTp K D N) (KTf K D N)
      (MvPolynomial.C (algebraMap (𝓞 K) K s)) ≠ 0 := by
    intro s hs
    rw [ne_eq, IsFractionRing.to_map_eq_zero_iff, MvPolynomial.C_eq_zero]
    exact (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 K) K)).mpr hs
  have hOp : ∀ a : OT K D N, algebraMap (Op D N la) (KTf K D N) (algebraMap (OT K D N) (Op D N la) a) =
      algebraMap (KTp K D N) (KTf K D N) (OTtoKT K D N a) := opToKT_alg D N la
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨y, hy⟩
    exact IsUnit.mk0 _ ((map_ne_zero_iff _ hinj).mpr (nonZeroDivisors.ne_zero hy))
  · intro z
    obtain ⟨p, q, hq, rfl⟩ := IsFractionRing.div_surjective (A := KTp K D N) z
    obtain ⟨sp, hsp, p', hp'⟩ := hcl p
    obtain ⟨sq, hsq, q', hq'⟩ := hcl q
    have hq0 : algebraMap (KTp K D N) (KTf K D N) q ≠ 0 :=
      IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hq
    have e1 : algebraMap (Op D N la) (KTf K D N)
        (algebraMap (OT K D N) (Op D N la) (p' * MvPolynomial.C sq)) =
        algebraMap (KTp K D N) (KTf K D N) (MvPolynomial.C (algebraMap (𝓞 K) K sp)) *
          algebraMap (KTp K D N) (KTf K D N) p *
          algebraMap (KTp K D N) (KTf K D N) (MvPolynomial.C (algebraMap (𝓞 K) K sq)) := by
      rw [hOp, map_mul, hp', hC, map_mul, map_mul]
    have e2 : algebraMap (Op D N la) (KTf K D N)
        (algebraMap (OT K D N) (Op D N la) (q' * MvPolynomial.C sp)) =
        algebraMap (KTp K D N) (KTf K D N) (MvPolynomial.C (algebraMap (𝓞 K) K sq)) *
          algebraMap (KTp K D N) (KTf K D N) q *
          algebraMap (KTp K D N) (KTf K D N) (MvPolynomial.C (algebraMap (𝓞 K) K sp)) := by
      rw [hOp, map_mul, hq', hC, map_mul, map_mul]
    have hx2 : algebraMap (OT K D N) (Op D N la) (q' * MvPolynomial.C sp) ≠ 0 :=
      (map_ne_zero_iff _ hinj).mp (by
        rw [e2]
        exact mul_ne_zero (mul_ne_zero (hCne sq hsq) hq0) (hCne sp hsp))
    refine ⟨⟨algebraMap (OT K D N) (Op D N la) (p' * MvPolynomial.C sq),
      ⟨_, mem_nonZeroDivisors_of_ne_zero hx2⟩⟩, ?_⟩
    show _ * algebraMap (Op D N la) (KTf K D N)
        (algebraMap (OT K D N) (Op D N la) (q' * MvPolynomial.C sp)) = _
    rw [e1, e2]
    have h1 := hCne sq hsq
    have h2 := hCne sp hsp
    first
      | (field_simp; done)
      | (field_simp; ring)
      | (rw [div_mul_eq_mul_div, div_eq_iff hq0]; ring)
  · intro x y hxy
    exact ⟨1, by rw [hinj hxy]⟩
end ReciprocityTheory.ChartRestriction.G.T0.NPA
