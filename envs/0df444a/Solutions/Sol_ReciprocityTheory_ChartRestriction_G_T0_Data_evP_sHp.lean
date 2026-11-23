-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.Data.evP_sHp
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:07:34.644525+00:00
-- url     : https://prove2.me/submissions/2f1ad8a5-09fe-4007-a922-87b8a634c928

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_KTFiniteDimensional
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_SacSuccAbove
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_ratio_self
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_sac_self
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_sac_succAbove

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0
open NumberField MvPolynomial
variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]
  {𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)}
open ReciprocityTheory.ChartRestriction.G.T0.Data
variable (d : Data K ι Ω WT A)
namespace ReciprocityTheory.ChartRestriction.G.T0.Data
theorem _root_.solution (c : ι) (sg : K →+* ℂ) (pt : TVar d.D d.N → ℂ) (hd : d.AxH 𝒜) (P : Ω c →+* ℂ)
    (hP : P ∈ PT (Ω := Ω c) sg)
    (heq : ∀ i : Fin d.D, ∑ j, pt (i.succ, j) * P (ratio (Ω := Ω c) (d.w j c) (d.w (d.jc c) c)) = 0)
    (q : MvPolynomial (TVar d.D d.N) K) : d.evP c P pt (d.sHp c q) = eval₂ sg pt q := by
  have hP' : P.comp (algebraMap K (Ω c)) = sg := hP
  have hx : ∀ k, ratio (Ω := Ω c) (d.w ((d.jc c).succAbove k) c) (d.w (d.jc c) c) = d.x c k :=
    fun k => rfl
  have key : (d.evP c P pt).comp (d.sHp c).toRingHom = eval₂Hom sg pt := by
    apply MvPolynomial.ringHom_ext
    · intro a
      rw [RingHom.comp_apply, eval₂Hom_C]
      have h1 : (d.sHp c).toRingHom (C a) = C (algebraMap K (Ω c) a) := by
        show d.sHp c (algebraMap K _ a) = _
        rw [AlgHom.commutes, MvPolynomial.algebraMap_apply]
      rw [h1, evP, eval₂Hom_C]
      exact RingHom.congr_fun hP' a
    · rintro ⟨i, j⟩
      rw [RingHom.comp_apply, eval₂Hom_X']
      show d.evP c P pt (d.sHp c (X (i, j))) = pt (i, j)
      rw [sHp, aeval_X, pImg]
      dsimp only
      rcases Fin.eq_self_or_eq_succAbove (d.jc c) j with rfl | ⟨k, rfl⟩
      · rw [sac_self]
        cases i using Fin.cases with
        | zero => simp [evP]
        | succ i' =>
          rw [if_neg (Fin.succ_ne_zero i')]
          have h1 := heq i'
          rw [Fin.sum_univ_succAbove _ (d.jc c), ratio_self (hd.w_base c), map_one, mul_one] at h1
          simp only [hx] at h1
          simp only [evP, map_neg, map_sum, map_mul, eval₂Hom_X', eval₂Hom_C, Sum.elim_inr]
          linear_combination -h1
      · rw [sac_succAbove]
        simp [evP]
  exact RingHom.congr_fun key q
end ReciprocityTheory.ChartRestriction.G.T0.Data
