-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.traceMat_injective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T05:28:10.285323+00:00
-- url     : https://prove2.me/submissions/b58466ee-29f0-4a32-bf68-a4395cc41216

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_CSandwichStA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_CSandwichStB
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_aeval_eq_sum_traceMat
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_Fib_coe_dehK
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_eq_zero_of_secTrace_mul_eq_zero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.Fib.coe_dehK



set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.GeometryOfNumbersTheory MvPolynomial MeasureTheory Module Filter Asymptotics
open scoped ComplexOrder Matrix
variable {Ω : Type} [Field Ω] [CharZero Ω] {κ : Type} [Fintype κ] {D : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
theorem _root_.solution {x : Ix κ → Ω} {e : Fin (D + 1) → Ix κ} (hfr : IsRatProjFrame x e)
    {n k r : ℕ} {b : Fin r → MvPolynomial (Ix κ) ℚ} (hb : IsSecBasis x n b)
    (H : Fin (projDeg x e) → MvPolynomial (Ix κ) ℤ) (hH : ∀ l, (H l).IsHomogeneous k)
    (hli : LinearIndependent (fnField (x ∘ e)) fun l => aeval x (H l))
    (g : Fin r → Fin (projDeg x e) → MvPolynomial (Fin (D + 1)) ℤ)
    (hgh : ∀ j l, (g j l).IsHomogeneous (n + k))
    (hgv : ∀ j l, aeval (x ∘ e) (g j l) = secTrace x e (n + k) (aeval x (b j) * aeval x (H l))) :
    Function.Injective ((traceMat D (n + k) g).map (Int.cast : ℤ → ℚ)).mulVec := by
  classical
  choose F hFh hFb using hb.1
  have hs : ∀ j, aeval x (b j) = aeval x (F j) := fun j => by
    rw [hFb j, ← algebraMap_int_eq, aeval_map_algebraMap]
  have hmemN : ∀ j l, aeval x (b j) * aeval x (H l) ∈ sec ℤ x (n + k) := fun j l => by
    rw [hs j, ← map_mul]
    exact Submodule.mem_map.mpr ⟨F j * H l, (mem_homogeneousSubmodule _ _).mpr ((hFh j).mul (hH l)), rfl⟩
  have hsn : ∀ j, aeval x (b j) ∈ sec ℤ x n := fun j => hb.2.2 ▸ Submodule.subset_span ⟨j, rfl⟩
  have key : ∀ u : Fin r → ℤ, traceMat D (n + k) g *ᵥ u = 0 → u = 0 := by
    intro u hu
    set s := ∑ j, u j • aeval x (b j) with hs_def
    have hsmem : s ∈ sec ℤ x n := Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (hsn j)
    have h0 : ∀ l, secTrace x e (n + k) (s * aeval x (H l)) = 0 := by
      intro l
      have h1 : s * aeval x (H l) =
          ((∑ j, u j • (⟨_, hmemN j l⟩ : sec ℤ x (n + k)) : sec ℤ x (n + k)) : Ω) := by
        rw [hs_def, Finset.sum_mul, Submodule.coe_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Submodule.coe_smul, smul_mul_assoc]
      rw [h1]
      show secTraceHom x e hfr (n + k) (∑ j, u j • (⟨_, hmemN j l⟩ : sec ℤ x (n + k))) = 0
      rw [map_sum]
      simp only [map_zsmul]
      have h3 : ∀ j, secTraceHom x e hfr (n + k) ⟨_, hmemN j l⟩ = aeval (x ∘ e) (g j l) :=
        fun j => (hgv j l).symm
      simp only [h3, aeval_eq_sum_traceMat g _ l (hgh _ l), Finset.smul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_eq_zero fun i _ => ?_
      have hu' := congrFun hu (finProdFinEquiv (l, i))
      simp only [Matrix.mulVec, dotProduct, Pi.zero_apply] at hu'
      calc ∑ j, u j • (((traceMat D (n + k) g (finProdFinEquiv (l, i)) j : ℤ) : Ω) *
              ∏ t, (x ∘ e) t ^ adtEnum D (n + k) i t)
          = ((∑ j, traceMat D (n + k) g (finProdFinEquiv (l, i)) j * u j : ℤ) : Ω) *
              ∏ t, (x ∘ e) t ^ adtEnum D (n + k) i t := by
            push_cast
            rw [Finset.sum_mul]
            refine Finset.sum_congr rfl fun j _ => ?_
            rw [zsmul_eq_mul]; ring
        _ = 0 := by rw [hu']; simp
    have hs0 := eq_zero_of_secTrace_mul_eq_zero x e hfr (fun l => aeval x (H l))
      (fun l => Submodule.mem_map.mpr ⟨H l, (mem_homogeneousSubmodule _ _).mpr (hH l), rfl⟩) hli n hsmem h0
    funext j
    exact Fintype.linearIndependent_iff.mp hb.2.1 u hs0 j
  intro v w hvw
  have hd : (traceMat D (n + k) g).map (Int.cast : ℤ → ℚ) *ᵥ (v - w) = 0 := by
    rw [Matrix.mulVec_sub, hvw, sub_self]
  obtain ⟨⟨c, hc⟩, hcu⟩ := IsLocalization.exist_integer_multiples_of_finite
    (nonZeroDivisors ℤ) (v - w)
  choose u hu using hcu
  have hu2 : ∀ i, ((u i : ℤ) : ℚ) = (c : ℚ) * (v - w) i := fun i => by
    have := hu i
    simp only [zsmul_eq_mul, algebraMap_int_eq, eq_intCast] at this
    exact this
  have hMu : traceMat D (n + k) g *ᵥ u = 0 := by
    funext p
    have h1 := RingHom.map_mulVec (Int.castRingHom ℚ) (traceMat D (n + k) g) u p
    have h2 : (Int.castRingHom ℚ) ∘ u = (c : ℚ) • (v - w) := by
      funext i; simp [hu2 i]
    rw [h2, Matrix.mulVec_smul] at h1
    simp only [Int.coe_castRingHom] at h1
    rw [hd, smul_zero] at h1
    simp only [Pi.zero_apply] at h1 ⊢
    exact_mod_cast h1
  have hu0 := key u hMu
  have hc0 : c ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp hc
  funext i
  have := hu2 i
  rw [hu0] at this
  simp only [Pi.zero_apply, Int.cast_zero] at this
  have h3 : (v - w) i = 0 := by
    rcases mul_eq_zero.mp this.symm with h | h
    · exact absurd (by exact_mod_cast h) hc0
    · exact h
  simpa [sub_eq_zero] using h3
end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
