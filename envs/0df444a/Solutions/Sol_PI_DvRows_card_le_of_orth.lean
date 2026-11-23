-- Prove2me | solution 1 for PI.DvRows.card_le_of_orth
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:02:13.36983+00:00
-- url     : https://prove2.me/submissions/92dbd14d-685d-4ace-a3e5-98db399fe02c

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_DivisionRowsRationalLattice
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProjectionRows_ValLeOneOfMemRange
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
noncomputable section
open PI PI.DvRows
open NumberField IsDedekindDomain Formalism.BasicNotions PI.Dv
variable {K : Type} [Field K] [NumberField K] [StarRing K]
namespace PI.DvRows
theorem _root_.solution (A : HLat K) (e : Module.End K A.V) (h : A.V →ₗ⋆[K] A.V →ₗ[K] K)
    (hee : e * e = e) (hH : IsHermE A e h) (U : Submodule K A.V) (hU : U ≤ LinearMap.range e)
    {d : ℕ} (y : Fin d → A.V) (hy : LinearIndependent K y) (hye : ∀ i, y i ∈ LinearMap.range e)
    (hyU : ∀ i, ∀ u ∈ U, h (y i) u = 0) :
    d + Module.finrank K U ≤ dimE A e := by
  classical
  haveI : FiniteDimensional K A.V := Module.Finite.of_basis A.b
  have hidem : ∀ x ∈ LinearMap.range e, e x = x := by
    rintro x ⟨z, rfl⟩
    change (e * e) z = e z
    rw [hee]
  let Θ : A.V →ₗ[K] (Fin d → K) := LinearMap.pi (fun i => (h (y i)).comp e)
  have hsurj : LinearMap.range Θ = ⊤ := by
    by_contra hne
    obtain ⟨f, hf0, hle⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.2 hne)
    let a : Fin d → K := fun i => f (fun j => if i = j then 1 else 0)
    have hfa : ∀ v : Fin d → K, f v = ∑ i, a i * v i := by
      intro v
      conv_lhs => rw [pi_eq_sum_univ v]
      simp only [map_sum, map_smul, smul_eq_mul, a]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [mul_comm]
    let z : A.V := ∑ i, star (a i) • y i
    have hz : ∀ x, h z x = 0 := by
      intro x
      have hze : z ∈ LinearMap.range e :=
        Submodule.sum_mem _ (fun i _ => Submodule.smul_mem _ _ (hye i))
      have h1 : h z x = h z (e x) := by
        rw [← hH.2.2, hidem z hze]
      have h2 : f (Θ x) = 0 := hle ⟨x, rfl⟩
      rw [hfa] at h2
      rw [h1]
      simp only [z, map_sum, LinearMap.sum_apply, map_smulₛₗ, starRingEnd_apply, star_star,
        LinearMap.smul_apply, smul_eq_mul]
      simpa [Θ] using h2
    have hz0 : z = 0 := hH.2.1 z hz
    have ha : ∀ i, a i = 0 := by
      intro i
      have := (Fintype.linearIndependent_iff.1 hy) (fun i => star (a i)) hz0 i
      simpa using this
    apply hf0
    apply LinearMap.ext
    intro v
    rw [hfa]
    simp [ha]
  have hrn := LinearMap.finrank_range_add_finrank_ker Θ
  rw [hsurj, finrank_top, Module.finrank_fin_fun] at hrn
  have hrn2 := LinearMap.finrank_range_add_finrank_ker e
  have hsup : U ⊔ LinearMap.ker e ≤ LinearMap.ker Θ := by
    refine sup_le (fun u hu => ?_) (fun x hx => ?_)
    · rw [LinearMap.mem_ker]
      funext i
      simp [Θ, hidem u (hU hu), hyU i u hu]
    · rw [LinearMap.mem_ker] at hx ⊢
      funext i
      simp [Θ, hx]
  have hinf : U ⊓ LinearMap.ker e = ⊥ := by
    rw [eq_bot_iff]
    rintro u ⟨hu, hk⟩
    have hk' : e u = 0 := LinearMap.mem_ker.1 hk
    rw [Submodule.mem_bot, ← hidem u (hU hu), hk']
  have h3 := Submodule.finrank_sup_add_finrank_inf_eq U (LinearMap.ker e)
  rw [hinf, finrank_bot] at h3
  have h4 := Submodule.finrank_mono hsup
  unfold dimE
  omega
end PI.DvRows
