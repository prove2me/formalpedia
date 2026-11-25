-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Chart.isUnivRing_bc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T14:20:29.169223+00:00
-- url     : https://prove2.me/submissions/dae6d575-1f3b-4d19-ac32-8d1035313eeb

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_EigLatBasis
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabPull
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_AlgChart
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsUnivRingBc
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_jetMapA_zR
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_jetLift_zR
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_jet_ext
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_zR_mem_ker
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_Tri_prod


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
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Chart
attribute [local instance] Over.cartesianMonoidalCategory
variable {R : Type} [CommRing R] {B : Type} [CommRing B] [Algebra R B] (eps : B →ₐ[R] R) {n : ℕ}
variable {R' : Type} [CommRing R'] [Algebra R R']
namespace ReciprocityTheory.ChartRestriction.G.Chart
theorem _root_.solution (m : ℕ) (π : B →ₐ[R] JetR R (Fin n) m) (hπ : IsUnivRing eps m π)
    (hπa : (jetAug R (Fin n) m).comp π = eps) (A : Type) [CommRing A] [Algebra R' A] [Algebra R A]
    [IsScalarTower R R' A] (aug : A →ₐ[R'] R') (hJ : (RingHom.ker aug) ^ (m + 1) = ⊥) (h : B →ₐ[R] A)
    (hh : (aug.restrictScalars R).comp h = (Algebra.ofId R R').comp eps) :
    ∃! ψ : JetR R' (Fin n) m →ₐ[R'] A,
      aug.comp ψ = jetAug R' (Fin n) m ∧ h = (ψ.restrictScalars R).comp ((jetMapA n m).comp π) := by
  classical
  let f1 : R × A →ₐ[R] R' := (Algebra.ofId R R').comp (AlgHom.fst R R A)
  let f2 : R × A →ₐ[R] R' := (aug.restrictScalars R).comp (AlgHom.snd R R A)
  let A' : Subalgebra R (R × A) := AlgHom.equalizer f1 f2
  have memA' : ∀ p : R × A, p ∈ A' ↔ algebraMap R R' p.1 = aug p.2 := by
    intro p
    first
      | exact Iff.rfl
      | simp [A', f1, f2, AlgHom.mem_equalizer]
  let aug' : A' →ₐ[R] R := (AlgHom.fst R R A).comp A'.val
  let snd' : A' →ₐ[R] A := (AlgHom.snd R R A).comp A'.val
  have hJ' : (RingHom.ker aug') ^ (m + 1) = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    have hz1 : z ∈ RingHom.ker aug' := Ideal.pow_le_self (by omega) hz
    have hmap : Ideal.map snd' (RingHom.ker aug') ≤ RingHom.ker aug := by
      rw [Ideal.map_le_iff_le_comap]
      intro u hu
      rw [Ideal.mem_comap, RingHom.mem_ker]
      rw [RingHom.mem_ker] at hu
      have hu' := (memA' _).mp u.2
      have hu0 : (u : R × A).1 = 0 := hu
      show aug (u : R × A).2 = 0
      rw [← hu', hu0, map_zero]
    have h2 : snd' z ∈ (RingHom.ker aug) ^ (m + 1) := by
      have := Ideal.mem_map_of_mem snd' hz
      rw [Ideal.map_pow] at this
      exact Ideal.pow_right_mono hmap (m + 1) this
    rw [hJ, Ideal.mem_bot] at h2
    rw [Ideal.mem_bot]
    rw [RingHom.mem_ker] at hz1
    apply Subtype.ext
    apply Prod.ext
    · exact hz1
    · exact h2
  let h' : B →ₐ[R] A' := (eps.prod h).codRestrict A' (fun b => (memA' _).mpr (by
    have := DFunLike.congr_fun hh b
    simpa using this.symm))
  have hcomp : aug'.comp h' = eps := AlgHom.ext fun b => rfl
  obtain ⟨ψ0, ⟨hψ0a, hψ0b⟩, huniq⟩ := hπ A' aug' hJ' h' hcomp
  let ψ1 : JetR R (Fin n) m →ₐ[R] A := snd'.comp ψ0
  have hψ1z : ∀ j, ψ1 (zR m j) ∈ RingHom.ker aug := by
    intro j
    rw [RingHom.mem_ker]
    have e1 := ((memA' _).mp (ψ0 (zR m j)).2).symm
    have e2 : aug' (ψ0 (zR m j)) = 0 := by
      rw [← AlgHom.comp_apply, hψ0a]
      exact (RingHom.mem_ker).mp (zR_mem_ker m j)
    have e2' : ((ψ0 (zR m j) : A') : R × A).1 = 0 := e2
    show aug ((ψ0 (zR m j) : A') : R × A).2 = 0
    rw [e1, e2', map_zero]
  let ψ : JetR R' (Fin n) m →ₐ[R'] A :=
    jetLift R' (RingHom.ker aug) hJ (fun j => ψ1 (zR m j)) hψ1z
  have key1 : (ψ.restrictScalars R).comp (jetMapA n m) = ψ1 := by
    apply jet_ext
    intro j
    simp only [AlgHom.comp_apply, AlgHom.restrictScalars_apply, jetMapA_zR, ψ, jetLift_zR]
  refine ⟨ψ, ⟨?_, ?_⟩, ?_⟩
  · apply jet_ext
    intro j
    simp only [AlgHom.comp_apply, ψ, jetLift_zR]
    rw [(RingHom.mem_ker).mp (hψ1z j), (RingHom.mem_ker).mp (zR_mem_ker m j)]
  · rw [← AlgHom.comp_assoc, key1]
    apply AlgHom.ext
    intro b
    show h b = snd' (ψ0 (π b))
    rw [← AlgHom.comp_apply ψ0 π, ← hψ0b]
    rfl
  · rintro ψ' ⟨ha', hb'⟩
    let χ : JetR R (Fin n) m →ₐ[R] A := (ψ'.restrictScalars R).comp (jetMapA n m)
    have hχ0 : (Algebra.ofId R R').comp (jetAug R (Fin n) m) = (aug.restrictScalars R).comp χ := by
      apply jet_ext
      intro j
      have e0 : jetAug R (Fin n) m (zR m j) = 0 := (RingHom.mem_ker).mp (zR_mem_ker m j)
      have e1 : aug (ψ' (zR m j)) = 0 := by
        rw [← AlgHom.comp_apply, ha']
        exact (RingHom.mem_ker).mp (zR_mem_ker m j)
      simp only [AlgHom.comp_apply, χ, AlgHom.restrictScalars_apply, jetMapA_zR, e0, map_zero, e1]
    have hχ : ∀ u, algebraMap R R' (jetAug R (Fin n) m u) = aug (χ u) := by
      intro u
      have := DFunLike.congr_fun hχ0 u
      simpa using this
    let χ' : JetR R (Fin n) m →ₐ[R] A' :=
      ((jetAug R (Fin n) m).prod χ).codRestrict A' (fun u => (memA' _).mpr (hχ u))
    have hχ'a : aug'.comp χ' = jetAug R (Fin n) m := AlgHom.ext fun u => rfl
    have hχ'b : h' = χ'.comp π := by
      apply AlgHom.ext
      intro b
      apply Subtype.ext
      apply Prod.ext
      · show eps b = jetAug R (Fin n) m (π b)
        rw [← hπa]
        rfl
      · show h b = χ (π b)
        rw [hb']
        rfl
    have heq := huniq χ' ⟨hχ'a, hχ'b⟩
    apply jet_ext
    intro j
    have e1 : ψ' (zR m j) = χ (zR m j) := by
      simp only [χ, AlgHom.comp_apply, AlgHom.restrictScalars_apply, jetMapA_zR]
    have e2 : χ (zR m j) = ψ1 (zR m j) := by
      show ((χ' (zR m j) : A') : R × A).2 = ((ψ0 (zR m j) : A') : R × A).2
      rw [heq]
    rw [e1, e2]
    simp only [ψ, jetLift_zR]
end ReciprocityTheory.ChartRestriction.G.Chart
