-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_PtsIntegralPoints_ptsIntegralAt_eq_c05886725c9e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:23:26.209583+00:00
-- url     : https://prove2.me/submissions/3b457bd5-7d9f-4467-ba64-a90187218fa9

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_HeightPtsIntegralPoints
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_POrbitCurve
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterBridgeB
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_PPtsIntegralPoints
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_PtsIntegralPoints_rel_equivalence_7165b98bf69b
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_PtsIntegralPoints_sheetDensity_eq_a10d7016cd98
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_mcPts_smul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_sameOrbit_of_segre
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_segre_smul


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open ReciprocityTheory.ChartRestriction.G MeasureTheory
open GroundTheory.Heights₂.Heights.PtsIntegralPoints
set_option linter.unusedSectionVars false
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
namespace GroundTheory.Heights₂.Heights.PtsIntegralPoints
theorem _root_.solution [Nonempty K] (P : Ideal (Geo.MRing ι)) (hP : Geo.IsMultiHomogIdeal P)
    (g : ((Σ k, ι k) → ℂ) → ℝ)
    (hg : ∀ (c : K → ℂ) (z : (Σ k, ι k) → ℂ), (∀ k, c k ≠ 0) → z ∈ Geo.mcPts P →
      g (fun p ↦ c p.1 * z p) = g z)
    (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (0 + 1) → ℂ)) (hΨ : Geo.IsGoodProj P Ψ) :
    Geo.ptsIntegralAt P Ψ Fin.elim0 g = ∑ᶠ q : projPts P, g (Quot.out q : Geo.mcPts P) := by
  classical
  have hE := rel_equivalence P
  have hcons : ∀ (y : Fin 0 → ℂ) (v : Fin (0 + 1) → ℂ), v = Fin.cons 1 y ↔ v 0 = 1 := by
    intro y v
    constructor
    · rintro rfl; rfl
    · intro h; funext i; rw [show i = 0 from Fin.ext (by have := i.isLt; omega)]; exact h
  have hne : ∀ z ∈ Geo.mcPts P, Ψ (Geo.segre z) 0 ≠ 0 := fun z hz h ↦
    hΨ z hz (funext fun i ↦ by rw [show i = 0 from Fin.ext (by have := i.isLt; omega)]; exact h)
  let k₀ : K := Classical.arbitrary K
  let t : projPts P → ℂ := fun q ↦ (Ψ (Geo.segre (Quot.out q : Geo.mcPts P)) 0)⁻¹
  have ht : ∀ q, t q ≠ 0 := fun q ↦ inv_ne_zero (hne _ (Quot.out q).2)
  let c : projPts P → K → ℂ := fun q k ↦ if k = k₀ then t q else 1
  have hc : ∀ q k, c q k ≠ 0 := fun q k ↦ by
    simp only [c]
    split_ifs
    · exact ht q
    · exact one_ne_zero
  have hcprod : ∀ q, ∏ k, c q k = t q := fun q ↦ by simp [c]
  let zq : projPts P → (Σ k, ι k) → ℂ := fun q p ↦ c q p.1 * (Quot.out q).1 p
  have hzq : ∀ q, zq q ∈ Geo.mcPts P := fun q ↦ Geo.mcPts_smul hP (c q) (hc q) (Quot.out q).2
  have hseg : ∀ q, Geo.segre (zq q) = t q • Geo.segre (Quot.out q : Geo.mcPts P) := fun q ↦ by
    rw [← hcprod q]
    exact Geo.segre_smul (c q) (Quot.out q).1
  have hone : ∀ q, Ψ (Geo.segre (zq q)) 0 = 1 := fun q ↦ by
    rw [hseg, map_smul, Pi.smul_apply, smul_eq_mul]
    exact inv_mul_cancel₀ (hne _ (Quot.out q).2)
  have hrep : ∀ z : Geo.mcPts P, ∃ d : K → ℂ, (∀ k, d k ≠ 0) ∧
      (z : (Σ k, ι k) → ℂ) = fun p ↦ d p.1 * (Quot.out (Quot.mk _ z : projPts P)).1 p :=
    fun z ↦ hE.eqvGen_iff.mp (Quot.eqvGen_exact (Quot.out_eq (Quot.mk _ z : projPts P)))
  have hsum : ∀ y : Fin 0 → ℂ, ∑ᶠ w ∈ Geo.fibre P Ψ y, Geo.sheetDensity P Ψ Fin.elim0 g y w =
      ∑ᶠ q : projPts P, g (Quot.out q : Geo.mcPts P) := by
    intro y
    let σ : projPts P → Geo.fibre P Ψ y := fun q ↦
      ⟨Geo.segre (zq q), zq q, hzq q, rfl, (hcons y _).mpr (hone q)⟩
    have hinj : Function.Injective σ := by
      intro q q' h
      have h' : Geo.segre (zq q) = Geo.segre (zq q') := congrArg Subtype.val h
      obtain ⟨d, hd, hdq⟩ :=
        Geo.sameOrbit_of_segre (z := zq q) (hzq q').1 1 one_ne_zero (by rw [one_smul, h'])
      have e1 : (Quot.mk _ (Quot.out q) : projPts P) = Quot.mk _ ⟨zq q, hzq q⟩ :=
        Quot.sound ⟨c q, hc q, rfl⟩
      have e2 : (Quot.mk _ ⟨zq q', hzq q'⟩ : projPts P) = Quot.mk _ ⟨zq q, hzq q⟩ :=
        Quot.sound ⟨d, hd, hdq⟩
      have e3 : (Quot.mk _ (Quot.out q') : projPts P) = Quot.mk _ ⟨zq q', hzq q'⟩ :=
        Quot.sound ⟨c q', hc q', rfl⟩
      rw [Quot.out_eq] at e1 e3
      exact e1.trans (e2.symm.trans e3.symm)
    have hsurj : Function.Surjective σ := by
      rintro ⟨w, z, hz, rfl, hw⟩
      obtain ⟨d, hd, hdz⟩ := hrep ⟨z, hz⟩
      refine ⟨Quot.mk _ ⟨z, hz⟩, Subtype.ext ?_⟩
      have hsz : Geo.segre z = (∏ k, d k) •
          Geo.segre (Quot.out (Quot.mk _ ⟨z, hz⟩ : projPts P) : Geo.mcPts P) := by
        rw [← Geo.segre_smul]
        exact congrArg Geo.segre hdz
      have h1 := (hcons y _).mp hw
      rw [hsz, map_smul, Pi.smul_apply, smul_eq_mul] at h1
      have h2 : ∏ k, d k = t (Quot.mk _ ⟨z, hz⟩) := eq_inv_of_mul_eq_one_left h1
      show Geo.segre (zq _) = Geo.segre z
      rw [hseg, hsz, h2]
    rw [← finsum_set_coe_eq_finsum_mem, ← finsum_comp_equiv (Equiv.ofBijective σ ⟨hinj, hsurj⟩)]
    refine finsum_congr fun q ↦ ?_
    show Geo.sheetDensity P Ψ Fin.elim0 g y (Geo.segre (zq q)) = _
    rw [sheetDensity_eq P Ψ g hg y (hzq q) ((hcons y _).mpr (hone q))]
    exact hg (c q) _ (hc q) (Quot.out q).2
  rw [Geo.ptsIntegralAt]
  simp only [hsum]
  rw [integral_const, MeasureTheory.volume_pi, Measure.pi_of_empty]
  simp
end GroundTheory.Heights₂.Heights.PtsIntegralPoints
