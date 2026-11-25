-- Prove2me | solution 1 for P2M_ReciprocityTheory_AnForm_R_inter_reesCharts__6b26385361aa
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T15:12:23.041099+00:00
-- url     : https://prove2.me/submissions/d1ce4cfc-6f5a-45d2-b61b-085f7b5d5e60

import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_WChartsA
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_WChartsB
import Theorems.Thm_ReciprocityTheory_AnForm_R_reesChart_lift
import Theorems.Thm_P2M_ReciprocityTheory_AnForm_R_effCartier_comap_of_isOpenImmersion__bb69f67b52e9
import Theorems.Thm_ReciprocityTheory_AnForm_R_germ_mem_nonZeroDivisors
import Theorems.Thm_ReciprocityTheory_AnForm_R_isAffineOpen_of_iso
import Theorems.Thm_ReciprocityTheory_AnForm_R_res_mem_nonZeroDivisors
import Theorems.Thm_ReciprocityTheory_AnForm_R_sec_algebraMap_of_iso
import Theorems.Thm_ReciprocityTheory_AnForm_R_sec_mem_nonZeroDivisors


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.R
open AlgebraicGeometry CategoryTheory
noncomputable section
namespace ReciprocityTheory.AnForm.R
theorem _root_.solution {X W : Scheme.{0}} (π : W ⟶ X) (J : X.IdealSheafData) (hB : FinalTheorems.Blowup π J)
    (U : X.affineOpens) {m : ℕ} (g : Fin m → Γ(X, U.1)) (hg : Ideal.span (Set.range g) = J.ideal U)
    (V : Fin m → W.Opens) (hV : ∀ i, V i ≤ π ⁻¹ᵁ U.1)
    (e : ∀ i, (V i).toScheme ≅ Spec (CommRingCat.of (FinalTheorems.reesChart g i)))
    (he : ∀ i, (e i).hom ≫ Spec.map (CommRingCat.ofHom (algebraMap Γ(X, U.1) (FinalTheorems.reesChart g i))) ≫
      U.2.fromSpec = (V i).ι ≫ π)
    (i j : Fin m) (t : Γ(W, V i))
    (ht : t = (V i).topIso.hom ((e i).hom.appTop ((Scheme.ΓSpecIso _).inv
      ⟨IsLocalization.mk' (Localization.Away (g i)) (g j) (⟨g i, Submonoid.mem_powers _⟩ : Submonoid.powers (g i)),
        Algebra.subset_adjoin ⟨j, rfl⟩⟩))) :
    V i ⊓ V j = W.basicOpen t := by
  classical
  let σ : ∀ k, FinalTheorems.reesChart g k →+* Γ(W, V k) := fun k =>
    (V k).topIso.hom.hom.comp (((e k).hom.appTop).hom.comp
      (Scheme.ΓSpecIso (.of (FinalTheorems.reesChart g k))).inv.hom)
  let q : ∀ k l, FinalTheorems.reesChart g k := fun k l =>
    ⟨IsLocalization.mk' (Localization.Away (g k)) (g l) (⟨g k, Submonoid.mem_powers _⟩ : Submonoid.powers (g k)),
      Algebra.subset_adjoin ⟨l, rfl⟩⟩
  have hq : ∀ k l, algebraMap Γ(X, U.1) (FinalTheorems.reesChart g k) (g l) =
      q k l * algebraMap Γ(X, U.1) (FinalTheorems.reesChart g k) (g k) := fun k l =>
    Subtype.ext (IsLocalization.mk'_spec _ _ _).symm
  have hsec : ∀ k r, σ k (algebraMap _ _ r) = π.appLE _ (V k) (hV k) r := fun k r =>
    sec_algebraMap_of_iso π U (V k) (hV k) _ (e k) (he k) r
  have hP : ∀ k l, π.appLE _ (V k) (hV k) (g l) = σ k (q k l) * π.appLE _ (V k) (hV k) (g k) := by
    intro k l; rw [← hsec, ← hsec, ← map_mul, ← hq]
  have hnz : ∀ k, π.appLE _ (V k) (hV k) (g k) ∈ nonZeroDivisors Γ(W, V k) := by
    intro k
    rw [← hsec]
    apply sec_mem_nonZeroDivisors (V k) (e k)
    rw [mem_nonZeroDivisors_iff_right]
    intro x hx
    have hu : IsUnit (algebraMap Γ(X, U.1) (Localization.Away (g k)) (g k)) :=
      IsLocalization.Away.algebraMap_isUnit _
    apply Subtype.ext
    exact hu.mul_left_eq_zero.1 (congrArg Subtype.val hx)
  have hti : t = σ i (q i j) := ht
  have hVi : IsAffineOpen (V i) := isAffineOpen_of_iso (V i) (e i)
  apply le_antisymm
  · intro w hw
    have hwi : w ∈ V i := hw.1
    have hwj : w ∈ V j := hw.2
    rw [Scheme.mem_basicOpen W t w hwi, hti]
    have hg : ∀ k l (hwk : w ∈ V k), W.presheaf.germ (V k) w hwk (π.appLE _ (V k) (hV k) (g l)) =
        W.presheaf.germ (π ⁻¹ᵁ U.1) w (hV k hwk) (π.app U.1 (g l)) := by
      intro k l hwk
      simp only [Scheme.Hom.appLE, CommRingCat.comp_apply, TopCat.Presheaf.germ_res_apply]
    have h1 := congrArg (W.presheaf.germ (V i) w hwi) (hP i j)
    have h2 := congrArg (W.presheaf.germ (V j) w hwj) (hP j i)
    rw [map_mul, hg, hg] at h1
    rw [map_mul, hg, hg] at h2
    have hA := germ_mem_nonZeroDivisors hVi (hnz i) w hwi
    rw [hg] at hA
    have h3 : (W.presheaf.germ (V j) w hwj (σ j (q j i)) * W.presheaf.germ (V i) w hwi (σ i (q i j)) - 1) *
        W.presheaf.germ (π ⁻¹ᵁ U.1) w (hV i hwi) (π.app U.1 (g i)) = 0 := by
      rw [sub_mul, one_mul, mul_assoc, ← h1, ← h2, sub_self]
    have h4 := sub_eq_zero.1 ((mem_nonZeroDivisors_iff_right.1 hA) _ h3)
    exact IsUnit.of_mul_eq_one_right _ h4
  · have hD : IsAffineOpen (W.basicOpen t) := hVi.basicOpen t
    have hDle : W.basicOpen t ≤ V i := W.basicOpen_le t
    have hDU : W.basicOpen t ≤ π ⁻¹ᵁ U.1 := hDle.trans (hV i)
    let ρ := W.presheaf.map (homOfLE hDle).op
    let φ := π.appLE U.1 (W.basicOpen t) hDU
    have hφ : ∀ l, φ (g l) = ρ (π.appLE _ (V i) (hV i) (g l)) := fun l => by
      show _ = (π.appLE _ (V i) (hV i) ≫ W.presheaf.map (homOfLE hDle).op) (g l)
      rw [Scheme.Hom.appLE_map]
    have hu : IsUnit (ρ t) := W.toRingedSpace.isUnit_res_basicOpen t
    have key : ∀ (a b u x : Γ(W, W.basicOpen t)), u * x = 1 → a * b = a * u * (x * b) := by
      intro a b u x h; linear_combination (-(a * b)) * h
    have hc : ∀ l, φ.hom (g l) = (ρ (σ i (q i l)) * ↑hu.unit⁻¹) * φ.hom (g j) := by
      intro l
      show φ (g l) = _ * φ (g j)
      rw [hφ, hφ, hP i l, hP i j, ← hti, map_mul, map_mul]
      exact key _ _ _ _ hu.val_inv_mul
    have hnzj : φ.hom (g j) ∈ nonZeroDivisors Γ(W, W.basicOpen t) := by
      show φ (g j) ∈ _
      rw [hφ, hP i j, map_mul, ← hti]
      exact mul_mem hu.mem_nonZeroDivisors (res_mem_nonZeroDivisors hDle hVi (hnz i))
    obtain ⟨ψ, hψ⟩ := reesChart_lift φ.hom g j hnzj _ hc
    let a := hD.fromSpec
    let b := Spec.map (CommRingCat.ofHom ψ) ≫ (e j).inv ≫ (V j).ι
    have hab : b ≫ π = a ≫ π := by
      simp only [a, b, Category.assoc]
      rw [← he j, Iso.inv_hom_id_assoc, ← Spec.map_comp_assoc, ← CommRingCat.ofHom_comp, hψ,
        ← IsAffineOpen.SpecMap_appLE_fromSpec π U.2 hD hDU]
      rfl
    have hE : FinalTheorems.EffCartier (J.comap (a ≫ π)) := by
      rw [Scheme.IdealSheafData.comap_comp]; exact effCartier_comap_of_isOpenImmersion' _ a hB.1
    obtain ⟨h0, -, huniq⟩ := hB.2 _ (a ≫ π) hE
    have hab' : b = a := (huniq b hab).trans (huniq a rfl).symm
    intro w hw
    have hw' : w ∈ Set.range hD.fromSpec := by rw [hD.range_fromSpec]; exact hw
    obtain ⟨x, rfl⟩ := hw'
    refine ⟨hDle hw, ?_⟩
    change a x ∈ V j
    rw [← hab']
    change (V j).ι ((Spec.map (CommRingCat.ofHom ψ) ≫ (e j).inv) x) ∈ V j
    exact ((Spec.map (CommRingCat.ofHom ψ) ≫ (e j).inv) x).2
end ReciprocityTheory.AnForm.R
