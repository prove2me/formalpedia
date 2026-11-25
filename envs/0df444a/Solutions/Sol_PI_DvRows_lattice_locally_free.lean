-- Prove2me | solution 1 for PI.DvRows.lattice_locally_free
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T09:36:06.390622+00:00
-- url     : https://prove2.me/submissions/5c74be61-3ebf-40b8-b5ec-0cfdccef3f14

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_LocBasis
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProjectionRows_LatticeFinitelyGenerated
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProjectionRows_LocFree
import Theorems.Thm_PI_DvRows_den_of_locP
import Theorems.Thm_Formalism_DivisionValues_idxChange_span_top
import Theorems.Thm_Formalism_DivisionValues_semilocal_basis_exists
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
import Theorems.Thm_Formalism_HermitianLatticesTheory_locBasic_hcompl_not_mem
import Theorems.Thm_Formalism_HermitianLatticesTheory_locBasic_le_locS
import Theorems.Thm_PI_DvRows_combo_apply
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
open NumberField IsDedekindDomain
namespace PI.DvRows
theorem _root_.solution : LocFree := by
  intro K _ _ V _ _ _ _ w Y hY
  let _ : StarRing K := starRingOfComm
  obtain ⟨T, hT⟩ := hY
  obtain ⟨B, hBT, hBsp, hBli⟩ := exists_linearIndependent K (T : Set V)
  have hBfin : B.Finite := (T.finite_toSet).subset hBT
  have := hBfin.fintype
  set r := Fintype.card B with hr
  set eB := Fintype.equivFin B with heB
  set v : Fin r → V := fun i => ((eB.symm i : B) : V) with hv
  have hvli : LinearIndependent K v := hBli.comp _ eB.symm.injective
  have hvY : ∀ i, v i ∈ Y := fun i => hT ▸ Submodule.subset_span (hBT (eB.symm i).2)
  have hrv : Set.range v = B := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      exact (eB.symm i).2
    · intro hx
      exact ⟨eB ⟨x, hx⟩, by simp [hv]⟩
  have hvsp : Submodule.span K (Set.range v) = Submodule.span K (Y : Set V) := by
    rw [hrv, hBsp, ← hT, Submodule.span_span_of_tower]
  set f : (Fin r → K) →ₗ[K] V := combo v with hf
  set fO : (Fin r → K) →ₗ[𝓞 K] V := f.restrictScalars (𝓞 K) with hfO
  have hfinj : Function.Injective f := by
    intro a b hab
    have h2 : combo v (a - b) = 0 := by
      rw [map_sub]; exact sub_eq_zero.2 hab
    rw [combo_apply] at h2
    have := (Fintype.linearIndependent_iff.1 hvli) _ h2
    funext i
    exact sub_eq_zero.1 (this i)
  have hfsingle : ∀ i, f (Pi.single i 1) = v i := by
    intro i
    rw [hf, combo_apply]
    rw [Finset.sum_eq_single i (fun j _ hj => by rw [Pi.single_eq_of_ne hj, zero_smul])
      (fun h => absurd (Finset.mem_univ i) h), Pi.single_eq_same, one_smul]
  have hfmem : ∀ x, f x ∈ Submodule.span K (Set.range v) := by
    intro x
    rw [hf, combo_apply]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  have hrange : ∀ y ∈ Submodule.span K (Set.range v), ∃ x, f x = y := by
    intro y hy
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun K).1 hy
    exact ⟨c, by rw [hf, combo_apply, hc]⟩
  set Y' : Submodule (𝓞 K) (Fin r → K) := Y.comap fO with hY'
  have hmapY : Y'.map fO = Y := by
    apply le_antisymm (Submodule.map_comap_le _ _)
    intro y hy
    obtain ⟨x, hx⟩ := hrange y (by rw [hvsp]; exact Submodule.subset_span hy)
    refine ⟨x, ?_, hx⟩
    show f x ∈ Y
    rw [hx]; exact hy
  have hY'fg : Y'.FG := Submodule.fg_of_fg_map_injective fO hfinj (by rw [hmapY]; exact ⟨T, hT⟩)
  have hstd : ∀ i, (Pi.single i 1 : Fin r → K) ∈ Y' := by
    intro i
    rw [hY', Submodule.mem_comap]
    show f (Pi.single i 1) ∈ Y
    rw [hfsingle]; exact hvY i
  have hY'sp : Submodule.span K (Y' : Set (Fin r → K)) = ⊤ := by
    rw [eq_top_iff, ← (Pi.basisFun K (Fin r)).span_eq, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    rw [Pi.basisFun_apply]
    exact Submodule.subset_span (hstd i)
  have hlat : Submodule.IsLattice K Y' := ⟨hY'fg, hY'sp⟩
  obtain ⟨g, hgli, hgloc⟩ := Formalism.DivisionValues.semilocal_basis_exists K r Y' hlat w
  have hgtop : Submodule.span K (Set.range g) = ⊤ := Formalism.DivisionValues.idxChange_span_top hgli

  set b0 : Fin r → V := fun i => f (g i) with hb0
  have hb0li : LinearIndependent K b0 := hgli.map' f (LinearMap.ker_eq_bot.2 hfinj)
  have hb0sp : Submodule.span K (Set.range b0) = Submodule.span K (Y : Set V) := by
    rw [← hvsp]
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      exact hfmem (g i)
    · rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      have h1 : (Pi.single i 1 : Fin r → K) ∈ Submodule.span K (Set.range g) := by
        rw [hgtop]; exact Submodule.mem_top
      have h2 := Submodule.mem_map_of_mem (f := f) h1
      rw [Submodule.map_span, ← Set.range_comp, hfsingle] at h2
      exact h2
  have hloc1 : ∀ x ∈ Submodule.span (𝓞 K) (Set.range g),
      ∃ s : 𝓞 K, s ∉ w.asIdeal ∧ s • x ∈ Y' := by
    intro x hx
    have : x ∈ Formalism.HermitianLatticesTheory.loc (K := K) w.asIdeal Y' := by
      rw [← hgloc]
      exact Formalism.HermitianLatticesTheory.locBasic_le_locS _ _ hx
    obtain ⟨s, hs, hsx⟩ := this
    exact ⟨s, Formalism.HermitianLatticesTheory.locBasic_hcompl_not_mem (K := K) w.asIdeal s hs, hsx⟩
  have hloc2 : ∀ x ∈ Y', ∃ s : 𝓞 K, s ∉ w.asIdeal ∧
      s • x ∈ Submodule.span (𝓞 K) (Set.range g) := by
    intro x hx
    have : x ∈ Formalism.HermitianLatticesTheory.loc (K := K) w.asIdeal (Submodule.span (𝓞 K) (Set.range g)) := by
      rw [hgloc]
      exact Formalism.HermitianLatticesTheory.locBasic_le_locS _ _ hx
    obtain ⟨s, hs, hsx⟩ := this
    exact ⟨s, Formalism.HermitianLatticesTheory.locBasic_hcompl_not_mem (K := K) w.asIdeal s hs, hsx⟩

  have hb0loc : Submodule.span (𝓞 K) (Set.range b0) ≤ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal Y := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    obtain ⟨s, hs, hsx⟩ := hloc1 (g i) (Submodule.subset_span ⟨i, rfl⟩)
    refine ⟨s, hs, ?_⟩
    have : fO (s • g i) ∈ Y := hsx
    rwa [map_smul] at this
  obtain ⟨t, htw, htY⟩ := den_of_locP w (Submodule.fg_span (Set.finite_range b0)) hb0loc
  have ht0 : algebraMap (𝓞 K) K t ≠ 0 := by
    intro h0; apply htw
    have : t = 0 := by simpa using h0
    rw [this]; exact w.asIdeal.zero_mem
  have e : (fun i => t • b0 i) = fun i => (algebraMap (𝓞 K) K t) • b0 i := by
    funext i; rw [algebraMap_smul]
  refine ⟨r, fun i => t • b0 i, ?_, ?_, ?_, ?_⟩
  · rw [e, Fintype.linearIndependent_iff]
    intro gg hgg i
    have h3 : ∑ i, (gg i * algebraMap (𝓞 K) K t) • b0 i = 0 := by
      rw [← hgg]
      exact Finset.sum_congr rfl fun i _ => by rw [mul_smul]
    have := (Fintype.linearIndependent_iff.1 hb0li) _ h3 i
    exact (mul_eq_zero.1 this).resolve_right ht0
  · rw [e, ← hb0sp]
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
    · rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      have h4 : b0 i = (algebraMap (𝓞 K) K t)⁻¹ • ((algebraMap (𝓞 K) K t) • b0 i) := by
        rw [smul_smul, inv_mul_cancel₀ ht0, one_smul]
      rw [SetLike.mem_coe, h4]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  · intro i
    exact htY _ (Submodule.subset_span ⟨i, rfl⟩)
  · intro y hy
    obtain ⟨x, hxY, rfl⟩ := (by rw [hmapY]; exact hy : y ∈ Y'.map fO)
    obtain ⟨s, hs, hsx⟩ := hloc2 x hxY
    refine ⟨t * s, ?_, ?_⟩
    · intro hm
      rcases w.isPrime.mem_or_mem hm with h | h
      · exact htw h
      · exact hs h
    · have h1 : fO (s • x) ∈ (Submodule.span (𝓞 K) (Set.range g)).map fO :=
        Submodule.mem_map_of_mem hsx
      rw [Submodule.map_span, ← Set.range_comp] at h1
      rw [map_smul] at h1
      rw [mul_smul]
      have h2 : Submodule.span (𝓞 K) (Set.range (fO ∘ g)) ≤
          (Submodule.span (𝓞 K) (Set.range fun i => t • b0 i)).comap (t • LinearMap.id) := by
        rw [Submodule.span_le]
        rintro _ ⟨i, rfl⟩
        rw [SetLike.mem_coe, Submodule.mem_comap, LinearMap.smul_apply, LinearMap.id_apply]
        exact Submodule.subset_span ⟨i, rfl⟩
      exact h2 h1
end PI.DvRows
