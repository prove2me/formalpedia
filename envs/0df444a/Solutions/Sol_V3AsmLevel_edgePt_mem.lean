-- Prove2me | solution 1 for V3AsmLevel.edgePt_mem
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/16791632-a4d1-5495-b6ab-e928f9dca034

import Mathlib
import Definitions.Def_ModularCurve_ResolvedModelSiteLevel
import Theorems.Thm_ModularCurve_DRModelPackageLevel_bcMap_genericPoint_specializes_crossingPt
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_V3AsmLevel_edgePt_mem

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 1600000

section Model
open MvPolynomial.CrossingQuotient MvPolynomial.CrossingQuotient.Resolution Topology

universe u
variable {W : Type u} [CommRing W] (t : W) (e : ℕ) (𝔭 : Ideal W) [𝔭.IsMaximal] (ht : t ∈ 𝔭)

private theorem algebraMap_t_mem_of_V_mem (he : 1 ≤ e) (i : Fin e) (P : chartScheme t)
    (hV : V (t ^ e) ∈ ((toCrossing t e) ((ι t e i) P)).asIdeal) :
    algebraMap W (MvPolynomial.CrossingQuotient W t) t ∈ P.asIdeal := by
  rw [toCrossing_ι_apply] at hV
  change V (t ^ e) ∈ Ideal.comap _ P.asIdeal at hV
  have hte : algebraMap W (MvPolynomial.CrossingQuotient W (t ^ e)) (t ^ e) ∈
      Ideal.comap (resolutionChart t e i).toRingHom P.asIdeal := by
    rw [← U_mul_V]; exact Ideal.mul_mem_left _ _ hV
  rw [Ideal.mem_comap, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, AlgHom.commutes, map_pow] at hte
  exact P.isPrime.mem_of_pow_mem e hte

private theorem algebraMap_t_mem_of_U_mem (he : 1 ≤ e) (i : Fin e) (P : chartScheme t)
    (hU : U (t ^ e) ∈ ((toCrossing t e) ((ι t e i) P)).asIdeal) :
    algebraMap W (MvPolynomial.CrossingQuotient W t) t ∈ P.asIdeal := by
  rw [toCrossing_ι_apply] at hU
  change U (t ^ e) ∈ Ideal.comap _ P.asIdeal at hU
  have hte : algebraMap W (MvPolynomial.CrossingQuotient W (t ^ e)) (t ^ e) ∈
      Ideal.comap (resolutionChart t e i).toRingHom P.asIdeal := by
    rw [← U_mul_V]; exact Ideal.mul_mem_right _ _ hU
  rw [Ideal.mem_comap, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, AlgHom.commutes, map_pow] at hte
  exact P.isPrime.mem_of_pow_mem e hte

private theorem forall_mem_of_t_mem (h𝔭 : 𝔭 = Ideal.span {t}) (P : chartScheme t)
    (htP : algebraMap W (MvPolynomial.CrossingQuotient W t) t ∈ P.asIdeal) :
    ∀ w ∈ 𝔭, algebraMap W (MvPolynomial.CrossingQuotient W t) w ∈ P.asIdeal := by
  intro w hw
  rw [h𝔭] at hw
  obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hw
  rw [map_mul]; exact Ideal.mul_mem_left _ _ htP

private theorem eq_origin_zero_of_specializes (he : 1 ≤ e) (h𝔭 : 𝔭 = Ideal.span {t})
    (b : crossingScheme (t ^ e)) (hV : V (t ^ e) ∈ b.asIdeal) (hU : U (t ^ e) ∉ b.asIdeal)
    (o o' : Resolution t e) (ho : toCrossing t e o = b) (ho' : o' ∈ closure ({o} : Set (Resolution t e)))
    (hvert : toCrossing t e o' = vertexPt t e 𝔭 ht he) :
    o' = origin t e 𝔭 ht ⟨0, he⟩ := by
  obtain ⟨i, P, rfl⟩ := exists_ι_apply_eq t e o
  subst ho
  have htP := algebraMap_t_mem_of_V_mem t e he i P hV
  have h𝔭P := forall_mem_of_t_mem t 𝔭 h𝔭 P htP

  have hi : (i : ℕ) = 0 := by
    by_contra hne
    apply hU
    rw [toCrossing_ι_apply]
    change U (t ^ e) ∈ Ideal.comap _ P.asIdeal
    rw [Ideal.mem_comap, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, resolutionChart_U]
    have h1 : algebraMap W (MvPolynomial.CrossingQuotient W t) (t ^ (i : ℕ)) ∈ P.asIdeal := by
      rw [map_pow]; exact Ideal.pow_mem_of_mem _ htP _ (Nat.pos_of_ne_zero hne)
    exact Ideal.mul_mem_right _ _ h1
  have hi' : i = ⟨0, he⟩ := Fin.ext hi
  subst hi'

  have hxP : U t ∉ P.asIdeal := by
    intro hx; apply hU
    rw [toCrossing_ι_apply]
    change U (t ^ e) ∈ Ideal.comap _ P.asIdeal
    rw [Ideal.mem_comap, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, resolutionChart_U]
    exact Ideal.mul_mem_left _ _ hx
  have hyP : V t ∈ P.asIdeal := by
    have : U t * V t ∈ P.asIdeal := by rw [U_mul_V]; exact htP
    exact (P.isPrime.mem_or_mem this).resolve_left hxP
  have hle : lineVIdeal t 𝔭 ht ≤ P.asIdeal := (lineVIdeal_le_iff t 𝔭 ht).mpr ⟨hyP, h𝔭P⟩

  have ho_mem : (ι t e ⟨0, he⟩) P ∈ closure ({lineGen t e 𝔭 ht ⟨0, he⟩} : Set (Resolution t e)) :=
    (mem_closure_lineGen_iff t e 𝔭 ht ⟨0, he⟩ _).mpr (Or.inl ⟨P, hle, rfl⟩)
  have ho'_mem : o' ∈ closure ({lineGen t e 𝔭 ht ⟨0, he⟩} : Set (Resolution t e)) :=
    (isClosed_closure.closure_subset_iff.mpr (Set.singleton_subset_iff.mpr ho_mem)) ho'
  rcases (mem_closure_lineGen_iff t e 𝔭 ht ⟨0, he⟩ o').mp ho'_mem with ⟨Q, hQ, rfl⟩ | ⟨j, Q, hj, -, -⟩
  ·
    have hxQ : U t ∈ Q.asIdeal := by
      have hv := congrArg (fun q : crossingScheme (t ^ e) => q.asIdeal) hvert
      simp only [toCrossing_ι_apply, vertexPt] at hv
      have hm : U (t ^ e) ∈ Ideal.comap (resolutionChart t e ⟨0, he⟩).toRingHom Q.asIdeal := by
        rw [hv]; exact U_mem_originIdeal _ _ _
      rw [Ideal.mem_comap, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, resolutionChart_U] at hm
      simpa using hm
    have hQU : lineUIdeal t 𝔭 ht ≤ Q.asIdeal := (lineUIdeal_le_iff t 𝔭 ht).mpr ⟨hxQ, ((lineVIdeal_le_iff t 𝔭 ht).mp hQ).2⟩
    rw [eq_originPt_of_lineU_le_of_lineV_le t 𝔭 ht hQU hQ, origin_def]
  · exfalso; simp at hj

private theorem eq_origin_last_of_specializes (he : 1 ≤ e) (h𝔭 : 𝔭 = Ideal.span {t})
    (b : crossingScheme (t ^ e)) (hU : U (t ^ e) ∈ b.asIdeal) (hV : V (t ^ e) ∉ b.asIdeal)
    (o o' : Resolution t e) (ho : toCrossing t e o = b) (ho' : o' ∈ closure ({o} : Set (Resolution t e)))
    (hvert : toCrossing t e o' = vertexPt t e 𝔭 ht he) :
    o' = origin t e 𝔭 ht ⟨e - 1, by omega⟩ := by
  obtain ⟨i, P, rfl⟩ := exists_ι_apply_eq t e o
  subst ho
  have htP := algebraMap_t_mem_of_U_mem t e he i P hU
  have h𝔭P := forall_mem_of_t_mem t 𝔭 h𝔭 P htP

  have hi : (i : ℕ) = e - 1 := by
    by_contra hne
    apply hV
    rw [toCrossing_ι_apply]
    change V (t ^ e) ∈ Ideal.comap _ P.asIdeal
    rw [Ideal.mem_comap, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, resolutionChart_V]
    have h1 : algebraMap W (MvPolynomial.CrossingQuotient W t) (t ^ (e - 1 - (i : ℕ))) ∈ P.asIdeal := by
      rw [map_pow]; exact Ideal.pow_mem_of_mem _ htP _ (Nat.pos_of_ne_zero (by have := i.2; omega))
    exact Ideal.mul_mem_right _ _ h1
  have h0 : e - 1 - (i : ℕ) = 0 := by omega
  have hyP : V t ∉ P.asIdeal := by
    intro hy; apply hV
    rw [toCrossing_ι_apply]
    change V (t ^ e) ∈ Ideal.comap _ P.asIdeal
    rw [Ideal.mem_comap, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, resolutionChart_V, h0, pow_zero, map_one, one_mul]
    exact hy
  have hxP : U t ∈ P.asIdeal := by
    have : U t * V t ∈ P.asIdeal := by rw [U_mul_V]; exact htP
    exact (P.isPrime.mem_or_mem this).resolve_right hyP
  have hle : lineUIdeal t 𝔭 ht ≤ P.asIdeal := (lineUIdeal_le_iff t 𝔭 ht).mpr ⟨hxP, h𝔭P⟩
  have hlast : (i : ℕ) + 1 = e := by omega
  have ho_mem : (ι t e i) P ∈ closure ({lineUGen t e 𝔭 ht i} : Set (Resolution t e)) :=
    (mem_closure_lineUGen_last_iff t e 𝔭 ht _ hlast _).mpr ⟨P, hle, rfl⟩
  have ho'_mem : o' ∈ closure ({lineUGen t e 𝔭 ht i} : Set (Resolution t e)) :=
    (isClosed_closure.closure_subset_iff.mpr (Set.singleton_subset_iff.mpr ho_mem)) ho'
  obtain ⟨Q, hQ, rfl⟩ := (mem_closure_lineUGen_last_iff t e 𝔭 ht _ hlast o').mp ho'_mem
  have hyQ : V t ∈ Q.asIdeal := by
    have hv := congrArg (fun q : crossingScheme (t ^ e) => q.asIdeal) hvert
    simp only [toCrossing_ι_apply, vertexPt] at hv
    have hm : V (t ^ e) ∈ Ideal.comap (resolutionChart t e i).toRingHom Q.asIdeal := by
      rw [hv]; exact V_mem_originIdeal _ _ _
    rw [Ideal.mem_comap, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, resolutionChart_V, h0, pow_zero, map_one,
      one_mul] at hm
    exact hm
  have hQV : lineVIdeal t 𝔭 ht ≤ Q.asIdeal := (lineVIdeal_le_iff t 𝔭 ht).mpr ⟨hyQ, ((lineUIdeal_le_iff t 𝔭 ht).mp hQ).2⟩
  rw [eq_originPt_of_lineU_le_of_lineV_le t 𝔭 ht hQ hQV, ← origin_def]
  congr 1
  exact Fin.ext hi

end Model

section Site
open ModularCurve MvPolynomial.CrossingQuotient MvPolynomial.CrossingQuotient.Resolution Topology

variable {N₀ q : ℕ} [NeZero N₀] [Fact q.Prime] {hqN : ¬ q ∣ N₀} (𝔛 : DRModelPackageLevel N₀ q hqN) (O : Type) [CommRing O] [IsDomain O]
  [IsDiscreteValuationRing O] (ρO : DRLevel.R q →+* O) (hϖ : IsLocalRing.maximalIdeal O = Ideal.span {((q : ℕ) : O)})
  (κ : Type) [Field κ] [CharP κ q] [IsAlgClosed κ] [DecidableEq κ] (toκ : O →+* κ) (H : V3AsmLevel.SiteHyps 𝔛 O ρO κ toκ)

private theorem ξ_specializes_x (n : V3Glue.LevelSite.Node 𝔛 κ (toκ.comp ρO)) (j : Fin 2) :
    V3AsmLevel.ξ 𝔛 O ρO κ toκ j ⤳ (V3AsmLevel.C 𝔛 O ρO κ toκ hϖ H).x n := by
  have h := ModularCurve.DRModelPackageLevel.bcMap_genericPoint_specializes_crossingPt N₀ q hqN 𝔛 O ρO κ toκ n
  change V3AsmLevel.ξ 𝔛 O ρO κ toκ j ⤳ V3Glue.LevelSite.xpt 𝔛 (V3AsmLevel.bc O ρO κ toκ) n
  revert j
  refine Fin.cases ?_ (fun i => ?_)
  · exact h.1
  · have : i = 0 := Subsingleton.elim _ _
    subst this
    exact h.2

private theorem ξ_mem_U (n : V3Glue.LevelSite.Node 𝔛 κ (toκ.comp ρO)) (j : Fin 2) :
    V3AsmLevel.ξ 𝔛 O ρO κ toκ j ∈ (V3AsmLevel.C 𝔛 O ρO κ toκ hϖ H).U n :=
  (ξ_specializes_x 𝔛 O ρO hϖ κ toκ H n j).mem_open ((V3AsmLevel.C 𝔛 O ρO κ toκ hϖ H).U n).isOpen
    ((V3AsmLevel.C 𝔛 O ρO κ toκ hϖ H).x_mem_U n)

private theorem xU_mem_closure_ξ (n : V3Glue.LevelSite.Node 𝔛 κ (toκ.comp ρO)) (j : Fin 2) :
    (V3AsmLevel.C 𝔛 O ρO κ toκ hϖ H).xU n ∈
      closure ({⟨V3AsmLevel.ξ 𝔛 O ρO κ toκ j, ξ_mem_U 𝔛 O ρO hϖ κ toκ H n j⟩} : Set ↥((V3AsmLevel.C 𝔛 O ρO κ toκ hϖ H).U n)) := by
  rw [← specializes_iff_mem_closure]
  exact Topology.IsInducing.subtypeVal.specializes_iff.mp (ξ_specializes_x 𝔛 O ρO hϖ κ toκ H n j)

private theorem ξ_ne_x (hξ : ∀ j, V3AsmLevel.ξ 𝔛 O ρO κ toκ j ∈ (V3AsmLevel.C 𝔛 O ρO κ toκ hϖ H).X0) (n : V3Glue.LevelSite.Node 𝔛 κ (toκ.comp ρO)) (j : Fin 2) :
    V3AsmLevel.ξ 𝔛 O ρO κ toκ j ≠ (V3AsmLevel.C 𝔛 O ρO κ toκ hϖ H).x n :=
  (V3AsmLevel.mem_X0_iff 𝔛 O ρO κ toκ hϖ H _).mp (hξ j) n

private theorem V_mem_f (n : V3Glue.LevelSite.Node 𝔛 κ (toκ.comp ρO)) (y : ↥((V3AsmLevel.C 𝔛 O ρO κ toκ hϖ H).U n))
    (hy : (y : ModularCurve.DRLevel.XO (N₀ := N₀) ρO) ∈ Set.range (𝔛.comp κ (toκ.comp ρO) 0 ≫ V3AsmLevel.bc O ρO κ toκ).base) :
    V (((q : ℕ) : O) ^ (V3AsmLevel.C 𝔛 O ρO κ toκ hϖ H).thick n) ∈ ((((V3AsmLevel.C 𝔛 O ρO κ toκ hϖ H).f n)).base y).asIdeal := by
  have key := (V3Glue.LevelSite.chartData 𝔛 O ρO κ (toκ.comp ρO) (V3AsmLevel.bc O ρO κ toκ) H.hC n).orient_inf_conv
  refine key _ ?_
  convert hy using 2
  exact congrArg (fun φ => φ.base y) (Scheme.homOfLE_ι _ _)

private theorem U_mem_f (n : V3Glue.LevelSite.Node 𝔛 κ (toκ.comp ρO)) (y : ↥((V3AsmLevel.C 𝔛 O ρO κ toκ hϖ H).U n))
    (hy : (y : ModularCurve.DRLevel.XO (N₀ := N₀) ρO) ∈ Set.range (𝔛.comp κ (toκ.comp ρO) 1 ≫ V3AsmLevel.bc O ρO κ toκ).base) :
    U (((q : ℕ) : O) ^ (V3AsmLevel.C 𝔛 O ρO κ toκ hϖ H).thick n) ∈ ((((V3AsmLevel.C 𝔛 O ρO κ toκ hϖ H).f n)).base y).asIdeal := by
  have key := (V3Glue.LevelSite.chartData 𝔛 O ρO κ (toκ.comp ρO) (V3AsmLevel.bc O ρO κ toκ) H.hC n).orient_zero_conv
  refine key _ ?_
  convert hy using 2
  exact congrArg (fun φ => φ.base y) (Scheme.homOfLE_ι _ _)

private theorem not_U_mem_and_V_mem (n : V3Glue.LevelSite.Node 𝔛 κ (toκ.comp ρO)) (y : ↥((V3AsmLevel.C 𝔛 O ρO κ toκ hϖ H).U n))
    (hy : (y : ModularCurve.DRLevel.XO (N₀ := N₀) ρO) ≠ (V3AsmLevel.C 𝔛 O ρO κ toκ hϖ H).x n) :
    ¬ (U (((q : ℕ) : O) ^ (V3AsmLevel.C 𝔛 O ρO κ toκ hϖ H).thick n) ∈ ((((V3AsmLevel.C 𝔛 O ρO κ toκ hϖ H).f n)).base y).asIdeal ∧
       V (((q : ℕ) : O) ^ (V3AsmLevel.C 𝔛 O ρO κ toκ hϖ H).thick n) ∈ ((((V3AsmLevel.C 𝔛 O ρO κ toκ hϖ H).f n)).base y).asIdeal) := by
  have h := ((V3AsmLevel.C 𝔛 O ρO κ toκ hϖ H).f_mem_Vc_iff n y).mpr hy
  have h' := TopologicalSpace.Opens.mem_sup.mp h
  rcases h' with hU | hV
  · exact fun hh => (PrimeSpectrum.mem_basicOpen _ _).mp hU hh.1
  · exact fun hh => (PrimeSpectrum.mem_basicOpen _ _).mp hV hh.2

end Site

open ModularCurve in
set_option maxHeartbeats 6400000 in

theorem solution (N₀ q : ℕ) [NeZero N₀] [Fact q.Prime] (hqN : ¬ q ∣ N₀) (𝔛 : ModularCurve.DRModelPackageLevel N₀ q hqN)
    (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ρO : ModularCurve.DRLevel.R q →+* O)
    (hϖ : IsLocalRing.maximalIdeal O = Ideal.span {((q : ℕ) : O)})
    (κ : Type) [Field κ] [CharP κ q] [IsAlgClosed κ] [DecidableEq κ] (toκ : O →+* κ)
    (H : V3AsmLevel.SiteHyps 𝔛 O ρO κ toκ) (hξ : ∀ j, V3AsmLevel.ξ 𝔛 O ρO κ toκ j ∈ (V3AsmLevel.C 𝔛 O ρO κ toκ hϖ H).X0) :
    ∀ (n : V3Glue.LevelSite.Node 𝔛 κ (toκ.comp ρO)) (d : Fin ((V3AsmLevel.width 𝔛 O ρO κ toκ hϖ H) n)),
      V3AsmLevel.edgePt 𝔛 O ρO κ toκ hϖ H n d ∈ ((V3AsmLevel.comp 𝔛 O ρO κ toκ hϖ H hξ (ModularCurve.DRResolvedModelPackageLevel.chainPos (V3AsmLevel.width 𝔛 O ρO κ toκ hϖ H) n d)).support : Set (V3AsmLevel.Y 𝔛 O ρO κ toκ hϖ H)) ∩ ((V3AsmLevel.comp 𝔛 O ρO κ toκ hϖ H hξ (ModularCurve.DRResolvedModelPackageLevel.chainPos (V3AsmLevel.width 𝔛 O ρO κ toκ hϖ H) n (d + 1))).support : Set (V3AsmLevel.Y 𝔛 O ρO κ toκ hϖ H)) := by
  intro n d
  classical
  haveI := 𝔛.isIntegral_fibre0 (toκ.comp ρO)

  have he : 1 ≤ V3AsmLevel.width 𝔛 O ρO κ toκ hϖ H n := V3AsmLevel.one_le_width 𝔛 O ρO κ toκ hϖ H n
  have hU0 := ξ_mem_U 𝔛 O ρO hϖ κ toκ H n 0
  have hU1 := ξ_mem_U 𝔛 O ρO hϖ κ toκ H n 1

  have inr_mem : ∀ (k : Fin (V3AsmLevel.width 𝔛 O ρO κ toκ hϖ H n - 1)), ((k : ℕ) = d ∨ (k : ℕ) + 1 = d) →
      V3AsmLevel.edgePt 𝔛 O ρO κ toκ hϖ H n d ∈
        ((V3AsmLevel.comp 𝔛 O ρO κ toκ hϖ H hξ (Sum.inr ⟨n, k⟩)).support : Set (V3AsmLevel.Y 𝔛 O ρO κ toκ hϖ H)) := by
    intro k hk
    rw [V3AsmLevel.comp_def, V3AsmLevel.edgePt_def]
    refine (V3AsmLevel.C 𝔛 O ρO κ toκ hϖ H).edgePt'_mem_support_compG_inr (V3AsmLevel.hRF 𝔛 O ρO κ toκ hϖ H)
      (V3AsmLevel.gRes 𝔛 O ρO κ toκ hϖ H) (V3AsmLevel.hgRes 𝔛 O ρO κ toκ hϖ H) (V3AsmLevel.ξ 𝔛 O ρO κ toκ) hξ
      (V3AsmLevel.oRes 𝔛 O ρO κ toκ hϖ H) (V3AsmLevel.hoRes 𝔛 O ρO κ toκ hϖ H) n d k ?_
    rcases hk with hk | hk
    · have : (⟨(k : ℕ), by have := k.2; dsimp only [V3AsmLevel.width] at this ⊢; omega⟩ : Fin ((V3AsmLevel.C 𝔛 O ρO κ toκ hϖ H).thick n)) = d :=
        Fin.ext hk
      unfold V3AsmLevel.oRes V3AsmLevel.gRes
      rw [this]
      exact MvPolynomial.CrossingQuotient.Resolution.origin_mem_closure_lineUGen _ _ _ _ d
    · unfold V3AsmLevel.oRes V3AsmLevel.gRes
      exact MvPolynomial.CrossingQuotient.Resolution.origin_mem_closure_lineUGen_pred _ _ _ _ d _ hk

  have inl0_mem : (d : ℕ) = 0 → V3AsmLevel.edgePt 𝔛 O ρO κ toκ hϖ H n d ∈
      ((V3AsmLevel.comp 𝔛 O ρO κ toκ hϖ H hξ (Sum.inl 0)).support : Set (V3AsmLevel.Y 𝔛 O ρO κ toκ hϖ H)) := by
    intro hd
    rw [V3AsmLevel.comp_def, V3AsmLevel.edgePt_def]
    refine (V3AsmLevel.C 𝔛 O ρO κ toκ hϖ H).edgePt'_mem_support_compG_inl (V3AsmLevel.hRF 𝔛 O ρO κ toκ hϖ H)
      (V3AsmLevel.gRes 𝔛 O ρO κ toκ hϖ H) (V3AsmLevel.hgRes 𝔛 O ρO κ toκ hϖ H) (V3AsmLevel.ξ 𝔛 O ρO κ toκ) hξ
      (V3AsmLevel.oRes 𝔛 O ρO κ toκ hϖ H) (V3AsmLevel.hoRes 𝔛 O ρO κ toκ hϖ H) n 0 d hU0
      (xU_mem_closure_ξ 𝔛 O ρO hϖ κ toκ H n 0) ?_
    intro o o' ho ho' hvert
    have hV : MvPolynomial.CrossingQuotient.V (((q : ℕ) : O) ^ (V3AsmLevel.C 𝔛 O ρO κ toκ hϖ H).thick n) ∈
        ((((V3AsmLevel.C 𝔛 O ρO κ toκ hϖ H).f n)).base ⟨V3AsmLevel.ξ 𝔛 O ρO κ toκ 0, hU0⟩).asIdeal :=
      V_mem_f 𝔛 O ρO hϖ κ toκ H n _ ⟨genericPoint _, by show _ = V3AsmLevel.ξ 𝔛 O ρO κ toκ 0; rw [V3AsmLevel.ξ_zero]⟩
    have hUV := not_U_mem_and_V_mem 𝔛 O ρO hϖ κ toκ H n ⟨V3AsmLevel.ξ 𝔛 O ρO κ toκ 0, hU0⟩
      (ξ_ne_x 𝔛 O ρO hϖ κ toκ H hξ n 0)
    have hU : MvPolynomial.CrossingQuotient.U (((q : ℕ) : O) ^ (V3AsmLevel.C 𝔛 O ρO κ toκ hϖ H).thick n) ∉
        ((((V3AsmLevel.C 𝔛 O ρO κ toκ hϖ H).f n)).base ⟨V3AsmLevel.ξ 𝔛 O ρO κ toκ 0, hU0⟩).asIdeal := fun h => hUV ⟨h, hV⟩
    rw [V3AsmLevel.vertex_eq] at hvert
    have := eq_origin_zero_of_specializes ((q : ℕ) : O) ((V3AsmLevel.C 𝔛 O ρO κ toκ hϖ H).thick n)
      (IsLocalRing.maximalIdeal O) (V3AsmLevel.p_mem_maximalIdeal O hϖ) he hϖ _ hV hU o o' ho ho' hvert
    rw [this]
    unfold V3AsmLevel.oRes
    congr 1
    exact Fin.ext hd.symm
  have inl1_mem : (d : ℕ) + 1 = V3AsmLevel.width 𝔛 O ρO κ toκ hϖ H n → V3AsmLevel.edgePt 𝔛 O ρO κ toκ hϖ H n d ∈
      ((V3AsmLevel.comp 𝔛 O ρO κ toκ hϖ H hξ (Sum.inl 1)).support : Set (V3AsmLevel.Y 𝔛 O ρO κ toκ hϖ H)) := by
    intro hd
    rw [V3AsmLevel.comp_def, V3AsmLevel.edgePt_def]
    refine (V3AsmLevel.C 𝔛 O ρO κ toκ hϖ H).edgePt'_mem_support_compG_inl (V3AsmLevel.hRF 𝔛 O ρO κ toκ hϖ H)
      (V3AsmLevel.gRes 𝔛 O ρO κ toκ hϖ H) (V3AsmLevel.hgRes 𝔛 O ρO κ toκ hϖ H) (V3AsmLevel.ξ 𝔛 O ρO κ toκ) hξ
      (V3AsmLevel.oRes 𝔛 O ρO κ toκ hϖ H) (V3AsmLevel.hoRes 𝔛 O ρO κ toκ hϖ H) n 1 d hU1
      (xU_mem_closure_ξ 𝔛 O ρO hϖ κ toκ H n 1) ?_
    intro o o' ho ho' hvert
    have hU : MvPolynomial.CrossingQuotient.U (((q : ℕ) : O) ^ (V3AsmLevel.C 𝔛 O ρO κ toκ hϖ H).thick n) ∈
        ((((V3AsmLevel.C 𝔛 O ρO κ toκ hϖ H).f n)).base ⟨V3AsmLevel.ξ 𝔛 O ρO κ toκ 1, hU1⟩).asIdeal :=
      U_mem_f 𝔛 O ρO hϖ κ toκ H n _ ⟨genericPoint _, by show _ = V3AsmLevel.ξ 𝔛 O ρO κ toκ 1; rw [V3AsmLevel.ξ_one]⟩
    have hUV := not_U_mem_and_V_mem 𝔛 O ρO hϖ κ toκ H n ⟨V3AsmLevel.ξ 𝔛 O ρO κ toκ 1, hU1⟩
      (ξ_ne_x 𝔛 O ρO hϖ κ toκ H hξ n 1)
    have hV : MvPolynomial.CrossingQuotient.V (((q : ℕ) : O) ^ (V3AsmLevel.C 𝔛 O ρO κ toκ hϖ H).thick n) ∉
        ((((V3AsmLevel.C 𝔛 O ρO κ toκ hϖ H).f n)).base ⟨V3AsmLevel.ξ 𝔛 O ρO κ toκ 1, hU1⟩).asIdeal := fun h => hUV ⟨hU, h⟩
    rw [V3AsmLevel.vertex_eq] at hvert
    have := eq_origin_last_of_specializes ((q : ℕ) : O) ((V3AsmLevel.C 𝔛 O ρO κ toκ hϖ H).thick n)
      (IsLocalRing.maximalIdeal O) (V3AsmLevel.p_mem_maximalIdeal O hϖ) he hϖ _ hU hV o o' ho ho' hvert
    rw [this]
    unfold V3AsmLevel.oRes
    congr 1
    exact Fin.ext (by simp only; dsimp only [V3AsmLevel.width] at hd; omega)

  constructor
  · by_cases hd : (d : ℕ) = 0
    · have hpos : DRResolvedModelPackageLevel.chainPos (V3AsmLevel.width 𝔛 O ρO κ toκ hϖ H) n d = Sum.inl 0 := by
        simp [ModularCurve.DRResolvedModelPackageLevel.chainPos, hd]
      rw [hpos]; exact inl0_mem hd
    · have hpos : DRResolvedModelPackageLevel.chainPos (V3AsmLevel.width 𝔛 O ρO κ toκ hϖ H) n d =
          Sum.inr ⟨n, ⟨(d : ℕ) - 1, by omega⟩⟩ := by
        simp [ModularCurve.DRResolvedModelPackageLevel.chainPos, hd, d.2]
      rw [hpos]; exact inr_mem ⟨(d : ℕ) - 1, by omega⟩ (Or.inr (by simp only; omega))
  · by_cases hd : (d : ℕ) + 1 < V3AsmLevel.width 𝔛 O ρO κ toκ hϖ H n
    · have hpos : DRResolvedModelPackageLevel.chainPos (V3AsmLevel.width 𝔛 O ρO κ toκ hϖ H) n ((d : ℕ) + 1) =
          Sum.inr ⟨n, ⟨(d : ℕ), by omega⟩⟩ := by
        simp [ModularCurve.DRResolvedModelPackageLevel.chainPos, hd]
      rw [hpos]; exact inr_mem ⟨(d : ℕ), by omega⟩ (Or.inl rfl)
    · have hd' : (d : ℕ) + 1 = V3AsmLevel.width 𝔛 O ρO κ toκ hϖ H n := by omega
      have hpos : DRResolvedModelPackageLevel.chainPos (V3AsmLevel.width 𝔛 O ρO κ toκ hϖ H) n ((d : ℕ) + 1) = Sum.inl 1 := by
        simp [ModularCurve.DRResolvedModelPackageLevel.chainPos, hd]
      rw [hpos]; exact inl1_mem hd'

end S_V3AsmLevel_edgePt_mem
end P2MW
export P2MW.S_V3AsmLevel_edgePt_mem (solution)
