-- Prove2me | solution 1 for V3Asm.edgePt_mem
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/db5f0e92-e073-5f23-86f4-b354b12b3ded

import Mathlib
import Definitions.Def_ModularCurve_ResolvedModelSite
import Theorems.Thm_ModularCurve_DRModelPackage_baseChangeMap_genericPoint_specializes_crossing
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_V3Asm_edgePt_mem

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace F7E85
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 1600000

section Model
open MvPolynomial.CrossingQuotient MvPolynomial.CrossingQuotient.Resolution Topology

universe u
variable {W : Type u} [CommRing W] (t : W) (e : ℕ) (𝔭 : Ideal W) [𝔭.IsMaximal] (ht : t ∈ 𝔭)

theorem algebraMap_t_mem_of_V_mem (he : 1 ≤ e) (i : Fin e) (P : chartScheme t)
    (hV : V (t ^ e) ∈ ((toCrossing t e) ((ι t e i) P)).asIdeal) :
    algebraMap W (MvPolynomial.CrossingQuotient W t) t ∈ P.asIdeal := by
  rw [toCrossing_ι_apply] at hV
  change V (t ^ e) ∈ Ideal.comap _ P.asIdeal at hV
  have hte : algebraMap W (MvPolynomial.CrossingQuotient W (t ^ e)) (t ^ e) ∈
      Ideal.comap (resolutionChart t e i).toRingHom P.asIdeal := by
    rw [← U_mul_V]; exact Ideal.mul_mem_left _ _ hV
  rw [Ideal.mem_comap, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, AlgHom.commutes, map_pow] at hte
  exact P.isPrime.mem_of_pow_mem e hte

theorem algebraMap_t_mem_of_U_mem (he : 1 ≤ e) (i : Fin e) (P : chartScheme t)
    (hU : U (t ^ e) ∈ ((toCrossing t e) ((ι t e i) P)).asIdeal) :
    algebraMap W (MvPolynomial.CrossingQuotient W t) t ∈ P.asIdeal := by
  rw [toCrossing_ι_apply] at hU
  change U (t ^ e) ∈ Ideal.comap _ P.asIdeal at hU
  have hte : algebraMap W (MvPolynomial.CrossingQuotient W (t ^ e)) (t ^ e) ∈
      Ideal.comap (resolutionChart t e i).toRingHom P.asIdeal := by
    rw [← U_mul_V]; exact Ideal.mul_mem_right _ _ hU
  rw [Ideal.mem_comap, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, AlgHom.commutes, map_pow] at hte
  exact P.isPrime.mem_of_pow_mem e hte

theorem forall_mem_of_t_mem (h𝔭 : 𝔭 = Ideal.span {t}) (P : chartScheme t)
    (htP : algebraMap W (MvPolynomial.CrossingQuotient W t) t ∈ P.asIdeal) :
    ∀ w ∈ 𝔭, algebraMap W (MvPolynomial.CrossingQuotient W t) w ∈ P.asIdeal := by
  intro w hw
  rw [h𝔭] at hw
  obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hw
  rw [map_mul]; exact Ideal.mul_mem_left _ _ htP

theorem eq_origin_zero_of_specializes (he : 1 ≤ e) (h𝔭 : 𝔭 = Ideal.span {t})
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

theorem eq_origin_last_of_specializes (he : 1 ≤ e) (h𝔭 : 𝔭 = Ideal.span {t})
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
end F7E85

namespace F7E85
section Site
open ModularCurve MvPolynomial.CrossingQuotient MvPolynomial.CrossingQuotient.Resolution Topology

variable (p : ℕ) [Fact p.Prime] (𝔛 : DRModelPackage p) (O : Type) [CommRing O] [IsDomain O]
  [IsDiscreteValuationRing O] (hϖ : IsLocalRing.maximalIdeal O = Ideal.span {((p : ℕ) : O)})
  (κ : Type) [Field κ] [CharP κ p] [IsAlgClosed κ] (toκ : O →+* κ) (H : V3Asm.SiteHyps p 𝔛 O κ toκ)

theorem ξ_specializes_x (n : V3Glue.Site.Node p 𝔛 κ) (j : Fin 2) :
    V3Asm.ξ p 𝔛 O κ toκ j ⤳ (V3Asm.C p 𝔛 O κ toκ hϖ H).x n := by
  have h := ModularCurve.DRModelPackage.baseChangeMap_genericPoint_specializes_crossing p 𝔛 O κ toκ n
  change V3Asm.ξ p 𝔛 O κ toκ j ⤳ V3Glue.Site.xpt 𝔛 (V3Asm.bc p O κ toκ) n
  revert j
  refine Fin.cases ?_ (fun i => ?_)
  · exact h.1
  · have : i = 0 := Subsingleton.elim _ _
    subst this
    exact h.2

theorem ξ_mem_U (n : V3Glue.Site.Node p 𝔛 κ) (j : Fin 2) :
    V3Asm.ξ p 𝔛 O κ toκ j ∈ (V3Asm.C p 𝔛 O κ toκ hϖ H).U n :=
  (ξ_specializes_x p 𝔛 O hϖ κ toκ H n j).mem_open ((V3Asm.C p 𝔛 O κ toκ hϖ H).U n).isOpen
    ((V3Asm.C p 𝔛 O κ toκ hϖ H).x_mem_U n)

theorem xU_mem_closure_ξ (n : V3Glue.Site.Node p 𝔛 κ) (j : Fin 2) :
    (V3Asm.C p 𝔛 O κ toκ hϖ H).xU n ∈
      closure ({⟨V3Asm.ξ p 𝔛 O κ toκ j, ξ_mem_U p 𝔛 O hϖ κ toκ H n j⟩} : Set ↥((V3Asm.C p 𝔛 O κ toκ hϖ H).U n)) := by
  rw [← specializes_iff_mem_closure]
  exact Topology.IsInducing.subtypeVal.specializes_iff.mp (ξ_specializes_x p 𝔛 O hϖ κ toκ H n j)

theorem ξ_ne_x (hξ : ∀ j, V3Asm.ξ p 𝔛 O κ toκ j ∈ (V3Asm.C p 𝔛 O κ toκ hϖ H).X0) (n : V3Glue.Site.Node p 𝔛 κ) (j : Fin 2) :
    V3Asm.ξ p 𝔛 O κ toκ j ≠ (V3Asm.C p 𝔛 O κ toκ hϖ H).x n :=
  (V3Asm.mem_X0_iff p 𝔛 O κ toκ hϖ H _).mp (hξ j) n

theorem V_mem_f (n : V3Glue.Site.Node p 𝔛 κ) (y : ↥((V3Asm.C p 𝔛 O κ toκ hϖ H).U n))
    (hy : (y : V3Glue.Site.XO p O) ∈ Set.range (𝔛.compInf κ ≫ V3Asm.bc p O κ toκ).base) :
    V (((p : ℕ) : O) ^ (V3Asm.C p 𝔛 O κ toκ hϖ H).thick n) ∈ ((((V3Asm.C p 𝔛 O κ toκ hϖ H).f n)).base y).asIdeal := by
  have key := (V3Glue.Site.chartData p 𝔛 O κ (V3Asm.bc p O κ toκ) H.hC n).orient_inf_conv
  refine key _ ?_
  convert hy using 2
  exact congrArg (fun φ => φ.base y) (Scheme.homOfLE_ι _ _)

theorem U_mem_f (n : V3Glue.Site.Node p 𝔛 κ) (y : ↥((V3Asm.C p 𝔛 O κ toκ hϖ H).U n))
    (hy : (y : V3Glue.Site.XO p O) ∈ Set.range (𝔛.compZero κ ≫ V3Asm.bc p O κ toκ).base) :
    U (((p : ℕ) : O) ^ (V3Asm.C p 𝔛 O κ toκ hϖ H).thick n) ∈ ((((V3Asm.C p 𝔛 O κ toκ hϖ H).f n)).base y).asIdeal := by
  have key := (V3Glue.Site.chartData p 𝔛 O κ (V3Asm.bc p O κ toκ) H.hC n).orient_zero_conv
  refine key _ ?_
  convert hy using 2
  exact congrArg (fun φ => φ.base y) (Scheme.homOfLE_ι _ _)

theorem not_U_mem_and_V_mem (n : V3Glue.Site.Node p 𝔛 κ) (y : ↥((V3Asm.C p 𝔛 O κ toκ hϖ H).U n))
    (hy : (y : V3Glue.Site.XO p O) ≠ (V3Asm.C p 𝔛 O κ toκ hϖ H).x n) :
    ¬ (U (((p : ℕ) : O) ^ (V3Asm.C p 𝔛 O κ toκ hϖ H).thick n) ∈ ((((V3Asm.C p 𝔛 O κ toκ hϖ H).f n)).base y).asIdeal ∧
       V (((p : ℕ) : O) ^ (V3Asm.C p 𝔛 O κ toκ hϖ H).thick n) ∈ ((((V3Asm.C p 𝔛 O κ toκ hϖ H).f n)).base y).asIdeal) := by
  have h := ((V3Asm.C p 𝔛 O κ toκ hϖ H).f_mem_Vc_iff n y).mpr hy
  have h' := TopologicalSpace.Opens.mem_sup.mp h
  rcases h' with hU | hV
  · exact fun hh => (PrimeSpectrum.mem_basicOpen _ _).mp hU hh.1
  · exact fun hh => (PrimeSpectrum.mem_basicOpen _ _).mp hV hh.2

end Site
end F7E85

open ModularCurve in
set_option maxHeartbeats 6400000 in

theorem solution (p : ℕ) [Fact p.Prime] (𝔛 : ModularCurve.DRModelPackage p)
    (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (hϖ : IsLocalRing.maximalIdeal O = Ideal.span {((p : ℕ) : O)})
    (κ : Type) [Field κ] [CharP κ p] [IsAlgClosed κ] (toκ : O →+* κ)
    (H : V3Asm.SiteHyps p 𝔛 O κ toκ) (hξ : ∀ j, V3Asm.ξ p 𝔛 O κ toκ j ∈ (V3Asm.C p 𝔛 O κ toκ hϖ H).X0) :
    ∀ (n : V3Glue.Site.Node p 𝔛 κ) (d : Fin ((V3Asm.width p 𝔛 O κ toκ hϖ H) n)),
      V3Asm.edgePt p 𝔛 O κ toκ hϖ H n d ∈ ((V3Asm.comp p 𝔛 O κ toκ hϖ H hξ (ModularCurve.DRResolvedModelPackage.chainPos (V3Asm.width p 𝔛 O κ toκ hϖ H) n d)).support : Set (V3Asm.Y p 𝔛 O κ toκ hϖ H)) ∩ ((V3Asm.comp p 𝔛 O κ toκ hϖ H hξ (ModularCurve.DRResolvedModelPackage.chainPos (V3Asm.width p 𝔛 O κ toκ hϖ H) n (d + 1))).support : Set (V3Asm.Y p 𝔛 O κ toκ hϖ H)) := by
  intro n d
  classical

  have he : 1 ≤ V3Asm.width p 𝔛 O κ toκ hϖ H n := V3Asm.one_le_width p 𝔛 O κ toκ hϖ H n
  have hU0 := F7E85.ξ_mem_U p 𝔛 O hϖ κ toκ H n 0
  have hU1 := F7E85.ξ_mem_U p 𝔛 O hϖ κ toκ H n 1

  have inr_mem : ∀ (k : Fin (V3Asm.width p 𝔛 O κ toκ hϖ H n - 1)), ((k : ℕ) = d ∨ (k : ℕ) + 1 = d) →
      V3Asm.edgePt p 𝔛 O κ toκ hϖ H n d ∈
        ((V3Asm.comp p 𝔛 O κ toκ hϖ H hξ (Sum.inr ⟨n, k⟩)).support : Set (V3Asm.Y p 𝔛 O κ toκ hϖ H)) := by
    intro k hk
    rw [V3Asm.comp_def, V3Asm.edgePt_def]
    refine (V3Asm.C p 𝔛 O κ toκ hϖ H).edgePt'_mem_support_compG_inr (V3Asm.hRF p 𝔛 O κ toκ hϖ H)
      (V3Asm.gRes p 𝔛 O κ toκ hϖ H) (V3Asm.hgRes p 𝔛 O κ toκ hϖ H) (V3Asm.ξ p 𝔛 O κ toκ) hξ
      (V3Asm.oRes p 𝔛 O κ toκ hϖ H) (V3Asm.hoRes p 𝔛 O κ toκ hϖ H) n d k ?_
    rcases hk with hk | hk
    · have : (⟨(k : ℕ), by have := k.2; dsimp only [V3Asm.width] at this ⊢; omega⟩ : Fin ((V3Asm.C p 𝔛 O κ toκ hϖ H).thick n)) = d :=
        Fin.ext hk
      unfold V3Asm.oRes V3Asm.gRes
      rw [this]
      exact MvPolynomial.CrossingQuotient.Resolution.origin_mem_closure_lineUGen _ _ _ _ d
    · unfold V3Asm.oRes V3Asm.gRes
      exact MvPolynomial.CrossingQuotient.Resolution.origin_mem_closure_lineUGen_pred _ _ _ _ d _ hk

  have inl0_mem : (d : ℕ) = 0 → V3Asm.edgePt p 𝔛 O κ toκ hϖ H n d ∈
      ((V3Asm.comp p 𝔛 O κ toκ hϖ H hξ (Sum.inl 0)).support : Set (V3Asm.Y p 𝔛 O κ toκ hϖ H)) := by
    intro hd
    rw [V3Asm.comp_def, V3Asm.edgePt_def]
    refine (V3Asm.C p 𝔛 O κ toκ hϖ H).edgePt'_mem_support_compG_inl (V3Asm.hRF p 𝔛 O κ toκ hϖ H)
      (V3Asm.gRes p 𝔛 O κ toκ hϖ H) (V3Asm.hgRes p 𝔛 O κ toκ hϖ H) (V3Asm.ξ p 𝔛 O κ toκ) hξ
      (V3Asm.oRes p 𝔛 O κ toκ hϖ H) (V3Asm.hoRes p 𝔛 O κ toκ hϖ H) n 0 d hU0
      (F7E85.xU_mem_closure_ξ p 𝔛 O hϖ κ toκ H n 0) ?_
    intro o o' ho ho' hvert
    have hV : MvPolynomial.CrossingQuotient.V (((p : ℕ) : O) ^ (V3Asm.C p 𝔛 O κ toκ hϖ H).thick n) ∈
        ((((V3Asm.C p 𝔛 O κ toκ hϖ H).f n)).base ⟨V3Asm.ξ p 𝔛 O κ toκ 0, hU0⟩).asIdeal :=
      F7E85.V_mem_f p 𝔛 O hϖ κ toκ H n _ ⟨genericPoint _, by show _ = V3Asm.ξ p 𝔛 O κ toκ 0; rw [V3Asm.ξ_zero]⟩
    have hUV := F7E85.not_U_mem_and_V_mem p 𝔛 O hϖ κ toκ H n ⟨V3Asm.ξ p 𝔛 O κ toκ 0, hU0⟩
      (F7E85.ξ_ne_x p 𝔛 O hϖ κ toκ H hξ n 0)
    have hU : MvPolynomial.CrossingQuotient.U (((p : ℕ) : O) ^ (V3Asm.C p 𝔛 O κ toκ hϖ H).thick n) ∉
        ((((V3Asm.C p 𝔛 O κ toκ hϖ H).f n)).base ⟨V3Asm.ξ p 𝔛 O κ toκ 0, hU0⟩).asIdeal := fun h => hUV ⟨h, hV⟩
    rw [V3Asm.vertex_eq] at hvert
    have := F7E85.eq_origin_zero_of_specializes ((p : ℕ) : O) ((V3Asm.C p 𝔛 O κ toκ hϖ H).thick n)
      (IsLocalRing.maximalIdeal O) (V3Asm.p_mem_maximalIdeal p O hϖ) he hϖ _ hV hU o o' ho ho' hvert
    rw [this]
    unfold V3Asm.oRes
    congr 1
    exact Fin.ext hd.symm
  have inl1_mem : (d : ℕ) + 1 = V3Asm.width p 𝔛 O κ toκ hϖ H n → V3Asm.edgePt p 𝔛 O κ toκ hϖ H n d ∈
      ((V3Asm.comp p 𝔛 O κ toκ hϖ H hξ (Sum.inl 1)).support : Set (V3Asm.Y p 𝔛 O κ toκ hϖ H)) := by
    intro hd
    rw [V3Asm.comp_def, V3Asm.edgePt_def]
    refine (V3Asm.C p 𝔛 O κ toκ hϖ H).edgePt'_mem_support_compG_inl (V3Asm.hRF p 𝔛 O κ toκ hϖ H)
      (V3Asm.gRes p 𝔛 O κ toκ hϖ H) (V3Asm.hgRes p 𝔛 O κ toκ hϖ H) (V3Asm.ξ p 𝔛 O κ toκ) hξ
      (V3Asm.oRes p 𝔛 O κ toκ hϖ H) (V3Asm.hoRes p 𝔛 O κ toκ hϖ H) n 1 d hU1
      (F7E85.xU_mem_closure_ξ p 𝔛 O hϖ κ toκ H n 1) ?_
    intro o o' ho ho' hvert
    have hU : MvPolynomial.CrossingQuotient.U (((p : ℕ) : O) ^ (V3Asm.C p 𝔛 O κ toκ hϖ H).thick n) ∈
        ((((V3Asm.C p 𝔛 O κ toκ hϖ H).f n)).base ⟨V3Asm.ξ p 𝔛 O κ toκ 1, hU1⟩).asIdeal :=
      F7E85.U_mem_f p 𝔛 O hϖ κ toκ H n _ ⟨genericPoint _, by show _ = V3Asm.ξ p 𝔛 O κ toκ 1; rw [V3Asm.ξ_one]⟩
    have hUV := F7E85.not_U_mem_and_V_mem p 𝔛 O hϖ κ toκ H n ⟨V3Asm.ξ p 𝔛 O κ toκ 1, hU1⟩
      (F7E85.ξ_ne_x p 𝔛 O hϖ κ toκ H hξ n 1)
    have hV : MvPolynomial.CrossingQuotient.V (((p : ℕ) : O) ^ (V3Asm.C p 𝔛 O κ toκ hϖ H).thick n) ∉
        ((((V3Asm.C p 𝔛 O κ toκ hϖ H).f n)).base ⟨V3Asm.ξ p 𝔛 O κ toκ 1, hU1⟩).asIdeal := fun h => hUV ⟨hU, h⟩
    rw [V3Asm.vertex_eq] at hvert
    have := F7E85.eq_origin_last_of_specializes ((p : ℕ) : O) ((V3Asm.C p 𝔛 O κ toκ hϖ H).thick n)
      (IsLocalRing.maximalIdeal O) (V3Asm.p_mem_maximalIdeal p O hϖ) he hϖ _ hU hV o o' ho ho' hvert
    rw [this]
    unfold V3Asm.oRes
    congr 1
    exact Fin.ext (by simp only; dsimp only [V3Asm.width] at hd; omega)

  constructor
  · by_cases hd : (d : ℕ) = 0
    · have hpos : DRResolvedModelPackage.chainPos (V3Asm.width p 𝔛 O κ toκ hϖ H) n d = Sum.inl 0 := by
        simp [ModularCurve.DRResolvedModelPackage.chainPos, hd]
      rw [hpos]; exact inl0_mem hd
    · have hpos : DRResolvedModelPackage.chainPos (V3Asm.width p 𝔛 O κ toκ hϖ H) n d =
          Sum.inr ⟨n, ⟨(d : ℕ) - 1, by omega⟩⟩ := by
        simp [ModularCurve.DRResolvedModelPackage.chainPos, hd, d.2]
      rw [hpos]; exact inr_mem ⟨(d : ℕ) - 1, by omega⟩ (Or.inr (by simp only; omega))
  · by_cases hd : (d : ℕ) + 1 < V3Asm.width p 𝔛 O κ toκ hϖ H n
    · have hpos : DRResolvedModelPackage.chainPos (V3Asm.width p 𝔛 O κ toκ hϖ H) n ((d : ℕ) + 1) =
          Sum.inr ⟨n, ⟨(d : ℕ), by omega⟩⟩ := by
        simp [ModularCurve.DRResolvedModelPackage.chainPos, hd]
      rw [hpos]; exact inr_mem ⟨(d : ℕ), by omega⟩ (Or.inl rfl)
    · have hd' : (d : ℕ) + 1 = V3Asm.width p 𝔛 O κ toκ hϖ H n := by omega
      have hpos : DRResolvedModelPackage.chainPos (V3Asm.width p 𝔛 O κ toκ hϖ H) n ((d : ℕ) + 1) = Sum.inl 1 := by
        simp [ModularCurve.DRResolvedModelPackage.chainPos, hd]
      rw [hpos]; exact inl1_mem hd'

end S_V3Asm_edgePt_mem
end P2MW
export P2MW.S_V3Asm_edgePt_mem (solution)
