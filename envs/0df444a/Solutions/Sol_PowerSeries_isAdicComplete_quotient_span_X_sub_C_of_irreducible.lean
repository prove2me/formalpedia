-- Prove2me | solution 1 for PowerSeries.isAdicComplete_quotient_span_X_sub_C_of_irreducible
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/538fbb81-d7ad-5f1d-b0e9-54edcb43dfc7

import Mathlib
import Theorems.Thm_PowerSeries_quotient_span_X_sub_C_pow_of_irreducible
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_PowerSeries_isAdicComplete_quotient_span_X_sub_C_of_irreducible
set_option autoImplicit false

namespace FltWs21
namespace Pkt

open PowerSeries IsLocalRing

theorem mem_smul_top_of_mem {R : Type*} [CommRing R] {I : Ideal R} {x : R} (hx : x ∈ I) :
    x ∈ (I • ⊤ : Submodule R R) := by
  have h := Submodule.smul_mem_smul hx (Submodule.mem_top : (1 : R) ∈ ⊤)
  simpa only [smul_eq_mul, mul_one] using h

theorem smul_top_le {R : Type*} [CommRing R] (I : Ideal R) : (I • ⊤ : Submodule R R) ≤ I :=
  Submodule.smul_le.mpr fun r hr x _ => Ideal.mul_mem_right x I hr

theorem isPrecomplete_quotient {R : Type*} [CommRing R] (I P : Ideal R) [IsPrecomplete I R] :
    IsPrecomplete I (R ⧸ P) := by
  classical
  refine ⟨fun f hf => ?_⟩

  have hstep : ∀ n, ∃ r : R, r ∈ I ^ n ∧ Ideal.Quotient.mk P r = f (n + 1) - f n := by
    intro n
    have h := hf (Nat.le_succ n)
    rw [SModEq.sub_mem, Ideal.smul_top_eq_map, Submodule.restrictScalars_mem, Ideal.Quotient.algebraMap_eq,
      Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective] at h
    obtain ⟨r, hr, hr'⟩ := h
    exact ⟨-r, neg_mem hr, by rw [map_neg, hr', neg_sub]⟩
  choose r hrI hrq using hstep
  obtain ⟨g0, hg0⟩ := Ideal.Quotient.mk_surjective (f 0)
  let g : ℕ → R := fun n => Nat.rec g0 (fun k acc => acc + r k) n
  have hg_succ : ∀ n, g (n + 1) = g n + r n := fun n => rfl
  have hgq : ∀ n, Ideal.Quotient.mk P (g n) = f n := by
    intro n
    induction n with
    | zero => exact hg0
    | succ n ih => rw [hg_succ, map_add, ih, hrq]; abel
  have hgc : ∀ {m n : ℕ}, m ≤ n → g m ≡ g n [SMOD I ^ m • (⊤ : Submodule R R)] := by
    intro m n hmn
    rw [SModEq.sub_mem]
    induction hmn with
    | refl => rw [sub_self]; exact Submodule.zero_mem _
    | @step k hle ih =>
      rw [hg_succ, show g m - (g k + r k) = (g m - g k) - r k by ring]
      exact Submodule.sub_mem _ ih (mem_smul_top_of_mem (Ideal.pow_le_pow_right hle (hrI k)))
  obtain ⟨L, hL⟩ := IsPrecomplete.prec' g (fun hmn => hgc hmn)
  refine ⟨Ideal.Quotient.mk P L, fun n => ?_⟩
  have h1 : g n - L ∈ I ^ n := smul_top_le _ ((SModEq.sub_mem).mp (hL n))
  rw [SModEq.sub_mem, ← hgq n, ← map_sub]
  have h2 := Submodule.smul_mem_smul h1 (Submodule.mem_top : (1 : R ⧸ P) ∈ ⊤)
  rwa [Algebra.smul_def, Ideal.Quotient.algebraMap_eq, mul_one] at h2

end FltWs21.Pkt

theorem solution
    {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O) (hϖ : Irreducible ϖ) :
    ∃ (_ : IsDomain (PowerSeries O ⧸ Ideal.span {(PowerSeries.X : PowerSeries O) - PowerSeries.C ϖ}))
      (_ : IsDiscreteValuationRing (PowerSeries O ⧸ Ideal.span {(PowerSeries.X : PowerSeries O) - PowerSeries.C ϖ}))
      (_ : IsAdicComplete
        (IsLocalRing.maximalIdeal (PowerSeries O ⧸ Ideal.span {(PowerSeries.X : PowerSeries O) - PowerSeries.C ϖ}))
        (PowerSeries O ⧸ Ideal.span {(PowerSeries.X : PowerSeries O) - PowerSeries.C ϖ})),
      Irreducible (Ideal.Quotient.mk (Ideal.span {(PowerSeries.X : PowerSeries O) - PowerSeries.C ϖ}) (PowerSeries.C ϖ)) := by
  classical
  set P : Ideal (PowerSeries O) := Ideal.span {(PowerSeries.X : PowerSeries O) - PowerSeries.C ϖ} with hPdef
  obtain ⟨hprime, hPIR, hloc, hirr⟩ : P.IsPrime ∧ IsPrincipalIdealRing (PowerSeries O ⧸ P) ∧
      IsLocalRing (PowerSeries O ⧸ P) ∧ Irreducible (Ideal.Quotient.mk P (PowerSeries.C ϖ)) := by
    have h := PowerSeries.quotient_span_X_sub_C_pow_of_irreducible ϖ hϖ 1 le_rfl
    rw [pow_one] at h
    exact h
  haveI : P.IsPrime := hprime
  haveI hdom : IsDomain (PowerSeries O ⧸ P) := Ideal.Quotient.isDomain P
  haveI := hPIR
  haveI := hloc
  have hne : Ideal.Quotient.mk P (PowerSeries.C ϖ) ≠ 0 := hirr.ne_zero
  have hnu : ¬ IsUnit (Ideal.Quotient.mk P (PowerSeries.C ϖ)) := hirr.not_isUnit
  haveI hdvr : IsDiscreteValuationRing (PowerSeries O ⧸ P) := by
    refine ⟨fun hbot => hne ?_⟩
    have hm : Ideal.Quotient.mk P (PowerSeries.C ϖ) ∈ IsLocalRing.maximalIdeal (PowerSeries O ⧸ P) :=
      (IsLocalRing.mem_maximalIdeal _).mpr (mem_nonunits_iff.mpr hnu)
    rw [hbot] at hm
    exact (Submodule.mem_bot _).mp hm
  have hX : Ideal.Quotient.mk P (PowerSeries.X : PowerSeries O) = Ideal.Quotient.mk P (PowerSeries.C ϖ) := by
    rw [Ideal.Quotient.eq, hPdef]
    exact Ideal.subset_span rfl
  have hmax : IsLocalRing.maximalIdeal (PowerSeries O ⧸ P)
      = (Ideal.span {(PowerSeries.X : PowerSeries O)}).map (Ideal.Quotient.mk P) := by
    rw [Ideal.map_span, Set.image_singleton, hX]
    exact hirr.maximalIdeal_eq
  have hcomplete : IsAdicComplete (IsLocalRing.maximalIdeal (PowerSeries O ⧸ P)) (PowerSeries O ⧸ P) := by
    rw [hmax]
    haveI hH : IsHausdorff ((Ideal.span {(PowerSeries.X : PowerSeries O)}).map (Ideal.Quotient.mk P)) (PowerSeries O ⧸ P) := by
      refine IsHausdorff.of_isLocalRing _ _ ?_
      rw [← hmax]
      exact (IsLocalRing.maximalIdeal.isMaximal _).ne_top
    haveI hPc : IsPrecomplete ((Ideal.span {(PowerSeries.X : PowerSeries O)}).map (Ideal.Quotient.mk P)) (PowerSeries O ⧸ P) := by
      rw [← Ideal.Quotient.algebraMap_eq, IsPrecomplete.map_algebraMap_iff]
      exact FltWs21.Pkt.isPrecomplete_quotient _ _
    exact ⟨⟩
  exact ⟨hdom, hdvr, hcomplete, hirr⟩

end S_PowerSeries_isAdicComplete_quotient_span_X_sub_C_of_irreducible
end P2MW
export P2MW.S_PowerSeries_isAdicComplete_quotient_span_X_sub_C_of_irreducible (solution)
