-- Prove2me | solution 1 for Polynomial.abv_coeff_mul_pow_le_of_evalEval_C_add_X_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/3bd23907-b7e1-5004-8c1b-b0e4a5de03a8

import Mathlib
import Theorems.Thm_Ideal_existsUnique_sub_mem_and_eval_eq_zero_of_isUnit_derivative
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Polynomial_abv_coeff_mul_pow_le_of_evalEval_C_add_X_eq_zero

set_option autoImplicit false

open Polynomial

namespace P2MG3b

theorem hensel_rychlik {W : Type*} [CommRing W] (I : Ideal W) [IsAdicComplete I W]
    (G : Polynomial W) (y₀ e a : W) (he : (Polynomial.derivative G).eval y₀ = e)
    (ha : G.eval y₀ = e ^ 2 * a) (haI : a ∈ I) :
    ∃ t : W, t ∈ I ∧ G.eval (y₀ + e * t) = 0 := by

  obtain ⟨k, hk⟩ := Polynomial.binomExpansion (G.map (C : W →+* Polynomial W)) (C y₀) (C e * X)
  have hev : ∀ q : Polynomial W, (G.map (C : W →+* Polynomial W)).eval q = G.comp q := fun q => by
    rw [Polynomial.eval_map, Polynomial.comp]
  have hder : Polynomial.derivative (G.map (C : W →+* Polynomial W)) = (Polynomial.derivative G).map C :=
    Polynomial.derivative_map G C
  rw [hev, hev, hder, Polynomial.eval_map, ← Polynomial.comp, Polynomial.comp_C, Polynomial.comp_C, ha, he] at hk

  set H : Polynomial W := C a + X + k * C (e * e) * X ^ 2 with hH
  have hfac : G.comp (C y₀ + C e * X) = C (e ^ 2) * (C a + X + k * X ^ 2) := by
    rw [hk]; simp only [map_mul, map_pow]; ring
  set H' : Polynomial W := C a + X + k * X ^ 2 with hH'
  have hH0 : H'.eval 0 = a := by simp [hH']
  have hH1 : (Polynomial.derivative H').eval 0 = 1 := by
    simp [hH', Polynomial.derivative_mul]
  obtain ⟨t, ⟨ht1, ht2⟩, -⟩ :=
    Ideal.existsUnique_sub_mem_and_eval_eq_zero_of_isUnit_derivative I H' 0 (by rw [hH0]; exact haI)
      (by rw [hH1]; exact isUnit_one)
  refine ⟨t, by simpa using ht1, ?_⟩
  have := congrArg (fun p : Polynomial W => p.eval t) hfac
  simp only [Polynomial.eval_comp, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X] at this
  rw [this, ht2, mul_zero]

variable {K : Type*} [Field K]

def intRing (μ : AbsoluteValue K ℝ) (hμ : IsNonarchimedean μ) : Subring K where
  carrier := {x | μ x ≤ 1}
  mul_mem' {a b} ha hb := by
    show μ (a * b) ≤ 1
    rw [map_mul]; exact mul_le_one₀ ha (μ.nonneg _) hb
  one_mem' := by show μ 1 ≤ 1; rw [map_one]
  add_mem' {a b} ha hb := by
    show μ (a + b) ≤ 1
    exact (hμ a b).trans (max_le ha hb)
  zero_mem' := by show μ 0 ≤ 1; rw [map_zero]; exact zero_le_one
  neg_mem' {a} ha := by show μ (-a) ≤ 1; rwa [map_neg_eq_map]

theorem mem_intRing {μ : AbsoluteValue K ℝ} {hμ : IsNonarchimedean μ} {x : K} : x ∈ intRing μ hμ ↔ μ x ≤ 1 := Iff.rfl

theorem exists_lift (μ : AbsoluteValue K ℝ) (hμ : IsNonarchimedean μ)
    (G : Polynomial (Polynomial K)) (hG : ∀ i j, μ ((G.coeff i).coeff j) ≤ 1) :
    ∃ G' : Polynomial (Polynomial (intRing μ hμ)),
      G'.map (Polynomial.mapRingHom (intRing μ hμ).subtype) = G := by
  rw [← Polynomial.mem_lifts, Polynomial.lifts_iff_coeff_lifts]
  intro i
  rw [Set.mem_range]
  have : G.coeff i ∈ Polynomial.lifts (intRing μ hμ).subtype := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    intro j
    exact ⟨⟨(G.coeff i).coeff j, hG i j⟩, rfl⟩
  obtain ⟨q, hq⟩ := (Polynomial.mem_lifts _).mp this
  exact ⟨q, hq⟩

end P2MG3b

namespace P2MG3b

open Polynomial

theorem alg_eq_C (R : Type*) [CommRing R] : algebraMap R (PowerSeries R) = PowerSeries.C := by
  ext r; simp

noncomputable def BP {R : Type*} [CommRing R] (G : Polynomial (Polynomial R)) (c : PowerSeries R) :
    Polynomial (PowerSeries R) :=
  (G.map (Polynomial.mapRingHom (PowerSeries.C (R := R)))).map (Polynomial.evalRingHom c)

theorem eval_BP {R : Type*} [CommRing R] (G : Polynomial (Polynomial R)) (c Y : PowerSeries R) :
    (BP G c).eval Y = (G.map (Polynomial.mapRingHom (PowerSeries.C (R := R)))).evalEval c Y := by
  rw [BP, Polynomial.evalEval, Polynomial.eval_map, Polynomial.eval₂_evalRingHom]

theorem derivative_BP {R : Type*} [CommRing R] (G : Polynomial (Polynomial R)) (c : PowerSeries R) :
    Polynomial.derivative (BP G c) = BP (Polynomial.derivative G) c := by
  rw [BP, BP, Polynomial.derivative_map, Polynomial.derivative_map]

theorem hom_eval_BP {R : Type*} [CommRing R] (ψ : PowerSeries R →+* PowerSeries R)
    (hψ : ψ.comp (PowerSeries.C (R := R)) = PowerSeries.C (R := R))
    (G : Polynomial (Polynomial R)) (c Y : PowerSeries R) :
    ψ ((BP G c).eval Y) = (BP G (ψ c)).eval (ψ Y) := by
  rw [eval_BP, eval_BP, ← Polynomial.map_mapRingHom_evalEval ψ, Polynomial.map_map, Polynomial.mapRingHom_comp, hψ]

theorem map_eval_BP {R S : Type*} [CommRing R] [CommRing S] (ι : R →+* S)
    (G : Polynomial (Polynomial R)) (c Y : PowerSeries R) :
    PowerSeries.map ι ((BP G c).eval Y)
      = (BP (G.map (Polynomial.mapRingHom ι)) (PowerSeries.map ι c)).eval (PowerSeries.map ι Y) := by
  rw [eval_BP, eval_BP, ← Polynomial.map_mapRingHom_evalEval (PowerSeries.map ι), Polynomial.map_map,
    Polynomial.map_map, Polynomial.mapRingHom_comp, Polynomial.mapRingHom_comp]
  have : (PowerSeries.map ι).comp (PowerSeries.C (R := R)) = (PowerSeries.C (R := S)).comp ι := by
    ext r : 1
    simp [PowerSeries.map_C]
  rw [this]

theorem constantCoeff_eval_BP {R : Type*} [CommRing R] (G : Polynomial (Polynomial R)) (c Y : PowerSeries R) :
    PowerSeries.constantCoeff ((BP G c).eval Y)
      = G.evalEval (PowerSeries.constantCoeff c) (PowerSeries.constantCoeff Y) := by
  rw [eval_BP, ← Polynomial.map_mapRingHom_evalEval (PowerSeries.constantCoeff (R := R)), Polynomial.map_map,
    Polynomial.mapRingHom_comp]
  have hcomp : (PowerSeries.constantCoeff (R := R)).comp (PowerSeries.C (R := R)) = RingHom.id R := by
    ext r; simp
  rw [hcomp, Polynomial.mapRingHom_id]
  simp [Polynomial.map_id]

theorem mem_span_X_iff {R : Type*} [CommRing R] (f : PowerSeries R) :
    f ∈ Ideal.span ({PowerSeries.X} : Set (PowerSeries R)) ↔ PowerSeries.constantCoeff f = 0 := by
  rw [Ideal.mem_span_singleton, PowerSeries.X_dvd_iff]

theorem eval_map_C_add (R : Type*) [CommRing R] (p : Polynomial R) (z w : R) :
    ∃ q : PowerSeries R, (p.map (PowerSeries.C (R := R))).eval (PowerSeries.C z + PowerSeries.C w * PowerSeries.X)
      = PowerSeries.C (p.eval z) + PowerSeries.C w * PowerSeries.X *
          (PowerSeries.C ((Polynomial.derivative p).eval z) + PowerSeries.C w * PowerSeries.X * q) := by
  obtain ⟨k, hk⟩ := Polynomial.binomExpansion (p.map (PowerSeries.C (R := R))) (PowerSeries.C z)
    (PowerSeries.C w * PowerSeries.X)
  refine ⟨k, ?_⟩
  rw [hk, Polynomial.derivative_map, Polynomial.eval_map, Polynomial.eval₂_at_apply, Polynomial.eval_map,
    Polynomial.eval₂_at_apply]
  ring

theorem eval_BP_C {R : Type*} [CommRing R] (G : Polynomial (Polynomial R)) (c : PowerSeries R) (y : R) :
    (BP G c).eval (PowerSeries.C y) = ((G.eval (Polynomial.C y)).map (PowerSeries.C (R := R))).eval c := by
  rw [eval_BP, Polynomial.evalEval, ← Polynomial.map_C (f := PowerSeries.C (R := R)), Polynomial.map_mapRingHom_eval_map]

theorem exists_integral_root {R : Type*} [CommRing R] (GO : Polynomial (Polynomial R)) (z' y' : R)
    (h0 : GO.evalEval z' y' = 0) :
    ∃ s : PowerSeries R, s ∈ Ideal.span ({PowerSeries.X} : Set (PowerSeries R)) ∧
      (BP GO (PowerSeries.C z' + PowerSeries.C (((Polynomial.derivative GO).evalEval z' y') ^ 2) * PowerSeries.X)).eval
        (PowerSeries.C y' + PowerSeries.C ((Polynomial.derivative GO).evalEval z' y') * s) = 0 := by
  set d' := (Polynomial.derivative GO).evalEval z' y' with hd'
  set e₁ : PowerSeries R := PowerSeries.C z' + PowerSeries.C (d' ^ 2) * PowerSeries.X with he₁
  set G₁ := BP GO e₁ with hG₁
  obtain ⟨q₁, hq₁⟩ := eval_map_C_add R (GO.eval (Polynomial.C y')) z' (d' ^ 2)
  obtain ⟨q₂, hq₂⟩ := eval_map_C_add R ((Polynomial.derivative GO).eval (Polynomial.C y')) z' (d' ^ 2)
  set B₁ : PowerSeries R := PowerSeries.C ((Polynomial.derivative (GO.eval (Polynomial.C y'))).eval z')
      + PowerSeries.C (d' ^ 2) * PowerSeries.X * q₁ with hB₁
  set B₂ : PowerSeries R := PowerSeries.C ((Polynomial.derivative ((Polynomial.derivative GO).eval (Polynomial.C y'))).eval z')
      + PowerSeries.C (d' ^ 2) * PowerSeries.X * q₂ with hB₂
  have hval : G₁.eval (PowerSeries.C y') = PowerSeries.C (d' ^ 2) * PowerSeries.X * B₁ := by
    rw [hG₁, eval_BP_C, hq₁]
    have : (GO.eval (Polynomial.C y')).eval z' = 0 := h0
    rw [this, map_zero, zero_add]
  have hder : (Polynomial.derivative G₁).eval (PowerSeries.C y') = PowerSeries.C d' * (1 + PowerSeries.C d' * PowerSeries.X * B₂) := by
    rw [hG₁, derivative_BP, eval_BP_C, hq₂]
    have : ((Polynomial.derivative GO).eval (Polynomial.C y')).eval z' = d' := rfl
    rw [this, map_pow]; ring
  set v : PowerSeries R := 1 + PowerSeries.C d' * PowerSeries.X * B₂ with hv
  have hvunit : IsUnit v := by
    rw [PowerSeries.isUnit_iff_constantCoeff, hv]; simp
  obtain ⟨vu, hvu⟩ := hvunit
  set vi : PowerSeries R := ((vu⁻¹ : (PowerSeries R)ˣ) : PowerSeries R) with hvi
  have hvvi : v * vi = 1 := by rw [← hvu, hvi, Units.mul_inv]
  set a : PowerSeries R := vi * vi * (PowerSeries.X * B₁) with ha
  have haI : a ∈ Ideal.span ({PowerSeries.X} : Set (PowerSeries R)) :=
    Ideal.mul_mem_left _ _ (Ideal.mul_mem_right _ _ (Ideal.subset_span rfl))
  clear_value B₁ B₂ v vi a
  have hea : G₁.eval (PowerSeries.C y') = (PowerSeries.C d' * v) ^ 2 * a := by
    rw [hval, ha, map_pow]
    linear_combination (-((PowerSeries.C d') ^ 2 * PowerSeries.X * B₁ * (v * vi + 1))) * hvvi
  obtain ⟨t, ht1, ht2⟩ := hensel_rychlik (Ideal.span {PowerSeries.X}) G₁ (PowerSeries.C y') (PowerSeries.C d' * v) a hder hea haI
  refine ⟨v * t, Ideal.mul_mem_left _ _ ht1, ?_⟩
  rw [← ht2]; congr 1; ring

variable {K : Type*} [Field K]

local notation "KT" => PowerSeries K

theorem root_unique (G : Polynomial (Polynomial K)) (c : KT) {Y₁ Y₂ : KT}
    (hsep : (Polynomial.derivative G).evalEval (PowerSeries.constantCoeff c) (PowerSeries.constantCoeff Y₁) ≠ 0)
    (h12 : PowerSeries.constantCoeff Y₁ = PowerSeries.constantCoeff Y₂)
    (h1 : (BP G c).eval Y₁ = 0) (h2 : (BP G c).eval Y₂ = 0) : Y₁ = Y₂ := by
  set I : Ideal KT := Ideal.span {PowerSeries.X} with hI
  set y₀ := PowerSeries.constantCoeff Y₁
  have hG : (BP G c).eval (PowerSeries.C y₀) ∈ I := by
    rw [hI, mem_span_X_iff, constantCoeff_eval_BP, PowerSeries.constantCoeff_C, ← constantCoeff_eval_BP, h1, map_zero]
  have hG' : IsUnit ((Polynomial.derivative (BP G c)).eval (PowerSeries.C y₀)) := by
    rw [derivative_BP, PowerSeries.isUnit_iff_constantCoeff, constantCoeff_eval_BP, PowerSeries.constantCoeff_C]
    exact isUnit_iff_ne_zero.mpr hsep
  obtain ⟨Y, -, huniq⟩ := Ideal.existsUnique_sub_mem_and_eval_eq_zero_of_isUnit_derivative I (BP G c) (PowerSeries.C y₀) hG hG'
  have e1 := huniq Y₁ ⟨by rw [hI, mem_span_X_iff, map_sub, PowerSeries.constantCoeff_C, sub_self], h1⟩
  have e2 := huniq Y₂ ⟨by rw [hI, mem_span_X_iff, map_sub, PowerSeries.constantCoeff_C, ← h12, sub_self], h2⟩
  rw [e1, e2]

theorem rescale_comp_C (a : K) : (PowerSeries.rescale a).comp (PowerSeries.C (R := K)) = PowerSeries.C (R := K) := by
  ext r n
  simp only [RingHom.comp_apply, PowerSeries.coeff_rescale, PowerSeries.coeff_C]
  split_ifs with h
  · subst h; simp
  · simp

theorem main (μ : AbsoluteValue K ℝ) (hμ : IsNonarchimedean μ)
    (G : Polynomial (Polynomial K)) (hG : ∀ i j, μ ((G.coeff i).coeff j) ≤ 1)
    (z₀ y₀ : K) (hz : μ z₀ ≤ 1) (hy : μ y₀ ≤ 1)
    (hsep : (Polynomial.derivative G).evalEval z₀ y₀ ≠ 0)
    (Y : KT) (hY0 : PowerSeries.constantCoeff Y = y₀)
    (hY : (BP G (PowerSeries.C z₀ + PowerSeries.X)).eval Y = 0)
    (n : ℕ) (hn : 1 ≤ n) :
    μ (PowerSeries.coeff n Y) * μ ((Polynomial.derivative G).evalEval z₀ y₀) ^ (2 * n)
      ≤ μ ((Polynomial.derivative G).evalEval z₀ y₀) := by
  classical
  set O : Subring K := intRing μ hμ with hO
  obtain ⟨GO, hGO⟩ := exists_lift μ hμ G hG
  set ι : O →+* K := O.subtype with hι
  set z' : O := ⟨z₀, hz⟩ with hz'
  set y' : O := ⟨y₀, hy⟩ with hy'
  set d : K := (Polynomial.derivative G).evalEval z₀ y₀ with hd
  set d' : O := (Polynomial.derivative GO).evalEval z' y' with hd'
  have hιz : ι z' = z₀ := rfl
  have hιy : ι y' = y₀ := rfl
  have hdd : ι d' = d := by
    rw [hd', ← Polynomial.map_mapRingHom_evalEval ι, ← Polynomial.derivative_map, hGO]; rfl
  have h0 : G.evalEval z₀ y₀ = 0 := by
    have := congrArg PowerSeries.constantCoeff hY
    rwa [constantCoeff_eval_BP, map_add, PowerSeries.constantCoeff_C, PowerSeries.constantCoeff_X,
      add_zero, hY0, map_zero] at this
  have hg0 : GO.evalEval z' y' = 0 := by
    apply Subtype.val_injective
    show ι (GO.evalEval z' y') = ι 0
    rw [← Polynomial.map_mapRingHom_evalEval ι, hGO, map_zero, hιz, hιy, h0]
  obtain ⟨s, hs1, hs2⟩ := exists_integral_root GO z' y' hg0
  rw [← hd'] at hs2
  have hs0 : PowerSeries.constantCoeff s = 0 := (mem_span_X_iff s).mp hs1
  set c₂ : KT := PowerSeries.C z₀ + PowerSeries.C (d ^ 2) * PowerSeries.X with hc₂
  set Y₁ : KT := PowerSeries.C y₀ + PowerSeries.C d * PowerSeries.map ι s with hY₁
  have he₁' : PowerSeries.map ι (PowerSeries.C z' + PowerSeries.C (d' ^ 2) * PowerSeries.X) = c₂ := by
    rw [map_add, map_mul, PowerSeries.map_C, PowerSeries.map_C, PowerSeries.map_X, map_pow, hdd]; rfl
  have hY₁' : PowerSeries.map ι (PowerSeries.C y' + PowerSeries.C d' * s) = Y₁ := by
    rw [map_add, map_mul, PowerSeries.map_C, PowerSeries.map_C, hdd]; rfl
  have hY₁root : (BP G c₂).eval Y₁ = 0 := by
    have := congrArg (PowerSeries.map ι) hs2
    rw [map_zero, map_eval_BP, hGO, he₁', hY₁'] at this
    exact this
  set Y₂ : KT := PowerSeries.rescale (d ^ 2) Y with hY₂
  have hψC : ∀ k : K, PowerSeries.rescale (d ^ 2) (PowerSeries.C k) = PowerSeries.C k := fun k =>
    congrArg (fun φ : K →+* KT => φ k) (rescale_comp_C (K := K) (d ^ 2))
  have hY₂root : (BP G c₂).eval Y₂ = 0 := by
    have := congrArg (PowerSeries.rescale (d ^ 2)) hY
    rw [map_zero, hom_eval_BP (PowerSeries.rescale (d ^ 2)) (rescale_comp_C (d ^ 2)), map_add, hψC,
      PowerSeries.rescale_X] at this
    rw [hc₂, hY₂]; exact this
  have hc₂0 : PowerSeries.constantCoeff c₂ = z₀ := by
    rw [hc₂, map_add, map_mul, PowerSeries.constantCoeff_C, PowerSeries.constantCoeff_X, mul_zero, add_zero]
  have hY₂0 : PowerSeries.constantCoeff Y₂ = y₀ := by
    rw [hY₂, ← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_rescale, pow_zero, one_mul,
      PowerSeries.coeff_zero_eq_constantCoeff_apply, hY0]
  have hY₁0 : PowerSeries.constantCoeff Y₁ = y₀ := by
    rw [hY₁, map_add, map_mul, PowerSeries.constantCoeff_C, PowerSeries.constantCoeff_C,
      ← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map,
      PowerSeries.coeff_zero_eq_constantCoeff_apply, hs0, map_zero, mul_zero, add_zero]
  have hsep' : (Polynomial.derivative G).evalEval (PowerSeries.constantCoeff c₂) (PowerSeries.constantCoeff Y₂) ≠ 0 := by
    rw [hc₂0, hY₂0]; exact hsep
  have heq : Y₂ = Y₁ := root_unique G c₂ hsep' (by rw [hY₂0, hY₁0]) hY₂root hY₁root

  have hcoef : (d ^ 2) ^ n * PowerSeries.coeff n Y = d * ι (PowerSeries.coeff n s) := by
    have := congrArg (PowerSeries.coeff n) heq
    rw [hY₂, PowerSeries.coeff_rescale] at this
    rw [this, hY₁, map_add, PowerSeries.coeff_C, if_neg (by omega), zero_add, PowerSeries.coeff_C_mul,
      PowerSeries.coeff_map]
  have hint : μ (ι (PowerSeries.coeff n s)) ≤ 1 := (PowerSeries.coeff n s).2
  have hcalc : μ (PowerSeries.coeff n Y) * μ d ^ (2 * n) = μ d * μ (ι (PowerSeries.coeff n s)) := by
    rw [← map_pow, pow_mul, ← map_mul, mul_comm, hcoef, map_mul]
  rw [hcalc]
  exact mul_le_of_le_one_right (μ.nonneg _) hint

end P2MG3b

open Polynomial in
theorem solution
    {K : Type*} [Field K] (μ : AbsoluteValue K ℝ) (hμ : IsNonarchimedean μ)
    (G : Polynomial (Polynomial K)) (hG : ∀ i j, μ ((G.coeff i).coeff j) ≤ 1)
    (z₀ y₀ : K) (hz : μ z₀ ≤ 1) (hy : μ y₀ ≤ 1)
    (hsep : (Polynomial.derivative G).evalEval z₀ y₀ ≠ 0)
    (Y : PowerSeries K) (hY0 : PowerSeries.constantCoeff Y = y₀)
    (hY : (G.map (Polynomial.mapRingHom (algebraMap K (PowerSeries K)))).evalEval
        (PowerSeries.C z₀ + PowerSeries.X) Y = 0)
    (n : ℕ) (hn : 1 ≤ n) :
    μ (PowerSeries.coeff n Y) * μ ((Polynomial.derivative G).evalEval z₀ y₀) ^ (2 * n)
      ≤ μ ((Polynomial.derivative G).evalEval z₀ y₀) := by
  have hY' : (P2MG3b.BP G (PowerSeries.C z₀ + PowerSeries.X)).eval Y = 0 := by
    rw [P2MG3b.eval_BP, ← P2MG3b.alg_eq_C]; exact hY
  exact P2MG3b.main μ hμ G hG z₀ y₀ hz hy hsep Y hY0 hY' n hn

end S_Polynomial_abv_coeff_mul_pow_le_of_evalEval_C_add_X_eq_zero
end P2MW
export P2MW.S_Polynomial_abv_coeff_mul_pow_le_of_evalEval_C_add_X_eq_zero (solution)
