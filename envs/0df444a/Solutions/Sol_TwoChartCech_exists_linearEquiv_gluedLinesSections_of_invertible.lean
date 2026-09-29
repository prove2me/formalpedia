-- Prove2me | solution 1 for TwoChartCech.exists_linearEquiv_gluedLinesSections_of_invertible
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/f6110f6f-df79-572f-b48c-4b7e3f72e20d

import Mathlib
import Definitions.Def_TwoChartCech_GluedLines
import Theorems.Thm_TwoChartCech_exists_linearEquiv_gluedLinesM0_of_invertible
import Theorems.Thm_TwoChartCech_exists_linearEquiv_gluedLinesM1_of_invertible
import Theorems.Thm_LaurentPolynomial_isUnit_iff_exists_C_mul_T
import Theorems.Thm_Module_Invertible_of_ringEquiv
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_TwoChartCech_exists_linearEquiv_gluedLinesSections_of_invertible

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 3200000

p2m_open "TwoChartCech P2MW.S_TwoChartCech_exists_linearEquiv_gluedLinesSections_of_invertible.TwoChartCech LaurentPolynomial"
open scoped TensorProduct

universe u

noncomputable section

namespace TwoChartCech
p2m_export "TwoChartCech" "levalUnit polyPart invPolyPart gluedLinesOverlap gluedLinesCover GluedCond GluedCond.zero GluedCond.mul gluedLinesM01 gluedLinesM0 gluedLinesM1 gluedLinesSections Cover Sections exists_linearEquiv_gluedLinesM0_of_invertible exists_linearEquiv_gluedLinesM1_of_invertible"
p2m_open "TwoChartCech"
namespace GluedLinesModel

variable {k : Type u} [Field k] {s : ℕ}

theorem eval_toLaurent (u : kˣ) (p : Polynomial k) : levalUnit k u (Polynomial.toLaurent p) = p.eval (u : k) := by
  rw [levalUnit, LaurentPolynomial.eval₂_toLaurent, Polynomial.eval₂_id]

theorem toLaurent_mem_polyPart (p : Polynomial k) : Polynomial.toLaurent p ∈ polyPart k := by
  intro n hn
  rw [LaurentPolynomial.toLaurent_support] at hn
  obtain ⟨m, -, rfl⟩ := Finset.mem_map.mp hn
  exact Int.natCast_nonneg m

def lagr (a : Fin s → kˣ) (t : Fin s → k) : k[T;T⁻¹] := by
  classical
  exact Polynomial.toLaurent (Lagrange.interpolate Finset.univ (fun i => (a i : k)) t)

theorem lagr_mem_polyPart (a : Fin s → kˣ) (t : Fin s → k) : lagr a t ∈ polyPart k := toLaurent_mem_polyPart _

theorem eval_lagr (a : Fin s → kˣ) (ha : Function.Injective a) (t : Fin s → k) (i : Fin s) :
    levalUnit k (a i) (lagr a t) = t i := by
  classical
  rw [lagr, eval_toLaurent]
  exact Lagrange.eval_interpolate_at_node _ (fun i _ j _ h => ha (Units.ext h)) (Finset.mem_univ i)

variable (a b : Fin s → kˣ) (ha : Function.Injective a) (hb : Function.Injective b)

def w₁ (μ : Fin s → kˣ) : k[T;T⁻¹] × k[T;T⁻¹] := (lagr a (fun i => (μ i : k)), 1)

def w₂ (μ : Fin s → kˣ) : k[T;T⁻¹] × k[T;T⁻¹] := (1, lagr b (fun i => ((μ i)⁻¹ : kˣ)))

include ha in
theorem gluedCond_w₁ (μ : Fin s → kˣ) : GluedCond a b μ (w₁ a μ) := fun i => by
  change levalUnit k (a i) (lagr a _) = μ i * levalUnit k (b i) 1
  rw [eval_lagr a ha, map_one, mul_one]

include hb in
theorem gluedCond_w₂ (μ : Fin s → kˣ) : GluedCond a b μ (w₂ b μ) := fun i => by
  change levalUnit k (a i) 1 = μ i * levalUnit k (b i) (lagr b _)
  rw [eval_lagr b hb, map_one, Units.mul_inv]

theorem w₁_mem_polyPart (μ : Fin s → kˣ) : w₁ a μ ∈ (polyPart k).prod (polyPart k) :=
  Subalgebra.mem_prod.mpr ⟨lagr_mem_polyPart _ _, Subalgebra.one_mem _⟩

theorem w₂_mem_polyPart (μ : Fin s → kˣ) : w₂ b μ ∈ (polyPart k).prod (polyPart k) :=
  Subalgebra.mem_prod.mpr ⟨Subalgebra.one_mem _, lagr_mem_polyPart _ _⟩

theorem decomp (μ : Fin s → kˣ) (v : k[T;T⁻¹] × k[T;T⁻¹]) :
    let f₁ := lagr a (fun i => levalUnit k (b i) v.2)
    ((f₁, v.2) : k[T;T⁻¹] × k[T;T⁻¹]) * w₁ a μ + (v.1 - f₁ * (w₁ a μ).1, 0) * w₂ b μ = v := by
  intro f₁
  apply Prod.ext
  · change f₁ * (w₁ a μ).1 + (v.1 - f₁ * (w₁ a μ).1) * 1 = v.1
    ring
  · change v.2 * 1 + 0 * (w₂ b μ).2 = v.2
    ring

include ha in
theorem coeff_f_mem_overlap (μ : Fin s → kˣ) (v : k[T;T⁻¹] × k[T;T⁻¹]) :
    ((lagr a (fun i => levalUnit k (b i) v.2), v.2) : k[T;T⁻¹] × k[T;T⁻¹]) ∈ gluedLinesOverlap k a b :=
  fun i => by change levalUnit k (a i) (lagr a _) = levalUnit k (b i) v.2; rw [eval_lagr a ha]

include ha in
theorem coeff_g_mem_overlap (μ : Fin s → kˣ) (v : k[T;T⁻¹] × k[T;T⁻¹]) (hv : GluedCond a b μ v) :
    ((v.1 - lagr a (fun i => levalUnit k (b i) v.2) * (w₁ a μ).1, 0) : k[T;T⁻¹] × k[T;T⁻¹]) ∈
      gluedLinesOverlap k a b := fun i => by
  change levalUnit k (a i) (v.1 - lagr a _ * lagr a _) = levalUnit k (b i) 0
  rw [map_sub, map_mul, eval_lagr a ha, eval_lagr a ha, hv i, map_zero]
  ring

include ha in

theorem exists_coeffs_M01 (μ : Fin s → kˣ) (v : ↥(gluedLinesM01 k a b μ)) :
    ∃ f g : ↥(gluedLinesOverlap k a b), (v : k[T;T⁻¹] × k[T;T⁻¹]) = (f : _) * w₁ a μ + (g : _) * w₂ b μ :=
  ⟨⟨_, coeff_f_mem_overlap a b ha μ v⟩, ⟨_, coeff_g_mem_overlap a b ha μ v v.2⟩, (decomp a b μ v).symm⟩

include ha in

theorem exists_coeffs_M0 (μ : Fin s → kˣ) (v : ↥(gluedLinesM0 k a b μ)) :
    ∃ f g : ↥(gluedLinesOverlap k a b ⊓ (polyPart k).prod (polyPart k)),
      (v : k[T;T⁻¹] × k[T;T⁻¹]) = (f : _) * w₁ a μ + (g : _) * w₂ b μ := by
  obtain ⟨hcond, hpoly⟩ := v.2
  obtain ⟨hp1, hp2⟩ := Subalgebra.mem_prod.mp hpoly
  refine ⟨⟨_, coeff_f_mem_overlap a b ha μ v, Subalgebra.mem_prod.mpr ⟨lagr_mem_polyPart _ _, hp2⟩⟩,
    ⟨_, coeff_g_mem_overlap a b ha μ v hcond, Subalgebra.mem_prod.mpr ⟨?_, Subalgebra.zero_mem _⟩⟩,
    (decomp a b μ v).symm⟩
  exact Subalgebra.sub_mem _ hp1 (Subalgebra.mul_mem _ (lagr_mem_polyPart _ _) (lagr_mem_polyPart _ _))

theorem mul_mem_gluedCond {μ ν : Fin s → kˣ} {v w : k[T;T⁻¹] × k[T;T⁻¹]} (hv : GluedCond a b μ v)
    (hw : GluedCond a b ν w) : GluedCond a b (μ * ν) (v * w) := fun i => by
  simp only [Prod.fst_mul, Prod.snd_mul, map_mul, hv i, hw i, Pi.mul_apply, Units.val_mul]
  ring

include ha hb in

theorem M01_mul_M01_inv (μ : Fin s → kˣ) :
    gluedLinesM01 k a b μ * gluedLinesM01 k a b μ⁻¹ = 1 := by
  apply le_antisymm
  · rw [Submodule.mul_le]
    intro v hv w hw
    rw [Submodule.mem_one]
    have h := mul_mem_gluedCond a b hv hw
    rw [mul_inv_cancel] at h
    refine ⟨⟨v * w, fun i => ?_⟩, rfl⟩
    have := h i
    rwa [Pi.one_apply, Units.val_one, one_mul] at this
  · rw [Submodule.one_le]

    have h11 : w₁ a μ * w₁ a μ⁻¹ ∈ gluedLinesM01 k a b μ * gluedLinesM01 k a b μ⁻¹ :=
      Submodule.mul_mem_mul (gluedCond_w₁ a b ha μ) (gluedCond_w₁ a b ha μ⁻¹)
    have h22 : w₂ b μ * w₂ b μ⁻¹ ∈ gluedLinesM01 k a b μ * gluedLinesM01 k a b μ⁻¹ :=
      Submodule.mul_mem_mul (gluedCond_w₂ a b hb μ) (gluedCond_w₂ a b hb μ⁻¹)
    set P := (w₁ a μ).1 * (w₁ a μ⁻¹).1 with hP
    have hPa : ∀ i, levalUnit k (a i) P = 1 := fun i => by
      rw [hP, map_mul]
      change levalUnit k (a i) (lagr a _) * levalUnit k (a i) (lagr a _) = 1
      rw [eval_lagr a ha, eval_lagr a ha, Pi.inv_apply, ← Units.val_mul, mul_inv_cancel, Units.val_one]
    have hβ : ((1 - P, 0) : k[T;T⁻¹] × k[T;T⁻¹]) ∈ gluedLinesOverlap k a b := fun i => by
      change levalUnit k (a i) (1 - P) = levalUnit k (b i) 0
      rw [map_sub, map_one, hPa, sub_self, map_zero]
    have hsum : (1 : k[T;T⁻¹] × k[T;T⁻¹]) =
        w₁ a μ * w₁ a μ⁻¹ + (⟨(1 - P, 0), hβ⟩ : ↥(gluedLinesOverlap k a b)) • (w₂ b μ * w₂ b μ⁻¹) := by
      rw [Subalgebra.smul_def, smul_eq_mul]
      apply Prod.ext
      · change (1 : k[T;T⁻¹]) = P + (1 - P) * (1 * 1); ring
      · change (1 : k[T;T⁻¹]) = 1 * 1 + 0 * ((w₂ b μ).2 * (w₂ b μ⁻¹).2); ring
    rw [hsum]
    exact Submodule.add_mem _ h11 (Submodule.smul_mem _ _ h22)

include ha hb in

theorem invertible_M01 (μ : Fin s → kˣ) : Module.Invertible ↥(gluedLinesOverlap k a b) ↥(gluedLinesM01 k a b μ) := by
  haveI : FaithfulSMul ↥(gluedLinesOverlap k a b) (k[T;T⁻¹] × k[T;T⁻¹]) :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr Subtype.val_injective
  let U : (Submodule ↥(gluedLinesOverlap k a b) (k[T;T⁻¹] × k[T;T⁻¹]))ˣ :=
    ⟨gluedLinesM01 k a b μ, gluedLinesM01 k a b μ⁻¹, M01_mul_M01_inv a b ha hb μ,
      (mul_comm _ _).trans (M01_mul_M01_inv a b ha hb μ)⟩
  exact Module.Invertible.left (Submodule.tensorInvEquiv U)

include ha hb in
theorem M0_mul_M0_inv (μ : Fin s → kˣ) :
    gluedLinesM0 k a b μ * gluedLinesM0 k a b μ⁻¹ = 1 := by
  apply le_antisymm
  · rw [Submodule.mul_le]
    intro v hv w hw
    rw [Submodule.mem_one]
    have h := mul_mem_gluedCond a b hv.1 hw.1
    rw [mul_inv_cancel] at h
    refine ⟨⟨v * w, fun i => ?_, Subalgebra.mul_mem _ hv.2 hw.2⟩, rfl⟩
    have := h i
    rwa [Pi.one_apply, Units.val_one, one_mul] at this
  · rw [Submodule.one_le]
    have h11 : w₁ a μ * w₁ a μ⁻¹ ∈ gluedLinesM0 k a b μ * gluedLinesM0 k a b μ⁻¹ :=
      Submodule.mul_mem_mul ⟨gluedCond_w₁ a b ha μ, w₁_mem_polyPart a μ⟩ ⟨gluedCond_w₁ a b ha μ⁻¹, w₁_mem_polyPart a μ⁻¹⟩
    have h22 : w₂ b μ * w₂ b μ⁻¹ ∈ gluedLinesM0 k a b μ * gluedLinesM0 k a b μ⁻¹ :=
      Submodule.mul_mem_mul ⟨gluedCond_w₂ a b hb μ, w₂_mem_polyPart b μ⟩ ⟨gluedCond_w₂ a b hb μ⁻¹, w₂_mem_polyPart b μ⁻¹⟩
    set P := (w₁ a μ).1 * (w₁ a μ⁻¹).1 with hP
    have hPa : ∀ i, levalUnit k (a i) P = 1 := fun i => by
      rw [hP, map_mul]
      change levalUnit k (a i) (lagr a _) * levalUnit k (a i) (lagr a _) = 1
      rw [eval_lagr a ha, eval_lagr a ha, Pi.inv_apply, ← Units.val_mul, mul_inv_cancel, Units.val_one]
    have hPpoly : P ∈ polyPart k := Subalgebra.mul_mem _ (lagr_mem_polyPart _ _) (lagr_mem_polyPart _ _)
    have hβ : ((1 - P, 0) : k[T;T⁻¹] × k[T;T⁻¹]) ∈ gluedLinesOverlap k a b ⊓ (polyPart k).prod (polyPart k) :=
      ⟨fun i => by
        change levalUnit k (a i) (1 - P) = levalUnit k (b i) 0
        rw [map_sub, map_one, hPa, sub_self, map_zero],
       Subalgebra.mem_prod.mpr ⟨Subalgebra.sub_mem _ (Subalgebra.one_mem _) hPpoly, Subalgebra.zero_mem _⟩⟩
    have hsum : (1 : k[T;T⁻¹] × k[T;T⁻¹]) =
        w₁ a μ * w₁ a μ⁻¹ + (⟨(1 - P, 0), hβ⟩ : ↥(gluedLinesOverlap k a b ⊓ (polyPart k).prod (polyPart k))) •
          (w₂ b μ * w₂ b μ⁻¹) := by
      rw [Subalgebra.smul_def, smul_eq_mul]
      apply Prod.ext
      · change (1 : k[T;T⁻¹]) = P + (1 - P) * (1 * 1); ring
      · change (1 : k[T;T⁻¹]) = 1 * 1 + 0 * ((w₂ b μ).2 * (w₂ b μ⁻¹).2); ring
    rw [hsum]
    exact Submodule.add_mem _ h11 (Submodule.smul_mem _ _ h22)

include ha hb in

theorem invertible_M0 (μ : Fin s → kˣ) :
    Module.Invertible ↥(gluedLinesOverlap k a b ⊓ (polyPart k).prod (polyPart k)) ↥(gluedLinesM0 k a b μ) := by
  haveI : FaithfulSMul ↥(gluedLinesOverlap k a b ⊓ (polyPart k).prod (polyPart k)) (k[T;T⁻¹] × k[T;T⁻¹]) :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr Subtype.val_injective
  let U : (Submodule ↥(gluedLinesOverlap k a b ⊓ (polyPart k).prod (polyPart k)) (k[T;T⁻¹] × k[T;T⁻¹]))ˣ :=
    ⟨gluedLinesM0 k a b μ, gluedLinesM0 k a b μ⁻¹, M0_mul_M0_inv a b ha hb μ,
      (mul_comm _ _).trans (M0_mul_M0_inv a b ha hb μ)⟩
  exact Module.Invertible.left (Submodule.tensorInvEquiv U)

def lagrInv (a : Fin s → kˣ) (t : Fin s → k) : k[T;T⁻¹] :=
  LaurentPolynomial.invert (lagr (fun i => (a i)⁻¹) t)

theorem lagrInv_mem_invPolyPart (a : Fin s → kˣ) (t : Fin s → k) : lagrInv a t ∈ invPolyPart k := by
  intro n hn
  have hne : (lagrInv a t).coeff n ≠ 0 := Finsupp.mem_support_iff.mp hn
  simp only [lagrInv, LaurentPolynomial.invert_apply] at hne
  have := lagr_mem_polyPart (fun i => (a i)⁻¹) t (-n) (Finsupp.mem_support_iff.mpr hne)
  omega

theorem levalUnit_invert' (u : kˣ) (f : k[T;T⁻¹]) :
    levalUnit k u (LaurentPolynomial.invert f) = levalUnit k u⁻¹ f := by
  induction f using LaurentPolynomial.induction_on' with
  | add p q hp hq => simp only [map_add, hp, hq]
  | C_mul_T n c =>
    have hinv : LaurentPolynomial.invert (LaurentPolynomial.C c * T n : k[T;T⁻¹]) = LaurentPolynomial.C c * T (-n) := by
      simp
    rw [hinv, levalUnit, LaurentPolynomial.eval₂_C_mul_T, LaurentPolynomial.eval₂_C_mul_T, inv_zpow']

theorem eval_lagrInv (a : Fin s → kˣ) (ha : Function.Injective a) (t : Fin s → k) (i : Fin s) :
    levalUnit k (a i) (lagrInv a t) = t i := by
  rw [lagrInv, levalUnit_invert']
  exact eval_lagr (fun i => (a i)⁻¹) (fun i j h => ha (inv_injective h)) t i

def w₁' (μ : Fin s → kˣ) : k[T;T⁻¹] × k[T;T⁻¹] := (lagrInv a (fun i => (μ i : k)), 1)

def w₂' (μ : Fin s → kˣ) : k[T;T⁻¹] × k[T;T⁻¹] := (1, lagrInv b (fun i => ((μ i)⁻¹ : kˣ)))

include ha in
theorem gluedCond_w₁' (μ : Fin s → kˣ) : GluedCond a b μ (w₁' a μ) := fun i => by
  change levalUnit k (a i) (lagrInv a _) = μ i * levalUnit k (b i) 1
  rw [eval_lagrInv a ha, map_one, mul_one]

include hb in
theorem gluedCond_w₂' (μ : Fin s → kˣ) : GluedCond a b μ (w₂' b μ) := fun i => by
  change levalUnit k (a i) 1 = μ i * levalUnit k (b i) (lagrInv b _)
  rw [eval_lagrInv b hb, map_one, Units.mul_inv]

theorem mem_N1_iff (μ : Fin s → kˣ) (v : k[T;T⁻¹] × k[T;T⁻¹]) :
    v ∈ gluedLinesM1 k a b μ 0 0 ↔ GluedCond a b μ v ∧ v.1 ∈ invPolyPart k ∧ v.2 ∈ invPolyPart k := by
  change (GluedCond a b μ v ∧ v.1 * T (-0) ∈ invPolyPart k ∧ v.2 * T (-0) ∈ invPolyPart k) ↔ _
  rw [neg_zero, T_zero, mul_one, mul_one]

include ha hb in
theorem N1_mul_N1_inv (μ : Fin s → kˣ) :
    gluedLinesM1 k a b μ 0 0 * gluedLinesM1 k a b μ⁻¹ 0 0 = 1 := by
  apply le_antisymm
  · rw [Submodule.mul_le]
    intro v hv w hw
    rw [mem_N1_iff] at hv hw
    rw [Submodule.mem_one]
    have h := mul_mem_gluedCond a b hv.1 hw.1
    rw [mul_inv_cancel] at h
    refine ⟨⟨v * w, fun i => ?_, Subalgebra.mem_prod.mpr
      ⟨Subalgebra.mul_mem _ hv.2.1 hw.2.1, Subalgebra.mul_mem _ hv.2.2 hw.2.2⟩⟩, rfl⟩
    have := h i
    rwa [Pi.one_apply, Units.val_one, one_mul] at this
  · rw [Submodule.one_le]
    have hm₁ : ∀ ν : Fin s → kˣ, w₁' a ν ∈ gluedLinesM1 k a b ν 0 0 := fun ν =>
      (mem_N1_iff a b ν _).mpr ⟨gluedCond_w₁' a b ha ν, lagrInv_mem_invPolyPart _ _, Subalgebra.one_mem _⟩
    have hm₂ : ∀ ν : Fin s → kˣ, w₂' b ν ∈ gluedLinesM1 k a b ν 0 0 := fun ν =>
      (mem_N1_iff a b ν _).mpr ⟨gluedCond_w₂' a b hb ν, Subalgebra.one_mem _, lagrInv_mem_invPolyPart _ _⟩
    have h11 : w₁' a μ * w₁' a μ⁻¹ ∈ gluedLinesM1 k a b μ 0 0 * gluedLinesM1 k a b μ⁻¹ 0 0 :=
      Submodule.mul_mem_mul (hm₁ μ) (hm₁ μ⁻¹)
    have h22 : w₂' b μ * w₂' b μ⁻¹ ∈ gluedLinesM1 k a b μ 0 0 * gluedLinesM1 k a b μ⁻¹ 0 0 :=
      Submodule.mul_mem_mul (hm₂ μ) (hm₂ μ⁻¹)
    set P := (w₁' a μ).1 * (w₁' a μ⁻¹).1 with hP
    have hPa : ∀ i, levalUnit k (a i) P = 1 := fun i => by
      rw [hP, map_mul]
      change levalUnit k (a i) (lagrInv a _) * levalUnit k (a i) (lagrInv a _) = 1
      rw [eval_lagrInv a ha, eval_lagrInv a ha, Pi.inv_apply, ← Units.val_mul, mul_inv_cancel, Units.val_one]
    have hPinv : P ∈ invPolyPart k := Subalgebra.mul_mem _ (lagrInv_mem_invPolyPart _ _) (lagrInv_mem_invPolyPart _ _)
    have hβ : ((1 - P, 0) : k[T;T⁻¹] × k[T;T⁻¹]) ∈ gluedLinesOverlap k a b ⊓ (invPolyPart k).prod (invPolyPart k) :=
      ⟨fun i => by
        change levalUnit k (a i) (1 - P) = levalUnit k (b i) 0
        rw [map_sub, map_one, hPa, sub_self, map_zero],
       Subalgebra.mem_prod.mpr ⟨Subalgebra.sub_mem _ (Subalgebra.one_mem _) hPinv, Subalgebra.zero_mem _⟩⟩
    have hsum : (1 : k[T;T⁻¹] × k[T;T⁻¹]) =
        w₁' a μ * w₁' a μ⁻¹ + (⟨(1 - P, 0), hβ⟩ : ↥(gluedLinesOverlap k a b ⊓ (invPolyPart k).prod (invPolyPart k))) •
          (w₂' b μ * w₂' b μ⁻¹) := by
      rw [Subalgebra.smul_def, smul_eq_mul]
      apply Prod.ext
      · change (1 : k[T;T⁻¹]) = P + (1 - P) * (1 * 1); ring
      · change (1 : k[T;T⁻¹]) = 1 * 1 + 0 * ((w₂' b μ).2 * (w₂' b μ⁻¹).2); ring
    rw [hsum]
    exact Submodule.add_mem _ h11 (Submodule.smul_mem _ _ h22)

include ha hb in

theorem invertible_N1 (μ : Fin s → kˣ) :
    Module.Invertible ↥(gluedLinesOverlap k a b ⊓ (invPolyPart k).prod (invPolyPart k)) ↥(gluedLinesM1 k a b μ 0 0) := by
  haveI : FaithfulSMul ↥(gluedLinesOverlap k a b ⊓ (invPolyPart k).prod (invPolyPart k)) (k[T;T⁻¹] × k[T;T⁻¹]) :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr Subtype.val_injective
  let U : (Submodule ↥(gluedLinesOverlap k a b ⊓ (invPolyPart k).prod (invPolyPart k)) (k[T;T⁻¹] × k[T;T⁻¹]))ˣ :=
    ⟨gluedLinesM1 k a b μ 0 0, gluedLinesM1 k a b μ⁻¹ 0 0, N1_mul_N1_inv a b ha hb μ,
      (mul_comm _ _).trans (N1_mul_N1_inv a b ha hb μ)⟩
  exact Module.Invertible.left (Submodule.tensorInvEquiv U)

section BaseChange

abbrev A0s (k : Type u) [Field k] {s : ℕ} (a b : Fin s → kˣ) : Subalgebra k (k[T;T⁻¹] × k[T;T⁻¹]) :=
  gluedLinesOverlap k a b ⊓ (polyPart k).prod (polyPart k)
abbrev A01s (k : Type u) [Field k] {s : ℕ} (a b : Fin s → kˣ) : Subalgebra k (k[T;T⁻¹] × k[T;T⁻¹]) :=
  gluedLinesOverlap k a b

@[reducible] def algebraA0A01 : Algebra ↥(A0s k a b) ↥(A01s k a b) :=
  (Subalgebra.inclusion (inf_le_left : A0s k a b ≤ A01s k a b)).toRingHom.toAlgebra

attribute [local instance] algebraA0A01

scoped instance isScalarTower_A0_A01_amb :
    IsScalarTower ↥(A0s k a b) ↥(A01s k a b) (k[T;T⁻¹] × k[T;T⁻¹]) :=
  ⟨fun r t v => show ((r : k[T;T⁻¹] × k[T;T⁻¹]) * (t : k[T;T⁻¹] × k[T;T⁻¹])) * v =
      (r : k[T;T⁻¹] × k[T;T⁻¹]) * ((t : k[T;T⁻¹] × k[T;T⁻¹]) * v) from mul_assoc _ _ _⟩

def inclM0 (μ : Fin s → kˣ) : ↥(gluedLinesM0 k a b μ) →ₗ[↥(A0s k a b)] ↥(gluedLinesM01 k a b μ) where
  toFun v := ⟨v.1, v.2.1⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

include ha hb in

theorem exists_baseChange_M0 (μ : Fin s → kˣ) :
    ∃ e : ↥(A01s k a b) ⊗[↥(A0s k a b)] ↥(gluedLinesM0 k a b μ) ≃ₗ[↥(A01s k a b)] ↥(gluedLinesM01 k a b μ),
      ∀ v, e ((1 : ↥(A01s k a b)) ⊗ₜ[↥(A0s k a b)] v) = ⟨v.1, v.2.1⟩ := by
  let Φ := (inclM0 a b μ).liftBaseChange ↥(A01s k a b)
  have hΦ : ∀ (f : ↥(A01s k a b)) (v : ↥(gluedLinesM0 k a b μ)),
      Φ (f ⊗ₜ v) = f • (⟨v.1, v.2.1⟩ : ↥(gluedLinesM01 k a b μ)) :=
    fun f v => LinearMap.liftBaseChange_tmul _ _ _ _
  have hsurj : Function.Surjective Φ := by
    intro w
    obtain ⟨f, g, hfg⟩ := exists_coeffs_M01 a b ha μ w
    let v₁ : ↥(gluedLinesM0 k a b μ) := ⟨w₁ a μ, gluedCond_w₁ a b ha μ, w₁_mem_polyPart a μ⟩
    let v₂ : ↥(gluedLinesM0 k a b μ) := ⟨w₂ b μ, gluedCond_w₂ a b hb μ, w₂_mem_polyPart b μ⟩
    refine ⟨f ⊗ₜ v₁ + g ⊗ₜ v₂, ?_⟩
    rw [map_add, hΦ, hΦ]
    apply Subtype.ext
    change (f : k[T;T⁻¹] × k[T;T⁻¹]) * w₁ a μ + (g : k[T;T⁻¹] × k[T;T⁻¹]) * w₂ b μ = w
    exact hfg.symm
  haveI := invertible_M0 a b ha hb μ
  haveI := invertible_M01 a b ha hb μ
  have hbij : Function.Bijective Φ := Module.Invertible.bijective_of_surjective hsurj
  refine ⟨LinearEquiv.ofBijective Φ hbij, fun v => ?_⟩
  rw [LinearEquiv.ofBijective_apply, hΦ, one_smul]

end BaseChange

section Hom

open Polynomial in

def cond₀ : k[T;T⁻¹] × k[T;T⁻¹] :=
  (Polynomial.toLaurent (∏ i, (Polynomial.X - Polynomial.C (a i : k))),
    Polynomial.toLaurent (∏ i, (Polynomial.X - Polynomial.C (b i : k))))

open Polynomial in
theorem cond₀_ne_zero : (cond₀ a b).1 ≠ 0 ∧ (cond₀ a b).2 ≠ 0 := by
  constructor <;>
  · refine Polynomial.toLaurent_ne_zero.mpr (Polynomial.Monic.ne_zero ?_)
    exact Polynomial.monic_prod_of_monic _ _ fun i _ => Polynomial.monic_X_sub_C _

open Polynomial in
theorem eval_cond₀ (i : Fin s) : levalUnit k (a i) (cond₀ a b).1 = 0 ∧ levalUnit k (b i) (cond₀ a b).2 = 0 := by
  constructor <;>
  · rw [cond₀, eval_toLaurent, Polynomial.eval_prod]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp)

theorem cond₀_mul_mem (w : k[T;T⁻¹] × k[T;T⁻¹]) : cond₀ a b * w ∈ gluedLinesOverlap k a b := fun i => by
  rw [Prod.fst_mul, Prod.snd_mul, map_mul, map_mul, (eval_cond₀ a b i).1, (eval_cond₀ a b i).2, zero_mul, zero_mul]

theorem mul_hom_comm {μ μ' : Fin s → kˣ}
    (ψ : ↥(gluedLinesM01 k a b μ) →ₗ[↥(gluedLinesOverlap k a b)] ↥(gluedLinesM01 k a b μ'))
    (v w : ↥(gluedLinesM01 k a b μ)) :
    (w : k[T;T⁻¹] × k[T;T⁻¹]) * ((ψ v : ↥(gluedLinesM01 k a b μ')) : k[T;T⁻¹] × k[T;T⁻¹]) = (v : k[T;T⁻¹] × k[T;T⁻¹]) * ((ψ w : ↥(gluedLinesM01 k a b μ')) : k[T;T⁻¹] × k[T;T⁻¹]) := by
  set c := cond₀ a b with hc
  let cw : ↥(gluedLinesOverlap k a b) := ⟨c * w, cond₀_mul_mem a b w⟩
  let cv : ↥(gluedLinesOverlap k a b) := ⟨c * v, cond₀_mul_mem a b v⟩
  have h1 : cw • v = cv • w := Subtype.ext (by
    change c * (w : k[T;T⁻¹] × k[T;T⁻¹]) * v = c * (v : k[T;T⁻¹] × k[T;T⁻¹]) * w; ring)
  have h2 := congrArg (fun z => ((ψ z : ↥(gluedLinesM01 k a b μ')) : k[T;T⁻¹] × k[T;T⁻¹])) h1
  simp only [map_smul] at h2
  change c * (w : k[T;T⁻¹] × k[T;T⁻¹]) * ((ψ v : ↥(gluedLinesM01 k a b μ')) : k[T;T⁻¹] × k[T;T⁻¹]) =
    c * (v : k[T;T⁻¹] × k[T;T⁻¹]) * (ψ w : k[T;T⁻¹] × k[T;T⁻¹]) at h2
  have h3 : c * ((w : k[T;T⁻¹] × k[T;T⁻¹]) * ((ψ v : ↥(gluedLinesM01 k a b μ')) : k[T;T⁻¹] × k[T;T⁻¹]) -
      (v : k[T;T⁻¹] × k[T;T⁻¹]) * (ψ w : k[T;T⁻¹] × k[T;T⁻¹])) = 0 := by
    rw [mul_sub, ← mul_assoc, ← mul_assoc, h2, sub_self]
  have h4 := Prod.ext_iff.mp h3
  rw [Prod.fst_mul, Prod.snd_mul, Prod.fst_zero, Prod.snd_zero] at h4
  have e1 := (mul_eq_zero.mp h4.1).resolve_left (cond₀_ne_zero a b).1
  have e2 := (mul_eq_zero.mp h4.2).resolve_left (cond₀_ne_zero a b).2
  exact sub_eq_zero.mp (Prod.ext e1 e2)

include ha hb in

theorem exists_hom_eq_mul {μ μ' : Fin s → kˣ}
    (ψ : ↥(gluedLinesM01 k a b μ) →ₗ[↥(gluedLinesOverlap k a b)] ↥(gluedLinesM01 k a b μ')) :
    ∃ u : k[T;T⁻¹] × k[T;T⁻¹], ∀ v : ↥(gluedLinesM01 k a b μ), ((ψ v : ↥(gluedLinesM01 k a b μ')) : k[T;T⁻¹] × k[T;T⁻¹]) = u * v := by
  let W₁ : ↥(gluedLinesM01 k a b μ) := ⟨w₁ a μ, gluedCond_w₁ a b ha μ⟩
  let W₂ : ↥(gluedLinesM01 k a b μ) := ⟨w₂ b μ, gluedCond_w₂ a b hb μ⟩
  refine ⟨(((ψ W₂ : ↥(gluedLinesM01 k a b μ')) : k[T;T⁻¹] × k[T;T⁻¹]).1, ((ψ W₁ : ↥(gluedLinesM01 k a b μ')) : k[T;T⁻¹] × k[T;T⁻¹]).2), fun v => ?_⟩
  have h1 := Prod.ext_iff.mp (mul_hom_comm a b ψ v W₁)
  have h2 := Prod.ext_iff.mp (mul_hom_comm a b ψ v W₂)
  simp only [Prod.fst_mul, Prod.snd_mul] at h1 h2
  apply Prod.ext
  ·
    have := h2.1
    change (1 : k[T;T⁻¹]) * ((ψ v : ↥(gluedLinesM01 k a b μ')) : k[T;T⁻¹] × k[T;T⁻¹]).1 = (v : k[T;T⁻¹] × k[T;T⁻¹]).1 * ((ψ W₂ : ↥(gluedLinesM01 k a b μ')) : k[T;T⁻¹] × k[T;T⁻¹]).1 at this
    rw [one_mul] at this
    rw [this, Prod.fst_mul, mul_comm]
  ·
    have := h1.2
    change (1 : k[T;T⁻¹]) * ((ψ v : ↥(gluedLinesM01 k a b μ')) : k[T;T⁻¹] × k[T;T⁻¹]).2 = (v : k[T;T⁻¹] × k[T;T⁻¹]).2 * ((ψ W₁ : ↥(gluedLinesM01 k a b μ')) : k[T;T⁻¹] × k[T;T⁻¹]).2 at this
    rw [one_mul] at this
    rw [this, Prod.snd_mul, mul_comm]

end Hom

section BaseChange1

theorem decomp' (μ : Fin s → kˣ) (v : k[T;T⁻¹] × k[T;T⁻¹]) :
    let f₁ := lagr a (fun i => levalUnit k (b i) v.2)
    ((f₁, v.2) : k[T;T⁻¹] × k[T;T⁻¹]) * w₁' a μ + (v.1 - f₁ * (w₁' a μ).1, 0) * w₂' b μ = v := by
  intro f₁
  apply Prod.ext
  · change f₁ * (w₁' a μ).1 + (v.1 - f₁ * (w₁' a μ).1) * 1 = v.1
    ring
  · change v.2 * 1 + 0 * (w₂' b μ).2 = v.2
    ring

include ha in
theorem coeff_g'_mem_overlap (μ : Fin s → kˣ) (v : k[T;T⁻¹] × k[T;T⁻¹]) (hv : GluedCond a b μ v) :
    ((v.1 - lagr a (fun i => levalUnit k (b i) v.2) * (w₁' a μ).1, 0) : k[T;T⁻¹] × k[T;T⁻¹]) ∈
      gluedLinesOverlap k a b := fun i => by
  change levalUnit k (a i) (v.1 - lagr a _ * lagrInv a _) = levalUnit k (b i) 0
  rw [map_sub, map_mul, eval_lagr a ha, eval_lagrInv a ha, hv i, map_zero]
  ring

include ha in

theorem exists_coeffs_M01' (μ : Fin s → kˣ) (v : ↥(gluedLinesM01 k a b μ)) :
    ∃ f g : ↥(gluedLinesOverlap k a b), (v : k[T;T⁻¹] × k[T;T⁻¹]) = (f : _) * w₁' a μ + (g : _) * w₂' b μ :=
  ⟨⟨_, coeff_f_mem_overlap a b ha μ v⟩, ⟨_, coeff_g'_mem_overlap a b ha μ v v.2⟩, (decomp' a b μ v).symm⟩

abbrev A1s (k : Type u) [Field k] {s : ℕ} (a b : Fin s → kˣ) : Subalgebra k (k[T;T⁻¹] × k[T;T⁻¹]) :=
  gluedLinesOverlap k a b ⊓ (invPolyPart k).prod (invPolyPart k)

@[reducible] def algebraA1A01 : Algebra ↥(A1s k a b) ↥(A01s k a b) :=
  (Subalgebra.inclusion (inf_le_left : A1s k a b ≤ A01s k a b)).toRingHom.toAlgebra

attribute [local instance] algebraA1A01

scoped instance isScalarTower_A1_A01_amb :
    IsScalarTower ↥(A1s k a b) ↥(A01s k a b) (k[T;T⁻¹] × k[T;T⁻¹]) :=
  ⟨fun r t v => show ((r : k[T;T⁻¹] × k[T;T⁻¹]) * (t : k[T;T⁻¹] × k[T;T⁻¹])) * v =
      (r : k[T;T⁻¹] × k[T;T⁻¹]) * ((t : k[T;T⁻¹] × k[T;T⁻¹]) * v) from mul_assoc _ _ _⟩

def inclN1 (μ : Fin s → kˣ) : ↥(gluedLinesM1 k a b μ 0 0) →ₗ[↥(A1s k a b)] ↥(gluedLinesM01 k a b μ) where
  toFun v := ⟨v.1, v.2.1⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

include ha hb in

theorem exists_baseChange_N1 (μ : Fin s → kˣ) :
    ∃ e : ↥(A01s k a b) ⊗[↥(A1s k a b)] ↥(gluedLinesM1 k a b μ 0 0) ≃ₗ[↥(A01s k a b)] ↥(gluedLinesM01 k a b μ),
      ∀ v, e ((1 : ↥(A01s k a b)) ⊗ₜ[↥(A1s k a b)] v) = ⟨v.1, v.2.1⟩ := by
  let Φ := (inclN1 a b μ).liftBaseChange ↥(A01s k a b)
  have hΦ : ∀ (f : ↥(A01s k a b)) (v : ↥(gluedLinesM1 k a b μ 0 0)),
      Φ (f ⊗ₜ v) = f • (⟨v.1, v.2.1⟩ : ↥(gluedLinesM01 k a b μ)) :=
    fun f v => LinearMap.liftBaseChange_tmul _ _ _ _
  have hsurj : Function.Surjective Φ := by
    intro w
    obtain ⟨f, g, hfg⟩ := exists_coeffs_M01' a b ha μ w
    let v₁ : ↥(gluedLinesM1 k a b μ 0 0) := ⟨w₁' a μ, (mem_N1_iff a b μ _).mpr
      ⟨gluedCond_w₁' a b ha μ, lagrInv_mem_invPolyPart _ _, Subalgebra.one_mem _⟩⟩
    let v₂ : ↥(gluedLinesM1 k a b μ 0 0) := ⟨w₂' b μ, (mem_N1_iff a b μ _).mpr
      ⟨gluedCond_w₂' a b hb μ, Subalgebra.one_mem _, lagrInv_mem_invPolyPart _ _⟩⟩
    refine ⟨f ⊗ₜ v₁ + g ⊗ₜ v₂, ?_⟩
    rw [map_add, hΦ, hΦ]
    apply Subtype.ext
    change (f : k[T;T⁻¹] × k[T;T⁻¹]) * w₁' a μ + (g : k[T;T⁻¹] × k[T;T⁻¹]) * w₂' b μ = w
    exact hfg.symm
  haveI := invertible_N1 a b ha hb μ
  haveI := invertible_M01 a b ha hb μ
  have hbij : Function.Bijective Φ := Module.Invertible.bijective_of_surjective hsurj
  refine ⟨LinearEquiv.ofBijective Φ hbij, fun v => ?_⟩
  rw [LinearEquiv.ofBijective_apply, hΦ, one_smul]

end BaseChange1

end GluedLinesModel
p2m_reactivate "P2MW.S_TwoChartCech_exists_linearEquiv_gluedLinesSections_of_invertible.TwoChartCech.GluedLinesModel"
end TwoChartCech
p2m_reactivate "P2MW.S_TwoChartCech_exists_linearEquiv_gluedLinesSections_of_invertible.TwoChartCech.GluedLinesModel P2MW.S_TwoChartCech_exists_linearEquiv_gluedLinesSections_of_invertible.TwoChartCech"

end
p2m_reactivate "P2MW.S_TwoChartCech_exists_linearEquiv_gluedLinesSections_of_invertible.TwoChartCech.GluedLinesModel P2MW.S_TwoChartCech_exists_linearEquiv_gluedLinesSections_of_invertible.TwoChartCech"

set_option maxHeartbeats 16000000 in
open TwoChartCech.GluedLinesModel in

theorem solution
    (k : Type u) [Field k] {s : ℕ} (a b : Fin s → kˣ) (ha : Function.Injective a) (hb : Function.Injective b)
    (𝒰 : Cover.{u, u} k) (S : Sections.{u, u, u} 𝒰)
    (φ₀ : 𝒰.A0 ≃ₐ[k] (gluedLinesCover k a b).A0) (φ₁ : 𝒰.A1 ≃ₐ[k] (gluedLinesCover k a b).A1)
    (φ₀₁ : 𝒰.A01 ≃ₐ[k] (gluedLinesCover k a b).A01)
    (hφ₀ : ∀ f, φ₀₁ (𝒰.ρ0 f) = (gluedLinesCover k a b).ρ0 (φ₀ f))
    (hφ₁ : ∀ f, φ₀₁ (𝒰.ρ1 f) = (gluedLinesCover k a b).ρ1 (φ₁ f))
    [Module.Invertible 𝒰.A0 S.M0] [Module.Invertible 𝒰.A1 S.M1] :
    letI : Algebra 𝒰.A0 𝒰.A01 := 𝒰.ρ0.toRingHom.toAlgebra
    letI : Algebra 𝒰.A1 𝒰.A01 := 𝒰.ρ1.toRingHom.toAlgebra
    ∀ (rbc0 : 𝒰.A01 ⊗[𝒰.A0] S.M0 ≃ₗ[𝒰.A01] S.M01) (rbc1 : 𝒰.A01 ⊗[𝒰.A1] S.M1 ≃ₗ[𝒰.A01] S.M01),
      (∀ t, rbc0 ((1 : 𝒰.A01) ⊗ₜ[𝒰.A0] t) = S.r0 t) →
      (∀ t, rbc1 ((1 : 𝒰.A01) ⊗ₜ[𝒰.A1] t) = S.r1 t) →
      ∃ (n m : ℤ) (lam : Fin s → kˣ)
        (e₀ : S.M0 ≃ₗ[k] (gluedLinesSections k a b lam n m).M0)
        (e₁ : S.M1 ≃ₗ[k] (gluedLinesSections k a b lam n m).M1)
        (e₀₁ : S.M01 ≃ₗ[k] (gluedLinesSections k a b lam n m).M01),
        (∀ t, e₀₁ (S.r0 t) = (gluedLinesSections k a b lam n m).r0 (e₀ t)) ∧
        (∀ t, e₀₁ (S.r1 t) = (gluedLinesSections k a b lam n m).r1 (e₁ t)) := by
  classical
  letI algA0 : Algebra 𝒰.A0 𝒰.A01 := 𝒰.ρ0.toRingHom.toAlgebra
  letI algA1 : Algebra 𝒰.A1 𝒰.A01 := 𝒰.ρ1.toRingHom.toAlgebra
  intro rbc0 rbc1 hr0 hr1

  haveI inv01 : Module.Invertible 𝒰.A01 S.M01 := Module.Invertible.congr rbc0

  letI algφ₀ : Algebra 𝒰.A0 ↥(A0s k a b) := φ₀.toAlgHom.toRingHom.toAlgebra
  letI algφ₁ : Algebra 𝒰.A1 ↥(A1s k a b) := φ₁.toAlgHom.toRingHom.toAlgebra
  obtain ⟨μ0, ⟨eP0⟩⟩ := TwoChartCech.exists_linearEquiv_gluedLinesM0_of_invertible k a b ha hb
    (↥(A0s k a b) ⊗[𝒰.A0] S.M0)
  obtain ⟨μ1, ⟨eP1⟩⟩ := TwoChartCech.exists_linearEquiv_gluedLinesM1_of_invertible k a b ha hb
    (↥(A1s k a b) ⊗[𝒰.A1] S.M1)

  have smul_one_φ₀ : ∀ r : 𝒰.A0, r • (1 : ↥(A0s k a b)) = φ₀ r := fun r => by
    rw [Algebra.smul_def, mul_one]; rfl
  have j0_smul : ∀ (r : 𝒰.A0) (m : S.M0),
      ((1 : ↥(A0s k a b)) ⊗ₜ[𝒰.A0] (r • m) : ↥(A0s k a b) ⊗[𝒰.A0] S.M0) = φ₀ r • ((1 : ↥(A0s k a b)) ⊗ₜ[𝒰.A0] m) :=
    fun r m => by rw [← TensorProduct.smul_tmul, smul_one_φ₀, TensorProduct.smul_tmul', smul_eq_mul, mul_one]

  let ℓ0 : ↥(A0s k a b) ⊗[𝒰.A0] S.M0 →ₗ[𝒰.A0] S.M0 :=
    TensorProduct.lift
      { toFun := fun x =>
          { toFun := fun m => φ₀.symm x • m
            map_add' := fun _ _ => smul_add _ _ _
            map_smul' := fun r m => by rw [RingHom.id_apply, smul_comm] }
        map_add' := fun x y => by ext m; change φ₀.symm (x + y) • m = φ₀.symm x • m + φ₀.symm y • m; rw [map_add, add_smul]
        map_smul' := fun r x => by
          ext m
          change φ₀.symm (r • x) • m = r • (φ₀.symm x • m)
          rw [Algebra.smul_def, map_mul, mul_smul]
          congr 1
          exact φ₀.symm_apply_apply r }
  have ℓ0_tmul : ∀ (x : ↥(A0s k a b)) (m : S.M0), ℓ0 (x ⊗ₜ m) = φ₀.symm x • m := fun x m => TensorProduct.lift.tmul _ _
  have ℓ0_j0 : ∀ m : S.M0, ℓ0 ((1 : ↥(A0s k a b)) ⊗ₜ m) = m := fun m => by rw [ℓ0_tmul, map_one, one_smul]
  have j0_ℓ0 : ∀ z : ↥(A0s k a b) ⊗[𝒰.A0] S.M0, ((1 : ↥(A0s k a b)) ⊗ₜ[𝒰.A0] (ℓ0 z)) = z := fun z => by
    induction z using TensorProduct.induction_on with
    | zero => rw [map_zero, TensorProduct.tmul_zero]
    | tmul x m =>
      rw [ℓ0_tmul, ← TensorProduct.smul_tmul, smul_one_φ₀, AlgEquiv.apply_symm_apply]
    | add z w hz hw => rw [map_add, TensorProduct.tmul_add, hz, hw]

  have E0_smul_aux : ∀ (c : k) (m : S.M0),
      eP0 ((1 : ↥(A0s k a b)) ⊗ₜ[𝒰.A0] (c • m)) = c • eP0 ((1 : ↥(A0s k a b)) ⊗ₜ[𝒰.A0] m) := fun c m => by
    rw [← algebraMap_smul 𝒰.A0 c m, j0_smul, map_smul, AlgEquiv.commutes, algebraMap_smul]
  let E0 : S.M0 ≃ₗ[k] ↥(gluedLinesM0 k a b μ0) :=
    { toFun := fun m => eP0 ((1 : ↥(A0s k a b)) ⊗ₜ[𝒰.A0] m)
      map_add' := fun m m' => by rw [TensorProduct.tmul_add, map_add]
      map_smul' := fun c m => by rw [RingHom.id_apply]; exact E0_smul_aux c m
      invFun := fun v => ℓ0 (eP0.symm v)
      left_inv := fun m => by change ℓ0 (eP0.symm (eP0 _)) = m; rw [LinearEquiv.symm_apply_apply, ℓ0_j0]
      right_inv := fun v => by change eP0 (1 ⊗ₜ ℓ0 (eP0.symm v)) = v; rw [j0_ℓ0, LinearEquiv.apply_symm_apply] }
  have E0_apply : ∀ m : S.M0, E0 m = eP0 ((1 : ↥(A0s k a b)) ⊗ₜ[𝒰.A0] m) := fun _ => rfl
  have E0_smul : ∀ (r : 𝒰.A0) (m : S.M0), (E0 (r • m) : k[T;T⁻¹] × k[T;T⁻¹]) = (φ₀ r : k[T;T⁻¹] × k[T;T⁻¹]) * E0 m :=
    fun r m => by rw [E0_apply, E0_apply, j0_smul, map_smul]; rfl

  letI modAmb : Module 𝒰.A0 (k[T;T⁻¹] × k[T;T⁻¹]) :=
    Module.compHom (k[T;T⁻¹] × k[T;T⁻¹]) ((A0s k a b).val.toRingHom.comp φ₀.toAlgHom.toRingHom)
  have amb_smul : ∀ (r : 𝒰.A0) (z : k[T;T⁻¹] × k[T;T⁻¹]), r • z = (φ₀ r : k[T;T⁻¹] × k[T;T⁻¹]) * z :=
    fun _ _ => rfl
  have coe_φ₀₁_algebraMap : ∀ r : 𝒰.A0,
      ((φ₀₁ (algebraMap 𝒰.A0 𝒰.A01 r) : ↥(A01s k a b)) : k[T;T⁻¹] × k[T;T⁻¹]) = (φ₀ r : k[T;T⁻¹] × k[T;T⁻¹]) :=
    fun r => by change ((φ₀₁ (𝒰.ρ0 r) : ↥(A01s k a b)) : k[T;T⁻¹] × k[T;T⁻¹]) = _; rw [hφ₀]; rfl
  let B : 𝒰.A01 →ₗ[𝒰.A0] S.M0 →ₗ[𝒰.A0] (k[T;T⁻¹] × k[T;T⁻¹]) :=
    { toFun := fun t =>
        { toFun := fun m => (φ₀₁ t : k[T;T⁻¹] × k[T;T⁻¹]) * (E0 m : k[T;T⁻¹] × k[T;T⁻¹])
          map_add' := fun m m' => by rw [map_add, Submodule.coe_add, mul_add]
          map_smul' := fun r m => by
            rw [RingHom.id_apply, E0_smul, amb_smul]
            ring }
      map_add' := fun t t' => by
        refine LinearMap.ext fun m => ?_
        change ((φ₀₁ (t + t') : ↥(A01s k a b)) : k[T;T⁻¹] × k[T;T⁻¹]) * _ =
          (φ₀₁ t : k[T;T⁻¹] × k[T;T⁻¹]) * _ + (φ₀₁ t' : k[T;T⁻¹] × k[T;T⁻¹]) * _
        rw [map_add, Subalgebra.coe_add, add_mul]
      map_smul' := fun r t => by
        refine LinearMap.ext fun m => ?_
        change ((φ₀₁ (r • t) : ↥(A01s k a b)) : k[T;T⁻¹] × k[T;T⁻¹]) * (E0 m : k[T;T⁻¹] × k[T;T⁻¹]) =
          (φ₀ r : k[T;T⁻¹] × k[T;T⁻¹]) * ((φ₀₁ t : k[T;T⁻¹] × k[T;T⁻¹]) * (E0 m : k[T;T⁻¹] × k[T;T⁻¹]))
        rw [Algebra.smul_def, map_mul, Subalgebra.coe_mul, coe_φ₀₁_algebraMap, mul_assoc] }
  let F : 𝒰.A01 ⊗[𝒰.A0] S.M0 →ₗ[𝒰.A0] (k[T;T⁻¹] × k[T;T⁻¹]) := TensorProduct.lift B
  have F_tmul : ∀ (t : 𝒰.A01) (m : S.M0),
      F (t ⊗ₜ m) = (φ₀₁ t : k[T;T⁻¹] × k[T;T⁻¹]) * (E0 m : k[T;T⁻¹] × k[T;T⁻¹]) :=
    fun t m => TensorProduct.lift.tmul _ _
  have F_smul : ∀ (t : 𝒰.A01) (z : 𝒰.A01 ⊗[𝒰.A0] S.M0),
      F (t • z) = (φ₀₁ t : k[T;T⁻¹] × k[T;T⁻¹]) * F z := fun t z => by
    induction z using TensorProduct.induction_on with
    | zero => rw [smul_zero, map_zero, mul_zero]
    | tmul t' m => rw [TensorProduct.smul_tmul', smul_eq_mul, F_tmul, F_tmul, map_mul, Subalgebra.coe_mul, mul_assoc]
    | add z w hz hw => rw [smul_add, map_add, map_add, hz, hw, mul_add]
  have F_mem : ∀ z : 𝒰.A01 ⊗[𝒰.A0] S.M0, GluedCond a b μ0 (F z) := fun z => by
    induction z using TensorProduct.induction_on with
    | zero => rw [map_zero]; exact GluedCond.zero a b μ0
    | tmul t m => rw [F_tmul]; exact GluedCond.mul (φ₀₁ t).2 (E0 m).2.1
    | add z w hz hw => rw [map_add]; exact hz.add hw

  letI modM01 : Module 𝒰.A01 ↥(gluedLinesM01 k a b μ0) := Module.compHom _ φ₀₁.toAlgHom.toRingHom
  haveI := invertible_M01 a b ha hb μ0
  haveI invM01 : Module.Invertible 𝒰.A01 ↥(gluedLinesM01 k a b μ0) :=
    Module.Invertible.of_ringEquiv φ₀₁.toRingEquiv ↥(gluedLinesM01 k a b μ0) (fun _ _ => rfl)
  let e01L : S.M01 →ₗ[𝒰.A01] ↥(gluedLinesM01 k a b μ0) :=
    { toFun := fun x => ⟨F (rbc0.symm x), F_mem _⟩
      map_add' := fun x y => Subtype.ext (by
        change F (rbc0.symm (x + y)) = F (rbc0.symm x) + F (rbc0.symm y); rw [map_add, map_add])
      map_smul' := fun t x => Subtype.ext (by
        change F (rbc0.symm (t • x)) = (φ₀₁ t : k[T;T⁻¹] × k[T;T⁻¹]) * F (rbc0.symm x)
        rw [map_smul, F_smul]) }
  have e01_coe : ∀ x : S.M01, (e01L x : k[T;T⁻¹] × k[T;T⁻¹]) = F (rbc0.symm x) := fun _ => rfl
  have e01_r0 : ∀ m : S.M0, (e01L (S.r0 m) : k[T;T⁻¹] × k[T;T⁻¹]) = E0 m := fun m => by
    rw [e01_coe, ← hr0, LinearEquiv.symm_apply_apply, F_tmul, map_one, Subalgebra.coe_one, one_mul]
  have e01_smul : ∀ (t : 𝒰.A01) (x : S.M01),
      (e01L (t • x) : k[T;T⁻¹] × k[T;T⁻¹]) = (φ₀₁ t : k[T;T⁻¹] × k[T;T⁻¹]) * e01L x :=
    fun t x => by rw [map_smul]; rfl
  have e01_r0' : ∀ m : S.M0, e01L (S.r0 m) = ⟨(E0 m).1, (E0 m).2.1⟩ := fun m => Subtype.ext (e01_r0 m)
  have e01_surj : Function.Surjective e01L := by
    intro w
    obtain ⟨f, g, hfg⟩ := exists_coeffs_M01 a b ha μ0 w
    let W₁ : ↥(gluedLinesM0 k a b μ0) := ⟨w₁ a μ0, gluedCond_w₁ a b ha μ0, w₁_mem_polyPart a μ0⟩
    let W₂ : ↥(gluedLinesM0 k a b μ0) := ⟨w₂ b μ0, gluedCond_w₂ a b hb μ0, w₂_mem_polyPart b μ0⟩
    refine ⟨φ₀₁.symm f • S.r0 (E0.symm W₁) + φ₀₁.symm g • S.r0 (E0.symm W₂), ?_⟩
    have h1 : e01L (φ₀₁.symm f • S.r0 (E0.symm W₁)) = φ₀₁.symm f • e01L (S.r0 (E0.symm W₁)) := map_smul _ _ _
    have h2 : e01L (φ₀₁.symm g • S.r0 (E0.symm W₂)) = φ₀₁.symm g • e01L (S.r0 (E0.symm W₂)) := map_smul _ _ _
    rw [map_add, h1, h2, e01_r0', e01_r0']
    apply Subtype.ext
    change (φ₀₁ (φ₀₁.symm f) : k[T;T⁻¹] × k[T;T⁻¹]) * (E0 (E0.symm W₁) : k[T;T⁻¹] × k[T;T⁻¹]) +
      (φ₀₁ (φ₀₁.symm g) : k[T;T⁻¹] × k[T;T⁻¹]) * (E0 (E0.symm W₂) : k[T;T⁻¹] × k[T;T⁻¹]) = w
    rw [AlgEquiv.apply_symm_apply, AlgEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply,
      LinearEquiv.apply_symm_apply]
    exact hfg.symm
  have e01_bij : Function.Bijective e01L := Module.Invertible.bijective_of_surjective e01_surj

  have smul_one_φ₁ : ∀ r : 𝒰.A1, r • (1 : ↥(A1s k a b)) = φ₁ r := fun r => by
    rw [Algebra.smul_def, mul_one]; rfl
  have j1_smul : ∀ (r : 𝒰.A1) (m : S.M1),
      ((1 : ↥(A1s k a b)) ⊗ₜ[𝒰.A1] (r • m) : ↥(A1s k a b) ⊗[𝒰.A1] S.M1) = φ₁ r • ((1 : ↥(A1s k a b)) ⊗ₜ[𝒰.A1] m) :=
    fun r m => by rw [← TensorProduct.smul_tmul, smul_one_φ₁, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  let ℓ1 : ↥(A1s k a b) ⊗[𝒰.A1] S.M1 →ₗ[𝒰.A1] S.M1 :=
    TensorProduct.lift
      { toFun := fun x =>
          { toFun := fun m => φ₁.symm x • m
            map_add' := fun _ _ => smul_add _ _ _
            map_smul' := fun r m => by rw [RingHom.id_apply, smul_comm] }
        map_add' := fun x y => by ext m; change φ₁.symm (x + y) • m = φ₁.symm x • m + φ₁.symm y • m; rw [map_add, add_smul]
        map_smul' := fun r x => by
          ext m
          change φ₁.symm (r • x) • m = r • (φ₁.symm x • m)
          rw [Algebra.smul_def, map_mul, mul_smul]
          congr 1
          exact φ₁.symm_apply_apply r }
  have ℓ1_tmul : ∀ (x : ↥(A1s k a b)) (m : S.M1), ℓ1 (x ⊗ₜ m) = φ₁.symm x • m := fun x m => TensorProduct.lift.tmul _ _
  have ℓ1_j1 : ∀ m : S.M1, ℓ1 ((1 : ↥(A1s k a b)) ⊗ₜ m) = m := fun m => by rw [ℓ1_tmul, map_one, one_smul]
  have j1_ℓ1 : ∀ z : ↥(A1s k a b) ⊗[𝒰.A1] S.M1, ((1 : ↥(A1s k a b)) ⊗ₜ[𝒰.A1] (ℓ1 z)) = z := fun z => by
    induction z using TensorProduct.induction_on with
    | zero => rw [map_zero, TensorProduct.tmul_zero]
    | tmul x m =>
      rw [ℓ1_tmul, ← TensorProduct.smul_tmul, smul_one_φ₁, AlgEquiv.apply_symm_apply]
    | add z w hz hw => rw [map_add, TensorProduct.tmul_add, hz, hw]
  have E1_smul_aux : ∀ (c : k) (m : S.M1),
      eP1 ((1 : ↥(A1s k a b)) ⊗ₜ[𝒰.A1] (c • m)) = c • eP1 ((1 : ↥(A1s k a b)) ⊗ₜ[𝒰.A1] m) := fun c m => by
    rw [← algebraMap_smul 𝒰.A1 c m, j1_smul, map_smul, AlgEquiv.commutes, algebraMap_smul]
  let E1 : S.M1 ≃ₗ[k] ↥(gluedLinesM1 k a b μ1 0 0) :=
    { toFun := fun m => eP1 ((1 : ↥(A1s k a b)) ⊗ₜ[𝒰.A1] m)
      map_add' := fun m m' => by rw [TensorProduct.tmul_add, map_add]
      map_smul' := fun c m => by rw [RingHom.id_apply]; exact E1_smul_aux c m
      invFun := fun v => ℓ1 (eP1.symm v)
      left_inv := fun m => by change ℓ1 (eP1.symm (eP1 _)) = m; rw [LinearEquiv.symm_apply_apply, ℓ1_j1]
      right_inv := fun v => by change eP1 (1 ⊗ₜ ℓ1 (eP1.symm v)) = v; rw [j1_ℓ1, LinearEquiv.apply_symm_apply] }
  have E1_apply : ∀ m : S.M1, E1 m = eP1 ((1 : ↥(A1s k a b)) ⊗ₜ[𝒰.A1] m) := fun _ => rfl
  have E1_smul : ∀ (r : 𝒰.A1) (m : S.M1), (E1 (r • m) : k[T;T⁻¹] × k[T;T⁻¹]) = (φ₁ r : k[T;T⁻¹] × k[T;T⁻¹]) * E1 m :=
    fun r m => by rw [E1_apply, E1_apply, j1_smul, map_smul]; rfl
  have E1_symm_smul : ∀ (x : ↥(A1s k a b)) (v : ↥(gluedLinesM1 k a b μ1 0 0)),
      E1.symm (x • v) = φ₁.symm x • E1.symm v := fun x v => by
    apply E1.injective
    apply Subtype.ext
    rw [LinearEquiv.apply_symm_apply, E1_smul, AlgEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
    rfl

  letI algA1s : Algebra ↥(A1s k a b) ↥(A01s k a b) := algebraA1A01 a b
  have coe_φ₀₁_ρ1 : ∀ x : ↥(A1s k a b),
      ((φ₀₁ (𝒰.ρ1 (φ₁.symm x)) : ↥(A01s k a b)) : k[T;T⁻¹] × k[T;T⁻¹]) = (x : k[T;T⁻¹] × k[T;T⁻¹]) :=
    fun x => by rw [hφ₁, AlgEquiv.apply_symm_apply]; rfl
  let ψ0' : ↥(gluedLinesM1 k a b μ1 0 0) →ₗ[↥(A1s k a b)] ↥(gluedLinesM01 k a b μ0) :=
    { toFun := fun v => e01L (S.r1 (E1.symm v))
      map_add' := fun v v' => by rw [map_add, map_add, map_add]
      map_smul' := fun x v => Subtype.ext (by
        rw [RingHom.id_apply, E1_symm_smul, S.r1_smul, e01_smul, coe_φ₀₁_ρ1]
        rfl) }
  have ψ0'_coe : ∀ v, (ψ0' v : k[T;T⁻¹] × k[T;T⁻¹]) = e01L (S.r1 (E1.symm v)) := fun _ => rfl
  obtain ⟨bc1, hbc1⟩ := exists_baseChange_N1 a b ha hb μ1
  let Ψ : ↥(gluedLinesM01 k a b μ1) →ₗ[↥(A01s k a b)] ↥(gluedLinesM01 k a b μ0) :=
    (ψ0'.liftBaseChange ↥(A01s k a b)).comp bc1.symm.toLinearMap
  have Ψ_N1 : ∀ v : ↥(gluedLinesM1 k a b μ1 0 0),
      (Ψ ⟨v.1, v.2.1⟩ : k[T;T⁻¹] × k[T;T⁻¹]) = e01L (S.r1 (E1.symm v)) := fun v => by
    have h1 : bc1.symm ⟨v.1, v.2.1⟩ = (1 : ↥(A01s k a b)) ⊗ₜ v := by
      rw [LinearEquiv.symm_apply_eq]; exact (hbc1 v).symm
    change ((ψ0'.liftBaseChange ↥(A01s k a b)) (bc1.symm ⟨v.1, v.2.1⟩) : k[T;T⁻¹] × k[T;T⁻¹]) = _
    rw [h1, LinearMap.liftBaseChange_tmul, one_smul]
    rfl

  have Ψ_surj : Function.Surjective Ψ := by
    intro w
    obtain ⟨x, rfl⟩ := e01_surj w
    obtain ⟨z, rfl⟩ := rbc1.surjective x
    induction z using TensorProduct.induction_on with
    | zero => exact ⟨0, by rw [map_zero, map_zero, map_zero]⟩
    | tmul t m1 =>
      refine ⟨φ₀₁ t • ⟨(E1 m1).1, (E1 m1).2.1⟩, Subtype.ext ?_⟩
      rw [map_smul, Submodule.coe_smul, Subalgebra.smul_def, smul_eq_mul, Ψ_N1, LinearEquiv.symm_apply_apply,
        ← e01_smul, ← hr1, ← map_smul rbc1, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    | add z z' hz hz' =>
      obtain ⟨y, hy⟩ := hz
      obtain ⟨y', hy'⟩ := hz'
      exact ⟨y + y', by rw [map_add, hy, hy', map_add, map_add]⟩
  haveI := invertible_M01 a b ha hb μ1
  have Ψ_bij : Function.Bijective Ψ := Module.Invertible.bijective_of_surjective Ψ_surj
  let ΨE := LinearEquiv.ofBijective Ψ Ψ_bij
  obtain ⟨u, hu⟩ := exists_hom_eq_mul a b ha hb Ψ
  obtain ⟨u', hu'⟩ := exists_hom_eq_mul a b ha hb ΨE.symm.toLinearMap

  have huu' : ∀ W : ↥(gluedLinesM01 k a b μ1), u' * (u * (W : k[T;T⁻¹] × k[T;T⁻¹])) = W := fun W => by
    have := congrArg (fun z : ↥(gluedLinesM01 k a b μ1) => (z : k[T;T⁻¹] × k[T;T⁻¹])) (ΨE.symm_apply_apply W)
    change ((ΨE.symm.toLinearMap (Ψ W) : ↥(gluedLinesM01 k a b μ1)) : k[T;T⁻¹] × k[T;T⁻¹]) = W at this
    rwa [hu', hu] at this
  have hW₁ := Prod.ext_iff.mp (huu' ⟨w₁ a μ1, gluedCond_w₁ a b ha μ1⟩)
  have hW₂ := Prod.ext_iff.mp (huu' ⟨w₂ b μ1, gluedCond_w₂ a b hb μ1⟩)
  have hunit1 : u'.1 * u.1 = 1 := by
    have := hW₂.1
    change u'.1 * (u.1 * 1) = 1 at this
    rwa [mul_one] at this
  have hunit2 : u'.2 * u.2 = 1 := by
    have := hW₁.2
    change u'.2 * (u.2 * 1) = 1 at this
    rwa [mul_one] at this
  obtain ⟨c, n, hcn⟩ := (LaurentPolynomial.isUnit_iff_exists_C_mul_T u.1).mp
    ⟨Units.mkOfMulEqOne u.1 u'.1 ((mul_comm _ _).trans hunit1), rfl⟩
  obtain ⟨c', m, hcm⟩ := (LaurentPolynomial.isUnit_iff_exists_C_mul_T u.2).mp
    ⟨Units.mkOfMulEqOne u.2 u'.2 ((mul_comm _ _).trans hunit2), rfl⟩

  have hu_eq : u = (LaurentPolynomial.C (c : k) * T n, LaurentPolynomial.C (c' : k) * T m) := Prod.ext hcn hcm

  have hu'1 : u'.1 = LaurentPolynomial.C ((c⁻¹ : kˣ) : k) * T (-n) := by
    have h : u'.1 * (LaurentPolynomial.C (c : k) * T n) = 1 := by rw [← hcn]; exact hunit1
    calc u'.1 = u'.1 * (LaurentPolynomial.C (c : k) * T n) * (LaurentPolynomial.C ((c⁻¹ : kˣ) : k) * T (-n)) := by
            rw [mul_assoc, show LaurentPolynomial.C (c : k) * T n * (LaurentPolynomial.C ((c⁻¹ : kˣ) : k) * T (-n)) =
              (LaurentPolynomial.C (c : k) * LaurentPolynomial.C ((c⁻¹ : kˣ) : k)) * (T n * T (-n)) by ring,
              ← map_mul, Units.mul_inv, map_one, one_mul, ← T_add, add_neg_cancel, T_zero, mul_one]
      _ = LaurentPolynomial.C ((c⁻¹ : kˣ) : k) * T (-n) := by rw [h, one_mul]
  have hu'2 : u'.2 = LaurentPolynomial.C ((c'⁻¹ : kˣ) : k) * T (-m) := by
    have h : u'.2 * (LaurentPolynomial.C (c' : k) * T m) = 1 := by rw [← hcm]; exact hunit2
    calc u'.2 = u'.2 * (LaurentPolynomial.C (c' : k) * T m) * (LaurentPolynomial.C ((c'⁻¹ : kˣ) : k) * T (-m)) := by
            rw [mul_assoc, show LaurentPolynomial.C (c' : k) * T m * (LaurentPolynomial.C ((c'⁻¹ : kˣ) : k) * T (-m)) =
              (LaurentPolynomial.C (c' : k) * LaurentPolynomial.C ((c'⁻¹ : kˣ) : k)) * (T m * T (-m)) by ring,
              ← map_mul, Units.mul_inv, map_one, one_mul, ← T_add, add_neg_cancel, T_zero, mul_one]
      _ = LaurentPolynomial.C ((c'⁻¹ : kˣ) : k) * T (-m) := by rw [h, one_mul]
  have huu'1 : u.1 * u'.1 = 1 := (mul_comm _ _).trans hunit1
  have huu'2 : u.2 * u'.2 = 1 := (mul_comm _ _).trans hunit2
  have C_mem_inv : ∀ d : k, (LaurentPolynomial.C d : k[T;T⁻¹]) ∈ invPolyPart k := fun d => by
    intro j hj
    rw [← LaurentPolynomial.single_eq_C] at hj
    rw [Finset.mem_singleton.mp (Finsupp.support_single_subset hj)]

  have mem_fwd : ∀ v : ↥(gluedLinesM1 k a b μ1 0 0), u * (v : k[T;T⁻¹] × k[T;T⁻¹]) ∈ gluedLinesM1 k a b μ0 n m := by
    intro v
    obtain ⟨-, hv1, hv2⟩ := (mem_N1_iff a b μ1 _).mp v.2
    refine ⟨?_, ?_, ?_⟩
    · have := (Ψ ⟨v.1, v.2.1⟩).2
      rwa [hu] at this
    · rw [hu_eq]
      change LaurentPolynomial.C (c : k) * T n * (v : k[T;T⁻¹] × k[T;T⁻¹]).1 * T (-n) ∈ invPolyPart k
      rw [show LaurentPolynomial.C (c : k) * T n * (v : k[T;T⁻¹] × k[T;T⁻¹]).1 * T (-n) =
          LaurentPolynomial.C (c : k) * (v : k[T;T⁻¹] × k[T;T⁻¹]).1 * (T n * T (-n)) by ring,
        ← T_add, add_neg_cancel, T_zero, mul_one]
      exact Subalgebra.mul_mem _ (C_mem_inv _) hv1
    · rw [hu_eq]
      change LaurentPolynomial.C (c' : k) * T m * (v : k[T;T⁻¹] × k[T;T⁻¹]).2 * T (-m) ∈ invPolyPart k
      rw [show LaurentPolynomial.C (c' : k) * T m * (v : k[T;T⁻¹] × k[T;T⁻¹]).2 * T (-m) =
          LaurentPolynomial.C (c' : k) * (v : k[T;T⁻¹] × k[T;T⁻¹]).2 * (T m * T (-m)) by ring,
        ← T_add, add_neg_cancel, T_zero, mul_one]
      exact Subalgebra.mul_mem _ (C_mem_inv _) hv2
  have mem_bwd : ∀ z : ↥(gluedLinesM1 k a b μ0 n m), u' * (z : k[T;T⁻¹] × k[T;T⁻¹]) ∈ gluedLinesM1 k a b μ1 0 0 := by
    intro z
    obtain ⟨hz0, hz1, hz2⟩ := z.2
    refine (mem_N1_iff a b μ1 _).mpr ⟨?_, ?_, ?_⟩
    · have := (ΨE.symm.toLinearMap ⟨z.1, hz0⟩).2
      rwa [hu'] at this
    · change u'.1 * (z : k[T;T⁻¹] × k[T;T⁻¹]).1 ∈ invPolyPart k
      rw [hu'1, show LaurentPolynomial.C ((c⁻¹ : kˣ) : k) * T (-n) * (z : k[T;T⁻¹] × k[T;T⁻¹]).1 =
        LaurentPolynomial.C ((c⁻¹ : kˣ) : k) * ((z : k[T;T⁻¹] × k[T;T⁻¹]).1 * T (-n)) by ring]
      exact Subalgebra.mul_mem _ (C_mem_inv _) hz1
    · change u'.2 * (z : k[T;T⁻¹] × k[T;T⁻¹]).2 ∈ invPolyPart k
      rw [hu'2, show LaurentPolynomial.C ((c'⁻¹ : kˣ) : k) * T (-m) * (z : k[T;T⁻¹] × k[T;T⁻¹]).2 =
        LaurentPolynomial.C ((c'⁻¹ : kˣ) : k) * ((z : k[T;T⁻¹] × k[T;T⁻¹]).2 * T (-m)) by ring]
      exact Subalgebra.mul_mem _ (C_mem_inv _) hz2
  have uu'z : ∀ z : k[T;T⁻¹] × k[T;T⁻¹], u * (u' * z) = z := fun z => by
    rw [← mul_assoc, show u * u' = 1 from Prod.ext huu'1 huu'2, one_mul]
  have u'uz : ∀ z : k[T;T⁻¹] × k[T;T⁻¹], u' * (u * z) = z := fun z => by
    rw [← mul_assoc, show u' * u = 1 from Prod.ext hunit1 hunit2, one_mul]

  let e1 : S.M1 ≃ₗ[k] ↥(gluedLinesM1 k a b μ0 n m) :=
    { toFun := fun y => ⟨u * (E1 y : k[T;T⁻¹] × k[T;T⁻¹]), mem_fwd (E1 y)⟩
      map_add' := fun y y' => Subtype.ext (by
        change u * ((E1 (y + y') : ↥(gluedLinesM1 k a b μ1 0 0)) : k[T;T⁻¹] × k[T;T⁻¹]) = u * _ + u * _
        rw [map_add, Submodule.coe_add, mul_add])
      map_smul' := fun d y => Subtype.ext (by
        change u * ((E1 (d • y) : ↥(gluedLinesM1 k a b μ1 0 0)) : k[T;T⁻¹] × k[T;T⁻¹]) =
          d • (u * ((E1 y : ↥(gluedLinesM1 k a b μ1 0 0)) : k[T;T⁻¹] × k[T;T⁻¹]))
        rw [map_smul, Submodule.coe_smul_of_tower, mul_smul_comm])
      invFun := fun z => E1.symm ⟨u' * (z : k[T;T⁻¹] × k[T;T⁻¹]), mem_bwd z⟩
      left_inv := fun y => by
        apply E1.injective
        rw [LinearEquiv.apply_symm_apply]
        exact Subtype.ext (u'uz _)
      right_inv := fun z => Subtype.ext (by
        change u * ((E1 (E1.symm _) : ↥(gluedLinesM1 k a b μ1 0 0)) : k[T;T⁻¹] × k[T;T⁻¹]) = z
        rw [LinearEquiv.apply_symm_apply]
        exact uu'z _) }

  have e01_ksmul : ∀ (d : k) (x : S.M01), e01L (d • x) = d • e01L x := fun d x => by
    apply Subtype.ext
    rw [← algebraMap_smul 𝒰.A01 d x, e01_smul, AlgEquiv.commutes, Submodule.coe_smul_of_tower, Algebra.smul_def]
    rfl
  let e01K : S.M01 ≃ₗ[k] ↥(gluedLinesM01 k a b μ0) :=
    LinearEquiv.ofBijective
      { toFun := e01L, map_add' := fun x y => map_add e01L x y, map_smul' := fun d x => e01_ksmul d x } e01_bij
  refine ⟨n, m, μ0, E0, e1, e01K, fun t => Subtype.ext (e01_r0 t), fun y => Subtype.ext ?_⟩
  change (e01L (S.r1 y) : k[T;T⁻¹] × k[T;T⁻¹]) = u * ((E1 y : ↥(gluedLinesM1 k a b μ1 0 0)) : k[T;T⁻¹] × k[T;T⁻¹])
  have hfin := hu ⟨(E1 y).1, (E1 y).2.1⟩
  rw [Ψ_N1, LinearEquiv.symm_apply_apply] at hfin
  exact hfin

end S_TwoChartCech_exists_linearEquiv_gluedLinesSections_of_invertible
end P2MW
export P2MW.S_TwoChartCech_exists_linearEquiv_gluedLinesSections_of_invertible (solution)
