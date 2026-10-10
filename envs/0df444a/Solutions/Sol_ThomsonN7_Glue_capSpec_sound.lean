-- Prove2me | solution 1 for ThomsonN7.Glue.capSpec_sound
-- status  : ACCEPTED   (prove)
-- author  : @Lucas
-- created : 2026-10-10T02:08:39.579452+00:00
-- url     : https://prove2.me/submissions/00c7f578-3555-4ab1-abf5-e60e081d0c2b

import Mathlib
import Definitions.Def_ThomsonN7_core
import Theorems.Thm_ThomsonN7_Reg_hessian_lower
import Theorems.Thm_ThomsonN7_Reg_energy_ge_cubic
import Theorems.Thm_ThomsonN7_Reg_sum_Dpair_lower
import Theorems.Thm_ThomsonN7_Glue_tubeRigid_of_le

/-!
# Thomson problem for N = 7 (and the D3h stretch target for N = 9)

Minimise the Coulomb energy `E(x) = ∑_{i<j} 1 / ‖x i - x j‖` over configurations of `N` pairwise
distinct points on the unit sphere `S² ⊂ ℝ³`.

* `N = 7`: the unique minimiser (up to `O(3)` and relabelling) is the regular pentagonal bipyramid,
  with `E = 1/2 + 5√2 + 5/(2 sin(π/5)) + 5/(2 sin(2π/5)) = 14.452977414…`.
* `N = 9`: the (numerically known) minimiser is the D3h tricapped trigonal prism, which has one free
  parameter `z` (the height of the two triangular faces); numerically `z ≈ 0.70365`,
  `E ≈ 25.759986531`.
-/

open Real

namespace ThomsonN7

/-! ## Auxiliary facts (already proved; they show the definitions are well-posed) -/

lemma norm_sq_cyl_sub (ρ θ h ρ' θ' h' : ℝ) :
    ‖cyl ρ θ h - cyl ρ' θ' h'‖ ^ 2 = ρ ^ 2 + ρ' ^ 2 - 2 * ρ * ρ' * cos (θ - θ') + (h - h') ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  simp [cyl, Fin.sum_univ_three, cos_sub]
  nlinarith [sin_sq_add_cos_sq θ, sin_sq_add_cos_sq θ']

lemma norm_sq_cyl (ρ θ h : ℝ) : ‖cyl ρ θ h‖ ^ 2 = ρ ^ 2 + h ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  simp [cyl, Fin.sum_univ_three, mul_pow]
  nlinarith [sin_sq_add_cos_sq θ]

lemma int_eq_zero_of_cos_eq_one (m : ℕ) (hm : 0 < m) (d : ℤ) (hd : |d| < m)
    (h : cos (2 * π * d / m) = 1) : d = 0 := by
  obtain ⟨n, hn⟩ := (Real.cos_eq_one_iff _).1 h
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have h1 : (n : ℝ) * m = d := by
    field_simp at hn
    nlinarith [Real.pi_pos]
  have h2 : n * (m : ℤ) = d := by exact_mod_cast h1
  have hm2 : (0 : ℤ) < m := by exact_mod_cast hm
  rw [abs_lt] at hd
  rcases lt_trichotomy n 0 with hn0 | hn0 | hn0
  · nlinarith
  · subst hn0; simpa using h2.symm
  · nlinarith

lemma cos_sub_eq_one_of_cyl_eq {ρ θ θ' h : ℝ} (hρ : 0 < ρ)
    (H : cyl ρ θ h = cyl ρ θ' h) : cos (θ - θ') = 1 := by
  have := norm_sq_cyl_sub ρ θ h ρ θ' h
  rw [H, sub_self, norm_zero] at this
  have hρ2 : 0 < ρ ^ 2 := by positivity
  nlinarith

lemma pent_angle_inj {i j : ℕ} (hi : i < 5) (hj : j < 5)
    (H : cos (2 * π * (i : ℕ) / 5 - 2 * π * (j : ℕ) / 5) = 1) : i = j := by
  have := int_eq_zero_of_cos_eq_one 5 (by norm_num) ((i : ℤ) - j) (by rw [abs_lt]; constructor <;> omega)
    (by convert H using 2; push_cast; ring)
  omega

lemma pent_of_lt {i : Fin 7} (hi : (i : ℕ) < 5) :
    pentBipyramid i = cyl 1 (2 * π * (i : ℕ) / 5) 0 := by
  simp [pentBipyramid, hi]

lemma pent_five : pentBipyramid 5 = cyl 0 0 1 := by simp [pentBipyramid]
lemma pent_six : pentBipyramid 6 = cyl 0 0 (-1) := by simp [pentBipyramid]

lemma pent_cases (i : Fin 7) : (i : ℕ) < 5 ∨ i = 5 ∨ i = 6 := by
  fin_cases i <;> simp

theorem pentBipyramid_injective : Function.Injective pentBipyramid := by
  intro i j hij
  have h2 := congrArg (fun v : R3 => v 2) hij
  rcases pent_cases i with hi | rfl | rfl <;> rcases pent_cases j with hj | rfl | rfl
  · rw [pent_of_lt hi, pent_of_lt hj] at hij
    exact Fin.ext (pent_angle_inj hi hj (cos_sub_eq_one_of_cyl_eq one_pos hij))
  · simp [pent_of_lt hi, pent_five, cyl] at h2
  · simp [pent_of_lt hi, pent_six, cyl] at h2
  · simp [pent_of_lt hj, pent_five, cyl] at h2
  · rfl
  · simp [pent_five, pent_six, cyl] at h2; norm_num at h2
  · simp [pent_of_lt hj, pent_six, cyl] at h2
  · simp [pent_five, pent_six, cyl] at h2; norm_num at h2
  · rfl

/-- The pentagonal bipyramid is an admissible configuration. -/
theorem pentBipyramid_mem : pentBipyramid ∈ SphereConfig 7 := by
  refine ⟨fun i => ?_, pentBipyramid_injective⟩
  have : ‖pentBipyramid i‖ ^ 2 = 1 := by
    rcases pent_cases i with hi | rfl | rfl
    · rw [pent_of_lt hi, norm_sq_cyl]; norm_num
    · rw [pent_five, norm_sq_cyl]; norm_num
    · rw [pent_six, norm_sq_cyl]; norm_num
  nlinarith [norm_nonneg (pentBipyramid i)]

/- BEGIN M0 -/
namespace Base

open Finset

lemma norm_sub_sq_of_unit {x y : R3} (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) :
    ‖x - y‖ ^ 2 = 2 - 2 * inner ℝ x y := by
  rw [norm_sub_sq_real, hx, hy]; ring

lemma norm_sub_inv_eq_phi {x y : R3} (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) :
    ‖x - y‖⁻¹ = phi (inner ℝ x y) := by
  unfold phi
  rw [← norm_sub_sq_of_unit hx hy, Real.sqrt_sq (norm_nonneg _)]

lemma neg_one_le_inner_of_unit {x y : R3} (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) :
    -1 ≤ inner ℝ x y := by
  have := abs_real_inner_le_norm x y
  rw [hx, hy, mul_one] at this
  exact (abs_le.1 this).1

lemma inner_lt_one_of_ne {x y : R3} (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) (hne : x ≠ y) :
    inner ℝ x y < 1 := by
  have h := norm_sub_sq_of_unit hx hy
  have : 0 < ‖x - y‖ := norm_pos_iff.2 (sub_ne_zero.2 hne)
  nlinarith

/-- For unit vectors the energy is a sum of `phi` of the pairwise inner products. -/
lemma coulombEnergy_eq_sum_phi {n : ℕ} {x : Fin n → R3} (hx : ∀ i, ‖x i‖ = 1) :
    coulombEnergy x = ∑ i, ∑ j ∈ Finset.Ioi i, phi (inner ℝ (x i) (x j)) := by
  unfold coulombEnergy
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
    norm_sub_inv_eq_phi (hx i) (hx j)

/-! ### Invariance -/

lemma coulombEnergy_comp_isometry {n : ℕ} (g : R3 ≃ₗᵢ[ℝ] R3) (x : Fin n → R3) :
    coulombEnergy (fun i => g (x i)) = coulombEnergy x := by
  unfold coulombEnergy
  simp only [← map_sub, LinearIsometryEquiv.norm_map]

lemma two_mul_sum_Ioi {n : ℕ} (F : Fin n → Fin n → ℝ) (hF : ∀ i j, F i j = F j i) :
    2 * ∑ i, ∑ j ∈ Finset.Ioi i, F i j = ∑ i, ∑ j, if i = j then 0 else F i j := by
  have h1 : ∀ i : Fin n, ∑ j ∈ Finset.Ioi i, F i j = ∑ j, if i < j then F i j else 0 := by
    intro i
    rw [← Finset.sum_filter]
    congr 1
    ext j; simp
  have h2 : ∀ i j : Fin n, (if i = j then 0 else F i j) =
      (if i < j then F i j else 0) + (if j < i then F j i else 0) := by
    intro i j
    rcases lt_trichotomy i j with h | h | h
    · simp [h, h.ne, not_lt_of_gt h]
    · simp [h]
    · simp [h, h.ne', not_lt_of_gt h, hF i j]
  simp only [h1, h2, Finset.sum_add_distrib]
  rw [Finset.sum_comm (f := fun i j => if j < i then F j i else 0)]
  ring

lemma coulombEnergy_comp_perm {n : ℕ} (σ : Equiv.Perm (Fin n)) (x : Fin n → R3) :
    coulombEnergy (fun i => x (σ i)) = coulombEnergy x := by
  have key : ∀ y : Fin n → R3, 2 * coulombEnergy y =
      ∑ i, ∑ j, if i = j then 0 else ‖y i - y j‖⁻¹ := by
    intro y
    exact two_mul_sum_Ioi (fun i j => ‖y i - y j‖⁻¹) (fun i j => by rw [norm_sub_rev])
  have h := key (fun i => x (σ i))
  have h' := key x
  have : 2 * coulombEnergy (fun i => x (σ i)) = 2 * coulombEnergy x := by
    rw [h, h']
    calc ∑ i, ∑ j, (if i = j then (0 : ℝ) else ‖x (σ i) - x (σ j)‖⁻¹)
        = ∑ i, ∑ j, (if σ i = σ j then (0 : ℝ) else ‖x (σ i) - x (σ j)‖⁻¹) := by
          simp only [σ.apply_eq_iff_eq]
      _ = ∑ i, ∑ j, (if σ i = j then (0 : ℝ) else ‖x (σ i) - x j‖⁻¹) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          exact Equiv.sum_comp σ (fun j => if σ i = j then (0 : ℝ) else ‖x (σ i) - x j‖⁻¹)
      _ = ∑ i, ∑ j, (if i = j then (0 : ℝ) else ‖x i - x j‖⁻¹) :=
          Equiv.sum_comp σ (fun i => ∑ j, if i = j then (0 : ℝ) else ‖x i - x j‖⁻¹)
  linarith

lemma sphereConfig_comp {n : ℕ} (g : R3 ≃ₗᵢ[ℝ] R3) (σ : Equiv.Perm (Fin n)) {x : Fin n → R3}
    (hx : x ∈ SphereConfig n) : (fun i => g (x (σ i))) ∈ SphereConfig n := by
  refine ⟨fun i => ?_, ?_⟩
  · rw [LinearIsometryEquiv.norm_map]; exact hx.1 _
  · intro i j hij
    exact σ.injective (hx.2 (g.injective hij))

/-! ### Gram values of the pentagonal bipyramid -/

lemma cos_2pi5 : cos (2 * π / 5) = c1 := by
  have hs : √5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have h : cos (2 * π / 5) = 2 * cos (π / 5) ^ 2 - 1 := by
    rw [← cos_two_mul]; congr 1; ring
  rw [h, cos_pi_div_five]; unfold c1
  linear_combination (1 / 8) * hs

lemma pent_norm (i : Fin 7) : ‖pentBipyramid i‖ = 1 := pentBipyramid_mem.1 i

end Base
/- END M0 -/

/- BEGIN M1 -/
namespace ThreePoint

open Finset Matrix
open scoped RealInnerProductSpace

/-! # Bachoc–Vallentin three-point positivity on `S²` (any block size, any `k`)

`Q3 k u v t = ((1-u²)(1-v²))^{k/2} T_k((t-uv)/√((1-u²)(1-v²)))` via the Chebyshev recursion.
-/

/-! ### Addition theorem (de Moivre) -/

/-! ### Combinatorics of ordered triple sums -/

section Comb

variable {n : ℕ}

end Comb

section Comb2

variable {n : ℕ}

end Comb2

section Comb3

variable {n : ℕ}

end Comb3

section Comb4

variable {n : ℕ}

end Comb4

section Final

variable {n : ℕ}

end Final

/-! ### The kernels at the diagonal `(1,1,1)` -/

section FinalZ

variable {n : ℕ}

end FinalZ

/- BEGIN M5 -/
section Critical

end Critical

section Critical

end Critical

section Critical

end Critical

section CriticalZ

variable {n : ℕ}

end CriticalZ

section CriticalZsym

variable {n : ℕ}

section Perm

variable (τ : Fin n → Fin n → ℝ) (hτ : ∀ i j, τ j i = τ i j) (f : ℝ → ℝ → ℝ → ℝ)

include hτ

end Perm

end CriticalZsym

section CriticalFinal

variable {n : ℕ}

end CriticalFinal

/- END M5 -/

end ThreePoint

/- BEGIN CERT3 -/

/-!
# Kronecker-substitution checking of polynomial identities

A polynomial `e : Ex` in three variables `u, v, t` with integer coefficients is given as an
expression tree.  To prove `∀ u v t : ℝ, e(u,v,t) = 0` it suffices to check, with kernel
(GMP) integer arithmetic, that
* every exponent of every variable is `< D`,
* the `ℓ¹`-norm of the (uncollected) coefficients is `< 2^w`,
* the value of `e` at the integers `u = 2^w`, `v = 2^(w D)`, `t = 2^(w D²)` is `0`.
-/

namespace Kron

namespace Ex

end Ex

namespace Ex

end Ex

open Ex

end Kron

/-! ## Builders for `Ex` with evaluation lemmas -/

namespace Kron
namespace Ex

variable (u v t : ℝ)

/-! ### Substitution of variables by variables or `1` -/

end Ex
end Kron

/- BEGIN CERT1 -/
section Cert1Block

open Kron Kron.Ex

namespace Cert

open ThreePoint

/-! ## `Q_k` as a polynomial expression -/

/-! ## Quadratic forms: `L D Lᵀ` plus a diagonally dominant remainder -/

/-! ## Integer data of a positive semidefinite block -/

namespace Blk

end Blk

end Cert

end Cert1Block

/- BEGIN CERT3FILE -/
section Cert3Block

open Kron Kron.Ex

namespace Cert

open ThreePoint

/-! ## Helpers: zero-skipping scaling, monomial-preserving substitution -/

/-! ## The `F`-blocks: `Λ · Fp(u,v)` -/

/-! ## Block matrices and their quadratic forms -/

/-! ## Symmetrisation and the `F`-part of the identity -/

/-! ## SOS blocks with multipliers -/

/-! ## The certificate and its soundness -/

open scoped RealInnerProductSpace

namespace Cert3

end Cert3

namespace Cert3

end Cert3

namespace Cert3

end Cert3

end Cert

end Cert3Block

/- END CERT3 -/

/- BEGIN M2 -/
namespace M2

/-! ## The number field `ℚ(√2, 2 sin (π/5))` -/

namespace K8

/-! ### Rational enclosures and positivity of elements of `K8` -/

end K8

namespace K8

end K8

/-! ### Polynomials with `K8` coefficients: dense lists, lowest degree first -/

namespace Pl

end Pl

open Pl

end M2
/- END M2 -/

/- BEGIN M3 -/
namespace M3

open scoped InnerProductSpace

end M3

/- BEGIN P3ext -/

/-! ## P3: Bregman (Taylor) lower bounds for the Coulomb pair potential (agent7) -/

namespace Base

end Base

/- END P3ext -/

/- BEGIN P1 -/

/-! ## P1: the bipyramid is a critical point of the Coulomb energy on the constraint set (agent7) -/

namespace Reg

open Base

end Reg

/- END P1 -/

/- BEGIN GAUGE -/

/-! ## G: gauge (Procrustes) lemma `exists_gauge` (agent7) -/

namespace Reg

open scoped RealInnerProductSpace

lemma planeRot_apply (u v : R3) (c s : ℝ) (w : R3) :
    planeRot u v c s w = w + ((c - 1) * ⟪u, w⟫ - s * ⟪v, w⟫) • u
      + ((c - 1) * ⟪v, w⟫ + s * ⟪u, w⟫) • v := by
  simp [planeRot]
  module

lemma norm_planeRot (u v : R3) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : ⟪u, v⟫ = 0) (c s : ℝ)
    (hcs : c ^ 2 + s ^ 2 = 1) (w : R3) : ‖planeRot u v c s w‖ = ‖w‖ := by
  rw [planeRot_apply]
  set p := (c - 1) * ⟪u, w⟫ - s * ⟪v, w⟫ with hp
  set q := (c - 1) * ⟪v, w⟫ + s * ⟪u, w⟫ with hq
  have hvu : ⟪v, u⟫ = 0 := by rw [real_inner_comm]; exact huv
  have hu2 : ⟪u, u⟫ = 1 := by rw [real_inner_self_eq_norm_sq, hu]; norm_num
  have hv2 : ⟪v, v⟫ = 1 := by rw [real_inner_self_eq_norm_sq, hv]; norm_num
  have h1 : ‖w + p • u + q • v‖ ^ 2 = ‖w‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq]
    simp only [inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right,
      hu2, hv2, huv, hvu]
    rw [real_inner_comm u w, real_inner_comm v w]
    have h2 : p ^ 2 + q ^ 2 = ((c - 1) ^ 2 + s ^ 2) * (⟪u, w⟫ ^ 2 + ⟪v, w⟫ ^ 2) := by
      rw [hp, hq]; ring
    have h3 : p * ⟪u, w⟫ + q * ⟪v, w⟫ = (c - 1) * (⟪u, w⟫ ^ 2 + ⟪v, w⟫ ^ 2) := by
      rw [hp, hq]; ring
    nlinarith [h2, h3]
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 h1

lemma isoSet_isClosed : IsClosed IsoSet := by
  have : IsoSet = ⋂ x : R3, {A : R3 →L[ℝ] R3 | ‖A x‖ = ‖x‖} := by
    ext A; simp [IsoSet]
  rw [this]
  refine isClosed_iInter fun x => ?_
  exact isClosed_eq ((ContinuousLinearMap.apply ℝ R3 x).continuous.norm) continuous_const

lemma isoSet_isBounded : Bornology.IsBounded IsoSet := by
  refine (Metric.isBounded_iff_subset_closedBall 0).2 ⟨1, fun A hA => ?_⟩
  rw [mem_closedBall_zero_iff]
  exact A.opNorm_le_bound zero_le_one fun x => by simp [hA x]

lemma isoSet_isCompact : IsCompact IsoSet :=
  Metric.isCompact_of_isClosed_isBounded isoSet_isClosed isoSet_isBounded

lemma id_mem_isoSet : ContinuousLinearMap.id ℝ R3 ∈ IsoSet := fun _ => rfl

lemma procScore_continuous {n : ℕ} (P y : Fin n → R3) : Continuous (procScore P y) := by
  unfold procScore
  refine continuous_finsetSum _ fun i _ => ?_
  exact continuous_const.inner (ContinuousLinearMap.apply ℝ R3 (y i)).continuous

lemma exists_max_score {n : ℕ} (P y : Fin n → R3) :
    ∃ A ∈ IsoSet, ∀ B ∈ IsoSet, procScore P y B ≤ procScore P y A := by
  obtain ⟨A, hA, hmax⟩ := isoSet_isCompact.exists_isMaxOn ⟨_, id_mem_isoSet⟩
    (procScore_continuous P y).continuousOn
  exact ⟨A, hA, fun B hB => hmax hB⟩

/-- If `t β ≤ t² α` for all `t` then `β = 0`. -/
lemma eq_zero_of_mul_le_sq_mul {α β : ℝ} (h : ∀ t : ℝ, t * β ≤ t ^ 2 * α) : β = 0 := by
  set d := 1 + |α| with hd
  have hd0 : 0 < d := by positivity
  set t := β / d with ht
  have htd : t * d = β := by rw [ht]; field_simp
  have h1 := h t
  rw [← htd] at h1
  have h2 : t ^ 2 * (d - α) ≤ 0 := by nlinarith
  have h3 : 1 ≤ d - α := by have := le_abs_self α; linarith
  have h4 : t ^ 2 ≤ 0 := by nlinarith [sq_nonneg t]
  have h5 : t = 0 := by nlinarith [sq_nonneg t]
  rw [← htd, h5, zero_mul]

lemma comp_planeRot_mem {A : R3 →L[ℝ] R3} (hA : A ∈ IsoSet) (u v : R3) (hu : ‖u‖ = 1)
    (hv : ‖v‖ = 1) (huv : ⟪u, v⟫ = 0) (c s : ℝ) (hcs : c ^ 2 + s ^ 2 = 1) :
    (planeRot u v c s).comp A ∈ IsoSet := fun x => by
  rw [ContinuousLinearMap.comp_apply, norm_planeRot u v hu hv huv c s hcs, hA x]

/-- First-order condition of the Procrustes maximiser: for every orthonormal pair `u, v`,
`∑ᵢ (⟪u, A yᵢ⟫ ⟪Pᵢ, v⟫ - ⟪v, A yᵢ⟫ ⟪Pᵢ, u⟫) = 0`. -/
lemma max_score_stationary {n : ℕ} (P y : Fin n → R3) {A : R3 →L[ℝ] R3} (hA : A ∈ IsoSet)
    (hmax : ∀ B ∈ IsoSet, procScore P y B ≤ procScore P y A) (u v : R3) (hu : ‖u‖ = 1)
    (hv : ‖v‖ = 1) (huv : ⟪u, v⟫ = 0) :
    ∑ i, (⟪u, A (y i)⟫ * ⟪P i, v⟫ - ⟪v, A (y i)⟫ * ⟪P i, u⟫) = 0 := by
  set α := ∑ i, (⟪u, A (y i)⟫ * ⟪P i, u⟫ + ⟪v, A (y i)⟫ * ⟪P i, v⟫) with hα
  set β := ∑ i, (⟪u, A (y i)⟫ * ⟪P i, v⟫ - ⟪v, A (y i)⟫ * ⟪P i, u⟫) with hβ
  refine eq_zero_of_mul_le_sq_mul (α := α) fun t => ?_
  have hd : 0 < 1 + t ^ 2 := by positivity
  set c := (1 - t ^ 2) / (1 + t ^ 2) with hc
  set s := 2 * t / (1 + t ^ 2) with hs
  have hcs : c ^ 2 + s ^ 2 = 1 := by
    rw [hc, hs]; field_simp; ring
  have h1 := hmax _ (comp_planeRot_mem hA u v hu hv huv c s hcs)
  have h2 : procScore P y ((planeRot u v c s).comp A) = procScore P y A + (c - 1) * α + s * β := by
    unfold procScore
    simp only [ContinuousLinearMap.comp_apply, planeRot_apply, inner_add_right, real_inner_smul_right,
      hα, hβ, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  rw [h2] at h1
  have h3 : (c - 1) * α + s * β ≤ 0 := by linarith
  have h4 : c - 1 = -(2 * t ^ 2) / (1 + t ^ 2) := by rw [hc]; field_simp; ring
  rw [h4, hs] at h3
  have h5 : (-(2 * t ^ 2) / (1 + t ^ 2)) * α + (2 * t / (1 + t ^ 2)) * β
      = 2 / (1 + t ^ 2) * (t * β - t ^ 2 * α) := by ring
  rw [h5] at h3
  have h6 : 0 < 2 / (1 + t ^ 2) := by positivity
  nlinarith

lemma isoOfMem_apply (A : R3 →L[ℝ] R3) (hA : A ∈ IsoSet) (x : R3) : isoOfMem A hA x = A x := rfl

/-- **Gauge (Procrustes) lemma.**  For any two `n`-tuples `P, y` of points of `ℝ³` there is a
linear isometry `g` of `ℝ³` such that the `3 × 3` matrix `∑ᵢ Pᵢ ⊗ g(yᵢ)` is symmetric, and `g y` is
no farther from `P` (in the sum of squared distances) than `y` itself. -/
theorem exists_gauge {n : ℕ} (P y : Fin n → R3) :
    ∃ g : R3 ≃ₗᵢ[ℝ] R3,
      (∀ a b : Fin 3, ∑ i, P i a * g (y i) b = ∑ i, P i b * g (y i) a) ∧
      ∑ i, ‖g (y i) - P i‖ ^ 2 ≤ ∑ i, ‖y i - P i‖ ^ 2 := by
  obtain ⟨A, hA, hmax⟩ := exists_max_score P y
  refine ⟨isoOfMem A hA, fun a b => ?_, ?_⟩
  · by_cases hab : a = b
    · rw [hab]
    · have h := max_score_stationary P y hA hmax (EuclideanSpace.single a 1)
        (EuclideanSpace.single b 1) (by simp) (by simp) (by simp [EuclideanSpace.inner_single_left, hab])
      simp only [EuclideanSpace.inner_single_left, EuclideanSpace.inner_single_right,
        RCLike.conj_to_real, one_mul] at h
      simp only [isoOfMem_apply]
      rw [Finset.sum_sub_distrib] at h
      have e1 : ∑ i, P i a * A (y i) b = ∑ i, A (y i) b * P i a :=
        Finset.sum_congr rfl fun i _ => mul_comm _ _
      have e2 : ∑ i, P i b * A (y i) a = ∑ i, A (y i) a * P i b :=
        Finset.sum_congr rfl fun i _ => mul_comm _ _
      rw [e1, e2]
      linarith [h]
  · have hid := hmax (ContinuousLinearMap.id ℝ R3) id_mem_isoSet
    unfold procScore at hid
    simp only [ContinuousLinearMap.id_apply] at hid
    have key : ∀ (B : R3 →L[ℝ] R3), B ∈ IsoSet →
        ∑ i, ‖B (y i) - P i‖ ^ 2 = ∑ i, (‖y i‖ ^ 2 + ‖P i‖ ^ 2) - 2 * procScore P y B := by
      intro B hB
      unfold procScore
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [norm_sub_sq_real, hB (y i), real_inner_comm]
      ring
    have k1 := key A hA
    have k2 := key (ContinuousLinearMap.id ℝ R3) id_mem_isoSet
    simp only [isoOfMem_apply]
    simp only [ContinuousLinearMap.id_apply] at k2
    unfold procScore at k1 k2
    simp only [ContinuousLinearMap.id_apply] at k2
    linarith

end Reg

/- END GAUGE -/

/- BEGIN P2 -/

/- BEGIN RegB (P2: exact energy identity; needs M0 = namespace Base and the Challenge preamble) -/
namespace RegB

open Base Finset

section vectors

variable (y : Fin 7 → R3)

end vectors

end RegB
/- END RegB -/

/- END P2 -/

/- BEGIN GV -/

namespace GV

open Base

lemma inner_coord (x y : R3) : inner ℝ x y = x 0 * y 0 + x 1 * y 1 + x 2 * y 2 := by
  simp [PiLp.inner_apply, Fin.sum_univ_three]
  ring

lemma norm_sq_coord (x : R3) : ‖x‖ ^ 2 = x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  simp [Fin.sum_univ_three]

lemma pent0 : pentBipyramid 0 = !₂[1, 0, 0] := by
  simp [pentBipyramid, cyl]

lemma pent1 : pentBipyramid 1 = !₂[cos (2 * π / 5), sin (2 * π / 5), 0] := by
  simp [pentBipyramid, cyl]

lemma pent5' : pentBipyramid 5 = !₂[0, 0, 1] := by
  simp [pentBipyramid, cyl]

lemma abs_le_one_of_sq_add {a b c : ℝ} (h : a ^ 2 + b ^ 2 + c ^ 2 = 1) : |a| ≤ 1 := by
  rw [abs_le]
  constructor <;> nlinarith [sq_nonneg a, sq_nonneg b, sq_nonneg c]

lemma s1_bounds {c1 s1 : ℝ} (hc1 : 309 / 1000 ≤ c1) (hc1' : c1 ≤ 31 / 100)
    (hs1 : s1 ^ 2 = 1 - c1 ^ 2) (hs1p : 0 < s1) : 95 / 100 ≤ s1 ∧ s1 ≤ 952 / 1000 := by
  constructor <;> nlinarith

lemma L22_bounds {c1 g01 L22 w : ℝ} (hw0 : 0 ≤ w) (hw : w ≤ 1 / 10)
    (hc1 : 309 / 1000 ≤ c1) (hc1' : c1 ≤ 31 / 100) (hg01 : |g01 - c1| ≤ w)
    (hL22p : 0 < L22) (hL22 : L22 ^ 2 = 1 - g01 ^ 2) : 9 / 10 ≤ L22 ∧ L22 ≤ 1 := by
  obtain ⟨g01l, g01u⟩ := abs_le.1 hg01
  constructor <;> nlinarith

lemma L32_bound {g01 g05 g15 L22 L32 w : ℝ} (hw0 : 0 ≤ w)
    (hg01l : 209 / 1000 ≤ g01) (hg01u : g01 ≤ 41 / 100)
    (hg05 : |g05| ≤ w) (hg15 : |g15| ≤ w)
    (hL22a : 9 / 10 ≤ L22) (hL32 : L32 * L22 = g15 - g01 * g05) : |L32| ≤ 157 / 100 * w := by
  obtain ⟨g05l, g05u⟩ := abs_le.1 hg05
  obtain ⟨g15l, g15u⟩ := abs_le.1 hg15
  have h1 : |L32| * L22 ≤ 141 / 100 * w := by
    have : |L32 * L22| = |L32| * L22 := by rw [abs_mul, abs_of_pos (by linarith : 0 < L22)]
    rw [← this, hL32, abs_le]
    constructor <;> nlinarith
  nlinarith [abs_nonneg L32]

lemma L33_bounds {g05 L32 L33 w : ℝ} (hw0 : 0 ≤ w) (hw : w ≤ 1 / 10)
    (hg05 : |g05| ≤ w) (hL32 : |L32| ≤ 157 / 100 * w)
    (hL33p : 0 < L33) (hL33 : L33 ^ 2 = 1 - g05 ^ 2 - L32 ^ 2) :
    98 / 100 ≤ L33 ∧ L33 ≤ 1 ∧ 1 - L33 ≤ 175 / 1000 * w := by
  obtain ⟨g05l, g05u⟩ := abs_le.1 hg05
  obtain ⟨l32l, l32u⟩ := abs_le.1 hL32
  have hg2 : g05 ^ 2 ≤ w ^ 2 := by nlinarith
  have hl2 : L32 ^ 2 ≤ (157 / 100 * w) ^ 2 := by nlinarith
  have h1 : L33 ≤ 1 := by nlinarith [sq_nonneg g05, sq_nonneg L32]
  have h2 : 98 / 100 ≤ L33 := by nlinarith
  refine ⟨h2, h1, ?_⟩
  nlinarith

lemma L22_s1_close {c1 s1 g01 L22 w : ℝ} (hw0 : 0 ≤ w)
    (hc1 : 309 / 1000 ≤ c1) (hc1' : c1 ≤ 31 / 100) (hs1a : 95 / 100 ≤ s1)
    (hg01 : |g01 - c1| ≤ w) (hg01l : 209 / 1000 ≤ g01) (hg01u : g01 ≤ 41 / 100)
    (hL22a : 9 / 10 ≤ L22) (hs1 : s1 ^ 2 = 1 - c1 ^ 2) (hL22 : L22 ^ 2 = 1 - g01 ^ 2) :
    |L22 - s1| ≤ 4 / 10 * w := by
  obtain ⟨g01l', g01u'⟩ := abs_le.1 hg01
  have key : (L22 - s1) * (L22 + s1) = (c1 - g01) * (c1 + g01) := by nlinarith
  have hpos : 0 < L22 + s1 := by linarith
  have h2 : |L22 - s1| * (L22 + s1) = |c1 - g01| * |c1 + g01| := by
    rw [← abs_of_pos hpos, ← abs_mul, key, abs_mul]
  have h3 : |c1 - g01| ≤ w := by rw [abs_sub_comm]; exact hg01
  have h4 : |c1 + g01| ≤ 72 / 100 := by
    rw [abs_le]; constructor <;> linarith
  have h5 : |c1 - g01| * |c1 + g01| ≤ 72 / 100 * w := by
    calc |c1 - g01| * |c1 + g01| ≤ w * (72 / 100) :=
          mul_le_mul h3 h4 (abs_nonneg _) hw0
      _ = 72 / 100 * w := by ring
  nlinarith [abs_nonneg (L22 - s1)]

lemma abs_mul_le' {x y p q : ℝ} (hx : |x| ≤ p) (hy : |y| ≤ q) : |x * y| ≤ p * q := by
  rw [abs_mul]
  exact mul_le_mul hx hy (abs_nonneg _) ((abs_nonneg _).trans hx)

lemma db_bound {c1 s1 g01 L22 a b a0 b0 w : ℝ} (hw0 : 0 ≤ w)
    (hg01 : |g01 - c1| ≤ w) (hg01l : 209 / 1000 ≤ g01) (hg01u : g01 ≤ 41 / 100)
    (hL22a : 9 / 10 ≤ L22) (hLs : |L22 - s1| ≤ 4 / 10 * w)
    (ha0 : |a0| ≤ 1) (hb0 : |b0| ≤ 1) (e0 : |a - a0| ≤ w)
    (e1 : |(g01 * a + L22 * b) - (c1 * a0 + s1 * b0)| ≤ w) : |b - b0| ≤ 32 / 10 * w := by
  have key : L22 * (b - b0) = ((g01 * a + L22 * b) - (c1 * a0 + s1 * b0))
      - g01 * (a - a0) - (g01 - c1) * a0 + (s1 - L22) * b0 := by ring
  have hg : |g01| ≤ 41 / 100 := abs_le.2 ⟨by linarith, hg01u⟩
  have t2 : |g01 * (a - a0)| ≤ 41 / 100 * w := abs_mul_le' hg e0
  have t3 : |(g01 - c1) * a0| ≤ w * 1 := abs_mul_le' hg01 ha0
  have hLs' : |s1 - L22| ≤ 4 / 10 * w := by rw [abs_sub_comm]; exact hLs
  have t4 : |(s1 - L22) * b0| ≤ 4 / 10 * w * 1 := abs_mul_le' hLs' hb0
  obtain ⟨t1l, t1u⟩ := abs_le.1 e1
  obtain ⟨t2l, t2u⟩ := abs_le.1 t2
  obtain ⟨t3l, t3u⟩ := abs_le.1 t3
  obtain ⟨t4l, t4u⟩ := abs_le.1 t4
  have h1 : |L22 * (b - b0)| ≤ 281 / 100 * w := by
    rw [abs_le]; constructor <;> nlinarith
  rw [abs_mul, abs_of_pos (by linarith : 0 < L22)] at h1
  nlinarith [abs_nonneg (b - b0)]

lemma dc_bound {g05 L32 L33 a b c c0 w : ℝ} (hw0 : 0 ≤ w)
    (hg05 : |g05| ≤ w) (hL32 : |L32| ≤ 157 / 100 * w)
    (hL33a : 98 / 100 ≤ L33) (hL33b : L33 ≤ 1) (hL33c : 1 - L33 ≤ 175 / 1000 * w)
    (ha : |a| ≤ 1) (hb : |b| ≤ 1) (hc0 : |c0| ≤ 1)
    (e5 : |(g05 * a + L32 * b + L33 * c) - c0| ≤ w) : |c - c0| ≤ 39 / 10 * w := by
  have key : L33 * (c - c0) = ((g05 * a + L32 * b + L33 * c) - c0)
      + (1 - L33) * c0 - g05 * a - L32 * b := by ring
  have h1L : |1 - L33| ≤ 175 / 1000 * w := abs_le.2 ⟨by linarith, hL33c⟩
  have t2 : |(1 - L33) * c0| ≤ 175 / 1000 * w * 1 := abs_mul_le' h1L hc0
  have t3 : |g05 * a| ≤ w * 1 := abs_mul_le' hg05 ha
  have t4 : |L32 * b| ≤ 157 / 100 * w * 1 := abs_mul_le' hL32 hb
  obtain ⟨t1l, t1u⟩ := abs_le.1 e5
  obtain ⟨t2l, t2u⟩ := abs_le.1 t2
  obtain ⟨t3l, t3u⟩ := abs_le.1 t3
  obtain ⟨t4l, t4u⟩ := abs_le.1 t4
  have h1 : |L33 * (c - c0)| ≤ 375 / 100 * w := by
    rw [abs_le]; constructor <;> nlinarith
  rw [abs_mul, abs_of_pos (by linarith : 0 < L33)] at h1
  nlinarith [abs_nonneg (c - c0)]

lemma core_bound {c1 s1 g01 g05 g15 L22 L32 L33 a b c a0 b0 c0 w : ℝ}
    (hw0 : 0 ≤ w) (hw : w ≤ 1 / 10)
    (hc1 : 309 / 1000 ≤ c1) (hc1' : c1 ≤ 31 / 100) (hs1 : s1 ^ 2 = 1 - c1 ^ 2) (hs1p : 0 < s1)
    (hg01 : |g01 - c1| ≤ w) (hg05 : |g05| ≤ w) (hg15 : |g15| ≤ w)
    (hL22p : 0 < L22) (hL22 : L22 ^ 2 = 1 - g01 ^ 2)
    (hL32 : L32 * L22 = g15 - g01 * g05)
    (hL33p : 0 < L33) (hL33 : L33 ^ 2 = 1 - g05 ^ 2 - L32 ^ 2)
    (hab : a ^ 2 + b ^ 2 + c ^ 2 = 1) (hab0 : a0 ^ 2 + b0 ^ 2 + c0 ^ 2 = 1)
    (e0 : |a - a0| ≤ w)
    (e1 : |(g01 * a + L22 * b) - (c1 * a0 + s1 * b0)| ≤ w)
    (e5 : |(g05 * a + L32 * b + L33 * c) - c0| ≤ w) :
    (a - a0) ^ 2 + (b - b0) ^ 2 + (c - c0) ^ 2 ≤ (11 / 2 * w) ^ 2 := by
  obtain ⟨hs1a, -⟩ := s1_bounds hc1 hc1' hs1 hs1p
  obtain ⟨hg01l', hg01u'⟩ := abs_le.1 hg01
  have hg01l : 209 / 1000 ≤ g01 := by linarith
  have hg01u : g01 ≤ 41 / 100 := by linarith
  obtain ⟨hL22a, -⟩ := L22_bounds hw0 hw hc1 hc1' hg01 hL22p hL22
  have hL32b := L32_bound hw0 hg01l hg01u hg05 hg15 hL22a hL32
  obtain ⟨hL33a, hL33b, hL33c⟩ := L33_bounds hw0 hw hg05 hL32b hL33p hL33
  have hLs := L22_s1_close hw0 hc1 hc1' hs1a hg01 hg01l hg01u hL22a hs1 hL22
  have ha : |a| ≤ 1 := abs_le_one_of_sq_add hab
  have hb : |b| ≤ 1 := abs_le_one_of_sq_add (by linarith : b ^ 2 + a ^ 2 + c ^ 2 = 1)
  have ha0 : |a0| ≤ 1 := abs_le_one_of_sq_add hab0
  have hb0 : |b0| ≤ 1 := abs_le_one_of_sq_add (by linarith : b0 ^ 2 + a0 ^ 2 + c0 ^ 2 = 1)
  have hc0 : |c0| ≤ 1 := abs_le_one_of_sq_add (by linarith : c0 ^ 2 + a0 ^ 2 + b0 ^ 2 = 1)
  have db := db_bound hw0 hg01 hg01l hg01u hL22a hLs ha0 hb0 e0 e1
  have dc := dc_bound hw0 hg05 hL32b hL33a hL33b hL33c ha hb hc0 e5
  have h1 : (a - a0) ^ 2 ≤ w ^ 2 := sq_le_sq' (abs_le.1 e0).1 (abs_le.1 e0).2
  have h2 : (b - b0) ^ 2 ≤ (32 / 10 * w) ^ 2 := sq_le_sq' (abs_le.1 db).1 (abs_le.1 db).2
  have h3 : (c - c0) ^ 2 ≤ (39 / 10 * w) ^ 2 := sq_le_sq' (abs_le.1 dc).1 (abs_le.1 dc).2
  nlinarith

open scoped InnerProductSpace

lemma inner_cols (a b c d e f : ℝ) :
    inner ℝ (!₂[a, b, c] : R3) (!₂[d, e, f] : R3) = a * d + b * e + c * f := by
  rw [inner_coord]
  simp

lemma isometry_of_gram_fin3 (u v : Fin 3 → R3) (hu : LinearIndependent ℝ u)
    (h : ∀ i j, ⟪u i, u j⟫_ℝ = ⟪v i, v j⟫_ℝ) :
    LinearIndependent ℝ v ∧ ∃ g : R3 ≃ₗᵢ[ℝ] R3, ∀ i, g (u i) = v i := by
  have hgram : Matrix.gram ℝ v = Matrix.gram ℝ u := by
    ext i j; simp [h]
  have hv : LinearIndependent ℝ v := by
    apply Matrix.linearIndependent_of_det_gram_ne_zero
    rw [hgram]
    exact Matrix.det_gram_ne_zero_iff_linearIndependent.mpr hu
  refine ⟨hv, ?_⟩
  have hcard : Fintype.card (Fin 3) = Module.finrank ℝ R3 := by simp
  let bu := basisOfLinearIndependentOfCardEqFinrank hu hcard
  let bv := basisOfLinearIndependentOfCardEqFinrank hv hcard
  let f : R3 ≃ₗ[ℝ] R3 := bu.equiv bv (Equiv.refl _)
  have hf : ∀ i, f (u i) = v i := by
    intro i
    have := bu.equiv_apply (b' := bv) (e := Equiv.refl _) (i := i)
    simpa [f, bu, bv] using this
  have key : ∀ a b : R3, ⟪f a, f b⟫_ℝ = ⟪a, b⟫_ℝ := by
    intro a b
    conv_rhs => rw [← bu.sum_repr a, ← bu.sum_repr b]
    conv_lhs => rw [← bu.sum_repr a, ← bu.sum_repr b]
    simp [map_sum, map_smul, sum_inner, inner_sum, inner_smul_left, inner_smul_right, hf, h,
      bu]
  exact ⟨f.isometryOfInner key, fun i => by simpa using hf i⟩

lemma inner_frame0 (g01 g05 g15 : ℝ) (v : R3) : ⟪v, frame g01 g05 g15 0⟫_ℝ = v 0 := by
  simp [frame, inner_coord]

lemma inner_frame1 (g01 g05 g15 : ℝ) (v : R3) :
    ⟪v, frame g01 g05 g15 1⟫_ℝ = v 0 * g01 + v 1 * L22 g01 := by
  simp [frame, inner_coord]

lemma inner_frame2 (g01 g05 g15 : ℝ) (v : R3) :
    ⟪v, frame g01 g05 g15 2⟫_ℝ = v 0 * g05 + v 1 * L32 g01 g05 g15 + v 2 * L33 g01 g05 g15 := by
  simp [frame, inner_coord]

lemma frame_gram {g01 g05 g15 : ℝ} (h22 : 0 < L22 g01)
    (h33 : 0 ≤ 1 - g05 ^ 2 - L32 g01 g05 g15 ^ 2) (i j : Fin 3) :
    ⟪frame g01 g05 g15 i, frame g01 g05 g15 j⟫_ℝ =
      ![![1, g01, g05], ![g01, 1, g15], ![g05, g15, 1]] i j := by
  have hd : 0 < 1 - g01 ^ 2 := Real.sqrt_pos.1 h22
  have s22 : L22 g01 ^ 2 = 1 - g01 ^ 2 := Real.sq_sqrt hd.le
  have s33 : L33 g01 g05 g15 ^ 2 = 1 - g05 ^ 2 - L32 g01 g05 g15 ^ 2 := Real.sq_sqrt h33
  have m32 : L32 g01 g05 g15 * L22 g01 = g15 - g01 * g05 := div_mul_cancel₀ _ h22.ne'
  have f0 : frame g01 g05 g15 0 = !₂[1, 0, 0] := rfl
  have f1 : frame g01 g05 g15 1 = !₂[g01, L22 g01, 0] := rfl
  have f2 : frame g01 g05 g15 2 = !₂[g05, L32 g01 g05 g15, L33 g01 g05 g15] := rfl
  have e00 : ⟪frame g01 g05 g15 0, frame g01 g05 g15 0⟫_ℝ = 1 := by
    rw [f0, inner_cols]; ring
  have e01 : ⟪frame g01 g05 g15 0, frame g01 g05 g15 1⟫_ℝ = g01 := by
    rw [f0, f1, inner_cols]; ring
  have e02 : ⟪frame g01 g05 g15 0, frame g01 g05 g15 2⟫_ℝ = g05 := by
    rw [f0, f2, inner_cols]; ring
  have e11 : ⟪frame g01 g05 g15 1, frame g01 g05 g15 1⟫_ℝ = 1 := by
    rw [f1, inner_cols]; linear_combination s22
  have e12 : ⟪frame g01 g05 g15 1, frame g01 g05 g15 2⟫_ℝ = g15 := by
    rw [f1, f2, inner_cols]; linear_combination m32
  have e22 : ⟪frame g01 g05 g15 2, frame g01 g05 g15 2⟫_ℝ = 1 := by
    rw [f2, inner_cols]; linear_combination s33
  fin_cases i <;> fin_cases j
  · exact e00
  · exact e01
  · exact e02
  · exact (real_inner_comm _ _).trans e01
  · exact e11
  · exact e12
  · exact (real_inner_comm _ _).trans e02
  · exact (real_inner_comm _ _).trans e12
  · exact e22

lemma c1_bounds : 309 / 1000 ≤ c1 ∧ c1 ≤ 31 / 100 := by
  have h5 : (5 : ℝ) = √5 ^ 2 := (Real.sq_sqrt (by norm_num)).symm
  have hs : 0 ≤ √5 := Real.sqrt_nonneg 5
  unfold c1
  constructor <;> nlinarith

lemma P_inner_01 : ⟪pentBipyramid 0, pentBipyramid 1⟫_ℝ = c1 := by
  rw [pent0, pent1, inner_cols, cos_2pi5]; ring

lemma P_inner_05 : ⟪pentBipyramid 0, pentBipyramid 5⟫_ℝ = 0 := by
  rw [pent0, pent5', inner_cols]; ring

lemma P_inner_15 : ⟪pentBipyramid 1, pentBipyramid 5⟫_ℝ = 0 := by
  rw [pent1, pent5', inner_cols]; ring

lemma P_inner_0 (v : R3) : ⟪v, pentBipyramid 0⟫_ℝ = v 0 := by
  rw [pent0, inner_coord]; simp

lemma P_inner_1 (v : R3) :
    ⟪v, pentBipyramid 1⟫_ℝ = c1 * v 0 + sin (2 * π / 5) * v 1 := by
  rw [pent1, inner_coord, cos_2pi5]; simp; ring

lemma P_inner_5 (v : R3) : ⟪v, pentBipyramid 5⟫_ℝ = v 2 := by
  rw [pent5', inner_coord]; simp

lemma sin_2pi5_sq : sin (2 * π / 5) ^ 2 = 1 - c1 ^ 2 := by
  have := sin_sq_add_cos_sq (2 * π / 5)
  rw [cos_2pi5] at this
  linarith

lemma sin_2pi5_pos : 0 < sin (2 * π / 5) := by
  apply sin_pos_of_pos_of_lt_pi
  · positivity
  · linarith [pi_pos]

theorem exists_iso_close {y : Fin 7 → R3} (hy : ∀ i, ‖y i‖ = 1) {w : ℝ} (hw : w ≤ 1 / 10)
    (hG : ∀ i j, |⟪y i, y j⟫_ℝ - ⟪pentBipyramid i, pentBipyramid j⟫_ℝ| ≤ w) :
    ∃ g : R3 ≃ₗᵢ[ℝ] R3, ∀ i, ‖g (y i) - pentBipyramid i‖ ≤ 11 / 2 * w := by
  have hw0 : 0 ≤ w := (abs_nonneg _).trans (hG 0 0)
  obtain ⟨hc1a, hc1b⟩ := c1_bounds
  obtain ⟨g01, hg01d⟩ : ∃ g, g = ⟪y 0, y 1⟫_ℝ := ⟨_, rfl⟩
  obtain ⟨g05, hg05d⟩ : ∃ g, g = ⟪y 0, y 5⟫_ℝ := ⟨_, rfl⟩
  obtain ⟨g15, hg15d⟩ : ∃ g, g = ⟪y 1, y 5⟫_ℝ := ⟨_, rfl⟩
  have hg01 : |g01 - c1| ≤ w := by
    have := hG 0 1; rw [P_inner_01, ← hg01d] at this; exact this
  have hg05 : |g05| ≤ w := by
    have := hG 0 5; rw [P_inner_05, sub_zero, ← hg05d] at this; exact this
  have hg15 : |g15| ≤ w := by
    have := hG 1 5; rw [P_inner_15, sub_zero, ← hg15d] at this; exact this
  obtain ⟨g01l, g01u⟩ := abs_le.1 hg01
  have hg01l : 209 / 1000 ≤ g01 := by linarith
  have hg01u : g01 ≤ 41 / 100 := by linarith
  have hd : 0 < 1 - g01 ^ 2 := by nlinarith
  have h22 : 0 < L22 g01 := Real.sqrt_pos.2 hd
  have s22 : L22 g01 ^ 2 = 1 - g01 ^ 2 := Real.sq_sqrt hd.le
  have m32 : L32 g01 g05 g15 * L22 g01 = g15 - g01 * g05 := div_mul_cancel₀ _ h22.ne'
  obtain ⟨hL22a, -⟩ := L22_bounds hw0 hw hc1a hc1b hg01 h22 s22
  have hL32b := L32_bound hw0 hg01l hg01u hg05 hg15 hL22a m32
  have h33 : 0 < 1 - g05 ^ 2 - L32 g01 g05 g15 ^ 2 := by
    obtain ⟨a1, a2⟩ := abs_le.1 hg05
    obtain ⟨b1, b2⟩ := abs_le.1 hL32b
    nlinarith
  have hL33p : 0 < L33 g01 g05 g15 := Real.sqrt_pos.2 h33
  have s33 : L33 g01 g05 g15 ^ 2 = 1 - g05 ^ 2 - L32 g01 g05 g15 ^ 2 := Real.sq_sqrt h33.le
  -- Gram matrix of the reference triple
  have e00 : ⟪y 0, y 0⟫_ℝ = 1 := by rw [real_inner_self_eq_norm_sq, hy 0]; norm_num
  have e11 : ⟪y 1, y 1⟫_ℝ = 1 := by rw [real_inner_self_eq_norm_sq, hy 1]; norm_num
  have e55 : ⟪y 5, y 5⟫_ℝ = 1 := by rw [real_inner_self_eq_norm_sq, hy 5]; norm_num
  let u : Fin 3 → R3 := ![y 0, y 1, y 5]
  have hu_gram : ∀ i j, ⟪u i, u j⟫_ℝ = ![![1, g01, g05], ![g01, 1, g15], ![g05, g15, 1]] i j := by
    intro i j
    fin_cases i <;> fin_cases j
    · exact e00
    · exact hg01d.symm
    · exact hg05d.symm
    · exact (real_inner_comm _ _).trans hg01d.symm
    · exact e11
    · exact hg15d.symm
    · exact (real_inner_comm _ _).trans hg05d.symm
    · exact (real_inner_comm _ _).trans hg15d.symm
    · exact e55
  have hgram : ∀ i j, ⟪u i, u j⟫_ℝ = ⟪frame g01 g05 g15 i, frame g01 g05 g15 j⟫_ℝ := by
    intro i j
    rw [hu_gram, frame_gram h22 h33.le]
  have hli : LinearIndependent ℝ u := by
    apply Matrix.linearIndependent_of_det_gram_ne_zero
    have hG3 : Matrix.gram ℝ u = !![1, g01, g05; g01, 1, g15; g05, g15, 1] := by
      ext i j
      rw [Matrix.gram_apply, hu_gram]
      fin_cases i <;> fin_cases j <;> rfl
    have hdet : Matrix.det (!![1, g01, g05; g01, 1, g15; g05, g15, 1] : Matrix (Fin 3) (Fin 3) ℝ)
        = L22 g01 ^ 2 * L33 g01 g05 g15 ^ 2 := by
      rw [Matrix.det_fin_three]
      simp
      linear_combination (-(L22 g01) ^ 2) * s33 + (-(1 - g05 ^ 2)) * s22
        + (L32 g01 g05 g15 * L22 g01 + g15 - g01 * g05) * m32
    rw [hG3, hdet]
    positivity
  obtain ⟨-, g, hg⟩ := isometry_of_gram_fin3 u (frame g01 g05 g15) hli hgram
  refine ⟨g, fun j => ?_⟩
  obtain ⟨v, hv⟩ : ∃ v : R3, v = g (y j) := ⟨_, rfl⟩
  have hvn : ‖v‖ = 1 := by rw [hv, g.norm_map, hy]
  have hin : ∀ k : Fin 3, ⟪v, frame g01 g05 g15 k⟫_ℝ = ⟪y j, u k⟫_ℝ := by
    intro k
    rw [← hg k, hv, g.inner_map_map]
  have d0 : v 0 = ⟪y j, y 0⟫_ℝ := by
    have := hin 0; rw [inner_frame0] at this; exact this
  have d1 : v 0 * g01 + v 1 * L22 g01 = ⟪y j, y 1⟫_ℝ := by
    have := hin 1; rw [inner_frame1] at this; exact this
  have d5 : v 0 * g05 + v 1 * L32 g01 g05 g15 + v 2 * L33 g01 g05 g15 = ⟪y j, y 5⟫_ℝ := by
    have := hin 2; rw [inner_frame2] at this; exact this
  have e0 : |v 0 - pentBipyramid j 0| ≤ w := by
    have := hG j 0; rwa [← d0, P_inner_0] at this
  have e1 : |(g01 * v 0 + L22 g01 * v 1)
      - (c1 * pentBipyramid j 0 + sin (2 * π / 5) * pentBipyramid j 1)| ≤ w := by
    have := hG j 1; rw [← d1, P_inner_1] at this
    have h : g01 * v 0 + L22 g01 * v 1 = v 0 * g01 + v 1 * L22 g01 := by ring
    rwa [h]
  have e5 : |(g05 * v 0 + L32 g01 g05 g15 * v 1 + L33 g01 g05 g15 * v 2)
      - pentBipyramid j 2| ≤ w := by
    have := hG j 5; rw [← d5, P_inner_5] at this
    have h : g05 * v 0 + L32 g01 g05 g15 * v 1 + L33 g01 g05 g15 * v 2
        = v 0 * g05 + v 1 * L32 g01 g05 g15 + v 2 * L33 g01 g05 g15 := by ring
    rwa [h]
  have hab : v 0 ^ 2 + v 1 ^ 2 + v 2 ^ 2 = 1 := by rw [← norm_sq_coord, hvn]; norm_num
  have hab0 : pentBipyramid j 0 ^ 2 + pentBipyramid j 1 ^ 2 + pentBipyramid j 2 ^ 2 = 1 := by
    rw [← norm_sq_coord, pent_norm]; norm_num
  have key := core_bound hw0 hw hc1a hc1b sin_2pi5_sq sin_2pi5_pos hg01 hg05 hg15 h22 s22 m32
    hL33p s33 hab hab0 e0 e1 e5
  have hsq : ‖v - pentBipyramid j‖ ^ 2 = (v 0 - pentBipyramid j 0) ^ 2
      + (v 1 - pentBipyramid j 1) ^ 2 + (v 2 - pentBipyramid j 2) ^ 2 := by
    rw [norm_sq_coord]; simp
  rw [← hv]
  refine (sq_le_sq₀ (norm_nonneg _) (by positivity)).1 ?_
  rw [hsq]; exact key

end GV

/- END GV -/

/- BEGIN TWOREGIME -/

namespace TwoRegime

open scoped InnerProductSpace

end TwoRegime

namespace TwoRegime

open scoped InnerProductSpace
open Base

end TwoRegime

namespace TwoRegime

open scoped InnerProductSpace
open Base

/-- A uniform Gram window `w ≤ 1/10` around the labelled `P` is controlled by the sup-norm
statement at radius `(11/2) w` (chart step `GV.exists_iso_close`). -/
theorem localGram_of_localMinAt {w : ℝ} (hw : w ≤ 1 / 10) (hL : LocalMinAt (11 / 2 * w)) :
    LocalGram (fun _ => w) := by
  intro y hy hG
  have hw0 : 0 ≤ w := (abs_nonneg _).trans (hG 0 1 (by decide))
  have hG' : ∀ i j, |⟪y i, y j⟫_ℝ - ⟪pentBipyramid i, pentBipyramid j⟫_ℝ| ≤ w := by
    intro i j
    by_cases h : i = j
    · subst h
      rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq, hy.1 i, pent_norm i]
      simpa using hw0
    · exact hG i j h
  obtain ⟨g, hg⟩ := GV.exists_iso_close hy.1 hw hG'
  have hz : (fun a => g (y (Equiv.refl (Fin 7) a))) ∈ SphereConfig 7 :=
    sphereConfig_comp g (Equiv.refl (Fin 7)) hy
  have hE : coulombEnergy (fun a => g (y (Equiv.refl (Fin 7) a))) = coulombEnergy y := by
    rw [coulombEnergy_comp_isometry g (fun a => y (Equiv.refl (Fin 7) a)),
      coulombEnergy_comp_perm (Equiv.refl (Fin 7)) y]
  obtain ⟨h1, h2⟩ := hL _ hz (fun i => by simpa using hg i)
  refine ⟨hE ▸ h1, fun hEq => ?_⟩
  obtain ⟨g', hg'⟩ := h2 (hE.trans hEq)
  refine ⟨g'.trans g.symm, fun j => ?_⟩
  have := hg' j
  simp only [Equiv.refl_apply] at this
  simp only [LinearIsometryEquiv.trans_apply]
  rw [← this]
  simp

end TwoRegime

/- END TWOREGIME -/

/- BEGIN TR_D -/
namespace TwoRegime

open scoped InnerProductSpace
open Base

end TwoRegime

/- END TR_D -/

/- BEGIN TR_E -/
namespace ThreePoint

open Finset Matrix
open scoped RealInnerProductSpace

section FinalCut

variable {n : ℕ}

end FinalCut

end ThreePoint

namespace TwoRegime

open scoped InnerProductSpace
open Base

end TwoRegime

/- END TR_E -/

/- BEGIN TR_G -/
namespace TwoRegime

open scoped InnerProductSpace
open Base

end TwoRegime

namespace TwoRegime

open scoped InnerProductSpace
open Base

end TwoRegime

/- BEGIN TR_G3 -/
namespace TwoRegime

open scoped InnerProductSpace
open Base

/-- A symmetric local statement gives the asymmetric one on any smaller window. -/
theorem localGramA_of_localGram {ω lo hi : ℝ → ℝ} (hL : LocalGram ω) (hlo : ∀ t, lo t ≤ ω t)
    (hhi : ∀ t, hi t ≤ ω t) : LocalGramA lo hi := by
  intro y hy hw
  refine hL y hy fun i j hij => ?_
  obtain ⟨h1, h2⟩ := hw i j hij
  rw [abs_le]
  have := hlo ⟪pentBipyramid i, pentBipyramid j⟫_ℝ
  have := hhi ⟪pentBipyramid i, pentBipyramid j⟫_ℝ
  simp only [Equiv.refl_apply] at h1 h2
  constructor <;> linarith

/-- The local statement transported along a relabelling of the points. -/
theorem local_of_windowA {lo hi : ℝ → ℝ} (hL : LocalGramA lo hi) {y : Fin 7 → R3}
    (hy : y ∈ SphereConfig 7) (σ : Equiv.Perm (Fin 7)) (hσ : InWindow lo hi y σ) :
    coulombEnergy pentBipyramid ≤ coulombEnergy y ∧
    (coulombEnergy y = coulombEnergy pentBipyramid →
      ∃ (g : R3 ≃ₗᵢ[ℝ] R3) (σ : Equiv.Perm (Fin 7)), ∀ i, y i = g (pentBipyramid (σ i))) := by
  have hz : (fun a => (LinearIsometryEquiv.refl ℝ R3) (y (σ.symm a))) ∈ SphereConfig 7 :=
    sphereConfig_comp (LinearIsometryEquiv.refl ℝ R3) σ.symm hy
  have hE : coulombEnergy (fun a => (LinearIsometryEquiv.refl ℝ R3) (y (σ.symm a)))
      = coulombEnergy y := by
    rw [coulombEnergy_comp_isometry (LinearIsometryEquiv.refl ℝ R3) (fun a => y (σ.symm a)),
      coulombEnergy_comp_perm σ.symm y]
  obtain ⟨h1, h2⟩ := hL _ hz (fun i j hij => by
    have := hσ (σ.symm i) (σ.symm j) (fun h => hij (σ.symm.injective h))
    simpa using this)
  refine ⟨hE ▸ h1, fun hEq => ?_⟩
  obtain ⟨g', hg'⟩ := h2 (hE.trans hEq)
  refine ⟨g', σ, fun j => ?_⟩
  have := hg' (σ j)
  simpa using this

end TwoRegime
/- END TR_G3 -/
/- BEGIN TR_G4 -/
namespace TwoRegime

open scoped InnerProductSpace
open Base

end TwoRegime
/- END TR_G4 -/
/- END TR_G -/

/- BEGIN INTERFACES -/
namespace Interfaces

open Finset Base

end Interfaces
/- END INTERFACES -/

/- BEGIN GLUE -/
namespace Glue

open Finset Base Interfaces

end Glue
/- END GLUE -/

/- BEGIN TR_F -/
namespace EPBounds

open Real

end EPBounds
/- END TR_F -/
end ThomsonN7

section RegLocalSection
/- BEGIN REGLOCAL (agent7): perturbative strict local minimality of the pentagonal bipyramid.
   Splice AFTER Level1d (needs GAUGE = exists_gauge, P1/P3ext, Base, TwoRegime.LocalMinAt).
   Pieces in order: Loc1 (H, B3) | QCore1 (certificate defs/lemmas) | Q2 (expansion) | QCore2 (core) | Loc2 (glue). -/
open Real
open scoped RealInnerProductSpace
namespace ThomsonN7
/- BEGIN LOC1 (agent7): exact chart identity (H) and cubic Bregman lower bound (B3) in h = y - P.
   Splice AFTER the GAUGE block (needs P1, P3ext); compiles against Level1b.lean lines 1-3641. -/
namespace Reg
open Base

/-- For a unit vector `y i = P i + h i` the normal component of `h i` is `-‖h i‖²/2`. -/
lemma inner_P_h {y : Fin 7 → R3} (hy : ∀ i, ‖y i‖ = 1) (i : Fin 7) :
    inner ℝ (pentBipyramid i) (y i - pentBipyramid i) = -(1 / 2) * ‖y i - pentBipyramid i‖ ^ 2 := by
  have h1 := hy i
  have h2 := pent_norm i
  have h3 : ‖y i‖ ^ 2 = ‖pentBipyramid i + (y i - pentBipyramid i)‖ ^ 2 := by simp
  rw [norm_add_sq_real, h1, h2] at h3
  linarith

end Reg

/- END LOC1 -/

end ThomsonN7

/- BEGIN QCORE1 -/
namespace ThomsonN7
namespace Reg

end Reg
end ThomsonN7
/- END QCORE1 -/

/- BEGIN Q2 -/
open Real
open scoped RealInnerProductSpace
namespace ThomsonN7
namespace Reg
open Base

end Reg
end ThomsonN7

/- END Q2 -/

/- BEGIN QCORE2 -/
namespace ThomsonN7
namespace Reg

end Reg
end ThomsonN7
/- END QCORE2 -/

/- BEGIN LOC2 -/
open Real
open scoped RealInnerProductSpace
namespace ThomsonN7
namespace Reg
open Base

/-! ### The atom box for the penalised Hessian certificate -/

lemma gaugeG_zero {y : Fin 7 → R3}
    (hg : ∀ a b : Fin 3, ∑ i, pentBipyramid i a * y i b = ∑ i, pentBipyramid i b * y i a)
    (a b : Fin 3) : gaugeG (fun i => y i - pentBipyramid i) a b = 0 := by
  have h1 : ∀ i, pentBipyramid i a * (y i - pentBipyramid i) b
      - pentBipyramid i b * (y i - pentBipyramid i) a
      = pentBipyramid i a * y i b - pentBipyramid i b * y i a := by
    intro i
    simp only [PiLp.sub_apply]
    ring
  unfold gaugeG
  simp only [h1, Finset.sum_sub_distrib]
  rw [hg a b]
  ring

lemma pen_eq {y : Fin 7 → R3} (hy : ∀ i, ‖y i‖ = 1)
    (hg : ∀ a b : Fin 3, ∑ i, pentBipyramid i a * y i b = ∑ i, pentBipyramid i b * y i a) :
    Pen (fun i => y i - pentBipyramid i) = 1 / 4 * ∑ i, ‖y i - pentBipyramid i‖ ^ 4 := by
  have hs : ∑ i, inner ℝ (pentBipyramid i) (y i - pentBipyramid i) ^ 2
      = 1 / 4 * ∑ i, ‖y i - pentBipyramid i‖ ^ 4 := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [inner_P_h hy i]; ring
  have h0 := gaugeG_zero hg
  unfold Pen
  rw [h0 0 1, h0 0 2, h0 1 2]
  linarith [hs]

/-- **Local inequality.** For a gauge-fixed unit injective configuration within `10⁻⁴` of the
bipyramid (coordinatewise in `ℝ³`-norm), the energy excess is at least `10⁻³ ∑ ‖yᵢ - Pᵢ‖²`. -/
theorem local_ineq {y : Fin 7 → R3} (hy : ∀ i, ‖y i‖ = 1) (hinj : Function.Injective y)
    (hg : ∀ a b : Fin 3, ∑ i, pentBipyramid i a * y i b = ∑ i, pentBipyramid i b * y i a)
    (hρ : ∀ i, ‖y i - pentBipyramid i‖ ≤ 1 / 10000) :
    1 / 1000 * ∑ i, ‖y i - pentBipyramid i‖ ^ 2
      ≤ coulombEnergy y - coulombEnergy pentBipyramid := by
  have hB3 := energy_ge_cubic hy hinj
  have hX : ∑ i, ∑ j ∈ Finset.Ioi i, (3 / 2 * phi (gP i j) ^ 5 * tau y i j ^ 2
        + 5 / 2 * phi (gP i j) ^ 7 * tau y i j ^ 3)
      = ∑ i, ∑ j ∈ Finset.Ioi i, 3 / 2 * phi (gP i j) ^ 5
          * (inner ℝ (pentBipyramid i) (y j - pentBipyramid j)
              + inner ℝ (y i - pentBipyramid i) (pentBipyramid j)) ^ 2
        + ∑ i, ∑ j ∈ Finset.Ioi i, Dpair y i j := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    unfold Dpair
    ring
  have hmain : Qhess (fun i => y i - pentBipyramid i) + ∑ i, ∑ j ∈ Finset.Ioi i, Dpair y i j
      ≤ coulombEnergy y - coulombEnergy pentBipyramid := by
    unfold Qhess
    linarith [hB3, hX]
  have hD := sum_Dpair_lower (y := y) (r := 1 / 10000) (by norm_num) hρ
  have hH := hessian_lower (fun i => y i - pentBipyramid i)
  have hP := pen_eq hy hg
  have hquart : ∑ i, ‖y i - pentBipyramid i‖ ^ 4
      ≤ (1 / 10000) ^ 2 * ∑ i, ‖y i - pentBipyramid i‖ ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    have h1 : ‖y i - pentBipyramid i‖ ^ 2 ≤ (1 / 10000) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) (hρ i) 2
    have h2 : 0 ≤ ‖y i - pentBipyramid i‖ ^ 2 := sq_nonneg _
    nlinarith
  have hS : 0 ≤ ∑ i, ‖y i - pentBipyramid i‖ ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  linarith [hmain, hD, hH, hP, hquart, hS]

/-- **Strict local minimality of the pentagonal bipyramid** (perturbative, radius `10⁻⁴` in
`ℓ²` distance of the labelled configuration): every configuration within that distance has energy
at least `E(P)`, and equality forces the configuration to be an isometric image of `P`. -/
theorem pent_local_min {z : Fin 7 → R3} (hz : z ∈ SphereConfig 7)
    (hclose : ∑ i, ‖z i - pentBipyramid i‖ ^ 2 ≤ (1 / 10000) ^ 2) :
    coulombEnergy pentBipyramid ≤ coulombEnergy z ∧
      (coulombEnergy z = coulombEnergy pentBipyramid →
        ∃ g : R3 ≃ₗᵢ[ℝ] R3, ∀ i, z i = g (pentBipyramid i)) := by
  obtain ⟨g, hg1, hg2⟩ := exists_gauge pentBipyramid z
  have hy1 : ∀ i, ‖g (z i)‖ = 1 := fun i => by rw [LinearIsometryEquiv.norm_map]; exact hz.1 i
  have hyinj : Function.Injective (fun i => g (z i)) := g.injective.comp hz.2
  have hE : coulombEnergy (fun i => g (z i)) = coulombEnergy z := coulombEnergy_comp_isometry g z
  have hρ : ∀ i, ‖g (z i) - pentBipyramid i‖ ≤ 1 / 10000 := by
    intro i
    have h1 : ‖g (z i) - pentBipyramid i‖ ^ 2 ≤ ∑ j, ‖g (z j) - pentBipyramid j‖ ^ 2 :=
      Finset.single_le_sum (f := fun j => ‖g (z j) - pentBipyramid j‖ ^ 2)
        (fun j _ => sq_nonneg _) (Finset.mem_univ i)
    have h2 : ‖g (z i) - pentBipyramid i‖ ^ 2 ≤ (1 / 10000) ^ 2 := h1.trans (hg2.trans hclose)
    exact le_of_sq_le_sq h2 (by norm_num)
  have key := local_ineq (y := fun i => g (z i)) hy1 hyinj hg1 hρ
  rw [hE] at key
  have hS : 0 ≤ ∑ i, ‖g (z i) - pentBipyramid i‖ ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  refine ⟨by linarith, fun heq => ⟨g.symm, fun i => ?_⟩⟩
  have hS0 : ∑ i, ‖g (z i) - pentBipyramid i‖ ^ 2 = 0 := by linarith
  have hi : ‖g (z i) - pentBipyramid i‖ ^ 2 = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => sq_nonneg _)).1 hS0 i (Finset.mem_univ i)
  have hi' : g (z i) = pentBipyramid i := sub_eq_zero.1 (norm_eq_zero.1 (pow_eq_zero_iff (two_ne_zero) |>.1 hi))
  rw [← hi']
  simp

end Reg
end ThomsonN7

/- END LOC2 -/

namespace ThomsonN7
namespace Reg

/-- Sup-norm form of the tiny-ball local minimality: every unit injective configuration within
`1/30000` of the labelled bipyramid in every vertex has energy at least `E(P)`, with equality
only on the `O(3)`-orbit of `P`. -/
theorem pent_local_min_sup {z : Fin 7 → R3} (hz : z ∈ SphereConfig 7)
    (hclose : ∀ i, ‖z i - pentBipyramid i‖ ≤ 1 / 30000) :
    coulombEnergy pentBipyramid ≤ coulombEnergy z ∧
      (coulombEnergy z = coulombEnergy pentBipyramid →
        ∃ g : R3 ≃ₗᵢ[ℝ] R3, ∀ i, z i = g (pentBipyramid i)) := by
  refine pent_local_min hz ?_
  have h1 : ∀ i, ‖z i - pentBipyramid i‖ ^ 2 ≤ (1 / 30000) ^ 2 :=
    fun i => pow_le_pow_left₀ (norm_nonneg _) (hclose i) 2
  calc ∑ i, ‖z i - pentBipyramid i‖ ^ 2 ≤ ∑ _i : Fin 7, (1 / 30000 : ℝ) ^ 2 :=
        Finset.sum_le_sum fun i _ => h1 i
    _ = 7 * (1 / 30000) ^ 2 := by simp
    _ ≤ (1 / 10000) ^ 2 := by norm_num

end Reg

/-- The tiny-ball local statement in the `LocalMinAt` interface of `TwoRegime`. -/
theorem TwoRegime.localMinAt_tiny : TwoRegime.LocalMinAt (1 / 30000) :=
  fun _ hz h => Reg.pent_local_min_sup hz h

end ThomsonN7

/- END REGLOCAL -/
end RegLocalSection

/- BEGIN CASE1 -/
namespace ThomsonN7
namespace CutOneD

end CutOneD
end ThomsonN7

namespace ThomsonN7

namespace Case1Data
open ThomsonN7 ThomsonN7.Cert

end Case1Data

end ThomsonN7

namespace ThomsonN7
namespace Case1

open scoped InnerProductSpace
open ThomsonN7.Cert ThomsonN7.Cert.Cert3

/-! ### Chunked evaluation of the Kronecker check for `Case1Data.cf`

The identity expression `Case1Data.cf.idE` has about 147 000 nodes.  Evaluating `chk` on it in one
kernel call is correct but keeps every intermediate kernel term alive until the end of the
declaration.  Here the same check is split into separate declarations, one per piece of the
expression (`hE`, four `F`-blocks, eight `S`-blocks).  For every expression `e`, `c1Stat w D e`
computes, in one structural pass, the tuple `(ℓ¹-norm, deg u, deg v, deg t, Kronecker value)`
(`c1Stat_eq`).  The 13 pieces are evaluated by `decide +kernel` against exact literals, in 13
separate declarations; the statistics of `Case1Data.cf.idE` follow by the composition lemma
`c1Stat_idE` and closed arithmetic on the literals, and `chk` is then decided by its own definition
(`Nat.log2 ℓ¹ + 1 = 179`, `max deg + 1 = 11`, Kronecker value `0`).  The statement of `cf_ok` is
unchanged; the literals are data found by a program outside Lean and are only ever checked. -/

/-! The 13 pieces, each evaluated in its own declaration (`w = 179`, `D = 11`). -/

end Case1
end ThomsonN7

/- END CASE1 -/

/- BEGIN CASE2RED -/
namespace ThomsonN7
namespace Case1

section Case2Red

open scoped InnerProductSpace
open Base

end Case2Red

end Case1
end ThomsonN7
/- END CASE2RED -/

section Asm_Typed
open Finset Matrix
open scoped RealInnerProductSpace

namespace ThomsonN7
namespace ThreePoint

/-! # Typed (root-dependent) three-point bound

Every root `i` carries its own kernel `s i`; every pair `{i, j}` carries its own minorant `H i j`.
-/

section TypedRoot

end TypedRoot

section TypedComb

variable {n : ℕ}

end TypedComb

end ThreePoint
end ThomsonN7

end Asm_Typed

section Asm_Typed2
open Finset Matrix
open scoped RealInnerProductSpace

namespace ThomsonN7
namespace ThreePoint

/-! # Typed three-point bound with free pair shares

Each triple `{i, j, l}` receives a share `W i j l` of the pair function of `{i, j}` (and
similarly for the constant), so that the total over the triples containing a pair is prescribed.
-/

section TypedComb2

variable {n : ℕ}

end TypedComb2

end ThreePoint
end ThomsonN7

end Asm_Typed2

section Asm_Typed7
open Finset Matrix
open scoped RealInnerProductSpace

namespace ThomsonN7
namespace ThreePoint

section Sym

end Sym

/-! # The `n = 7` typed instance: two poles (indices `0, 1`) and five ring points (`2..6`) -/

section Typed7

end Typed7

end ThreePoint
end ThomsonN7

end Asm_Typed7

section Asm_T4
namespace ThomsonN7
namespace M6

/-! ### Integer interval arithmetic (exact, no rounding) -/

/-! ### Homogeneous Gram determinants and their interval enclosures -/

/-! ### Boxes, bisection and the two refutation checkers -/

end M6
end ThomsonN7

open scoped InnerProductSpace

namespace ThomsonN7
namespace T4

open M6

/-! ### Combinatorics of the ring: a 2-colouring of `K₅` without monochromatic triangle is a pentagon -/

/-! ### The ring colouring of a configuration -/

/-! ### The relabelling of the bipyramid -/

/-! ### Nominal Gram entries of the relabelled bipyramid -/

/-! ### Ring rigidity -/

end T4
end ThomsonN7

end Asm_T4

section Asm_Glue1
/-!
# Glue for the near-antipodal case (Case 2)

Abstract, numerics-independent assembly:

* `Glue.exists_minpair_perm`: every 7-configuration is a relabelling of one whose pair `(0,1)` has the
  smallest inner product;
* `Glue.RootedClaim`, `Glue.case2_of_rooted`, `Glue.seven_of_rooted`: the rooted claim implies both
  Challenge statements (through `Case1.seven_of_case2`);
* `Glue.rooted_of_cap_slabs`: a cap certificate plus finitely many slab certificates give the rooted
  claim;
* `Glue.slab_of_typed`, `Glue.cap_of_typed`: a typed pair-minorant bound gives the slab / cap claims
  (with the equality analysis through `M3.contact_rigidity`).
-/

namespace ThomsonN7
namespace Glue

section Rooted

open scoped InnerProductSpace
open Base

end Rooted

section Typed

open scoped InnerProductSpace
open Base

/-- The energy of a unit configuration as a double sum of `phi`. -/
lemma energy_eq_sum {y : Fin 7 → R3} (hy : y ∈ SphereConfig 7) :
    coulombEnergy y = ∑ i : Fin 7, ∑ j ∈ Finset.Ioi i, phi ⟪y i, y j⟫_ℝ :=
  coulombEnergy_eq_sum_phi hy.1

end Typed

end Glue
end ThomsonN7

end Asm_Glue1

section Asm_Glue2
/-!
# Glue for the near-sharp (tube) cap certificate, route S2

A typed pair-minorant bound `e <= sum_{i<j} H_cls(<y_i, y_j>)` which is only *near*-sharp
(`E(P) <= e + delta`) still gives the cap claim, provided

* the pair slacks `phi - H_cls` control the distance to the nodes (`slack <= delta` puts the inner
  product within `tau` of a node of its class);
* the tube rigidity `TubeRigid tau` (closeness of all 21 inner products to the class nodes gives a
  relabelling of the pentagonal bipyramid within `tau` in every Gram entry);
* the local statement `LocalGramA` holds on the window `tau` (Regime B).

The proof is: `E(y) <= E(P)` implies `sum of slacks <= delta`, hence every slack `<= delta`, hence the
tube, hence the window, hence the local statement.
-/

namespace ThomsonN7
namespace Glue

section Tube

open scoped InnerProductSpace
open Base

/-- The certified local window: Regime B holds for uniform Gram windows `tau <= 1/165000`. -/
theorem localGramA_of_le {τ : ℝ} (hτ : τ ≤ 1 / 165000) :
    TwoRegime.LocalGramA (fun _ => τ) (fun _ => τ) := by
  have hL : TwoRegime.LocalGram (fun _ => (1 / 165000 : ℝ)) :=
    TwoRegime.localGram_of_localMinAt (w := 1 / 165000) (by norm_num)
      (by
        have : (11 / 2 * (1 / 165000 : ℝ)) = 1 / 30000 := by norm_num
        rw [this]
        exact TwoRegime.localMinAt_tiny)
  exact TwoRegime.localGramA_of_localGram hL (fun _ => hτ) (fun _ => hτ)

/-- A relabelling with all Gram entries within `tau` of those of `P ∘ σ` puts `y` in the
symmetric window. -/
lemma inWindow_of_close {τ : ℝ} {y : Fin 7 → R3} {σ : Equiv.Perm (Fin 7)}
    (h : ∀ i j, i ≠ j →
      |⟪y i, y j⟫_ℝ - ⟪pentBipyramid (σ i), pentBipyramid (σ j)⟫_ℝ| ≤ τ) :
    TwoRegime.InWindow (fun _ => τ) (fun _ => τ) y σ := by
  intro i j hij
  have := abs_le.1 (h i j hij)
  constructor <;> linarith [this.1, this.2]

/-- Termwise facts for the pairs of a minimal-pair configuration, slack version: the class minorant
lies below `phi`, and a slack at most `delta` puts the inner product in the class predicate. -/
lemma pair_facts_tube {y : Fin 7 → R3} (hy : y ∈ SphereConfig 7) {lo hi δ : ℝ}
    (HA HB HC : ℝ → ℝ) (ZA ZB ZC : ℝ → Prop)
    (hmin : ∀ i j, i ≠ j → ⟪y 0, y 1⟫_ℝ ≤ ⟪y i, y j⟫_ℝ)
    (hlo : lo ≤ ⟪y 0, y 1⟫_ℝ) (hhi : ⟪y 0, y 1⟫_ℝ ≤ hi)
    (hA : ∀ t, lo ≤ t → t ≤ hi → HA t ≤ phi t ∧ (phi t - HA t ≤ δ → ZA t))
    (hB : ∀ t, lo ≤ t → t < 1 → HB t ≤ phi t ∧ (phi t - HB t ≤ δ → ZB t))
    (hC : ∀ t, lo ≤ t → t < 1 → HC t ≤ phi t ∧ (phi t - HC t ≤ δ → ZC t))
    (i j : Fin 7) (hij : i < j) :
    cls3 HA HB HC i j ⟪y i, y j⟫_ℝ ≤ phi ⟪y i, y j⟫_ℝ ∧
    (phi ⟪y i, y j⟫_ℝ - cls3 HA HB HC i j ⟪y i, y j⟫_ℝ ≤ δ →
      cls3 ZA ZB ZC i j ⟪y i, y j⟫_ℝ) := by
  have hne : i ≠ j := hij.ne
  have hlt : ⟪y i, y j⟫_ℝ < 1 := inner_lt_one_of_ne (hy.1 i) (hy.1 j) (fun h => hne (hy.2 h))
  have hge : lo ≤ ⟪y i, y j⟫_ℝ := hlo.trans (hmin i j hne)
  have hij' : i.val < j.val := hij
  have hj7 := j.isLt
  unfold cls3
  by_cases h1 : i.val ≤ 1 ∧ j.val ≤ 1
  · have hi5 : i = 0 := Fin.ext (by simp; omega)
    have hj6 : j = 1 := Fin.ext (by simp; omega)
    subst hi5 hj6
    simpa only [h1, ite_true, and_self] using hA _ hlo hhi
  · by_cases h2 : i.val ≤ 1 ∨ j.val ≤ 1
    · simpa only [h1, h2, ite_false, ite_true] using hB _ hge hlt
    · simpa only [h1, h2, ite_false] using hC _ hge hlt

/-- **Cap claim from a near-sharp typed minorant bound (tube route).**  The typed sum is bounded
below by `e` on the cap `⟪y 0, y 1⟫ ≤ a0` (minimal-pair configurations), with `E(P) ≤ e + δ`.  The
class minorants lie below `phi` and a slack `≤ δ` puts the inner product within `τ` of the class
nodes (`-1` for poles, `0` for pole--ring, `c1, c2` for ring--ring).  With tube rigidity and the
local statement on the window `τ`, `E(y) ≥ E(P)` on the cap and equality forces a pentagonal
bipyramid. -/
theorem cap_of_typed_tube {a0 e δ τ : ℝ} (HA HB HC : ℝ → ℝ)
    (hL : TwoRegime.LocalGramA (fun _ => τ) (fun _ => τ)) (hrig : TubeRigid τ)
    (hTB : ∀ y ∈ SphereConfig 7, ⟪y 0, y 1⟫_ℝ ≤ a0 →
      (∀ i j, i ≠ j → ⟪y 0, y 1⟫_ℝ ≤ ⟪y i, y j⟫_ℝ) →
      e ≤ ∑ i : Fin 7, ∑ j ∈ Finset.Ioi i, cls3 HA HB HC i j ⟪y i, y j⟫_ℝ)
    (hEδ : coulombEnergy pentBipyramid ≤ e + δ)
    (hA : ∀ t, -1 ≤ t → t ≤ a0 → HA t ≤ phi t ∧ (phi t - HA t ≤ δ → |t + 1| ≤ τ))
    (hB : ∀ t, -1 ≤ t → t < 1 → HB t ≤ phi t ∧ (phi t - HB t ≤ δ → |t| ≤ τ))
    (hC : ∀ t, -1 ≤ t → t < 1 → HC t ≤ phi t ∧
      (phi t - HC t ≤ δ → |t - c1| ≤ τ ∨ |t - c2| ≤ τ)) :
    ∀ y ∈ SphereConfig 7, ⟪y 0, y 1⟫_ℝ ≤ a0 →
      (∀ i j, i ≠ j → ⟪y 0, y 1⟫_ℝ ≤ ⟪y i, y j⟫_ℝ) → Concl y := by
  intro y hy hle hmin
  by_cases hbig : coulombEnergy pentBipyramid < coulombEnergy y
  · exact ⟨hbig.le, fun hE => absurd hE hbig.ne'⟩
  push Not at hbig
  have hlo : -1 ≤ ⟪y 0, y 1⟫_ℝ := neg_one_le_inner_of_unit (hy.1 0) (hy.1 1)
  have hP := hTB y hy hle hmin
  have hpf := fun i j hij => pair_facts_tube hy HA HB HC (fun t => |t + 1| ≤ τ)
    (fun t => |t| ≤ τ) (fun t => |t - c1| ≤ τ ∨ |t - c2| ≤ τ) hmin hlo hle hA hB hC i j hij
  have hnn : ∀ i j, j ∈ Finset.Ioi i →
      0 ≤ phi ⟪y i, y j⟫_ℝ - cls3 HA HB HC i j ⟪y i, y j⟫_ℝ := fun i j hj =>
    sub_nonneg.2 (hpf i j (Finset.mem_Ioi.1 hj)).1
  have hsplit : ∑ i : Fin 7, ∑ j ∈ Finset.Ioi i,
      (phi ⟪y i, y j⟫_ℝ - cls3 HA HB HC i j ⟪y i, y j⟫_ℝ)
      = coulombEnergy y
        - ∑ i : Fin 7, ∑ j ∈ Finset.Ioi i, cls3 HA HB HC i j ⟪y i, y j⟫_ℝ := by
    rw [energy_eq_sum hy, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_sub_distrib ..
  have htot : ∑ i : Fin 7, ∑ j ∈ Finset.Ioi i,
      (phi ⟪y i, y j⟫_ℝ - cls3 HA HB HC i j ⟪y i, y j⟫_ℝ) ≤ δ := by
    rw [hsplit]; linarith
  -- each slack is at most the total slack, hence at most `δ`
  have hsl : ∀ i j, i < j →
      phi ⟪y i, y j⟫_ℝ - cls3 HA HB HC i j ⟪y i, y j⟫_ℝ ≤ δ := by
    intro i j hij
    have h1 : phi ⟪y i, y j⟫_ℝ - cls3 HA HB HC i j ⟪y i, y j⟫_ℝ
        ≤ ∑ j ∈ Finset.Ioi i, (phi ⟪y i, y j⟫_ℝ - cls3 HA HB HC i j ⟪y i, y j⟫_ℝ) :=
      Finset.single_le_sum (f := fun j => phi ⟪y i, y j⟫_ℝ - cls3 HA HB HC i j ⟪y i, y j⟫_ℝ)
        (fun j hj => hnn i j hj) (Finset.mem_Ioi.2 hij)
    have h2 : ∑ j ∈ Finset.Ioi i, (phi ⟪y i, y j⟫_ℝ - cls3 HA HB HC i j ⟪y i, y j⟫_ℝ)
        ≤ ∑ i : Fin 7, ∑ j ∈ Finset.Ioi i,
          (phi ⟪y i, y j⟫_ℝ - cls3 HA HB HC i j ⟪y i, y j⟫_ℝ) :=
      Finset.single_le_sum
        (f := fun i => ∑ j ∈ Finset.Ioi i,
          (phi ⟪y i, y j⟫_ℝ - cls3 HA HB HC i j ⟪y i, y j⟫_ℝ))
        (fun i _ => Finset.sum_nonneg fun j hj => hnn i j hj) (Finset.mem_univ i)
    linarith
  have hcl : ∀ i j, i < j →
      cls3 (fun t => |t + 1| ≤ τ) (fun t => |t| ≤ τ)
        (fun t => |t - c1| ≤ τ ∨ |t - c2| ≤ τ) i j ⟪y i, y j⟫_ℝ :=
    fun i j hij => (hpf i j hij).2 (hsl i j hij)
  have hAp : |⟪y 0, y 1⟫_ℝ + 1| ≤ τ := by
    have h := hcl 0 1 (by decide)
    simpa [cls3] using h
  have hBp : ∀ k : Fin 7, k.val ≤ 1 → ∀ r : Fin 7, 2 ≤ r.val → k < r → |⟪y k, y r⟫_ℝ| ≤ τ := by
    intro k hk r hr hkr
    have h := hcl k r hkr
    have h1 : ¬ (k.val ≤ 1 ∧ r.val ≤ 1) := by omega
    have h2 : k.val ≤ 1 ∨ r.val ≤ 1 := Or.inl hk
    simpa only [cls3, h1, h2, ite_false, ite_true] using h
  have hCp : ∀ r r' : Fin 7, 2 ≤ r.val → r < r' →
      |⟪y r, y r'⟫_ℝ - c1| ≤ τ ∨ |⟪y r, y r'⟫_ℝ - c2| ≤ τ := by
    intro r r' hr hrr'
    have h := hcl r r' hrr'
    have hr' : 2 ≤ r'.val := by
      have : r.val < r'.val := hrr'
      omega
    have h1 : ¬ (r.val ≤ 1 ∧ r'.val ≤ 1) := by omega
    have h2 : ¬ (r.val ≤ 1 ∨ r'.val ≤ 1) := by omega
    simpa only [cls3, h1, h2, ite_false] using h
  obtain ⟨σ, hσ⟩ := hrig y hy.1 hAp
    (fun r hr => hBp 0 (by simp) r hr (by rw [Fin.lt_def]; simp; omega))
    (fun r hr => hBp 1 (by simp) r hr (by rw [Fin.lt_def]; simp; omega)) hCp
  exact TwoRegime.local_of_windowA hL hy σ (inWindow_of_close hσ)

end Tube

end Glue
end ThomsonN7

end Asm_Glue2

section Asm_Glue2b
namespace ThomsonN7
namespace Glue
section TubeFromT4
open scoped RealInnerProductSpace

end TubeFromT4
end Glue
end ThomsonN7

end Asm_Glue2b

section Asm_Glue3
/-!
# Glue3: the typed three-point bound (`Typed7`) feeds the cap / slab glue (`Glue1`, `Glue2`)

`ThreePoint.typed7_bound` bounds `e` by the typed double sum `∑ i<j, H7 HA HB HC i j ⟪x i, x j⟫`.
Here we identify `H7` with the class selector `Glue.cls3` (poles are the indices `0, 1`) and
restate the bound in exactly the shape needed by `Glue.cap_of_typed`, `Glue.cap_of_typed_tube`
and `Glue.slab_of_typed`.
-/

namespace ThomsonN7
namespace Glue

section Bridge

open scoped InnerProductSpace
open Base

end Bridge

section Assembly

open scoped InnerProductSpace
open Base

end Assembly

end Glue
end ThomsonN7

end Asm_Glue3

section Asm_Glue4
/-!
# Glue4: the final interface (`CapSpec`, `SlabSpec`) and the assembly `seven_of_specs`

The near-sharp cap and the margin slabs are certified by *typed* three-point data
(`Typed7`): PSD blocks `FP FR`, class minorants `HA HB HC`, multipliers `ψBa ψCb`, constants
`cal cbe`, together with one-dimensional facts on the minorants.  `CapSpec a0` (resp.
`SlabSpec lo hi`) is the proposition "such data exist"; every certificate producer has to prove
one of these propositions and nothing else.  `seven_of_specs` is the assembly: a cap spec at
`a 0` and slab specs on `[a k, a (k+1)]` for `k < K`, with `a K ≥ -9/10`, give both Challenge
statements for `N = 7`.

The tube-rigidity hypothesis of the near-sharp cap and the local (Regime B) statement are
discharged here once and for all (`Glue.tubeRigid_of_le`, `Glue.localGramA_of_le`).
-/

namespace ThomsonN7
namespace Glue

section Final

open scoped InnerProductSpace
open Base

/-- A cap specification proves the cap claim for minimal-pair configurations. -/
theorem capSpec_sound {a0 : ℝ} (h : CapSpec a0) :
    ∀ y ∈ SphereConfig 7, ⟪y 0, y 1⟫_ℝ ≤ a0 →
      (∀ i j, i ≠ j → ⟪y 0, y 1⟫_ℝ ≤ ⟪y i, y j⟫_ℝ) → Concl y := by
  obtain ⟨e, δ, τ, HA, HB, HC, hτ, hEδ, hTB, hA, hB, hC⟩ := h
  exact cap_of_typed_tube HA HB HC (localGramA_of_le hτ) (tubeRigid_of_le (hτ.trans (by norm_num)))
    (fun y hy hle hmin => hTB y hy hle hmin) hEδ hA hB hC

end Final

end Glue
end ThomsonN7

end Asm_Glue4

section Asm_EPEnc
/-!  agent9: 40-digit enclosure of the minimal energy `E(P)` (for the near-sharp cap route).  -/

namespace ThomsonN7
namespace Glue
section EPEnc
open Real

end EPEnc
end Glue
end ThomsonN7

end Asm_EPEnc

section Asm_Coerce
/-!
# One-dimensional facts for the typed cap / slab certificates (CoerceCert)

The typed three-point bound uses class minorants `H_cls ≤ phi` of the pair potential
`phi t = (√(2 - 2t))⁻¹`.  For a polynomial `H = Q / Dq` write `y = √(2 - 2t) / 2 ∈ (0, 1]`, so
`t = 1 - 2 y²`, `phi = 1 / (2 y)` and

  `phi t - H t = F(y) / (2 y Dq)`,   `F(y) = Dq - 2 y Q(1 - 2 y²)`,

a *polynomial* in `y` (no square roots, no sign case split).  Hence

* `H ≤ phi` on a `y`-interval is the polynomial inequality `F ≥ 0` (`PlainCert`);
* exact double contact at a rational node `y = p / q` is the factorisation `F = (q y - p)² G`
  (`Contact1`; two nodes: `Contact2`; simple contact at the boundary `y = 1`: `ContactA`), and
  `G ≥ g0 > 0` gives *coercivity*: `phi - H ≤ δ` forces `y` (hence `t`) close to the node.

Positivity of a polynomial on a rational `y`-interval is certified by exact Bernstein pieces
(`BPiece`), checked by list arithmetic in the kernel (no SDP data, no rounding).
-/

namespace ThomsonN7
namespace Glue
namespace Coerce

open CutOneD Base

/-! ## A. Polynomial helpers and Bernstein pieces -/

/-! ## B. The substitution `y = √(2 - 2t) / 2` -/

/-! ## C. Plain certificates: `H ≤ phi` on a `y`-interval -/

/-! ## D. Contact certificates with coercivity -/

/-! ## E. Shapes of the hypotheses `hA hB hC` of `cap_of_typed_tube7` and closeness of the nodes -/

end Coerce
end Glue
end ThomsonN7

end Asm_Coerce

section Asm_Coerce2
/-!
# Relaxed contact certificates (Coerce2)

`Coerce.Contact1` / `Contact2` need an *exact* double root of `F` at a rational node, which integer
SDP data cannot provide.  Here the factorisation is relaxed to

  `s · F = (q y - p)² · G + R`   (resp. `(q1 y - p1)² (q2 y - p2)² · G + R`)

with integers `s > 0`, polynomials `G, R` with `G ≥ g0 > 0` and `R ≥ 0` on `[0, 1]` (both by exact
Bernstein chains).  Then `F ≥ 0` on `[0, 1]` (so `H ≤ phi`), and `F ≤ 2 Dq δ` forces
`g0 (q y - p)² ≤ 2 s Dq δ`, i.e. the same coercivity as in the exact case with `Dq` replaced by
`s Dq`.
-/

namespace ThomsonN7
namespace Glue
namespace Coerce

open CutOneD Base

/-! ## A. One node -/

/-! ## B. Two nodes -/

end Coerce
end Glue
end ThomsonN7

end Asm_Coerce2

section Asm_CertF
/-! # Fast (linear-traversal) checking of sum-of-squares blocks

The blocks `⟨d, l, Δ⟩` of `Cert1` are read by random access (`List.getD`), which costs `O(r³)`
kernel steps per block.  Here the same quadratic form and the same positivity check are
implemented by traversing the coefficient lists once, and proved equivalent to the random-access
versions.  Also: packed integer data (one natural-number literal per array, decoded in the kernel).
-/

namespace ThomsonN7

open Kron Kron.Ex
namespace Cert

open ThreePoint

/-! ## Packed integer data -/

/-! ## The quadratic form of a block, by list traversal -/

/-! ## The positivity check, by list traversal -/

end Cert
end ThomsonN7

end Asm_CertF

section Asm_CertT
namespace ThomsonN7

open Kron Kron.Ex
namespace Cert

open ThreePoint

/-! ## Multiplier atoms of the typed certificates -/

/-! ## Kronecker values of the quadratic form of a block -/

/-! ## Size bounds of packed blocks -/

/-! ### Degrees -/

/-! ## Analytic bounds of typed blocks -/

/-! ## Sums of expressions -/

/-! ## The hybrid check -/

end Cert
end ThomsonN7

namespace ThomsonN7

open Kron Kron.Ex
namespace Cert

/-! # Flat (Nat-only inner loops) evaluation of the quadratic form of a packed block -/

end Cert
end ThomsonN7

namespace ThomsonN7

open Kron Kron.Ex
namespace Cert

open ThreePoint
open scoped RealInnerProductSpace

/-! ## One-variable polynomials, marginals, kernel sums -/

/-! ## The three type slacks, scaled to integer polynomials -/

section RealSide

variable (K : ℕ) (m : ℕ → ℕ) (Lam : ℕ) (blP blR : ℕ → Blk)

end RealSide

/-! ## The certificate -/

namespace TCert

variable (cf : TCert)

/-! ### The real data of a certificate -/

end TCert

end Cert
end ThomsonN7

end Asm_CertT

section Asm_SlabHead
/-!
# One-dimensional facts for the typed slab certificates: `H ≤ φ` on an interval

`φ(t) = (√(2 - 2t))⁻¹`.  For `t < 1` put `y = √((1 - t)/2) > 0`, so that `t = 1 - 2 y²` and
`φ(t) = 1/(2y)`.  A polynomial `H(t) = Q(t)/Lam` satisfies `H ≤ φ` iff `q(y) = Lam - 2 y Q(1 - 2y²) ≥ 0`.

A certificate for `q ≥ 0` on `{ν₂ y² ≤ μ₂}` (i.e. `t ≥ lo`) or `{ν₂ y² ≤ μ₂, μ₁ ≤ ν₁ y²}`
(i.e. `lo ≤ t ≤ hi`) is an exact polynomial identity

  `m · Lam · q(y) = Σ_T mult_T(y) · Σ (weight · square)`

where `mult_T` is a product of a subset of the atoms `y`, `μ₂ - ν₂ y²`, `ν₁ y² - μ₁`, and all
weights are natural numbers.  The identity is checked by kernel evaluation of integer polynomials.
-/

namespace ThomsonN7
namespace SlabOneD

/-! ## Fast check by evaluation at a large integer point (Kronecker substitution)

If an integer polynomial `R` satisfies `R(X) = 0` and all its coefficients have absolute value
`< X`, then `R = 0`.  The coefficient bound is obtained from `ℓ¹`-norm majorants along the same
expression tree as the identity, so the kernel only evaluates a few hundred big-integer operations
instead of expanding all polynomial products. -/

end SlabOneD
end ThomsonN7

end Asm_SlabHead

section Asm_Bridge
/-!
# Bridge: the certificate checker `Cert.TCert.sound_lo` feeds `Glue.SlabSpec` / `Glue.CapSpec`

`TCert.sound_lo` bounds `ef` by the typed double sum `∑ i<j, H7 HAf HBf HCf i j ⟪x i, x j⟫`.
Here we restate it with the class selector `Glue.cls3` (via `Glue3.sum_H7_eq_sum_cls3`) and, for a
certificate whose four boolean checks hold, produce the final interface of `Glue4`.  The remaining
inputs are the one-dimensional facts about the minorants (`HAf ≤ phi`, ...) and the numerical
comparison of `ef` with the energy `E(P)`.
-/

namespace ThomsonN7
namespace Glue

section Bridge

open scoped InnerProductSpace
open Base

end Bridge

end Glue
end ThomsonN7

end Asm_Bridge

section Asm_Bridge1D
/-!
# Bridge1D: agent2's one-dimensional slab facts (`SlabOneD`) feed `Bridge`

`SlabOneD.peval Q t / Lam` is the polynomial `polyR Lam Q t` of `CertT`; a generated slab
`SlabOneD.Slab_x.HA_le_phi` therefore gives `HAf ≤ phi` on the slab of a certificate whose
`HA`, `Lam` are the data of `Slab_x.certHA`.
-/

namespace ThomsonN7
namespace Glue

section Bridge1D

open scoped InnerProductSpace
open Base

end Bridge1D

end Glue
end ThomsonN7

end Asm_Bridge1D

section Asm_Bridge2
/-!
# Bridge2: near-sharp cap specification from a certificate and its contact factorisations

`Bridge.capSpec_of_tcert` asks for coercive one-dimensional facts about the three minorants
`HAf, HBf, HCf` of a cap certificate.  `Coerce` produces exactly these facts from an exact
factorisation of `F = Dq - 2 y Q(1 - 2 y²)` at rational `y`-nodes (`ContactA`, `Contact1`,
`Contact2`).  Here the two are glued: the contact data are attached to a certificate `cf` by the
equalities `c.Q = cf.HX`, `c.Dq = cf.Lam`.
-/

namespace ThomsonN7
namespace Glue

section Bridge2

open scoped InnerProductSpace
open Base

end Bridge2

end Glue
end ThomsonN7

end Asm_Bridge2

section Asm_Bridge3
/-!
# Bridge3: near-sharp cap specification with relaxed contacts

Same as `Bridge2.capSpec_of_contacts`, but the pole--ring and ring--ring minorants come with the
*relaxed* factorisations `s F = (q y - p)² G + R` (`Coerce.Contact1R`, `Coerce.Contact2R`), which
integer SDP data can satisfy; the pole--pole minorant keeps the exact simple contact at `y = 1`.
-/

namespace ThomsonN7
namespace Glue

section Bridge3

open scoped InnerProductSpace
open Base

end Bridge3

end Glue
end ThomsonN7

end Asm_Bridge3

section Asm_cap_tc
namespace ThomsonN7
open Kron Kron.Ex
namespace Cert
open ThreePoint

end Cert
end ThomsonN7

end Asm_cap_tc

section Asm_cap_ct
namespace ThomsonN7
namespace Final

end Final
end ThomsonN7

end Asm_cap_ct

section Asm_cap_capspec
namespace ThomsonN7
namespace Final

end Final
end ThomsonN7

end Asm_cap_capspec

section Asm_s99_98_tc
namespace ThomsonN7
open Kron Kron.Ex
namespace Cert
open ThreePoint

end Cert
end ThomsonN7

end Asm_s99_98_tc

section Asm_s99_98_1d
namespace ThomsonN7
namespace SlabOneD

namespace Slab_s99_98

end Slab_s99_98

end SlabOneD
end ThomsonN7

end Asm_s99_98_1d

section Asm_s99_98_spec
namespace ThomsonN7
namespace Final

end Final
end ThomsonN7

end Asm_s99_98_spec

section Asm_s98_96_tc
namespace ThomsonN7
open Kron Kron.Ex
namespace Cert
open ThreePoint

end Cert
end ThomsonN7

end Asm_s98_96_tc

section Asm_s98_96_1d
namespace ThomsonN7
namespace SlabOneD

namespace Slab_s98_96

end Slab_s98_96

end SlabOneD
end ThomsonN7

end Asm_s98_96_1d

section Asm_s98_96_spec
namespace ThomsonN7
namespace Final

end Final
end ThomsonN7

end Asm_s98_96_spec

section Asm_s96_94_tc
namespace ThomsonN7
open Kron Kron.Ex
namespace Cert
open ThreePoint

end Cert
end ThomsonN7

end Asm_s96_94_tc

section Asm_s96_94_1d
namespace ThomsonN7
namespace SlabOneD

namespace Slab_s96_94

end Slab_s96_94

end SlabOneD
end ThomsonN7

end Asm_s96_94_1d

section Asm_s96_94_spec
namespace ThomsonN7
namespace Final

end Final
end ThomsonN7

end Asm_s96_94_spec

section Asm_s94_93_tc
namespace ThomsonN7
open Kron Kron.Ex
namespace Cert
open ThreePoint

end Cert
end ThomsonN7

end Asm_s94_93_tc

section Asm_s94_93_1d
namespace ThomsonN7
namespace SlabOneD

namespace Slab_s94_93

end Slab_s94_93

end SlabOneD
end ThomsonN7

end Asm_s94_93_1d

section Asm_s94_93_spec
namespace ThomsonN7
namespace Final

end Final
end ThomsonN7

end Asm_s94_93_spec

section Asm_s93_90_tc
namespace ThomsonN7
open Kron Kron.Ex
namespace Cert
open ThreePoint

end Cert
end ThomsonN7

end Asm_s93_90_tc

section Asm_s93_90_1d
namespace ThomsonN7
namespace SlabOneD

namespace Slab_s93_90

end Slab_s93_90

end SlabOneD
end ThomsonN7

end Asm_s93_90_1d

section Asm_s93_90_spec
namespace ThomsonN7
namespace Final

end Final
end ThomsonN7

end Asm_s93_90_spec

section Asm_Final
namespace ThomsonN7
namespace Final

end Final
end ThomsonN7

end Asm_Final

namespace ThomsonN7

end ThomsonN7


open ThomsonN7 in
theorem solution {a0 : ℝ} (h : Glue.CapSpec a0) :
    ∀ y ∈ SphereConfig 7, inner ℝ (y 0) (y 1) ≤ a0 →
      (∀ i j, i ≠ j → inner ℝ (y 0) (y 1) ≤ inner ℝ (y i) (y j)) → Glue.Concl y :=
  ThomsonN7.Glue.capSpec_sound h
