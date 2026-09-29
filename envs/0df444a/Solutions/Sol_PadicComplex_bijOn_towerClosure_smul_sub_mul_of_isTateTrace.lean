-- Prove2me | solution 1 for PadicComplex.bijOn_towerClosure_smul_sub_mul_of_isTateTrace
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/9f6195e7-21e4-5441-9f5f-e167eecf2807

import Mathlib
import Definitions.Def_PadicComplex_GaloisAction
import Definitions.Def_PadicComplex_TateTrace
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_PadicComplex_bijOn_towerClosure_smul_sub_mul_of_isTateTrace

set_option autoImplicit false

noncomputable section

namespace TP7

open UniformSpace
open scoped Pointwise NNReal

variable {p : ℕ} [Fact p.Prime]

local notation "Ω" => PadicAlgCl p
local notation "Γ" => (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p)

section levels

variable (p)
variable (Km : ℕ → IntermediateField ℚ_[p] (PadicAlgCl p))

def coeL : (PadicAlgCl p) →ₗ[ℚ_[p]] ℂ_[p] :=
  (IsScalarTower.toAlgHom ℚ_[p] (PadicAlgCl p) ℂ_[p]).toLinearMap

@[scoped simp] lemma coeL_apply (x : Ω) : coeL p x = (x : ℂ_[p]) := rfl

def lev (n : ℕ) : Submodule ℚ_[p] ℂ_[p] :=
  LinearMap.range ((coeL p).comp (Km n).val.toLinearMap)

lemma mem_lev_iff {n : ℕ} {x : ℂ_[p]} : x ∈ lev p Km n ↔ ∃ k : Km n, ((k : Ω) : ℂ_[p]) = x := by
  simp [lev, LinearMap.mem_range]

lemma coe_mem_lev {n : ℕ} (k : Km n) : ((k : Ω) : ℂ_[p]) ∈ lev p Km n :=
  (mem_lev_iff p Km).2 ⟨k, rfl⟩

lemma coe_lev (n : ℕ) :
    (lev p Km n : Set ℂ_[p]) = Set.range fun k : Km n => ((k : Ω) : ℂ_[p]) := by
  ext x
  simp [mem_lev_iff]

variable {Km} in
lemma lev_mono (hmono : Monotone Km) : Monotone (lev p Km) := by
  intro a b hab x hx
  obtain ⟨k, rfl⟩ := (mem_lev_iff p Km).1 hx
  exact (mem_lev_iff p Km).2 ⟨⟨k, hmono hab k.2⟩, rfl⟩

scoped instance lev_finiteDimensional (n : ℕ) [FiniteDimensional ℚ_[p] (Km n)] :
    FiniteDimensional ℚ_[p] (lev p Km n) := by
  unfold lev; infer_instance

def Xsub : Submodule ℚ_[p] ℂ_[p] := (⨆ n, lev p Km n).topologicalClosure

variable {Km} in
lemma coe_Xsub (hmono : Monotone Km) :
    (Xsub p Km : Set ℂ_[p]) = PadicComplex.towerClosure p Km := by
  unfold Xsub PadicComplex.towerClosure
  rw [Submodule.topologicalClosure_coe, Submodule.coe_iSup_of_directed _ (lev_mono p hmono).directed_le]
  congr 1

variable {Km} in
lemma mem_X_iff (hmono : Monotone Km) {x : ℂ_[p]} :
    x ∈ PadicComplex.towerClosure p Km ↔ x ∈ Xsub p Km := by
  rw [← SetLike.mem_coe, coe_Xsub p hmono]

variable {Km} in
lemma lev_le_Xsub (n : ℕ) : lev p Km n ≤ Xsub p Km :=
  (le_iSup (lev p Km) n).trans (Submodule.le_topologicalClosure _)

variable {Km} in
lemma lev_subset_X (hmono : Monotone Km) (n : ℕ) :
    (lev p Km n : Set ℂ_[p]) ⊆ PadicComplex.towerClosure p Km := by
  rw [← coe_Xsub p hmono]
  exact lev_le_Xsub p n

lemma isClosed_X : IsClosed (PadicComplex.towerClosure p Km) := isClosed_closure

end levels

structure Setup (p : ℕ) [Fact p.Prime] (Km : ℕ → IntermediateField ℚ_[p] (PadicAlgCl p)) (m : ℕ) (d : ℝ)
    (R : ℂ_[p] → ℂ_[p]) (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) : Prop where
  mono : Monotone Km
  fin : ∀ n, FiniteDimensional ℚ_[p] (Km n)
  tr : PadicComplex.IsTateTrace p Km m d R
  hσ : σ ∈ (Km m).fixingSubgroup
  hσ' : σ ∉ (Km (m + 1)).fixingSubgroup
  stab : ∀ n, ∀ y ∈ Km n, σ y ∈ Km n

def D (d : ℝ) : ℝ := max d 0

lemma D_nonneg (d : ℝ) : 0 ≤ D d := le_max_right _ _

def Tσ (σ : Γ) : ℂ_[p] →ₗ[ℚ_[p]] ℂ_[p] := DistribSMul.toLinearMap ℚ_[p] ℂ_[p] σ - LinearMap.id

lemma Tσ_apply (σ : Γ) (x : ℂ_[p]) : Tσ σ x = σ • x - x := rfl

namespace Setup

set_option linter.unusedSectionVars false

variable {Km : ℕ → IntermediateField ℚ_[p] (PadicAlgCl p)} {m : ℕ} {d : ℝ} {R : ℂ_[p] → ℂ_[p]}
  {σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p} (H : Setup p Km m d R σ)
include H

local notation "X" => PadicComplex.towerClosure p Km

lemma zero_mem_X : (0 : ℂ_[p]) ∈ X := by
  have := subset_closure (Set.mem_iUnion.2 ⟨m, ⟨(0 : Km m), rfl⟩⟩ :
    (fun k : Km m => ((k : Ω) : ℂ_[p])) 0 ∈ ⋃ n, Set.range fun k : Km n => ((k : Ω) : ℂ_[p]))
  simp at this
  exact this

lemma add_mem_X {x y : ℂ_[p]} (hx : x ∈ X) (hy : y ∈ X) : x + y ∈ X := by
  rw [mem_X_iff p H.mono] at hx hy ⊢; exact Submodule.add_mem _ hx hy

lemma sub_mem_X {x y : ℂ_[p]} (hx : x ∈ X) (hy : y ∈ X) : x - y ∈ X := by
  rw [mem_X_iff p H.mono] at hx hy ⊢; exact Submodule.sub_mem _ hx hy

lemma neg_mem_X {x : ℂ_[p]} (hx : x ∈ X) : -x ∈ X := by
  rw [mem_X_iff p H.mono] at hx ⊢; exact Submodule.neg_mem _ hx

lemma smul_mem_X (q : ℚ_[p]) {x : ℂ_[p]} (hx : x ∈ X) : q • x ∈ X := by
  rw [mem_X_iff p H.mono] at hx ⊢; exact Submodule.smul_mem _ q hx

lemma R_zero : R 0 = 0 := by
  have := H.tr.map_add 0 H.zero_mem_X 0 H.zero_mem_X
  simpa using this

lemma R_neg {x : ℂ_[p]} (hx : x ∈ X) : R (-x) = -R x := by
  have := H.tr.map_add x hx (-x) (H.neg_mem_X hx)
  rw [add_neg_cancel, H.R_zero] at this
  linear_combination -this

lemma R_add {x y : ℂ_[p]} (hx : x ∈ X) (hy : y ∈ X) : R (x + y) = R x + R y :=
  H.tr.map_add x hx y hy

lemma R_sub {x y : ℂ_[p]} (hx : x ∈ X) (hy : y ∈ X) : R (x - y) = R x - R y := by
  rw [sub_eq_add_neg, H.R_add hx (H.neg_mem_X hy), H.R_neg hy, sub_eq_add_neg]

lemma R_smul (q : ℚ_[p]) {x : ℂ_[p]} (hx : x ∈ X) : R (q • x) = q • R x := by
  have h := H.tr.map_mul_left (algebraMap ℚ_[p] (Km m) q) x hx
  have hc : (((algebraMap ℚ_[p] (Km m) q : Km m) : Ω) : ℂ_[p]) = algebraMap ℚ_[p] ℂ_[p] q := by
    change algebraMap Ω ℂ_[p] (algebraMap ℚ_[p] Ω q) = _
    exact (IsScalarTower.algebraMap_apply ℚ_[p] Ω ℂ_[p] q).symm
  rw [hc] at h
  rw [Algebra.smul_def, Algebra.smul_def, h]

lemma R_mem_lev {x : ℂ_[p]} (hx : x ∈ X) : R x ∈ lev p Km m := by
  obtain ⟨k, hk⟩ := H.tr.exists_eq_coe x hx
  rw [hk]; exact coe_mem_lev p Km k

lemma R_mem_X {x : ℂ_[p]} (hx : x ∈ X) : R x ∈ X :=
  lev_subset_X p H.mono m (H.R_mem_lev hx)

lemma R_of_mem_lev {x : ℂ_[p]} (hx : x ∈ lev p Km m) : R x = x := by
  obtain ⟨k, rfl⟩ := (mem_lev_iff p Km).1 hx
  exact H.tr.apply_coe k

lemma R_R {x : ℂ_[p]} (hx : x ∈ X) : R (R x) = R x :=
  H.R_of_mem_lev (H.R_mem_lev hx)

lemma R_gal {x : ℂ_[p]} (hx : x ∈ X) : R (σ • x) = R x := H.tr.apply_smul σ H.hσ x hx

lemma est {x : ℂ_[p]} (hx : x ∈ X) : ‖x - R x‖ ≤ D d * ‖σ • x - x‖ :=
  (H.tr.norm_sub_apply_le σ H.hσ H.hσ' x hx).trans
    (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))

lemma norm_R_le {x : ℂ_[p]} (hx : x ∈ X) : ‖R x‖ ≤ (1 + 2 * D d) * ‖x‖ := by
  have h1 := H.est hx
  have h2 : ‖σ • x - x‖ ≤ 2 * ‖x‖ := by
    calc ‖σ • x - x‖ ≤ ‖σ • x‖ + ‖x‖ := norm_sub_le _ _
      _ = 2 * ‖x‖ := by rw [PadicComplex.norm_smul_eq]; ring
  have h3 : ‖R x‖ ≤ ‖x‖ + ‖x - R x‖ := by
    calc ‖R x‖ = ‖x - (x - R x)‖ := by rw [sub_sub_cancel]
      _ ≤ ‖x‖ + ‖x - R x‖ := norm_sub_le _ _
  have hD := D_nonneg d
  nlinarith [norm_nonneg x]

lemma norm_R_sub_R_le {x y : ℂ_[p]} (hx : x ∈ X) (hy : y ∈ X) :
    ‖R x - R y‖ ≤ (1 + 2 * D d) * ‖x - y‖ := by
  rw [← H.R_sub hx hy]
  exact H.norm_R_le (H.sub_mem_X hx hy)

lemma gal_mem_lev {n : ℕ} {x : ℂ_[p]} (hx : x ∈ lev p Km n) : σ • x ∈ lev p Km n := by
  obtain ⟨k, rfl⟩ := (mem_lev_iff p Km).1 hx
  rw [PadicComplex.smul_coe]
  exact (mem_lev_iff p Km).2 ⟨⟨σ k, H.stab n k k.2⟩, rfl⟩

lemma gal_mem_X {x : ℂ_[p]} (hx : x ∈ X) : σ • x ∈ X := by
  have hU : (fun y : ℂ_[p] => σ • y) '' (⋃ n, Set.range fun k : Km n => ((k : Ω) : ℂ_[p])) ⊆
      ⋃ n, Set.range fun k : Km n => ((k : Ω) : ℂ_[p]) := by
    rintro _ ⟨y, hy, rfl⟩
    obtain ⟨n, k, rfl⟩ := Set.mem_iUnion.1 hy
    refine Set.mem_iUnion.2 ⟨n, ⟨σ k, H.stab n k k.2⟩, ?_⟩
    simp [PadicComplex.smul_coe]
  have h := image_closure_subset_closure_image (PadicComplex.continuous_smul_left p σ)
    (s := ⋃ n, Set.range fun k : Km n => ((k : Ω) : ℂ_[p])) ⟨x, hx, rfl⟩
  exact closure_mono hU h

lemma gal_of_mem_lev {x : ℂ_[p]} (hx : x ∈ lev p Km m) : σ • x = x := by
  obtain ⟨k, rfl⟩ := (mem_lev_iff p Km).1 hx
  rw [PadicComplex.smul_coe, (IntermediateField.mem_fixingSubgroup_iff _ _).1 H.hσ _ k.2]

lemma T_mem_X {x : ℂ_[p]} (hx : x ∈ X) : Tσ σ x ∈ X := H.sub_mem_X (H.gal_mem_X hx) hx

lemma R_T {x : ℂ_[p]} (hx : x ∈ X) : R (Tσ σ x) = 0 := by
  rw [Tσ_apply, H.R_sub (H.gal_mem_X hx) hx, H.R_gal hx, sub_self]

lemma norm_T_le (x : ℂ_[p]) : ‖Tσ σ x‖ ≤ 2 * ‖x‖ := by
  rw [Tσ_apply]
  calc ‖σ • x - x‖ ≤ ‖σ • x‖ + ‖x‖ := norm_sub_le _ _
    _ = 2 * ‖x‖ := by rw [PadicComplex.norm_smul_eq]; ring

def X0 : Submodule ℚ_[p] ℂ_[p] where
  carrier := {x | x ∈ X ∧ R x = 0}
  zero_mem' := ⟨H.zero_mem_X, H.R_zero⟩
  add_mem' := by
    rintro x y ⟨hx, hRx⟩ ⟨hy, hRy⟩
    exact ⟨H.add_mem_X hx hy, by rw [H.R_add hx hy, hRx, hRy, add_zero]⟩
  smul_mem' := by
    rintro q x ⟨hx, hRx⟩
    exact ⟨H.smul_mem_X q hx, by rw [H.R_smul q hx, hRx, smul_zero]⟩

lemma mem_X0_iff {x : ℂ_[p]} : x ∈ H.X0 ↔ x ∈ X ∧ R x = 0 := Iff.rfl

lemma sub_R_mem_X0 {x : ℂ_[p]} (hx : x ∈ X) : x - R x ∈ H.X0 :=
  ⟨H.sub_mem_X hx (H.R_mem_X hx), by rw [H.R_sub hx (H.R_mem_X hx), H.R_R hx, sub_self]⟩

lemma T_mem_X0 {x : ℂ_[p]} (hx : x ∈ X) : Tσ σ x ∈ H.X0 := ⟨H.T_mem_X hx, H.R_T hx⟩

lemma norm_le_of_mem_X0 {x : ℂ_[p]} (hx : x ∈ H.X0) : ‖x‖ ≤ D d * ‖Tσ σ x‖ := by
  have h := H.est hx.1
  rwa [hx.2, sub_zero] at h

lemma isClosed_X0 : IsClosed (H.X0 : Set ℂ_[p]) := by
  refine isClosed_of_closure_subset fun x hx => ?_
  have hxX : x ∈ X :=
    (closure_mono (fun y (hy : y ∈ H.X0) => hy.1)) hx |> (isClosed_X p Km).closure_subset
  refine ⟨hxX, ?_⟩
  rw [← norm_eq_zero]
  refine le_antisymm (le_of_forall_pos_lt_add fun ε hε => ?_) (norm_nonneg _)
  have hL : 0 < 1 + 2 * D d := by have := D_nonneg d; linarith
  obtain ⟨y, hy, hxy⟩ := Metric.mem_closure_iff.1 hx (ε / (1 + 2 * D d)) (div_pos hε hL)
  have hy' : y ∈ H.X0 := hy
  calc ‖R x‖ = ‖R x - R y‖ := by rw [hy'.2, sub_zero]
    _ ≤ (1 + 2 * D d) * ‖x - y‖ := H.norm_R_sub_R_le hxX hy'.1
    _ < (1 + 2 * D d) * (ε / (1 + 2 * D d)) := by
        rw [← dist_eq_norm]; exact mul_lt_mul_of_pos_left hxy hL
    _ = 0 + ε := by rw [zero_add]; exact mul_div_cancel₀ ε hL.ne'

def V (n : ℕ) : Submodule ℚ_[p] ℂ_[p] := lev p Km n ⊓ H.X0

lemma V_le_lev (n : ℕ) : H.V n ≤ lev p Km n := inf_le_left

lemma V_le_X0 (n : ℕ) : H.V n ≤ H.X0 := inf_le_right

scoped instance V_finiteDimensional (n : ℕ) : FiniteDimensional ℚ_[p] (H.V n) := by
  haveI := H.fin n
  exact Submodule.finiteDimensional_of_le (H.V_le_lev n)

lemma T_mem_V {n : ℕ} {x : ℂ_[p]} (hx : x ∈ H.V n) : Tσ σ x ∈ H.V n :=
  ⟨Submodule.sub_mem _ (H.gal_mem_lev hx.1) hx.1, H.T_mem_X0 hx.2.1⟩

lemma T_eq_zero {x : ℂ_[p]} (hx : x ∈ H.X0) (h : Tσ σ x = 0) : x = 0 := by
  have := H.norm_le_of_mem_X0 hx
  rw [h, norm_zero, mul_zero] at this
  exact norm_le_zero_iff.1 this

lemma T_surj_V (n : ℕ) {y : ℂ_[p]} (hy : y ∈ H.V n) : ∃ x ∈ H.V n, Tσ σ x = y := by
  let T' : H.V n →ₗ[ℚ_[p]] H.V n := (Tσ σ).restrict fun x hx => H.T_mem_V hx
  have hinj : Function.Injective T' := by
    intro a b hab
    apply Subtype.ext
    have h1 : Tσ σ (a - b : H.V n) = 0 := by
      have := congrArg Subtype.val hab
      simp only [T', LinearMap.coe_restrict_apply] at this
      rw [Submodule.coe_sub, map_sub, this, sub_self]
    have := H.T_eq_zero (H.V_le_X0 n (a - b).2) h1
    rwa [Submodule.coe_sub, sub_eq_zero] at this
  obtain ⟨x, hx⟩ := LinearMap.surjective_of_injective hinj ⟨y, hy⟩
  exact ⟨x, x.2, by simpa [T'] using congrArg Subtype.val hx⟩

lemma dense_V {y : ℂ_[p]} (hy : y ∈ H.X0) {ε : ℝ} (hε : 0 < ε) :
    ∃ n, ∃ z ∈ H.V n, ‖y - z‖ < ε := by
  have hL : 0 < 2 + 2 * D d := by have := D_nonneg d; linarith
  obtain ⟨w, hw, hyw⟩ := Metric.mem_closure_iff.1 hy.1 (ε / (2 + 2 * D d)) (div_pos hε hL)
  obtain ⟨n₀, k, rfl⟩ := Set.mem_iUnion.1 hw
  set w : ℂ_[p] := ((k : Ω) : ℂ_[p]) with hwdef
  have hwlev : w ∈ lev p Km (max n₀ m) := lev_mono p H.mono (le_max_left _ _) (coe_mem_lev p Km k)
  have hwX : w ∈ X := lev_subset_X p H.mono _ hwlev
  refine ⟨max n₀ m, w - R w, ⟨Submodule.sub_mem _ hwlev ?_, H.sub_R_mem_X0 hwX⟩, ?_⟩
  · exact lev_mono p H.mono (le_max_right _ _) (H.R_mem_lev hwX)
  · have h1 : ‖R w‖ ≤ (1 + 2 * D d) * ‖y - w‖ := by
      have := H.norm_R_sub_R_le hwX hy.1
      rwa [hy.2, sub_zero, norm_sub_rev] at this
    rw [dist_eq_norm] at hyw
    calc ‖y - (w - R w)‖ = ‖(y - w) + R w‖ := by rw [sub_sub_eq_add_sub, add_sub_right_comm]
      _ ≤ ‖y - w‖ + ‖R w‖ := norm_add_le _ _
      _ ≤ ‖y - w‖ + (1 + 2 * D d) * ‖y - w‖ := by linarith
      _ = (2 + 2 * D d) * ‖y - w‖ := by ring
      _ < (2 + 2 * D d) * (ε / (2 + 2 * D d)) := mul_lt_mul_of_pos_left hyw hL
      _ = ε := mul_div_cancel₀ ε hL.ne'

def T0 : H.X0 → H.X0 := fun x => ⟨Tσ σ x, H.T_mem_X0 x.2.1⟩

@[scoped simp] lemma coe_T0 (x : H.X0) : (H.T0 x : ℂ_[p]) = Tσ σ x := rfl

scoped instance completeSpace_X0 : CompleteSpace H.X0 :=
  letI : IsClosed (H.X0 : Set ℂ_[p]) := H.isClosed_X0
  IsClosed.completeSpace_coe

lemma T0_antilipschitz : AntilipschitzWith (D d).toNNReal H.T0 := by
  refine AntilipschitzWith.of_le_mul_dist fun x y => ?_
  rw [Subtype.dist_eq, Subtype.dist_eq, dist_eq_norm, dist_eq_norm, coe_T0, coe_T0, ← map_sub,
    Real.coe_toNNReal _ (D_nonneg d)]
  exact H.norm_le_of_mem_X0 (Submodule.sub_mem _ x.2 y.2)

lemma T0_lipschitz : LipschitzWith 2 H.T0 := by
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  rw [Subtype.dist_eq, Subtype.dist_eq, dist_eq_norm, dist_eq_norm, coe_T0, coe_T0, ← map_sub]
  exact_mod_cast H.norm_T_le _

lemma T0_bijective : Function.Bijective H.T0 := by
  refine ⟨fun a b hab => ?_, ?_⟩
  · apply Subtype.ext
    have h1 : Tσ σ (a - b : H.X0) = 0 := by
      have := congrArg Subtype.val hab
      rw [coe_T0, coe_T0] at this
      rw [Submodule.coe_sub, map_sub, this, sub_self]
    have := H.T_eq_zero (a - b).2 h1
    rwa [Submodule.coe_sub, sub_eq_zero] at this
  · have hclosed : IsClosed (Set.range H.T0) :=
      H.T0_antilipschitz.isClosed_range H.T0_lipschitz.uniformContinuous
    have hdense : ∀ y : H.X0, y ∈ closure (Set.range H.T0) := by
      intro y
      refine Metric.mem_closure_iff.2 fun ε hε => ?_
      obtain ⟨n, z, hz, hyz⟩ := H.dense_V y.2 hε
      obtain ⟨x, hx, rfl⟩ := H.T_surj_V n hz
      refine ⟨H.T0 ⟨x, H.V_le_X0 n hx⟩, ⟨_, rfl⟩, ?_⟩
      rwa [Subtype.dist_eq, dist_eq_norm]
    rw [hclosed.closure_eq] at hdense
    exact fun y => hdense y

def ρ : H.X0 → H.X0 := (Equiv.ofBijective H.T0 H.T0_bijective).symm

lemma T0_ρ (y : H.X0) : H.T0 (H.ρ y) = y := Equiv.ofBijective_apply_symm_apply _ _ _

lemma T_ρ (y : H.X0) : Tσ σ (H.ρ y : ℂ_[p]) = y := congrArg Subtype.val (H.T0_ρ y)

lemma norm_ρ_sub_ρ_le (y y' : H.X0) :
    ‖(H.ρ y : ℂ_[p]) - H.ρ y'‖ ≤ D d * ‖(y : ℂ_[p]) - y'‖ := by
  have h := H.norm_le_of_mem_X0 (Submodule.sub_mem _ (H.ρ y).2 (H.ρ y').2)
  rwa [map_sub, H.T_ρ, H.T_ρ] at h

section contraction

variable {μ : ℚ_[p]} (hμd : ‖μ - 1‖ * d < 1)
include hμd

lemma contraction_const_lt_one : ‖μ - 1‖ * D d < 1 := by
  unfold D
  rcases le_or_gt 0 d with hd | hd
  · rwa [max_eq_left hd]
  · rw [max_eq_right hd.le, mul_zero]; exact one_pos

lemma exists_smul_sub_smul_eq_of_mem_X0 {y : ℂ_[p]} (hy : y ∈ H.X0) :
    ∃ x ∈ H.X0, σ • x - μ • x = y := by

  let Φ : H.X0 → H.X0 := fun x =>
    H.ρ ⟨y + (μ - 1) • (x : ℂ_[p]), Submodule.add_mem _ hy (Submodule.smul_mem _ _ x.2)⟩
  set K : ℝ≥0 := ‖μ - 1‖₊ * (D d).toNNReal with hK
  have hKcoe : (K : ℝ) = ‖μ - 1‖ * D d := by
    rw [hK, NNReal.coe_mul, coe_nnnorm, Real.coe_toNNReal _ (D_nonneg d)]
  have hΦ : ContractingWith K Φ := by
    refine ⟨?_, LipschitzWith.of_dist_le_mul fun x x' => ?_⟩
    · rw [← NNReal.coe_lt_coe, hKcoe, NNReal.coe_one]
      exact H.contraction_const_lt_one hμd
    · rw [Subtype.dist_eq, Subtype.dist_eq, dist_eq_norm, dist_eq_norm, hKcoe]
      refine (H.norm_ρ_sub_ρ_le _ _).trans ?_
      rw [Subtype.coe_mk, Subtype.coe_mk, add_sub_add_left_eq_sub, ← smul_sub, norm_smul]
      nlinarith [norm_nonneg (μ - 1), norm_nonneg ((x : ℂ_[p]) - x'), D_nonneg d]
  haveI : Nonempty H.X0 := ⟨0⟩
  set x := ContractingWith.fixedPoint Φ hΦ with hxdef
  have hfix : Φ x = x := ContractingWith.fixedPoint_isFixedPt hΦ
  refine ⟨x, x.2, ?_⟩
  have h1 : Tσ σ (x : ℂ_[p]) = y + (μ - 1) • (x : ℂ_[p]) := by
    have := congrArg (fun z : H.X0 => (H.T0 z : ℂ_[p])) hfix
    simp only [Φ, coe_T0, H.T_ρ] at this
    exact this.symm
  rw [Tσ_apply] at h1
  rw [sub_smul, one_smul] at h1
  linear_combination h1

end contraction

end Setup
p2m_reactivate "P2MW.S_PadicComplex_bijOn_towerClosure_smul_sub_mul_of_isTateTrace.TP7.Setup"

end TP7
p2m_reactivate "P2MW.S_PadicComplex_bijOn_towerClosure_smul_sub_mul_of_isTateTrace.TP7.Setup P2MW.S_PadicComplex_bijOn_towerClosure_smul_sub_mul_of_isTateTrace.TP7"

open TP7 in
theorem solution
    (p : ℕ) [Fact p.Prime] (Km : ℕ → IntermediateField ℚ_[p] (PadicAlgCl p)) (hmono : Monotone Km)
    (hfin : ∀ n, FiniteDimensional ℚ_[p] (Km n))
    (m : ℕ) (d : ℝ) (R : ℂ_[p] → ℂ_[p]) (hR : PadicComplex.IsTateTrace p Km m d R)
    (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) (hσ : σ ∈ (Km m).fixingSubgroup)
    (hσ' : σ ∉ (Km (m + 1)).fixingSubgroup) (hstab : ∀ n, ∀ y ∈ Km n, σ y ∈ Km n)
    (μ : ℚ_[p]) (hμ : μ ≠ 1) (hμd : ‖μ - 1‖ * d < 1) :
    Set.BijOn (fun x : ℂ_[p] => σ • x - algebraMap ℚ_[p] ℂ_[p] μ * x)
      (PadicComplex.towerClosure p Km) (PadicComplex.towerClosure p Km) := by
  have H : Setup p Km m d R σ := ⟨hmono, hfin, hR, hσ, hσ', hstab⟩

  let S : ℂ_[p] →ₗ[ℚ_[p]] ℂ_[p] := DistribSMul.toLinearMap ℚ_[p] ℂ_[p] σ - μ • LinearMap.id
  have hS : ∀ x : ℂ_[p], σ • x - algebraMap ℚ_[p] ℂ_[p] μ * x = S x := fun x => by
    simp only [S, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply]
    rw [Algebra.smul_def μ x]
    rfl
  have hS' : ∀ x : ℂ_[p], S x = Tσ σ x - (μ - 1) • x := fun x => by
    rw [Tσ_apply, ← hS, sub_smul, one_smul, Algebra.smul_def]; ring
  simp_rw [hS]
  have hSX : ∀ x ∈ PadicComplex.towerClosure p Km, S x ∈ PadicComplex.towerClosure p Km := by
    intro x hx
    rw [hS']; exact H.sub_mem_X (H.T_mem_X hx) (H.smul_mem_X _ hx)
  have hSX0 : ∀ x ∈ H.X0, S x ∈ H.X0 := fun x hx => by
    rw [hS']; exact Submodule.sub_mem _ (H.T_mem_X0 hx.1) (Submodule.smul_mem _ _ hx)

  have hSlev : ∀ x ∈ lev p Km m, S x = (1 - μ) • x := fun x hx => by
    rw [← hS, H.gal_of_mem_lev hx, sub_smul, one_smul, Algebra.smul_def]
  have h1μ : (1 - μ : ℚ_[p]) ≠ 0 := sub_ne_zero.2 (Ne.symm hμ)
  have hlt : ‖μ - 1‖ * D d < 1 := H.contraction_const_lt_one hμd
  refine ⟨hSX, ?_, ?_⟩
  ·
    intro x hx x' hx' hxx'
    have hz : S (x - x') = 0 := by rw [map_sub]; exact sub_eq_zero.2 hxx'
    set z := x - x' with hzdef
    have hzX : z ∈ PadicComplex.towerClosure p Km := H.sub_mem_X hx hx'
    have hk : R z ∈ lev p Km m := H.R_mem_lev hzX
    have hz0 : z - R z ∈ H.X0 := H.sub_R_mem_X0 hzX
    have hdec : S z = (1 - μ) • R z + S (z - R z) := by
      conv_lhs => rw [← add_sub_cancel (R z) z]
      rw [map_add, hSlev _ hk]

    have hRk : (1 - μ) • R z = 0 := by
      have h := congrArg R hdec
      rw [hz, H.R_zero, H.R_add (H.smul_mem_X _ (H.R_mem_X hzX)) (hSX0 _ hz0).1, (hSX0 _ hz0).2,
        add_zero, H.R_smul _ (H.R_mem_X hzX), H.R_R hzX] at h
      exact h.symm
    have hk0 : R z = 0 := by
      rcases smul_eq_zero.1 hRk with h | h
      · exact absurd h h1μ
      · exact h
    rw [hk0, smul_zero, zero_add, sub_zero] at hdec

    rw [hk0, sub_zero] at hz0
    have hTz : Tσ σ z = (μ - 1) • z := by
      have := hS' z; rw [hz] at this; exact (sub_eq_zero.1 this.symm)
    have hest := H.norm_le_of_mem_X0 hz0
    rw [hTz, norm_smul] at hest
    have hz00 : ‖z‖ = 0 := by
      nlinarith [norm_nonneg z, norm_nonneg (μ - 1), D_nonneg d]
    exact sub_eq_zero.1 (norm_eq_zero.1 hz00)
  ·
    intro y hy
    have hk : R y ∈ lev p Km m := H.R_mem_lev hy
    have hy0 : y - R y ∈ H.X0 := H.sub_R_mem_X0 hy
    obtain ⟨x₀, hx₀, hx₀eq⟩ := H.exists_smul_sub_smul_eq_of_mem_X0 hμd hy0
    refine ⟨(1 - μ)⁻¹ • R y + x₀, H.add_mem_X (H.smul_mem_X _ (H.R_mem_X hy)) hx₀.1, ?_⟩
    show S _ = y
    have hSx₀ : S x₀ = y - R y := by rw [← hS, Algebra.smul_def] at *; exact hx₀eq
    rw [map_add, map_smul, hSlev _ hk, hSx₀, smul_smul, inv_mul_cancel₀ h1μ, one_smul,
      add_sub_cancel]

end
p2m_reactivate "P2MW.S_PadicComplex_bijOn_towerClosure_smul_sub_mul_of_isTateTrace.TP7.Setup P2MW.S_PadicComplex_bijOn_towerClosure_smul_sub_mul_of_isTateTrace.TP7"

end S_PadicComplex_bijOn_towerClosure_smul_sub_mul_of_isTateTrace
end P2MW
export P2MW.S_PadicComplex_bijOn_towerClosure_smul_sub_mul_of_isTateTrace (solution)
