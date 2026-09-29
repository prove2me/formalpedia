-- Prove2me | solution 1 for PDivisibleGroup.point_eq_one_of_forall_norm_sub_counit_lt_one_of_formallyEtale_of_ringOfIntegers
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/b7e0766e-254d-5c4d-8c17-ffed68d5c69b

import Mathlib
import Definitions.Def_PDivisibleGroup_Points
import Definitions.Def_PadicAlgCl_RingOfIntegers
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_PDivisibleGroup_point_eq_one_of_forall_norm_sub_counit_lt_one_of_formallyEtale_of_ringOfIntegers

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 80000

noncomputable section

namespace PDivC5a

open scoped NNReal

variable (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p))

def unitBall : Subalgebra (PadicAlgCl.ringOfIntegers p K) (PadicAlgCl p) where
  carrier := {x | ‖x‖ ≤ 1}
  mul_mem' {x y} hx hy := by
    simp only [Set.mem_setOf_eq] at hx hy ⊢
    rw [norm_mul]
    exact mul_le_one₀ hx (norm_nonneg _) hy
  one_mem' := by simp
  add_mem' {x y} hx hy := (IsUltrametricDist.norm_add_le_max x y).trans (max_le hx hy)
  zero_mem' := by simp
  algebraMap_mem' r := PadicAlgCl.ringOfIntegers.norm_coe_le_one p K r

variable {p K}

theorem mem_unitBall_iff (x : PadicAlgCl p) : x ∈ unitBall p K ↔ ‖x‖ ≤ 1 := Iff.rfl

def ballIdeal (t : ℝ) (ht : 0 ≤ t) : Ideal (unitBall p K) where
  carrier := {x | ‖(x : PadicAlgCl p)‖ ≤ t}
  add_mem' {x y} hx hy := by
    simp only [Set.mem_setOf_eq] at hx hy ⊢
    rw [Subalgebra.coe_add]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hx hy)
  zero_mem' := by
    simp only [Set.mem_setOf_eq, Subalgebra.coe_zero, norm_zero]
    exact ht
  smul_mem' c x hx := by
    simp only [Set.mem_setOf_eq] at hx ⊢
    rw [smul_eq_mul, Subalgebra.coe_mul, norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _) c.2).trans hx

theorem mem_ballIdeal_iff {t : ℝ} (ht : 0 ≤ t) (x : unitBall p K) :
    x ∈ ballIdeal t ht ↔ ‖(x : PadicAlgCl p)‖ ≤ t := Iff.rfl

theorem ballIdeal_mul_le {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) :
    ballIdeal (p := p) (K := K) s hs * ballIdeal t ht ≤ ballIdeal (s * t) (mul_nonneg hs ht) :=
  Ideal.mul_le.2 fun x hx y hy => by
    rw [mem_ballIdeal_iff] at hx hy ⊢
    rw [Subalgebra.coe_mul, norm_mul]
    exact mul_le_mul hx hy (norm_nonneg _) hs

theorem ballIdeal_pow_le {r : ℝ} (hr : 0 ≤ r) (n : ℕ) :
    ballIdeal (p := p) (K := K) r hr ^ n ≤ ballIdeal (r ^ n) (pow_nonneg hr n) := by
  induction n with
  | zero =>
    intro x _
    rw [mem_ballIdeal_iff, pow_zero]
    exact x.2
  | succ n ih =>
    rw [pow_succ]
    refine (Ideal.mul_mono ih le_rfl).trans ?_
    have := ballIdeal_mul_le (p := p) (K := K) (pow_nonneg hr n) hr
    simpa [pow_succ] using this

end PDivC5a

end

set_option maxHeartbeats 3200000 in
set_option synthInstance.maxHeartbeats 800000 in
open PDivC5a in
theorem solution
    (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] K]
    {h : ℕ} (Q : PDivisibleGroup (PadicAlgCl.ringOfIntegers p K) p h) (v : ℕ) [Algebra.FormallyEtale (PadicAlgCl.ringOfIntegers p K) (Q.level v)]
    (g : Q.Point (PadicAlgCl p) v)
    (hg : ∀ a : Q.level v, ‖PDivisibleGroup.Point.toAlgHom g a -
      algebraMap (PadicAlgCl.ringOfIntegers p K) (PadicAlgCl p) (Coalgebra.counit a)‖ < 1) :
    g = 1 := by
  classical

  let φ : Q.level v →ₐ[PadicAlgCl.ringOfIntegers p K] PadicAlgCl p := PDivisibleGroup.Point.toAlgHom g
  let ψ : Q.level v →ₐ[PadicAlgCl.ringOfIntegers p K] PadicAlgCl p :=
    PDivisibleGroup.Point.toAlgHom (1 : Q.Point (PadicAlgCl p) v)
  have hψ : ∀ a, ψ a = algebraMap (PadicAlgCl.ringOfIntegers p K) (PadicAlgCl p) (Coalgebra.counit a) :=
    fun a => PDivisibleGroup.Point.one_apply (G := Q) (L := PadicAlgCl p) a
  suffices hφψ : φ = ψ by
    rw [← PDivisibleGroup.Point.ofAlgHom_toAlgHom g,
      ← PDivisibleGroup.Point.ofAlgHom_toAlgHom (1 : Q.Point (PadicAlgCl p) v)]
    exact congrArg PDivisibleGroup.Point.ofAlgHom hφψ

  let δ : Q.level v →ₗ[PadicAlgCl.ringOfIntegers p K] PadicAlgCl p := φ.toLinearMap - ψ.toLinearMap
  have hδ : ∀ a, δ a = φ a - ψ a := fun a => rfl
  have hg' : ∀ a, ‖δ a‖ < 1 := fun a => by rw [hδ, hψ]; exact hg a

  have hIntR : Algebra.IsIntegral ℤ_[p] (PadicAlgCl.ringOfIntegers p K) :=
    ⟨fun x => (isIntegral_algHom_iff (PadicAlgCl.ringOfIntegers p K).val Subtype.val_injective).1
      (PadicAlgCl.ringOfIntegers.isIntegral_coe x)⟩
  have hφO : ∀ a, φ a ∈ unitBall p K := fun a => by
    rw [mem_unitBall_iff]
    have h1 : IsIntegral (PadicAlgCl.ringOfIntegers p K) (φ a) :=
      (Algebra.IsIntegral.isIntegral (R := PadicAlgCl.ringOfIntegers p K) a).map φ
    have h2 : IsIntegral ℤ_[p] (φ a) :=
      isIntegral_trans (R := ℤ_[p]) (A := PadicAlgCl.ringOfIntegers p K) _ h1
    exact PadicAlgCl.ringOfIntegers.norm_le_one_of_isIntegral (p := p) h2
  have hψO : ∀ a, ψ a ∈ unitBall p K := fun a => by
    rw [mem_unitBall_iff, hψ]
    exact PadicAlgCl.ringOfIntegers.norm_coe_le_one p K _
  let φ' : Q.level v →ₐ[PadicAlgCl.ringOfIntegers p K] unitBall p K := φ.codRestrict (unitBall p K) hφO
  let ψ' : Q.level v →ₐ[PadicAlgCl.ringOfIntegers p K] unitBall p K := ψ.codRestrict (unitBall p K) hψO
  have hφ' : ∀ a, ((φ' a : unitBall p K) : PadicAlgCl p) = φ a := fun a => rfl
  have hψ' : ∀ a, ((ψ' a : unitBall p K) : PadicAlgCl p) = ψ a := fun a => rfl

  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := PadicAlgCl.ringOfIntegers p K) (M := Q.level v)
  let r0 : NNReal := s.sup fun a => ‖δ a‖₊
  have hr0 : r0 < 1 := by
    refine (Finset.sup_lt_iff (by simp)).2 fun a _ => ?_
    have := hg' a
    rwa [← coe_nnnorm, ← NNReal.coe_one, NNReal.coe_lt_coe] at this
  let r : ℝ := r0
  have hr1 : r < 1 := by
    show (r0 : ℝ) < 1
    exact_mod_cast hr0
  have hrnn : 0 ≤ r := r0.2
  have hδr : ∀ a, ‖δ a‖ ≤ r := by
    intro a
    have ha : a ∈ Submodule.span (PadicAlgCl.ringOfIntegers p K) (s : Set (Q.level v)) := by
      rw [hs]; exact Submodule.mem_top
    induction ha using Submodule.span_induction with
    | mem x hx =>
      rw [← coe_nnnorm]
      show ((‖δ x‖₊ : NNReal) : ℝ) ≤ ((r0 : NNReal) : ℝ)
      exact NNReal.coe_le_coe.2 (Finset.le_sup (f := fun a => ‖δ a‖₊) hx)
    | zero => rw [map_zero, norm_zero]; exact hrnn
    | add x y _ _ hx hy =>
      rw [map_add]
      exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hx hy)
    | smul c x _ hx =>
      rw [map_smul, Algebra.smul_def, norm_mul, PadicAlgCl.ringOfIntegers.algebraMap_coe]
      exact (mul_le_of_le_one_left (norm_nonneg _)
        (PadicAlgCl.ringOfIntegers.norm_coe_le_one p K c)).trans hx

  have hN : ∀ (N : ℕ) (a : Q.level v), ‖δ a‖ ≤ r ^ N := by
    intro N a
    let J : Ideal (unitBall p K) := ballIdeal (r ^ N) (pow_nonneg hrnn N)
    letI : CommRing (unitBall p K ⧸ J) := Ideal.Quotient.commRing J
    let I : Ideal (unitBall p K ⧸ J) := (ballIdeal r hrnn).map (Ideal.Quotient.mk J)
    have hI : IsNilpotent I := by
      refine ⟨N, ?_⟩
      rw [← Ideal.map_pow, Ideal.zero_eq_bot, Ideal.map_eq_bot_iff_le_ker, Ideal.mk_ker]
      exact ballIdeal_pow_le hrnn N
    let mkJ : unitBall p K →ₐ[PadicAlgCl.ringOfIntegers p K] unitBall p K ⧸ J :=
      Ideal.Quotient.mkₐ (PadicAlgCl.ringOfIntegers p K) J
    let g₁ : Q.level v →ₐ[PadicAlgCl.ringOfIntegers p K] unitBall p K ⧸ J := mkJ.comp φ'
    let g₂ : Q.level v →ₐ[PadicAlgCl.ringOfIntegers p K] unitBall p K ⧸ J := mkJ.comp ψ'
    have hg₁ : ∀ x, g₁ x = Ideal.Quotient.mk J (φ' x) := fun x => rfl
    have hg₂ : ∀ x, g₂ x = Ideal.Quotient.mk J (ψ' x) := fun x => rfl
    have hsub : ∀ x, φ' x - ψ' x ∈ ballIdeal r hrnn := fun x => by
      rw [mem_ballIdeal_iff, Subalgebra.coe_sub, hφ', hψ', ← hδ]
      exact hδr x
    have h12 : ∀ x, Ideal.Quotient.mk I (g₁ x) = Ideal.Quotient.mk I (g₂ x) := fun x => by
      refine Ideal.Quotient.eq.2 ?_
      rw [hg₁, hg₂, ← map_sub]
      exact Ideal.mem_map_of_mem _ (hsub x)
    have heq : g₁ = g₂ := Algebra.FormallyUnramified.ext I hI h12
    have hx : Ideal.Quotient.mk J (φ' a) = Ideal.Quotient.mk J (ψ' a) := by
      rw [← hg₁, ← hg₂, heq]
    have hmem := Ideal.Quotient.eq.1 hx
    rw [mem_ballIdeal_iff, Subalgebra.coe_sub, hφ', hψ', ← hδ] at hmem
    exact hmem

  refine AlgHom.ext fun a => ?_
  by_contra hne
  have hpos : 0 < ‖δ a‖ := by
    rw [hδ, norm_pos_iff]
    exact sub_ne_zero.2 hne
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hpos hr1
  exact absurd ((hN n a).trans_lt hn) (lt_irrefl _)

end S_PDivisibleGroup_point_eq_one_of_forall_norm_sub_counit_lt_one_of_formallyEtale_of_ringOfIntegers
end P2MW
export P2MW.S_PDivisibleGroup_point_eq_one_of_forall_norm_sub_counit_lt_one_of_formallyEtale_of_ringOfIntegers (solution)
