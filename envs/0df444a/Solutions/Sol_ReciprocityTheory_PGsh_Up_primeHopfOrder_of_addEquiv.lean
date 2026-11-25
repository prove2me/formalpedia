-- Prove2me | solution 1 for ReciprocityTheory.PGsh.Up.primeHopfOrder_of_addEquiv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T15:53:32.081939+00:00
-- url     : https://prove2.me/submissions/9bf27ee6-0c80-4725-a38b-fe2732846498

import Definitions.Def_ReciprocityTheory_DualLattices_PrimeHopfOrderStatement
import Definitions.Def_ReciprocityTheory_DualLattices_PrimeHopfOrderOfAddEquiv
import Theorems.Thm_ReciprocityTheory_PGsh_Up_hasColen_map
import Theorems.Thm_ReciprocityTheory_PGsh_Up_map_pbE_symm
import Theorems.Thm_ReciprocityTheory_PGsh_Up_mem_augIdeal_pull
import Theorems.Thm_ReciprocityTheory_PGsh_Up_pow_mem_aug
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
namespace ReciprocityTheory.PGsh.Up
open ReciprocityTheory.PGsh.L2
section Transport
variable {C : Type} [Field C] {R : Type} [CommRing R] [Algebra R C]
variable {X Y : Type} [AddCommGroup X] [Fintype X] [DecidableEq X]
  [AddCommGroup Y] [Fintype Y] [DecidableEq Y]
private theorem pbE_symm_pow (e : X ≃+ Y) (f : X → C) (n : ℕ) :
    (pbE (C := C) (R := R) e).symm (f ^ n) = ((pbE (C := C) (R := R) e).symm f) ^ n := by
  funext y
  simp only [pbE_symm_apply, Pi.pow_apply]
end Transport
end ReciprocityTheory.PGsh.Up
end
end

set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up
open ReciprocityTheory.PGsh.L2
namespace ReciprocityTheory.PGsh.Up
theorem _root_.solution (hU3 : PrimeHopfOrderStatement) (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C]
    [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C]
    (hv : v.Integers R) (hp : v (p : C) < 1) {K : Type} [AddCommGroup K] [Fintype K]
    [DecidableEq K] (e : ZMod p ≃+ K) (AK : HopfOrder (C := C) R K) :
    ∃ (xK : K → C) (δ : R) (x1 : C), xK ∈ augIdeal AK.carrier ∧
      xK ^ p = (fun a => algebraMap R C δ * xK a) ∧ v (algebraMap R C δ) = v x1 ^ (p - 1) ∧
      (∀ f ∈ augIdeal AK.carrier, ∃ r : R,
        f - r • xK ∈ augIdeal AK.carrier * augIdeal AK.carrier) ∧
      HasColen R v AK.carrier (v x1 ^ (p * (p - 1) / 2)) := by
  obtain ⟨x, _, δ, hx, hx0, -, -, -, hxp, hδ, -, haug, -, hcol⟩ :=
    hU3 p C v R hv hp (hopfPull e AK)
  have hxa : x ∈ ReciprocityTheory.PGsh.L2.augIdeal (hopfPull e AK).carrier := by
    simp only [ReciprocityTheory.PGsh.L2.augIdeal, Submodule.mem_inf, LinearMap.mem_ker, LinearMap.proj_apply]
    exact ⟨hx, hx0⟩
  have hxK := (mem_augIdeal_pull e AK x).1 hxa
  refine ⟨(pbE (C := C) (R := R) e).symm x, δ, x 1, hxK, ?_, hδ, ?_, ?_⟩
  · funext k
    have h := congrFun hxp (e.symm k)
    simp only [Pi.pow_apply] at h ⊢
    rw [pbE_symm_apply]
    exact h
  · have key : ∀ F ∈ Submodule.span R {y | ∃ j : ℕ, 1 ≤ j ∧ j < p ∧ y = x ^ j},
        ∃ r : R, (pbE (C := C) (R := R) e).symm F - r • (pbE (C := C) (R := R) e).symm x ∈
          ReciprocityTheory.PGsh.L2.augIdeal AK.carrier * ReciprocityTheory.PGsh.L2.augIdeal AK.carrier := by
      intro F hF
      induction hF using Submodule.span_induction with
      | mem y hy =>
        obtain ⟨j, hj1, -, rfl⟩ := hy
        rcases Nat.lt_or_ge j 2 with hj | hj
        · obtain rfl : j = 1 := by omega
          refine ⟨1, ?_⟩
          rw [pow_one, one_smul, sub_self]
          exact zero_mem _
        · obtain ⟨m, rfl⟩ : ∃ m, j = m + 2 := ⟨j - 2, by omega⟩
          refine ⟨0, ?_⟩
          rw [zero_smul, sub_zero, pbE_symm_pow, show m + 2 = (m + 1) + 1 from rfl, pow_succ]
          exact Submodule.mul_mem_mul (pow_mem_aug AK hxK m) hxK
      | zero =>
        refine ⟨0, ?_⟩
        rw [map_zero, zero_smul, sub_zero]
        exact zero_mem _
      | add a b _ _ ha hb =>
        obtain ⟨r1, h1⟩ := ha
        obtain ⟨r2, h2⟩ := hb
        refine ⟨r1 + r2, ?_⟩
        convert add_mem h1 h2 using 1
        rw [map_add, add_smul]
        abel
      | smul c a _ ha =>
        obtain ⟨r1, h1⟩ := ha
        refine ⟨c * r1, ?_⟩
        convert Submodule.smul_mem _ c h1 using 1
        rw [map_smul, smul_sub, mul_smul]
    intro f hf
    have hF : pbE (C := C) (R := R) e f ∈
        ReciprocityTheory.PGsh.L2.augIdeal (hopfPull e AK).carrier := by
      rw [mem_augIdeal_pull, LinearEquiv.symm_apply_apply]
      exact hf
    rw [haug] at hF
    obtain ⟨r, hr⟩ := key _ hF
    rw [LinearEquiv.symm_apply_apply] at hr
    exact ⟨r, hr⟩
  · have hc := hasColen_map v e.symm _ _ hcol
    rwa [show (hopfPull e AK).carrier =
        AK.carrier.map (pbE (C := C) (R := R) e : (K → C) →ₗ[R] (ZMod p → C)) from rfl,
      map_pbE_symm] at hc
end ReciprocityTheory.PGsh.Up
