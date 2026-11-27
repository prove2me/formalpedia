-- Prove2me | solution 1 for P2M_UpperTheory_Reformulated_B_Qp1_exists_limit_of_approx__0e8cc604b966
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T05:19:50.647326+00:00
-- url     : https://prove2.me/submissions/a20c08f3-122d-4405-985f-1754bacf3e23

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_ExistsLimitOfApprox

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

namespace UpperTheory.Reformulated.B.Qp1.exists_limit_of_approx
theorem _root_.solution.{u_1} :
    ∀ {R : Type u_1} [inst : CommRing R] (I : Ideal R)
    [IsPrecomplete I R] (P : ℕ → R → Prop),
    (∀ (n : ℕ) (x : R), P n x → ∃ (y : R), y - x ∈ I ^ n ∧ P (n + (1 : ℕ)) y) →
      ∀ {x₀ : R}, P (0 : ℕ) x₀ → ∃ (x : R), ∀ (n : ℕ), ∃ (y : R), P n y ∧ x - y ∈ I ^ n := by
  intro R _ I hI P h x₀ h₀
  choose g hg hP using h
  let f : (n : ℕ) → {x : R // P n x} := fun n =>
    Nat.rec (motive := fun n => {x : R // P n x}) ⟨x₀, h₀⟩
      (fun n x => ⟨g n x.1 x.2, hP n x.1 x.2⟩) n
  have hstep : ∀ n, (f (n + 1)).1 - (f n).1 ∈ I ^ n := fun n => hg n (f n).1 (f n).2
  have hdiff : ∀ m n, m ≤ n → (f n).1 - (f m).1 ∈ I ^ m := by
    intro m n hmn
    induction n, hmn using Nat.le_induction with
    | base => simp
    | succ n hmn ih =>
      have h1 : (f (n + 1)).1 - (f n).1 ∈ I ^ m := Ideal.pow_le_pow_right hmn (hstep n)
      have h2 := (I ^ m).add_mem h1 ih
      rwa [sub_add_sub_cancel] at h2
  have htop : ∀ n : ℕ, (I ^ n • ⊤ : Submodule R R) = I ^ n := fun n => by
    rw [smul_eq_mul, Ideal.mul_top]
  obtain ⟨L, hL⟩ := IsPrecomplete.prec hI (f := fun n => (f n).1) (by
    intro m n hmn
    refine SModEq.symm ?_
    rw [SModEq.sub_mem, htop]
    exact hdiff m n hmn)
  refine ⟨L, fun n => ⟨(f n).1, (f n).2, ?_⟩⟩
  have h3 := (hL n).symm
  rwa [SModEq.sub_mem, htop] at h3
end UpperTheory.Reformulated.B.Qp1.exists_limit_of_approx
