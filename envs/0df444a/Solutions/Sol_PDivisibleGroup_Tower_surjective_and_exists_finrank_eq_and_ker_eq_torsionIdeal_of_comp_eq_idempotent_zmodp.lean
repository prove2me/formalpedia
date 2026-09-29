-- Prove2me | solution 1 for PDivisibleGroup.Tower.surjective_and_exists_finrank_eq_and_ker_eq_torsionIdeal_of_comp_eq_idempotent_zmodp
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/4610bbc0-30c9-5e29-86b2-7e7732e31ec5

import Mathlib
import Definitions.Def_PDivisibleGroup_Basic
import Definitions.Def_PDivisibleGroup_Tower
import Theorems.Thm_HopfAlgebra_finrank_eq_finrank_quotient_map_ker_counit_mul_finrank_range
import Theorems.Thm_PDivisibleGroup_Tower_exists_algEquiv_range_nsmulAlgHom_and_finite_projective_rankAtStalk
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_PDivisibleGroup_Tower_surjective_and_exists_finrank_eq_and_ker_eq_torsionIdeal_of_comp_eq_idempotent_zmodp
p2m_attr_erase "instance" "HopfAlgebra.HopfKerHopf.instHopfAlgebra HopfAlgebra.HopfKerHopf.instCoalgebra HopfAlgebra.HopfKerHopf.instIsCocomm HopfAlgebra.HopfKerHopf.instBialgebra HopfAlgebra.HopfIdealQuotient.instIsCocomm HopfAlgebra.HopfIdealQuotient.instBialgebra HopfAlgebra.HopfIdealQuotient.instHopfAlgebra Ideal.isHopfIdeal_bot HopfAlgebra.flat_quotient_bot HopfAlgebra.finiteType_quotient"
p2m_attr_erase "simp" "HopfAlgebra.canAlgHom_tmul HopfAlgebra.canMap_tmul HopfAlgebra.HopfKerHopf.ι₂_comulK HopfAlgebra.HopfKerHopf.ι₃_tmul HopfAlgebra.HopfKerHopf.counitK_apply HopfAlgebra.HopfKerHopf.coe_antipodeK HopfAlgebra.HopfKerHopf.ι₂_tmul HopfAlgebra.HopfKerHopf.coe_antipode HopfAlgebra.HopfKerHopf.hopfKerVal_apply HopfAlgebra.HopfKerHopf.valL_apply HopfAlgebra.HopfKerHopf.ι₂_comul HopfAlgebra.HopfIdealQuotient.comul_mk HopfAlgebra.antipodeAlgHom_apply HopfAlgebra.quotientFactorBialgHom_apply_mk HopfAlgebra.quotientBialgHom_apply HopfAlgebra.quotientLiftPoint_mk HopfAlgebra.convCompMonoidHom_apply HopfAlgebra.HopfIdealQuotient.antipode_mk HopfAlgebra.HopfIdealQuotient.counit_mk"

set_option autoImplicit false

open scoped TensorProduct

open PDivisibleGroup.Tower in

theorem solution
    (p : ℕ) [Fact p.Prime] (h : ℕ)
    (B : ℕ → Type) [∀ n, CommRing (B n)] [∀ n, HopfAlgebra (ZMod p) (B n)]
    [∀ n, Coalgebra.IsCocomm (ZMod p) (B n)] [∀ n, Module.Finite (ZMod p) (B n)]
    (s : ∀ n, B (n + 1) →ₐc[ZMod p] B n) (hs : ∀ n, Function.Surjective (s n))
    (hrankB : ∀ n, Module.finrank (ZMod p) (B n) = p ^ (n * h))
    (hkerB : ∀ n, RingHom.ker (s n) = PDivisibleGroup.Hopf.torsionIdeal (ZMod p) (B (n + 1)) (p ^ n))

    (e : ∀ n, B n →ₐc[ZMod p] B n) (he : ∀ n, (e n).comp (e n) = e n)
    (het : ∀ n, (s n).comp (e (n + 1)) = (e n).comp (s n))
    (C : ℕ → Type) [∀ n, CommRing (C n)] [∀ n, HopfAlgebra (ZMod p) (C n)]
    [∀ n, Coalgebra.IsCocomm (ZMod p) (C n)] [∀ n, Module.Finite (ZMod p) (C n)]
    (q : ∀ n, B n →ₐc[ZMod p] C n) (i : ∀ n, C n →ₐc[ZMod p] B n)
    (hq : ∀ n, Function.Surjective (q n))
    (hqi : ∀ n, (q n).comp (i n) = BialgHom.id (ZMod p) (C n))
    (hiq : ∀ n, (i n).comp (q n) = e n) :
    (∀ n, Function.Surjective ((q n).comp ((s n).comp (i (n + 1))))) ∧
    (∃ h₁ : ℕ, h₁ ≤ h ∧ ∀ n, Module.finrank (ZMod p) (C n) = p ^ (n * h₁)) ∧
    (∀ n, RingHom.ker ((q n).comp ((s n).comp (i (n + 1)))) =
      PDivisibleGroup.Hopf.torsionIdeal (ZMod p) (C (n + 1)) (p ^ n)) := by
  classical
  have hp : p.Prime := Fact.out

  have hqi' : ∀ n c, q n (i n c) = c := fun n c => by
    have := DFunLike.congr_fun (hqi n) c; rwa [BialgHom.comp_apply] at this
  have hiq' : ∀ n b, i n (q n b) = e n b := fun n b => by
    have := DFunLike.congr_fun (hiq n) b; rwa [BialgHom.comp_apply] at this
  have het' : ∀ n b, s n (e (n + 1) b) = e n (s n b) := fun n b => by
    have := DFunLike.congr_fun (het n) b; rwa [BialgHom.comp_apply, BialgHom.comp_apply] at this
  have hqe : ∀ n b, q n (e n b) = q n b := fun n b => by rw [← hiq', hqi']
  have hei : ∀ n c, e n (i n c) = i n c := fun n c => by rw [← hiq', hqi']
  have hiinj : ∀ n, Function.Injective (i n) := fun n =>
    Function.LeftInverse.injective (g := q n) (hqi' n)
  have hkerq : ∀ n b, q n b = 0 ↔ e n b = 0 := fun n b => by
    constructor
    · intro hb; rw [← hiq', hb, map_zero]
    · intro hb; rw [← hqe, hb, map_zero]

  have htq : ∀ (n : ℕ) (b : B (n + 1)), ((q n).comp ((s n).comp (i (n + 1)))) (q (n + 1) b) = q n (s n b) :=
    fun n b => by
    rw [BialgHom.comp_apply, BialgHom.comp_apply, hiq', het', hqe]

  have hsurj : ∀ n, Function.Surjective ((q n).comp ((s n).comp (i (n + 1)))) := by
    intro n c
    obtain ⟨b, rfl⟩ := hq n c
    obtain ⟨b', rfl⟩ := hs n b
    exact ⟨q (n + 1) b', htq n b'⟩

  have hker : ∀ n, RingHom.ker ((q n).comp ((s n).comp (i (n + 1)))) =
      PDivisibleGroup.Hopf.torsionIdeal (ZMod p) (C (n + 1)) (p ^ n) := by
    intro n
    rw [← PDivisibleGroup.Hopf.map_torsionIdeal_of_surjective (q (n + 1)) (hq (n + 1)) (p ^ n), ← hkerB n]
    apply le_antisymm
    · intro c hc
      rw [RingHom.mem_ker] at hc
      have h1 : s n (i (n + 1) c) = 0 := by
        have h2 : e n (s n (i (n + 1) c)) = 0 := by
          rw [← hkerq]
          rw [BialgHom.comp_apply, BialgHom.comp_apply] at hc
          exact hc
        rw [← hei, het', h2]
      have : c = (q (n + 1) : B (n + 1) →ₐ[ZMod p] C (n + 1)) (i (n + 1) c) := (hqi' _ c).symm
      rw [this]
      exact Ideal.mem_map_of_mem _ ((RingHom.mem_ker).2 h1)
    · rw [Ideal.map_le_iff_le_comap]
      intro b hb
      rw [RingHom.mem_ker] at hb
      change ((q n).comp ((s n).comp (i (n + 1)))) (q (n + 1) b) = 0
      rw [htq, hb, map_zero]
  refine ⟨hsurj, ?_, hker⟩

  let d : ℕ → ℕ := fun n => Module.finrank (ZMod p) (C n)

  have hdvd : ∀ n, d n ∣ p ^ (n * h) := by
    intro n
    have h1 := HopfAlgebra.finrank_eq_finrank_quotient_map_ker_counit_mul_finrank_range (ZMod p) (i n)
    have h2 : Module.finrank (ZMod p) ↥(i n : C n →ₐ[ZMod p] B n).range = d n :=
      (LinearEquiv.finrank_eq (AlgEquiv.ofInjective (i n : C n →ₐ[ZMod p] B n) (hiinj n)).toLinearEquiv).symm
    rw [hrankB, h2] at h1
    exact Dvd.intro_left _ h1.symm

  have hTe : ∀ (u : ℕ) (a : B (1 + u)), PDivisibleGroup.Tower.transitionLE s 1 u (e (1 + u) a) =
      e 1 (PDivisibleGroup.Tower.transitionLE s 1 u a) := by
    intro u
    induction u with
    | zero => intro a; rfl
    | succ u ih =>
      intro a
      rw [PDivisibleGroup.Tower.transitionLE_succ_apply, PDivisibleGroup.Tower.transitionLE_succ_apply]
      change PDivisibleGroup.Tower.transitionLE s 1 u (s (1 + u) (e ((1 + u) + 1) a)) =
        e 1 (PDivisibleGroup.Tower.transitionLE s 1 u (s (1 + u) a))
      rw [het', ih]
  have hrange : ∀ n, Module.finrank (ZMod p) ↥(PDivisibleGroup.Hopf.nsmulAlgHom (ZMod p) (C (1 + n)) (p ^ n)).range = d 1 := by
    intro n
    obtain ⟨e₁, he₁⟩ := (PDivisibleGroup.Tower.exists_algEquiv_range_nsmulAlgHom_and_finite_projective_rankAtStalk
      p h B s hs hrankB hkerB 1 n).1
    let T := PDivisibleGroup.Tower.transitionLE s 1 n
    have hT : Function.Surjective T := PDivisibleGroup.Tower.transitionLE_surjective s hs 1 n

    let F : B 1 →ₗ[ZMod p] C (1 + n) :=
      (q (1 + n) : B (1 + n) →ₐ[ZMod p] C (1 + n)).toLinearMap ∘ₗ
        ((PDivisibleGroup.Hopf.nsmulAlgHom (ZMod p) (B (1 + n)) (p ^ n)).range.val.toLinearMap ∘ₗ
          e₁.toLinearEquiv.toLinearMap)
    have hF : ∀ b : B (1 + n), F (T b) = PDivisibleGroup.Hopf.nsmulAlgHom (ZMod p) (C (1 + n)) (p ^ n) (q (1 + n) b) := by
      intro b
      change q (1 + n) ((e₁ (T b) : B (1 + n))) = _
      rw [he₁, PDivisibleGroup.Hopf.nsmulAlgHom_bialgHom_apply]

    have hrF : (PDivisibleGroup.Hopf.nsmulAlgHom (ZMod p) (C (1 + n)) (p ^ n)).range.toSubmodule = LinearMap.range F := by
      apply le_antisymm
      · rintro c ⟨c', rfl⟩
        obtain ⟨b, rfl⟩ := hq (1 + n) c'
        exact ⟨T b, hF b⟩
      · rintro c ⟨x, rfl⟩
        obtain ⟨b, rfl⟩ := hT x
        rw [hF]
        exact ⟨q (1 + n) b, rfl⟩

    have hkF : LinearMap.ker F = LinearMap.ker (q 1 : B 1 →ₐ[ZMod p] C 1).toLinearMap := by
      ext x
      rw [LinearMap.mem_ker, LinearMap.mem_ker]
      obtain ⟨b, rfl⟩ := hT x
      change q (1 + n) ((e₁ (T b) : B (1 + n))) = 0 ↔ q 1 (T b) = 0
      rw [hkerq, hkerq, he₁, ← PDivisibleGroup.Hopf.nsmulAlgHom_bialgHom_apply (e (1 + n)) (p ^ n) b, ← he₁, hTe]
      rw [ZeroMemClass.coe_eq_zero, map_eq_zero_iff e₁ e₁.injective]
    have h1 := LinearMap.finrank_range_add_finrank_ker F
    have h2 := LinearMap.finrank_range_add_finrank_ker (q 1 : B 1 →ₐ[ZMod p] C 1).toLinearMap
    rw [LinearMap.range_eq_top.2 (show Function.Surjective ((q 1 : B 1 →ₐ[ZMod p] C 1).toLinearMap) from hq 1),
      finrank_top] at h2
    rw [hkF] at h1
    rw [← Subalgebra.finrank_toSubmodule, hrF]
    change Module.finrank (ZMod p) ↥(LinearMap.range F) = Module.finrank (ZMod p) (C 1)
    omega

  have hmul : ∀ n, d (n + 1) = d n * d 1 := by
    intro n
    have h1 := HopfAlgebra.finrank_eq_finrank_quotient_map_ker_counit_mul_finrank_range (ZMod p)
      (PDivisibleGroup.Hopf.nsmulBialgHom (ZMod p) (C (n + 1)) (p ^ n))
    rw [PDivisibleGroup.Hopf.toAlgHom_nsmulBialgHom] at h1
    have hr : Module.finrank (ZMod p) ↥(PDivisibleGroup.Hopf.nsmulAlgHom (ZMod p) (C (n + 1)) (p ^ n)).range = d 1 := by
      have := hrange n
      rwa [Nat.add_comm] at this
    have hJ : Ideal.map (PDivisibleGroup.Hopf.nsmulAlgHom (ZMod p) (C (n + 1)) (p ^ n))
        (RingHom.ker (Bialgebra.counitAlgHom (ZMod p) (C (n + 1)))) =
        RingHom.ker ((q n).comp ((s n).comp (i (n + 1))) : C (n + 1) →ₐ[ZMod p] C n) := by
      rw [show RingHom.ker ((q n).comp ((s n).comp (i (n + 1))) : C (n + 1) →ₐ[ZMod p] C n) =
        RingHom.ker ((q n).comp ((s n).comp (i (n + 1)))) from rfl, hker n]
      rfl
    have hQ : Module.finrank (ZMod p) (C (n + 1) ⧸ Ideal.map (PDivisibleGroup.Hopf.nsmulAlgHom (ZMod p) (C (n + 1)) (p ^ n))
        (RingHom.ker (Bialgebra.counitAlgHom (ZMod p) (C (n + 1))))) = d n := by
      rw [LinearEquiv.finrank_eq ((Ideal.quotientEquivAlgOfEq (ZMod p) hJ).trans
        (Ideal.quotientKerAlgEquivOfSurjective (f := ((q n).comp ((s n).comp (i (n + 1))) : C (n + 1) →ₐ[ZMod p] C n))
          (hsurj n))).toLinearEquiv]
    rw [hQ, hr] at h1
    exact h1

  have hd0 : d 0 = 1 := Nat.dvd_one.1 (by simpa using hdvd 0)
  obtain ⟨h₁, hh₁, hd1⟩ : ∃ h₁ ≤ 1 * h, d 1 = p ^ h₁ := (Nat.dvd_prime_pow hp).1 (hdvd 1)
  refine ⟨h₁, by omega, fun n => ?_⟩
  induction n with
  | zero => rw [Nat.zero_mul, pow_zero]; exact hd0
  | succ n ih =>
    change d (n + 1) = _
    rw [hmul, show d n = p ^ (n * h₁) from ih, hd1, ← pow_add, Nat.succ_mul]

end S_PDivisibleGroup_Tower_surjective_and_exists_finrank_eq_and_ker_eq_torsionIdeal_of_comp_eq_idempotent_zmodp
end P2MW
export P2MW.S_PDivisibleGroup_Tower_surjective_and_exists_finrank_eq_and_ker_eq_torsionIdeal_of_comp_eq_idempotent_zmodp (solution)
